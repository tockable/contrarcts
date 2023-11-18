//SPDX-License-Identifier: Unlicense

pragma solidity ^0.8.0;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import "erc721a/contracts/extensions/ERC721AQueryable.sol";

contract TockableDrop is ERC721AQueryable, Ownable, ReentrancyGuard {
    /// contract version
    uint256 public constant TOCKABLE_CONTRACT_VERSION = 1;

    /// Errors
    error InvalidArgs();
    error NotInitialazed();
    error MintIsNotLive();
    error MoreThanAllowed();
    error MoreThanAvailable();
    error NotElligible();
    error NotEnoughEth();
    error UnAuthorized();
    error WithdrawFailed();
    error TraitsIsFrozen();
    error TokenHasBeenTakenBefore(uint256[] indexes);

    /// Structs
    struct IpfsHash {
        bytes32 part1;
        bytes32 part2;
    }

    struct Role {
        uint256 id;
        uint256 price;
        uint256 maxAllowedMint;
    }

    struct Session {
        uint256 id;
        uint256[] allowedRoles;
        uint256 allocation;
    }

    /// Constants
    string private constant CONTRACT_NAME = "Tockable";
    string private constant TOKEN_NAME = "tockable";
    string private constant TOKEN_SYMBOL = "TCKBLE";
    uint256 public constant TOTAL_SUPPLY = 0; // 0 if collection is unlimited
    uint256 private constant FIRST_TOKEN_ID = 1;
    uint256 private constant BASE_FEE = 0.0002 ether;
    bool public constant duplicateVerification = false;
    bool public constant isUnlimited = false;

    /// Parameters
    bytes32[] public traitTypes;
    address private tockableAddress;
    address private signerAddress;
    bool public isMintLive = false;
    bool public isTraitsFrozen = false;
    uint256 public activeSession;
    uint256 private existingRolesLength;
    uint256 private exisitngSessionsLength;

    /// Mappings
    mapping(uint256 => uint256) private mintedInSessionById;
    mapping(address => mapping(uint256 => mapping(uint256 => uint256)))
        private mintedByAddressInRoleInSessionId;
    mapping(uint256 => Role) private getRoleById;
    mapping(uint256 => Session) private getSessionById;

    mapping(uint256 => IpfsHash) private ipfsHashOf;
    mapping(uint256 => mapping(bytes32 => bytes32))
        private traitValueOfTraitTypeOf;
    mapping(bytes32 => bool) private hasBeenTaken;

    /// setters
    function setRoles(Role[] calldata _roles) external onlyOwner {
        if (_roles.length == 0) revert InvalidArgs();
        if (existingRolesLength > 0) {
            if (_roles.length < existingRolesLength) revert InvalidArgs();
        }

        unchecked {
            for (uint256 i = 0; i < _roles.length; i++) {
                getRoleById[i] = _roles[i];
            }
        }

        if (existingRolesLength < _roles.length)
            existingRolesLength = _roles.length;
    }

    function setSessions(Session[] calldata _sessions) external onlyOwner {
        if (_sessions.length == 0) revert InvalidArgs();
        if (exisitngSessionsLength > 0) {
            if (_sessions.length < exisitngSessionsLength) revert InvalidArgs();
        }

        unchecked {
            for (uint256 i = 0; i < _sessions.length; i++) {
                getSessionById[i] = _sessions[i];
            }
        }

        if (exisitngSessionsLength < _sessions.length)
            exisitngSessionsLength = _sessions.length;
    }

    function setMintIsLive(bool _status) public onlyOwner {
        isMintLive = _status;
    }

    function setActiveSession(uint256 _activeSession) external onlyOwner {
        if (!isMintLive) setMintIsLive(true);
        activeSession = _activeSession;
    }

    function addTraitTypes(bytes32[] calldata _traitTypes) external onlyOwner {
        if (isTraitsFrozen) revert TraitsIsFrozen();

        for (uint256 i = 0; i < _traitTypes.length; i++) {
            traitTypes.push(_traitTypes[i]);
        }

        isTraitsFrozen = true;
    }

    function _startTokenId() internal view virtual override returns (uint256) {
        return FIRST_TOKEN_ID;
    }

    /// Mint
    function mint(
        uint256 _quantity,
        IpfsHash[] calldata _cids,
        bytes calldata _signature,
        uint256 _roleId,
        bytes32[][] calldata _traits
    ) external payable nonReentrant {
        if (traitTypes.length == 0) revert NotInitialazed();
        if (!isMintLive) revert MintIsNotLive();

        inMintArgsValid(_quantity, _cids, _traits);
        isElligible(_roleId);
        isSignatureValid(msg.sender, _roleId, _signature);
        isTokenLeftInTotal(_quantity);
        isTokenLeftInActiveSession(_quantity);
        isTokenLeftForAddressInRoleInSession(msg.sender, _roleId, _quantity);
        isDuplicate(_traits);

        uint256 payAmount = (getRoleById[_roleId].price + BASE_FEE) * _quantity;
        if (msg.value < payAmount) revert NotEnoughEth();

        uint256 nextTokenIdBeforeMint = _nextTokenId();

        _safeMint(msg.sender, _quantity);

        setTokenTraits(_quantity, nextTokenIdBeforeMint, _cids, _traits);

        mintedInSessionById[activeSession] =
            mintedInSessionById[activeSession] +
            _quantity;

        mintedByAddressInRoleInSessionId[msg.sender][_roleId][activeSession] =
            mintedByAddressInRoleInSessionId[msg.sender][_roleId][
                activeSession
            ] +
            _quantity;

        uint256 tockableFee = _quantity * BASE_FEE;
        withdrawEth(payable(tockableAddress), tockableFee);
    }

    function ownerMint(
        uint256 _quantity,
        IpfsHash[] calldata _cids,
        bytes32[][] calldata _traits
    ) external nonReentrant onlyOwner {
        if (traitTypes.length == 0) revert NotInitialazed();

        inMintArgsValid(_quantity, _cids, _traits);
        isTokenLeftInTotal(_quantity);
        isDuplicate(_traits);

        uint256 nextTokenIdBeforeMint = _nextTokenId();
        _safeMint(msg.sender, _quantity);
        setTokenTraits(_quantity, nextTokenIdBeforeMint, _cids, _traits);
    }

    /// Validators
    function isTokenLeftInTotal(uint256 _quantity) private view {
        if (!isUnlimited) {
            if (tokensLeft() < _quantity) revert MoreThanAvailable();
        }
    }

    function isTokenLeftInActiveSession(uint256 _quantity) private view {
        if (!isUnlimited) {
            if (tokensLeftInSession(activeSession) < _quantity)
                revert MoreThanAvailable();
        }
    }

    function isTokenLeftForAddressInRoleInSession(
        address _address,
        uint256 _roleId,
        uint256 _quantity
    ) private view {
        if (
            tokensLeftForAddressInRoleInActiveSession(_address, _roleId) <
            _quantity
        ) revert MoreThanAllowed();
    }

    function isSignatureValid(
        address _address,
        uint256 _roleId,
        bytes memory _signature
    ) private view {
        if (recoverSigner(_address, _roleId, _signature) != signerAddress)
            revert UnAuthorized();
    }

    function isElligible(uint256 _roleId) private view {
        uint256[] memory allowedRolesIdsInCurrentSession = getSessionById[
            activeSession
        ].allowedRoles;
        if (!isInArray(allowedRolesIdsInCurrentSession, _roleId))
            revert NotElligible();
    }

    function inMintArgsValid(
        uint256 _quantity,
        IpfsHash[] calldata _cids,
        bytes32[][] calldata _traits
    ) private pure {
        if (_traits.length == 0) revert InvalidArgs();
        if (_cids.length != _quantity) revert InvalidArgs();
        if (_cids.length != _traits.length) revert InvalidArgs();
    }

    function isDuplicate(bytes32[][] calldata _traits) private {
        if (!duplicateVerification) return;
        uint256[] memory indexes = new uint256[](_traits.length);

        unchecked {
            for (uint256 i = 0; i < _traits.length; i++) {
                bytes32 tokenHash = createHashFromTraits(_traits[i]);
                if (hasBeenTaken[tokenHash]) {
                    indexes[i] = 1;
                } else {
                    indexes[i] = 0;
                    hasBeenTaken[tokenHash] = true;
                }
            }
        }

        if (isInArray(indexes, 1)) {
            revert TokenHasBeenTakenBefore({indexes: indexes});
        }
    }

    /// Metadata
    function tokenURI(
        uint256 tokenId
    ) public view virtual override(ERC721A, IERC721A) returns (string memory) {
        string memory metadata = string(
            abi.encodePacked(
                '{"name": "',
                TOKEN_NAME,
                " #",
                toString(tokenId),
                '", '
            )
        );

        metadata = string(
            abi.encodePacked(
                metadata,
                '"image": "',
                getTokenImageIpfsUrl(tokenId),
                '", '
            )
        );

        metadata = string(
            abi.encodePacked(metadata, '"symbol": "', TOKEN_SYMBOL, '", ')
        );

        metadata = string(
            abi.encodePacked(
                metadata,
                '"attributes": ',
                getTokenAttributes(tokenId),
                "}"
            )
        );

        return metadata;
    }

    /// Transfer
    function transfersFrom(
        address from,
        address to,
        uint256[] memory tokenIds
    ) public virtual {
        for (uint i = 0; i < tokenIds.length; i++)
            transferFrom(from, to, tokenIds[i]);
    }

    function safeTransfersFrom(
        address from,
        address to,
        uint256[] memory tokenIds,
        bytes memory _data
    ) public virtual {
        for (uint i = 0; i < tokenIds.length; i++)
            safeTransferFrom(from, to, tokenIds[i], _data);
    }

    /// Withdraws
    function withdraw() public onlyOwner {
        withdrawEth(payable(msg.sender), address(this).balance);
    }

    function withdrawEth(address payable to, uint256 amount) private {
        if (amount == 0) return;
        (bool ow, ) = to.call{value: amount}("");
        if (!ow) revert WithdrawFailed();
    }

    receive() external payable {}

    /// Helpers & Utils
    function tokensLeft() public view returns (uint256) {
        return TOTAL_SUPPLY - _totalMinted();
    }

    function tokensLeftInSession(uint256 _id) public view returns (uint256) {
        return getSessionById[_id].allocation - mintedInSessionById[_id];
    }

    function tokensLeftForAddressInRoleInActiveSession(
        address _address,
        uint256 _roleId
    ) private view returns (uint256) {
        uint256 minted = mintedByAddressInRoleInSessionId[_address][_roleId][
            activeSession
        ];
        uint256 maxMintable = getRoleById[_roleId].maxAllowedMint;
        return maxMintable - minted;
    }

    function setIpfsHash(
        uint256 _tokenId,
        IpfsHash calldata _ipfsHash
    ) private {
        ipfsHashOf[_tokenId] = _ipfsHash;
    }

    function setTokenTraits(
        uint256 _quantity,
        uint256 _nextTokenIdBeforeMint,
        IpfsHash[] calldata _cids,
        bytes32[][] calldata _traits
    ) private {
        unchecked {
            for (uint256 i = 0; i < _quantity; i++) {
                setIpfsHash(_nextTokenIdBeforeMint + i, _cids[i]);
                for (uint256 j = 0; j < _traits[i].length; j++) {
                    if (_traits[i].length != traitTypes.length)
                        revert InvalidArgs();
                    traitValueOfTraitTypeOf[_nextTokenIdBeforeMint + i][
                        traitTypes[j]
                    ] = _traits[i][j];
                }
            }
        }
    }

    function getIpfsHashOf(
        uint256 _tokenId
    ) public view returns (IpfsHash memory) {
        return ipfsHashOf[_tokenId];
    }

    function decodeIpfsHash(
        uint256 _tokenId
    ) private view returns (string memory) {
        string memory output = string(
            abi.encodePacked(
                ipfsHashOf[_tokenId].part1,
                ipfsHashOf[_tokenId].part2
            )
        );
        return output;
    }

    function recoverSigner(
        address _address,
        uint256 _roleId,
        bytes memory _signature
    ) private view returns (address) {
        bytes32 hash = keccak256(
            abi.encodePacked(_address, _roleId, activeSession)
        );
        bytes32 messageDigest = keccak256(
            abi.encodePacked("\x19Ethereum Signed Message:\n32", hash)
        );
        return ECDSA.recover(messageDigest, _signature);
    }

    function getTokenImageIpfsUrl(
        uint256 _tokenId
    ) private view returns (string memory) {
        string memory cid = decodeIpfsHash(_tokenId);
        return string(abi.encodePacked("ipfs://", cid));
    }

    function createHashFromTraits(
        bytes32[] calldata _traits
    ) private view returns (bytes32) {
        string memory attributes = "";
        if (_traits.length == 0) revert InvalidArgs();
        if (_traits.length != traitTypes.length) revert InvalidArgs();

        unchecked {
            for (uint256 i = 0; i < _traits.length; i++) {
                attributes = string(
                    abi.encodePacked(attributes, traitTypes[i], _traits[i])
                );
            }
        }
        bytes32 hash = keccak256(abi.encodePacked(attributes));
        return hash;
    }

    function getTokenAttributes(
        uint256 _tokenId
    ) public view returns (string memory) {
        string memory attributes = "[";

        for (uint256 i = 0; i < traitTypes.length - 1; i++) {
            attributes = string(
                abi.encodePacked(
                    attributes,
                    '{"trait_type": "',
                    traitTypes[i],
                    '", "value": "',
                    traitValueOfTraitTypeOf[_tokenId][traitTypes[i]],
                    '"}, '
                )
            );
        }

        attributes = string(
            abi.encodePacked(
                attributes,
                '{"trait_type": "',
                traitTypes[traitTypes.length - 1],
                '", "value": "',
                traitValueOfTraitTypeOf[_tokenId][
                    traitTypes[traitTypes.length - 1]
                ],
                '"}]'
            )
        );

        return attributes;
    }

    function getContractData()
        external
        view
        returns (
            string memory,
            string memory,
            string memory,
            uint256,
            bool,
            bool,
            bool,
            bool,
            bytes32[] memory
        )
    {
        return (
            CONTRACT_NAME,
            TOKEN_NAME,
            TOKEN_SYMBOL,
            TOTAL_SUPPLY,
            isMintLive,
            duplicateVerification,
            isUnlimited,
            isTraitsFrozen,
            traitTypes
        );
    }

    function getSupplyData(
        address _address,
        uint256 _roleId
    ) external view returns (uint256, uint256, uint256) {
        uint256 tokensLeftInTotal = tokensLeft();
        uint256 tokensLeftInActiveSession = tokensLeftInSession(activeSession);
        uint256 tokensLeftForAddress = tokensLeftForAddressInRoleInActiveSession(
                _address,
                _roleId
            );

        return (
            tokensLeftInTotal,
            tokensLeftInActiveSession,
            tokensLeftForAddress
        );
    }

    function isInArray(
        uint256[] memory _arr,
        uint256 _val
    ) private pure returns (bool) {
        uint256 len = _arr.length;
        for (uint256 i = 0; i < len; i++) if (_arr[i] == _val) return true;
        return false;
    }

    // https://github.com/oraclize/ethereum-api/blob/b42146b063c7d6ee1358846c198246239e9360e8/oraclizeAPI_0.4.25.sol
    function toString(uint256 _val) internal pure returns (string memory) {
        if (_val == 0) {
            return "0";
        }
        uint256 temp = _val;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (_val != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(_val % 10)));
            _val /= 10;
        }
        return string(buffer);
    }

    /// Constructor
    constructor(
        address _tockableAddress,
        address _signerAddress
    ) ERC721A(CONTRACT_NAME, TOKEN_SYMBOL) Ownable(msg.sender) {
        tockableAddress = _tockableAddress;
        signerAddress = _signerAddress;
    }
}
