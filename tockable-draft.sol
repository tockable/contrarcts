//SPDX-License-Identifier: Unlicense

pragma solidity ^0.8.0;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import "erc721a/contracts/extensions/ERC721AQueryable.sol";

contract TockableDrop is ERC721AQueryable, Ownable, ReentrancyGuard {
    /// Errors
    error InvalidArgs();
    error MintIsNotLive();
    error MoreThanAllowed();
    error MoreThanAvailable();
    error NotElligible();
    error NotEnoughEth();
    error UnAuthorized();
    error WithdrawFailed();
    error TritsIsFrozen();
    error IsTakenBefore();

    /// Events
    event ethReceived(address, uint256);

    /// Structs
    struct IpfsHash {
        bytes32 part1;
        bytes32 part2;
    }

    struct Trait {
        bytes32 trait_type;
        bytes32 value;
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
    uint256 activeSession;

    /// Mappings
    mapping(uint256 => uint256) mintedInSessionById;
    mapping(bytes => uint256) mintedBySignature;
    mapping(uint256 => Role) getRoleById;
    mapping(uint256 => Session) getSessionById;
    mapping(uint256 => IpfsHash) ipfsHashOf;
    mapping(uint256 => mapping(bytes32 => bytes32)) traitValueOfTraitTypeOf;
    mapping(bytes32 => bool) isTaken;

    /// setters
    function setRoles(Role[] calldata _roles) external onlyOwner {
        if (_roles.length == 0) revert InvalidArgs();
        unchecked {
            for (uint256 i = 0; i < _roles.length; i++) {
                getRoleById[i] = _roles[i];
            }
        }
    }

    function setSessions(Session[] calldata _sessions) external onlyOwner {
        if (_sessions.length == 0) revert InvalidArgs();
        unchecked {
            for (uint256 i = 0; i < _sessions.length; i++) {
                getSessionById[i] = _sessions[i];
            }
        }
    }

    function setMintIsLive(bool _status) public onlyOwner {
        isMintLive = _status;
    }

    function setActiveSession(uint256 _activeSession) external onlyOwner {
        if (!isMintLive) setMintIsLive(true);
        activeSession = _activeSession;
    }

    function addTraitTypes(bytes32[] calldata _traitTypes) external onlyOwner {
        if (isTraitsFrozen) revert TritsIsFrozen();
        for (uint256 i = 0; i < _traitTypes.length; i++) {
            traitTypes.push(_traitTypes[i]);
        }
        isTraitsFrozen = true;
    }

    /// Mint
    function mint(
        uint256 _quantity,
        IpfsHash[] calldata _cids,
        bytes calldata _signature,
        uint256 _roleId,
        Trait[][] calldata _traits
    ) external payable nonReentrant {
        if (!isMintLive) revert MintIsNotLive();
        if (_cids.length != _quantity) revert InvalidArgs();
        if (_cids.length != _traits.length) revert InvalidArgs();
        if (_traits.length != traitTypes.length) revert InvalidArgs();

        isTokenLeftInTotal(_quantity);
        isTokenLeftInActiveSession(_quantity);
        isElligible(_roleId);
        isSignatureValid(msg.sender, _roleId, _signature);
        isSignatureHasQuota(_signature, _roleId, _quantity);

        if (duplicateVerification) {
            unchecked {
                for (uint256 i = 0; i < _traits.length; i++) {
                    bytes32 tokenHash = createHashFromTraits(_traits[i]);
                    if (isTaken[tokenHash]) revert IsTakenBefore();
                    isTaken[tokenHash] = true;
                }
            }
        }

        uint256 payAmount = (getRoleById[_roleId].price + BASE_FEE) * _quantity;
        if (msg.value < payAmount) revert NotEnoughEth();

        uint256 nextTokenId = _nextTokenId();
        unchecked {
            for (uint256 i = 0; i < _quantity; i++) {
                setIpfsHash(nextTokenId + i, _cids[i]);
                for (uint256 j = 0; j < _traits[i].length; j++) {
                    traitValueOfTraitTypeOf[nextTokenId + i][
                        _traits[i][j].trait_type
                    ] = _traits[i][j].value;
                }
            }
        }
        _safeMint(msg.sender, _quantity);

        mintedInSessionById[activeSession] =
            mintedInSessionById[activeSession] +
            _quantity;

        mintedBySignature[_signature] =
            mintedBySignature[_signature] +
            _quantity;

        uint256 tockableFee = _quantity * BASE_FEE;
        withdrawEth(payable(tockableAddress), tockableFee);
    }

    function ownerMint(address _to, uint256 _quantity) external onlyOwner {
        isTokenLeftInTotal(_quantity);
        _safeMint(_to, _quantity);
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

    function isSignatureHasQuota(
        bytes memory _signature,
        uint256 _roleId,
        uint256 _quantity
    ) private view {
        if (
            mintedBySignature[_signature] + _quantity >
            getRoleById[_roleId].maxAllowedMint
        ) {
            revert MoreThanAllowed();
        }
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
        uint256[] storage allowedRolesIdsInCurrentSession = getSessionById[
            activeSession
        ].allowedRoles;
        if (!isInArray(allowedRolesIdsInCurrentSession, _roleId)) {
            revert NotElligible();
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
            abi.encodePacked('"image": "', getTokenImageIpfsUrl(tokenId), '", ')
        );
        metadata = string(
            abi.encodePacked('"attributes": ', getTokenAttributes(tokenId), "}")
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

    receive() external payable {
        emit ethReceived(msg.sender, msg.value);
    }

    /// Helpers & Utils
    function tokensLeft() public view returns (uint256) {
        return TOTAL_SUPPLY - _totalMinted();
    }

    function tokensLeftInSession(uint256 _id) public view returns (uint256) {
        return getSessionById[_id].allocation - mintedInSessionById[_id];
    }

    function setIpfsHash(
        uint256 _tokenId,
        IpfsHash calldata _ipfsHash
    ) private {
        ipfsHashOf[_tokenId] = _ipfsHash;
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
        Trait[] calldata _traits
    ) private pure returns (bytes32) {
        string memory attributes = "";

        for (uint256 i = 0; i < _traits.length; i++) {
            attributes = string(
                abi.encodePacked(
                    attributes,
                    _traits[i].trait_type,
                    _traits[i].value
                )
            );
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

    function isInArray(
        uint256[] storage _arr,
        uint256 _val
    ) private view returns (bool) {
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
