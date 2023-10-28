//SPDX-License-Identifier: Unlicense

pragma solidity ^0.8.0;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import "@openzeppelin/contracts/utils/math/Math.sol";
import "@openzeppelin/contracts/utils/Strings.sol";
import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import "erc721a/contracts/extensions/ERC721AQueryable.sol";

contract TockDropNoWL is ERC721AQueryable, Ownable, ReentrancyGuard {
    /// Errors
    error InvalidPayment();
    error InvalidAmount();
    error InvalidArgs();
    error MintIsNotLive();
    error MoreThanAllowed();
    error MoreThanAvailable();
    error NotElligible();
    error NotEnoughEth();
    error UnAuthorized();
    error WithdrawFailed();

    /// Events
    event ethReceived(address, uint256);

    /// Structs
    struct IpfsHash {
        bytes32 part1;
        bytes32 part2;
    }

    /// Constants
    uint256 public constant TOTAL_SUPPLY = 10;
    uint256 private constant FIRST_TOKEN_ID = 1;
    uint256 private constant BASE_FEE = 0.0002 ether;
    string private constant TOKEN_NAME = "tockable";
    string private constant TOKEN_SYMBOL = "TCKBLE";

    /// Parameters
    address private tockableAddress;
    address private signerAddress;
    bool public mintIsLive = false;

    uint256 activeSession;

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

    /// Mappings
    mapping(uint256 => uint256) mintedInSessionById;
    mapping(bytes32 => uint256) mintedBySignature;
    mapping(uint256 => Role) getRoleById;
    mapping(uint256 => Session) getSessionById;
    mapping(uint256 => IpfsHash) ipfsHashOf;

    function setRoles(Role[] calldata _roles) external onlyOwner {
        unchecked {
            for (uint256 i = 0; i < _roles.length; i++) {
                getRoleById[i] = _roles[i];
            }
        }
    }

    function setSessions(Session[] calldata _session) external onlyOwner {
        unchecked {
            for (uint256 i = 0; i < _sessions.length; i++) {
                getSessionById[i] = _sessions[i];
            }
        }
    }

    function setMintIsLive(bool _status) external onlyOwner {
        mintIsLive = _status;
    }

    function setActiveSession(uint256 _activeSession) external onlyOwner {
        if (!mintIsLive) setMintIsLive(true);
        activeSession = _activeSession;
    }

    function getIpfsHashOf(
        uint256 _tokenId
    ) public view returns (IpfsHash memory) {
        return ipfsHashOf[_tokenId];
    }

    /// Mint
    function mint(
        uint256 _quantity,
        IpfsHash[] calldata _cids,
        bytes32 _hash,
        bytes calldata _signature,
        uint256 _roleId
    ) external payable nonReentrant {
        if (!mintIsLive) revert MintIsNotLive();
        if (_cids.length != _quantity) revert InvalidArgs();

        isTokensLeftInTotal(_quantity);
        isTokensLeftInActiveSession(_quantity);
        isSignatureValid(_hash, _signature);
        isSignatureAllowedToMint(_signature);

        uint256 payAmount = (getRoleById[_roleId].price + BASE_FEE) * _quantity;
        if (msg.value < payAmount) revert NotEnoughEth();

        uint256 nextTokenId = _nextTokenId();
        unchecked {
            for (uint256 i = 0; i < _cids.length; i++)
                setIpfsHash(nextTokenId + i, _cids[i]);
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
        isTokensLeftInTotal(_quantity);
        _safeMint(_to, _quantity);
    }

    /// Validators
    function isTokenLeftInTotal(uint256 _quantity) private view {
        if (tokensLeft() < _quantity) revert MoreThanAvailable();
    }

    function isTolenLeftInActiveSession(uint256 _quantity) private view {
        if (tokensLeftInSession(activeSession) < _quantity)
            revert MoreThanAvailable();
    }

    function isSignatureAllowedToMint(bytes32 _signature) private view {
        if (
            mintedBySignature[_signature] + _quantity >
            getRoleById[_roleId].maxMintAllowed
        ) {
            revert MoreThanAllowed();
        }
    }

    function isSignatureValid(
        bytes32 _hash,
        bytes memory _signature
    ) private view {
        if (recoverSigner(_hash, _signature) != signerAddress)
            revert UnAuthorized();
    }

    function isElligible(uint256 _roleId) private {
        uint256 allowedRolesIdsInCurrentSession = getSessionById[activeSession]
            .allowedRoles;
        if (!isInArray(allowedRolesIdsInCurrentSession, _roleId)) {
            revert NotElligible();
        }
    }

    /// Helpers & Utils
    function tokensLeft() public view returns (uint256) {
        return TOTAL_SUPPLY - _totalMinted();
    }

    function tokensLeftInSession(_id) public view returns (uint256) {
        return getSessionById[_id].allocation - mintedInSessionById[_id];
    }

    function setIpfsHash(
        uint256 _tokenId,
        IpfsHash calldata _ipfsHash
    ) private {
        ipfsHashOf[_tokenId] = _ipfsHash;
    }

    function decodeIpfsHash(
        uint256 tokenId
    ) private view returns (string memory) {
        string memory output = string(
            abi.encodePacked(
                ipfsHashOf[tokenId].part1,
                ipfsHashOf[tokenId].part2
            )
        );
        return output;
    }

    function recoverSigner(
        bytes32 _hash,
        bytes memory _signature
    ) private pure returns (address) {
        bytes32 messageDigest = keccak256(
            abi.encodePacked("\x19Ethereum Signed Message:\n32", _hash)
        );
        return ECDSA.recover(messageDigest, _signature);
    }

    function isInArray(
        uint256[] storage array,
        uint256 value
    ) private view returns (bool) {
        uint256 len = array.length;
        for (uint i = 0; i < len; i++) if (array[i] == value) return true;
        return false;
    }

    /// Metadata
    function tokenURI(
        uint256 tokenId
    ) public view virtual override(ERC721A, IERC721A) returns (string memory) {
        string memory cid = decodeIpfsHash(tokenId);
        return string(abi.encodePacked("ipfs://", cid));
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

    /// Constructor
    constructor(
        address _tockableAddress,
        address _signerAddress
    ) ERC721A(TOKEN_NAME, TOKEN_SYMBOL) Ownable(msg.sender) {
        tockableAddress = _tockableAddress;
        signerAddress = _signerAddress;
    }
}
