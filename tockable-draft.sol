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
    error MoreThanAvailable();
    error MoreThanMaxMintAllowed();
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
    uint256 private constant BASE_FEE = 1_000_000_000_000_000_000;
    string private constant TOKEN_NAME = "tockable";
    string private constant TOKEN_SYMBOL = "TCKBLE";

    /// Parameters
    address private tockableAddress;
    address private signerAddress;
    uint256 public maxMintPerWallet = 2;
    uint256 public PRICE = 2_000_000_000_000_000_000;
    bool public mintIsLive = false;

    /// Mappings
    mapping(uint256 => IpfsHash) ipfsHashOf;

    /// Owner setters
    function setPrice(uint256 _price) external onlyOwner {
        PRICE = _price;
    }

    function setMintIsLive(bool _status) external onlyOwner {
        mintIsLive = _status;
    }

    function setMaxMintPerWallet(uint256 _maxMintPerWallet) external onlyOwner {
        maxMintPerWallet = _maxMintPerWallet;
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
        bytes calldata _signature
    ) external payable nonReentrant {
        if (!mintIsLive) revert MintIsNotLive();
        if (_quantity > maxMintPerWallet) revert MoreThanMaxMintAllowed();
        if (_cids.length != _quantity) revert InvalidArgs();

        isTokenLeft(_quantity);
        isSignatureValid(_hash, _signature);

        uint256 payAmount = (PRICE + BASE_FEE) * _quantity;
        if (msg.value < payAmount) revert NotEnoughEth();

        uint256 nextTokenId = _nextTokenId();
        unchecked {
            for (uint256 i = 0; i < _cids.length; i++)
                setIpfsHash(nextTokenId + i, _cids[i]);
        }

        _safeMint(msg.sender, _quantity);

        uint256 tockableFee = _quantity * BASE_FEE;
        withdrawEth(payable(tockableAddress), tockableFee);
    }

    function ownerMint(address _to, uint256 _quantity) external onlyOwner {
        isTokenLeft(_quantity);
        _safeMint(_to, _quantity);
    }

    /// Helpers
    function tokensLeft() public view returns (uint256) {
        return TOTAL_SUPPLY - _totalMinted();
    }

    function isTokenLeft(uint256 _quantity) private view {
        if (tokensLeft() < _quantity) revert MoreThanAvailable();
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

    function isSignatureValid(
        bytes32 _hash,
        bytes memory _signature
    ) private view {
        if (recoverSigner(_hash, _signature) != signerAddress) revert UnAuthorized();
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
