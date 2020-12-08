// https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki
package bip39

import (
	"crypto/rand"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/binary"
	"errors"
	"fmt"
	"github.com/sea-project/crypto-bip-bip39/wordlists"
	"math/big"
	"strings"
	"golang.org/x/crypto/pbkdf2"
)

var (
	last11BitsMask  = big.NewInt(2047)
	shift11BitsMask = big.NewInt(2048)
	bigOne          = big.NewInt(1)
	bigTwo          = big.NewInt(2)

	wordLengthChecksumMasksMapping = map[int]*big.Int{
		12: big.NewInt(15),
		15: big.NewInt(31),
		18: big.NewInt(63),
		21: big.NewInt(127),
		24: big.NewInt(255),
	}
	wordLengthChecksumShiftMapping = map[int]*big.Int{
		12: big.NewInt(16),
		15: big.NewInt(8),
		18: big.NewInt(4),
		21: big.NewInt(2),
	}
	wordList []string
	wordMap map[string]int
)

// 定义错误
var (
	ErrInvalidMnemonic = errors.New("Invalid mnenomic")
	ErrEntropyLengthInvalid = errors.New("Entropy length must be [128, 256] and a multiple of 32")
	ErrValidatedSeedLengthMismatch = errors.New("Seed length does not match validated seed length")
	ErrChecksumIncorrect = errors.New("Checksum incorrect")
)

// 初始化bip39助记词规范
func init() {
	SetWordList(wordlists.English)
}

// SetWordList
func SetWordList(list []string) {
	wordList = list
	wordMap = map[string]int{}
	for i, v := range wordList {
		wordMap[v] = i
	}
}

// NewEntropy 初始化熵 128-256位
func NewEntropy(bitSize int) ([]byte, error) {
	err := validateEntropyBitSize(bitSize)
	if err != nil {
		return nil, err
	}

	entropy := make([]byte, bitSize/8)
	_, err = rand.Read(entropy)
	return entropy, err
}

// NewMnemonic 根据熵计算助记词字符串
func NewMnemonic(entropy []byte) (string, error) {

	entropyBitLength := len(entropy) * 8
	checksumBitLength := entropyBitLength / 32
	sentenceLength := (entropyBitLength + checksumBitLength) / 11
	err := validateEntropyBitSize(entropyBitLength)
	if err != nil {
		return "", err
	}

	entropy, err = addChecksum(entropy)
	if err != nil {
		return "", err
	}

	entropyInt := new(big.Int).SetBytes(entropy)
	words := make([]string, sentenceLength)
	word := big.NewInt(0)
	for i := sentenceLength - 1; i >= 0; i-- {
		word.And(entropyInt, last11BitsMask)
		entropyInt.Div(entropyInt, shift11BitsMask)
		wordBytes := padByteSlice(word.Bytes(), 2)
		words[i] = wordList[binary.BigEndian.Uint16(wordBytes)]
	}
	return strings.Join(words, " "), nil
}

// NewSeed
func NewSeed(mnemonic string, password string) []byte {
	return pbkdf2.Key([]byte(mnemonic), []byte("mnemonic"+password), 2048, 64, sha512.New)
}

// EntropyFromMnemonic 根据助记词反推熵
func EntropyFromMnemonic(mnemonic string) ([]byte, error) {
	mnemonicSlice, isValid := splitMnemonicWords(mnemonic)
	if !isValid {
		return nil, ErrInvalidMnemonic
	}

	b := big.NewInt(0)
	for _, v := range mnemonicSlice {
		index, ok := wordMap[v]
		if !ok {
			return nil, fmt.Errorf("word `%v` not found in reverse map", v)
		}
		var wordBytes [2]byte
		binary.BigEndian.PutUint16(wordBytes[:], uint16(index))
		b = b.Mul(b, shift11BitsMask)
		b = b.Or(b, big.NewInt(0).SetBytes(wordBytes[:]))
	}

	checksum := big.NewInt(0)
	checksumMask := wordLengthChecksumMasksMapping[len(mnemonicSlice)]
	checksum = checksum.And(b, checksumMask)
	b.Div(b, big.NewInt(0).Add(checksumMask, bigOne))

	entropy := b.Bytes()
	entropy = padByteSlice(entropy, len(mnemonicSlice)/3*4)

	entropyChecksumBytes, err := computeChecksum(entropy)
	if err != nil {
		return nil, err
	}

	entropyChecksum := big.NewInt(int64(entropyChecksumBytes[0]))
	if l := len(mnemonicSlice); l != 24 {
		checksumShift := wordLengthChecksumShiftMapping[l]
		entropyChecksum.Div(entropyChecksum, checksumShift)
	}
	if checksum.Cmp(entropyChecksum) != 0 {
		return nil, ErrChecksumIncorrect
	}
	return entropy, nil
}

// MnemonicToByteArray
func MnemonicToByteArray(mnemonic string, raw ...bool) ([]byte, error) {
	var (
		mnemonicSlice    = strings.Split(mnemonic, " ")
		entropyBitSize   = len(mnemonicSlice) * 11
		checksumBitSize  = entropyBitSize % 32
		fullByteSize     = (entropyBitSize-checksumBitSize)/8 + 1
		checksumByteSize = fullByteSize - (fullByteSize % 4)
	)

	if !IsMnemonicValid(mnemonic) {
		return nil, ErrInvalidMnemonic
	}

	checksummedEntropy := big.NewInt(0)
	modulo := big.NewInt(2048)
	for _, v := range mnemonicSlice {
		index := big.NewInt(int64(wordMap[v]))
		checksummedEntropy.Mul(checksummedEntropy, modulo)
		checksummedEntropy.Add(checksummedEntropy, index)
	}

	checksumModulo := big.NewInt(0).Exp(bigTwo, big.NewInt(int64(checksumBitSize)), nil)
	rawEntropy := big.NewInt(0).Div(checksummedEntropy, checksumModulo)

	rawEntropyBytes := padByteSlice(rawEntropy.Bytes(), checksumByteSize)
	checksummedEntropyBytes := padByteSlice(checksummedEntropy.Bytes(), fullByteSize)

	unpaddedChecksumedBytes, err := addChecksum(rawEntropyBytes)
	if err != nil {
		return nil, err
	}

	newChecksummedEntropyBytes := padByteSlice(unpaddedChecksumedBytes, fullByteSize)
	if !compareByteSlices(checksummedEntropyBytes, newChecksummedEntropyBytes) {
		return nil, ErrChecksumIncorrect
	}

	if len(raw) > 0 && raw[0] {
		return rawEntropyBytes, nil
	}
	return checksummedEntropyBytes, nil
}

// NewSeedWithMnemonic 根据助记词直接计算随机种子
func NewSeedWithMnemonic(mnemonic string, password string) ([]byte, error) {
	_, err := MnemonicToByteArray(mnemonic)
	if err != nil {
		return nil, err
	}
	return NewSeed(mnemonic, password), nil
}

// IsMnemonicValid 助记词校验
func IsMnemonicValid(mnemonic string) bool {

	words := strings.Fields(mnemonic)
	wordCount := len(words)
	if wordCount%3 != 0 || wordCount < 12 || wordCount > 24 {
		return false
	}

	for _, word := range words {
		if _, ok := wordMap[word]; !ok {
			return false
		}
	}
	return true
}

// addChecksum 增加32位校验码
func addChecksum(data []byte) ([]byte, error) {

	hash, err := computeChecksum(data)
	if err != nil {
		return nil, err
	}
	firstChecksumByte := hash[0]

	checksumBitLength := uint(len(data) / 4)
	dataBigInt := new(big.Int).SetBytes(data)
	for i := uint(0); i < checksumBitLength; i++ {
		dataBigInt.Mul(dataBigInt, bigTwo)
		if firstChecksumByte&(1<<(7-i)) > 0 {
			dataBigInt.Or(dataBigInt, bigOne)
		}
	}
	return dataBigInt.Bytes(), nil
}

// computeChecksum 计算校验码
func computeChecksum(data []byte) ([]byte, error) {
	hasher := sha256.New()
	_, err := hasher.Write(data)
	if err != nil {
		return nil, err
	}
	return hasher.Sum(nil), nil
}

// validateEntropyBitSize 熵验证
func validateEntropyBitSize(bitSize int) error {
	if (bitSize%32) != 0 || bitSize < 128 || bitSize > 256 {
		return ErrEntropyLengthInvalid
	}
	return nil
}

// padByteSlice
func padByteSlice(slice []byte, length int) []byte {
	offset := length - len(slice)
	if offset <= 0 {
		return slice
	}
	newSlice := make([]byte, length)
	copy(newSlice[offset:], slice)
	return newSlice
}

// compareByteSlices
func compareByteSlices(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// splitMnemonicWords
func splitMnemonicWords(mnemonic string) ([]string, bool) {
	words := strings.Fields(mnemonic)
	numOfWords := len(words)
	if numOfWords%3 != 0 || numOfWords < 12 || numOfWords > 24 {
		return nil, false
	}
	return words, true
}
