package library

import bytes "bytes"
import hex "encoding/hex"
import errors "errors"
import io "io"
import big "math/big"
import rand "crypto/rand"
import sign "golang.org/x/crypto/nacl/sign"
//@ import . "dh-gobra/verification/bytes"
//@ import . "dh-gobra/verification/place"
//@ import . "dh-gobra/verification/iospec"
//@ import am "dh-gobra/verification/term"
//@ import tm "dh-gobra/verification/util"

const NonceLength = 24

// based on RFC 3526
const GroupGenerator = 2
const GroupSizeString = "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF"
const DHHalfKeyLength = 256

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ requires token(t) && e_Setup_Alice(t, rid)
//@ ensures  err == nil ==> acc(Mem(skA), 1/4) && acc(Mem(pkB), 1/4)
//@ ensures  err == nil ==> gamma(tm.integer32(idA)) == gamma(old(get_e_Setup_Alice_r1(t, rid)))
//@ ensures  err == nil ==> gamma(tm.integer32(idB)) == gamma(old(get_e_Setup_Alice_r2(t, rid)))
//@ ensures  err == nil ==> Abs(skA) == gamma(old(get_e_Setup_Alice_r3(t, rid)))
//@ ensures  err == nil ==> Abs(pkB) == gamma(tm.pk(old(get_e_Setup_Alice_r4(t, rid))))
//@ ensures  err == nil ==> token(t1) && t1 == old(get_e_Setup_Alice_placeDst(t, rid))
// assumptions (PA axiom applied locally):
//@ ensures err == nil ==> (gamma(old(get_e_Setup_Alice_r1(t, rid))) == gamma(tm.integer32(idA)) ==> old(get_e_Setup_Alice_r1(t, rid)) == tm.integer32(idA))
//@ ensures err == nil ==> (gamma(old(get_e_Setup_Alice_r2(t, rid))) == gamma(tm.integer32(idB)) ==> old(get_e_Setup_Alice_r2(t, rid)) == tm.integer32(idB))
func (l *LibState) Setup(/*@ ghost t Place, ghost rid tm.Term @*/) (idA, idB uint32, skA, pkB []byte, err error /*@, ghost t1 Place @*/) {
	idA = l.idA
	idB = l.idB
	skA = l.skA[:]
	pkB = l.pkB[:]
	err = nil
	return
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ requires token(t) && e_FrFact(t, rid)
//@ ensures  err == nil ==> Mem(nonce)
//@ ensures  err == nil ==> Abs(nonce) == gamma(old(get_e_FrFact_r1(t, rid)))
//@ ensures  err == nil ==> token(t1) && t1 == old(get_e_FrFact_placeDst(t, rid))
func (l *LibState) CreateNonce(/*@ ghost t Place, ghost rid tm.Term @*/) (nonce []byte, err error /*@, ghost t1 Place @*/) {
	var nonceBuf [NonceLength]byte
	io.ReadFull(rand.Reader, nonceBuf[:])
	return nonceBuf[:], nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(exp), 1/16)
//@ ensures err == nil ==> Mem(res)
// arg is big-endian
func (l *LibState) expModWithIntBase(base *big.Int, exp []byte) (res []byte, err error) {
	// prepare mod argument:
	groupSizeBytes, err := hex.DecodeString(GroupSizeString)
	if err != nil {
		return nil, err
	}
	mod := big.NewInt(0)
	mod.SetBytes(groupSizeBytes)

	// prepare exp argument:
	expInt := big.NewInt(0)
	expInt.SetBytes(exp)

	// perform calculation:
	r := big.NewInt(0)
	r.Exp(base, expInt, mod)

	// extract result:
	var resBuf [DHHalfKeyLength]byte
	r.FillBytes(resBuf[:])
	return resBuf[:], nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(base), 1/16) && acc(Mem(exp), 1/16)
//@ ensures err == nil ==> Mem(res)
// args are big-endian
func (l *LibState) expMod(base, exp []byte) (res []byte, err error) {
	// prepare mod argument:
	baseInt := big.NewInt(0)
	baseInt.SetBytes(base)
	return l.expModWithIntBase(baseInt, exp)
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(exp), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == expB(generatorB(), Abs(exp))
// arg is big-endian
func (l *LibState) DhExp(exp []byte) (res []byte, err error) {
	g := big.NewInt(GroupGenerator)
	return l.expModWithIntBase(g, exp)
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(dhSecret), 1/16) && acc(Mem(dhHalfKey), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == expB(Abs(dhHalfKey), Abs(dhSecret))
// args are big-endian
func (l *LibState) DhSharedSecret(dhSecret, dhHalfKey []byte) (res []byte, err error) {
	return l.expMod(dhHalfKey, dhSecret)
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(data), 1/16) && acc(Mem(sk), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == signB(Abs(data), Abs(sk))
func (l *LibState) Sign(data []byte, sk []byte) (res []byte, err error) {
	if len(sk) != 64 {
		return nil, errors.New("invalid secret key")
	}
	var skBuf [64]byte
	copy(skBuf[:], sk)

	var out []byte
	// not that the (64 bytes) signature is prepended to the plaintext
	return sign.Sign(out, data, &skBuf), nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(signedData), 1/16)
//@ requires acc(Mem(pk), 1/16)
//@ requires Abs(pk) == gamma(tm.pk(skT))
//@ ensures  acc(Mem(pk), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(signedData) == signB(Abs(res), gamma(skT))
func (l *LibState) Open(signedData []byte, pk []byte /*@, ghost skT tm.Term @*/) (res []byte, err error) {
	if len(pk) != 32 {
		return nil, errors.New("invalid public key")
	}
	var pkBuf [32]byte
	copy(pkBuf[:], pk)
	
	var out []byte
	data, success := sign.Open(out, signedData, &pkBuf)
	if success {
		return data, nil
	} else {
		return nil, errors.New("signature check has failed")
	}
}

//@ trusted
//@ requires acc(Mem(s1), 1/16) && acc(Mem(s2), 1/16)
//@ ensures  res == (Abs(s1) == Abs(s2))
//@ pure
func Equals(s1, s2 []byte) (res bool) {
	return bytes.Equal(s1, s2)
}
