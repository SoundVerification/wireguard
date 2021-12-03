package library

import (
	device "wireguard-gobra/wireguard/device"
	tai64n "wireguard-gobra/wireguard/tai64n"
)

//@ import . "wireguard-gobra/wireguard/verification/bytes"
//@ import . "wireguard-gobra/wireguard/verification/iospec"
//@ import . "wireguard-gobra/wireguard/verification/place"
//@ import . "wireguard-gobra/wireguard/verification/term"

//@ requires token(t) && e_init0I(t, rid)
//@ requires acc(Mem(prologue), 1/16) && acc(Mem(info), 1/16)
//@ ensures  acc(Mem(prologue), 1/16) && acc(Mem(info), 1/16)
//@ ensures  Mem(b3) && Mem(b4)
//@ ensures  ok ==> integer32B(b1) == gamma(old(get_e_init0I_m1(t, rid)))
//@ ensures  ok ==> integer32B(b2) == gamma(old(get_e_init0I_m2(t, rid)))
//@ ensures  ok ==> Abs(b3) == gamma(old(get_e_init0I_m3(t, rid)))
//@ ensures  ok ==> Abs(b4) == gamma(old(get_e_init0I_m4(t, rid)))
//@ ensures  ok ==> token(t1) && t1 == old(get_e_init0I_t1(t, rid))
// assumptions (PA axiom applied locally):
//@ ensures ok ==> (gamma(old(get_e_init0I_m1(t, rid))) == gamma(integer32(b1)) ==> old(get_e_init0I_m1(t, rid)) == integer32(b1))
//@ ensures ok ==> (gamma(old(get_e_init0I_m2(t, rid))) == gamma(integer32(b2)) ==> old(get_e_init0I_m2(t, rid)) == integer32(b2))
//@ ensures ok ==> (gamma(old(get_e_init0I_m3(t, rid))) == gamma(prologueTerm()) ==> old(get_e_init0I_m3(t, rid)) == prologueTerm())
//@ ensures ok ==> (gamma(old(get_e_init0I_m4(t, rid))) == gamma(infoTerm()) ==> old(get_e_init0I_m4(t, rid)) == infoTerm())
func GetInit0I(a uint32, b uint32, prologue ByteString, info ByteString /*@, ghost t Place, ghost rid Term @*/) (ok bool, b1 uint32, b2 uint32, b3 ByteString, b4 ByteString /*@, ghost t1 Place @*/) {
	ok = true
	b1 = a
	b2 = b
	prologueCopy := NewByteString(len(prologue))
	copy(prologueCopy, prologue)
	b3 = prologueCopy
	infoCopy := NewByteString(len(info))
	copy(infoCopy, info)
	b4 = infoCopy
	return
}

//@ requires token(t) && e_resp0R(t, rid)
//@ requires acc(Mem(prologue), 1/16) && acc(Mem(info), 1/16)
//@ ensures  acc(Mem(prologue), 1/16) && acc(Mem(info), 1/16)
//@ ensures  Mem(b3) && Mem(b4)
//@ ensures  ok ==> integer32B(b1) == gamma(old(get_e_resp0R_m1(t, rid)))
//@ ensures  ok ==> integer32B(b2) == gamma(old(get_e_resp0R_m2(t, rid)))
//@ ensures  ok ==> Abs(b3) == gamma(old(get_e_resp0R_m3(t, rid)))
//@ ensures  ok ==> Abs(b4) == gamma(old(get_e_resp0R_m4(t, rid)))
//@ ensures  ok ==> token(t1) && t1 == old(get_e_resp0R_t1(t, rid))
// assumptions (PA axiom applied locally):
//@ ensures ok ==> (gamma(old(get_e_resp0R_m1(t, rid))) == gamma(integer32(b1)) ==> old(get_e_resp0R_m1(t, rid)) == integer32(b1))
//@ ensures ok ==> (gamma(old(get_e_resp0R_m2(t, rid))) == gamma(integer32(b2)) ==> old(get_e_resp0R_m2(t, rid)) == integer32(b2))
//@ ensures ok ==> (gamma(old(get_e_resp0R_m3(t, rid))) == gamma(prologueTerm()) ==> old(get_e_resp0R_m3(t, rid)) == prologueTerm())
//@ ensures ok ==> (gamma(old(get_e_resp0R_m4(t, rid))) == gamma(infoTerm()) ==> old(get_e_resp0R_m4(t, rid)) == infoTerm())
func GetResp0R(a uint32, b uint32, prologue ByteString, info ByteString /*@, ghost t Place, ghost rid Term @*/) (ok bool, b1 uint32, b2 uint32, b3 ByteString, b4 ByteString /*@, ghost t1 Place @*/) {
	ok = true
	b1 = a
	b2 = b
	prologueCopy := NewByteString(len(prologue))
	copy(prologueCopy, prologue)
	b3 = prologueCopy
	infoCopy := NewByteString(len(info))
	copy(infoCopy, info)
	b4 = infoCopy
	return
}

//@ requires acc(LibMem(libState), 1/16)
//@ requires token(t) && e_LtK(t, rid)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(b2)
//@ ensures  ok ==> integer32B(b1) == gamma(old(get_e_LtK_m1(t, rid)))
//@ ensures  ok ==> Abs(b2) == gamma(old(get_e_LtK_m2(t, rid)))
//@ ensures  ok ==> token(t1) && t1 == old(get_e_LtK_t1(t, rid))
// assumptions (PA axiom applied locally):
//@ ensures ok ==> (gamma(old(get_e_LtK_m1(t, rid))) == gamma(integer32(b1)) ==> old(get_e_LtK_m1(t, rid)) == integer32(b1))
func (libState *LibraryState) GetLtKBio(own uint32 /*@, ghost t Place, ghost rid Term @*/) (ok bool, b1 uint32, b2 ByteString /*@, ghost t1 Place @*/) {
	ok = true
	b1 = own
	b2 = libState.dev.StaticIdentity.PrivateKey[:]
	return
}

//@ requires acc(LibMem(libState), 1/16)
//@ requires token(t) && e_LtpK(t, rid)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(b2)
//@ ensures  ok ==> integer32B(b1) == gamma(old(get_e_LtpK_m1(t, rid)))
//@ ensures  ok ==> Abs(b2) == gamma(old(get_e_LtpK_m2(t, rid)))
//@ ensures  ok ==> token(t1) && t1 == old(get_e_LtpK_t1(t, rid))
// assumptions (PA axiom applied locally):
//@ ensures ok ==> (gamma(old(get_e_LtpK_m1(t, rid))) == gamma(integer32(b1)) ==> old(get_e_LtpK_m1(t, rid)) == integer32(b1))
func (libState *LibraryState) GetLtpKBio(other uint32 /*@, ghost t Place, ghost rid Term @*/) (ok bool, b1 uint32, b2 ByteString /*@, ghost t1 Place @*/) {
	ok = true
	b1 = other
	b2 = libState.dev.Peer.Handshake.RemoteStatic[:]
	return
}

//@ requires acc(LibMem(libState), 1/16)
//@ requires token(t) && e_PsK(t, rid)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(b3)
//@ ensures  ok ==> integer32B(b1) == gamma(old(get_e_PsK_m1(t, rid)))
//@ ensures  ok ==> integer32B(b2) == gamma(old(get_e_PsK_m2(t, rid)))
//@ ensures  ok ==> Abs(b3) == gamma(old(get_e_PsK_m3(t, rid)))
//@ ensures  ok ==> token(t1) && t1 == old(get_e_PsK_t1(t, rid))
// assumptions (PA axiom applied locally):
//@ ensures ok ==> (gamma(old(get_e_PsK_m1(t, rid))) == gamma(integer32(b1)) ==> old(get_e_PsK_m1(t, rid)) == integer32(b1))
//@ ensures ok ==> (gamma(old(get_e_PsK_m2(t, rid))) == gamma(integer32(b2)) ==> old(get_e_PsK_m2(t, rid)) == integer32(b2))
func (libState *LibraryState) GetPsKBio(a uint32, b uint32 /*@, ghost t Place, ghost rid Term @*/) (ok bool, b1 uint32, b2 uint32, b3 ByteString /*@, ghost t1 Place @*/) {
	ok = true
	b1 = a
	b2 = b
	b3 = libState.dev.Peer.Handshake.PresharedKey[:]
	return
}

//  && len(key) == 32
//@ requires token(t) && e_fr(t, rid)
//@ ensures  ok ==> Mem(key) && Size(key) == 32
//@ ensures  ok ==> token(t1) && t1 == old(get_e_fr_t1(t, rid))
//@ ensures  ok ==> Abs(key) == gamma(old(get_e_fr_n(t, rid)))
func NewPrivateKey( /*@ ghost t Place, ghost rid Term @*/ ) (key ByteString, ok bool /*@, ghost t1 Place @*/) {
	sk, err := device.NewPrivateKey()
	if err == nil {
		key = sk[:]
		ok = true
	}
	return
}

// ensures len(res) == 12
//@ requires token(t) && e_Timestamp(t, rid)
//@ ensures  Mem(res) && Size(res) == 12
//@ ensures  token(t1) && t1 == old(get_e_Timestamp_t1(t, rid))
//@ ensures  Abs(res) == gamma(old(get_e_Timestamp_m(t, rid)))
func Timestamp( /*@ ghost t Place, ghost rid Term @*/ ) (res ByteString /*@, ghost t1 Place @*/) {
	var array [12]byte = tai64n.Now()
	return array[:]
}

//@ requires acc(LibMem(libState), 1/16) && Mem(msg)
//@ requires token(t) && e_MAC(t, rid)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(msg) && Size(msg) == old(Size(msg))
//@ ensures  mac1 == gamma(old(get_e_MAC_m(t, rid)))
//@ ensures  token(t1) && t1 == old(get_e_MAC_t1(t, rid))
//@ ensures  (old(Abs(msg)) == tuple7B(getFirstB(b),getSecondB(b),getThirdB(b),getForthB(b),getFifthB(b),zeroStringB(16),zeroStringB(16)) ==> Abs(msg) == tuple7B(getFirstB(b),getSecondB(b),getThirdB(b),getForthB(b),getFifthB(b),mac1,zeroStringB(16)))
func (libState *LibraryState) AddMac1(msg ByteString /*@, ghost b Bytes, ghost t Place, ghost rid Term @*/) /*@ (mac1 Bytes, t1 Place) @*/ {
	// first, compute key that will be used for MACing (could be precomputed)
	// note that the peer's public key (instead of own one) is used in the derivation
	var macKey [KeySize]byte
	ComputeHash(macKey[:], []byte(device.WGLabelMAC1), libState.dev.Peer.Handshake.RemoteStatic[:])

	// set MAC1
	startMac1 := len(msg) - 2*MacSize
	mac1Slice := msg[startMac1 : startMac1+MacSize]
	ComputeMac(mac1Slice, macKey[:], msg[:startMac1]) // MAC all request fields except MAC1 and MAC2
	tmpMac1 := make([]byte, MacSize)
	copy(tmpMac1, mac1Slice)
	//@ mac1 = tmpMac1
	return
}

//@ requires acc(LibMem(libState), 1/16) && Mem(msg)
//@ requires token(t) && e_MAC(t, rid)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(msg) && Size(msg) == old(Size(msg))
//@ ensures  mac2 == gamma(old(get_e_MAC_m(t, rid)))
//@ ensures  token(t1) && t1 == old(get_e_MAC_t1(t, rid))
//@ ensures  (old(Abs(msg)) == tuple7B(getFirstB(b),getSecondB(b),getThirdB(b),getForthB(b),getFifthB(b),getSixthB(b),zeroStringB(16)) ==> Abs(msg) == tuple7B(getFirstB(b),getSecondB(b),getThirdB(b),getForthB(b),getFifthB(b),getSixthB(b),mac2))
func (libState *LibraryState) AddMac2(msg ByteString /*@, ghost b Bytes, ghost t Place, ghost rid Term @*/) /*@ (mac2 Bytes, t1 Place ) @*/ {
	// MAC2 is not set as we assume that the system is not under load
	startMac2 := len(msg) - MacSize
	mac2Slice := msg[startMac2:]
	tmpMac2 := make([]byte, MacSize)
	copy(tmpMac2, mac2Slice)
	//@ mac2 = tmpMac2
	return
}

//@ requires token(t) && e_Counter(t, rid)
//@ ensures  token(t1) && t1 == old(get_e_Counter_t1(t, rid)) && integer64B(res) == gamma(old(get_e_Counter_n(t, rid)))
// assumptions (PA axiom applied locally):
//@ ensures  gamma(old(get_e_Counter_n(t, rid))) == gamma(integer64(res)) ==> old(get_e_Counter_n(t, rid)) == integer64(res)
func GetCounter(counter uint64 /*@, ghost t Place, ghost rid Term @*/) (res uint64 /*@, ghost t1 Place @*/) {
	return counter
}
