package responder

import lib "wireguard-gobra/wireguard/library"

//@ import by "wireguard-gobra/wireguard/verification/bytes"
//@ import tm "wireguard-gobra/wireguard/verification/util"
//@ import am "wireguard-gobra/wireguard/verification/term"
//@ import pub "wireguard-gobra/wireguard/verification/pub"
//@ import fresh "wireguard-gobra/wireguard/verification/fresh"

type Responder struct {
	LibState      lib.LibraryState
	HandshakeInfo lib.HandshakeArguments
	a, b          uint32
}

/*@

pred HandshakeMem1(hs *lib.Handshake) {
	acc(hs) && lib.Mem(hs.ChainHash) && lib.Mem(hs.ChainKey) && lib.Mem(hs.RemoteEphemeral) &&
	lib.Size(hs.ChainHash) == 32 && lib.Size(hs.ChainKey) == 32 && lib.Size(hs.RemoteEphemeral) == 32
}

pred HandshakeMem2(hs *lib.Handshake) {
	acc(hs) && lib.Mem(hs.ChainHash) && lib.Mem(hs.ChainKey) && lib.Mem(hs.LocalEphemeral) && lib.Mem(hs.RemoteEphemeral) &&
	lib.Size(hs.ChainHash) == 32 && lib.Size(hs.ChainKey) == 32 && lib.Size(hs.LocalEphemeral) == 32 && lib.Size(hs.RemoteEphemeral) == 32
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getNHash1(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in lib.Abs(hs.ChainHash)
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getNKey1(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in lib.Abs(hs.ChainKey)
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getEpkI1(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in lib.Abs(hs.RemoteEphemeral)
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getSidI1(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in by.integer32B(hs.RemoteIndex)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getNHash2(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in lib.Abs(hs.ChainHash)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getNKey2(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in lib.Abs(hs.ChainKey)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getEpkI2(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in lib.Abs(hs.RemoteEphemeral)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getEkR2(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in lib.Abs(hs.LocalEphemeral)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getSidI2(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in by.integer32B(hs.RemoteIndex)
}


pred ResponderMem(responder * Responder) {
	lib.LibMem(&responder.LibState) &&
	lib.HandshakeArgsMem(&responder.HandshakeInfo) &&
	acc(&responder.a) && acc(&responder.b)
}


ghost
requires acc(ResponderMem(responder), _)
pure func getSidR(responder *Responder) by.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in by.integer32B((responder.HandshakeInfo).LocalIndex)
}

ghost
requires acc(ResponderMem(responder), _)
pure func getKR(responder *Responder) by.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in lib.Abs((responder.HandshakeInfo).PrivateKey)
}

ghost
requires acc(ResponderMem(responder), _)
pure func getPkI(responder *Responder) by.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in lib.Abs((responder.HandshakeInfo).RemoteStatic)
}

ghost
requires acc(ResponderMem(responder), _)
pure func getPsk(responder *Responder) by.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in lib.Abs((responder.HandshakeInfo).PresharedKey)
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getRid() (rid tm.Term) {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in (
		tm.integer32((responder.HandshakeInfo).LocalIndex))
}



ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getPP() (pp tm.Term) {
	return unfolding acc(ResponderMem(responder), _) in tm.tuple4(am.pubTerm(pub.pub_integer32(responder.a)), am.pubTerm(pub.pub_integer32(responder.b)), tm.prologueTerm(), tm.infoTerm())
}

@*/
