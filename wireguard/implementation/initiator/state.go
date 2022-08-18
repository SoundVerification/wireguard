package initiator

import lib "wireguard-gobra/wireguard/library"

//@ import by "wireguard-gobra/wireguard/verification/bytes"
//@ import tm "wireguard-gobra/wireguard/verification/util"
//@ import am "wireguard-gobra/wireguard/verification/term"
//@ import pub "wireguard-gobra/wireguard/verification/pub"
//@ import fresh "wireguard-gobra/wireguard/verification/fresh"

type Initiator struct {
	LibState      lib.LibraryState
	HandshakeInfo lib.HandshakeArguments
	a, b          uint32
}

/*@

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getRid() (rid tm.Term) {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in (
		tm.integer32((initiator.HandshakeInfo).LocalIndex))
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func (initiator *Initiator) getPP() (pp tm.Term) {
	return unfolding acc(InitiatorMem(initiator), _) in tm.tuple4(am.pubTerm(pub.pub_integer32(initiator.a)), am.pubTerm(pub.pub_integer32(initiator.b)), tm.prologueTerm(), tm.infoTerm())
}

pred HandshakeMem(hs *lib.Handshake) {
	acc(hs) && lib.Mem(hs.ChainHash) && lib.Mem(hs.ChainKey) && lib.Mem(hs.LocalEphemeral) &&
	lib.Size(hs.ChainHash) == 32 && lib.Size(hs.ChainKey) == 32 && lib.Size(hs.LocalEphemeral) == 32
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getNHash(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in lib.Abs(hs.ChainHash)
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getNKey(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in lib.Abs(hs.ChainKey)
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getEkI(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in lib.Abs(hs.LocalEphemeral)
}

ghost
requires acc(HandshakeMem(hs), _)
pure func getSidR(hs *lib.Handshake) by.Bytes {
	return unfolding acc(HandshakeMem(hs), _) in by.integer32B(hs.RemoteIndex)
}


pred InitiatorMem(initiator * Initiator) {
	lib.LibMem(&initiator.LibState) &&
	lib.HandshakeArgsMem(&initiator.HandshakeInfo) &&
	acc(&initiator.a) && acc(&initiator.b)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getSidI(initiator *Initiator) by.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in by.integer32B((initiator.HandshakeInfo).LocalIndex)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getKI(initiator *Initiator) by.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in lib.Abs((initiator.HandshakeInfo).PrivateKey)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getPkR(initiator *Initiator) by.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in lib.Abs((initiator.HandshakeInfo).RemoteStatic)
}

ghost
requires acc(InitiatorMem(initiator), _)
pure func getPsk(initiator *Initiator) by.Bytes {
	return unfolding acc(InitiatorMem(initiator), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in lib.Abs((initiator.HandshakeInfo).PresharedKey)
}

@*/
