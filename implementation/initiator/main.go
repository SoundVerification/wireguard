package initiator

import lib "wireguard-gobra/wireguard/library"

//@ import by "wireguard-gobra/wireguard/verification/bytes"
//@ import ft "wireguard-gobra/wireguard/verification/fact"
//@ import pl "wireguard-gobra/wireguard/verification/place"
//@ import io "wireguard-gobra/wireguard/verification/iospec"
//@ import .  "wireguard-gobra/wireguard/verification/messages/initiator"
//@ import tm "wireguard-gobra/wireguard/verification/term"


//@ requires lib.LibMem(&initiator.LibState) && acc(&initiator.HandshakeInfo) && acc(&initiator.a) && acc(&initiator.b)
//@ requires pl.token(t) && io.P_i(t, tm.integer32(sid), mset[ft.Fact]{})
func (initiator *Initiator) RunInitiator(sid, a, b uint32 /*@, ghost t pl.Place @*/) {
	ok /*@, pskT, ltkT, ltpkT, t1, s1 @*/ := initiator.getInitialState(sid, a, b /*@, t @*/)
	if !ok {
		return
	}

	//@ ghost var kirT, kriT tm.Term
	keypair, ok /*@, kirT, kriT, t2, s2 @*/ := initiator.runHandshake( /*@ pskT, ltkT, ltpkT, t1, s1 @*/ )
	if !ok {
		return
	}

	go initiator.forwardPackets(keypair /*@, kirT, kriT, t2, s2 @*/)
}

//@ requires lib.LibMem(&initiator.LibState) && acc(&initiator.HandshakeInfo) && acc(&initiator.a) && acc(&initiator.b)
//@ requires pl.token(t) && io.P_i(t, tm.integer32(sid), mset[ft.Fact]{})
//@ ensures  ok ==> InitiatorMem(initiator)
//@ ensures  ok ==> pl.token(t1) && io.P_i(t1, initiator.getRid(), s1)
//@ ensures  ok ==> ft.psK(tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), pskT) in s1
//@	ensures  ok ==> ft.ltK(tm.getFirst(initiator.getPP()), ltkT) in s1
//@	ensures  ok ==> ft.ltpK(tm.getSecond(initiator.getPP()), ltpkT) in s1
//@ ensures  ok ==> ft.init0(initiator.getRid(), initiator.getPP()) in s1
//@ ensures  ok ==> getPsk(initiator) == by.gamma(pskT)
//@ ensures  ok ==> getKI(initiator) == by.gamma(ltkT)
//@ ensures  ok ==> getPkR(initiator) == by.gamma(ltpkT)
func (initiator *Initiator) getInitialState(sid, a, b uint32 /*@, ghost t pl.Place @*/) (ok bool /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := tm.integer32(sid)
	//@ ghost pp := tm.tuple4(tm.integer32(a), tm.integer32(b), tm.prologueTerm(), tm.infoTerm())
	//@ t1, s1 := t, mset[ft.Fact]{}

	var psk lib.ByteString
	ok, psk /*@, pskT, t1, s1 @*/ = initiator.getPsk(a, b /*@, t, rid, s1 @*/)
	if !ok {
		return
	}

	var ltk lib.ByteString
	ok, ltk /*@, ltkT, t1, s1 @*/ = initiator.getLtk(a, b /*@, t1, rid, s1 @*/)
	if !ok {
		return
	}

	var ltpk lib.ByteString
	ok, ltpk /*@, ltpkT, t1, s1 @*/ = initiator.getLtpk(a, b /*@, t1, rid, s1 @*/)
	if !ok {
		return
	}

	(initiator.HandshakeInfo).PresharedKey = psk
	(initiator.HandshakeInfo).PrivateKey = ltk
	(initiator.HandshakeInfo).LocalIndex = sid
	(initiator.HandshakeInfo).LocalStatic = lib.PublicKey(ltk)
	(initiator.HandshakeInfo).RemoteStatic = ltpk
	initiator.a = a
	initiator.b = b

	//@ fold lib.HandshakeArgsMem(&initiator.HandshakeInfo)
	//@ fold InitiatorMem(initiator)

	ok /*@, t1, s1 @*/ = initiator.getInit0(/*@ t1, rid, s1 @*/)
	return
}

//@ requires acc(lib.LibMem(&initiator.LibState), 1/2)
//@ requires pl.token(t) && io.P_i(t, rid, s)
//@ ensures  acc(lib.LibMem(&initiator.LibState), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_i(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.psK(tm.integer32(a), tm.integer32(b), term) in s1
//@ ensures  ok ==> lib.Mem(psk) && lib.Size(psk) == 32 && lib.Abs(psk) == by.gamma(term)
func (initiator *Initiator) getPsk(a, b uint32 /*@, ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool, psk lib.ByteString /*@, ghost term tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_i(t, rid, s)
	//@ unfold io.P_i11(t, rid, s)
	//@ assert acc(io.e_PsK(t, rid))
	//@ term := io.get_e_PsK_m3(t, rid)
	var b1, b2 uint32
	ok, b1, b2, psk /*@, t1 @*/ = initiator.LibState.GetPsKBio(a, b /*@, t, rid @*/)
	if a != b1 || b != b2 || len(psk) != 32 {
		ok = false
	}
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.psK(tm.integer32(a), tm.integer32(b), term) }
	return
}

//@ requires acc(lib.LibMem(&initiator.LibState), 1/2)
//@ requires pl.token(t) && io.P_i(t, rid, s)
//@ ensures  acc(lib.LibMem(&initiator.LibState), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_i(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.ltK(tm.integer32(a), term) in s1
//@ ensures  ok ==> lib.Mem(ltk) && lib.Size(ltk) == 32 && lib.Abs(ltk) == by.gamma(term)
func (initiator *Initiator) getLtk(a, b uint32 /*@, ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool, ltk lib.ByteString /*@, ghost term tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_i(t, rid, s)
	//@ unfold io.P_i9(t, rid, s)
	//@ assert acc(io.e_LtK(t, rid))
	//@ term := io.get_e_LtK_m2(t, rid)
	var b1 uint32
	ok, b1, ltk /*@, t1 @*/ = initiator.LibState.GetLtKBio(a /*@, t, rid @*/)
	if a != b1 || len(ltk) != 32 {
		ok = false
	}
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.ltK(tm.integer32(a), term) }
	return
}

//@ requires acc(lib.LibMem(&initiator.LibState), 1/2)
//@ requires pl.token(t) && io.P_i(t, rid, s)
//@ ensures  acc(lib.LibMem(&initiator.LibState), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_i(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.ltpK(tm.integer32(b), term) in s1
//@ ensures  ok ==> lib.Mem(ltpk) && lib.Size(ltpk) == 32 && lib.Abs(ltpk) == by.gamma(term)
func (initiator *Initiator) getLtpk(a, b uint32 /*@, ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool, ltpk lib.ByteString /*@, ghost term tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_i(t, rid, s)
	//@ unfold io.P_i10(t, rid, s)
	//@ assert acc(io.e_LtpK(t, rid))
	//@ term := io.get_e_LtpK_m2(t, rid)
	var b1 uint32
	ok, b1, ltpk /*@, t1 @*/ = initiator.LibState.GetLtpKBio(b /*@, t, rid @*/)
	if b != b1 || len(ltpk) != 32 {
		ok = false
	}
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.ltpK(tm.integer32(b), term) }
	return
}

//@ requires acc(InitiatorMem(initiator), 1/2)
//@ requires pl.token(t) && io.P_i(t, rid, s)
//@ ensures  acc(InitiatorMem(initiator), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_i(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.init0(rid, initiator.getPP()) in s1
func (initiator *Initiator) getInit0(/*@ ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_i(t, rid, s)
	//@ unfold io.P_i16(t, rid, s)
	//@ assert acc(io.e_init0I(t, rid))
	//@ m1, m2, m3, m4 := io.get_e_init0I_m1(t, rid), io.get_e_init0I_m2(t, rid), io.get_e_init0I_m3(t, rid), io.get_e_init0I_m4(t, rid)
	//@ unfold acc(InitiatorMem(initiator), 1/2)
	a := initiator.a
	b := initiator.b
	//@ fold acc(InitiatorMem(initiator), 1/2)
	prologue := lib.PreludeBytes()
	info := lib.WireGuardBytes()
	ok, b1, b2, b3, b4 /*@, t1 @*/ := lib.GetInit0I(a, b, prologue, info /*@, t, rid @*/)
	if a != b1 || b != b2 || !lib.EqualsSlice(prologue, b3) || !lib.EqualsSlice(info, b4) {
		ok = false
	}
	//@ pp := tm.tuple4(m1, m2, m3, m4)
	//@ s1 = s union mset[ft.Fact] { ft.init0(rid, pp) }
	return
}
