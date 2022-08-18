package initiator

import lib "wireguard-gobra/wireguard/library"

//@ import by "wireguard-gobra/wireguard/verification/bytes"
//@ import ft "wireguard-gobra/wireguard/verification/fact"
//@ import pl "wireguard-gobra/wireguard/verification/place"
//@ import io "wireguard-gobra/wireguard/verification/iospec"
//@ import .  "wireguard-gobra/wireguard/verification/messages/initiator"
//@ import tm "wireguard-gobra/wireguard/verification/util"
//@ import am "wireguard-gobra/wireguard/verification/term"
//@ import pub "wireguard-gobra/wireguard/verification/pub"
//@ import fresh "wireguard-gobra/wireguard/verification/fresh"

//@ requires lib.LibMem(&initiator.LibState) && acc(&initiator.HandshakeInfo) && acc(&initiator.a) && acc(&initiator.b)
//@ requires pl.token(t) && io.P_Init(t, am.freshTerm(fresh.fr_integer32(sid)), mset[ft.Fact]{})
//@ requires sid != 1 && sid != 2 && sid != 4
func (initiator *Initiator) RunInitiator(sid, a, b uint32 /*@, ghost t pl.Place @*/) {
	ok /*@, pskT, ltkT, ltpkT, t1, s1 @*/ := initiator.getInitialState(sid, a, b /*@, t @*/)
	if !ok {
		return
	}

	//@ ghost var sidRT, kirT, kriT tm.Term
	keypair, ok /*@, sidRT, kirT, kriT, t2, s2 @*/ := initiator.runHandshake( /*@ pskT, ltkT, ltpkT, t1, s1 @*/ )
	if !ok {
		return
	}

	go initiator.forwardPackets(keypair /*@, sidRT, kirT, kriT, t2, s2 @*/)
}

//@ requires lib.LibMem(&initiator.LibState) && acc(&initiator.HandshakeInfo) && acc(&initiator.a) && acc(&initiator.b)
//@ requires pl.token(t) && io.P_Init(t, am.freshTerm(fresh.fr_integer32(sid)), mset[ft.Fact]{})
//@ requires sid != 1 && sid != 2 && sid != 4
//@ ensures  ok ==> InitiatorMem(initiator)
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
//@ ensures  ok ==> ft.PsK_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), pskT) in s1
//@	ensures  ok ==> ft.LtK_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), ltkT) in s1
//@	ensures  ok ==> ft.LtpK_Init(initiator.getRid(), tm.getSecond(initiator.getPP()), ltpkT) in s1
//@ ensures  ok ==> ft.Setup_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP())) in s1
//@ ensures  ok ==> getPsk(initiator) == by.gamma(pskT)
//@ ensures  ok ==> getKI(initiator) == by.gamma(ltkT)
//@ ensures  ok ==> getPkR(initiator) == by.gamma(ltpkT)
func (initiator *Initiator) getInitialState(sid, a, b uint32 /*@, ghost t pl.Place @*/) (ok bool /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := am.freshTerm(fresh.fr_integer32(sid))
	//@ ghost pp := tm.tuple4(am.pubTerm(pub.pub_integer32(a)), am.pubTerm(pub.pub_integer32(b)), tm.prologueTerm(), tm.infoTerm())
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

	//  assert tm.getFirst(initiator.getPP()) == a

	ok /*@, t1, s1 @*/ = initiator.getInit0( /*@ t1, rid, s1 @*/ )
	return
}

//@ requires acc(lib.LibMem(&initiator.LibState), 1/2)
//@ requires pl.token(t) && io.P_Init(t, rid, s)
//@ ensures  acc(lib.LibMem(&initiator.LibState), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.PsK_Init(rid, am.pubTerm(pub.pub_integer32(a)), am.pubTerm(pub.pub_integer32(b)), term) in s1
//@ ensures  ok ==> lib.Mem(psk) && lib.Size(psk) == 32 && lib.Abs(psk) == by.gamma(term)
func (initiator *Initiator) getPsk(a, b uint32 /*@, ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool, psk lib.ByteString /*@, ghost term tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_8(t, rid, s)
	//@ assert acc(io.e_PsK(t, rid))
	//@ term := io.get_e_PsK_r3(t, rid)
	var b1, b2 uint32
	ok, b1, b2, psk /*@, t1 @*/ = initiator.LibState.GetPsKBio(a, b /*@, t, rid @*/)
	if a != b1 || b != b2 || len(psk) != 32 {
		ok = false
	}
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.PsK_Init(rid, am.pubTerm(pub.pub_integer32(a)), am.pubTerm(pub.pub_integer32(b)), term) }
	return
}

//@ requires acc(lib.LibMem(&initiator.LibState), 1/2)
//@ requires pl.token(t) && io.P_Init(t, rid, s)
//@ ensures  acc(lib.LibMem(&initiator.LibState), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.LtK_Init(rid, am.pubTerm(pub.pub_integer32(a)), term) in s1
//@ ensures  ok ==> lib.Mem(ltk) && lib.Size(ltk) == 32 && lib.Abs(ltk) == by.gamma(term)
func (initiator *Initiator) getLtk(a, b uint32 /*@, ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool, ltk lib.ByteString /*@, ghost term tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_6(t, rid, s)
	//@ assert acc(io.e_LtK(t, rid))
	//@ term := io.get_e_LtK_r2(t, rid)
	var b1 uint32
	ok, b1, ltk /*@, t1 @*/ = initiator.LibState.GetLtKBio(a /*@, t, rid @*/)
	if a != b1 || len(ltk) != 32 {
		ok = false
	}
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.LtK_Init(rid, am.pubTerm(pub.pub_integer32(a)), term) }
	return
}

//@ requires acc(lib.LibMem(&initiator.LibState), 1/2)
//@ requires pl.token(t) && io.P_Init(t, rid, s)
//@ ensures  acc(lib.LibMem(&initiator.LibState), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.LtpK_Init(rid, am.pubTerm(pub.pub_integer32(b)), term) in s1
//@ ensures  ok ==> lib.Mem(ltpk) && lib.Size(ltpk) == 32 && lib.Abs(ltpk) == by.gamma(term)
func (initiator *Initiator) getLtpk(a, b uint32 /*@, ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/) (ok bool, ltpk lib.ByteString /*@, ghost term tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_7(t, rid, s)
	//@ assert acc(io.e_LtpK(t, rid))
	//@ term := io.get_e_LtpK_r2(t, rid)
	var b1 uint32
	ok, b1, ltpk /*@, t1 @*/ = initiator.LibState.GetLtpKBio(b /*@, t, rid @*/)
	if b != b1 || len(ltpk) != 32 {
		ok = false
	}
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.LtpK_Init(rid, am.pubTerm(pub.pub_integer32(b)), term) }
	return
}

//@ requires acc(InitiatorMem(initiator), 1/2)
//@ requires pl.token(t) && io.P_Init(t, rid, s)
//@ ensures  acc(InitiatorMem(initiator), 1/2)
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, rid, s1)
//@ ensures  ok ==> s subset s1 && ft.Setup_Init(rid, tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP())) in s1
func (initiator *Initiator) getInit0( /*@ ghost t pl.Place, ghost rid tm.Term, ghost s mset[ft.Fact] @*/ ) (ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_15(t, rid, s)
	//@ assert acc(io.e_Setup_Init(t, rid))
	//@ m1, m2, m3, m4 := io.get_e_Setup_Init_r1(t, rid), io.get_e_Setup_Init_r2(t, rid), tm.prologueTerm(), tm.infoTerm()
	//@ unfold acc(InitiatorMem(initiator), 1/2)
	a := initiator.a
	b := initiator.b
	//@ fold acc(InitiatorMem(initiator), 1/2)
	ok, b1, b2 /*@, t1 @*/ := lib.GetInit0I(a, b /*@, t, rid @*/)
	if a != b1 || b != b2 {
		ok = false
	}
	//@ pp := tm.tuple4(m1, m2, m3, m4)
	//@ s1 = s union mset[ft.Fact] { ft.Setup_Init(rid, tm.getFirst(pp), tm.getSecond(pp), tm.getThird(pp), tm.getForth(pp)) }
	return
}
