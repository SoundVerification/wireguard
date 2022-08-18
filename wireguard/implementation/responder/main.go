package responder

import lib "wireguard-gobra/wireguard/library"

//@ import by "wireguard-gobra/wireguard/verification/bytes"
//@ import cl "wireguard-gobra/wireguard/verification/claim"
//@ import ft "wireguard-gobra/wireguard/verification/fact"
//@ import io "wireguard-gobra/wireguard/verification/iospec"
//@ import .  "wireguard-gobra/wireguard/verification/messages/responder"
//@ import pl "wireguard-gobra/wireguard/verification/place"
//@ import tm "wireguard-gobra/wireguard/verification/util"
//@ import am "wireguard-gobra/wireguard/verification/term"
//@ import pub "wireguard-gobra/wireguard/verification/pub"
//@ import fresh "wireguard-gobra/wireguard/verification/fresh"

//@ requires lib.LibMem(&responder.LibState) && acc(&responder.HandshakeInfo) && acc(&responder.a) && acc(&responder.b)
//@ requires pl.token(t) && io.P_Resp(t, am.freshTerm(fresh.fr_integer32(sid)), mset[ft.Fact]{})
//@ requires sid != 1 && sid != 2 && sid != 4
func (responder *Responder) RunResponder(sid, a, b uint32 /*@, ghost t pl.Place @*/) {
	ok /*@, keys, t1, s1 @*/ := responder.getInitialState(sid, a, b /*@, t @*/)
	if !ok {
		return
	}

	keypair, ok /*@, v1, t1, s1 @*/ := responder.runHandshake( /*@ keys, t1, s1 @*/ )
	if !ok {
		return
	}
	go responder.forwardPackets(keypair /*@, v1, t1, s1 @*/)
}

//@ requires lib.LibMem(&responder.LibState) && acc(&responder.HandshakeInfo) && acc(&responder.a) && acc(&responder.b)
//@ requires pl.token(t) && io.P_Resp(t, am.freshTerm(fresh.fr_integer32(sid)), mset[ft.Fact]{})
//@ requires sid != 1 && sid != 2 && sid != 4
//@ ensures  ok ==> ResponderMem(responder)
//@ ensures  ok ==> pl.token(t1) && io.P_Resp(t1, responder.getRid(), s1)
//@ ensures  ok ==> len(keys) == 3
//@ ensures  ok ==> ft.LtK_Resp(responder.getRid(), tm.getSecond(responder.getPP()), keys[0]) in s1 && by.gamma(keys[0]) == getKR(responder)
//@ ensures  ok ==> ft.LtpK_Resp(responder.getRid(), tm.getFirst(responder.getPP()), keys[1]) in s1 && by.gamma(keys[1]) == getPkI(responder)
//@ ensures  ok ==> ft.PsK_Resp(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), keys[2]) in s1  && by.gamma(keys[2]) == getPsk(responder)
//@ ensures  ok ==> ft.Setup_Resp(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP())) in s1
func (responder *Responder) getInitialState(sid, a, b uint32 /*@, ghost t pl.Place @*/) (ok bool /*@, ghost keys seq[tm.Term], ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := am.freshTerm(fresh.fr_integer32(sid))
	//TODO make a and b uint16
	//@ ghost pp := tm.tuple4(am.pubTerm(pub.pub_integer32(a)), am.pubTerm(pub.pub_integer32(b)), tm.prologueTerm(), tm.infoTerm())
	//@ t1, s1 := t, mset[ft.Fact]{}

	//@ unfold io.P_Resp(t1, rid, s1)
	//@ unfold io.phiRF_Resp_6(t1, rid, s1)
	//@ kRT := io.get_e_LtK_r2(t1, rid)
	ok, bX, ltk /*@, t1 @*/ := (responder.LibState).GetLtKBio(b /*@, t1, rid @*/)
	if !ok || b != bX || len(ltk) != 32 {
		ok = false
		return
	}
	//@ s1 = s1 union mset[ft.Fact]{ ft.LtK_Resp(rid, am.pubTerm(pub.pub_integer32(b)), kRT) }
	//@ assert ft.LtK_Resp(rid, am.pubTerm(pub.pub_integer32(b)), kRT) in s1

	//@ unfold io.P_Resp(t1, rid, s1)
	//@ unfold io.phiRF_Resp_7(t1, rid, s1)
	//@ pkIT := io.get_e_LtpK_r2(t1, rid)
	ok, aX, ltpk /*@, t1 @*/ := (responder.LibState).GetLtpKBio(a /*@, t1, rid @*/)
	if !ok || a != aX || len(ltpk) != 32 {
		ok = false
		return
	}
	//@ s1 = s1 union mset[ft.Fact]{ ft.LtpK_Resp(rid, am.pubTerm(pub.pub_integer32(a)), pkIT) }

	//@ unfold io.P_Resp(t1, rid, s1)
	//@ unfold io.phiRF_Resp_8(t1, rid, s1)
	//@ pskT := io.get_e_PsK_r3(t1, rid)
	ok, aX, bY, psk /*@, t1 @*/ := (responder.LibState).GetPsKBio(a, b /*@, t1, rid @*/)
	if !ok || a != aX || b != bY || len(psk) != 32 {
		ok = false
		return
	}
	//@ s1 = s1 union mset[ft.Fact]{ ft.PsK_Resp(rid, am.pubTerm(pub.pub_integer32(a)), am.pubTerm(pub.pub_integer32(b)), pskT) }

	(responder.HandshakeInfo).PresharedKey = psk
	(responder.HandshakeInfo).PrivateKey = ltk
	(responder.HandshakeInfo).LocalIndex = sid
	(responder.HandshakeInfo).LocalStatic = lib.PublicKey(ltk)
	(responder.HandshakeInfo).RemoteStatic = ltpk
	responder.a = a
	responder.b = b

	//@ fold lib.HandshakeArgsMem(&responder.HandshakeInfo)
	//@ fold ResponderMem(responder)
	//@ assert pp == responder.getPP()

	//@ unfold io.P_Resp(t1, rid, s1)
	//@ unfold io.phiRF_Resp_14(t1, rid, s1)
	ok, aX, bX /*@, t1 @*/ = lib.GetResp0R(a, b /*@, t1, rid @*/)
	if a != aX || b != bX {
		ok = false
	}
	//@ s1 = s1 union mset[ft.Fact]{ ft.Setup_Resp(rid, tm.getFirst(pp), tm.getSecond(pp), tm.getThird(pp), tm.getForth(pp)) }
	//@ keys = seq[tm.Term]{ kRT, pkIT, pskT }

	return
}
