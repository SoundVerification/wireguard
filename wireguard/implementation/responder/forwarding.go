package responder

import lib "wireguard-gobra/wireguard/library"

//@ import by  "wireguard-gobra/wireguard/verification/bytes"
//@ import cl  "wireguard-gobra/wireguard/verification/claim"
//@ import ft  "wireguard-gobra/wireguard/verification/fact"
//@ import io  "wireguard-gobra/wireguard/verification/iospec"
//@ import .   "wireguard-gobra/wireguard/verification/messages/responder"
//@ import pap "wireguard-gobra/wireguard/verification/pattern"
//@ import pl  "wireguard-gobra/wireguard/verification/place"
//@ import tm  "wireguard-gobra/wireguard/verification/util"
//@ import am  "wireguard-gobra/wireguard/verification/term"
//@ import pub "wireguard-gobra/wireguard/verification/pub"
//@ import fresh "wireguard-gobra/wireguard/verification/fresh"

//@ requires ResponderMem(responder) && lib.ConnectionMem(conn)
//@ requires pl.token(t) && io.P_Resp(t, responder.getRid(), s)
//@ requires len(v) == 6
//@ requires ft.St_Resp_2(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s
//@ requires by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
//@ requires lib.ConnectionNonceVal(conn) == 0
func (responder *Responder) forwardPackets(conn *lib.Connection /*@, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) {

	//@ ghost t1, s1 := t, s
	//@ ghost firstReceive := true

	//@ invariant ResponderMem(responder) && lib.ConnectionMem(conn)
	//@ invariant len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
	//@ invariant pl.token(t1) && io.P_Resp(t1, responder.getRid(), s1)
	//@ invariant lib.ConnectionNonceVal(conn) >= 0
	//@ invariant  firstReceive ==> ft.St_Resp_2(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
	//@ invariant !firstReceive ==> ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
	for {

		var response lib.ByteString
		var done bool = false // ADAPT

		//@ invariant acc(ResponderMem(responder), 1/4) && acc(lib.ConnectionMem(conn), 1/2)
		//@ invariant len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
		//@ invariant pl.token(t1) && io.P_Resp(t1, responder.getRid(), s1)
		//@ invariant (!done &&  firstReceive) ==> ft.St_Resp_2(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
		//@ invariant (!done && !firstReceive) ==> ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
		//@ invariant  done ==> lib.Mem(response)
		//@ invariant  done ==> ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
		for !done {
			response, done /*@, t1, s1  @*/ = responder.receiveMessage(conn /*@, firstReceive, v, t1, s1 @*/)
		}
		//@ firstReceive = false

		//@ ghost rid := responder.getRid()
		//@ unfold io.P_Resp(t1,rid,s1)
		//@ unfold io.phiRF_Resp_13(t1,rid,s1)
		//@ unfold ResponderMem(responder)
		(responder.LibState).ConsumePacket(response)

		request, ok /*@, msgT, t2 @*/ := (responder.LibState).GetPacket( /*@ t1, rid @*/ )
		//@ t1 = t2
		//@ fold ResponderMem(responder)
		/*@
		ghost if !ok {
			fold io.phiRF_Resp_13(t1,rid,s1)
			fold io.P_Resp(t1,rid,s1)
		}
		@*/
		if ok {
			//@ s1 = s1 union mset[ft.Fact] { ft.Message_Resp(rid, msgT) }
			/*@ _, t1, s1 = @*/
			responder.sendMessage(request, conn /*@, msgT, v, t1, s1 @*/)
		}
	}
}

//@ requires acc(ResponderMem(responder), 1/8) && lib.ConnectionMem(conn) && lib.Mem(msg)
//@ requires pl.token(t) && io.P_Resp(t, responder.getRid(), s)
//@ requires len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
//@ requires lib.ConnectionNonceVal(conn) >= 0
//@ requires ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s
//@ requires by.gamma(msgT) == lib.Abs(msg) && ft.Message_Resp(responder.getRid(), msgT) in s
//@ ensures  acc(ResponderMem(responder), 1/8) && lib.ConnectionMem(conn)
//@ ensures  pl.token(t1) && io.P_Resp(t1, responder.getRid(), s1)
//@ ensures  ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
//@ ensures  lib.ConnectionSidI(conn) == old(lib.ConnectionSidI(conn)) && lib.ConnectionKIR(conn) == old(lib.ConnectionKIR(conn)) && lib.ConnectionKRI(conn) == old(lib.ConnectionKRI(conn))
//@ ensures  lib.ConnectionNonceVal(conn) >= 0
func (responder *Responder) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost msgT tm.Term, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	//@ unfold lib.ConnectionMem(conn)

	//@ unfold io.P_Resp(t, rid, s)
	//@ unfold io.phiRF_Resp_12(t, rid, s)
	nonce /*@, t1 @*/ := lib.GetCounter(conn.Nonce /*@, t, rid @*/)
	//@ s1 = s union mset[ft.Fact]{ ft.Counter_Resp(rid, tm.integer64(nonce)) }
	//@ assert io.P_Resp(t1, rid, s1)

	if conn.Nonce >= 18446744073709543423 {
		//@ fold lib.ConnectionMem(conn)
		ok = false
		return
	}
	nonceBytes := lib.NonceToBytes(nonce)

	//@ unfold acc(ResponderMem(responder), 1/8)
	plaintext := (responder.LibState).PadMsg(msg)
	//@ fold acc(ResponderMem(responder), 1/8)

	encryptedMsg, ok := lib.AeadEnc(conn.SendKey, nonceBytes, plaintext, nil)
	if !ok {
		//@ fold lib.ConnectionMem(conn)
		return
	}

	message := &lib.Message{
		Type:     4,
		Receiver: conn.RemoteIndex,
		Nonce:    nonce,
		Payload:  encryptedMsg,
	}

	packet := lib.MarshalMessage(message)

	/*@
	var Q3sidR tm.Term = rid
	var Q3a tm.Term = tm.getFirst(pp)
	var Q3b tm.Term = tm.getSecond(pp)
	var Q3prologue tm.Term = tm.getThird(pp)
	var Q3info tm.Term = tm.getForth(pp)
	var Q3sidI tm.Term = v[0]
	var Q3kIR tm.Term = v[4]
	var Q3kRI tm.Term = v[5]
	var Q3nRI tm.Term = tm.integer64(nonce)
	var Q3p tm.Term = msgT

	l := tm.InternalResp4L(Q3sidR, Q3a, Q3b, Q3prologue, Q3info, Q3sidI, Q3kIR, Q3kRI, Q3nRI, Q3p)
	a := tm.InternalResp4A(Q3sidR, Q3a, Q3b, Q3prologue, Q3info, Q3sidI, Q3kIR, Q3kRI, Q3nRI, Q3p)
	r := tm.InternalResp4R(Q3sidR, Q3a, Q3b, Q3prologue, Q3info, Q3sidI, Q3kIR, Q3kRI, Q3nRI, Q3p)

	unfold io.P_Resp(t1, rid, s1)
	unfold io.phiR_Resp_3(t1, rid, s1)
	t1 = io.internBIO_e_Send_Resp_Loop(t1, Q3sidR, Q3a, Q3b, Q3prologue, Q3info, Q3sidI, Q3kIR, Q3kRI, Q3nRI, Q3p, l, a, r)
	s1 = ft.U(l,r,s1)

	unfold io.P_Resp(t1, rid, s1)
	unfold io.phiRG_Resp_5(t1, rid, s1)

	ghost m := tm.tuple4(tm.integer32(4), v[0], tm.integer64(nonce), tm.aead(v[5], tm.integer64(nonce), msgT, tm.zeroString(0)))
	assert ft.OutFact_Resp(rid, m) in s1 // for the trigger
	@*/

	//@ unfold acc(ResponderMem(responder), 1/8)
	ok /*@, t1 @*/ = (responder.LibState).Send(packet /*@, t1, rid, m @*/)
	//@ fold acc(ResponderMem(responder), 1/8)

	/*@
	ghost if !ok {

		fold io.phiRG_Resp_5(t1, rid, s1)
		fold io.P_Resp(t1, rid, s1)
	}
	@*/
	if ok {
		//@ s1 = s1 setminus mset[ft.Fact]{ ft.OutFact_Resp(rid, m) }
		conn.Nonce += 1
	}

	//@ fold lib.ConnectionMem(conn)

	return
}

//@ requires acc(ResponderMem(responder), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ requires pl.token(t) && io.P_Resp(t, responder.getRid(), s)
//@ requires len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
//@ requires q ? (ft.St_Resp_2(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s) : (ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s)
//@ ensures  acc(ResponderMem(responder), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ ensures  pl.token(t1) && io.P_Resp(t1, responder.getRid(), s1)
//@ ensures  ok ==> lib.Mem(msg)
//@ ensures  ok ==> ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1
//@ ensures !ok ==> (q ? (ft.St_Resp_2(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1) : (ft.St_Resp_3(responder.getRid(), tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), tm.getThird(responder.getPP()), tm.getForth(responder.getPP()), v[0], v[4], v[5]) in s1))
func (responder *Responder) receiveMessage(conn *lib.Connection /*@, ghost q bool, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (msg lib.ByteString, ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	//@ unfold io.P_Resp(t, rid, s)
	//@ unfold io.phiRF_Resp_9(t, rid, s)
	//@ s1 = s union mset[ft.Fact]{ ft.InFact_Resp(rid, io.get_e_InFact_r1(t, rid)) }
	//@ unfold acc(ResponderMem(responder), 1/8)
	packet, ok /*@, c, t1 @*/ := (responder.LibState).Receive( /*@ t, rid @*/ )
	//@ fold acc(ResponderMem(responder), 1/8)
	if !ok {
		//@ s1 = s
		//@ fold io.phiRF_Resp_9(t1, rid, s1)
		//@ fold io.P_Resp(t1, rid, s1)
		return
	}

	message, ok := lib.UnmarshalMessage(packet)
	if !ok {
		return
	}

	ok = message.Type == 4
	if !ok {
		return
	}

	//@ unfold acc(ResponderMem(responder), 1/8)
	//@ unfold acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), 1/8)
	ok = (responder.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), 1/8)
	//@ fold acc(ResponderMem(responder), 1/8)
	if !ok {
		return
	}

	nonceBytes := lib.NonceToBytes(message.Nonce)

	//@ unfold acc(lib.ConnectionMem(conn), 1/8)
	plaintext, ok := lib.AeadDec(conn.RecvKey, nonceBytes, message.Payload, nil)
	//@ fold acc(lib.ConnectionMem(conn), 1/8)
	if !ok { // ADAPT
		return
	}
	//@ m := lib.Abs(plaintext)
	//@ n := by.integer64B(message.Nonce)
	//@ nX, mX := pap.patternProperty4(rid, pp, v[0], v[5],v[4],by.oneTerm(n),by.oneTerm(m),c,t1,s1,false)

	/*@
	ghost if q {
		var Q4sidR tm.Term = rid
		var Q4a tm.Term = tm.getFirst(pp)
		var Q4b tm.Term = tm.getSecond(pp)
		var Q4prologue tm.Term = tm.getThird(pp)
		var Q4info tm.Term = tm.getForth(pp)
		var Q4sidI tm.Term = v[0]
		var Q4kIR tm.Term = v[4]
		var Q4kRI tm.Term = v[5]
		var Q4x tm.Term = rid
		var Q4n tm.Term = nX
		var Q4p tm.Term = mX

		l := tm.InternalResp3L(Q4sidR, Q4a, Q4b, Q4prologue, Q4info, Q4sidI, Q4kIR, Q4kRI, Q4x, Q4n, Q4p)
		a := tm.InternalResp3A(Q4sidR, Q4a, Q4b, Q4prologue, Q4info, Q4sidI, Q4kIR, Q4kRI, Q4x, Q4n, Q4p)
		r := tm.InternalResp3R(Q4sidR, Q4a, Q4b, Q4prologue, Q4info, Q4sidI, Q4kIR, Q4kRI, Q4x, Q4n, Q4p)

		unfold io.P_Resp(t1, rid, s1)
		unfold io.phiR_Resp_2(t1, rid, s1)
		t1 = io.internBIO_e_Receive_First_Resp(t1, Q4sidR, Q4a, Q4b, Q4prologue, Q4info, Q4sidI, Q4kIR, Q4kRI, Q4x, Q4n, Q4p, l, a, r)
		s1 = ft.U(l, r, s1)
	} else {

		var Q5sidR tm.Term = rid
		var Q5a tm.Term = tm.getFirst(pp)
		var Q5b tm.Term = tm.getSecond(pp)
		var Q5prologue tm.Term = tm.getThird(pp)
		var Q5info tm.Term = tm.getForth(pp)
		var Q5sidI tm.Term = v[0]
		var Q5kIR tm.Term = v[4]
		var Q5kRI tm.Term = v[5]
		var Q5x tm.Term = rid
		var Q5nIR tm.Term = nX
		var Q5p tm.Term = mX

		l := tm.InternalResp5L(Q5sidR, Q5a, Q5b, Q5prologue, Q5info, Q5sidI, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p)
		a := tm.InternalResp5A(Q5sidR, Q5a, Q5b, Q5prologue, Q5info, Q5sidI, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p)
		r := tm.InternalResp5R(Q5sidR, Q5a, Q5b, Q5prologue, Q5info, Q5sidI, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p)


		unfold io.P_Resp(t1, rid, s1)
		unfold io.phiR_Resp_4(t1, rid, s1)
		t1 = io.internBIO_e_Receive_Resp_Loop(t1, Q5sidR, Q5a, Q5b, Q5prologue, Q5info, Q5sidI, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p, l, a, r)
		s1 = ft.U(l, r, s1)
	}
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}
