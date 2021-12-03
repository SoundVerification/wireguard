package responder

import lib "wireguard-gobra/wireguard/library"

//@ import by  "wireguard-gobra/wireguard/verification/bytes"
//@ import cl  "wireguard-gobra/wireguard/verification/claim"
//@ import ft  "wireguard-gobra/wireguard/verification/fact"
//@ import io  "wireguard-gobra/wireguard/verification/iospec"
//@ import .   "wireguard-gobra/wireguard/verification/messages/responder"
//@ import pap "wireguard-gobra/wireguard/verification/pattern"
//@ import pl  "wireguard-gobra/wireguard/verification/place"
//@ import tm  "wireguard-gobra/wireguard/verification/term"
//@ import th  "wireguard-gobra/wireguard/verification/theta"


//@ requires ResponderMem(responder) && lib.ConnectionMem(conn)
//@ requires pl.token(t) && io.P_r(t, responder.getRid(), s)
//@ requires len(v) == 6
//@ requires ft.resp2(responder.getRid(), responder.getPP(), v[4], v[5], tm.zeroString(1), tm.zeroString(1)) in s
//@ requires by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
//@ requires lib.ConnectionNonceVal(conn) == 0
func (responder *Responder) forwardPackets(conn *lib.Connection /*@, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) {

	//@ ghost t1, s1 := t, s
	//@ ghost firstReceive := true

	//@ invariant ResponderMem(responder) && lib.ConnectionMem(conn)
	//@ invariant len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
	//@ invariant pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
	//@ invariant lib.ConnectionNonceVal(conn) >= 0
	//@ invariant  firstReceive ==> ft.resp2(responder.getRid(), responder.getPP(), v[4], v[5], tm.zeroString(1), tm.zeroString(1)) in s1
	//@ invariant !firstReceive ==> ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s1
	for {

		var response lib.ByteString
		var done bool = false // ADAPT

		//@ invariant acc(ResponderMem(responder), 1/4) && acc(lib.ConnectionMem(conn), 1/2)
		//@ invariant len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
		//@ invariant pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
		//@ invariant (!done &&  firstReceive) ==> ft.resp2(responder.getRid(), responder.getPP(), v[4], v[5], tm.zeroString(1), tm.zeroString(1)) in s1
		//@ invariant (!done && !firstReceive) ==> ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s1
		//@ invariant  done ==> lib.Mem(response)
		//@ invariant  done ==> ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s1
		for !done {
			response, done /*@, t1, s1  @*/ = responder.receiveMessage(conn /*@, firstReceive, v, t1, s1 @*/)
		}
		//@ firstReceive = false

		//@ ghost rid := responder.getRid()
		//@ unfold io.P_r(t1,rid,s1)
		//@ unfold io.P_r13(t1,rid,s1)
		//@ unfold ResponderMem(responder)
		(responder.LibState).ConsumePacket(response)

		request, ok /*@, msgT, t2 @*/ := (responder.LibState).GetPacket(/*@ t1, rid @*/)
		//@ t1 = t2
		//@ fold ResponderMem(responder)
		/*@
		ghost if !ok {
			fold io.P_r13(t1,rid,s1)
			fold io.P_r(t1,rid,s1)
		}
		@*/
		if ok {
			//@ s1 = s1 union mset[ft.Fact] { ft.message(msgT) }
			/*@ _, t1, s1 = @*/ responder.sendMessage(request, conn /*@, msgT, v, t1, s1 @*/)
		}
	}
}





//@ requires acc(ResponderMem(responder), 1/8) && lib.ConnectionMem(conn) && lib.Mem(msg)
//@ requires pl.token(t) && io.P_r(t, responder.getRid(), s)
//@ requires len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
//@ requires lib.ConnectionNonceVal(conn) >= 0
//@ requires ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s
//@ requires by.gamma(msgT) == lib.Abs(msg) && ft.message(msgT) in s
//@ ensures  acc(ResponderMem(responder), 1/8) && lib.ConnectionMem(conn)
//@ ensures  pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
//@ ensures  ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s1
//@ ensures  lib.ConnectionSidI(conn) == old(lib.ConnectionSidI(conn)) && lib.ConnectionKIR(conn) == old(lib.ConnectionKIR(conn)) && lib.ConnectionKRI(conn) == old(lib.ConnectionKRI(conn))
//@ ensures  lib.ConnectionNonceVal(conn) >= 0
func (responder *Responder) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost msgT tm.Term, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	//@ unfold lib.ConnectionMem(conn)

	//@ unfold io.P_r(t, rid, s)
	//@ unfold io.P_r12(t, rid, s) 
	nonce /*@, t1 @*/ := lib.GetCounter(conn.Nonce /*@, t, rid @*/)
	//@ s1 = s union mset[ft.Fact]{ ft.counter(tm.integer64(nonce)) }
	//@ assert io.P_r(t1, rid, s1)

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
	ghost theta := th.createThetaR4(pp, v[4],v[5],v[0],msgT,nonce)
	ghost l := mset[ft.Fact]{
		ft.resp3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
		ft.counter(tm.integer64(th.getNRI(theta))),
		ft.message(th.getP(theta)),
	} 
	ghost a := mset[cl.Claim]{ } 
	ghost r := mset[ft.Fact]{ 
		ft.resp3(rid, pp, th.getKIR(theta), th.getKRI(theta)), 
		ft.outFact(tm.tuple4(tm.integer32(4), th.getSidI(theta), tm.integer64(th.getNRI(theta)), tm.aead(th.getKRI(theta), tm.integer64(th.getNRI(theta)), th.getP(theta), tm.zeroString(0)))),
	}

	unfold io.P_r(t1, rid, s1)
	unfold io.P_r4(t1, rid, s1)
	t1 = io.internalBio4R(t1, theta, l, a, r)
	s1 = ft.U(l,r,s1)

	unfold io.P_r(t1, rid, s1)
	unfold io.P_r6(t1, rid, s1) 

	ghost m := tm.tuple4(tm.integer32(4), v[0], tm.integer64(nonce), tm.aead(v[5], tm.integer64(nonce), msgT, tm.zeroString(0)))
	assert ft.outFact(m) in s1 // for the trigger
	@*/

	//@ unfold acc(ResponderMem(responder), 1/8)
	ok /*@, t1 @*/= (responder.LibState).Send(packet /*@, t1, rid, m @*/)
	//@ fold acc(ResponderMem(responder), 1/8)

	/*@
	ghost if !ok {
		fold io.P_r6(t1, rid, s1) 
		fold io.P_r(t1, rid, s1)
	}
	@*/
	if ok {
		//@ s1 = s1 setminus mset[ft.Fact]{ ft.outFact(m) }
		conn.Nonce += 1
	}

	//@ fold lib.ConnectionMem(conn)

	return
}



//@ requires acc(ResponderMem(responder), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ requires pl.token(t) && io.P_r(t, responder.getRid(), s)
//@ requires len(v) == 6 && by.gamma(v[0]) == lib.ConnectionSidI(conn) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == lib.ConnectionKRI(conn) && by.gamma(v[5]) == lib.ConnectionKIR(conn)
//@ requires q ? (ft.resp2(responder.getRid(), responder.getPP(), v[4], v[5], tm.zeroString(1), tm.zeroString(1)) in s) : (ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s) 
//@ ensures  acc(ResponderMem(responder), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ ensures  pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
//@ ensures  ok ==> lib.Mem(msg)
//@ ensures  ok ==> ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s1
//@ ensures !ok ==> (q ? (ft.resp2(responder.getRid(), responder.getPP(), v[4], v[5], tm.zeroString(1), tm.zeroString(1)) in s1) : (ft.resp3(responder.getRid(), responder.getPP(), v[4], v[5]) in s1))
func (responder *Responder) receiveMessage(conn *lib.Connection /*@, ghost q bool, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (msg lib.ByteString, ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	//@ unfold io.P_r(t, rid, s)
	//@ unfold io.P_r7(t, rid, s)
	//@ s1 = s union mset[ft.Fact]{ ft.inFact(io.get_e_in_m(t, rid)) }
	//@ unfold acc(ResponderMem(responder), 1/8)
	packet, ok /*@, c, t1 @*/ := (responder.LibState).Receive(/*@ t, rid @*/)
	//@ fold acc(ResponderMem(responder), 1/8)
	if !ok {
		//@ s1 = s
		//@ fold io.P_r7(t1, rid, s1)
		//@ fold io.P_r(t1, rid, s1)
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
	//@ nX, mX := pap.patternProperty4(rid, pp, v[5],v[4],by.oneTerm(n),by.oneTerm(m),c,t1,s1,false)

	/*@
	ghost if q {
		ghost theta := th.createThetaR5(pp,v[4],v[5],v[0],mX,nX)
		ghost l := mset[ft.Fact] {
			ft.resp2(rid,pp, th.getKIR(theta), th.getKRI(theta), tm.zeroString(1), tm.zeroString(1)),
			ft.inFact(tm.tuple4(tm.integer32(4), rid, th.getNIRTerm(theta), tm.aead(th.getKIR(theta), th.getNIRTerm(theta), th.getP(theta), tm.zeroString(0)))),
		}
		ghost a := mset[cl.Claim]{
			cl.receivedFirstResp(rid, tm.getFirst(pp), tm.getSecond(pp), th.getKIR(theta), th.getKRI(theta), th.getP(theta)),
			cl.commitRespInit(tm.tuple5(tm.getFirst(pp), tm.getSecond(pp), th.getKIR(theta), th.getKRI(theta), th.getP(theta))),
			cl.secret(tm.getFirst(pp), tm.getSecond(pp), tm.tuple2(th.getKIR(theta), th.getKRI(theta))),
		}
		ghost r := mset[ft.Fact]{
			ft.resp3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
		}
		unfold io.P_r(t1, rid, s1)
		unfold io.P_r3(t1, rid, s1)
		t1 = io.internalBio3R(t1, theta, l, a, r)
		s1 = ft.U(l, r, s1)
	} else {

		ghost theta := th.createThetaR5(pp,v[4],v[5],v[0],mX,nX)
		ghost l := mset[ft.Fact] {
			ft.resp3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
			ft.inFact(tm.tuple4(tm.integer32(4), rid, th.getNIRTerm(theta), tm.aead(th.getKIR(theta), th.getNIRTerm(theta), th.getP(theta), tm.zeroString(0)))),
		}
		ghost a := mset[cl.Claim]{}
		ghost r := mset[ft.Fact]{
			ft.resp3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
		}
		unfold io.P_r(t1, rid, s1)
		unfold io.P_r5(t1, rid, s1)
		t1 = io.internalBio5R(t1, theta, l, a, r)
		s1 = ft.U(l, r, s1)
	}
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}
