package initiator

import lib "wireguard-gobra/wireguard/library"

//@ import by  "wireguard-gobra/wireguard/verification/bytes"
//@ import cl  "wireguard-gobra/wireguard/verification/claim"
//@ import ft  "wireguard-gobra/wireguard/verification/fact"
//@ import pl  "wireguard-gobra/wireguard/verification/place"
//@ import io  "wireguard-gobra/wireguard/verification/iospec"
//@ import .   "wireguard-gobra/wireguard/verification/messages/initiator"
//@ import pap "wireguard-gobra/wireguard/verification/pattern"
//@ import tm  "wireguard-gobra/wireguard/verification/term"
//@ import th  "wireguard-gobra/wireguard/verification/theta"


//@ requires InitiatorMem(initiator) && lib.ConnectionMem(conn)
//@ requires pl.token(t) && io.P_i(t, initiator.getRid(), s)
//@ requires lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ requires lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ requires lib.ConnectionNonceVal(conn) == 0
//@ requires ft.init2(initiator.getRid(), initiator.getPP(), kirT, kriT, tm.zeroString(1), tm.zeroString(1)) in s
func (initiator *Initiator) forwardPackets(conn *lib.Connection /*@, ghost kirT tm.Term, ghost kriT tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) {

	//@ t1, s1 := t, s
	//@ ghost var isFirstMessage bool = true

	//@ invariant InitiatorMem(initiator) && lib.ConnectionMem(conn)
	//@ invariant lib.ConnectionKIR(conn) == by.gamma(kirT)
	//@ invariant lib.ConnectionKRI(conn) == by.gamma(kriT)
	//@ invariant  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
	//@ invariant !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
	//@ invariant pl.token(t1) && io.P_i(t1, initiator.getRid(), s1)
	//@ invariant isFirstMessage ==> ft.init2(initiator.getRid(), initiator.getPP(), kirT, kriT, tm.zeroString(1), tm.zeroString(1)) in s1
	//@ invariant !isFirstMessage ==> ft.init3(initiator.getRid(), initiator.getPP(), kirT, kriT) in s1
	for {
		/*@
		ghost rid := initiator.getRid()
		unfold io.P_i(t1, rid, s1)
		unfold io.P_i13(t1, rid, s1)
		assert acc(io.e_Message(t1, rid))
		@*/
		//@ unfold acc(InitiatorMem(initiator), 1/2)
		var request lib.ByteString
		var ok bool
		//@ ghost var term tm.Term
		request, ok /*@, term, t1 @*/ = (initiator.LibState).GetPacket( /*@ t1, rid @*/ )
		//@ fold acc(InitiatorMem(initiator), 1/2)
		/*@
		ghost if ok {
			s1 = s1 union mset[ft.Fact]{ ft.message(term) }
		} else {
			fold io.P_i13(t1, rid, s1)
			fold io.P_i(t1, rid, s1)
		}
		@*/
		//@ assert ok ==> pl.token(t1) && io.P_i(t1, rid, s1)
		//@ assert !ok ==> pl.token(t1) && io.P_i(t1, rid, s1)
		//@ assert isFirstMessage ==> ft.init2(rid, initiator.getPP(), kirT, kriT, tm.zeroString(1), tm.zeroString(1)) in s1
		//@ assert !isFirstMessage ==> ft.init3(rid, initiator.getPP(), kirT, kriT) in s1
		if ok {
			//@ ghost var isInState3 bool
			ok /*@, isInState3, t1, s1 @*/ = initiator.sendMessage(request, conn /*@, isFirstMessage, kirT, kriT, term, t1, s1 @*/)
			//@ isFirstMessage = !isInState3

			if ok {
				var response lib.ByteString
				var done bool = false // ADAPT
				//@ invariant acc(InitiatorMem(initiator), 1/4) && acc(lib.ConnectionMem(conn), 1/4)
				//@ invariant done ==> lib.Mem(response)
				//@ invariant pl.token(t1) && io.P_i(t1, initiator.getRid(), s1)
				//@ invariant lib.ConnectionKIR(conn) == by.gamma(kirT)
				//@ invariant lib.ConnectionKRI(conn) == by.gamma(kriT)
				//@ invariant ft.init3(initiator.getRid(), initiator.getPP(), kirT, kriT) in s1
				for !done {
					response, done /*@, t1, s1 @*/ = initiator.receiveMessage(conn /*@, kirT, kriT, t1, s1 @*/)
				}

				//@ unfold acc(InitiatorMem(initiator), 1/2)
				(initiator.LibState).ConsumePacket(response)
				//@ fold acc(InitiatorMem(initiator), 1/2)
			}
		}
	}

}

//@ requires acc(InitiatorMem(initiator), 1/8) && lib.ConnectionMem(conn) && lib.Mem(msg)
//@ requires lib.Abs(msg) == by.gamma(msgTerm)
//@ requires pl.token(t) && io.P_i(t, initiator.getRid(), s)
//@ requires ft.message(msgTerm) in s
//@ requires lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ requires lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ requires  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
//@ requires !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
//@ requires  isFirstMessage ==> ft.init2(initiator.getRid(), initiator.getPP(), kirT, kriT, tm.zeroString(1), tm.zeroString(1)) in s
//@ requires !isFirstMessage ==> ft.init3(initiator.getRid(), initiator.getPP(), kirT, kriT) in s
//@ ensures  acc(InitiatorMem(initiator), 1/8) && lib.ConnectionMem(conn)
//@ ensures  pl.token(t1) && io.P_i(t1, initiator.getRid(), s1)
//@ ensures  lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ ensures  lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ ensures  !isFirstMessage ==> isInState3
//@ ensures  ok ==> isInState3
//@ ensures  !isInState3 ==> ft.init2(initiator.getRid(), initiator.getPP(), kirT, kriT, tm.zeroString(1), tm.zeroString(1)) in s1
//@ ensures  isInState3  ==> ft.init3(initiator.getRid(), initiator.getPP(), kirT, kriT) in s1
//@ ensures  !isInState3 ==> lib.ConnectionNonceVal(conn) == 0
//@ ensures  isInState3  ==> lib.ConnectionNonceVal(conn) > 0
func (initiator *Initiator) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost isFirstMessage bool, ghost kirT tm.Term, ghost kriT tm.Term, ghost msgTerm tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost isInState3 bool, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := initiator.getRid()
	//@ ghost pp := initiator.getPP()
	//@ isInState3 = !isFirstMessage
	//@ unfold lib.ConnectionMem(conn)

	if conn.Nonce >= 18446744073709543423 {
		//@ fold lib.ConnectionMem(conn)
		//@ t1, s1 = t, s
		ok = false
		return
	}

	var nonce uint64
	if conn.Nonce == 0 {
		nonce = 0
		//@ t1, s1 = t, s
	} else {
		//@ unfold io.P_i(t, rid, s)
		//@ unfold io.P_i12(t, rid, s)
		//@ assert acc(io.e_Counter(t, rid))
		nonce /*@, t1 @*/ = lib.GetCounter(conn.Nonce /*@, t, rid @*/)
		//@ s1 = s union mset[ft.Fact]{ ft.counter(tm.integer64(nonce)) }
	}
	nonceBytes := lib.NonceToBytes(nonce)

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	plaintext := (initiator.LibState).PadMsg(msg)
	//@ fold acc(InitiatorMem(initiator), 1/8)

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
	//@ sidR := by.integer32B(conn.RemoteIndex)
	//@ sidrT := tm.integer32(conn.RemoteIndex)

	//@ fold lib.ConnectionMem(conn)

	packet := lib.MarshalMessage(message)

	//@ packetT := tm.tuple4(tm.integer32(4), sidrT, tm.integer64(nonce), tm.aead(kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0)))
	//@ assert lib.Abs(packet) == by.gamma(packetT)

	/*@
	ghost if (isFirstMessage) {
		unfold io.P_i(t1, rid, s1)
		unfold io.P_i3(t1, rid, s1)
		theta := th.createThetaI3(pp, kirT, kriT, msgTerm, sidrT)
		l := mset[ft.Fact] {
			ft.init2(rid, pp, th.getKIR(theta), th.getKRI(theta), tm.zeroString(1), tm.zeroString(1)),
			ft.message(th.getP(theta)),
		}
		ghost var aM mset[cl.Claim] = mset[cl.Claim]{
			cl.sentFirstInit(rid, tm.getFirst(pp), tm.getSecond(pp), th.getKIR(theta), th.getP(theta)),
	        cl.runningRespInit(tm.tuple5(tm.getFirst(pp), tm.getSecond(pp), th.getKIR(theta), th.getKRI(theta), th.getP(theta))),
		}
		r := mset[ft.Fact]{
			ft.init3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
	        ft.outFact(tm.tuple4(tm.integer32(4), th.getSidR(theta), tm.integer64(0), tm.aead(th.getKIR(theta), tm.integer64(0), th.getP(theta), tm.zeroString(0)))),
		}
		t1 = io.internalBio3I(t1, theta, l, aM, r)
		// remove and add facts to s1
	    s1 = ft.U(l, r, s1)
	} else {
		unfold io.P_i(t1, rid, s1)
		unfold io.P_i4(t1, rid, s1)
		theta := th.createThetaI4(pp, kirT, kriT, msgTerm, sidrT, nonce - 1)
		l := mset[ft.Fact] {
			ft.init3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
			ft.counter(tm.integer64(th.getNIR(theta) + 1)),
			ft.message(th.getP(theta)),
		}
		ghost var aM mset[cl.Claim] = mset[cl.Claim]{}
		r := mset[ft.Fact]{
			ft.init3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
	        ft.outFact(tm.tuple4(tm.integer32(4), th.getSidR(theta), tm.integer64(th.getNIR(theta) + 1), tm.aead(th.getKIR(theta), tm.integer64(th.getNIR(theta) + 1), th.getP(theta), tm.zeroString(0)))),
		}
		t1 = io.internalBio4I(t1, theta, l, aM, r)
		// remove and add facts to s1
	    s1 = ft.U(l, r, s1)
	}
	isInState3 = true
	@*/

	//@ unfold lib.ConnectionMem(conn)
	conn.Nonce += 1
	//@ fold lib.ConnectionMem(conn)

	//@ unfold io.P_i(t1, rid, s1)
	//@ unfold io.P_i6(t1, rid, s1)

	//@ assert ft.outFact(packetT) # s1 > 0
	//@ assert io.e_out(t1, rid, packetT)
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	ok /*@, t1 @*/ = (initiator.LibState).Send(packet /*@, t1, rid, packetT @*/)
	//@ fold acc(InitiatorMem(initiator), 1/8)
	/*@ ghost if ok {
		s1 = s1 setminus mset[ft.Fact]{ ft.outFact(packetT) }
	} else {
		fold io.P_i6(t1, rid, s1)
		fold io.P_i(t1, rid, s1)
	}
	@*/

	return
}

//@ requires acc(InitiatorMem(initiator), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ requires pl.token(t) && io.P_i(t, initiator.getRid(), s)
//@ requires ft.init3(initiator.getRid(), initiator.getPP(), kirT, kriT) in s
//@ requires lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ requires lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ ensures  acc(InitiatorMem(initiator), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ ensures  ok ==> lib.Mem(msg)
//@ ensures  pl.token(t1) && io.P_i(t1, initiator.getRid(), s1)
//@ ensures  ft.init3(initiator.getRid(), initiator.getPP(), kirT, kriT) in s1
func (initiator *Initiator) receiveMessage(conn *lib.Connection /*@, ghost kirT tm.Term, ghost kriT tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) (msg lib.ByteString, ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := initiator.getRid()
	//@ unfold io.P_i(t, rid, s)
	//@ unfold io.P_i7(t, rid, s)
	//@ assert acc(io.e_in(t, rid))
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	packet, ok /*@, term, t1 @*/ := (initiator.LibState).Receive( /*@ t, rid @*/ )
	//@ fold acc(InitiatorMem(initiator), 1/8)
	if !ok {
		//@ fold io.P_i7(t, rid, s)
		//@ fold io.P_i(t, rid, s)
		//@ s1 = s
		return
	}
	//@ recvB := lib.Abs(packet)
	//@ s1 = s union mset[ft.Fact]{ ft.inFact(term) }

	message, ok := lib.UnmarshalMessage(packet)
	if !ok {
		return
	}

	ok = message.Type == 4
	if !ok {
		return
	}

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	//@ unfold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	ok = (initiator.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	//@ fold acc(InitiatorMem(initiator), 1/8)
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

	/*@
	pp := initiator.getPP()
	recvB := lib.Abs(packet)
	sidI := by.integer32B(message.Receiver)
	nonceB := by.integer64B(message.Nonce)
	assert recvB == by.gamma(tm.tuple4(by.oneTerm(by.integer32B(4)), rid, by.oneTerm(nonceB), tm.aead(kriT, by.oneTerm(nonceB), by.oneTerm(lib.Abs(plaintext)), tm.zeroString(0))))

	nRI, p := pap.patternProperty4(rid, pp, kirT, kriT, by.oneTerm(nonceB), by.oneTerm(lib.Abs(plaintext)), term, t1, s1, true)
	assert term == tm.tuple4(tm.integer32(4), rid, nRI, tm.aead(kriT, nRI, p, tm.zeroString(0)))

	unfold io.P_i(t1, rid, s1)
	unfold io.P_i5(t1, rid, s1)
	theta := th.createThetaI5(pp, kirT, kriT, nRI, p)
	l := mset[ft.Fact] {
		ft.init3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
		ft.inFact(tm.tuple4(tm.integer32(4), rid, th.getNRITerm(theta), tm.aead(th.getKRI(theta), th.getNRITerm(theta), th.getP(theta), tm.zeroString(0)))),
	}
	ghost var aM mset[cl.Claim] = mset[cl.Claim]{}
	r := mset[ft.Fact]{
		ft.init3(rid, pp, th.getKIR(theta), th.getKRI(theta)),
	}
	assert ft.G(l, s1)
	t1 = io.internalBio5I(t1, theta, l, aM, r)
	// remove and add facts to s1
	s1 = ft.U(l, r, s1)
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}
