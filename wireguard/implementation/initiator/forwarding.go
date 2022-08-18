package initiator

import lib "wireguard-gobra/wireguard/library"

//@ import by  "wireguard-gobra/wireguard/verification/bytes"
//@ import cl  "wireguard-gobra/wireguard/verification/claim"
//@ import ft  "wireguard-gobra/wireguard/verification/fact"
//@ import pl  "wireguard-gobra/wireguard/verification/place"
//@ import io  "wireguard-gobra/wireguard/verification/iospec"
//@ import .   "wireguard-gobra/wireguard/verification/messages/initiator"
//@ import pap "wireguard-gobra/wireguard/verification/pattern"
//@ import tm  "wireguard-gobra/wireguard/verification/util"
//@ import am  "wireguard-gobra/wireguard/verification/term"
//@ import pub "wireguard-gobra/wireguard/verification/pub"
//@ import fresh "wireguard-gobra/wireguard/verification/fresh"

//@ requires InitiatorMem(initiator) && lib.ConnectionMem(conn)
//@ requires pl.token(t) && io.P_Init(t, initiator.getRid(), s)
//@ requires lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ requires lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ requires lib.ConnectionSidI(conn) == by.gamma(sidRT)
//@ requires lib.ConnectionNonceVal(conn) == 0
//@ requires ft.St_Init_2(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s
func (initiator *Initiator) forwardPackets(conn *lib.Connection /*@, ghost sidRT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) {

	//@ t1, s1 := t, s
	//@ ghost var isFirstMessage bool = true

	//@ invariant InitiatorMem(initiator) && lib.ConnectionMem(conn)
	//@ invariant lib.ConnectionKIR(conn) == by.gamma(kirT)
	//@ invariant lib.ConnectionKRI(conn) == by.gamma(kriT)
	//@ invariant lib.ConnectionSidI(conn) == by.gamma(sidRT)
	//@ invariant  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
	//@ invariant !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
	//@ invariant pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
	//@ invariant isFirstMessage ==> ft.St_Init_2(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
	//@ invariant !isFirstMessage ==> ft.St_Init_3(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
	for {
		/*@
		ghost rid := initiator.getRid()
		unfold io.P_Init(t1, rid, s1)
		unfold io.phiRF_Init_13(t1, rid, s1)
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
			s1 = s1 union mset[ft.Fact]{ ft.Message_Init(rid, term) }
		} else {
			fold io.phiRF_Init_13(t1, rid, s1)
			fold io.P_Init(t1, rid, s1)
		}
		@*/
		//@ assert ok ==> pl.token(t1) && io.P_Init(t1, rid, s1)
		//@ assert !ok ==> pl.token(t1) && io.P_Init(t1, rid, s1)
		//@ assert isFirstMessage ==> ft.St_Init_2(rid, tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
		//@ assert !isFirstMessage ==> ft.St_Init_3(rid, tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
		if ok {
			//@ ghost var isInState3 bool
			ok /*@, isInState3, t1, s1 @*/ = initiator.sendMessage(request, conn /*@, isFirstMessage, sidRT, kirT, kriT, term, t1, s1 @*/)
			//@ isFirstMessage = !isInState3

			if ok {
				var response lib.ByteString
				var done bool = false // ADAPT
				//@ invariant acc(InitiatorMem(initiator), 1/4) && acc(lib.ConnectionMem(conn), 1/4)
				//@ invariant done ==> lib.Mem(response)
				//@ invariant pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
				//@ invariant lib.ConnectionKIR(conn) == by.gamma(kirT)
				//@ invariant lib.ConnectionKRI(conn) == by.gamma(kriT)
				//@ invariant lib.ConnectionSidI(conn) == by.gamma(sidRT)
				//@ invariant ft.St_Init_3(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
				for !done {
					response, done /*@, t1, s1 @*/ = initiator.receiveMessage(conn /*@, sidRT, kirT, kriT, t1, s1 @*/)
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
//@ requires pl.token(t) && io.P_Init(t, initiator.getRid(), s)
//@ requires ft.Message_Init(initiator.getRid(), msgTerm) in s
//@ requires lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ requires lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ requires lib.ConnectionSidI(conn) == by.gamma(sidRT)
//@ requires  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
//@ requires !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
//@ requires  isFirstMessage ==> ft.St_Init_2(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s
//@ requires !isFirstMessage ==> ft.St_Init_3(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s
//@ ensures  acc(InitiatorMem(initiator), 1/8) && lib.ConnectionMem(conn)
//@ ensures  pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
//@ ensures  lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ ensures  lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ ensures  lib.ConnectionSidI(conn) == by.gamma(sidRT)
//@ ensures  !isFirstMessage ==> isInState3
//@ ensures  ok ==> isInState3
//@ ensures  !isInState3 ==> ft.St_Init_2(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
//@ ensures  isInState3  ==> ft.St_Init_3(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
//@ ensures  !isInState3 ==> lib.ConnectionNonceVal(conn) == 0
//@ ensures  isInState3  ==> lib.ConnectionNonceVal(conn) > 0
func (initiator *Initiator) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost isFirstMessage bool, ghost sidRT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost msgTerm tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost isInState3 bool, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

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
		//@ unfold io.P_Init(t, rid, s)
		//@ unfold io.phiRF_Init_14(t, rid, s)
		//@ assert acc(io.e_Counter(t, rid))
		nonce /*@, t1 @*/ = lib.GetCounter(conn.Nonce /*@, t, rid @*/)
		//@ s1 = s union mset[ft.Fact]{ ft.Counter_Init(rid, tm.integer64(nonce)) }
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

	//@ fold lib.ConnectionMem(conn)

	packet := lib.MarshalMessage(message)

	//@ packetT := tm.tuple4(tm.integer32(4), sidRT, tm.integer64(nonce), tm.aead(kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0)))
	//@ assert lib.Abs(packet) == by.gamma(packetT)

	/*@
	ghost if (isFirstMessage) {
		unfold io.P_Init(t1, rid, s1)
		unfold io.phiR_Init_2(t1, rid, s1)

		var Q3sidI tm.Term = rid
		var Q3a tm.Term = tm.getFirst(pp)
		var Q3b tm.Term = tm.getSecond(pp)
		var Q3prologue tm.Term = tm.getThird(pp)
		var Q3info tm.Term = tm.getForth(pp)
		var Q3sidR tm.Term = sidRT
		var Q3kIR tm.Term = kirT
		var Q3kRI tm.Term = kriT
		var Q3p tm.Term = msgTerm

		l :=  tm.InternalInit3L(Q3sidI, Q3a, Q3b, Q3prologue, Q3info, Q3sidR, Q3kIR, Q3kRI, Q3p)
		aM := tm.InternalInit3A(Q3sidI, Q3a, Q3b, Q3prologue, Q3info, Q3sidR, Q3kIR, Q3kRI, Q3p)
		r :=  tm.InternalInit3R(Q3sidI, Q3a, Q3b, Q3prologue, Q3info, Q3sidR, Q3kIR, Q3kRI, Q3p)

		t1 = io.internBIO_e_Send_First_Init(t1, Q3sidI, Q3a, Q3b, Q3prologue, Q3info, Q3sidR, Q3kIR, Q3kRI, Q3p, l, aM, r)
		// remove and add facts to s1
		s1 = ft.U(l, r, s1)

		assert ft.OutFact_Init(rid, packetT) in s1
	} else {
		unfold io.P_Init(t1, rid, s1)
		unfold io.phiR_Init_3(t1, rid, s1)

		var Q4sidI tm.Term = rid
		var Q4a tm.Term = tm.getFirst(pp)
		var Q4b tm.Term = tm.getSecond(pp)
		var Q4prologue tm.Term = tm.getThird(pp)
		var Q4info tm.Term = tm.getForth(pp)
		var Q4sidR tm.Term = sidRT
		var Q4kIR tm.Term = kirT
		var Q4kRI tm.Term = kriT
		var Q4nIR tm.Term = tm.integer64(nonce)
		var Q4p tm.Term = msgTerm

		l :=  tm.InternalInit4L(Q4sidI, Q4a, Q4b, Q4prologue, Q4info, Q4sidR, Q4kIR, Q4kRI, Q4nIR, Q4p)
		aM := tm.InternalInit4A(Q4sidI, Q4a, Q4b, Q4prologue, Q4info, Q4sidR, Q4kIR, Q4kRI, Q4nIR, Q4p)
		r :=  tm.InternalInit4R(Q4sidI, Q4a, Q4b, Q4prologue, Q4info, Q4sidR, Q4kIR, Q4kRI, Q4nIR, Q4p)

		t1 = io.internBIO_e_Send_Init_Loop(t1, Q4sidI, Q4a, Q4b, Q4prologue, Q4info, Q4sidR, Q4kIR, Q4kRI, Q4nIR, Q4p, l, aM, r)
		// remove and add facts to s1
	  s1 = ft.U(l, r, s1)

		assert ft.OutFact_Init(rid, packetT) # s1 > 0
	}
	isInState3 = true
	@*/

	//@ unfold lib.ConnectionMem(conn)
	conn.Nonce += 1
	//@ fold lib.ConnectionMem(conn)

	//@ unfold io.P_Init(t1, rid, s1)
	//@ unfold io.phiRG_Init_5(t1, rid, s1)

	//@ assert ft.OutFact_Init(rid, packetT) # s1 > 0
	//@ assert io.e_OutFact(t1, rid, packetT)
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	ok /*@, t1 @*/ = (initiator.LibState).Send(packet /*@, t1, rid, packetT @*/)
	//@ fold acc(InitiatorMem(initiator), 1/8)
	/*@ ghost if ok {
		s1 = s1 setminus mset[ft.Fact]{ ft.OutFact_Init(rid, packetT) }
	} else {
		fold io.phiRG_Init_5(t1, rid, s1)
		fold io.P_Init(t1, rid, s1)
	}
	@*/

	return
}

//@ requires acc(InitiatorMem(initiator), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ requires pl.token(t) && io.P_Init(t, initiator.getRid(), s)
//@ requires ft.St_Init_3(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s
//@ requires lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ requires lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ requires lib.ConnectionSidI(conn) == by.gamma(sidRT)
//@ ensures  acc(InitiatorMem(initiator), 1/8) && acc(lib.ConnectionMem(conn), 1/8)
//@ ensures  ok ==> lib.Mem(msg)
//@ ensures  pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
//@ ensures  ft.St_Init_3(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
func (initiator *Initiator) receiveMessage(conn *lib.Connection /*@, ghost sidRT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) (msg lib.ByteString, ok bool /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := initiator.getRid()
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_12(t, rid, s)
	//@ assert acc(io.e_InFact(t, rid))
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	packet, ok /*@, term, t1 @*/ := (initiator.LibState).Receive( /*@ t, rid @*/ )
	//@ fold acc(InitiatorMem(initiator), 1/8)
	if !ok {
		//@ fold io.phiRF_Init_12(t, rid, s)
		//@ fold io.P_Init(t, rid, s)
		//@ s1 = s
		return
	}
	//@ recvB := lib.Abs(packet)
	//@ s1 = s union mset[ft.Fact]{ ft.InFact_Init(rid, term) }

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

	nRI, p := pap.patternProperty4(rid, pp, sidRT, kirT, kriT, by.oneTerm(nonceB), by.oneTerm(lib.Abs(plaintext)), term, t1, s1, true)
	assert term == tm.tuple4(tm.integer32(4), rid, nRI, tm.aead(kriT, nRI, p, tm.zeroString(0)))

	unfold io.P_Init(t1, rid, s1)
	unfold io.phiR_Init_4(t1, rid, s1)

	var Q5sidI tm.Term = rid
	var Q5a tm.Term = tm.getFirst(pp)
	var Q5b tm.Term = tm.getSecond(pp)
	var Q5prologue tm.Term = tm.getThird(pp)
	var Q5info tm.Term = tm.getForth(pp)
	var Q5sidR tm.Term = sidRT
	var Q5kIR tm.Term = kirT
	var Q5kRI tm.Term = kriT
	var Q5x tm.Term = rid
	var Q5nIR tm.Term = nRI
	var Q5p tm.Term = p

	l :=  tm.InternalInit5L(Q5sidI, Q5a, Q5b, Q5prologue, Q5info, Q5sidR, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p)
	aM := tm.InternalInit5A(Q5sidI, Q5a, Q5b, Q5prologue, Q5info, Q5sidR, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p)
	r :=  tm.InternalInit5R(Q5sidI, Q5a, Q5b, Q5prologue, Q5info, Q5sidR, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p)

	assert ft.M(l, s1)
	t1 = io.internBIO_e_Receive_Init_Loop(t1, Q5sidI, Q5a, Q5b, Q5prologue, Q5info, Q5sidR, Q5kIR, Q5kRI, Q5x, Q5nIR, Q5p, l, aM, r)
	// remove and add facts to s1
	s1 = ft.U(l, r, s1)
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}
