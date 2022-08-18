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

//@ requires acc(InitiatorMem(initiator), 1/2)
//@ requires pl.token(t) && io.P_Init(t, initiator.getRid(), s)
//@ requires ft.PsK_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), pskT) in s
//@ requires ft.LtK_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), ltkT) in s
//@ requires ft.LtpK_Init(initiator.getRid(), tm.getSecond(initiator.getPP()), ltpkT) in s
//@ requires ft.Setup_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP())) in s
//@ requires getPsk(initiator) == by.gamma(pskT)
//@ requires getKI(initiator) == by.gamma(ltkT)
//@ requires getPkR(initiator) == by.gamma(ltpkT)
//@ ensures  acc(InitiatorMem(initiator), 1/2)
//@ ensures  ok ==> lib.ConnectionMem(conn) && lib.ConnectionNonceVal(conn) == 0
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
//@ ensures  ok ==> ft.St_Init_2(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, kirT, kriT) in s1
//@ ensures  ok ==> lib.ConnectionKIR(conn) == by.gamma(kirT)
//@ ensures  ok ==> lib.ConnectionKRI(conn) == by.gamma(kriT)
//@ ensures  ok ==> lib.ConnectionSidI(conn) == by.gamma(sidRT)
func (initiator *Initiator) runHandshake( /*@ ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/ ) (conn *lib.Connection, ok bool /*@, ghost sidRT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	handshake := &lib.Handshake{}
	//@ ghost var ekiT, c3T, h4T tm.Term
	ok /*@, ekiT, c3T, h4T, t1, s1 @*/ = initiator.sendRequest(handshake /*@, pskT, ltkT, ltpkT, t, s @*/)
	if !ok {
		return
	}

	//@ assert getEkI(handshake) == by.gamma(ekiT)

	//@ unfold acc(InitiatorMem(initiator), 1/2)
	(initiator.LibState).Println("Success Sending Request")
	//@ fold acc(InitiatorMem(initiator), 1/2)

	//@ ghost var c7T tm.Term
	//@ BeforeRecvResp:
	ok /*@, sidRT, c7T, t1, s1 @*/ = initiator.receiveResponse(handshake /*@, pskT, ltkT, ltpkT, ekiT, c3T, h4T, t1, s1 @*/)
	if !ok {
		return
	}

	//@ unfold acc(InitiatorMem(initiator), 1/2)
	(initiator.LibState).Println("Success Consuming Response")
	//@ fold acc(InitiatorMem(initiator), 1/2)

	//@ BeforeSymSess:
	conn = initiator.beginSymmetricSession(handshake /*@, c7T @*/)

	//@ kirT = tm.kdf1_(c7T)
	//@ kriT = tm.kdf2_(c7T)

	return
}

//@ requires acc(InitiatorMem(initiator), 1/4) && acc(hs)
//@ requires pl.token(t) && io.P_Init(t, initiator.getRid(), s)
//@ requires ft.PsK_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), pskT) in s
//@ requires ft.LtK_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), ltkT) in s
//@ requires ft.LtpK_Init(initiator.getRid(), tm.getSecond(initiator.getPP()), ltpkT) in s
//@ requires ft.Setup_Init(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP())) in s
//@ requires getPsk(initiator) == by.gamma(pskT)
//@ requires getKI(initiator) == by.gamma(ltkT)
//@ requires getPkR(initiator) == by.gamma(ltpkT)
//@ ensures  acc(InitiatorMem(initiator), 1/4)
//@ ensures  ok ==> HandshakeMem(hs)
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
//@ ensures  ok ==> ft.St_Init_1(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), ltkT, ltpkT, ekiT, pskT, c3T, h4T) in s1
//@ ensures  ok ==> getEkI(hs) == by.gamma(ekiT)
//@ ensures  ok ==> getNKey(hs) == by.gamma(c3T)
//@ ensures  ok ==> getNHash(hs) == by.gamma(h4T)
func (initiator *Initiator) sendRequest(hs *lib.Handshake /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost ekiT tm.Term, ghost c3T tm.Term, ghost h4T tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := initiator.getRid()
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_9(t, rid, s)
	//@ assert acc(io.e_FrFact(t, rid))
	var newPk lib.ByteString
	//@ ekiT := io.get_e_FrFact_r1(t, rid)
	newPk, ok /*@, t1 @*/ = lib.NewPrivateKey( /*@ t, rid @*/ )
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.FrFact_Init(rid, ekiT) }

	//@ unfold io.P_Init(t1, rid, s1)
	//@ unfold io.phiRF_Init_10(t1, rid, s1)
	//@ assert acc(io.e_Timestamp(t1, rid))
	var newTs lib.ByteString
	_ = newTs // stops go's syntactic check from complaining
	//@ tsT := io.get_e_Timestamp_r1(t1, rid)
	newTs /*@, t1 @*/ = lib.Timestamp( /*@ t1, rid @*/ )
	//@ s1 = s1 union mset[ft.Fact]{ ft.Timestamp_Init(rid, tsT) }

	//@ sidI, kI, pkR, psk, ekI, ts := getSidI(initiator), getKI(initiator), getPkR(initiator), getPsk(initiator), lib.Abs(newPk), lib.Abs(newTs)

	request, ok := initiator.createRequest(hs, newPk, newTs)
	if !ok {
		return
	}

	packet := lib.MarshalRequest(request)
	//@ pp := initiator.getPP()
	//@ unfold acc(InitiatorMem(initiator), 1/4)

	//@ unfold io.P_Init(t1, rid, s1)
	//@ unfold io.phiRF_Init_11(t1, rid, s1)
	//@ ghost mac1T := io.get_e_MAC_r1(t1, rid)
	/*@ mac1, t1 := @*/
	(initiator.LibState).AddMac1(packet /*@, Bytes_M1(sidI, kI, pkR, ekI, ts, by.zeroStringB(16), by.zeroStringB(16)), t1, rid @*/)
	//@ s1 = s1 union mset[ft.Fact]{ ft.MAC_Init(rid, mac1T) }

	//@ unfold io.P_Init(t1, rid, s1)
	//@ unfold io.phiRF_Init_11(t1, rid, s1)
	//@ ghost mac2T := io.get_e_MAC_r1(t1, rid)
	/*@ mac2, t1 := @*/
	(initiator.LibState).AddMac2(packet /*@, Bytes_M1(sidI, kI, pkR, ekI, ts, by.gamma(mac1T), by.zeroStringB(16)), t1, rid @*/)
	//@ s1 = s1 union mset[ft.Fact]{ ft.MAC_Init(rid, mac2T) }

	//@ assert lib.Abs(packet) == by.gamma(Term_M1(rid, ltkT, ltpkT, ekiT, tsT, mac1T, mac2T))

	//@ c3T = Term_c3(ltkT, ltpkT, ekiT)
	//@ h4T = Term_h4(ltkT, ltpkT, ekiT, tsT)

	//@ unfold io.P_Init(t1, rid, s1)
	//@ unfold io.phiR_Init_0(t1, rid, s1)
	/*@
			var Q1sidI tm.Term = rid
			var Q1a tm.Term = tm.getFirst(pp)
			var Q1b tm.Term = tm.getSecond(pp)
			var Q1prologue tm.Term = tm.getThird(pp)
			var Q1info tm.Term = tm.getForth(pp)
			var Q1kI tm.Term = ltkT
			var Q1pkR tm.Term = ltpkT
			var Q1psk tm.Term = pskT
			var Q1ekI tm.Term  = ekiT
			var Q1timestamp tm.Term = tsT
			var Q1mac1I tm.Term = mac1T
			var Q1mac2I tm.Term = mac2T

			l :=  tm.InternalInit1L(Q1sidI, Q1a, Q1b, Q1prologue, Q1info, Q1kI, Q1pkR, Q1psk, Q1ekI, Q1timestamp, Q1mac1I, Q1mac2I)
			aM := tm.InternalInit1A(Q1sidI, Q1a, Q1b, Q1prologue, Q1info, Q1kI, Q1pkR, Q1psk, Q1ekI, Q1timestamp, Q1mac1I, Q1mac2I)
			r :=  tm.InternalInit1R(Q1sidI, Q1a, Q1b, Q1prologue, Q1info, Q1kI, Q1pkR, Q1psk, Q1ekI, Q1timestamp, Q1mac1I, Q1mac2I)

			t1 = io.internBIO_e_Handshake_St_Init_1(t1, Q1sidI, Q1a, Q1b, Q1prologue, Q1info, Q1kI, Q1pkR, Q1psk, Q1ekI, Q1timestamp, Q1mac1I, Q1mac2I, l, aM, r)
			// remove and add facts to s1
	        s1 = ft.U(l, r, s1)
		@*/

	//@ unfold io.P_Init(t1, rid, s1)
	//@ unfold io.phiRG_Init_5(t1, rid, s1)
	//@ packetTerm := Term_M1(rid, ltkT, ltpkT, ekiT, tsT, mac1T, mac2T)
	//@ assert ft.OutFact_Init(rid, packetTerm) in s1

	ok /*@, t1 @*/ = (initiator.LibState).Send(packet /*@, t1, rid, packetTerm @*/)
	//@ fold acc(InitiatorMem(initiator), 1/4)
	//@ s1 = s1 setminus mset[ft.Fact]{ ft.OutFact_Init(rid, packetTerm) }

	return
}

//@ requires acc(InitiatorMem(initiator), 1/8) && acc(hs)
//@ requires lib.Mem(newPk) && lib.Size(newPk) == 32 && lib.Mem(newTs) && lib.Size(newTs) == 12
//@ ensures  acc(InitiatorMem(initiator), 1/8)
//@ ensures  ok ==> HandshakeMem(hs) && lib.RequestMem(request)
//@ ensures  ok ==> lib.RequestAbs(request) == Bytes_M1(getSidI(initiator), getKI(initiator), getPkR(initiator), old(lib.Abs(newPk)), old(lib.Abs(newTs)), by.zeroStringB(16),by.zeroStringB(16))
//@ ensures  ok ==> getNHash(hs) == Bytes_h4(getKI(initiator), getPkR(initiator), old(lib.Abs(newPk)), old(lib.Abs(newTs)))
//@ ensures  ok ==> getNKey(hs) == Bytes_c3(getKI(initiator), getPkR(initiator), old(lib.Abs(newPk)))
//@ ensures  ok ==> getEkI(hs) == old(lib.Abs(newPk))
func (initiator *Initiator) createRequest(hs *lib.Handshake, newPk, newTs lib.ByteString) (request *lib.Request, ok bool) {

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	args := &initiator.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)

	//@ kI  := lib.Abs(args.PrivateKey)
	//@ pkR := lib.Abs(args.RemoteStatic)
	//@ ekI := lib.Abs(newPk)
	//@ ts  := lib.Abs(newTs)

	hs.ChainKey = lib.ComputeSingleHash(lib.WireGuardBytes())
	// ChainKey == c0
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c0()
	hs.ChainHash = lib.NewByteString(32)
	lib.ComputeHash(hs.ChainHash, hs.ChainKey, lib.PreludeBytes())
	// ChainHash == h0
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h0()

	hs.LocalEphemeral = newPk
	// localEphemeral == ekI

	publicEphemeral := lib.PublicKey(hs.LocalEphemeral)
	// publicEphemeral == epk_I

	lib.ComputeHashInplace(hs.ChainHash, args.RemoteStatic)
	// ChainHash == h1
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h1(pkR)

	lib.ComputeKDF1Inplace(hs.ChainKey, publicEphemeral)
	// hs.ChainKey == c1
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c1(ekI)
	lib.ComputeHashInplace(hs.ChainHash, publicEphemeral)
	// hs.ChainHash == h2
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h2(pkR, ekI)

	ss := lib.ComputeSharedSecret(hs.LocalEphemeral, args.RemoteStatic)
	// ss == g^(k_R * ek_I) == (g^k_R)^ek_I

	if lib.IsZero(ss) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return nil, false
	}

	key := lib.NewByteString(32)
	lib.ComputeKDF2Inplace(key, hs.ChainKey, ss)
	// ChainKey == c2
	// key == k1 == kdf2(<c1, g^(k_R * ek_I)>)
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c2(pkR, ekI)
	//@ assert lib.Abs(key) == Bytes_k1(pkR, ekI)

	encryptedStaticPk, ok := lib.AeadEnc(key, lib.ZeroNonce(), args.LocalStatic, hs.ChainHash)
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}
	// encryptedStaticPk == c_pk_I
	//@ assert lib.Abs(encryptedStaticPk) == Bytes_c_pkI(kI, pkR, ekI)

	lib.ComputeHashInplace(hs.ChainHash, encryptedStaticPk)
	// ChainHash == h3
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h3(kI, pkR, ekI)

	sharedStatic := lib.ComputeSharedSecret(args.PrivateKey, args.RemoteStatic)
	// sharedStatic == g^(k_R * k_I)

	if lib.IsZero(sharedStatic) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return nil, false
	}

	lib.ComputeKDF2Inplace(key, hs.ChainKey, sharedStatic)
	// key == k2 == kdf2(c2, g^(k_R * k_I))
	// ChainKey == c3
	//@ assert lib.Abs(key) == Bytes_k2(kI, pkR, ekI)
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c3(kI, pkR, ekI)

	timestamp, ok := lib.AeadEnc(key, lib.ZeroNonce(), newTs, hs.ChainHash)
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}
	// timestamp == c_t2
	//@ assert lib.Abs(timestamp) == Bytes_c_ts(kI, pkR, ekI, ts)

	request = &lib.Request{
		Type:      1,
		Sender:    args.LocalIndex,
		Ephemeral: publicEphemeral,
		Static:    encryptedStaticPk,
		Timestamp: timestamp,
	}

	lib.ComputeHashInplace(hs.ChainHash, timestamp)
	// ChainHash == h4
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h4(kI, pkR, ekI, ts)

	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(InitiatorMem(initiator), 1/8)
	//@ fold lib.RequestMem(request)
	//@ fold HandshakeMem(hs)

	return
}

//@ requires acc(InitiatorMem(initiator), 1/4) && HandshakeMem(hs)
//@ requires pl.token(t) && io.P_Init(t, initiator.getRid(), s)
//@ requires ft.St_Init_1(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), ltkT, ltpkT, ekiT, pskT, c3T, h4T) in s
//@ requires getPsk(initiator) == by.gamma(pskT)
//@ requires getKI(initiator) == by.gamma(ltkT)
//@ requires getPkR(initiator) == by.gamma(ltpkT)
//@ requires getEkI(hs) == by.gamma(ekiT)
//@ requires getNKey(hs) == by.gamma(c3T)
//@ requires getNHash(hs) == by.gamma(h4T)
//@ ensures  acc(InitiatorMem(initiator), 1/4) && HandshakeMem(hs)
//@ ensures  getEkI(hs) == old(getEkI(hs))
//@ ensures  ok ==> pl.token(t1) && io.P_Init(t1, initiator.getRid(), s1)
//@ ensures  ok ==> ft.St_Init_2(initiator.getRid(), tm.getFirst(initiator.getPP()), tm.getSecond(initiator.getPP()), tm.getThird(initiator.getPP()), tm.getForth(initiator.getPP()), sidRT, tm.kdf1_(c7T), tm.kdf2_(c7T)) in s1
//@ ensures  ok ==> getNKey(hs) == by.gamma(c7T) && getSidR(hs) == by.gamma(sidRT)
func (initiator *Initiator) receiveResponse(hs *lib.Handshake /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost ekiT tm.Term, ghost c3T tm.Term, ghost h4T tm.Term, ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost sidRT tm.Term, ghost c7T tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := initiator.getRid()
	//@ unfold io.P_Init(t, rid, s)
	//@ unfold io.phiRF_Init_12(t, rid, s)
	//@ assert acc(io.e_InFact(t, rid))
	//@ unfold acc(InitiatorMem(initiator), 1/4)
	packet, ok /*@, term, t1 @*/ := (initiator.LibState).Receive( /*@ t, rid @*/ )
	//@ fold acc(InitiatorMem(initiator), 1/4)
	if !ok {
		return
	}
	//@ recvB := lib.Abs(packet)
	//@ s1 := s union mset[ft.Fact]{ ft.InFact_Init(rid, term) }

	response, ok := lib.UnmarshalResponse(packet)
	if !ok {
		return
	}

	//@ BeforeConsume:
	ok = initiator.consumeResponse(hs, response)
	if !ok {
		return
	}

	/*@
	ghost if ok {
		pp   := initiator.getPP()
		sidI := old(getSidI(initiator))
		kI   := old(getKI(initiator))
		pkR  := old(getPkR(initiator))
		psk  := old(getPsk(initiator))
		ekI  := old(getEkI(hs))
		c3   := old(getNKey(hs))
		h4   := old(getNHash(hs))

		sidR := getSidR(hs)
		epkR := old[BeforeConsume](lib.ResponseEpkR(response))
		mac1 := old[BeforeConsume](lib.ResponseMac1(response))
		mac2 := old[BeforeConsume](lib.ResponseMac2(response))

		assert recvB == Bytes_M2(sidI, sidR, kI, psk, ekI, c3, h4, epkR, mac1, mac2)
		assert getNKey(hs) == Bytes_c7(kI, psk, ekI, c3, epkR)

		assert getNKey(hs) == by.gamma(Term_c7(ltkT, pskT, ekiT, c3T, by.oneTerm(epkR)))

		var sidRX, epkRX, mac1X, mac2X tm.Term
		assert by.gamma(term) == by.gamma(Term_M2(rid, by.oneTerm(sidR), ltkT, pskT, ekiT, c3T, h4T, by.oneTerm(epkR), by.oneTerm(mac1), by.oneTerm(mac2)))
		sidRX, epkRX, mac1X, mac2X = pap.patternProperty1(rid, pp, ltkT, ltpkT, pskT, ekiT, c3T, h4T, by.oneTerm(sidR), by.oneTerm(epkR), by.oneTerm(mac1), by.oneTerm(mac2), term, t1, s1)
		assert term == Term_M2(rid, sidRX, ltkT, pskT, ekiT, c3T, h4T, epkRX, mac1X, mac2X)
		cEmpty := Term_c_empty(ltkT, pskT, ekiT, c3T, h4T, epkRX)
		kIR := Bytes_k_IR(kI, psk, ekI, c3, epkR)
		kRI := Bytes_k_RI(kI, psk, ekI, c3, epkR)

		sidRT = sidRX
		assert getSidR(hs) == by.gamma(sidRT)
		c7T = Term_c7(ltkT, pskT, ekiT, c3T, epkRX)
		kirT := Term_k_IR(ltkT, pskT, ekiT, c3T, epkRX)
		kriT := Term_k_RI(ltkT, pskT, ekiT, c3T, epkRX)

		unfold io.P_Init(t1, rid, s1)
		unfold io.phiR_Init_1(t1, rid, s1)

		var Q2sidI tm.Term = rid
		var Q2a tm.Term = tm.getFirst(pp)
		var Q2b tm.Term = tm.getSecond(pp)
		var Q2prologue tm.Term = tm.getThird(pp)
		var Q2info tm.Term = tm.getForth(pp)
		var Q2kI tm.Term = ltkT
		var Q2pkR tm.Term = ltpkT
		var Q2ekI tm.Term = ekiT
		var Q2psk tm.Term = pskT
		var Q2c3 tm.Term = c3T
		var Q2h4 tm.Term = h4T
		var Q2sidR tm.Term = sidRX
		var Q2epkR tm.Term = epkRX
		var Q2mac1R tm.Term = mac1X
		var Q2mac2R tm.Term = mac2X

		l :=  tm.InternalInit2L(Q2sidI, Q2a, Q2b, Q2prologue, Q2info, Q2kI, Q2pkR, Q2ekI, Q2psk, Q2c3, Q2h4, Q2sidR, Q2epkR, Q2mac1R, Q2mac2R)
		aM := tm.InternalInit2A(Q2sidI, Q2a, Q2b, Q2prologue, Q2info, Q2kI, Q2pkR, Q2ekI, Q2psk, Q2c3, Q2h4, Q2sidR, Q2epkR, Q2mac1R, Q2mac2R)
		r :=  tm.InternalInit2R(Q2sidI, Q2a, Q2b, Q2prologue, Q2info, Q2kI, Q2pkR, Q2ekI, Q2psk, Q2c3, Q2h4, Q2sidR, Q2epkR, Q2mac1R, Q2mac2R)

		t1 = io.internBIO_e_Handshake_St_Init_2(t1, Q2sidI, Q2a, Q2b, Q2prologue, Q2info, Q2kI, Q2pkR, Q2ekI, Q2psk, Q2c3, Q2h4, Q2sidR, Q2epkR, Q2mac1R, Q2mac2R, l, aM, r)

		// remove and add facts to s1
		s1 = ft.U(l, r, s1)
	}
	@*/

	return
}

//@ requires acc(InitiatorMem(initiator), 1/8) && HandshakeMem(hs) && lib.ResponseMem(response)
//@ ensures  acc(InitiatorMem(initiator), 1/8) && HandshakeMem(hs)
//@ ensures  getEkI(hs) == old(getEkI(hs))
//@ ensures  ok ==> old(lib.ResponseAbs(response)) == Bytes_M2(getSidI(initiator), getSidR(hs), getKI(initiator), getPsk(initiator), old(getEkI(hs)), old(getNKey(hs)), old(getNHash(hs)), old(lib.ResponseEpkR(response)), old(lib.ResponseMac1(response)), old(lib.ResponseMac2(response)))
//@ ensures  ok ==> getNKey(hs) == Bytes_c7(getKI(initiator), getPsk(initiator), old(getEkI(hs)), old(getNKey(hs)), old(lib.ResponseEpkR(response)))
func (initiator *Initiator) consumeResponse(hs *lib.Handshake, response *lib.Response) (ok bool) {

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	args := &initiator.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ unfold HandshakeMem(hs)
	//@ unfold lib.ResponseMem(response)

	//@ kI := lib.Abs(args.PrivateKey)
	//@ psk := lib.Abs(args.PresharedKey)
	//@ ekI := lib.Abs(hs.LocalEphemeral)
	//@ c3 := lib.Abs(hs.ChainKey)
	//@ h4 := lib.Abs(hs.ChainHash)
	//@ epkR := lib.Abs(response.Ephemeral)

	ok = response.Type == 2
	if !ok {
		//@ fold HandshakeMem(hs)
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}

	ok = response.Receiver == args.LocalIndex
	if !ok {
		//@ fold HandshakeMem(hs)
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}

	chainHash := lib.NewByteString(32)
	chainKey := lib.NewByteString(32)

	lib.ComputeHash(chainHash, hs.ChainHash, response.Ephemeral)
	// chainHash == h5 == hash(<h4, epk_R>)
	//@ assert lib.Abs(chainHash) == Bytes_h5(h4, epkR)
	lib.ComputeKDF1(chainKey, hs.ChainKey, response.Ephemeral)
	// chainKey == c4
	//@ assert lib.Abs(chainKey) == Bytes_c4(c3, epkR)

	{
		ss := lib.ComputeSharedSecret(hs.LocalEphemeral, response.Ephemeral)
		// ss == epk_R^k_I == (g^ek_R)^ek_I
		lib.ComputeKDF1Inplace(chainKey, ss)
		// chainKey == c5
		lib.SetZero(ss)
	}
	//@ assert lib.Abs(chainKey) == Bytes_c5(ekI, c3, epkR)

	{
		ss := lib.ComputeSharedSecret(args.PrivateKey, response.Ephemeral)
		// ss == (g^ek_R)^k_I
		lib.ComputeKDF1Inplace(chainKey, ss)
		// chainKey == c6
		lib.SetZero(ss)
	}
	//@ assert lib.Abs(chainKey) == Bytes_c6(kI, ekI, c3, epkR)

	tau := lib.NewByteString(32)
	key := lib.NewByteString(32)
	lib.ComputeKDF3Inplace(tau, key, chainKey, args.PresharedKey)
	// chainKey == c7
	// tau == pi
	// key == k3
	//@ assert lib.Abs(chainKey) == Bytes_c7(kI, psk, ekI, c3, epkR)
	//@ assert lib.Abs(tau) == Bytes_pi(kI, psk, ekI, c3, epkR)
	//@ assert lib.Abs(key) == Bytes_k3(kI, psk, ekI, c3, epkR)

	lib.ComputeHashInplace(chainHash, tau)
	// chainHash == h6
	//@ assert lib.Abs(chainHash) == Bytes_h6(kI, psk, ekI, c3, h4, epkR)

	// authenticate transcript

	_, ok = lib.AeadDec(key, lib.ZeroNonce(), response.Empty, chainHash)
	// only check whether c_empty can be decrypted
	if !ok {
		//@ fold HandshakeMem(hs)
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}
	//@ assert lib.Abs(response.Empty) == Bytes_c_empty(kI, psk, ekI, c3, h4, epkR)

	lib.ComputeHashInplace(chainHash, response.Empty)
	// chainHash == hash(<h6, c_empty>)

	hs.ChainHash = chainHash
	hs.ChainKey = chainKey
	hs.RemoteIndex = response.Sender

	//@ fold HandshakeMem(hs)
	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(InitiatorMem(initiator), 1/8)

	return
}

//@ requires acc(InitiatorMem(initiator), 1/4) && HandshakeMem(hs)
//@ requires getNKey(hs) == by.gamma(c7T)
//@ ensures  acc(InitiatorMem(initiator), 1/4) && lib.ConnectionMem(conn)
//@ ensures  lib.ConnectionKIR(conn) == by.gamma(tm.kdf1_(c7T))
//@ ensures  lib.ConnectionKRI(conn) == by.gamma(tm.kdf2_(c7T))
//@ ensures  lib.ConnectionNonceVal(conn) == 0
//@ ensures  lib.ConnectionSidI(conn) == old(getSidR(hs))
func (initiator *Initiator) beginSymmetricSession(hs *lib.Handshake /*@, ghost c7T tm.Term @*/) (conn *lib.Connection) {

	sendKey := lib.NewByteString(32)
	recvKey := lib.NewByteString(32)
	//@ unfold HandshakeMem(hs)
	lib.ComputeKDF2(sendKey, recvKey, hs.ChainKey, nil)
	// sendKey == kdf1(c7) == k_IR
	// recvKey == kdf2(c7) == k_RI

	// zero handshake
	hs.ChainKey = nil
	hs.ChainHash = nil
	hs.LocalEphemeral = nil

	conn = &lib.Connection{
		Nonce:       0,
		SendKey:     sendKey,
		RecvKey:     recvKey,
		RemoteIndex: hs.RemoteIndex,
	}

	//@ fold lib.ConnectionMem(conn)

	return
}
