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


//@ requires acc(ResponderMem(responder), 1/2)
//@ requires pl.token(t) && io.P_r(t, responder.getRid(), s)
//@ requires len(v) == 3
//@ requires ft.ltK(tm.getSecond(responder.getPP()), v[0]) in s && by.gamma(v[0]) == getKR(responder)
//@ requires ft.ltpK(tm.getFirst(responder.getPP()), v[1]) in s && by.gamma(v[1]) == getPkI(responder)
//@ requires ft.psK(tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), v[2]) in s && by.gamma(v[2]) == getPsk(responder)
//@ requires ft.resp0(responder.getRid(), responder.getPP()) in s
//@ ensures  acc(ResponderMem(responder), 1/2)
//@ ensures  ok ==> lib.ConnectionMem(conn)
//@ ensures  ok ==> pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
//@ ensures  ok ==> len(v1) == 6
//@ ensures  ok ==> ft.resp2(responder.getRid(), responder.getPP(), v1[4], v1[5], tm.zeroString(1), tm.zeroString(1)) in s1
//@ ensures  ok ==> by.gamma(v1[0]) == lib.ConnectionSidI(conn) && by.gamma(v1[1]) == getKR(responder) && by.gamma(v1[2]) == getPkI(responder) && by.gamma(v1[3]) == getPsk(responder) && by.gamma(v1[4]) == lib.ConnectionKRI(conn) && by.gamma(v1[5]) == lib.ConnectionKIR(conn)
//@ ensures  ok ==> lib.ConnectionNonceVal(conn) == 0
func (responder *Responder) runHandshake(/*@ ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (conn *lib.Connection, ok bool /*@, ghost v1 seq[tm.Term], ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	handshake := &lib.Handshake{}
	ok /*@, v1, t1, s1 @*/ = responder.receiveRequest(handshake /*@, v, t, s @*/)
	if !ok {
		return
	}

	//@ unfold acc(ResponderMem(responder), 1/4)
	(responder.LibState).Println("Success Consuming Request")
	//@ fold acc(ResponderMem(responder), 1/4)

	ok /*@, v1, t1, s1 @*/ = responder.sendResponse(handshake /*@, v1, t1, s1 @*/)
	if !ok {
		return
	}

	//@ unfold acc(ResponderMem(responder), 1/4)
	(responder.LibState).Println("Success Sending Response")
	//@ fold acc(ResponderMem(responder), 1/4)

	conn = responder.beginSymmetricSession(handshake)
	//@ v1 = seq[tm.Term]{ v1[0], v1[1], v1[2], v1[3], tm.kdf1(v1[4]), tm.kdf2(v1[4]) }
	return
}

//@ requires acc(ResponderMem(responder), 1/4) && acc(hs)
//@ requires pl.token(t) && io.P_r(t, responder.getRid(), s)
//@ requires len(v) == 3
//@ requires ft.ltK(tm.getSecond(responder.getPP()), v[0]) in s && by.gamma(v[0]) == getKR(responder)
//@ requires ft.ltpK(tm.getFirst(responder.getPP()), v[1]) in s && by.gamma(v[1]) == getPkI(responder)
//@ requires ft.psK(tm.getFirst(responder.getPP()), tm.getSecond(responder.getPP()), v[2]) in s && by.gamma(v[2]) == getPsk(responder)
//@ requires ft.resp0(responder.getRid(), responder.getPP()) in s
//@ ensures  acc(ResponderMem(responder), 1/4)
//@ ensures  ok ==> HandshakeMem1(hs)
//@ ensures  ok ==> pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
//@ ensures  ok ==> len(v1) == 7
//@ ensures  ok ==> ft.resp1(responder.getRid(), responder.getPP(), v1[2], v1[1], v1[4], v1[3], v1[5], v1[6], v1[0]) in s1
//@ ensures  ok ==> by.gamma(v1[0]) == getSidI1(hs) && by.gamma(v1[1]) == getKR(responder) && by.gamma(v1[2]) == getPkI(responder) && by.gamma(v1[3]) == getPsk(responder) && by.gamma(v1[4]) == getEpkI1(hs) && by.gamma(v1[5]) == getNKey1(hs) && by.gamma(v1[6]) == getNHash1(hs) 
func (responder *Responder) receiveRequest(hs *lib.Handshake /*@, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost v1 seq[tm.Term], ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	
	//@ unfold acc(ResponderMem(responder), 1/4)
	//@ unfold io.P_r(t, rid, s)
	//@ unfold io.P_r7(t, rid, s)
	packet, ok /*@, msg, t1 @*/ := (responder.LibState).Receive(/*@ t, rid @*/)
	//@ s1 = s union mset[ft.Fact]{ ft.inFact(msg) }
	//@ fold acc(ResponderMem(responder), 1/4)
	if !ok {
		return
	}
	//@ b := lib.Abs(packet)

	request, ok := lib.UnmarshalRequest(packet)
	if !ok {
		return
	}

	//@ BeforeConsume:
	//@ ghost var ts by.Bytes
	ok /*@, ts @*/ = responder.consumeRequest(hs, request)

	/*@
	ghost if ok {
		sidI := getSidI1(hs)
		kR := old(getKR(responder))
		pkI := old(getPkI(responder))
		epkI := getEpkI1(hs)
		mac1 := old[BeforeConsume](lib.RequestMac1(request))
		mac2 := old[BeforeConsume](lib.RequestMac2(request))

		assert b == Bytes_M1(sidI,kR,pkI,epkI,ts,mac1,mac2)
		assert getNKey1(hs) == Bytes_c3(kR,pkI,epkI)
		assert getNHash1(hs) == Bytes_h4(kR,pkI,epkI,ts)

		sidIX, epkIX, tsX, mac1X, mac2X := pap.patternProperty3(rid, pp, v[0],v[1],by.oneTerm(sidI),by.oneTerm(epkI),by.oneTerm(ts),by.oneTerm(mac1),by.oneTerm(mac2),msg,t1,s1)

		assert msg == Term_M1(sidIX,v[0],v[1],epkIX,tsX,mac1X,mac2X)
		assert getNKey1(hs) == by.gamma(Term_c3(v[0],v[1],epkIX))
		assert getNHash1(hs) == by.gamma(Term_h4(v[0],v[1],epkIX,tsX))

		theta := th.createThetaR1(pp, v[0],v[1],sidIX,v[2],v[2],epkIX,tsX,mac1X,mac2X)
		l := mset[ft.Fact]{ 
			ft.resp0(rid, pp),
			ft.ltK(tm.getSecond(pp), th.getKR(theta)), 
			ft.ltpK(tm.getFirst(pp), th.getPkI(theta)),
			ft.psK(tm.getFirst(pp), tm.getSecond(pp), th.getPsk(theta)), 
			ft.inFact(Term_M1(th.getSidI(theta), th.getKR(theta), th.getPkI(theta), th.getEpkI(theta), th.getTs(theta), th.getMac1I(theta), th.getMac2I(theta))),
		}
		a := mset[cl.Claim]{ }
		r := mset[ft.Fact]{ 
			ft.resp1(rid, pp, th.getPkI(theta), th.getKR(theta), th.getEpkI(theta), th.getPsk(theta), Term_c3(th.getKR(theta), th.getPkI(theta), th.getEpkI(theta)), Term_h4(th.getKR(theta), th.getPkI(theta), th.getEpkI(theta), th.getTs(theta)), th.getSidI(theta)),
		}
		unfold io.P_r(t1, rid, s1)
		unfold io.P_r1(t1, rid, s1) 
		t1 = io.internalBio1R(t1,theta,l,a,r)
		s1 = ft.U(l,r,s1)
		v1 = seq[tm.Term] { sidIX, v[0], v[1], v[2], epkIX, Term_c3(v[0],v[1],epkIX), Term_h4(v[0],v[1],epkIX,tsX) }
	}
	@*/
	return
}

//@ requires acc(ResponderMem(responder), 1/8) && acc(hs) && lib.RequestMem(request)
//@ ensures  acc(ResponderMem(responder), 1/8)
//@ ensures  ok ==> HandshakeMem1(hs)
//@ ensures  ok ==> old(lib.RequestAbs(request)) == Bytes_M1(getSidI1(hs),getKR(responder),getPkI(responder),getEpkI1(hs),ts,old(lib.RequestMac1(request)),old(lib.RequestMac2(request)))
//@ ensures  ok ==> getNKey1(hs) == Bytes_c3(getKR(responder),getPkI(responder),getEpkI1(hs))
//@ ensures  ok ==> getNHash1(hs) == Bytes_h4(getKR(responder),getPkI(responder),getEpkI1(hs),ts)
func (responder *Responder) consumeRequest(hs *lib.Handshake, request *lib.Request) (ok bool /*@, ghost ts by.Bytes @*/) {

	//@ unfold acc(ResponderMem(responder), 1/8)
	args := &responder.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ unfold lib.RequestMem(request)

	//@ kR := lib.Abs(args.PrivateKey)
	//@ pkI := lib.Abs(args.RemoteStatic)
	//@ epkI := lib.Abs(request.Ephemeral)

	ok = request.Type == 1
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return
	}

	chainKey := lib.ComputeSingleHash(lib.WireGuardBytes())
	// chainKey == c0
	//@ assert lib.Abs(chainKey) == Bytes_c0()
	chainHash := lib.NewByteString(32)
	lib.ComputeHash(chainHash, chainKey, lib.PreludeBytes())
	// chainHash == h0
	//@ assert lib.Abs(chainHash) == Bytes_h0()

	lib.ComputeHashInplace(chainHash, args.LocalStatic)
	// chainHash == h1
	//@ assert lib.Abs(chainHash) == Bytes_h1(kR)
	lib.ComputeHashInplace(chainHash, request.Ephemeral)
	// chainHash == h2
	//@ assert lib.Abs(chainHash) == Bytes_h2(kR, epkI)
	lib.ComputeKDF1Inplace(chainKey, request.Ephemeral)
	// chainKey == c1
	//@ assert lib.Abs(chainKey) == Bytes_c1(epkI)

	ss := lib.ComputeSharedSecret(args.PrivateKey, request.Ephemeral)
	// ss == g^(k_R * ek_I) == (g^ek_I)^k_R

	if lib.IsZero(ss) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return false /*@, ts @*/
	}

	key := lib.NewByteString(32)
	lib.ComputeKDF2Inplace(key, chainKey, ss)
	// chainKey == c2
	// key == k1 == kdf2(<c1, g^(k_R * ek_I)>)
	//@ assert lib.Abs(chainKey) == Bytes_c2(kR, epkI)
	//@ assert lib.Abs(key) == Bytes_k1(kR, epkI)

	peerPK, ok := lib.AeadDec(key, lib.ZeroNonce(), request.Static, chainHash)
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return
	}
	// peerPK == pk_I

	lib.ComputeHashInplace(chainHash, request.Static)
	// chainHash == h3

	if !lib.EqualsSlice(args.RemoteStatic, peerPK) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return false /*@, ts @*/
	}
	//@ assert lib.Abs(request.Static) == Bytes_c_pkI(kR, pkI, epkI)
	//@ assert lib.Abs(chainHash) == Bytes_h3(kR, pkI, epkI)

	sharedStatic := lib.ComputeSharedSecret(args.PrivateKey, args.RemoteStatic)
	// sharedStatic == g^(k_R * k_I)

	if lib.IsZero(sharedStatic) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return false /*@, ts @*/
	}

	lib.ComputeKDF2Inplace(key, chainKey, sharedStatic)
	// chainKey == c3
	// key == k2 == kdf2(c2, g^(k_R * k_I))
	//@ assert lib.Abs(chainKey) == Bytes_c3(kR, pkI, epkI)
	//@ assert lib.Abs(key) == Bytes_k2(kR, pkI, epkI)

	_, ok = lib.AeadDec(key, lib.ZeroNonce(), request.Timestamp, chainHash)
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return
	}
	// result corresponds to decrypted timestamp from c_ts
	//@ ts = by.decryptB(lib.Abs(key), by.zeroStringB(12), lib.Abs(request.Timestamp))
	//@ assert lib.Abs(request.Timestamp) == Bytes_c_ts(kR, pkI, epkI, ts)

	lib.ComputeHashInplace(chainHash, request.Timestamp)
	// ChainHash == h4
	//@ assert lib.Abs(chainHash) == Bytes_h4(kR, pkI, epkI, ts)

	hs.ChainHash = chainHash
	hs.ChainKey = chainKey
	hs.RemoteIndex = request.Sender
	hs.RemoteEphemeral = request.Ephemeral

	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(ResponderMem(responder), 1/8)
	//@ fold HandshakeMem1(hs)

	return
}

//@ requires acc(ResponderMem(responder), 1/4) && HandshakeMem1(hs)
//@ requires pl.token(t) && io.P_r(t, responder.getRid(), s)
//@ requires len(v) == 7
//@ requires ft.resp1(responder.getRid(), responder.getPP(), v[2], v[1], v[4], v[3], v[5], v[6], v[0]) in s
//@ requires by.gamma(v[0]) == getSidI1(hs) && by.gamma(v[1]) == getKR(responder) && by.gamma(v[2]) == getPkI(responder) && by.gamma(v[3]) == getPsk(responder) && by.gamma(v[4]) == getEpkI1(hs) && by.gamma(v[5]) == getNKey1(hs) && by.gamma(v[6]) == getNHash1(hs) 
//@ ensures  acc(ResponderMem(responder), 1/4)
//@ ensures  ok ==> HandshakeMem2(hs)
//@ ensures  ok ==> pl.token(t1) && io.P_r(t1, responder.getRid(), s1)
//@ ensures  ok ==> len(v1) == 5
//@ ensures  ok ==> ft.resp2(responder.getRid(), responder.getPP(), tm.kdf1(v1[4]), tm.kdf2(v1[4]), tm.zeroString(1), tm.zeroString(1)) in s1
//@ ensures  ok ==> by.gamma(v1[0]) == getSidI2(hs) && by.gamma(v1[1]) == getKR(responder) && by.gamma(v1[2]) == getPkI(responder) && by.gamma(v1[3]) == getPsk(responder) && by.gamma(v1[4]) == getNKey2(hs)
func (responder *Responder) sendResponse(hs *lib.Handshake /*@, ghost v seq[tm.Term], ghost t pl.Place, ghost s mset[ft.Fact] @*/) (ok bool /*@, ghost v1 seq[tm.Term], ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()

	//@ unfold io.P_r(t, rid, s)
	//@ unfold io.P_r8(t, rid, s)
	//@ ekRT := io.get_e_fr_n(t, rid)
	newPk, ok /*@, t1 @*/ := lib.NewPrivateKey(/*@ t, rid @*/)
	if !ok {
		return
	}
	//@ s1 = s union mset[ft.Fact]{ ft.fr(ekRT) }

	//@ ekR := lib.Abs(newPk)
	//@ sidI := old(getSidI1(hs))
	//@ sidR, sidRT := old(getSidR(responder)), rid
	//@ pkI := old(getPkI(responder))
	//@ psk := old(getPsk(responder))
	//@ epkI := old(getEpkI1(hs))
	//@ c3 := old(getNKey1(hs))
	//@ h4 := old(getNHash1(hs))

	response, ok := responder.createResponse(hs, newPk)
	if !ok {
		return
	}

	packet := lib.MarshalResponse(response)
	//@ unfold acc(ResponderMem(responder), 1/4)

	//@ unfold io.P_r(t1, rid, s1)
	//@ unfold io.P_r15(t1, rid, s1)
	//@ mac1T := io.get_e_MAC_m(t1, rid)
	/*@ mac1, t1 := @*/ (responder.LibState).AddMac1(packet /*@, Bytes_M2(sidI,sidR,pkI,psk,epkI,c3,h4,ekR,by.zeroStringB(16),by.zeroStringB(16)), t1, rid @*/)
	//@ s1 = s1 union mset[ft.Fact] { ft.mac(mac1T) }

	//@ unfold io.P_r(t1, rid, s1)
	//@ unfold io.P_r15(t1, rid, s1)
	//@ mac2T := io.get_e_MAC_m(t1, rid)
	/*@ mac2, t1 := @*/ (responder.LibState).AddMac2(packet /*@, Bytes_M2(sidI,sidR,pkI,psk,epkI,c3,h4,ekR,mac1,by.zeroStringB(16)), t1, rid @*/)
	//@ s1 = s1 union mset[ft.Fact] { ft.mac(mac2T) }

	//@ assert lib.Abs(packet) == Bytes_M2(sidI,sidR,pkI,psk,epkI,c3,h4,ekR,mac1,mac2)
	//@ assert getNKey2(hs) == Bytes_c7(pkI,psk,epkI,c3,ekR)
	
	//@ ghost msg := Term_M2(v[0],sidRT,v[2],v[3],v[4],v[5],v[6],ekRT,mac1T,mac2T)
	//@ assert lib.Abs(packet) == by.gamma(msg)
	//@ assert getNKey2(hs) == by.gamma(Term_c7(v[2],v[3],v[4],v[5],ekRT))

	/*@
	theta := th.createThetaR2(pp, v[1],v[2],v[3],ekRT,v[4],v[5],v[6],v[0],mac1T,mac2T,mac2T,mac2T)
	l := mset[ft.Fact]{ 
		ft.resp1(rid, pp, th.getPkI(theta), th.getKR(theta), th.getEpkI(theta), th.getPsk(theta), th.getC3(theta), th.getH4(theta), th.getSidI(theta)), 
		ft.fr(th.getEkR(theta)),
		ft.mac(th.getMac1R(theta)),
		ft.mac(th.getMac2R(theta)),
	}
	a := mset[cl.Claim]{ 
		cl.runningInitResp(tm.tuple4(tm.getFirst(pp), tm.getSecond(pp), Term_k_IR(th.getPkI(theta),th.getPsk(theta),th.getEpkI(theta),th.getC3(theta),th.getEkR(theta)), Term_k_RI(th.getPkI(theta),th.getPsk(theta),th.getEpkI(theta),th.getC3(theta),th.getEkR(theta)))),
	}
	r := mset[ft.Fact]{ 
		ft.resp2(rid, pp, Term_k_IR(th.getPkI(theta),th.getPsk(theta),th.getEpkI(theta),th.getC3(theta),th.getEkR(theta)), Term_k_RI(th.getPkI(theta),th.getPsk(theta),th.getEpkI(theta),th.getC3(theta),th.getEkR(theta)), tm.zeroString(1), tm.zeroString(1)),
		ft.outFact(Term_M2(th.getSidI(theta),rid,th.getPkI(theta),th.getPsk(theta),th.getEpkI(theta),th.getC3(theta),th.getH4(theta),th.getEkR(theta),th.getMac1R(theta),th.getMac2R(theta))),
	}
	unfold io.P_r(t1, rid, s1)
	unfold io.P_r2(t1, rid, s1) 
	t1 = io.internalBio2R(t1,theta,l,a,r)
	s1 = ft.U(l,r,s1)
	@*/

	//@ unfold io.P_r(t1, rid, s1)
	//@ unfold io.P_r6(t1, rid, s1)
	//@ assert ft.outFact(msg) in s1 // for the trigger
	//@ assert pl.token(t1) && io.e_out(t1, rid, msg) && by.gamma(msg) == lib.Abs(packet)
	ok /*@, t1 @*/= (responder.LibState).Send(packet /*@, t1, rid, msg @*/)
	//@ s1 = s1 setminus mset[ft.Fact]{ ft.outFact(msg) }
	//@ fold acc(ResponderMem(responder), 1/4)
	//@ v1 = seq[tm.Term] { v[0], v[1], v[2], v[3], Term_c7(v[2],v[3],v[4],v[5],ekRT) }
	return
}

//@ requires acc(ResponderMem(responder), 1/8) && HandshakeMem1(hs)
//@ requires lib.Mem(newPk) && lib.Size(newPk) == 32
//@ ensures  acc(ResponderMem(responder), 1/8)
//@ ensures  ok ==> lib.ResponseMem(response) && HandshakeMem2(hs)
//@ ensures  ok ==> lib.ResponseAbs(response) == Bytes_M2(old(getSidI1(hs)),getSidR(responder),getPkI(responder),getPsk(responder),old(getEpkI1(hs)),old(getNKey1(hs)),old(getNHash1(hs)),old(lib.Abs(newPk)),by.zeroStringB(16),by.zeroStringB(16))
//@ ensures  ok ==> getSidI2(hs) == old(getSidI1(hs)) && getEpkI2(hs) == old(getEpkI1(hs))
//@ ensures  ok ==> getNKey2(hs) == Bytes_c7(getPkI(responder),getPsk(responder),old(getEpkI1(hs)),old(getNKey1(hs)),old(lib.Abs(newPk)))
func (responder *Responder) createResponse(hs *lib.Handshake, newPk lib.ByteString) (response *lib.Response, ok bool) {

	//@ unfold acc(ResponderMem(responder), 1/8)
	args := &responder.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ unfold HandshakeMem1(hs)

	//@ kR := lib.Abs(args.PrivateKey)
	//@ pkI := lib.Abs(args.RemoteStatic)
	//@ psk := lib.Abs(args.PresharedKey)
	//@ epkI := lib.Abs(hs.RemoteEphemeral)
	//@ c3 := lib.Abs(hs.ChainKey)
	//@ h4 := lib.Abs(hs.ChainHash)
	//@ ekR := lib.Abs(newPk)

	hs.LocalEphemeral = newPk
	// handshake.localEphemeral == ek_R

	ephemeral := lib.PublicKey(hs.LocalEphemeral)
	// ephemeral == epk_R

	lib.ComputeHashInplace(hs.ChainHash, ephemeral)
	// ChainHash == h5 == hash(<h4, epk_R>)
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h5(h4, ekR)
	lib.ComputeKDF1Inplace(hs.ChainKey, ephemeral)
	// ChainKey == c4
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c4(c3, ekR)

	{
		ss := lib.ComputeSharedSecret(hs.LocalEphemeral, hs.RemoteEphemeral)
		// ss == (g^ek_I)^ek_R
		lib.ComputeKDF1Inplace(hs.ChainKey, ss)
		// ChainKey == c5
		ss = lib.ComputeSharedSecret(hs.LocalEphemeral, args.RemoteStatic)
		// ss == (g^k_I)^ek_R
		lib.ComputeKDF1Inplace(hs.ChainKey, ss)
		// ChainKey == c6
	}
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c6(pkI, epkI,c3, ekR)

	tau := lib.NewByteString(32)
	key := lib.NewByteString(32)
	lib.ComputeKDF3Inplace(tau, key, hs.ChainKey, args.PresharedKey)
	// ChainKey == c7
	// tau == pi
	// key == k3
	//@ assert lib.Abs(hs.ChainKey) == Bytes_c7(pkI, psk, epkI, c3, ekR)
	//@ assert lib.Abs(tau) == Bytes_pi(pkI, psk, epkI, c3, ekR)
	//@ assert lib.Abs(key) == Bytes_k3(pkI, psk, epkI, c3, ekR)

	lib.ComputeHashInplace(hs.ChainHash, tau)
	// ChainHash == h6
	//@ assert lib.Abs(hs.ChainHash) == Bytes_h6(pkI, psk, epkI, c3, h4, ekR)

	empty, ok := lib.AeadEnc(key, lib.ZeroNonce(), nil, hs.ChainHash)
	// empty == c_empty
	if !ok { // ADAPT
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return
	}
	//@ assert lib.Abs(empty) == Bytes_c_empty(pkI, psk, epkI, c3, h4, ekR)

	lib.ComputeHashInplace(hs.ChainHash, empty)
	// chainHash == hash(<h6, c_empty>)

	response = &lib.Response{
		Type:      2,
		Sender:    args.LocalIndex,
		Receiver:  hs.RemoteIndex,
		Ephemeral: ephemeral,
		Empty:     empty,
	}

	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(ResponderMem(responder), 1/8)
	//@ fold lib.ResponseMem(response)
	//@ fold HandshakeMem2(hs)

	return
}

//@ requires acc(ResponderMem(responder), 1/4) && HandshakeMem2(hs)
//@ ensures  acc(ResponderMem(responder), 1/4) && lib.ConnectionMem(conn)
//@ ensures  lib.ConnectionKRI(conn) == by.kdf1B(old(getNKey2(hs)))
//@ ensures  lib.ConnectionKIR(conn) == by.kdf2B(old(getNKey2(hs)))
//@ ensures  lib.ConnectionNonceVal(conn) == 0
//@ ensures  lib.ConnectionSidI(conn) == old(getSidI2(hs))
func (responder *Responder) beginSymmetricSession(hs *lib.Handshake) (conn *lib.Connection) {

	sendKey := lib.NewByteString(32)
	recvKey := lib.NewByteString(32)
	//@ unfold HandshakeMem2(hs)
	lib.ComputeKDF2(recvKey, sendKey, hs.ChainKey, nil)
	// recvKey == kdf1(c7) == k_IR
	// sendKey == kdf2(c7) == k_RI

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
