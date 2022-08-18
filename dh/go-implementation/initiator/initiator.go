package initiator

import . "dh-gobra/library"
//@ import by "dh-gobra/verification/bytes"
//@ import cl "dh-gobra/verification/claim"
//@ import ft "dh-gobra/verification/fact"
//@ import pl "dh-gobra/verification/place"
//@ import io "dh-gobra/verification/iospec"
//@ import tm "dh-gobra/verification/util"
//@ import am "dh-gobra/verification/term"
//@ import p "dh-gobra/verification/pattern"
//@ import pub "dh-gobra/verification/pub"
//@ import fresh "dh-gobra/verification/fresh"

type Initiator struct {
	l *LibState
	idA uint32
	idB uint32
	skA []byte
	pkB []byte
}

/*@
pred (i *Initiator) Mem(skAT, skBT tm.Term) {
	acc(i) && acc(Mem(i.skA), 1/4) && acc(Mem(i.pkB), 1/4) && i.l.Mem() &&
	Abs(i.skA) == by.gamma(skAT) && Abs(i.pkB) == by.gamma(tm.pk(skBT))
}

ghost
requires acc(i.Mem(skAT, skBT), _)
pure
func (i *Initiator) getIdA(skAT, skBT tm.Term) uint32 {
	return unfolding acc(i.Mem(skAT, skBT), _) in i.idA
}

ghost
requires acc(i.Mem(skAT, skBT), _)
pure
func (i *Initiator) getIdB(skAT, skBT tm.Term) uint32 {
	return unfolding acc(i.Mem(skAT, skBT), _) in i.idB
}
@*/

//@ requires l.Mem()
//@ requires pl.token(t) && io.P_Alice(t, am.freshTerm(fresh.fr_integer32(rid)), mset[ft.Fact]{})
//@ requires rid != 0 && rid != 1
//@ ensures  l.Mem()
func RunInitiator(l *LibState, rid uint32 /*@, ghost t pl.Place @*/) (err error) {
	//@ ridT := tm.integer32(rid)
	//@ s := mset[ft.Fact]{}

	//@ unfold io.P_Alice(t, ridT, s)
	//@ unfold io.phiRF_Alice_5(t, ridT, s)
	//@ assert acc(io.e_Setup_Alice(t, ridT))
	//@ skAT := io.get_e_Setup_Alice_r3(t, ridT)
	//@ skBT := io.get_e_Setup_Alice_r4(t, ridT)

	var idA, idB uint32
	var skA, pkB []byte
	//@ ghost var t1 pl.Place
	idA, idB, skA, pkB, err /*@, t1 @*/ = l.Setup(/*@ t, ridT @*/)
	//@ s1 := mset[ft.Fact]{ ft.Setup_Alice(ridT, tm.integer32(idA), tm.integer32(idB), skAT, skBT) }
	if err != nil {
		return err
	}

	i := &Initiator {
		l,
		idA,
		idB,
		skA,
		pkB,
	}

	// create x
	//@ unfold io.P_Alice(t1, ridT, s1)
	//@ unfold io.phiRF_Alice_3(t1, ridT, s1)
	//@ assert acc(io.e_FrFact(t1, ridT))
	//@ xT := io.get_e_FrFact_r1(t1, ridT)
	var x []byte
	//@ ghost var t2 pl.Place
	x, err /*@, t2 @*/ = l.CreateNonce(/*@ t1, ridT @*/)
	//@ s2 := s1 union mset[ft.Fact]{ ft.FrFact_Alice(ridT, xT) }
	if err != nil {
		return err
	}
	var X []byte
	X, err = l.DhExp(x)
	//@ XT := tm.exp(tm.generator(), xT)
	if err != nil {
		return err
	}

	//@ fold i.Mem(skAT, skBT)
	//@ ghost var t3 pl.Place
	//@ ghost var s3 mset[ft.Fact]
	err /*@, t3, s3 @*/ = i.sendMsg1(X /*@, skAT, skBT, xT, t2, ridT, s2 @*/)
	if err != nil {
		//@ unfold i.Mem(skAT, skBT)
		return err
	}

	var receivedY []byte
	//@ ghost var YT tm.Term
	//@ ghost var t4 pl.Place
	//@ ghost var s4 mset[ft.Fact]
	receivedY, err /*@, YT, t4, s4 @*/ = i.recvMsg2(X, /*@ skAT, skBT, xT, t3, ridT, s3 @*/)
	if err != nil {
		//@ unfold i.Mem(skAT, skBT)
		return err
	}

	
	//@ unfold acc(i.Mem(skAT, skBT), 1/2)
	var sharedSecret []byte
	sharedSecret, err = i.l.DhSharedSecret(x, receivedY)
	//@ fold acc(i.Mem(skAT, skBT), 1/2)
	if err != nil {
		//@ unfold i.Mem(skAT, skBT)
		return err
	}

	//@ ghost var t5 pl.Place
	//@ ghost var s5 mset[ft.Fact]
	err /*@, t5, s5 @*/ = i.sendMsg3(X, receivedY /*@, skAT, skBT, xT, YT, t4, ridT, s4 @*/)
	if err != nil {
		//@ unfold i.Mem(skAT, skBT)
		return err
	}

	//@ unfold i.Mem(skAT, skBT)
	i.l.PrintSharedSecret(sharedSecret)
	return nil
}

//@ requires acc(i.Mem(skAT, skBT), 1/2) && acc(Mem(X), 1/8)
//@ requires Abs(X) == by.gamma(tm.exp(tm.generator(), xT))
//@ requires pl.token(t) && io.P_Alice(t, ridT, s)
//@ requires ft.Setup_Alice(ridT, tm.integer32(i.getIdA(skAT, skBT)), tm.integer32(i.getIdB(skAT, skBT)), skAT, skBT) in s
//@ requires ft.FrFact_Alice(ridT, xT) in s
//@ ensures  acc(i.Mem(skAT, skBT), 1/2) && acc(Mem(X), 1/8)
//@ ensures  err == nil ==> pl.token(t1) && io.P_Alice(t1, ridT, s1)
//@ ensures  err == nil ==> ft.St_Alice_1(ridT, tm.integer32(i.getIdA(skAT, skBT)), tm.integer32(i.getIdB(skAT, skBT)), skAT, skBT, xT) in s1
func (i *Initiator) sendMsg1(X []byte /*@, ghost skAT tm.Term, ghost skBT tm.Term, ghost xT tm.Term, ghost t pl.Place, ghost ridT tm.Term, ghost s mset[ft.Fact] @*/) (err error /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold io.P_Alice(t, ridT, s)
	//@ unfold io.phiR_Alice_0(t, ridT, s)
	//@ idAT := tm.integer32(i.getIdA(skAT, skBT))
	//@ idBT := tm.integer32(i.getIdB(skAT, skBT))
	//@ XT := tm.exp(tm.generator(), xT)
	/*@
	l := mset[ft.Fact]{ ft.Setup_Alice(ridT, idAT, idBT, skAT, skBT),
		ft.FrFact_Alice(ridT, xT) }
	a := mset[cl.Claim]{}
	r := mset[ft.Fact]{ ft.St_Alice_1(ridT, idAT, idBT, skAT, skBT, xT),
		ft.OutFact_Alice(ridT, XT) }
	@*/
	//@ assert io.e_Alice_send(t, ridT, idAT, idBT, skAT, skBT, xT, l, a, r)
	//@ t1 = io.internBIO_e_Alice_send(t, ridT, idAT, idBT, skAT, skBT, xT, l, a, r)
	//@ s1 = ft.U(l, r, s)
	
	//@ unfold acc(i.Mem(skAT, skBT), 1/8)
	msg1 := &Msg1{X: X}
	//@ fold acc(msg1.Mem(), 1/8)
	var msg1Data []byte
	msg1Data, err = i.l.MarshalMsg1(msg1)
	//@ unfold acc(msg1.Mem(), 1/8)
	if err != nil {
		//@ fold acc(i.Mem(skAT, skBT), 1/8)
		return
	}

	//@ unfold io.P_Alice(t1, ridT, s1)
	//@ unfold io.phiRG_Alice_2(t1, ridT, s1)
	//@ assert io.e_OutFact(t1, ridT, XT)
	err /*@, t1 @*/ = i.l.Send(msg1Data /*@, t1, ridT, XT @*/)
	//@ s1 = s1 setminus mset[ft.Fact]{ ft.OutFact_Alice(ridT, XT) }
	//@ fold acc(i.Mem(skAT, skBT), 1/8)
	return
}

//@ requires acc(i.Mem(skAT, skBT), 1/2) && acc(Mem(X), 1/8)
//@ requires Abs(X) == by.gamma(tm.exp(tm.generator(), xT))
//@ requires pl.token(t) && io.P_Alice(t, ridT, s)
//@ requires ft.St_Alice_1(ridT, tm.integer32(i.getIdA(skAT, skBT)), tm.integer32(i.getIdB(skAT, skBT)), skAT, skBT, xT) in s
//@ ensures  acc(i.Mem(skAT, skBT), 1/2) && acc(Mem(X), 1/8)
//@ ensures  err == nil ==> Mem(receivedY) && Abs(receivedY) == by.gamma(YT)
//@ ensures  err == nil ==> pl.token(t1) && io.P_Alice(t1, ridT, s1)
//@ ensures  err == nil ==> ft.St_Alice_2(ridT, tm.integer32(i.getIdA(skAT, skBT)), tm.integer32(i.getIdB(skAT, skBT)), skAT, skBT, xT, YT) in s1
//@ ensures  err == nil ==> ft.OutFact_Alice(ridT, tm.sign(tm.tuple5(tm.integer32(Msg3Tag), tm.integer32(i.getIdA(skAT, skBT)), tm.integer32(i.getIdB(skAT, skBT)), YT, tm.exp(tm.generator(), xT)), skAT)) in s1
func (i *Initiator) recvMsg2(X []byte, /*@ ghost skAT tm.Term, ghost skBT tm.Term, ghost xT tm.Term, ghost t pl.Place, ghost ridT tm.Term, ghost s mset[ft.Fact] @*/) (receivedY []byte, err error /*@, ghost YT tm.Term, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold acc(i.Mem(skAT, skBT), 1/2)
	//@ unfold io.P_Alice(t, ridT, s)
	//@ unfold io.phiRF_Alice_4(t, ridT, s)
	//@ assert io.e_InFact(t, ridT)
	var signedMsg2 []byte
	//@ ghost var msg2T tm.Term
	signedMsg2, err /*@, msg2T, t1 @*/ = i.l.Recv(/*@ t, ridT @*/)
	//@ s1 = s union mset[ft.Fact]{ ft.InFact_Alice(ridT, msg2T) }
	if err != nil {
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	}
	var msg2Data []byte
	msg2Data, err = i.l.Open(signedMsg2, i.pkB /*@, skBT @*/)
	if err != nil {
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	}
	var msg2 *Msg2
	msg2, err = i.l.UnmarshalMsg2(msg2Data)
	if err != nil {
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	}
	//@ unfold msg2.Mem()
	if msg2.IdA != i.idA || msg2.IdB != i.idB {
		err = i.l.NewError("IDs in msg2 do not match")
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	} 
	receivedY = msg2.Y

	// check receivedX
	if !Equals(X, msg2.X) {
		err = i.l.NewError("Received X does not match")
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	}
	//@ fold acc(i.Mem(skAT, skBT), 1/2)

	//@ idAT := tm.integer32(i.getIdA(skAT, skBT))
	//@ idBT := tm.integer32(i.getIdB(skAT, skBT))
	//@ XT := tm.exp(tm.generator(), xT)
	//@ YT := p.patternRequirement2(ridT, idAT, idBT, skAT, skBT, xT, by.oneTerm(Abs(receivedY)), msg2T, t1, s1)
	// the following assert stmt is needed for triggering reasons:
	//@ assert by.getMsgB(Abs(signedMsg2)) == Abs(msg2Data)
	//@ assert Abs(receivedY) == by.gamma(YT)

	//@ unfold io.P_Alice(t1, ridT, s1)
	//@ unfold io.phiR_Alice_1(t1, ridT, s1)
	//@ msg3T := tm.sign(tm.tuple5(tm.integer32(Msg3Tag), idAT, idBT, YT, XT), skAT)
	/*@
	l := mset[ft.Fact]{ ft.St_Alice_1(ridT, idAT, idBT, skAT, skBT, xT),
		ft.InFact_Alice(ridT, msg2T) } 
	a := mset[cl.Claim]{
		cl.IN_ALICE(YT, tm.tuple5(tm.integer32(Msg2Tag), idBT, idAT, XT, YT)),
        cl.Secret(idAT, idBT, tm.exp(YT, xT)),
        cl.Running(tm.idR(), tm.idI(), tm.tuple3(idAT, idBT, tm.exp(YT, xT))),
        cl.Commit(tm.idI(), tm.idR(), tm.tuple3(idAT, idBT, tm.exp(YT, xT))) }
	r := mset[ft.Fact]{ ft.St_Alice_2(ridT, idAT, idBT, skAT, skBT, xT, YT),
		ft.OutFact_Alice(ridT, msg3T) }
	@*/
	//@ assert io.e_Alice_recvAndSend(t1, ridT, idAT, idBT, skAT, skBT, xT, YT, l, a, r)
	//@ t1 = io.internBIO_e_Alice_recvAndSend(t1, ridT, idAT, idBT, skAT, skBT, xT, YT, l, a, r)
	//@ s1 = ft.U(l, r, s1)
	return
}

//@ requires acc(i.Mem(skAT, skBT), 1/2)
//@ requires acc(Mem(X), 1/8) && acc(Mem(receivedY), 1/8)
//@ requires Abs(X) == by.gamma(tm.exp(tm.generator(), xT)) && Abs(receivedY) == by.gamma(YT)
//@ requires pl.token(t) && io.P_Alice(t, ridT, s)
//@ requires ft.OutFact_Alice(ridT, tm.sign(tm.tuple5(tm.integer32(Msg3Tag), tm.integer32(i.getIdA(skAT, skBT)), tm.integer32(i.getIdB(skAT, skBT)), YT, tm.exp(tm.generator(), xT)), skAT)) in s
//@ ensures  acc(i.Mem(skAT, skBT), 1/2)
//@ ensures  acc(Mem(X), 1/8) && acc(Mem(receivedY), 1/8)
//@ ensures  err == nil ==> pl.token(t1) && io.P_Alice(t1, ridT, s1)
func (i *Initiator) sendMsg3(X, receivedY []byte /*@, ghost skAT tm.Term, ghost skBT tm.Term, ghost xT tm.Term, ghost YT tm.Term, ghost t pl.Place, ghost ridT tm.Term, ghost s mset[ft.Fact] @*/) (err error /*@, ghost t1 pl.Place, ghost s1 mset[ft.Fact] @*/) {
	//@ unfold acc(i.Mem(skAT, skBT), 1/2)
	msg3 := &Msg3{IdA: i.idA, IdB: i.idB, X: X, Y: receivedY}
	//@ fold acc(msg3.Mem(), 1/8)
	var msg3Data []byte
	msg3Data, err = i.l.MarshalMsg3(msg3)
	//@ unfold acc(msg3.Mem(), 1/8)
	if err != nil {
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	}
	var signedMsg3 []byte
	signedMsg3, err = i.l.Sign(msg3Data, i.skA)
	if err != nil {
		//@ fold acc(i.Mem(skAT, skBT), 1/2)
		return
	}

	//@ idAT := tm.integer32(i.idA)
	//@ idBT := tm.integer32(i.idB)
	//@ XT := tm.exp(tm.generator(), xT)
	//@ msgT := tm.sign(tm.tuple5(tm.integer32(Msg3Tag), idAT, idBT, YT, XT), skAT)
	//@ unfold io.P_Alice(t, ridT, s)
	//@ unfold io.phiRG_Alice_2(t, ridT, s)
	//@ assert acc(io.e_OutFact(t, ridT, msgT))
	err /*@, t1 @*/ = i.l.Send(signedMsg3 /*@, t, ridT, msgT @*/)
	//@ s1 = s setminus mset[ft.Fact]{ ft.OutFact_Alice(ridT, msgT) }
	//@ fold acc(i.Mem(skAT, skBT), 1/2)
	return
}
