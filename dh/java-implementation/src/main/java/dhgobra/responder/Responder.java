package dhgobra.responder;

// Verified with https://github.com/verifast/verifast/releases/tag/18.02

import java.util.Arrays;
import dhgobra.library.Library;
import dhgobra.library.Msg1;
import dhgobra.library.Msg2;
import dhgobra.library.Msg3;
import dhgobra.library.Config;
//@ import place.*;
//@ import fresh.*;
//@ import pub.*;
//@ import term.*;
//@ import fact.*;
//@ import claim.*;
//@ import iospec.*;

//@ predicate stateArgs(Term BT, Term AT, Term skBT, Term skAT, Term y, Term X) = true;

public final class Responder {
    private final Library lib;
    private final int rid;
    private int idA; // values are in the range of uint32
    private int idB; // values are in the range of uint32
    private byte[] pkA;
    private byte[] skB;

    public Responder(Library lib, int rid) 
      //@ requires lib.data();
      //@ ensures  this.lib |-> lib &*& lib.data() &*& this.rid |-> rid &*& this.idA |-> _ &*& this.idB |-> _ &*& this.pkA |-> _ &*& this.skB |-> _;
    {
        this.lib = lib;
        this.rid = rid;
    }

    public boolean Run() 
    /*@ requires 
            lib |-> ?libV &*& libV != null &*& libV.data() &*& rid |-> ?rid &*& idA |-> _ &*& idB |-> _ &*& pkA |-> _ &*& skB |-> _ &*&
            token(?p0) &*& P_Bob(p0, freshTerm(fr_int(rid)), msetList(nil));
    @*/ 
    /*@ ensures  
            result == false ? true : (
              token(?pN) &*& P_Bob(pN, freshTerm(fr_int(rid)), ?sAfter) &*& 
              stateArgs(?BT, ?AT, ?skBT, ?skAT, ?y, ?X) &*&
              sAfter == msetList(cons(St_Bob_2(freshTerm(fr_int(rid)), BT, AT, skBT, skAT, y, X),nil))
            );
    @*/
    {
        //@ Term  tami_rid = freshTerm(fr_int(rid));
        //@ mset<Fact> tami_s = msetList(nil);
        
        //@ open P_Bob(p0, tami_rid, tami_s);
        //@ bigstar_extract(phiRF_Bob_5(p0, tami_rid, tami_s), quant_phiRF_Bob_5);
        //@ open phiRF_Bob_5(p0, tami_rid, tami_s)(quant_phiRF_Bob_5);
        //@ assert e_Setup_Bob(p0, tami_rid, ?BT, ?AT, ?skBT, ?skAT, ?p1);
    
        Config config = lib.GetConfig();
        idA = config.idA;
        idB = config.idB;
        pkA = config.pkA;
        if (pkA == null) {
            return false;
        }

        skB = config.skB;
        if (skB == null) {
            return false;
        }
        
        //@ assert idA |-> ?idAV &*& idB |-> ?idBV &*& pkA |-> ?pkAV &*& skB |-> ?skBV;
        //@ assert [_]array_slice(pkAV, 0, pkAV.length, ?pkAS) &*& [_]libV.keyPair(?skAS, pkAS);
        
        //@ tami_s = msetList(cons(Setup_Bob(tami_rid, BT, AT, skBT, skAT), nil));
        
        //@ open P_Bob(p1, tami_rid, tami_s);
        //@ bigstar_extract(phiRF_Bob_4(p1, tami_rid, tami_s), quant_phiRF_Bob_4);
        //@ open phiRF_Bob_4(p1, tami_rid, tami_s)(quant_phiRF_Bob_4);
        //@ assert e_InFact(p1, tami_rid, ?receivedXT, ?p2);
        
        byte[] receivedX = recvMsg1();
        if (receivedX == null) {
            return false;
        }
        
        //@ assert [_]array_slice(receivedX, 0, receivedX.length, ?receivedXS);
        
        //@ tami_s = msetList(cons(Setup_Bob(tami_rid, BT, AT, skBT, skAT), cons(InFact_Bob(tami_rid, receivedXT), nil)));
        
        //@ open P_Bob(p2, tami_rid, tami_s);
        //@ bigstar_extract(phiRF_Bob_3(p2, tami_rid, tami_s), quant_phiRF_Bob_3);
        //@ open phiRF_Bob_3(p2, tami_rid, tami_s)(quant_phiRF_Bob_3);
        //@ assert e_FrFact(p2, tami_rid, ?yFR, ?p3);

        // create y
        byte[] y = lib.createNonce();
        if (y == null) {
            return false;
        }
        
        //@ assert [_]array_slice(y, 0, y.length, ?yS);
        
        byte[] Y = lib.dhExp(y);
        if (Y == null) {
            return false;
        }
        
        byte[] sharedSecret = lib.dhSharedSecret(y, receivedX);
        if (sharedSecret == null) {
            return false;
        }
        
        //@ tami_s = msetList(cons(Setup_Bob(tami_rid, BT, AT, skBT, skAT), cons(InFact_Bob(tami_rid, receivedXT), cons(FrFact_Bob(tami_rid, yFR), nil))));
        
        //@ open P_Bob(p3, tami_rid, tami_s);
        
        //@ Bob_quantified_vals v3Pre = quant_phiR_Bob_0(tami_rid, BT, AT, skBT, skAT, yFR, receivedXT, msetList(nil), msetList(nil), msetList(nil));
        //@ Bob_quantified_vals v3 = addLAR(v3Pre);
        
        //@ bigstar_extract(phiR_Bob_0(p3, tami_rid, tami_s), v3);
        //@ open phiR_Bob_0(p3, tami_rid, tami_s)(v3);
        //@ assert e_Bob_recvAndSend(p3, tami_rid, BT, AT, skBT, skAT, yFR, receivedXT, ?l3, ?a3, ?r3, ?p4);
        
        //@ internBIO_e_Bob_recvAndSend(p3, tami_rid, BT, AT, skBT, skAT, yFR, receivedXT, l3, a3, r3);
        
        //@ mset<Fact> tami_l = msetList(cons(Setup_Bob(tami_rid, BT, AT, skBT, skAT),cons(FrFact_Bob(tami_rid, yFR),cons(InFact_Bob(tami_rid, receivedXT),nil))));
        //@ mset<Fact> tami_r = msetList(cons(St_Bob_1(tami_rid, BT, AT, skBT, skAT, yFR, receivedXT), cons(OutFact_Bob(tami_rid, sign(format(pubTerm(const_0_pub()), BT, AT, receivedXT, exp(pubTerm(const_g_pub()), yFR)), skBT)),nil)));
        
        //@ assert P_Bob(p4, tami_rid, ?s4);
        //@ assert s4 == U(tami_l, tami_r, tami_s);
        //@ assert linearFacts(tami_l) == tami_l;
        //@ assert msetMinus(tami_s, linearFacts(tami_l)) == msetList(nil); // only this informatin is required
        //@ assert s4 == tami_r;
        //@ tami_s = tami_r;
        
        //@ open P_Bob(p4, tami_rid, tami_s);
        //@ Term m4 = sign(format(pubTerm(const_0_pub()), BT, AT, receivedXT, exp(pubTerm(const_g_pub()), yFR)), skBT);
        //@ bigstar_extract(phiRG_Bob_2(p4, tami_rid, tami_s), quant_phiRG_Bob_2(m4));
        //@ open phiRG_Bob_2(p4, tami_rid, tami_s)(quant_phiRG_Bob_2(m4));
        //@ assert e_OutFact(p4, tami_rid, m4, ?p5);
        
        boolean success = sendMsg2(Y, receivedX);
        if (!success) {
            return false;
        }
        
        //@ tami_s = msetList(cons(St_Bob_1(tami_rid, BT, AT, skBT, skAT, yFR, receivedXT), nil));
        
        //@ open P_Bob(p5, tami_rid, tami_s);
        //@ bigstar_extract(phiRF_Bob_4(p5, tami_rid, tami_s), quant_phiRF_Bob_4);
        //@ open phiRF_Bob_4(p5, tami_rid, tami_s)(quant_phiRF_Bob_4);
        //@ assert e_InFact(p5, tami_rid, ?msg3T, ?p6);

        Msg3 msg3 = recvMsg3();
        if (msg3 == null) {
            return false;
        }
        
        //@ assert [_]msg3.data(?idAV2, ?idBV2, ?XS2, ?YS2);
        //@ assert gamma(msg3T) == bytes_sign(bytes_format(bytes_const_1_pub(), bytes_int(idAV2), bytes_int(idBV2), YS2, XS2), skAS);
        
        //@ tami_s = msetList(cons(St_Bob_1(tami_rid, BT, AT, skBT, skAT, yFR, receivedXT), cons(InFact_Bob(tami_rid, msg3T), nil)));
        
        //@ assert P_Bob(p6, tami_rid, tami_s);
        
        //@ open [_]msg3.data(_, _, _, _);
        if (msg3.idA != idA || msg3.idB != idB) {
            // IDs in msg3 do not match
            return false;
        }
        byte[] receivedX2 = msg3.X;
        byte[] receivedY = msg3.Y;
        if (receivedX2 == null || receivedY == null) {
            return false;
        }

        if (!Arrays.equals(receivedX, receivedX2)) {
            lib.notMatchX();
            return false;
        }

        if (!Arrays.equals(Y, receivedY)) {
            lib.notMatchY();
            return false;
        }
        
        //@ assert gamma(msg3T) == bytes_sign(bytes_format(bytes_const_1_pub(), bytes_int(idAV), bytes_int(idBV), bytes_exp(bytes_const_g_pub(), yS), receivedXS), skAS);
        //@ patternRequirement(msg3T, AT, BT, yFR, receivedXT, skAT);
        
        //@ open P_Bob(p6, tami_rid, tami_s);
        
        //@ Bob_quantified_vals v6Pre = quant_phiR_Bob_1(tami_rid, BT, AT, skBT, skAT, yFR, receivedXT, msetList(nil), msetList(nil), msetList(nil));
        //@ Bob_quantified_vals v6 = addLAR(v6Pre);
        
        //@ bigstar_extract(phiR_Bob_1(p6, tami_rid, tami_s), v6);
        //@ open phiR_Bob_1(p6, tami_rid, tami_s)(v6);
        //@ assert e_Bob_recv(p6, tami_rid, BT, AT, skBT, skAT, yFR, receivedXT, ?l6, ?a6, ?r6, ?p7);
        
        //@ internBIO_e_Bob_recv(p6, tami_rid, BT, AT, skBT, skAT, yFR, receivedXT, l6, a6, r6);
        
        //@ tami_l = tami_s;
        //@ tami_r = msetList(cons(St_Bob_2(tami_rid, BT, AT, skBT, skAT, yFR, receivedXT),nil));
        
        //@ assert P_Bob(p7, tami_rid, ?s7);
        //@ assert s7 == U(tami_l, tami_r, tami_s);
        //@ assert linearFacts(tami_l) == tami_l;
        //@ assert msetMinus(tami_s, linearFacts(tami_l)) == msetList(nil); // only this informatin is required
        //@ assert s7 == tami_r;
        //@ tami_s = tami_r;
        
        //@ assert token(p7) &*& P_Bob(p7, tami_rid, tami_s);
        
        //@ close stateArgs(BT, AT, skBT, skAT, yFR, receivedXT);
        
        lib.success(sharedSecret);
        return true;
    }

    private byte[] recvMsg1() 
    /*@ requires 
            lib |-> ?libV &*& libV != null &*& libV.data() &*&
            token(?p) &*& e_InFact(p, ?tami_rid, ?new_x, ?pp);
    @*/
    /*@ ensures 
            lib |-> libV &*& libV != null &*& libV.data() &*&
            result == null ? true : (
              [_]array_slice(result, 0, result.length, ?resultS) &*& gamma(new_x) == resultS &*&
              token(pp)
            );
    @*/
    {
        byte[] msg1Data = lib.recv();
        if (msg1Data == null) {
            return null;
        }
        Msg1 msg1 = lib.unmarshalMsg1(msg1Data);
        if (msg1 == null) {
            return null;
        }
        //@ open msg1.data(_);
        return msg1.X;
    }

    private boolean sendMsg2(byte[] Y, byte[] receivedX) 
    /*@ requires 
            lib |-> ?libV &*& libV != null &*& libV.data() &*&
            idA |-> ?idAV &*& idB |-> ?idBV &*& 
            skB |-> ?skBV &*& [_]array_slice(skBV, 0, skBV.length, ?skBS) &*&
            [_]array_slice(Y, 0, Y.length, ?YS) &*& 
            [_]array_slice(receivedX, 0, receivedX.length, ?XS) &*&
            token(?p) &*& e_OutFact(p, ?tami_rid, ?m, ?pp) &*&
            gamma(m) == bytes_sign(bytes_format(bytes_const_0_pub(), bytes_int(idBV), bytes_int(idAV), XS, YS), skBS);
    @*/
    /*@ ensures 
            lib |-> libV &*& libV != null &*& libV.data() &*&
            idA |-> idAV &*& idB |-> idBV &*& 
            skB |-> skBV &*& [_]array_slice(skBV, 0, skBV.length, skBS) &*& 
            result == false ? true : (
              token(pp)
            );
    @*/
    {
        Msg2 msg2 = new Msg2(idA, idB, receivedX, Y);
        byte[] msg2Data = lib.marshalMsg2(msg2);
        if (msg2Data == null) {
            return false;
        }
        byte[] signedMsg2 = lib.sign(msg2Data, skB);
        if (signedMsg2 == null) {
            return false;
        }
        return lib.send(signedMsg2);
    }

    private Msg3 recvMsg3() 
    /*@ requires 
            lib |-> ?libV &*& libV != null &*& libV.data() &*&
            pkA |-> ?pkAV &*& [_]array_slice(pkAV, 0, pkAV.length, ?pkAS) &*& [_]libV.keyPair(?skAS, pkAS) &*& 
            token(?p) &*& e_InFact(p, ?tami_rid, ?new_x, ?pp);
    @*/
    /*@ ensures 
            lib |-> libV &*& libV != null &*& libV.data() &*&
            pkA |-> pkAV &*& [_]array_slice(pkAV, 0, pkAV.length, pkAS) &*& 
            result == null ? true : (
              [_]result.data(?idA, ?idB, ?X, ?Y) &*& gamma(new_x) == bytes_sign(bytes_format(bytes_const_1_pub(), bytes_int(idA), bytes_int(idB), Y, X), skAS) &*& 
              token(pp)
            );
    @*/
    {
        byte[] signedMsg3 = lib.recv();
        if (signedMsg3 == null) {
            return null;
        }
        byte[] msg3Data = lib.open(signedMsg3, pkA);
        if (msg3Data == null) {
            return null;
        }
        return lib.unmarshalMsg3(msg3Data);
    }
}
