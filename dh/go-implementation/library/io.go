package library

import errors "errors"
import fmt "fmt"
//@ import . "dh-gobra/verification/bytes"
//@ import . "dh-gobra/verification/place"
//@ import . "dh-gobra/verification/iospec"
//@ import tm "dh-gobra/verification/util"

const MAX_DATA_SIZE = 1024

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ requires acc(Mem(data), 1/16)
//@ requires token(t) && e_OutFact(t, rid, m) && gamma(m) == Abs(data)
//@ ensures  acc(Mem(data), 1/16)
//@ ensures  err == nil ==> token(t1) && t1 == old(get_e_OutFact_placeDst(t, rid, m))
func (l *LibState) Send(data []byte /*@, ghost t Place, ghost rid tm.Term, ghost m tm.Term @*/) (err error /*@, ghost t1 Place @*/) {
	bytesWritten, err := l.conn.Write(data)
	if err != nil {
		return err
	}
	if bytesWritten != len(data) {
		return errors.New("not all data has been sent")
	}
	return nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ requires token(t) && e_InFact(t, rid)
//@ ensures err == nil ==> Mem(data) && gamma(term) == Abs(data)
//@ ensures err == nil ==> token(t1) && t1 == old(get_e_InFact_placeDst(t, rid)) && term == old(get_e_InFact_r1(t, rid))
func (l *LibState) Recv(/*@ ghost t Place, ghost rid tm.Term @*/) (data []byte, err error /*@, ghost term tm.Term, ghost t1 Place @*/) {
	buf := make([]byte, MAX_DATA_SIZE)
	bytesRead, err := l.conn.Read(buf)
	if err != nil {
		return nil, err
	}
	buf = buf[:bytesRead]
	return buf, nil
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
func (l *LibState) Close() {
	l.connClosed = true
	l.conn.Close()
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ ensures err != nil
func (l *LibState) NewError(msg string) (err error) {
	return errors.New(msg)
}

//@ trusted
//@ preserves acc(l.Mem(), 1/16)
//@ preserves acc(Mem(sharedSecret), 1/16)
func (l *LibState) PrintSharedSecret(sharedSecret []byte) {
	fmt.Printf("Initiator & responder agreed on shared secret %x\n", sharedSecret)
}
