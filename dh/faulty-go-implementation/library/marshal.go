package library

import binary "encoding/binary"
import errors "errors"
//@ import . "dh-gobra/verification/bytes"

const Msg2Tag uint32 = 0
const Msg3Tag uint32 = 1

type Msg1 struct {
	X []byte
}

type Msg2 struct {
	IdA uint32
	IdB uint32
	X []byte
	Y []byte
}

type Msg3 struct {
	IdA uint32
	IdB uint32
	X []byte
	Y []byte
}

/*@
pred (m *Msg1) Mem() {
	acc(m) && Mem(m.X)
}

pred (m *Msg2) Mem() {
	acc(m) && Mem(m.X) && Mem(m.Y)
}

pred (m *Msg3) Mem() {
	acc(m) && Mem(m.Y) && Mem(m.X)
}
@*/

//@ trusted
//@ preserves acc(msg1.Mem(), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == (unfolding acc(msg1.Mem(), 1/16) in Abs(msg1.X))
func (l *LibState) MarshalMsg1(msg1 *Msg1) (res []byte, err error) {
	res = make([]byte, len(msg1.X))
	copy(res, msg1.X)
	return res, nil
}

//@ trusted
//@ preserves acc(Mem(data), 1/16)
//@ ensures err == nil ==> res.Mem()
//@ ensures err == nil ==> Abs(data) == (unfolding acc(res.Mem(), 1/16) in tuple5B(integer32B(Msg2Tag), integer32B(res.IdB), integer32B(res.IdA), Abs(res.X), Abs(res.Y)))
func (l *LibState) UnmarshalMsg2(data []byte) (res *Msg2, err error) {
	if len(data) < 2 * DHHalfKeyLength + 12 {
		return nil, errors.New("msg2 is too short")
	}

	tag := binary.BigEndian.Uint32(data[:4])
	// note that idB occurs before idA in the 2nd message:
	idB := binary.BigEndian.Uint32(data[4:8])
	idA := binary.BigEndian.Uint32(data[8:12])
	X := data[12:(DHHalfKeyLength + 12)]
	Y := data[(DHHalfKeyLength + 12):(2 * DHHalfKeyLength + 12)]

	if tag != Msg2Tag {
		return nil, errors.New("unexpected message tag in msg2")
	}

	return &Msg2{IdA: idA, IdB: idB, X: X, Y: Y}, nil
}

//@ trusted
//@ preserves acc(msg3.Mem(), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == (unfolding acc(msg3.Mem(), 1/16) in tuple5B(integer32B(Msg3Tag), integer32B(msg3.IdA), integer32B(msg3.IdB), Abs(msg3.Y), Abs(msg3.X)))
func (l *LibState) MarshalMsg3(msg3 *Msg3) (res []byte, err error) {
	res = make([]byte, 12)
	binary.BigEndian.PutUint32(res[:4], Msg3Tag)
	binary.BigEndian.PutUint32(res[4:8], msg3.IdA)
	binary.BigEndian.PutUint32(res[8:12], msg3.IdB)
	// note that Y occurs before X in the 3rd message:
	res = append(res, msg3.Y...)
	return append(res, msg3.X...), nil
}
