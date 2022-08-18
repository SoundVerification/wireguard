package library

import net "net"
//@ import by "dh-gobra/verification/bytes"

type LibState struct {
	conn net.Conn
	connClosed bool
	idA uint32
	idB uint32
	skA [64]byte
	pkB [32]byte
}

/*@
pred (l *LibState) Mem()

pred Mem(data []byte)

ghost
requires acc(Mem(b), _)
pure func Abs(b []byte) (res by.Bytes)
@*/

//@ trusted
//@ ensures err == nil ==> l.Mem()
func NewLibState(endpoint string, idA, idB uint32, privateKey [64]byte, peerPublicKey [32]byte) (l *LibState, err error) {
	conn, err := net.Dial("udp", endpoint)
	if err != nil {
		return nil, err
	}
	state := &LibState {
		conn: conn,
		connClosed: false,
		idA: idA,
		idB: idB,
		skA: privateKey,
		pkB: peerPublicKey,
	}
	return state, nil
}
