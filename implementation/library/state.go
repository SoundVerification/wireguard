package library

import (
	conn "wireguard-gobra/wireguard/conn"
	device "wireguard-gobra/wireguard/device"
)

//@ import by "wireguard-gobra/wireguard/verification/bytes"

type ByteString []byte

type LibraryState struct {
	dev      *device.Device
	endpoint conn.Endpoint
	input    <-chan []byte
	output   chan<- []byte
}

func NewLibraryState(d *device.Device) (libState LibraryState, args HandshakeArguments, ok bool) {
	localIndex, ok := RandUint32()
	if !ok {
		return
	}

	libState = LibraryState{
		dev:      d,
		endpoint: d.Peer.Endpoint,
		input:    d.InputChannel,
		output:   d.OutputChannel,
	}

	args = HandshakeArguments{
		PresharedKey: d.Peer.Handshake.PresharedKey[:],
		PrivateKey:   d.StaticIdentity.PrivateKey[:],
		LocalStatic:  d.StaticIdentity.PublicKey[:],
		LocalIndex:   localIndex,
		RemoteStatic: d.Peer.Handshake.RemoteStatic[:],
	}
	return
}

const MacSize int = 16
const NonceSize int = 12
const KeySize int = 32
const HashSize int = 32

type Request struct {
	Type      uint32
	Sender    uint32     // sid_I
	Ephemeral ByteString // epk_I    len == 32
	Static    ByteString // c_pk_I   len == 32 + 16
	Timestamp ByteString // c_ts     len == 12 + 16
	MAC1      ByteString //          len == 16
	MAC2      ByteString //          len == 16
}

type Response struct {
	Type      uint32
	Sender    uint32     // sid_R
	Receiver  uint32     // sid_I
	Ephemeral ByteString // epk_R    len == 32
	Empty     ByteString // c_empty  len == 0 + 16
	MAC1      ByteString //          len == 16
	MAC2      ByteString //          len == 16
}

type Message struct {
	Type     uint32
	Receiver uint32
	Nonce    uint64
	Payload  ByteString
}

type Handshake struct {
	ChainHash       ByteString // hN          len == 32
	ChainKey        ByteString // cN          len == 32
	LocalEphemeral  ByteString // ek_self     len == 32
	RemoteIndex     uint32     // sid_other
	RemoteEphemeral ByteString // epk_other   len == 32
}

type HandshakeArguments struct {
	PresharedKey ByteString // psk             len == 32
	PrivateKey   ByteString // k_self          len == 32
	LocalIndex   uint32     // sid_self        len == 32
	LocalStatic  ByteString // pk_self         len == 32
	RemoteStatic ByteString // pk_other        len == 32
}

type Connection struct {
	Nonce       uint64
	SendKey     ByteString
	RecvKey     ByteString
	RemoteIndex uint32
}

/* predicates and pure functions */

/*@
pred Mem(b ByteString)

ghost
requires acc(Mem(b), _)
ensures  Size(b) == 0 ==> res == by.zeroStringB(0)
pure func Abs(b ByteString) (res by.Bytes)

ghost
requires b != nil ==> acc(Mem(b), _)
ensures  b != nil ? res == Abs(b) : res == by.zeroStringB(l)
pure func SafeAbs(b ByteString, l int) (res by.Bytes)

@*/

//@ ghost
//@ requires acc(Mem(b), _)
//@ ensures res >= 0 && res == len(b)
//@ pure
func Size(b ByteString) (res int) {
	return len(b)
}

//@ requires acc(Mem(b1), 1/200) && acc(Mem(b2), 1/200)
//@ ensures Abs(b1) == Abs(b2)
//@ pure
func IsEqual(b1, b2 ByteString) (res bool) {
	s1, s2 := Size(b1), Size(b2)
	if s1 != s2 {
		return false
	}
	for i := 0; i < s1; i++ {
		if b1[i] != b2[i] {
			return false
		}
	}
	return true
}

/*@
pred LibMem(libState *LibraryState)

pred RequestMem(request *Request) {
	acc(request) && Mem(request.Ephemeral) && Mem(request.Static) && Mem(request.Timestamp) &&
	Size(request.Ephemeral) == 32 && Size(request.Static) == 48 && Size(request.Timestamp) == 28 &&
	(request.MAC1 != nil ==> Mem(request.MAC1) && Size(request.MAC1) == 16) &&
	(request.MAC2 != nil ==> Mem(request.MAC2) && Size(request.MAC2) == 16)
}

ghost
requires acc(RequestMem(request), _)
ensures res == (unfolding acc(RequestMem(request), _) in SafeAbs(request.MAC1,16))
pure func RequestMac1(request *Request) (res by.Bytes)

ghost
requires acc(RequestMem(request), _)
ensures res == (unfolding acc(RequestMem(request), _) in SafeAbs(request.MAC2,16))
pure func RequestMac2(request *Request) (res by.Bytes)


ghost
requires acc(RequestMem(request), _)
ensures  res == (unfolding acc(RequestMem(request), _) in by.tuple7B(by.integer32B(request.Type),by.integer32B(request.Sender),Abs(request.Ephemeral),Abs(request.Static),Abs(request.Timestamp),SafeAbs(request.MAC1,16),SafeAbs(request.MAC2,16)))
pure func RequestAbs(request *Request) (res by.Bytes)

pred ResponseMem(response *Response) {
	acc(response) && Mem(response.Ephemeral) && Mem(response.Empty) &&
	Size(response.Ephemeral) == 32 && Size(response.Empty) == 16 &&
	(response.MAC1 != nil ==> Mem(response.MAC1) && Size(response.MAC1) == 16) &&
	(response.MAC2 != nil ==> Mem(response.MAC2) && Size(response.MAC2) == 16)
}

ghost
requires acc(ResponseMem(response), _)
ensures res == (unfolding acc(ResponseMem(response), _) in Abs(response.Ephemeral))
pure func ResponseEpkR(response *Response) (res by.Bytes)

ghost
requires acc(ResponseMem(response), _)
ensures res == (unfolding acc(ResponseMem(response), _) in SafeAbs(response.MAC1,16))
pure func ResponseMac1(response *Response) (res by.Bytes)

ghost
requires acc(ResponseMem(response), _)
ensures res == (unfolding acc(ResponseMem(response), _) in SafeAbs(response.MAC2,16))
pure func ResponseMac2(response *Response) (res by.Bytes)

ghost
requires acc(ResponseMem(response), _)
ensures  res == (unfolding acc(ResponseMem(response), _) in by.tuple7B(by.integer32B(response.Type),by.integer32B(response.Sender),by.integer32B(response.Receiver),Abs(response.Ephemeral),Abs(response.Empty),SafeAbs(response.MAC1,16),SafeAbs(response.MAC2,16)))
pure func ResponseAbs(response *Response) (res by.Bytes) {
	return unfolding acc(ResponseMem(response), _) in by.tuple7B(by.integer32B(response.Type),by.integer32B(response.Sender),by.integer32B(response.Receiver),Abs(response.Ephermeral),Abs(response.Empty),Abs(response.MAC1),Abs(response.MAC2))
}

pred ConnectionMem(conn *Connection) {
	acc(conn) && Mem(conn.SendKey) && Mem(conn.RecvKey) &&
	Size(conn.SendKey) == 32 && Size(conn.RecvKey) == 32
}

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in Abs(conn.SendKey))
pure func ConnectionKIR(conn *Connection) (res by.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in Abs(conn.RecvKey))
pure func ConnectionKRI(conn *Connection) (res by.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in by.integer32B(conn.RemoteIndex))
pure func ConnectionSidI(conn *Connection) (res by.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in by.integer64B(conn.Nonce))
pure func ConnectionNonce(conn *Connection) (res by.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in conn.Nonce)
pure func ConnectionNonceVal(conn *Connection) (res uint64)

pred HandshakeArgsMem(args *HandshakeArguments) {
	acc(args) && Mem(args.PresharedKey) && Mem(args.PrivateKey) && Mem(args.LocalStatic) && Mem(args.RemoteStatic) &&
	Size(args.PresharedKey) == 32 && Size(args.PrivateKey) == 32 && Size(args.LocalStatic) == 32 && Size(args.RemoteStatic) == 32 &&
	Abs(args.LocalStatic) == by.expB(by.generatorB(), Abs(args.PrivateKey))
}
@*/
