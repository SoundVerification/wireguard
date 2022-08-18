package library

import (
	errors "errors"
	device "wireguard-gobra/wireguard/device"
)

//@ import by "wireguard-gobra/wireguard/verification/bytes"
//@ import io "wireguard-gobra/wireguard/verification/iospec"
//@ import pl "wireguard-gobra/wireguard/verification/place"
//@ import tm "wireguard-gobra/wireguard/verification/util"

//@ requires acc(LibMem(libState), 1/16) && acc(Mem(packet), 1/16)
//@ requires pl.token(t) && io.e_OutFact(t, rid, m) && by.gamma(m) == Abs(packet)
//@ ensures  acc(LibMem(libState), 1/16) && acc(Mem(packet), 1/16)
//@ ensures  ok  ==> pl.token(t1) && t1 == old(io.get_e_OutFact_placeDst(t, rid, m))
//@ ensures  !ok ==> t1 == t && pl.token(t) && io.e_OutFact(t, rid, m) && io.get_e_OutFact_placeDst(t, rid, m) == old(io.get_e_OutFact_placeDst(t, rid, m))
//@ trusted
func (libState *LibraryState) Send(packet ByteString /*@, ghost t pl.Place, ghost rid tm.Term, ghost m tm.Term @*/) (ok bool /*@, ghost t1 pl.Place @*/) {
	err := libState.sendBuffer(packet)
	return err == nil
}

//@ requires acc(LibMem(libState), 1/16) && acc(Mem(msg), 1/16)
//@ ensures  acc(LibMem(libState), 1/16) && acc(Mem(msg), 1/16)
//@ trusted
func (libState *LibraryState) ConsumePacket(msg ByteString) {
	libState.output <- msg
}

/**
 * Sends a raw buffer via network to the peer
 */
//@ trusted
func (libState *LibraryState) sendBuffer(buffer []byte) error {
	if libState.endpoint == nil {
		return errors.New("no known endpoint for peer")
	}

	return libState.dev.Net.Bind.Send(buffer, libState.endpoint)
}

//@ requires acc(LibMem(libState), 1/16) && Mem(msg)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(res) && Size(res) >= old(Size(msg))
//@ ensures  Abs(res) == old(Abs(msg))
//@ trusted
func (libState *LibraryState) PadMsg(msg ByteString) (res ByteString) {
	paddingSize := device.CalculatePaddingSize(len(msg), int(libState.dev.Mtu))
	var paddingZeros [device.PaddingMultiple]byte
	res = append(msg, paddingZeros[:paddingSize]...)
	return
}

//@ requires acc(LibMem(libState), 1/16) && Mem(msg)
//@ ensures  acc(LibMem(libState), 1/16) && Mem(msg) && Size(msg) == old(Size(msg))
//@ ensures  Mem(mac1) && Mem(mac2)
//@ ensures  old(Abs(msg)) == by.tuple7B(by.getFirstB(b),by.getSecondB(b),by.getThirdB(b),by.getForthB(b),by.getFifthB(b),by.zeroStringB(16),by.zeroStringB(16)) ==> Abs(msg) == by.tuple7B(by.getFirstB(b),by.getSecondB(b),by.getThirdB(b),by.getForthB(b),by.getFifthB(b),Abs(mac1),Abs(mac2))
//@ trusted
func (libState *LibraryState) AddMacs(msg ByteString /*@, ghost b by.Bytes @*/) (mac1, mac2 ByteString) {
	// first, compute key that will be used for MACing (could be precomputed)
	// note that the peer's public key (instead of own one) is used in the derivation
	var macKey [KeySize]byte
	ComputeHash(macKey[:], []byte(device.WGLabelMAC1), libState.dev.Peer.Handshake.RemoteStatic[:])

	// set MAC1
	startMac1 := len(msg) - 2*MacSize
	mac1Slice := msg[startMac1 : startMac1+MacSize]
	ComputeMac(mac1Slice, macKey[:], msg[:startMac1]) // MAC all request fields except MAC1 and MAC2
	mac1 = make([]byte, MacSize)
	copy(mac1, mac1Slice)

	// MAC2 is not set as we assume that the system is not under load
	mac2Slice := msg[startMac1+MacSize:]
	mac2 = make([]byte, MacSize)
	copy(mac2, mac2Slice)
	return
}

//@ requires acc(LibMem(libState), 1/16)
//@ ensures  acc(LibMem(libState), 1/16)
//@ trusted
func (libState *LibraryState) Println(msg string) {
	libState.dev.Log.Verbosef(msg)
}
