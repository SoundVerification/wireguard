package device

import (
	"bytes"
	"encoding/binary"
	"errors"

	"golang.org/x/crypto/chacha20poly1305"
)

type OutboundElement struct {
	buffer  [MaxMessageSize]byte // slice holding the packet data
	packet  []byte               // slice of "buffer" (always!)
	nonce   uint64               // nonce for encryption
	keypair *Keypair             // keypair for encryption
}

func (peer *Peer) SendHandshakeInitiation() error {
	peer.device.Log.Verbosef("%v - Sending handshake initiation", peer)

	msg, err := peer.device.CreateMessageInitiation(peer)
	if err != nil {
		peer.device.Log.Errorf("%v - Failed to create initiation message: %v", peer, err)
		return err
	}

	var buff [MessageInitiationSize]byte
	writer := bytes.NewBuffer(buff[:0])
	binary.Write(writer, binary.LittleEndian, msg)
	packet := writer.Bytes()
	peer.CookieGenerator.AddMacs(packet)

	err = peer.sendBuffer(packet)
	if err != nil {
		peer.device.Log.Errorf("%v - Failed to send handshake initiation: %v", peer, err)
	}

	return err
}

func (peer *Peer) SendHandshakeResponse() error {
	peer.device.Log.Verbosef("%v - Sending handshake response", peer)

	response, err := peer.device.CreateMessageResponse(peer)
	if err != nil {
		peer.device.Log.Errorf("%v - Failed to create response message: %v", peer, err)
		return err
	}

	var buff [MessageResponseSize]byte
	writer := bytes.NewBuffer(buff[:0])
	binary.Write(writer, binary.LittleEndian, response)
	packet := writer.Bytes()
	peer.CookieGenerator.AddMacs(packet)

	err = peer.BeginSymmetricSession()
	if err != nil {
		peer.device.Log.Errorf("%v - Failed to derive keypair: %v", peer, err)
		return err
	}

	err = peer.sendBuffer(packet)
	if err != nil {
		peer.device.Log.Errorf("%v - Failed to send handshake response: %v", peer, err)
	}
	return err
}

func (peer *Peer) SendMessage(buffer []byte) error {
	var elem OutboundElement
	copy(elem.buffer[:], buffer)
	offset := MessageTransportHeaderSize
	// elem.packet = elem.buffer[offset : offset+len(buffer)]
	elem.packet = elem.buffer[offset:len(buffer)]
	// elem.nonce = atomic.AddUint64(&keypair.sendNonce, 1) - 1
	elem.nonce = peer.keypair.sendNonce
	peer.keypair.sendNonce += 1
	if elem.nonce >= RejectAfterMessages {
		// atomic.StoreUint64(&keypair.sendNonce, RejectAfterMessages)
		peer.keypair.sendNonce = RejectAfterMessages
		return errors.New("no more messages can be sent under the current keypair - new handshake is necessary but not implemented")
	}
	elem.keypair = peer.keypair

	var paddingZeros [PaddingMultiple]byte

	// populate header fields
	header := elem.buffer[:MessageTransportHeaderSize]

	fieldType := header[0:4]
	fieldReceiver := header[4:8]
	fieldNonce := header[8:16]

	binary.LittleEndian.PutUint32(fieldType, MessageTransportType)
	binary.LittleEndian.PutUint32(fieldReceiver, elem.keypair.remoteIndex)
	binary.LittleEndian.PutUint64(fieldNonce, elem.nonce)

	// pad content to multiple of 16
	paddingSize := CalculatePaddingSize(len(elem.packet), int(peer.device.Mtu))
	elem.packet = append(elem.packet, paddingZeros[:paddingSize]...)

	// encrypt content
	peer.encryptPacket(&elem)

	// send packet
	return peer.sendBuffer(elem.packet)
}

func (peer *Peer) encryptPacket(elem *OutboundElement) {
	var nonce [chacha20poly1305.NonceSize]byte
	binary.LittleEndian.PutUint64(nonce[4:], elem.nonce)
	header := elem.buffer[:MessageTransportHeaderSize]
	elem.packet = elem.keypair.send.Seal(
		header,
		nonce[:],
		elem.packet,
		nil,
	)
}

/**
 * Sends a raw buffer via network to the peer
 */
func (peer *Peer) sendBuffer(buffer []byte) error {
	if peer.Endpoint == nil {
		return errors.New("no known endpoint for peer")
	}

	return peer.device.Net.Bind.Send(buffer, peer.Endpoint)
}

func CalculatePaddingSize(packetSize int, mtu int) int {
	lastUnit := packetSize
	if mtu == 0 {
		return ((lastUnit + PaddingMultiple - 1) & ^(PaddingMultiple - 1)) - lastUnit
	}
	if lastUnit > mtu {
		lastUnit %= mtu
	}
	paddedSize := ((lastUnit + PaddingMultiple - 1) & ^(PaddingMultiple - 1))
	if paddedSize > mtu {
		paddedSize = mtu
	}
	return paddedSize - lastUnit
}
