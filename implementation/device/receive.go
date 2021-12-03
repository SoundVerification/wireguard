package device

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"net"
	"time"

	"golang.org/x/crypto/chacha20poly1305"
	"golang.org/x/net/ipv4"
	"golang.org/x/net/ipv6"
)

type InboundElement struct {
	buffer  [MaxMessageSize]byte
	packet  []byte
	counter uint64
	keypair *Keypair
}

func (peer *Peer) ReceiveHandshakeInitiation() error {
	peer.device.Log.Verbosef("Going to ReceiveHandshakeInitiation")
	packet, err := peer.receiveBuffer()
	if err != nil {
		peer.device.Log.Errorf("Error while receiving handshake initiation: %s", err)
		return err
	}
	msgType := peer.getMsgType(packet)
	if msgType != MessageInitiationType {
		return fmt.Errorf("expected message initiation type but got %v", msgType)
	} else if len(packet) != MessageInitiationSize {
		return fmt.Errorf("unexpected message response size, got %v", len(packet))
	}
	peer.device.Log.Verbosef("Handshake initiation message successfully received")

	// unmarshal
	var msg MessageInitiation
	reader := bytes.NewReader(packet)
	err = binary.Read(reader, binary.LittleEndian, &msg)
	if err != nil {
		peer.device.Log.Errorf("Failed to decode initiation message")
		return err
	}

	// consume initiation
	consumedPeer := peer.device.ConsumeMessageInitiation(&msg)
	if consumedPeer == nil || peer != consumedPeer {
		peer.device.Log.Verbosef("Received invalid initiation message")
		return err
	}

	// update endpoint
	// peer.SetEndpointFromPacket(elem.endpoint)

	return nil
}

func (peer *Peer) ReceiveHandshakeResponse() error {
	peer.device.Log.Verbosef("Going to ReceiveHandshakeResponse")
	packet, err := peer.receiveBuffer()
	if err != nil {
		peer.device.Log.Errorf("Error while receiving handshake response: %s", err)
		return err
	}
	msgType := peer.getMsgType(packet)
	if msgType != MessageResponseType {
		return fmt.Errorf("expected message response type but got %v", msgType)
	} else if len(packet) != MessageResponseSize {
		return fmt.Errorf("unexpected message response size, got %v", len(packet))
	}
	peer.device.Log.Verbosef("Handshake response message successfully received")

	// unmarshal
	var msg MessageResponse
	reader := bytes.NewReader(packet)
	err = binary.Read(reader, binary.LittleEndian, &msg)
	if err != nil {
		peer.device.Log.Errorf("Failed to decode response message")
		return err
	}

	// consume response
	consumedPeer := peer.device.ConsumeMessageResponse(&msg)
	if consumedPeer == nil || peer != consumedPeer {
		peer.device.Log.Verbosef("Received invalid response message")
		return err
	}

	// update endpoint
	// peer.SetEndpointFromPacket(elem.endpoint)

	err = peer.BeginSymmetricSession()
	if err != nil {
		peer.device.Log.Errorf("symmetric session failed")
		return err
	}

	peer.device.Log.Verbosef("handshake succeeded")
	return nil
}

/**
 * Receives and handles a transport type message.
 * `message` will contain the decrypted payload or is nil if a keep-alive message has been received
 */
func (peer *Peer) ReceiveMessage() (message []byte, err error) {
	packet, err := peer.receiveBuffer()
	if err != nil {
		peer.device.Log.Errorf("Error while receiving handshake response: %s", err)
		return nil, err
	}
	msgType := peer.getMsgType(packet)
	if msgType != MessageTransportType {
		return nil, fmt.Errorf("expected message transport type but got %v", msgType)
	} else if len(packet) < MessageTransportSize {
		return nil, fmt.Errorf("transport message is too short, got %v", len(packet))
	}
	peer.device.Log.Verbosef("Transport message received")

	// lookup key pair
	receiver := binary.LittleEndian.Uint32(
		packet[MessageTransportOffsetReceiver:MessageTransportOffsetCounter],
	)
	// value := device.indexTable.Lookup(receiver)
	keypair := peer.keypair
	if receiver != keypair.localIndex {
		return nil, fmt.Errorf("unexpected receiver of transport message, got %v", receiver)
	}

	// check keypair expiry
	if keypair.created.Add(RejectAfterTime).Before(time.Now()) {
		return nil, errors.New("keypair has expired")
	}

	// create work element
	var elem InboundElement
	size := copy(elem.buffer[:], packet)
	if size != len(packet) {
		return nil, errors.New("unexpected number of bytes copied")
	}
	elem.packet = elem.buffer[:len(packet)]
	elem.keypair = keypair
	elem.counter = 0

	// decrypt
	err = peer.decryptPacket(&elem)
	if err != nil {
		peer.device.Log.Verbosef("decrypting message has failed")
		elem.packet = nil
		return nil, err
	}

	if !elem.keypair.replayFilter.ValidateCounter(elem.counter, RejectAfterMessages) {
		return nil, errors.New("invalid counter - reject message")
	}

	if len(elem.packet) == 0 {
		peer.device.Log.Verbosef("%v - Receiving keepalive packet", peer)
		return nil, nil
	}

	if peer.device.checkIpPacketHeader {
		switch elem.packet[0] >> 4 {
		case ipv4.Version:
			if len(elem.packet) < ipv4.HeaderLen {
				return nil, errors.New("invalid IPv4 packet")
			}
			field := elem.packet[IPv4offsetTotalLength : IPv4offsetTotalLength+2]
			length := binary.BigEndian.Uint16(field)
			if int(length) > len(elem.packet) || int(length) < ipv4.HeaderLen {
				return nil, errors.New("invalid IPv4 packet length")
			}
			elem.packet = elem.packet[:length]
			src := elem.packet[IPv4offsetSrc : IPv4offsetSrc+net.IPv4len]
			peer.device.Log.Verbosef("IPv4 packet with source address %h received - warning: allowed IP check is not performed", src)
			/*
				if device.allowedips.LookupIPv4(src) != peer {
					device.log.Verbosef("IPv4 packet with disallowed source address from %v", peer)
					goto skip
				}
			*/

		case ipv6.Version:
			if len(elem.packet) < ipv6.HeaderLen {
				return nil, errors.New("invalid IPv6 packet")
			}
			field := elem.packet[IPv6offsetPayloadLength : IPv6offsetPayloadLength+2]
			length := binary.BigEndian.Uint16(field)
			length += ipv6.HeaderLen
			if int(length) > len(elem.packet) {
				return nil, errors.New("invalid IPv6 packet length")
			}
			elem.packet = elem.packet[:length]
			src := elem.packet[IPv6offsetSrc : IPv6offsetSrc+net.IPv6len]
			peer.device.Log.Verbosef("IPv4 packet with source address %h received - warning: allowed IP check is not performed", src)
			/*
				if device.allowedips.LookupIPv6(src) != peer {
					device.log.Verbosef("IPv6 packet with disallowed source address from %v", peer)
					goto skip
				}
			*/

		default:
			return nil, errors.New("Packet with invalid IP version from " + peer.String())
		}
	}

	return elem.buffer[:MessageTransportOffsetContent+len(elem.packet)], nil
}

func (peer *Peer) receiveBuffer() ([]byte, error) {
	var buffer [MaxMessageSize]byte
	switch peer.device.IP {
	case ipv4.Version:
		size, _, err := peer.device.Net.Bind.ReceiveIPv4(buffer[:])
		packet := buffer[:size]
		return packet, err
	case ipv6.Version:
		size, _, err := peer.device.Net.Bind.ReceiveIPv6(buffer[:])
		packet := buffer[:size]
		return packet, err
	default:
		panic("invalid IP version")
	}
}

func (peer *Peer) getMsgType(packet []byte) uint32 {
	return binary.LittleEndian.Uint32(packet[:4])
}

func (peer *Peer) decryptPacket(elem *InboundElement) (err error) {
	var nonce [chacha20poly1305.NonceSize]byte
	counter := elem.packet[MessageTransportOffsetCounter:MessageTransportOffsetContent]
	content := elem.packet[MessageTransportOffsetContent:]
	// decrypt and release to consumer
	elem.counter = binary.LittleEndian.Uint64(counter)
	// copy counter to nonce
	binary.LittleEndian.PutUint64(nonce[0x4:0xc], elem.counter)
	elem.packet, err = elem.keypair.receive.Open(
		content[:0],
		nonce[:],
		content,
		nil,
	)
	return err
}
