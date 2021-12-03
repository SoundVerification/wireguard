package endpoint

import (
	"errors"

	"wireguard-gobra/wireguard/device"
	"wireguard-gobra/wireguard/log"
	"wireguard-gobra/wireguard/tun"
)

/**
 * Uses a UTUN virtual network interface to receive from / send to operating system
 */
type TUN struct {
	inputChannel  chan<- []byte
	outputChannel <-chan []byte
	closed        chan struct{}
	device        tun.Device
	log           *log.Logger
}

func NewTUN(inputChannel chan<- []byte, outputChannel <-chan []byte, interfaceName string, mtu int, log *log.Logger) (*TUN, error) {
	ep := new(TUN)
	ep.inputChannel = inputChannel
	ep.outputChannel = outputChannel
	ep.closed = make(chan struct{})
	ep.log = log
	var err error
	ep.device, err = tun.CreateTUN(interfaceName, mtu)
	return ep, err
}

func (ep *TUN) Listen() {
	go ep.read()
	go ep.write()
}

func (ep *TUN) close() {
	ep.device.Close()
	close(ep.inputChannel)
	close(ep.closed)
}

func (ep *TUN) Wait() <-chan struct{} {
	return ep.closed
}

func (ep *TUN) read() {
	for {
		var buf [device.MaxMessageSize]byte
		offset := device.MessageTransportHeaderSize
		size, err := ep.device.Read(buf[:], offset)
		if size == 0 || size > device.MaxContentSize {
			err = errors.New("invalid packet received from TUN")
		}

		if err == nil {
			ep.log.Verbosef("Packet from TUN received for sending to peer %x", buf[offset:offset+size])
			ep.inputChannel <- buf[offset : offset+size]
		}
	}
}

func (ep *TUN) write() {
	for {
		// read from channel:
		packet, ok := <-ep.outputChannel
		if ok {
			ep.log.Verbosef("sending packet to TUN: %x", packet)
			_, err := ep.device.Write(packet, device.MessageTransportOffsetContent)
			if err != nil {
				ep.log.Errorf("Writing message to TUN device failed %s", err)
			}
		} else {
			ep.log.Verbosef("Message receive channel was closed")
			break
		}
	}
}

const DefaultMTU = 1420
