package device

import (
	"wireguard-gobra/wireguard/conn"
	"wireguard-gobra/wireguard/log"
)

type Device struct {
	IsInitiator bool

	Net struct {
		Bind   conn.Bind // bind interface
		port   uint16    // listening port
		fwmark uint32    // mark value (0 = disabled)
	}

	InputChannel  chan []byte
	OutputChannel chan []byte

	StaticIdentity struct {
		PrivateKey NoisePrivateKey
		PublicKey  NoisePublicKey
	}

	Peer                *Peer
	IP                  int
	Mtu                 int32
	checkIpPacketHeader bool // indicates whether headers of received packets should be inspected or not

	closed chan struct{}
	Log    *log.Logger
}

func (device *Device) Up() error {
	// return device.changeState(deviceStateUp)
	return nil
}

func (device *Device) Down() error {
	// return device.changeState(deviceStateDown)
	return nil
}

func NewDevice(inputChannel, outputChannel chan []byte, isInitiator bool, bind conn.Bind, IP int, port uint16, endpoint conn.Endpoint, privateKey NoisePrivateKey, publicKey, peerPublicKey NoisePublicKey, mtu int32, logger *log.Logger, checkIpPacketHeader bool) *Device {
	device := new(Device)
	device.closed = make(chan struct{})
	device.IsInitiator = isInitiator
	device.Log = logger
	device.Net.Bind = bind
	device.Net.port = port
	device.InputChannel = inputChannel
	device.OutputChannel = outputChannel
	device.StaticIdentity.PrivateKey = privateKey
	device.StaticIdentity.PublicKey = publicKey
	device.Peer = NewPeer(device, endpoint, peerPublicKey)
	device.IP = IP
	device.Mtu = mtu
	device.checkIpPacketHeader = checkIpPacketHeader

	return device
}

func (device *Device) Start(protocol func(*Device)) {
	// open port
	err := device.bindUpdate()
	if err != nil {
		device.Log.Errorf("Bind Update failed with %s", err)
		return
	}

	protocol(device)
}

func (device *Device) RunProtocolInitiator() {

	err := device.performHandshakeInitiator()
	if err != nil {
		device.Log.Errorf("Handshake has failed %s", err)
		return
	}

	// forward messages
	go device.forwardPackets()
}

func (device *Device) RunProtocolResponder() {
	err := device.performHandshakeResponder()
	if err != nil {
		device.Log.Errorf("Handshake has failed %s", err)
		return
	}

	// forward messages
	go device.forwardPackets()
}

func (device *Device) bindUpdate() error {
	// bind to new port
	var err error
	netc := &device.Net
	netc.port, err = netc.Bind.Open(netc.port)
	if err != nil {
		netc.port = 0
		return err
	}
	device.Log.Verbosef("This endpoint is listening on port: %v", netc.port)
	/*
		netc.netlinkCancel, err = device.startRouteListener(netc.bind)
		if err != nil {
			netc.bind.Close()
			netc.port = 0
			return err
		}
	*/
	// set fwmark
	if netc.fwmark != 0 {
		err = netc.Bind.SetMark(netc.fwmark)
		if err != nil {
			return err
		}
	}

	// clear cached source addresses
	device.Peer.Endpoint.ClearSrc()

	return nil
}

func (device *Device) performHandshakeInitiator() error {
	// send handshake init
	err := device.Peer.SendHandshakeInitiation()
	if err != nil {
		device.Log.Errorf("Sending handshake initiation has failed")
		return err
	}
	// wait for handshake response:
	err = device.Peer.ReceiveHandshakeResponse()
	if err != nil {
		device.Log.Errorf("Receiving handshake response has failed")
		return err
	}
	return nil
}

func (device *Device) performHandshakeResponder() error {
	// wait for handshake init
	err := device.Peer.ReceiveHandshakeInitiation()
	if err != nil {
		device.Log.Errorf("Receiving handshake initiation has failed")
		return err
	}
	// send handshake response
	err = device.Peer.SendHandshakeResponse()
	if err != nil {
		device.Log.Errorf("Sending handshake response has failed")
		return err
	}
	return nil
}

/**
 * Either receives packets from OS and forwards them to the peer or vice versa
 */
func (device *Device) forwardPackets() {
	for {
		if device.IsInitiator {
			// receive packet from OS and forward it to peer
			request, ok := <-device.InputChannel
			if ok {
				// forward packet to peer:
				err := device.Peer.SendMessage(request)
				if err != nil {
					device.Log.Errorf("Sending message has failed: %s", err)
					continue
				}

				// receive response from peer:
				var response []byte
				for response == nil {
					response, err = device.Peer.ReceiveMessage()
					if err != nil {
						device.Log.Errorf("Receiving message has failed: %s", err)
						continue
					}
					if response == nil {
						// if a keep-alive message is received, ReceiveMessage returns a nil message
						device.Log.Verbosef("nil message received - forwarding is skipped and another message is expected to be received")
					}
				}

				// forward response to OS:
				device.OutputChannel <- response
			}
		} else {
			// receive packet from peer and forward it to OS
			// receive packet from peer:
			var request []byte
			var err error
			for request == nil {
				request, err = device.Peer.ReceiveMessage()
				if err != nil {
					device.Log.Errorf("Receiving message has failed: %s", err)
					continue
				}
				if request == nil {
					// if a keep-alive message is received, ReceiveMessage returns a nil message
					device.Log.Verbosef("nil message received - forwarding is skipped and another message is expected to be received")
				}
			}

			// forward packet to OS:
			device.OutputChannel <- request

			// receive response from OS:
			response, ok := <-device.InputChannel

			// forward response to peer:
			if ok {
				err := device.Peer.SendMessage(response)
				if err != nil {
					device.Log.Errorf("Sending message has failed: %s", err)
					continue
				} else {
					device.Log.Verbosef("Send Message")
				}
			}
		}
	}
}

func (device *Device) Close() {
	device.Log.Verbosef("Closing device")
	device.Net.Bind.Close()
	close(device.OutputChannel)
	close(device.closed)
}

func (device *Device) Wait() <-chan struct{} {
	return device.closed
}
