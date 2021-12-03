package endpoint

import (
	"bufio"
	"encoding/binary"
	"fmt"
	"os"

	"wireguard-gobra/wireguard/device"
	"wireguard-gobra/wireguard/log"
)

/**
 * Uses standard input and output to read and write input and output, respectively.
 * Output is coming from the other peer, input is forward to the other peer.
 */
type StandardIO struct {
	inputChannel		chan<- []byte
	outputChannel		<-chan []byte
	closed				chan struct{}
	scanner				*bufio.Scanner
	log					*log.Logger
	emptyMsgSent		bool
	emptyMsgReceived	bool
	isClosed			bool
}

func NewStandardIO(inputChannel chan<- []byte, outputChannel <-chan []byte,log *log.Logger) *StandardIO {
	standardIO := new(StandardIO)
	standardIO.log = log
	standardIO.inputChannel = inputChannel
	standardIO.outputChannel = outputChannel
	standardIO.closed = make(chan struct{})
	standardIO.scanner = bufio.NewScanner(os.Stdin)
	return standardIO
}

func (standardIO *StandardIO) Listen() {
	go standardIO.read()
	go standardIO.write()
}

func (standardIO *StandardIO) read() {
	fmt.Println("Please enter message to be sent:")
	for standardIO.scanner.Scan() {
		text := standardIO.scanner.Text()
		fmt.Println("Sending:", text)
		if (len(text) == 0) {
			standardIO.emptyMsgSent = true
		}
		standardIO.sendString(text)
		if (len(text) == 0) {
			break
		}
	}
	if err := standardIO.scanner.Err(); err != nil {
		standardIO.log.Errorf("Error reading from input:", err)
		return
	}
	// if `Scan()` returned false AND not error occurred, EOF has been reached
	// send an empty message in both directions to indicate shutdown to both parties
	if (!standardIO.emptyMsgSent) {
		fmt.Println("Sending empty msg")
		standardIO.emptyMsgSent = true
		standardIO.sendString("")
	}
	if (standardIO.emptyMsgSent && standardIO.emptyMsgReceived && !standardIO.isClosed) {
		// thus, shutdown application
		standardIO.isClosed = true
		standardIO.close()
	}
}

func (standardIO *StandardIO) sendString(s string) {
	// send slice of bytes to channel but prepend transport header many bytes:
	// TODO check if channel is still open
	// we prepend the string length such that we can easily decode it without
	// needing to worry about padding
	var stringLen [binary.MaxVarintLen64]byte
	binary.LittleEndian.PutUint64(stringLen[:], uint64(len(s)))
	buf := append(stringLen[:], []byte(s)...)
	standardIO.inputChannel <- buf
}

func (standardIO *StandardIO) write() {
	for {
		// read from channel:
		output, ok := <-standardIO.outputChannel
		if ok && len(output) >= device.MessageTransportHeaderSize {
			// remove transport header:
			buf := output[device.MessageTransportHeaderSize:]
			stringLen := binary.LittleEndian.Uint64(buf[:binary.MaxVarintLen64])
			msg := string(buf[binary.MaxVarintLen64:binary.MaxVarintLen64+stringLen])
			if len(msg) == 0 {
				fmt.Println("Empty msg received")
				standardIO.emptyMsgReceived = true
				if (standardIO.emptyMsgSent && standardIO.emptyMsgReceived && !standardIO.isClosed) {
					// thus, shutdown application
					standardIO.isClosed = true
					standardIO.close()
				}
			} else {
				fmt.Println("Message received:", msg)
			}
		} else {
			standardIO.log.Verbosef("Message receive channel was closed")
			break
		}
	}
}

func (standardIO *StandardIO) Wait() <-chan struct{} {
	return standardIO.closed
}

func (standardIO *StandardIO) close() {
	standardIO.log.Verbosef("Closing standard IO input channel")
	close(standardIO.inputChannel)
	close(standardIO.closed)
}
