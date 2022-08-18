package endpoint

type Endpoint interface {
	Listen()
	Wait() <-chan struct{}
}
