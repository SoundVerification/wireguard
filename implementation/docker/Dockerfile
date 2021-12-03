FROM ghcr.io/viperproject/gobra@sha256:114ee0a11cfc39407d570a7763d4bba1c4d09da1e2f47d0c5b31531be0669d7e

RUN apt-get update && \
	apt-get install -y \
    wget

# install go
RUN mkdir tmp && \
    cd tmp && \
    wget https://go.dev/dl/go1.17.3.linux-amd64.tar.gz && \
    rm -rf /usr/local/go && tar -C /usr/local -xzf go1.17.3.linux-amd64.tar.gz && \
    cd ../ && \
    rm -rf tmp

# add Go to path:
ENV PATH="${PATH}:/usr/local/go/bin"

COPY conn ./conn
COPY device ./device
COPY endpoint ./endpoint
COPY initiator ./initiator
COPY ipc ./ipc
COPY library ./library
COPY log ./log
COPY replay ./replay
COPY responder ./responder
COPY tai64n ./tai64n
COPY tun ./tun
COPY verification ./verification
COPY go.mod .
COPY go.sum .
COPY main.go .
COPY README.md .
COPY docker/compile.sh .
COPY docker/test.sh .
COPY docker/verify.sh .

# compile to trigger download of dependent Go packages:
RUN ./compile.sh

# disable entry point specified by the Gobra base container:
ENTRYPOINT []
