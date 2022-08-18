# the image for verifying the Tamarin model is based on Python2 because `wireguard.oracle`
# is a Python file that has to be executed with Python2.
FROM python:2.7

RUN apt-get update && \
    apt-get install -y \
        curl \
        zip \
        locales \
        graphviz \
        # libtinfo5 is needed by maude
        libtinfo5

# `/.local/bin` is the installation location of Tamarin and its dependencies
RUN mkdir -p /.local/bin
ENV PATH=/.local/bin:$PATH

# install Haskell stack
RUN curl -L https://www.stackage.org/stack/linux-x86_64 | tar xz --wildcards --strip-components=1 -C /.local/bin '*/stack' && \
    chmod a+x /.local/bin/stack && \
    stack --no-terminal setup

# install Maude
ENV TAMARIN_VERSION 1.6.0
ENV MAUDE_URL https://github.com/tamarin-prover/tamarin-prover/releases/download/$TAMARIN_VERSION/Maude-2.7.1-linux.zip
RUN curl -q -s -S -L --create-dirs -o maude.zip $MAUDE_URL && \
    unzip maude.zip -d /.local/bin/ && \
    rm maude.zip && \
    mv /.local/bin/maude.linux64 /.local/bin/maude && \
    chmod a+x /.local/bin/maude

# install tamarin-prover
RUN curl -q -s -S -L --create-dirs -o tamarin.tar.gz https://github.com/tamarin-prover/tamarin-prover/releases/download/$TAMARIN_VERSION/tamarin-prover-$TAMARIN_VERSION-linux64-ubuntu.tar.gz && \
    tar -x -C /.local/bin/ -f tamarin.tar.gz && \
    rm tamarin.tar.gz && \
    chmod +x /.local/bin/tamarin-prover

# change locale to `en_US.UTF-8`:
USER root
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && \
    locale-gen
ENV LANG en_US.UTF-8  
ENV LANGUAGE en_US:en  
ENV LC_ALL en_US.UTF-8

WORKDIR /tamarin
COPY dh/model/dh.spthy .
COPY wireguard/model/wireguard.oracle .
COPY wireguard/model/wireguard.spthy .
COPY tamarin-docker/verify-dh.sh .
COPY tamarin-docker/verify-wireguard.sh .
