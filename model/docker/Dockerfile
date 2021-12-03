FROM homebrew/brew

# download latest Tamarin version & its dependencies:
RUN brew install tamarin-prover/tap/tamarin-prover

# install python2:
RUN brew install pyenv
RUN pyenv install 2.7.18
RUN pyenv global 2.7.18
# create /usr/bin/python2 symlink as this is expected by `wireguard.oracle`:
# `/home/linuxbrew/.pyenv` corresponds to `$(pyenv root)`
RUN sudo ln -s /home/linuxbrew/.pyenv/shims/python2 /usr/bin/python2

# change locale to `en_US.UTF-8`:
USER root
RUN apt-get update && apt-get install -y locales
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && \
    locale-gen
ENV LANG en_US.UTF-8  
ENV LANGUAGE en_US:en  
ENV LC_ALL en_US.UTF-8

WORKDIR /tamarin

# download Tamarin 1.6.0:
RUN curl -L https://github.com/tamarin-prover/tamarin-prover/releases/download/1.6.0/tamarin-prover-1.6.0-linux64-ubuntu.tar.gz --output tamarin.tar.gz && \
	tar -xf tamarin.tar.gz && \
	rm tamarin.tar.gz

COPY wireguard.oracle .
COPY wireguard.spthy .
