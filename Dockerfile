FROM --platform=linux/amd64 debian:bookworm-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    git \
    m4 \
    unzip \
    opam \
    openssh-server \
    sudo \
    ca-certificates \
    pkg-config \
    libssl-dev \
    wget \
    && rm -rf /var/lib/apt/lists/*

RUN wget https://go.dev/dl/go1.22.4.linux-amd64.tar.gz \
    && tar -C /usr/local -xzf go1.22.4.linux-amd64.tar.gz \
    && rm go1.22.4.linux-amd64.tar.gz

ENV PATH="/usr/local/go/bin:${PATH}"
ENV GOPATH="/root/go"
ENV PATH="${GOPATH}/bin:${PATH}"

RUN passwd -d root
RUN mkdir /var/run/sshd
RUN sed -i 's/#Port 22/Port 37080/' /etc/ssh/sshd_config
RUN sed -i 's/#PermitRootLogin prohibit-password/PermitRootLogin yes/' /etc/ssh/sshd_config
RUN echo "PermitEmptyPasswords yes" >> /etc/ssh/sshd_config

RUN opam init --disable-sandboxing -y && eval $(opam env) && opam install -y dune menhir

RUN echo 'eval $(opam env)' >> /root/.bashrc

USER root
WORKDIR /root/compiler

ENV SHELL=/bin/bash

EXPOSE 37080

CMD ["sudo", "/usr/sbin/sshd", "-D", "-e"]
