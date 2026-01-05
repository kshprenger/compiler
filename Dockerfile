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
    && rm -rf /var/lib/apt/lists/*

# Configure SSH for remote access
RUN echo "root:root" | chpasswd
RUN mkdir /var/run/sshd
RUN sed -i 's/#Port 22/Port 37080/' /etc/ssh/sshd_config
RUN sed -i 's/#PermitRootLogin prohibit-password/PermitRootLogin yes/' /etc/ssh/sshd_config

USER root
WORKDIR /root/compiler

ENV SHELL=/bin/bash

EXPOSE 37080

CMD ["sudo", "/usr/sbin/sshd", "-D", "-e"]
