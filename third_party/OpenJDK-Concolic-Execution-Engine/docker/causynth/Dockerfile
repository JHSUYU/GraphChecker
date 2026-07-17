FROM --platform=linux/amd64 ubuntu:18.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       autoconf \
       build-essential \
       ca-certificates \
       file \
       gcc-6 \
       g++-6 \
       libasound2-dev \
       libcups2-dev \
       libffi-dev \
       libfontconfig1-dev \
       libfreetype6-dev \
       libx11-dev \
       libxext-dev \
       libxrender-dev \
       libxt-dev \
       libxtst-dev \
       openjdk-8-jdk \
       pkg-config \
       unzip \
       zip \
    && rm -rf /var/lib/apt/lists/*

ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
ENV PATH=${JAVA_HOME}/bin:${PATH}

WORKDIR /workspace
