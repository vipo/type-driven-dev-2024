FROM ubuntu

WORKDIR /root

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=${PATH}:/root/.pack/bin

RUN apt-get update -y \
  && apt-get install -y \
  build-essential \
  curl \
  git \
  libgmp3-dev \
  libncurses5-dev \
  libncursesw5-dev \
  libx11-dev \
  rlwrap \
  && rm -rf /var/lib/apt/lists/

RUN git clone https://github.com/cisco/ChezScheme \
  && cd ChezScheme \
  && git checkout 0b2f4d37d1e105039f76933206ca911c9aa936fb \
  && ./configure --threads \
  && make \
  && make install \
  && cd .. \
  && rm -rf ChezScheme

RUN git clone https://github.com/stefan-hoeck/idris2-pack.git pack \
  && cd pack \
  && git checkout 12f5a13977c6682f269e5f03758cea1c8e61ac77 \
  && echo scheme | bash -c ./install.bash \
  && cd .. \
  && rm -rf pack

RUN yes yes | pack install-app idris2-lsp

