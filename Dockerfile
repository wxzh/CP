FROM ubuntu:18.04
RUN apt-get update && apt-get install curl libtinfo-dev -y
RUN curl -sSL https://get.haskellstack.org/ | sh
WORKDIR /CP
COPY . .
RUN stack build
CMD ["stack", "exec", "cp-exe"]
