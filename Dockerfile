FROM openjdk:13-alpine3.10

RUN apk add --update gcc libc-dev zeromq-dev python3-dev linux-headers

ENV USER tlauser
ENV NB_UID 1000
ENV HOME /home/tlauser
RUN addgroup tlauser && adduser -D -G tlauser -u 1000 tlauser
COPY ./examples /home/tlauser
RUN chown -R tlauser /home/tlauser

RUN pip3 install tlaplus_jupyter
RUN python3 -m tlaplus_jupyter.install

USER tlauser
WORKDIR /home/tlauser
CMD ["jupyter", "notebook", "--ip", "0.0.0.0"]
