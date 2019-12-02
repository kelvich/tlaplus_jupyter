FROM openjdk:13-alpine3.10

RUN apk add --update gcc libc-dev zeromq-dev python3-dev linux-headers

ARG NB_USER=leslie
ARG NB_UID=1000
ENV NB_USER ${NB_USER}
ENV NB_UID ${NB_UID}
RUN addgroup ${NB_USER} && adduser -D -G ${NB_USER} -u ${NB_UID} ${NB_USER}
COPY ./examples /home/${NB_USER}
RUN chown -R ${NB_USER} /home/${NB_USER}

RUN pip3 install tlaplus_jupyter
RUN python3 -m tlaplus_jupyter.install

USER ${NB_USER}
WORKDIR /home/${NB_USER}
CMD ["jupyter", "notebook", "--ip", "0.0.0.0"]
