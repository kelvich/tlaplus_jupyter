FROM openjdk:13-alpine

RUN apk add --update gcc libc-dev zeromq-dev python-dev py-pip
RUN pip install --no-cache-dir jupyter

ARG NB_USER=jovyan
ARG NB_UID=1000

ENV USER ${NB_USER}
ENV NB_UID ${NB_UID}
ENV HOME /home/${NB_USER}

RUN addgroup ${NB_USER} && adduser \
    -h ${HOME} -D -G ${NB_USER} -u ${NB_UID} ${NB_USER}

COPY . ${HOME}/kernel
RUN cd ${HOME}/kernel && python setup.py install
RUN cd ${HOME} && python -m tlaplus_kernel.install
RUN chown -R ${NB_UID} ${HOME}

USER ${NB_USER}
WORKDIR $HOME
CMD ["jupyter", "notebook", "--ip", "0.0.0.0"]
