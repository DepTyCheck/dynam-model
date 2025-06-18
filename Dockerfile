FROM ghcr.io/stefan-hoeck/idris2-pack:latest

COPY groovy /opt/groovy
COPY jdk-21 /opt/java

ENV GROOVY_HOME=/opt/groovy/groovy-5.0.0-alpha-12
ENV JAVA_HOME=/opt/java
ENV PATH=$JAVA_HOME/bin:$GROOVY_HOME/bin:$PATH

WORKDIR /home/groovy

COPY build /home/groovy/build
COPY groovy_verify.sh .

ENTRYPOINT [ "./groovy_verify.sh", "4", "300" ]
