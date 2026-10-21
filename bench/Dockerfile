# 函子：题目镜像 ↦ 题目镜像 + 解释器。只加 /opt/lojita，不碰 /workspace、不装别的东西，题目与测试原样
ARG BASE
FROM ${BASE}
COPY ctx/agda       /opt/lojita/bin/agda
COPY ctx/agda-data  /opt/lojita/agda-data
COPY ctx/cubical    /opt/lojita/cubical
COPY ctx/lojita     /opt/lojita/lojita
ENV Agda_datadir=/opt/lojita/agda-data
RUN printf '/opt/lojita/cubical/cubical.agda-lib\n' > /opt/lojita/libraries \
 && chmod -R a+rwX /opt/lojita \
 && su agent -s /bin/sh -c 'cd /opt/lojita/lojita && LC_ALL=C.UTF-8 /opt/lojita/bin/agda --library-file=/opt/lojita/libraries src/Bench.agda' \
 && chmod -R a+rwX /opt/lojita
