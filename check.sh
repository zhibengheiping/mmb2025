#!/usr/bin/env bash
# SPDX-License-Identifier: AGPL-3.0-only

set -e

build() {
for name in test/*.mbt
do
    NAME=$(basename "${name%.mbt}")
    echo BUILD $NAME
    LL=/tmp/mmb/$NAME.ll
    ELF=/tmp/mmb/$NAME.elf
    BC=/tmp/mmb/$NAME.bc
    _build/default/bin/mmb -o $LL $name
    clang -fwrapv -fno-strict-aliasing -O2 -Wno-override-module -o $ELF $LL bench/rt.c -lm
done
}

check() {
for name in test/*.mbt
do
    NAME=$(basename "${name%.mbt}")
    ELF=/tmp/mmb/$NAME.elf
    ANS=test/$NAME.ans
    IN=test/$NAME.in
    if [ -e $ANS ]
    then
        echo CHECK $name
        if [ -e $IN ]
        then
            diff <($ELF < $IN) $ANS || echo 'failed' $?
        else
            diff <($ELF) $ANS || echo 'failed' $?
        fi
    fi
done
}

rebar3 escriptize
moon build
mkdir -p /tmp/mmb
build
check
