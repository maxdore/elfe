#!/bin/bash

if [ $# == 0 ]; then
    echo ":main" | ghci src/Main.hs -isrc -XDeriveGeneric -XOverloadedStrings -XDeriveDataTypeable #-package-db=.cabal-sandbox/*-packages.conf.d
fi
if [ $# ==  1 ]; then
    echo ":main $1" | ghci src/Main.hs -isrc -XDeriveGeneric -XOverloadedStrings -XDeriveDataTypeable #-package-db=.cabal-sandbox/*-packages.conf.d
fi

