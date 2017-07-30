#!/bin/bash

if [ $# == 0 ]; then
    echo ":main" | ghci src/Main.hs -isrc -XDeriveGeneric -XOverloadedStrings
fi
if [ $# ==  1 ]; then
    echo ":main $1" | ghci src/Main.hs -isrc -XDeriveGeneric -XOverloadedStrings
fi

