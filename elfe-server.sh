#!/bin/bash

echo ":main" | ghci src/Server.hs -isrc -XDeriveGeneric -XOverloadedStrings #-package-db=.cabal-sandbox/*-packages.conf.d

