#!/bin/bash

echo ":main" | ghci src/Server.hs -isrc -XDeriveGeneric -XOverloadedStrings -XDeriveDataTypeable #-package-db=.cabal-sandbox/*-packages.conf.d

