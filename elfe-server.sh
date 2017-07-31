#!/bin/bash

echo ":main" | ghci src/Server.hs -isrc -XDeriveGeneric -XOverloadedStrings

