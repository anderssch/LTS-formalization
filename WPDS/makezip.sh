#!/bin/bash
rm -f WPDS.zip
mkdir -p WPDS
cp *.thy WPDS
cp README.md WPDS
zip -r WPDS.zip WPDS
rm -r WPDS

