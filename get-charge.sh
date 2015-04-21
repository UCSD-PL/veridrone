#!/bin/bash

git clone git@github.com:jesper-bengtson/Charge.git
(cd Charge; git checkout a21ed562baf247c8bc5677fc55a594325799e193)
cp Charge.vars Charge/Charge\!/CoqoonMakefile.vars
(cd Charge/Charge\!/ ; ln -s CoqoonMakefile Makefile ; make -j3)
