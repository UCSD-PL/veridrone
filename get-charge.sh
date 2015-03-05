#!/bin/bash

git clone git@github.com:jesper-bengtson/Charge.git
(cd Charge; git checkout a21ed562baf247c8bc5677fc55a594325799e193; make -j3)
