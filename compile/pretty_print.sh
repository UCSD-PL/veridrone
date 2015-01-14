#!/bin/bash

#
# Shell script that wraps around the ocaml toplevel
# Enabling us to pretty-print Clight AST as C code
# Will clobber ./.ocaml_init, fyi
#
# Arguments:
# $1: extracted ML file to load
# $2: name of _compiled_ AST, in ML code (should usually be same name as in Coq)
# $3: name of file to output c code into
#

echo "Please read this script, be sure you understand what it does."
echo "And what arguments it expects. At this time there are no sanity checks,"
echo "Here is what your input is:"
echo "(Extracted) ML file to load: $1"
echo "Name of variable in $1 containing AST to pretty-print: $2"
echo "C file to output to: $3"
echo "Hit ENTER to confirm this is correct,"
echo "Or hit Ctrl-C to stop and change your input."
read START_PROMPT

#
# Construct the ocaml_init file, to make OCaml pretty-print the right thing
# According to the arguments we passed in
#

# clear the old value
echo "" > .ocaml_init
echo "open Unix;;" >> .ocaml_init
echo "#use" "\"$1\";;" >> .ocaml_init
echo "let fd = openfile" "\"$3\"" "[O_CREAT; O_TRUNC; O_RDWR] 0o777;;" >> .ocaml_init
echo "let oc = out_channel_of_descr fd;;" >> .ocaml_init
echo "let foc = Format.formatter_of_out_channel oc;;" >> .ocaml_init
echo "Pretty.PrintClight.print_program foc $2;;" >> .ocaml_init
echo "#quit;;" >> .ocaml_init

#
# Run ocaml with the proper ocaml_init
#
ocaml unix.cma str.cma pretty.cma -init ./.ocaml_init
