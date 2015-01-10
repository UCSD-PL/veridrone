#!/bin/bash

ocamlc -o ./src/pretty.cma -pack \
    gather/Errors.d.cmo \
    gather/Datatypes.d.cmo gather/Bool.d.cmo gather/Peano.d.cmo \
    gather/BinPos.d.cmo gather/BinNat.d.cmo gather/BinInt.d.cmo \
    gather/Zpower.d.cmo gather/Specif.d.cmo gather/List0.d.cmo \
    gather/ZArith_dec.d.cmo gather/Coqlib.d.cmo gather/Integers.d.cmo \
    gather/Fcore_Zaux.d.cmo gather/Zbool.d.cmo gather/Fcalc_bracket.d.cmo \
    gather/Fcore_digits.d.cmo gather/Fcore_FLT.d.cmo gather/Fcalc_round.d.cmo \
    gather/Fappli_IEEE.d.cmo gather/Fappli_IEEE_bits.d.cmo \
    gather/Fappli_IEEE_extra.d.cmo \
    gather/Archi.d.cmo gather/Floats.d.cmo \
    gather/Camlcoq.cmo gather/AST.d.cmo gather/Ctypes.d.cmo \
    gather/Csyntax.d.cmo gather/PrintCsyntax.cmo gather/PrintAST.cmo \
    gather/Clight.d.cmo gather/PrintClight.cmo
