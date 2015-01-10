open Util
open Pp
open Names

open Evd
open Goal
open Printf
open Unix
open Errors
open Marshal

open Pretty.PrintClight

let clight_dump_tactic s p = fun gl ->
    let fd = openfile s [O_CREAT; O_TRUNC; O_RDWR] 0o777 in
    let oc = out_channel_of_descr fd in
    let foc = Format.formatter_of_out_channel oc in
    (*to_channel oc p [No_sharing; Closures];*)
    print_program foc p;
    close_out oc;
    Tacticals.tclIDTAC gl

TACTIC EXTEND ClightDegen
       | ["clight_dump" string(s) constr(p)] -> [clight_dump_tactic s p] END;;
