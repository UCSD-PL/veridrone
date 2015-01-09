open Alphabet
open Automaton
open Datatypes
open Int0
open List0
open Peano
open Specif
open Streams
open Tuples
open Validator_complete

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Make = 
 functor (A:T) ->
 functor (Inter:sig 
  type 'a result =
  | Err
  | OK of 'a
  
  val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
  
  val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
  
  val bind2 : ('a1 * 'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
  
  val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream
  
  type noninitstate_type = A.Gram.symbol_semantic_type
  
  type stack = (A.noninitstate, noninitstate_type) sigT list
  
  val state_of_stack : A.initstate -> stack -> A.state
  
  val pop :
    A.Gram.symbol list -> stack -> 'a1 arrows_right -> (stack * 'a1) result
  
  type step_result =
  | Fail_sr
  | Accept_sr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  | Progress_sr of stack * A.GramDefs.token coq_Stream
  
  val step_result_rect :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    coq_Stream -> 'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) ->
    step_result -> 'a1
  
  val step_result_rec :
    A.initstate -> 'a1 -> (A.Gram.symbol_semantic_type -> A.GramDefs.token
    coq_Stream -> 'a1) -> (stack -> A.GramDefs.token coq_Stream -> 'a1) ->
    step_result -> 'a1
  
  val prod_action' :
    A.Gram.production -> A.Gram.symbol_semantic_type arrows_right
  
  val reduce_step :
    A.initstate -> stack -> A.Gram.production -> A.GramDefs.token coq_Stream
    -> step_result result
  
  val step :
    A.initstate -> stack -> A.GramDefs.token coq_Stream -> step_result result
  
  type parse_result =
  | Fail_pr
  | Timeout_pr
  | Parsed_pr of A.Gram.symbol_semantic_type * A.GramDefs.token coq_Stream
  
  val parse_result_rect :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token coq_Stream -> 'a1) -> parse_result -> 'a1
  
  val parse_result_rec :
    A.initstate -> 'a1 -> 'a1 -> (A.Gram.symbol_semantic_type ->
    A.GramDefs.token coq_Stream -> 'a1) -> parse_result -> 'a1
  
  val parse_fix :
    A.initstate -> stack -> A.GramDefs.token coq_Stream -> nat ->
    parse_result result
  
  val parse :
    A.initstate -> A.GramDefs.token coq_Stream -> nat -> parse_result result
 end) ->
 struct 
  module Valid = Make(A)
  
  type pt_zipper =
  | Top_ptz
  | Cons_ptl_ptz of A.Gram.symbol * A.GramDefs.token list
     * A.Gram.symbol_semantic_type * A.Gram.symbol list
     * A.GramDefs.token list * tuple * A.GramDefs.parse_tree_list
     * ptl_zipper
  and ptl_zipper =
  | Non_terminal_pt_ptlz of A.Gram.production * A.GramDefs.token list * 
     tuple * pt_zipper
  | Cons_ptl_ptlz of A.Gram.symbol * A.GramDefs.token list
     * A.Gram.symbol_semantic_type * A.GramDefs.parse_tree
     * A.Gram.symbol list * A.GramDefs.token list * tuple * ptl_zipper
  
  (** val pt_zipper_rect :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      'a1 -> (A.Gram.symbol -> A.GramDefs.token list ->
      A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
      list -> tuple -> A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) ->
      A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
      -> pt_zipper -> 'a1 **)
  
  let pt_zipper_rect init full_word full_sem f f0 hole_symb hole_word hole_sem = function
  | Top_ptz -> f
  | Cons_ptl_ptz (x, x0, x1, x2, x3, x4, x5, x6) -> f0 x x0 x1 x2 x3 x4 x5 x6
  
  (** val pt_zipper_rec :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      'a1 -> (A.Gram.symbol -> A.GramDefs.token list ->
      A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
      list -> tuple -> A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) ->
      A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
      -> pt_zipper -> 'a1 **)
  
  let pt_zipper_rec init full_word full_sem f f0 hole_symb hole_word hole_sem = function
  | Top_ptz -> f
  | Cons_ptl_ptz (x, x0, x1, x2, x3, x4, x5, x6) -> f0 x x0 x1 x2 x3 x4 x5 x6
  
  (** val ptl_zipper_rect :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      (A.Gram.production -> A.GramDefs.token list -> tuple -> pt_zipper ->
      'a1) -> (A.Gram.symbol -> A.GramDefs.token list ->
      A.Gram.symbol_semantic_type -> A.GramDefs.parse_tree -> A.Gram.symbol
      list -> A.GramDefs.token list -> tuple -> ptl_zipper -> 'a1 -> 'a1) ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
      'a1 **)
  
  let rec ptl_zipper_rect init full_word full_sem f f0 hole_symbs hole_word hole_sems = function
  | Non_terminal_pt_ptlz (p0, word, semantic_values, p1) ->
    f p0 word semantic_values p1
  | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, p0, head_symbolsq,
                   wordq, semantic_valuesq, p1) ->
    f0 head_symbolt wordt semantic_valuet p0 head_symbolsq wordq
      semantic_valuesq p1
      (Obj.magic (ptl_zipper_rect init full_word full_sem f f0)
        (head_symbolt :: head_symbolsq) (app wordt wordq) (semantic_valuet,
        semantic_valuesq) p1)
  
  (** val ptl_zipper_rec :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      (A.Gram.production -> A.GramDefs.token list -> tuple -> pt_zipper ->
      'a1) -> (A.Gram.symbol -> A.GramDefs.token list ->
      A.Gram.symbol_semantic_type -> A.GramDefs.parse_tree -> A.Gram.symbol
      list -> A.GramDefs.token list -> tuple -> ptl_zipper -> 'a1 -> 'a1) ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
      'a1 **)
  
  let rec ptl_zipper_rec init full_word full_sem f f0 hole_symbs hole_word hole_sems = function
  | Non_terminal_pt_ptlz (p0, word, semantic_values, p1) ->
    f p0 word semantic_values p1
  | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, p0, head_symbolsq,
                   wordq, semantic_valuesq, p1) ->
    f0 head_symbolt wordt semantic_valuet p0 head_symbolsq wordq
      semantic_valuesq p1
      (Obj.magic (ptl_zipper_rec init full_word full_sem f f0)
        (head_symbolt :: head_symbolsq) (app wordt wordq) (semantic_valuet,
        semantic_valuesq) p1)
  
  (** val ptlz_cost :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
      nat **)
  
  let ptlz_cost init full_word full_sem =
    let rec ptlz_cost0 hole_symbs hole_word hole_sems = function
    | Non_terminal_pt_ptlz (p, word, semantic_values, ptz) ->
      ptz_cost0 (A.Gram.NT (A.Gram.prod_lhs p)) word
        (uncurry (map (Obj.magic __) (rev (A.Gram.prod_rhs_rev p)))
          (A.Gram.prod_action p) semantic_values) ptz
    | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, pt, head_symbolsq,
                     wordq, semantic_valuesq, ptlz') ->
      Obj.magic ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordt wordq)
        (semantic_valuet, semantic_valuesq) ptlz'
    and ptz_cost0 hole_symb hole_word hole_sem = function
    | Top_ptz -> O
    | Cons_ptl_ptz (head_symbolt, wordt, semantic_valuet, head_symbolsq,
                    wordq, semantic_valuesq, ptl, ptlz') ->
      plus
        (plus (S O)
          (A.GramDefs.ptl_size head_symbolsq wordq semantic_valuesq ptl))
        (Obj.magic ptlz_cost0 (head_symbolt :: head_symbolsq)
          (app wordt wordq) (semantic_valuet, semantic_valuesq) ptlz')
    in ptlz_cost0
  
  (** val ptz_cost :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol -> A.GramDefs.token list -> A.Gram.symbol_semantic_type
      -> pt_zipper -> nat **)
  
  let ptz_cost init full_word full_sem =
    let rec ptlz_cost0 hole_symbs hole_word hole_sems = function
    | Non_terminal_pt_ptlz (p, word, semantic_values, ptz) ->
      ptz_cost0 (A.Gram.NT (A.Gram.prod_lhs p)) word
        (uncurry (map (Obj.magic __) (rev (A.Gram.prod_rhs_rev p)))
          (A.Gram.prod_action p) semantic_values) ptz
    | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, pt, head_symbolsq,
                     wordq, semantic_valuesq, ptlz') ->
      ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordt wordq)
        (semantic_valuet, semantic_valuesq) ptlz'
    and ptz_cost0 hole_symb hole_word hole_sem = function
    | Top_ptz -> O
    | Cons_ptl_ptz (head_symbolt, wordt, semantic_valuet, head_symbolsq,
                    wordq, semantic_valuesq, ptl, ptlz') ->
      plus
        (plus (S O)
          (A.GramDefs.ptl_size head_symbolsq wordq semantic_valuesq ptl))
        (ptlz_cost0 (head_symbolt :: head_symbolsq) (app wordt wordq)
          (semantic_valuet, semantic_valuesq) ptlz')
    in ptz_cost0
  
  type pt_dot =
  | Reduce_ptd of ptl_zipper
  | Shift_ptd of A.Gram.terminal * A.Gram.symbol_semantic_type
     * A.Gram.symbol list * A.GramDefs.token list * tuple
     * A.GramDefs.parse_tree_list * ptl_zipper
  
  (** val pt_dot_rect :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      (ptl_zipper -> 'a1) -> (A.Gram.terminal -> A.Gram.symbol_semantic_type
      -> A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
      A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1 **)
  
  let pt_dot_rect init full_word full_sem f f0 = function
  | Reduce_ptd x -> f x
  | Shift_ptd (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5
  
  (** val pt_dot_rec :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      (ptl_zipper -> 'a1) -> (A.Gram.terminal -> A.Gram.symbol_semantic_type
      -> A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
      A.GramDefs.parse_tree_list -> ptl_zipper -> 'a1) -> pt_dot -> 'a1 **)
  
  let pt_dot_rec init full_word full_sem f f0 = function
  | Reduce_ptd x -> f x
  | Shift_ptd (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5
  
  (** val ptd_cost :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      pt_dot -> nat **)
  
  let ptd_cost init full_word full_sem = function
  | Reduce_ptd ptlz ->
    ptlz_cost init full_word full_sem [] [] (Obj.magic ()) ptlz
  | Shift_ptd (term, sem, symbolsq, wordq, semsq, ptl, ptlz) ->
    plus (plus (S O) (A.GramDefs.ptl_size symbolsq wordq semsq ptl))
      (ptlz_cost init full_word full_sem ((A.Gram.T term) :: symbolsq)
        ((Coq_existT (term, sem)) :: wordq) (Obj.magic (sem, semsq)) ptlz)
  
  (** val ptlz_buffer :
      A.initstate -> A.GramDefs.token list -> A.GramDefs.token coq_Stream ->
      A.Gram.symbol_semantic_type -> A.Gram.symbol list -> A.GramDefs.token
      list -> tuple -> ptl_zipper -> A.GramDefs.token coq_Stream **)
  
  let ptlz_buffer init full_word buffer_end full_sem =
    let rec ptlz_buffer0 hole_symbs hole_word hole_sems = function
    | Non_terminal_pt_ptlz (p, word, semantic_values, ptz) ->
      ptz_buffer0 (A.Gram.NT (A.Gram.prod_lhs p)) word
        (uncurry (map (Obj.magic __) (rev (A.Gram.prod_rhs_rev p)))
          (A.Gram.prod_action p) semantic_values) ptz
    | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, p, head_symbolsq,
                     wordq, semantic_valuesq, ptlz') ->
      Obj.magic ptlz_buffer0 (head_symbolt :: head_symbolsq)
        (app wordt wordq) (semantic_valuet, semantic_valuesq) ptlz'
    and ptz_buffer0 hole_symb hole_word hole_sem = function
    | Top_ptz -> buffer_end
    | Cons_ptl_ptz (head_symbolt, wordt, semantic_valuet, head_symbolsq,
                    wordq, semantic_valuesq, ptl, ptlz') ->
      Inter.app_str wordq
        (Obj.magic ptlz_buffer0 (head_symbolt :: head_symbolsq)
          (app wordt wordq) (semantic_valuet, semantic_valuesq) ptlz')
    in ptlz_buffer0
  
  (** val ptz_buffer :
      A.initstate -> A.GramDefs.token list -> A.GramDefs.token coq_Stream ->
      A.Gram.symbol_semantic_type -> A.Gram.symbol -> A.GramDefs.token list
      -> A.Gram.symbol_semantic_type -> pt_zipper -> A.GramDefs.token
      coq_Stream **)
  
  let ptz_buffer init full_word buffer_end full_sem =
    let rec ptlz_buffer0 hole_symbs hole_word hole_sems = function
    | Non_terminal_pt_ptlz (p, word, semantic_values, ptz) ->
      ptz_buffer0 (A.Gram.NT (A.Gram.prod_lhs p)) word
        (uncurry (map (Obj.magic __) (rev (A.Gram.prod_rhs_rev p)))
          (A.Gram.prod_action p) semantic_values) ptz
    | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, p, head_symbolsq,
                     wordq, semantic_valuesq, ptlz') ->
      ptlz_buffer0 (head_symbolt :: head_symbolsq) (app wordt wordq)
        (semantic_valuet, semantic_valuesq) ptlz'
    and ptz_buffer0 hole_symb hole_word hole_sem = function
    | Top_ptz -> buffer_end
    | Cons_ptl_ptz (head_symbolt, wordt, semantic_valuet, head_symbolsq,
                    wordq, semantic_valuesq, ptl, ptlz') ->
      Inter.app_str wordq
        (ptlz_buffer0 (head_symbolt :: head_symbolsq) (app wordt wordq)
          (semantic_valuet, semantic_valuesq) ptlz')
    in ptz_buffer0
  
  (** val ptd_buffer :
      A.initstate -> A.GramDefs.token list -> A.GramDefs.token coq_Stream ->
      A.Gram.symbol_semantic_type -> pt_dot -> A.GramDefs.token coq_Stream **)
  
  let ptd_buffer init full_word buffer_end full_sem = function
  | Reduce_ptd ptlz ->
    ptlz_buffer init full_word buffer_end full_sem [] [] (Obj.magic ()) ptlz
  | Shift_ptd (term, sem, symbolsq, wordq, semsq, p, ptlz) ->
    lazy (Cons ((Coq_existT (term, sem)),
      (Inter.app_str wordq
        (ptlz_buffer init full_word buffer_end full_sem ((A.Gram.T
          term) :: symbolsq) ((Coq_existT (term, sem)) :: wordq)
          (Obj.magic (sem, semsq)) ptlz))))
  
  (** val ptlz_prod :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
      A.Gram.production **)
  
  let rec ptlz_prod init full_word full_sem hole_symbs hole_word hole_sems = function
  | Non_terminal_pt_ptlz (prod, word, semantic_values, p) -> prod
  | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, p, head_symbolsq,
                   wordq, semantic_valuesq, ptlz') ->
    Obj.magic (ptlz_prod init full_word full_sem)
      (head_symbolt :: head_symbolsq) (app wordt wordq) (semantic_valuet,
      semantic_valuesq) ptlz'
  
  (** val ptlz_past :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple -> ptl_zipper ->
      A.Gram.symbol list **)
  
  let rec ptlz_past init full_word full_sem hole_symbs hole_word hole_sems = function
  | Non_terminal_pt_ptlz (p, word, semantic_values, p0) -> []
  | Cons_ptl_ptlz (s, wordt, semantic_valuet, p, head_symbolsq, wordq,
                   semantic_valuesq, ptlz') ->
    s :: (Obj.magic (ptlz_past init full_word full_sem) (s :: head_symbolsq)
           (app wordt wordq) (semantic_valuet, semantic_valuesq) ptlz')
  
  (** val build_pt_dot :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
      A.GramDefs.parse_tree_list -> ptl_zipper -> pt_dot **)
  
  let rec build_pt_dot init full_word full_sem hole_symbs hole_word hole_sems ptl ptlz =
    match ptl with
    | A.GramDefs.Nil_ptl -> Reduce_ptd ptlz
    | A.GramDefs.Cons_ptl (head_symbolt, wordt, semantic_valuet, pt,
                           head_symbolsq, wordq, semantic_valuesq, ptl') ->
      (match pt with
       | A.GramDefs.Terminal_pt (term, sem) ->
         Shift_ptd (term, sem, head_symbolsq, wordq, semantic_valuesq, ptl',
           ptlz)
       | A.GramDefs.Non_terminal_pt (p, word, semantic_values, ptl'') ->
         build_pt_dot init full_word full_sem (rev (A.Gram.prod_rhs_rev p))
           word semantic_values ptl'' (Non_terminal_pt_ptlz (p, word,
           semantic_values, (Cons_ptl_ptz ((A.Gram.NT (A.Gram.prod_lhs p)),
           word,
           (uncurry (map (Obj.magic __) (rev (A.Gram.prod_rhs_rev p)))
             (A.Gram.prod_action p) semantic_values), head_symbolsq, wordq,
           semantic_valuesq, ptl', ptlz)))))
  
  (** val pop_ptlz :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.Gram.symbol list -> A.GramDefs.token list -> tuple ->
      A.GramDefs.parse_tree_list -> ptl_zipper -> (A.GramDefs.token list,
      (A.Gram.symbol_semantic_type, pt_zipper * A.GramDefs.parse_tree) sigT)
      sigT **)
  
  let rec pop_ptlz init full_word full_sem hole_symbs hole_word hole_sems ptl = function
  | Non_terminal_pt_ptlz (prod, word, sem, ptz) ->
    let sem0 =
      uncurry (map (Obj.magic __) (rev (A.Gram.prod_rhs_rev prod)))
        (A.Gram.prod_action prod) sem
    in
    Coq_existT (word, (Coq_existT (sem0, (ptz, (A.GramDefs.Non_terminal_pt
    ((ptlz_prod init full_word full_sem (rev (A.Gram.prod_rhs_rev prod)) word
       sem (Non_terminal_pt_ptlz (prod, word, sem, ptz))), word, sem,
    ptl))))))
  | Cons_ptl_ptlz (head_symbolt, wordt, semantic_valuet, pt, head_symbolsq,
                   wordq, semantic_valuesq, ptlz') ->
    Obj.magic (pop_ptlz init full_word full_sem)
      (head_symbolt :: head_symbolsq) (app wordt wordq) (semantic_valuet,
      semantic_valuesq) (A.GramDefs.Cons_ptl (head_symbolt, wordt,
      semantic_valuet, pt, head_symbolsq, wordq, semantic_valuesq, ptl))
      ptlz'
  
  (** val next_ptd :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      pt_dot -> pt_dot option **)
  
  let next_ptd init full_word full_sem = function
  | Reduce_ptd ptlz ->
    let Coq_existT (x, s) =
      pop_ptlz init full_word full_sem [] [] (Obj.magic ())
        A.GramDefs.Nil_ptl ptlz
    in
    let Coq_existT (x0, p) = s in
    let (ptz, pt) = p in
    (match ptz with
     | Top_ptz -> None
     | Cons_ptl_ptz (head_symbolt, wordt, semantic_valuet, head_symbolsq,
                     wordq, semantic_valuesq, ptl, ptlz') ->
       Some
         (build_pt_dot init full_word full_sem head_symbolsq wordq
           semantic_valuesq ptl (Cons_ptl_ptlz (head_symbolt, wordt,
           semantic_valuet, pt, head_symbolsq, wordq, semantic_valuesq,
           ptlz'))))
  | Shift_ptd (term, sem, symbolsq, wordq, semsq, ptl, ptlz) ->
    Some
      (build_pt_dot init full_word full_sem symbolsq wordq semsq ptl
        (Cons_ptl_ptlz ((A.Gram.T term), ((Coq_existT (term, sem)) :: []),
        sem, (A.GramDefs.Terminal_pt (term, sem)), symbolsq, wordq, semsq,
        ptlz)))
  
  (** val init_ptd :
      A.initstate -> A.GramDefs.token list -> A.Gram.symbol_semantic_type ->
      A.GramDefs.parse_tree -> pt_dot **)
  
  let init_ptd init full_word full_sem full_pt =
    let x = Top_ptz in
    (match full_pt with
     | A.GramDefs.Terminal_pt (t0, sem) -> Obj.magic ()
     | A.GramDefs.Non_terminal_pt (p, word, semantic_values, ptl) ->
       build_pt_dot init full_word full_sem (rev (A.Gram.prod_rhs_rev p))
         word semantic_values ptl (Non_terminal_pt_ptlz (p, word,
         semantic_values, x)))
 end

