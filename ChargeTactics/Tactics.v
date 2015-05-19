Require Export Charge.Logics.ILogic.
Require ChargeTactics.Lemmas.

Ltac charge_split := apply landR.

Ltac charge_search_prems found :=
  match goal with
  | |- ?X |-- ?Y =>
    solve [ found
          | apply landL1 ; charge_search_prems found
          | apply landL2 ; charge_search_prems found ]
  end.

Ltac charge_assumption :=
  charge_search_prems reflexivity.

Ltac charge_intro :=
  first [ apply lforallR; intro
        | apply Lemmas.limplAdj_true
        | apply limplAdj ].

Ltac charge_intros :=
  repeat match goal with
         | |- _ |-- _ -->> _ =>
           charge_intro
         | |- _ |-- @lforall _ _ _ _ =>
           charge_intro
         end.

Ltac charge_trivial := apply ltrueR.

Ltac charge_use :=
  first [ eapply Lemmas.lapply; [ charge_assumption | ]
        | eapply Lemmas.lapply2; [ charge_assumption | | ]
        | eapply Lemmas.lapply3; [ charge_assumption | | | ]
        | eapply Lemmas.lapply4; [ charge_assumption | | | | ]
        | eapply Lemmas.lapply5; [ charge_assumption | | | | | ] ].

Ltac ends_with H ABC C :=
  let rec go k ABC :=
      match ABC with
      | C => k
      | _ -->> ?BC =>
        let k' := (k; first [ apply Lemmas.landAdj_true in H | apply landAdj in H ]) in
        go k' BC
      end
  in
  go ltac:(idtac) ABC.

Ltac charge_apply H :=
  match type of H with
  | _ |-- ?X =>
    match goal with
    | |- _ |-- ?Y =>
      ends_with H X Y ; etransitivity ; [ | eapply H ]
    end
  end.

Ltac charge_simple_split :=
  match goal with
  | |- _ |-- _ //\\ _ => charge_split
  end.

Ltac charge_left :=
  match goal with
  | |- _ |-- _ \\// _ => apply lorR1
  end.

Ltac charge_right :=
  match goal with
  | |- _ |-- _ \\// _ => apply lorR2
  end.

Ltac charge_tauto :=
  repeat charge_simple_split ;
  solve [ charge_assumption
        | charge_trivial
        | match goal with
          | H : _ |-- _ |- _ =>
            charge_apply H ; charge_tauto
          end
        | charge_intro; repeat charge_intro; charge_tauto
        | charge_left ; solve [ charge_tauto ]
        | charge_right ; solve [ charge_tauto ]
        | charge_split; solve [ charge_tauto ]
        | charge_use ; charge_tauto
        | charge_split ; solve [ charge_tauto ] ].


Ltac charge_fwd :=
  let rec search_it fin :=
    match goal with
    | |- ?A //\\ ?B |-- ?G =>
      first [ simple eapply (Lemmas.land_limpl_specializeR_ap _ _ B G); [ charge_tauto | search_it ltac:(idtac) ]
            | simple apply (Lemmas.land_lexistsR_ap _ _ G B) ; [ intro; search_it ltac:(idtac) ] ]
    | |- ?A //\\ _ //\\ ?B |-- ?G =>
      first [ simple apply (Lemmas.land_limpl_specialize_ap _ _ A B G); [ charge_tauto | search_it ltac:(idtac) ]
            | simple apply (Lemmas.land_lexists_ap _ _ A B G) ; [ intro; search_it ltac:(idtac) ]
            | simple apply (Lemmas.landA_ap A _ B G) ; search_it fin ]
    | |- ?A //\\ ?B |-- ?G =>
      first [ simple eapply (Lemmas.land_limpl_specializeL_ap _ _ A G); [ charge_tauto | search_it ltac:(idtac) ]
            | simple apply (Lemmas.land_lexistsL_ap _ _ G A) ; [ intro; search_it ltac:(idtac) ]
            | fin ]
    | |- _ => fin
    end
  in
  repeat rewrite landA ;
  search_it ltac:(idtac).
