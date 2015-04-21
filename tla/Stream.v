(* A behavior of TLA is an infinite stream
   of states. *)
CoInductive stream (A:Type) :=
| Cons : A -> stream A -> stream A.

Arguments Stream.Cons {_} _ _.

(* The head of a stream *)
Definition hd {A} (s:stream A) : A :=
  match s with
    | Cons a _ => a
  end.

(* The tail of a stream *)
Definition tl {A} (s:stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.

(* The nth suffix of a stream *)
Fixpoint nth_suf {A} (n:nat) (s:stream A) : stream A :=
  match n with
    | O => s
    | S n => nth_suf n (tl s)
  end.

Lemma nth_suf_tl : forall A n (s:stream A),
  nth_suf n (tl s) =
  tl (nth_suf n s).
Proof.
  intros A n; induction n; intro s;
  firstorder.
Qed.

Lemma nth_suf_Sn : forall A n (s:Stream.stream A),
  Stream.nth_suf (S n) s =
  Stream.tl (Stream.nth_suf n s).
Proof.
  intros A n; induction n; intro s;
  firstorder.
Qed.
