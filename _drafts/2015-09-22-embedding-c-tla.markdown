---
layout: post
title: "Embedding C Programs in RTLA"
date: 2015-09-22
author: mmalvarez
categories: quadcopter floating-point
---

Our formalism, RTLA, is convenient for modeling the physical dynamics
in which our quadcopter controllers run. When we model systems in our formalism we use relations
between states. These are useful when modeling because they allow us to abstract
away the details of programming languages, but when we want to make an assertion
about a shim/monitor implemented in C, there is a gap between the logical model
and the executable code. In this blog post, we discuss a general technique
for embedding programs with standard programming-language style semantics into action formulas
(that is, RTLA formulas that can talk both about the state of the world "before" and "after"
some event occurs - the event, in this case, would be running the program).

*Point out that in TLA "x := 1" means "x gets 1 and everything else can change"; in
PL/semantics style it just means "x gets 1 and everything else stays the same".*
Thus, difficulty of implementing a "semicolon" operator in TLA

Later: "all evaluations of the program have this property" rather than just
"some evaluations have it"

Ideas
1. Logic vs. programs
2. Nontotality/crashing
3. Nondeterminism

<head>
    <!-- MathJAX import -->
    <script type="text/javascript"
            src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
    </script>
</head>

<!--
However, there is still a
gap: RTLA is a language that permits a high degree of nondeterminism.
Thus, writing our controllers in RTLA is not acceptable if we wish to
ascertain that the controller can in fact be run on a (deterministic)
computer. Additionally, the quadcopter platform on which our code will
be run computes with floating-point numbers, whereas infinite-precision
real arithmetic is native to RTLA. Thus, embedding C-like
(deterministic imperative) programs in RTLA - in a way that takes into
account the errors induced by floating-point computation - is important.
In this post I'm going to begin to describe how Gregory and I implemented this.
(In a later post we'll hopefully have time to go into detail on our
treatment of floating-point errors).
-->

### The Language

We're working with the following language:

{%highlight coq%}

    Inductive cmd :=
    | Seq (_ _ : cmd)
    | Skip
    | Asn (_ : nat) (_ : cexpr)
    | Ite (_ : cexpr) (_ _ : cmd)
    | Havoc (_ : nat)
    | Fail.

{%endhighlight%}

Here <tt>cexpr</tt> is a type describing arithmetic expressions; its
details are not so important here. Natural numbers are used to reference variables.
<tt>Havoc</tt> encodes a notion of nondeterministic choice: it sets the value of the
given variable to any number, nondeterministically.
The language has its semantics given by the following inductive relation:

{%highlight coq%}

    Inductive eval : state -> cmd -> state -> Prop :=
    | ESkip : forall s, eval s Skip s
    | ESeq : forall s s' s'' a b,
        eval s a s' ->
        eval s' b s'' ->
        eval s (Seq a b) s''
    | EAsn : forall s v e val,
        cexprD e s = Some val ->
        eval s (Asn v e) (update s v (Some val))
    | EIteTrue :
        forall s s' ex c1 c2,
        cexprD ex s = Some 0%R ->
        eval s c1 s' ->
        eval s (Ite ex c1 c2) s'
    | EIteFalse:
        forall s s' ex c1 c2 r,
        cexprD ex s = Some r ->
        r <> 0%R ->
        eval s c2 s' ->
        eval s (Ite ex c1 c2) s'
    | EHavoc : forall s v val,
        eval s (Havoc v) (update s v (Some val)).

{%endhighlight%}

(*TODO: say more about embedding functions and why we need them and stuff here*)

These embedding functions take a list of variable pairs
(describing how variables are mapped between TLA and our C-like imperative language), as well as
a data structure representing the program being embedded.
Below is our first attempt at defining embedding.

{%highlight coq%}
  Definition embedStep_ex (vars : list (Syntax.Var * Syntax.Var)) (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state post_state : state,
                      models vars pre init_state /\
                      eval init_state prg post_state /\
                      models vars post post_state)%type.
{%endhighlight%}

This approach is unrealistic as it supports "angelic non-determinism":
that is, if a program is able to step from state A to either
(nondeterministically) states B_good or B_bad (of which only B_good
satisfies the second "models" condition indicating that it matches
up with the post-state we expect to have), it is not considered a
problem that the program might also step to B_bad.

For deterministic languages this isn't so much of a problem, but since
RTLA is inherently nondeterministic it seemed right that we should support
embedding of nondeterministic languages as well. Our first attempt to
do so was the following:

{%highlight coq%}

  Definition embedStep (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      exists post_state : state,
                        eval init_state prg post_state /\
                        models post_vars post post_state)%type.

{%endhighlight%}

While this notion of embedding more realistically captures the "demonic"
non-determinism we need to support (i.e., "we can't step to a state that
does not meet spec" as opposed to "we can step to a state that does meet
spec"), it has other problems.
Namely, it does not treat crashing programs appropriately.
Under embedStep a crashing program can be proven to refine any
RTLA specification! If Fail is a program statement that cannot step
to anything in the "eval" relation, then the expression
embed_cmd' Fail is essentially equivalent to False, since it posits the
existence of a state, post_state, such that
eval init_state False post_state. But this is impossible by definition of
Fail, which cannot be stepped through.
This shows us that we have another design constraint that was perhaps not
obvious at the beginning: to not allow programs that crash to be
considered refinements of RTLA specifications describing valid programs.

To solve both of these problems we introduced a third variant, avoiding
the existentials that caused problems for programs that crash:

{%highlight coq%}

  Definition embedStep_noex (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast)
  : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    forall init_state : state,
                      models pre_vars pre init_state ->
                      forall post_state : state,
                        eval init_state prg post_state ->
                        models post_vars post post_state).

{%endhighlight%}

This version deals with failure properly, but it runs into problems with
nondeterminism.  (*TODO: finish that thought*)

At this point we realized that getting this definition right was going
to be a tougher problem than we'd originally anticipated. So, we put on
our thinking caps and, after a while, came up with the following definition,
able to handle both crashing and nondeterminism...

{%highlight coq%}

  Definition embedStep_maybenot (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      models pre_vars pre init_state /\
                      (~(exists post_state : state, eval init_state prg post_state) \/
                        (exists post_state : state, eval init_state prg post_state /\
                        models post_vars post post_state)))%type.

{%endhighlight%}

...well, almost, that is. It turns out that while this definition is able to
correctly handle programs that exhibit *either* crashing or nondetermninistic
behavior, it is unable to properly treat programs that exhibit *both*. First
though, notice that this definition is quite similar to embedStep_noex: the only
difference is the addition of the ~(exists post_state...) clause, to allow for
proper treatment of the case where programs crash (cannot take a step).

The following program, which crashes (or does not crash) based on a
nondeterministic choice:

{%highlight coq%}
    Havoc a; If (a == 0) then Fail else Skip
{%endhighlight%}

can be proven to refine TLA specifications corresponding to deterministic programs,
such as

{%highlight coq%}
    "a"! = "a"
{%endhighlight%}

(This specification asserts that the value of variable a in the next state
- after running the program - will equal the value before running the
program. This is true in the Skip case but not the Fail case.)

We consider this to be incorrect behavior, since the specification does not
capture the fact that the program has a possibility of crashing, and yet a
program that may (nondeterministically) crash can be proven to refine
this specification.

After a few more abortive attempts to rephrase embedding in a way that captured
all the behaviors we wanted, we realized we'd need to make some changes to our
evaluation relation if we wanted to have all the features we need
(correct behavior in the face of nondeterminism, failure, and
nondeterministic failure). In particular, we realized that the
evaluation relation specifying our language's semantics would have
to distinguish between "crashing" and "getting stuck".

(*TODO: give oeval inductive definition here*)

{%highlight coq%}
    Inductive oeval : state -> cmd -> option state -> Prop :=
    | OESkip : forall s, oeval s Skip (Some s)
    | OESeqS : forall s s' os'' a b,
        oeval s a (Some s') ->
        oeval s' b os'' ->
        oeval s (Seq a b) os''
    | OESeqN : forall s a b,
        oeval s a None ->
        oeval s (Seq a b) None
    | OEAsnS : forall s v e val,
        cexprD e s = Some val ->
        oeval s (Asn v e) (Some (update s v (Some val)))
    | OEAsnN : forall s v e,
        cexprD e s = None ->
        oeval s (Asn v e) None
    | OEIteT :
        forall s os' ex c1 c2,
        cexprD ex s = Some 0%R ->
        oeval s c1 os' ->
        oeval s (Ite ex c1 c2) os'
    | OEIteF:
        forall s os' ex c1 c2 r,
        cexprD ex s = Some r ->
        r <> 0%R ->
        oeval s c2 os' ->
        oeval s (Ite ex c1 c2) os'
    | OEIteN :
        forall s ex c1 c2,
        cexprD ex s = None ->
        oeval s (Ite ex c1 c2) None
    | OEHavoc : forall s v val,
        oeval s (Havoc v) (Some (update s v (Some val)))
    | OEFail : forall s, oeval s Fail None
    .
{%endhighlight%}

With this new semantics, we're almost there! We can once again try
a slightly modified version of embedStep_maybenot:

{%highlight coq%}
  Definition oembedStep_maybe (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      omodels pre_vars pre init_state /\
                      (~(exists post_state : state, eval init_state prg (Some post_state)) \/
                       (exists post_state : state, eval init_state prg (Some post_state) /\
                                                   omodels post_vars post post_state)))%type.
{%endhighlight%}

This doesn't quite work, however. We need our
definition to explicitly take advantage of the fact that the
post-state will be None in the case of a program crash. This brings
us to our final iteration of the embedding function:

{%highlight coq%}
  Definition oembedStep_maybenone (pre_vars post_vars : list (Syntax.Var * var))
             (prg : ast) : Syntax.Formula :=
    Syntax.Embed (fun pre post =>
                    exists init_state : state,
                      omodels pre_vars pre init_state /\
                      ((eval init_state prg None) \/
                       (exists post_state : state, eval init_state prg (Some post_state) /\
                                                   omodels post_vars post post_state)))%type.
{%endhighlight%}

Finally, we have a definition of embedding that allows us to prove refinements
that are actually valid, while not allowing us to prove refinements of
pathological programs (i.e., those that crash and/or exhibit nondeterminism)
from RTLA specifications that do not.

(*TODO: say more about why differentiating between crashing an "getting stuck"
makes a difference in the context of combining failure and nondeterminism*)

In a context like RTLA, the distinction between programs that crash and those that
"get stuck" is important. Programs that crash are allowed to disregard
their post-state (essentially, allowing complete nondeterminism after the fact).
Programs that "get stuck" in the sense of not being able to take a step of evaluation,
on the other hand, exhibit nondeterminism in both states. (I THINK)

In conclusion, defining notions like the embedding of an imperative
program into RTLA is surprisingly subtle, the subtlety mostly arising
from the nondeterministic nature of RTLA. The need to correctly
distinguish between different notions of "going wrong" - for instance,
the program crashing (stepping to None) versus the program entering
a nondeterministic state where "anything might happen" - was another challenge.
Hopefully this post gives a flavor for the kinds of subtleties and challenges
that can arise when doing semantics. (*need a better conclusion*)

Next time we'll talk about how to take the semantics for this C-like language
and use it to build the predicate transformers that will allow us to reason
about floating-point errors!
