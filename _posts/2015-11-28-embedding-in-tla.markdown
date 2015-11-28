---
layout: post
title: "Embedding Imperative Programs in LTL"
date: 2015-11-28
author: mmalvarez
categories: quadcopter semantics floating-point
---

In this post I'll describe how we embed certain classes of imperative
programs into LTL, the logic we use to model quadcopter behavior.
Doing so is key to being able to reason about how concrete quadcopter-controller
implementations will behave in the context of the copter's physical dynamics.

### Introduction - The Problem

Our VeriDrone model of hybrid systems is built on linear temporal logic (LTL).
In LTL, we express valid transitions of the system using relations between a
pre-state (before the transition occurs) and a post-state
(after the transition occurs).
This description of transitions is very expressive; for example, it allows us
to state interesting transitions such as evolution of the system by
differential equations without extending our formalism.
However, this power also introduces a mismatch between the expressiveness of the
model and the actual software that controls the system: there are many logical
expressions in LTL that don't obviously correspond to valid programs, and
we must also account for the difference between the floating-point computations
done in the controller software and the physical behavior of the drone,
which is modeled in real numbers.
In this post, we will discuss how we address this mismatch by demonstrating a
general technique for embedding programs (expressed using standard
programming-language techniques) in LTL formulas.

### Our Language

In our case, we're interested in a simple imperative language. It can
be thought of as a small subset of C, without function-calls, pointers,
or loops: we can manipulate floating-point values, assign them to variables,
and branch on their values. The exclusion of loops and recursion is
crucial: the floating-point analysis techniques we use here
to understand the errors induced by the programs' floating-point computation
cannot be easily applied to loops (doing so naively would produce
infinitely large error estimates, which is unhelpful.)

#### Syntax

We define the syntax of the programming language as the following type:

{%highlight coq%}
Inductive cmd :=
| Seq : cmd -> cmd -> cmd
| Skip : cmd
| Asn : string -> cexpr -> cmd
| Ite : cexpr -> cmd -> cmd -> cmd
{%endhighlight%}

Here, ```Seq``` is sequencing operator ("semicolon"); ```Skip``` is an
operation with no effect ("no-op"); ```Asn``` assigns a value to a variable
(where the variable is referenced by a ```string``` name).
```Ite``` implements a particular type of branching ("if-then-else")
behavior: if the given expression evaluates to a value less than zero, the
first of the two given commands is run; otherwise the second is run.

```cexpr``` is a simple expression language
with floating-point variables and constants, as well as floating-point addition,
subtraction, and multiplication.

{%highlight coq%}
Inductive cexpr :=
| Var : string -> cexpr
| Const : float -> cexpr
| Plus : cexpr -> cexpr -> cexpr
| Minus : cexpr -> cexpr -> cexpr
| Mult : cexpr -> cexpr -> cexpr.
{%endhighlight%}


The function ```cexprD``` (the "denotation function") runs an expression
and returns the result. That is to say, we give a
*denotational semantics* for our expression language. We omit the definition of
```cexprD``` for brevity, but here its type:

{%highlight coq%}
cexprD : cexpr -> option float
{%endhighlight%}

```cexprD``` returns ```None``` if evaluating the expression "crashes".
In the language described here, this can only happen in the case
of attempting to look up an undefined variable.

#### Program State

Shortly, we'll define the semantics of programs (inhabitants of the ```cmd```
type). To do so, however, we must first formalize a model of program state.
For simplicity, we work in a language where all variables have the
same type. Because we care about modeling the real-time computations
performed by VeriDrone's controller, the variables are all floating-point
numbers (we build on top of the [Flocq](http://flocq.gforge.inria.fr/)
formalization of floating-point numbers); specifically, the model of
IEEE-754 double-precision floating-point contained therein.


Programs have finite state (in the sense of having finitely many variables),
so we use an association list:

{%highlight coq%}
Definition fstate := list (string * float).
{%endhighlight%}

This definition is relatively easy to reason about on its own; however, the
representation is not canonical.
This lack of canonicity means that we need to define our own
notion of what it means for ```fstate```s to be *semantically* equal.
For example the following two ```fstate```s are semantically equal,
but not syntactically equal (Coq's default definition):
```[("a",1.0);("b",2.0)]``` and ```[("b",2.0);("a",1.0)]```.

The equivalence we care about is:

{%highlight coq%}
Definition states_iso (st st' : istate) : Prop :=
  forall (s : string),
    match (fm_lookup st s), (fm_lookup st' s) with
    | None, None => True
    | Some f1, Some f2 => pl_equ f1 f2
    | _, _ => False
    end.
{%endhighlight%}

That is, two states ```st``` and ```st'``` are equivalent in the necessary
sense if (and only if), for each variable, either

- Looking up the variable in both states fails, or
- Looking up the variable in both states succeeds, and the values read
are equal as PL variables.

In order to embed a language, we need to show (among other things)
that this notion of equality is respected by that particular
programming-language semantics.

The type of states used in the implementation of LTL that VeriDrone runs on
is somewhat different from the imperative language's ```fstate```. Here it is:

{%highlight coq%}
Definition state := (string -> R).
{%endhighlight%}

This is not a finite map, since all states must assign values to all
variables. In practice, we only care about a subset of the variables;
the rest are essentially populated with default, dummy values. A result
of this type mismatch is that many functions and theorems need to
carry around a ```list``` of ```string```s describing what variables
are considered relevant to the program at hand.

#### Semantics

To embed programs in LTL, we need a semantics for the language
we're embedding. In this case we follow the standard approach of giving
the language a *big-step operational semantics*
in terms of an inductively-defined relation that describes the transitions
of entire programs in terms of their starting and ending states.
(Note that, because the semantics is total and deterministic.
we could have just given it as a function. However, leaving it as a relation
makes it easier to extend the system to nondeterministic or nontotal programs,
though doing so in our case is future work.)

We encode the semantics of our language as an inductive relation over
```(fstate, cmd, fstate)``` triples.
```evals st p st'``` states that when the program ```p``` is run
from the state ```st``` it will terminate in the state ```st'```.

Formally, here is the semantics for our command language. This is a relatively
standard semantics, which I've already described at a high level above, so I
won't go into further detail here. One noteworthy thing about this semantics
is that it can "crash" if the evaluation of an expression fails
(```cexprD``` returns ```None```). Crashing is represented by a
lack of transition in the ```eval``` relation.

{%highlight coq%}
Inductive eval : fstate -> cmd -> fstate -> Prop :=
| ESkip : forall s, eval s Skip s
| ESeq : forall s s' s'' a b,
  eval s a s' ->
  eval s' b s'' ->
  eval s (Seq a b) s''
| EAsn : forall s v e val,
  cexprD e s = Some val ->
  eval s (Asn v e) (update s v val)
| EIteTrue :
  forall s s' ex c1 c2,
    cexprD ex s = Some f ->
    f < fzero ->
    eval s c1 s' ->
    eval s (Ite ex c1 c2) s'
| EIteFalse:
  forall s s' ex c1 c2 r,
    cexprD ex s = Some f ->
    f >= fzero ->
    eval s c2 s' ->
    eval s (Ite ex c1 c2) s'
{%endhighlight%}

(```fzero``` is shorthand for the floating-point constant 0, whose full name
is annoying to type out in Coq. ```<``` and ```gt``` are used to abbreviate
floating-point comparison functions.)

### Embedding

Embedding our simple language inside of LTL requires us to turn a
program - expressed as a syntactic object, with semantics provided by
an inductive relation, as above - into a formula describing the
*entire execution of the program* as a single state-transition; that is,
essentially, a predicate over ```(s1 : state, s2 : state)``` pairs, which is
satisfied for a given program ```p``` if and only if ```eval s1 p s2```
is satisfied.

We use the following module to build embeddings:

Embeddings will have (essentially) the following data type:

{%highlight coq%}
embedding : Type := list string -> ast -> LTL.Formula
{%endhighlight%}

The first argument is a list of variables to consider when embedding the
program, needed for the technical reason mentioned above. The second
argument is the program itself.
I call the type of programs ```ast``` rather than ```cmd``` here,
to emphasize the fact that we seek to be parametric in the
particular syntax and semantics that the program is expressed in
(recall that the goal is a general solution, not a solution tailored to a
particular language or semantics). In practice this means that we can't
ever do an explicit pattern-match on the constructors of ```ast```.

However, there are some wrinkles: first, as mentioned, LTL expresses
its states as functions (```string -> R```) giving a value to every variable;
our imperative language uses a finite map that only gives values to variables
used in the program; we deal with this by passing around variable-lists
as described above.

Second, and more importantly, our implementation of LTL is a logic over
real numbers, in order to make it easier to reason about the physical
behaviors of our system. Thus we'll need to make a formal connection
between the floating-point computations of our langauge and the
real-valued computations expressed in the logic. The gory details of
this connection are beyond the scope of this post, but I'll
touch on this topic again a bit later on.

#### Correctness of Embedding

What does it mean for our definition of embedding to be correct?
Obviously there are many functions that satisfy the ```embedding```
type above. In order to express what we mean by a *correct* embedding
function, we first need to define a predicate relating floating-point
program states to real-valued LTL states. Doing so will allow us to
make a formal connection between evaluations of concrete programs
and the evaluation of LTL logical formulas.

{%highlight coq%}
Definition models (vars : list string) (ist : istate) (sst : lstate) : Prop :=
  forall (s : string),
    (In s vars ->
    exists (d : pl_data),
      fm_lookup ist s = Some d /\
      asReal d (sst s)) /\
   (~In s vars -> fm_lookup ist s = None).
{%endhighlight%}

In our case, ```pl_data``` is an alias for the type of floating-point numbers
(```float```); ```asReal f r``` expresses the fact that, when the
value ```f``` is converted to a real number, the conversion succeeds
(in our case, this means that the floating-point value
retrieved was not Inf or NaN, so-called "exceptional values"
in floating-point), and yields the number ```r```.

```istate``` - "implementation state" - and ```ls``` - "logical state",
are respectively ```fstate``` and ```state``` in our case.
```fm_lookup``` simply looks up a variable in an
```istate```, returning ```None``` if the lookup fails.

Informally, this definition of ```models``` imposes
the following requirement on all variables:

1. For each variable ```v``` that we care about
(i.e., variables in the list ```vars```) the variable should
be present in ```ist```, and the result of looking up that
variable should be a real number ```d``` that equals the result
of looking up the same variable ```v``` in the real-valued state.
That is, the floating-point and real-valued states
should "agree" on these variables.
2. For all other variables, we require that they not be present
in the state ```ist``` (looking them up in the state should fail).

Armed with this definition, we can express the correctness property that
we want to hold over our candidate function for embedding programs into
LTL. What we'd like to have is, essentially, the following
diagram "commute", in that the result of taking the two paths
shown (labeled "Path 1" and "Path 2") should be the same.

<div><img src="{{ site.base_url }}/veridrone/images/EmbeddingCorrectness.svg" alt="Correctness Diagram" style="height: 450px;"/></div>

Informally, suppose we have a program ```p``` and we know that
```eval fs1 p fs2```. Then the embedding of ```p```
(informally, ```embed p```, omitting the variable-list argument
for brevity) should be able to take a step from ```rs1``` to
```rs2``` (according to LTL evaluation semantics, written as
```eval_formula``` in the diagram), where ```rs1``` is a real-valued
LTL state modeling the floating-point state ```fs1```
according to the ```models``` relation; and likewise for
```rs2``` and ```fs2```.

Writing this out formally gives us:

{%highlight coq%}
Definition embedding_correct1 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is is' : istate) (ls ls' : LTL.state) (tr : stream LTL.state),
      models v is ls ->
      models v is' ls' ->
      eval is prg is' ->
      LTL.eval_formula
        (embed v prg)
        (ls :: ls' :: tr)
{%endhighlight%}

It's worth noting here that some of the primitives (```LTL.*``` in particular)
have slightly different names in our Coq development; I've renamed them
here for clarity. ```stream``` is an infinite (co-inductive) list;
```LTL.eval_formula``` uses this type in order to be able to express
temporal properties about potentially infinite runs of systems.

We also want to make sure that crashing behavior is preserved:
if the source program crashed (i.e., can't take a step),
its corresponding LTL formula should not be able to take a step.
(We say that the LTL formula is not "enabled", to borrow a term
often used in the TLA variant of LTL).

Written out formally, we have:

{%highlight coq%}
  Definition embedding_correct2 (embed : embedding) : Prop :=
    forall (v : list string) (prg : ast) (is : istate) (ls : LTL.state) (tr : stream LTL.state),
      models v is ls ->
      ~(exists is', eval is prg is') ->
      ~(LTL.eval_formula
        (Enabled (embed v prg))
        (ls :: tr)).
{%endhighlight%}

A correct embedding function must meet *both* of these conditions.

#### Our Embedding Function

We use the following embedding function, which we've proven correct
(in the sense of proving that it meets both of the correctness
conditions spelled out above). For details of the proof, the interested
reader can consult the following
[excerpt from our Coq development](https://gist.github.com/mmalvarez/d3c87466a3cff104dddb#file-embed-v-L225)
(the full development is not yet publicly available).

{%highlight coq%}
  Definition embed_ex (v : list string) (prg : ast) : Formula :=
  LTL.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).
{%endhighlight%}

Here we use the ```LTL.Embed``` construct to
embed a step-predicate expressed in Coq's logic (that is, of type
```TLA.state -> TLA.state -> Prop```). In this case, we embed a
formula that requires the existence of appropriate "concrete states"
or "implementation states" (which have type ```istate``` in general;
or ```fstate``` in our case), such that the first one models the
initial TLA state, the second models the second, and the program
steps from the initial to the final concrete state according to the
evaluation semantics for the language.

However, it is worth noting that this definition of embedding is only correct
if the evaluation relation giving semantics to the embedded programming
language is deterministic (i.e., the language is a deterministic language).
The problem becomes more complicated in the face of nondeterminism:
consider, for instance, a program that nondeterministically fails.
It is less obvious how to construct an embedding function that will
preserve this behavior in LTL. The implementation given above would simply
throw away failures/"crashes" and
only preserve successful runs, but in practice we care greatly about
cases where the system crashes (because we must prevent them).
Since we do not need to support writing quadcopter controllers in
a nondeterministic source language, the definition given here suffices.

### Floating-Point Reasoning

Of course, there's still one missing piece here: making a formal connection
between the real-valued arithmetic used in our LTL model and the
floating-point arithmetic that controller programs (```cmd```s) run on.
We use a sound, interval-based overapproximation to safely capture
floating-point error. However, that's a story for another day.
The interested reader can consult the
[implementation](https://gist.github.com/mmalvarez/9f6efaae22aa07674251).

### Source

The full source code for this project isn't yet available, but I've created
two Gists that contain files relevant to this post.

- [Embed.v](https://gist.github.com/mmalvarez/d3c87466a3cff104dddb)
has general definitions related to embedding.
- [FloatEmbed.v](https://gist.github.com/mmalvarez/9f6efaae22aa07674251)
implements the Embed abstraction for our floating-point language

### Acknowledgements

I'd like to acknowledge Gregory Malecha, with whom I worked on this project,
and who helped to refine this blog post, and Sorin Lerner, my advisor.
