---
layout: post
title: "Embedding Imperative Programs in LTL"
date: 2015-11-16
author: mmalvarez
categories: quadcopter semantics floating-point
---

<!--
<head>
    <!-- MathJAX import -->
    <script type="text/javascript"
            src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
    </script>
    </head>
-->

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
the difference between the floating-point computations done in software and
the physical behavior of the drone, which is modeled in real numbers.
In this post, we will discuss how we address this mismatch by demonstrating a
general technique for embedding programs (expressed using standard
programming-language techniques) in LTL formulas.

### Our Language

In our case, we're interested in a simple imperative language. It can
be thought of as being "morally" a subset of C, without function-calls
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
| Seq (_ _ : cmd)
| Skip
| Asn (_ : nat) (_ : cexpr)
| Ite (_ : cexpr) (_ _ : cmd).
{%endhighlight%}

Here, ```Seq``` is sequencing operator ("semicolon"); ```Skip``` is an
operation with no effect ("no-op"); ```Asn``` assigns a value to a variable.
```Ite``` implements a particular type of branching ("if-then-else")
behavior: if the given expression evaluates to a value less than zero, the
first of the two given commands is run; otherwise the second is.

```cexpr``` is a simple expression language
with floating-point variables and constants, as well as floating-point addition,
subtraction, and multiplication.
The function ```cexprD``` (the "denotation function") runs an expression
and returns the result. That is to say, we give a
*denotational semantics* for our expression language. We omit the definition of
```cexprD``` for brevity, but here is ```cexpr```:

{%highlight coq%}
Inductive cexpr :=
| Var : Var -> fexpr
| Const : source.float -> fexpr
| Plus : fexpr -> fexpr -> fexpr
| Minus : fexpr -> fexpr -> fexpr
| Mult : fexpr -> fexpr -> fexpr.
{%endhighlight%}

It is worth pointing out ```cexprD```'s type:

{%highlight coq%}
cexprD : cexpr -> option R
{%endhighlight%}

```cexprD``` will return ```None``` if evaluating the expression "crashes".
In the language described here, this can only happen in the case
of attempting to look up a variable which has not been assigned.

#### Program State

Shortly, we'll define the semantics of programs (inhabitants of the ```cmd```
type). To do so, however, we must first formalize a model of program state.
First, for simplicity, we work in a language where all variables have the
same type. Because we care about modeling the real-time computations
performed by VeriDrone's controller, the variables are all floating-point
numbers (we build on top of the Flocq formalization of floating-point numbers).


Programs have finite state (in the sense of having finitely many variables),
so we use an association list:

{%highlight coq%}
Definition fstate := list (string * float)
{%endhighlight%}

This definition is relatively easy to reason about on its own, albeit with
the caveat that we must be careful when comparing them for equality:
```[("a",1.0);("b",2.0)] <> [("b",2.0);("a",1.0)]```, but the two are
*semantically* equal when considered as program states. We use our own
equality relation for program states instead of Coq's native equality.

The type of states used in the implementation of LTL that VeriDrone runs on
is somewhat different. Here it is:

{%highlight coq%}
Definition state := (string -> R)
{%endhighlight%}

This is not a finite map, since all states must assign values to all
variables. In practice, we only care about a subset of the variables;
the rest are essentially populated with default, dummy values. A result
of this type mismatch is that many functions and theorems need to
carry around a ```list``` of ```string```s describing what variables
are considered relevant to the program at hand.

The precise details of solution to this mismatch are not so interesting;
the curious reader can refer to the project source code.

#### Semantics

To embed programs in LTL, we need a semantics for the language
we're embedding. In this case we follow the standard approach of giving
the language a *big-step operational semantics*
in terms of an inductively-defined relation that describes the transitions
of entire programs in terms of their starting an ending states.
(Note that, because the semantics is total and deterministic,
we could have just given it as a function. However, leaving it as a relation
makes it easier to extend the system to nondeterministic or nontotal programs,
though doing so in our case is future work.)

We encode the semantics of our language as an inductive relation over
```(fstate, cexpr, fstate)``` tuples.
Intuitively, ```evals st p st'``` states that when the program ```p``` is run
from the state ```st``` it will terminate in the state ```st'```.

Formally, here is the semantics for our command language. This is a relatively
standard semantics, which I've already described at a high level above, so I
won't go into further detail here. One noteworthy thing about this semantics
is that it can "crash" if the evaluation of an expression fails
(```cexprD``` returns ```None```).

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
is annoying to type out in Coq)

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
We use the type ```ast``` rather than ```cmd``` because
we seek to be parametric in the particular syntax and semantics
(recall that the goal is a general solution, not a solution tailored to a
particular language or semantics).

However, there are some additional wrinkles: first, LTL expresses
its states as functions (```state -> R```) giving a value to every variable;
our imperative language uses a finite map that only gives values to variables
used in the program.

Second, and more importantly, our implementation of LTL is a logic over
real numbers, in order to make it easier to reason about the physical
behaviors of our system. Thus we'll need to make a formal connection
between the floating-point computations our our langauge and the
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
  Definition models (vars : list string) (ist : istate) (sst : Syntax.state) : Prop :=
    forall (s : string),
      (In s vars ->
      exists (d : pl_data),
        fm_lookup ist s = Some d /\
        asReal d (sst s)) /\
      (~In s vars -> fm_lookup ist s = None).
{%endhighlight%}

In our case, ```pl_data``` is simply an alias for the type of real numbers
(```R```); ```asReal f r``` expresses the fact that, when the floating-point
value ```f``` is converted to a real number, the conversion succeeds
(in particular, the value retrieved was not Inf or NaN, so-called
"exceptional value" in floating-point), and yields the number ```r```.

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

<div><img src="/veridrone/images/EmbeddingCorrectness.svg" alt="Correctness Diagram" style="height: 450px;"/></div>

Informally, suppose we have a program ```p``` and we know that
```eval fs1 p fs2```. Then the embedding of ```p```
(informally, ```embed p```, omitting the variable-list argument
for brevity) should be able to take a step from ```rs1``` to
```rs2``` (according to LTL evaluation semantics, written as
```eval_formula``` i the diagram), where ```rs1``` is a real-valued
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

It's worth noting here that some of the primitives (LTL.* in particular)
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
      ~(Semantics.eval_formula
        (Enabled (embed v prg))
        (ls :: tr)).
{%endhighlight%}

(We use ```is``` - "implementation state" - and ```ls``` - "logical state" -
here, as these are better names for the arguments in the general case)

A correct embedding function must meet *both* of these conditions.

#### Our Embedding Function

We use the following embedding function, which we've proven correct
(in the sense of proving that it meets both of the correctness
conditions spelled out above). For details of the proof, the interested
reader can consult our Coq development.

{%highlight coq%}
  Definition embed_ex (v : list string) (prg : ast) : Formula :=
  TLA.Embed (fun lpre lpost =>
                    exists cpre cpost,
                      models v cpre lpre /\
                      models v cpost lpost /\
                      eval cpre prg cpost).
{%endhighlight%}

This definition is relatively simple: we use the "TLA.Embed" construct to
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
language is deterministic (i.e., the language is deterministic). The problem
becomes much more complicated in the face of nondeterminism, due in part
to the limitations of the expressiveness of LTL. Consider, for instance,
a program that nondeterministically fails. It is far from obvious how to
construct an embedding function that will preserve this behavior in LTL.
The implementation given above would simply throw away failures/"crashes" and
only preserve successful runs, but in practice we care greatly about
cases where the system crashes (because we must prevent them).

### Floating-Point Reasoning

(I don't really like this section, as it doesn't really have concrete
examples. Other people have probably written better introductions
to range analysis anyway... Do you think I should remove this?)

As mentioned above, there's one major remaining obstacle to tackle before
we can soundly embed floating-point programs in real-valued LTL: we need
to account for the errors induced by the program's floating-point
computation.

More importantly, however, we have the formal gap between floating-point numbers
and real numbers, as alluded to above. Our technique for addressing this gap
is based on a fairly standard floating-point range analysis, with the twist
that the entire analysis is foundationally verified, build on the Flocq
formal floating-point semantics. A full description of how our range-analysis
works is beyond the scope of this blog post, but here is a brief overview.

- On top of Flocq, one of my colleagues has implemented primitives for
interval-based reasoning over floating-point numbers. For each floating-point
function (let's take ```a + b``` as an example), the system takes a
specification of the possible values ```a``` can take on as well as a
specification of the possible values ```b``` can take on; it outputs
a specification of the possible values output by the expression ```a + b```.

- Because we're doing a range-based analysis, the "specifications of possible
values" mentioned above will be either a (closed) interval or union of
intervals over the real numbers. The output of these functions will
likewise be an interval or union of intervals.

#### Analyzing Floating-Point Programs

- Using this range analysis, we build a
predicate-transformer semantics, that allows us to find safe input
ranges for our function. The semantics uses the result of the range
calculations described above in order to relate predicates on the
program output (post-state) to input (pre-state).

[Maybe describe/show examples of the Hoare semantics]

- Armed with this semantics we build (and prove correct) a weakest-
precondition function over programs in the ```cmd``` language
described above.

- We use this predicate-transformer semantics to reason about programs
embedded in LTL as described above. By

- In this way, given a predicate on the program's output (which,
in this case, can be thought of as a specification of desired
program behavior), we can determine the input constraints
necessary to realize this behavior.

- In particular, we can rule out the presence of exceptional
(infinity or not-a-number) floating-point values, which do not have
a natural translation into the reals. Being able to eliminate these
cases simplifies our embedding, which would become more complicated
if it had to deal with such values.

### Putting It All Together

We combine all of this into a Coq module for abstraction and ease of reuse.
The file compile/FloatEmbed.v is a good example of how to instantiate the
general embedding module type (defined in Embed.v).

[TODO say more here]

### Acknowledgements

I'd like to acknowledge Gregory Malecha, with whom I worked with on this project,
and who helped to refine my blog posts, as well as Vignesh Gowda, who implemented
the lower-level floating-point range analysis that this work built on top of; and
Sorin Lerner, my advisor.
