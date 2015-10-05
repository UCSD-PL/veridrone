---
layout: post
title: "Embedding C Programs in RLTL, Part 1: Embedding Real-Valued Semantics"
date: 2015-09-29
author: mmalvarez
categories: quadcopter floating-point semantics
---

<head>
    <!-- MathJAX import -->
    <script type="text/javascript"
            src="http://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
    </script>
</head>

### Introduction - The Problem

> Our VeriDrone model of hybrid systems is built on linear temporal logic (LTL).
In LTL, we express valid transitions of the system using relations between a pre-state (before the transition occurs) and a post-state (after the transition occurs).
> This description of transitions is very expressive; for example, it allows us to state interesting transitions such as evolution of the system by differential equations without extending our formalism.
> However, this power also introduces a mismatch between the expressivity of the model and the actual software that controls the system.
> In this post, we will discuss how we address this mismatch by demonstrating a general technique for embedding programs (expressed using standard programming-language techniques) in LTL formalas.
> While the problem may seem trivial, there are several interesting caveats that arise when the language includes non-determinism (e.g. ```rand()```) and unrecoverable errors (e.g. segmentaion faults).

> Maybe cut this paragraph into two pieces? One more motivation and the other more "what is our logic". The problem is that the two problems are intricately linked since the problem is "overcoming the semantic mismatch between two formalisms"

In order to reason about quadcopters as a hybrid system, we need to be able to reason about the controller code in the context of the system's physical dynamics.
That is to say, we need to be able to combine our source program that will run on the quadcopter and its semantics with the physical semantics of the quadcopter.
This is the first of three blog posts on our infrastructure for embedding controller programs (written in a C-like language) into our logic for hybrid systems.
Part two will focus on supporting additional language features (failure and nondeterminism) and part three will deal with the challenges that arise in supporting languages with floating-point number semantics.
For now, however, we focus on real-valued, deterministic, total programs that can neither crash nor "get stuck".

### Our Logic

> I'm not convinced that this is necessary. In particular, the discussion of always isn't important because we don't really need trace formulae, just action formulae.

We use a Temporal Logic of Actions (TLA)-inspired variant of Linear Temporal Logic (LTL).
For the purposes of this post I'll refer to this logic as RLTL, so called because it
is "real-valued": the only types of values we're allowed to talk about in RLTL are
real numbers. We have access to all the standard arithmetic and comparison operators
on real numbers, as well as the standard logical connectives. So if we want to
specify that, in the current state of the world, variable \\(x\\) is equal to 5 and
\\(y\\) is less than 3, we could say

$$x = 5 \land y \le 3$$

We would call this formula a "state formula", since it refers only to a single
state of the world. We can also talk about the values of variables in both
the current state and the next state, producing "step formulas" like the following,
stating that variable \\(x\\) is 5 in the current state and unchanged in the
following state:

$$x = 5 \land x' = x$$

We also have access to temporal modalities. Currently the one most useful to us is
the "always" modality, stating that a formula holds currently and will hold at
all points in the future. "Always" is useful for expressing safety properties of
the kind we care about. For instance, if \\(h\\) is the quadcopter's height, then
we can write the formula

$$ \square (h \le 100) $$

to express the statement that the copter's height does not exceed 100 units
at any point in the future.
An important thing to note about RLTL is that RLTL statements make no
assertions about variables they do not mention. So if we say
\\(x = 5 \land y' \le 3\\) the value of \\(x\\) in the next state
and \\(y\\) in the current state are unspecified. Reading these logical
formulas as programs, we can think of these unspecified variables as a
kind of nondeterministic choice. (On its own, \\(y' \le 3\\) would already
be a nondeterministic choice since it does not completely specify
the value of \\(y'\\)).

Here we see a crucial gap between RLTL and conventional programming
languages: "programming" in RLTL is a bit like programming on a
system that's trying to sabotage you while you aren't looking.
It dutifully sets all the variables you tell it to set, but if you
forget to mention a variable all bets are off. As we'll see
in this blog post and the next one, this fundamental mismatch
creates some tricky corner-cases for embedding.

### Our Imperative Language Semantics (Version 1)

> Embedding a Total, Deterministic Language

> Let's begin by looking at a total, deterministic language.
> We define the syntax of the programming language as the following inductive type.

To embed programs in RLTL, we first need a semantics for the language
we're embedding. In this case we follow the standard approach of giving
the language an *operational semantics* in terms of an inductively-defined
relation that describes how the programming language transitions between
states. (Note that, because the semantics is total and deterministic,
we could have just given it as a function. I leave it as a relation
since we will need the generality of a relation to support the
features introduced in the next blog post).

Here's the data structure defining the syntactic constructs of
the language we are going to embed into RLTL:

{%highlight coq%}
Inductive cmd :=
| Seq (_ _ : cmd)
| Skip
| Asn (_ : nat) (_ : cexpr)
| Ite (_ : cexpr) (_ _ : cmd).
{%endhighlight%}

> Next, we need to describe the semantics, i.e. the meaning, of each construct.
> For this simple definition, we will give a big-step operational semantics defined inductively.
> First, a state of the programming language is an assignment of variables to values.
> We will use an association list to make precise the fact that the state of the program is finite.
> Next , ..
> Intuitively, ```evals st p st'``` states that when the program ```p``` is run from the state ```st``` it will terminate in the state ```st'```.
> (just a note about ```cexpr```, I don't think that we need to show the code).

<tt>Seq</tt> here corresponds to sequencing (the semicolon
in C); <tt>Skip</tt> is a no-op; <tt>Asn</tt> assigns
a value into a variable (named by a natural number)
where the value is obtained by computing the value of
an expression (<tt>cexpr</tt>). Finally, <tt>Ite</tt> gives us
an "if-then-else" construct; it branches based on
whether the given expression evaluates to a value equal to zero.

For completeness, our expression language looks like this:

{%highlight coq%}
Inductive cexpr :=
| CVar : nat -> cexpr
| CConst : R -> cexpr
| CPlus : cexpr -> cexpr -> cexpr
| CMinus : cexpr -> cexpr -> cexpr
| CMult : cexpr -> cexpr -> cexpr.
{%endhighlight%}

The semantics for the expression language are what one would naively
expect: <tt>CVar</tt> pulls the value out of a variable; <tt>CConst</tt>
inserts a constant value; the arithmetic operations do the obvious thing
(with the caveat that these are real-arithmetic operations, not the
limited-precision datatypes we are used to programming with).

Here is the semantics for the first version of our command language:

{%highlight coq%}
Inductive eval : state -> cmd -> state -> Prop :=
| ESkip : forall s, eval s Skip s
| ESeq : forall s s' s'' a b,
  eval s a s' ->
  eval s' b s'' ->
  eval s (Seq a b) s''
| EAsn : forall s v e val,
  cexprD e s = val ->
  eval s (Asn v e) (update s v val)
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
{%endhighlight%}


Here <tt>state</tt> is any data structure mapping natural-number indices
("variable names") to real-number values. In our case we use an
association-list. <tt>update</tt> does what one would expect, updating
an entry in the mapping. Finally, <tt>cexprD</tt> is the function
giving meaning to evaluation of <tt>cexpr</tt>s, omitted for brevity.

> Embedding our simple language inside of LTL requires that we relate program states (association lists) to LTL states (functions).
> There are two levels of mapping: first, we need to show how variables in the language map to variables in LTL, and second, we need a way to relate values in our language to LTL values.
> The second is simple, since both LTL values and our language values are simply real numbers, therefore we can simply pick equality.
> The first relation is slightly more complex. We need to relate the infinite set of LTL variables to the finite set of variables in our programming language.
> We do this using the following defintion: (give the definition of models)
> This definition states that every ...


### Embedding into RLTL

In order to embed programs into RLTL, we will need a function that takes a
program (written in the language described above) and converts it to
a formula in RLTL. In practice we also need an additional piece of
data describing how the variables in RLTL match up with those of the
source language, since the two might label variables differently,
using different conventions or even different data-types.

For our first language, the following embedding function suffices:

{%highlight coq%}
Definition embed_program (vars : list (LTLVar * PLVar)) (prg : cmd)
: Formula :=
  Embed (fun pre post =>
           exists init_state post_state : state,
              models vars pre init_state /\
              eval init_state prg post_state /\
              models vars post post_state).
{%endhighlight%}

In prose, this says more or less the following. The RLTL
formula corresponding to the embedding of a program is a
"step-formula" (that is, a formula over two states, a pre-state
and a post-state) requiring the following:

- There exists an initial program state matching up with the
starting RLTL state
- The program must cause the evaluation relation to step from
the pre-state to the post-state
- There exists a final program state matching up with the
final RLTL state

> Does it make sense to put non-deterministic and error programs into this post now?
> It might be the case that the interesting issue comes from failure. With non-determinism, we just need to be explicit about backtracking failure and end-the-world failure.

### Discussion



This embedding function seems intuitively correct, but it has some
problematic corner cases related to crashing and nondeterministic
programs.

1. Suppose we have a nondeterministic program <tt>p</tt>
(written in a language with a different semantics that
permits such a program) that can nondeterministically
step to final states <tt>Bgood</tt>, in which
\\(a = 0\\), or to <tt>Bbad</tt> in which \\(a = 1\\).
Then we would be able to prove that (for an appropriately
chosen <tt>vmap</tt>) \\((embedStep\\_ex\\ vmap\\ p \to a' = 0)\\) -
that is to say, that a program that might or might not step
to a state with \\(a = 0\\) *refines* a program that
always does. Our definition of embedding only requires
one possible ending-state to meet the specification; it makes
no claims about other final states that might (nondeterministically)
be chosen. This is what is referred to as "angelic
nondeterminism"; it is unrealistic for our purposes.

2. Suppose we have a crashing program <tt>q</tt>
(again, written in a language with a semantics
permitting such a thing). In a semantics like the one we defined
above, crashing would usually be represented by a program statement
has no entry in the evaluation relation: a command that cannot
be stepped through, and hence in which there is no final state in the
evaluation relation. But the embedding function defined above
posits the existence of such a final state, so for a program
that crashes the result of the embedding
becomes equivalent to \\(\bot\\) - a logical absurdity
implying anything.
This is very bad, because it says that
\\((embedStep\\_ex\\ vmap\\ q \to k = 42)\\), or whatever other
specification we want to put on the right-hand side of the
arrow. This is more or less the opposite of what we want
for these programs: roughly, we want our notion of embedding to
express that crashing programs meet (i.e., refine or imply)
*no* specifitation, but here they can be shown to refine
*any* specification!

These shortcomings are disappointing, but the embedding function we have
defined does meet our original goal of enabling correct embedding of the
language defined above, since it is impossible to write programs
that crash or exhibit nondeterminism in that language.

(TODO: Say more about why this specification is "obviously correct"
for programs in my language, or at least give some examples?)

### Next Time

So we've just shown an embedding function that's able to embed programs
written in our simple, deterministic, total language. However,
it's not perfect: it cannot handle programs that exhibit nondeterminism or
that crash. In the next post in this series, we'll
see a new embedding function that
supports these features but is provably equivalent to our original
implementation for programs that lack them. We'll also have a bit more
discussion about where these problems come from, and why our solution
manages to address them and is "obviously" correct.

See you next time!
