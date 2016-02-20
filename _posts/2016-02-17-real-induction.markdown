---
layout: post
title:  "The Real Induction"
date:   2016-02-17 11:32:17
author: daricket
categories: induction
---

We do a lot of proofs as part of this project, many of them using
induction. In computer science, we're usually taught that induction can
prove facts about natural numbers, lists, trees, and other discrete
structures. But in VeriDrone, we deal with the physical world, which means
we work with real numbers. Can we use induction to prove facts about the
real numbers? It turns out we can, though the induction rule is more subtle
than you might expect.

### "Normal" Induction

Let's say you want to prove a property $$P$$ of natural numbers. Induction
says that you can prove $$P$$ holds on *all* natural numbers if you can
prove

- $$P$$ holds on 0 and
- For any $$n$$, if $$P$$ holds on $$n$$, then $$P$$ holds on $$n+1$$.

Intuitively, this process resembles dominoes. We prove a fact for (knock
over) the first element, and then use the inductive step to repeatedly
prove the fact for (knock over) the next element.

![]({{ site.baseurl }}/images/dominoes.jpeg)

Now suppose we want to prove some other property $$Q$$ using induction, but
$$Q$$ is a property of *real* numbers. Attempting to apply the same
induction principle, we can prove that $$Q$$ holds on all non-negative real
numbers if we can prove

- $$Q$$ holds on 0 and
- For any $$x \geq 0$$, if $$Q$$ holds on $$x$$, then $$Q$$ holds on ???

It's not really clear how to complete the inductive step. What is the
"next" real number after $$x$$? The real numbers are dense, which says that
for any two real numbers that aren't the same, there's another real number
between them. This means that there isn't really a notion of a next element
in the reals, as there is for natural numbers, lists, trees, and all the
other structures we normally perform induction on. Real numbers are not
like dominoes.

### Making it real

While there isn't a next real number, we could consider the "next" element
to be a non-empty interval of real numbers. Following this reasoning, the
inductive step for real numbers would require one to prove

- For any $$x \geq 0$$, if $$Q$$ holds on $$x$$, then $$Q$$ holds on all $$y \in [x,z)$$ for some $$z > x$$

Unfortunately, this isn't quite sufficient. The problem is that we can
continue to take positive steps forward without ever covering all the real
numbers. That is, we might only prove $$Q$$ for all real numbers less than
some bound:

![]({{ site.baseurl }}/images/Zeno_Dichotomy_Paradox.png)

There are a couple ways to resolve this issue. One is to ensure that each
step is always at least as large as some positive constant. However, we'll
take an alternate approach. In this approach, we'll make sure that if we
prove $$Q$$ for all numbers less than some bound (e.g. 1 in the above
image), then we prove it for that bound as well. Formally, this means we
need a second inductive step:

- For any $$x \geq 0$$, if $$Q$$ holds on all $$y \in [0,x)$$, then $$Q$$ holds on $$x$$

To summarize, the full induction theorem states that we can prove that our
friend $$Q$$ holds on all non-negative real numbers if we can prove:


<ol type="I">
  <li><script type="math/tex">Q</script> holds on 0</li>
  <li>For any <script type="math/tex">x \geq 0</script>, if <script type="math/tex">Q</script> holds on all <script type="math/tex">y \in [0,x]</script>, then <script type="math/tex">Q</script> holds on all <script type="math/tex">y \in [x,z)</script> for some <script type="math/tex">z > x</script></li>
  <li>For any <script type="math/tex">x \geq 0</script>, if <script type="math/tex">Q</script> holds on all <script type="math/tex">y \in [0,x)</script>, then <script type="math/tex">Q</script> holds on <script type="math/tex">x</script></li>
</ol>

Note that we've weakened the first inductive step by assuming that $$Q$$
holds on all $$y \in [0,x]$$. This is possible for discrete induction as
well.

The proof of real induction proceeds by contradiction. We construct the set
of all elements not satisfying $$Q$$ and rely on the fact that such a set
has a greatest lower bound. If the greatest lower bound satisfies $$Q$$
then this contradicts the first inductive step, and if it does not satisfy
$$Q$$, then this contradicts the second inductive step.

The following is a more formal proof, following the proof style from [this
paper](http://research.microsoft.com/en-us/um/people/lamport/pubs/proof.pdf).

<ul class="no-bullet">
  <li><textsc>Let</textsc> <script type="math/tex">A=\{x \in \mathbb{R} ~:~ 0 \leq x \wedge \neg Q(x) \}</script>.</li>
  <li><textsc>Assume</textsc>: <script type="math/tex">\exists~ x \in A</script></li>
  <li><textsc>Prove</textsc>: <script type="math/tex">False</script></li>
  <li>&lang;1&rang;1. <script type="math/tex">\exists~ i : \mathbb{R}</script> such that <script type="math/tex">i</script> is the greatest lower bound of <script type="math/tex">A</script>.
    <ul class="no-bullet">
      <li><textsc>Proof</textsc>: All non-empty lower bounded sets of reals have a greatest lower bound.</li>
    </ul>
  </li>
  <li>&lang;1&rang;2. <textsc>Case</textsc>: <script type="math/tex"> i\not\in A</script>.
    <ul class="no-bullet">
      <li>&lang;2&rang;1. <script type="math/tex">\forall x \in [0, i],\ Q(x)</script>
          <ul class="no-bullet">
      	      <li><textsc>Proof</textsc>: By the definition of greatest lower bound.</li>
    	  </ul>
      </li>
      <li>&lang;2&rang;2. <script type="math/tex">\exists~ z > i,\ \forall y \in [i, z),\ Q(y)</script>
          <ul class="no-bullet">
      	      <li><textsc>Proof</textsc>: By &lang;2&rang;1 and II.</li>
    	  </ul>
      </li>
      <li>&lang;2&rang;3. <script type="math/tex">z</script> is a lower bound of <script type="math/tex">A</script>.
          <ul class="no-bullet">
      	      <li><textsc>Proof</textsc>: By &lang;2&rang;1 and &lang;2&rang;2.</li>
    	  </ul>
      </li>
      <li>&lang;2&rang;4. QED
          <ul class="no-bullet">
      	      <li><textsc>Proof</textsc>: By &lang;2&rang;3 and the definition of greatest lower bound.</li>
    	  </ul>
      </li>
    </ul>
  </li>
  <li>&lang;1&rang;3. <textsc>Case</textsc>: <script type="math/tex">i\in A</script>.
    <ul class="no-bullet">
      <li>&lang;2&rang;1. <script type="math/tex">\forall ~ 0 \leq x < i,\ Q(x)</script>.
          <ul class="no-bullet">
	      <li><textsc>Proof</textsc>: Since <script type="math/tex">i</script> is a lower bound of <script type="math/tex">A</script></li>
    	  </ul>
      </li>
      <li>&lang;2&rang;2. <script type="math/tex">Q(i)</script>
          <ul class="no-bullet">
	      <li><textsc>Proof</textsc>: By III.</li>
    	  </ul>
      </li>
      <li>&lang;2&rang;3. QED
          <ul class="no-bullet">
      	      <li><textsc>Proof</textsc>: By &lang;2&rang;2 and &lang;1&rang;3.</li>
    	  </ul>
      </li>
    </ul>
  </li>
  <li>&lang;1&rang;4. QED
       <ul class="no-bullet">
      	  <li><textsc>Proof</textsc>: By &lang;1&rang;2 and &lang;1&rang;3.</li>
       </ul>
  </li>
</ul>

Of course, I didn't come up with any of this myself. I took the theorem and
proof from [this
paper](http://math.uga.edu/~pete/instructors_guide_shorter.pdf), which
mentions a number of other papers presenting some version of the theorem.

My esteemed colleague Gregory would also like me to mention that this
result leverages the topology of the real numbers, though I'm not sure if
anyone really knows what that means.

### An Application

The above paper gives many useful applications of real induction. Here, I'm
going to illustrate how it works on a very simple example, inspired by the
following simple application of discrete induction. Consider an infinite
sequence of numbers $$x_n$$ where $$x_0 \geq 0$$ and $$\forall n,\ x_n <
x_{n+1}$$. Suppose we want to prove that $$\forall n, x_n \geq 0$$. We can
do so by induction over the index into the sequence, which is a natural
number.

Now let's take a look at a continuous version of this property. Suppose we
have some function $$f : \mathbb{R} \rightarrow \mathbb{R}$$ such that $$0
\leq f(0)$$. Moreover, suppose we know that $$\forall t \geq 0, f'(t) >
0$$. We would like to prove that $$\forall t \geq 0, f(t) \geq 0$$. As in
the discrete case, we do so using induction, but this time using our
induction principle for the reals. The base case (I) is trivial, so we need
to prove two inductive steps. First,

- For any $$x \geq 0$$, if $$f(y) \geq 0$$ holds on all $$y \in [0,x]$$, then $$f(y) \geq 0$$ holds on all $$y \in [x,z)$$ for some $$z > x$$

This follows from the limit definition of a derivative. Informally, there
is some neighborhood around $$x$$ such that for any point $$y > x$$ in that
neighborhood, the slope of the line from $$(x, f(x))$$ to $$(y, f(y))$$ is
between $$0$$ and $$2*f'(x)$$. In other words, the slope is
nonnegative. More precisely, we instantiate $$\epsilon$$ in the limit
definition with $$f'(x)$$ so that for any line, $$|Slope - f'(x)| \leq
f'(x)$$. This implies that $$f(y) \geq f(x)$$, and $$f(x)\geq 0$$ by the
induction hypothesis. The size of the neighborhood serves as $$z-x$$ in the
above property. The following image depicts this:

![]({{ site.baseurl }}/images/real_ind_post1.svg){: style="width:55%"}

The second inductive step is

- For any $$x \geq 0$$, if $$f(y) \geq 0$$ holds on all $$y \in [0,x)$$, then $$f(x) \geq 0$$

This property follows from continuity of $$f$$. Suppose $$f(x) < 0$$. Then
by continuity, there is some other point $$y < x$$ such that $$f(y) < 0$$,
which is a contradiction.

![]({{ site.baseurl }}/images/real_ind_post2.svg){: style="width:55%"}

Of course, if we actually wanted to prove this property formally, we
probably wouldn't rely on such low-level definitions and would probably
instead rely on general theorems about derivatives. Nevertheless, I hope
this example helps to provide some intuition for real induction and a nice
comparison with discrete induction.