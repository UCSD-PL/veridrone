This directory contains the systems that we've specified using our version of TLA. Many of these systems are out of date and may no long build. At the moment, only look at the following files:

1. AbstractIndAccCtrl.v
2. OneDimAccShim1.v - a concrete height upper bound shim. This is a refinement of AbstractIndAccCtrl.v.
3. OneDimAccShim2.v - another concrete height upper bound shim. This is a refinement of AbstractIndAccCtrl.v as well.
4. OneDimAccShimUtil.v - this file defines useful functions and lemmas for the two height upper bound shims.

In order to build AbstractIndAccCtrl.v and OneDimAccShimUtil.v (on which the two height upper bound shims depend), you have to run make in the tla directory and then make in this directory. At some point, we should fix this.
