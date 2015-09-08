---
layout: post
title:  "Fun anecdote about the controller"
date:   2015-09-08 11:12:17
author: lerner
categories: quadcopter test
---

We're catching up with our video archive, and I found this fun video
that illustrates the kinds of non-research fun we've been having!  A
frustrating problem that took us a long time to fix, and caused us to
cry out "D'oh"!

So we were about to try a new test flight, and the quadcopter was
resting on the athletic fields when we usually run our test flights. I
started increasing upward thrust to get off the ground, and usually
the quadcopter would smoothly start lifting upward. But this time, the
quadcopter instead started tilting towards the right. Only two legs
would get off the ground, with the other two still on the ground. It
felt as though the quadcopter would just flip over before even taking
off! I pushed the throttle down, and tried gradually upward again, but
the same thing happened. And it happened over and over, and each time
the quacopter would rise on two legs I would bring it back down, for
fear of flipping. This felt extremely unusual. Our monitors weren't
even enabled yet! This video shows what was happening, and you can
hear me complaining how something is wrong:

<center>
  <video width="75%" controls>
    <source src="{{ site.baseurl }}/videos/controller-problems.mp4" type="video/mp4">
      Your browser does not support the video tag.
  </video>
</center>

"It's just wind!" said Dan. "Just gun it upwards and it will get past
the turbulence!" And indeed it was windy... and indeed, turbulence
can be worse at ground level because the rotors are blowing wind into
the ground... but still... we had lots wind before and nothing caused
this kind of tilting.

I felt something was wrong, something was off. So we tried the
time-tested remedy to many of our problems: reboot the quadcopter! So
disconnect battery, and put it back in. This often fixes odd
intermittent problems, since it resets the GPS, and all sensors, but
this time, it didn't. Same problem! We then re-calibrated the
compass, and made sure the GPS was getting enough
satellites. But the problem persisted. We reverted to the stable
version of the software that didn't have our changes on it, and still
the same thing.

Dan said: "Look we tried everything, it all seems ok, and it was
working before. It's probably wind, just gun it upwards!" Dan is
cavalier, but me, not so much. I was reluctant. But by this point,
we're all reaching our limit, and we had to try something, so I was
tempted to "gun it upwards". 

But then I noticed something. The display on the controller looked a
little different than usual. And then it all came together: the
fine-tuning knobs! The left and right stick on most controllers have
some sort of fine-tuning, which essentially allows you to set what
value zero position of the stick means. This can be useful in some
manual modes to fine tune things so that when your pitch/roll stick is
at the zero position (where zero position means you're just not
touching it and it stays at its center), the quadcopter stays put (and
if it doesn't, there are small knobs/buttons that you can use on the
controller to set the fine-tuning). It turns out in this case, someone
accidentally pushed the fine-tuning knobs all the way to the right, so
that the zero position really meant "go all the way to the
right". Once we fixed the fine-tuning back to normal, everything
worked as before. "D'oh"!!!

**Lesson 1:** always check your fine-tuning!

**Lesson 2:** If something feels
odd and wrong, be careful. We could easily have broken some propellers
if we gunned it all the way up (and I really was about to do it!!!)

