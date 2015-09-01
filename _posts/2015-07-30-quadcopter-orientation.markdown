---
layout: post
title:  "Improper quadcopter orientation"
date:   2015-07-30 14:32:17
author: daricket
categories: quadcopter test
---

As I mentioned in [this post]({% post_url 2015-07-17-fall-at-bounds %}),
the first test of our rectangular bounding monitor had a few interesting
problems. In order to discover the cause of the problems, we needed to run
more tests. However, running new tests seemed to uncover a new problem: the
monitor had no idea where it was.

More specifically, the rectangular monitor's estimate of its X position
(how far to the left or right it is) was completely off. This was
surprising to us since our first test revealed no such issue. The
consequence of this problem was that the monitor would cause the quadcopter
to behave in insane ways. Though Sorin had the quadcopter hovering well
within the safe zone, it would all of a sudden roll hard right because it
thought that it was outside the safe zone. Obviously, this was not ideal.

To debug these kinds of issues, we log a bunch of data while the quadcopter
flies. A quick look at the data revealed that the X position estimates the
quadcopter was receiving from the sensors was way off (by as much as 50
meters at times). The monitor doesn't actually get its data directly from
the sensors. Instead, the raw sensor data is first run through what's
called sensor fusion. Sensor fusion takes data from a variety of sensors
with different sources of error and computes an estimate of the current
state (position, velocity, etc.) of the vehicle. Our first guess was that
our code had somehow interacted in a weird way with the sensor fusion code.

To test this, we ran the quadcopter again, now logging raw GPS data, both
with and without our monitor code running. From this test, we discovered
two things:

1. The raw GPS coordinates were just as inaccurate as the X position
estimates coming from the sensor fusion code.
2. The raw GPS coordinates were way off, even when we weren't running
our monitor code.

One possibility was that the GPS unit was damaged from our original
test. However, we were able to rull this out because after the crash in our
original test, we were able to get the vehicle up and running again,
without any GPS issues. Another possibility was that the quadcopter's
*mode* was somehow affecting the position estimates. Quadcopter's like the
IRIS+ that we use often have multiple modes: stabilize, loiter, etc. These
mode essentially dictate how much the autopilot software helps the human
pilot. For example, stabilize just keeps the quadcopter at the pilot's
desired attitude, but doesn't try to control position or altitude. Loiter,
on the other hand, does holds the pilot's desired altitude and position.

For a few reasons that are irrelevant to this post, we had been flying only
in stabilize mode. Since stabilize doesn't need any position estimates, it
was possible that the software shuts down the GPS unit in order to save
power. I spent a lot of time looking into this possibility (the ardupilot
code on which we build is ~600,000 LOC). I even emailed the ardupilot
developer list to ask whether the mode can affect state estimates, but the
answer was no.

After several more frustrating flight tests, each leaving us more confused
then the last, we finally bothered to look into what exactly the X position
of the quadcopter meant. One key to the monitor working is that rolling
left and right affects the X position of the quadcopter. As it turns out,
the orientation of roll is relative to the initial orientation of the
quadcopter when it is turned on. The X position, on the other hand, has
nothing to do with the initial orientation of the quadcopter, and is
instead fixed to be east/west. In our initial test of the rectangular
bounding monitor, we just happened to initially orient the quadcopter so
that roll corresponded to east/west movement. In subsequent tests, we did
not. The bizarre X position estimates received by the quadcopter were
caused by movement in what we thought was the irrelevant Y direction (but
was in fact the X direction).

It was quite a relief to discover the cause of this issue, though we did
feel a bit silly for not realizing it earlier. Obviously, we now always
make sure that the initial orientation of the quadcopter is correct. And in
the future, we plan to have the monitor take into account the yaw of the
quadcopter so that it won't matter how we initially orient it. Yet again,
we see that formal verification doesn't solve all your problems.