---
layout: post
title:  "Aggressive Flying to Test Height Monitor"
date:   2015-09-17 11:00:00
author: lerner
categories: quadcopter test
---
<div style="float:left;margin:0 15px 5px 0; width:50%">
  <video width="100%" controls>
    <source src="{{ site.baseurl }}/videos/agressive-flying-height-limiter.mp4" type="video/mp4">
      Your browser does not support the video tag.
  </video>
</div>
Here is a video where we are testing our Coq verified altitude limiter
with some aggressive flying close to the height boundary. First, I try
flying up to the altitude boundary while flying aggressively to the
right. Then, with throttle pushed all the way up, I try various
motions in other directions, including so-called yaw (essentially
pivoting). As you can see, the altitude limiter keeps engaging (since
the throttle is all the way up), and it keeps the quadcopter within
the appropriate bounds, while allowing control in other dimensions.


<div style="clear:both;"></div>