This file contains instructions on how to build Redten.

These sources are known to work with Reduce 3.8 under csl, support for
older versions of Reduce is no longer current, and now that Reduce is
open-source, there's no reason to be using an old version, is there?


The quick build method is this:

r38 < redten.gen > log

(This assumes you have write permission to the reduce image file,
which is in this directory - you might want to make a copy of
that. This probably only works for csl Reduce, and I no longer have
access to a PSL, CUlisp or Franz. I cannot seem to get this to work
properly: r38 -i r38.img < redten.gen so I don't do it that way.)

Run r38 and type
load "redten";
and you should see the banner. Try
in "demo/kerr";
to see if one of the demos will run. Off you go...
If there are problems check te log output for obviour error messages.


Redten makes use of a control sequence in order to cause a scroll-up
of the terminal screen. Since each terminal is different, it may not
work on yours. Having it wrong will cause no error in the system, just
in certain circumstances the output will look odd. The default
definition is found at the top of sys.env (stored in the lisp variable
upcursor!*, in a running system it's in r10!-upcursor!*). You can
change that to suit, or define the environment variable UPCURSOR,
which is read by the Redten system at startup. 


Note - we have a lot of work to do to make these sources current, and
interface properly with a modern Reduce. But it should work even as it
is.

July 2009
