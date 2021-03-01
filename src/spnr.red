%******************************************************************************
%  FILE = spnr.red
% 
%  REDTEN source code
%  Copyright (c) 1986-1994,2006 University of Toronto.
%  All Rights Reserved.
%
%  Written by John Harper and Charles Dyer
%  harper@utsc.utoronto.ca  dyer@utsc.utoronto.ca
%
%  Permission to use this software without fee is granted subject to 
%  the following restrictions:
% 
%  1. This software may not be used or distributed for direct commercial
%     gain.
% 
%  2. The author is not responsible for the consequences of use of this
%     software, no matter how awful, even if they arise from flaws in it.
% 
%  3. The origin of this software must not be misrepresented, either by
%     explicit claim or by omission.
% 
%  4. This code may be altered to suit your need, but such alterations
%     must be plainly marked and the code must not be misrepresented
%     as the original software.
% 
%  5. This notice may not be removed or altered.
% 
%**********************************************************************
module 'spnr;
%symbolic;
%in "$redten/decl.red"$

flag ('(spmetric  spinmat spchristoffel), 'indexedfn);	%

spmetric := '(e3 e4);		% default names for metrics
put ('spmetric, 'simpfn, 'spmetric!*);

% spmetric* generates a set of spinor metrics.

symbolic procedure spmetric!* (u);
begin scalar e3, e4, le3, le4;
  e3 := mycar getnme (mycar u, '(nil . nil), 'spmetric);
  e4 := mycar getnme (mycadr u, '(nil . nil), 'spmetric);
  e3 := newnme (e3, mycar (spmetric)); 
  e4 := newnme (e4, mycadr (spmetric));
  tabprint (list ("computing ", e3," and ", e4));% so user knows what the name will be
  mktnsr!* (e3, '(-3 -3), ifmtsym '((-1 1 2)), 1, 'metric, "Spin metric (-3)");
  mktnsr!* (e4, '(-4 -4), ifmtsym '((-1 1 2)), 1, 'metric, "Spin metric (-4)");
  kill!* (mycar (get (e3, 'conjugate))) ;% remove the automatically made conjugate
  kill!* (mycar (get (e4, 'conjugate)));
  put (e3, 'conjugate, list (e4));	% each is the others conjugate.
  put (e4, 'conjugate, list (e3));
  put (e3, 'coords, 'nil);
  put (e4, 'coords, 'nil);
  le3 := makename (append (explode (e3), explode (invertextension!*)));  % make the inverses
  le4 := makename (append (explode (e4), explode (invertextension!*)));

  mktnsr!* (le3, '(3 3), ifmtsym '((-1 1 2)), 1, 'metric, "Spin metric (3)");
  mktnsr!* (le4, '(4 4), ifmtsym '((-1 1 2)), 1, 'metric, "Spin metric (4)");
  kill!* (mycar (get (le3, 'conjugate)));
  kill!* (mycar (get (le4, 'conjugate)));
  put (le3, 'conjugate, list (le4));	% each is the others conjugate.
  put (le4, 'conjugate, list (le3));
  put (le3, 'coords, 'nil);
  put (le4, 'coords, 'nil);
  put (e3, 'shift, list ('t, e3, le3, 'd3));
  put (e4, 'shift, list ('t, e4, le4, 'd4));
  put (le3, 'pname, e3);
  put (le4, 'pname, e4);
  put (le3, 'parent, e3);
  put (le4, 'parent, e4);
  put (e3, 'cov, '(0 nil 0));
  put (e4, 'cov, '(0 nil 0));
  flag (list (le3, le4), 'nodir);
  protect!* (e3, 'w);
  protect!* (e4, 'w);
  protect!* (le3, 'w);
  protect!* (le4, 'w);
%  if not indexed (mynth (currentmetric, 3)) then setmetric (e3);
%  if not indexed (mynth (currentmetric, 4)) then setmetric (e4);
  setmetric (e3); setmetric (e4);
  terpri ();	% print the names by hand.
  write (" ",e3,", ", e4);
  terpri ();
  return ('t . 1);
end;

spinmat := 'sig;	% default name for spin matrices.
put ('spinmat, 'simpfn, 'spinmat!*);

% spinmat* computes the spinmatrices associated with the defined tensor
% metric. currently it only can do this if the metric is diagonal,
% where it forms spin matrices that are closely related to the Pauli
% matrices of flat space.

symbolic procedure spinmat!* (u);
begin scalar lex, i1, i2, lex1, met, spnr;
  spnr := mycar getnme (mycar u, '(nil . nil), 'spinmat);
  spnr := newnme (spnr, spinmat);
  tabprint (list ("computing ", spnr));% so user knows what the name will be
  met := getmetric (1);		% tensor metric
  mktnsr!* (spnr, '(-1 3 4), ifmtsym '((c 1 2 3)), 'nil, 'connection,
	    mkmsg list("Spin matrices for metric %", getmetric(1)));
  put (spnr, 'printname, spinmat);
  lex := getindices (3);
  i1 := mycar (lex);
  i2 := mycadr (lex);
  if get (met, 'symmetry) = ifmtsym '((0 1 2)) then << % done by hand essentially
    lex1 := igen ('(a!# b!#), indexlim ('(1 1)), ifmtsym '((0 1 2)), 'nil);

    lex := simp (list ('cmod, list ('sqrt, 
           mk!*sq (quotsq (readtnsr (met, mycar (lex1)), '(2 . 1))))));
    writetnsr (spnr, list (mycaar (lex1), i1, i1),
         lex, 't);
    writetnsr (spnr, list (mycaar (lex1), i2, i2),
         lex, 't);
    lex1 := mycdr (lex1);
    lex := simp (list ('cmod, list ('sqrt, 
           mk!*sq (quotsq (readtnsr (met, mycar (lex1)), '(2 . 1))))));
    writetnsr (spnr, list (mycaar (lex1), i1, i2),
         lex, 't);
    lex1 := mycdr (lex1);
    lex := multsq (simp (list ('cmod, list ('sqrt, 
           mk!*sq (quotsq (readtnsr (met, mycar (lex1)), '(2 . 1)))))), 
          '((((i . 1) . -1)) . 1));
    writetnsr (spnr, list (mycaar (lex1), i1, i2),
         lex, 't);
    lex1 := mycdr (lex1);
    lex := simp (list ('cmod, list ('sqrt, 
           mk!*sq (quotsq (readtnsr (met, mycar (lex1)), '(2 . 1))))));
    writetnsr (spnr, list (mycaar (lex1), i1, i1),
         lex, 't);
    writetnsr (spnr, list (mycaar (lex1), i2, i2),
         negsq (lex), 't)
  >> else <<
    merror ("can't make spin matrices -- sorry.", 't)
  >>;
  put (spnr, 'itype, 'connection);
  put (spnr, 'cov, '(0 nil 0));
  protect!* (spnr, 'w);
  % set tensor-spinor connection (type 2)
%  if not indexed (mynth (currentconnection, 2)) then setcon (spnr);
  setcon (spnr);
%  put (spnr, 'altmetric, currentmetric);
%  put (spnr, 'altconnection, currentconnection);
  cleaner ('spinmat);
  return (spnr . 1);
end;

spchristoffel := 'spc;		% default name for christoffel symbols.
put ('spchristoffel, 'simpfn, 'spchristoffel!*);

% spchristoffel computes the spinor christoffel symbols from the spin
% matrices and the tensor christoffel symbols. 
% somewhere there's a factor of 4 hiding, the 8 below is a 2 in the formulae.
% See Pirani in "Lectures on GR", Brandeis, 1964, eqn 3.51

symbolic procedure spchristoffel!* (u);
begin scalar spnr, lex;
  spnr := mycar getnme (mycar (u), '(nil . nil), 'spchristoffel);
  lex := get (getmetric (1), 'spchristoffel);	% name stored on tensor metric.
  if not spnr and indexed (lex) then return (lex . 1);
  spnr := newnme (spnr, spchristoffel);
  tabprint (list ("computing ", spnr));% so user knows what the name will be
  mktnsr!* (spnr, '(3 -3 -1), '(), '(), 'spchristoffel,
	    mkmsg list("Spin Christoffel symbols for metric %", 
		    getmetric (1)));
  put (spnr, 'printname, spchristoffel);
  lex := list ('times,	% expression for symbol in terms of other things
         list ('rdr, getcon (3,1), '((!*at!- d!#) (!*at!+ c!#) (!*at!+ y!#))),
         list ('plus, list ('times,
         list ('rdr, getcon (3,1), '((!*at!+ e!#) (!*at!- b!#) (!*at!- y!#))),
         list ('rdr, mycar (christoffel2!* ('nil)), '(d!# a!# e!#))),
         list ('rdr, getcon (3,1), '((!*at!+ d!#) (!*at!- b!#) (!*at!- y!#)
                                     !*br a!#))));

                     % this 8 is supposed to be a 2, but its right this way!
  evaltnsr1 (spnr, '(c!# b!# a!#), list ('quotient, lex, 8), 'nil);
  protect!* (spnr, 'w);
  put (spnr, 'itype, 'spchristoffel);
  put (getmetric (1), 'spchristoffel, spnr);	% store name on tensor metric.
  cleaner ('spchristoffel);
%  put (spnr, 'altmetric, currentmetric);
%  put (spnr, 'altconnection, currentconnection);
  return (spnr . 1);
end;

endmodule;
;end;
