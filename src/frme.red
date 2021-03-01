%***************************************************************************
%  FILE = frme.red
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
module 'frme;
symbolic;
%in "$redten/decl.red"$


flag ('(frmetric nulltetrad gamma frriemann frricci
	frriccisc freinstein frweyl), 'indexedfn);	%

frmetric := 'eta;
frmetricseq := 1;		 % sequence number for making default metric names 
put ('frmetric, 'simpfn, 'frmetric!*);

% frmetric* constructs a null-tetrad metric.

symbolic procedure frmetric!* (u);
begin scalar ttrd, ttrdi, lex;
%  ttrd := mycar getnme (mycar u, '(nil . nil), 'frmetric);
  ttrd := mycar u;
  lex := makename (append (explode (frmetric), 
			     for each x in explode (frmetricseq)
			     collect mascii (x)));
  frmetricseq := frmetricseq + 1;		% does not decrement. 
  ttrd := newnme (ttrd, lex);
  tabprint (list ("computing ", ttrd));% so user knows what the name will be
% second arg non-nil makes an orthonormal metric
  if mycadr (u) then <<
    mktnsr!* (ttrd, '(-2 -2), ifmtsym '((0 1 2)), 'nil, 'metric,
	    "Ortho Frame metric ");
    lex := igen ('(a!# b!#), indexlim ('(-2 -2)), ifmtsym '((0 1 2)), 'nil);
    writetnsr (ttrd, mycar (lex), 1 . 1, 't);
    for each x in mycdr (lex) do writetnsr (ttrd, x, (-1) . 1, 't)
  >> else <<
    mktnsr!* (ttrd, '(-2 -2), ifmtsym '((1 1 2)), 'nil, 'metric,
	      "Null Frame metric");
    lex := getindices(2);
    lex := zpn (mycar (lex), mycadr (lex), 1);
    writetnsr (ttrd, list (mycar (lex), mycadr (lex)), 1 . 1, 't);
    writetnsr (ttrd, list (mycaddr (lex), mycadddr (lex)), (-1) . 1, 't)
  >>;
  put (ttrd, 'printname, mycar (u) or frmetric);
  put (ttrd, 'frmetric, ttrd);		% refers back to self for generic 
  ttrdi := mycar (invert!* (list (ttrd)));
  put (ttrd, 'coords, 'nil);
  put (ttrdi, 'coords, 'nil);
  put (ttrd, 'cov, '(0 nil 0));
  put (ttrdi, 'cov, '(0 nil 0));
  flag (list (ttrdi), 'nodir);
  protect!* (ttrd, 'w);
  protect!* (ttrdi, 'w);
  put (ttrd, 'shift, list ('t, ttrd, ttrdi, '!d2));
  setmetric (ttrd);
  return (ttrd . 1);
end;

put ('tenmetric, 'simpfn, 'tenmetric!*);

symbolic procedure tenmetric!* (u);
begin scalar lex, tnsr, lex1, tnsr2;
  tnsr := car metric!* ('nil . u);   % makes an empty metric (with name given)
  lex1 := list ('times,
          list ('rdr, getmetric (-2), '(c!# d!#)),
          list ('rdr, getcon (2,1), '((!*at!- c!#) (!*at!- a!#))),
          list ('rdr, getcon (2,1), '((!*at!- d!#) (!*at!- b!#))));
  describe!* (tnsr, mkmsg list("metric created from frame metric %", 
      	      getmetric(2)), 'nil);

  evaltnsr1 (tnsr, '(a!# b!#), lex1, 'nil);
  metric!* (list (tnsr));   % qualify it as a metric
  put (tnsr, 'cometric, list (getmetric (2)));
  put (tnsr, 'coconnection, list (getcon (2,1)));
  put (getmetric (2), 'cometric, list tnsr);
  put (getmetric (2), 'coconnection, list getcon (2,1));
  put (getcon (2,1), 'cometric, list (tnsr, getmetric (2)));

  foreach x in getfam (get (getcon(2, 1), 'parent) or getcon(2,1)) do
	  put (x, 'altmetric, currentmetric); % update this
  cleaner ('tenmetric);
  return (tnsr . 1);
end;

gamma := 'gam;
put ('gamma, 'simpfn, 'gamma!*);

% gamma* computes the gamma symbol in a tetrad frame.
% reference: General Relativity: An Einstein Centenary Survey,
% Chpt 7, pg 373-4

symbolic procedure gamma!* (u);
begin scalar lex, lex1, frme;
  frme := mycar getnme (mycar (u), '(nil . nil), 'gamma);
  lex1 := get (getmetric (1), 'gamma);	% see if it exists. (note name 
  if not frme and indexed (lex1) then return (lex1 . 1); %   on tensor metric)
  frme := newnme (frme, gamma);		% give it a name
  tabprint (list ("computing ", frme));% so user knows what the name will be
  getcon (2,1);				% see if connection is there 
  mktnsr!* ((lex1 := tmpnames ()), '(-2 -1 -1), ifmtsym '((-1 2 3)), 'nil, 'nil, 'nil);
  evaltnsr1 (lex1, '(a!# b!# c!#), 
    list ('plus,
     list ('rdr, getcon (2,1), '((!*at!- a!#) (!*at!- b!#) !*br c!#)),
     list ('minus, 
     list ('rdr, getcon (2,1), '((!*at!- a!#) (!*at!- c!#) !*br b!#)))), 'nil);
  mktnsr!* ((lex := tmpnames ()), '(-2 -2 -2), ifmtsym '((-1 1 2)), 'nil, 'nil, 'nil);
  evaltnsr1 (lex, '(a!# c!# b!#),
    list ('times, 
     list ('rdr, lex1, '(b!# d!# e!#)),
     list ('rdr, getcon (2,1), '((!*at!- a!#) (!*at!+ d!#))),
     list ('rdr, getcon (2,1), '((!*at!- c!#) (!*at!+ e!#)))), 'nil);
  mktnsr!* (frme, '(-2 -2 -2), ifmtsym '((-1 1 2)), '(), 'gamma,
	    mkmsg list("Ricci Rotation coefficients in tetrad for metric %",
		    getmetric(1)));
  put (frme, 'printname, gamma);
  evaltnsr1 (frme, '(a!# b!# c!#), 
    list ('quotient, list ('plus,
      list ('rdr, lex, '(a!# c!# b!#)),
      list ('rdr, lex, '(c!# b!# a!#)),
      list ('minus,
      list ('rdr, lex, '(b!# a!# c!#)))), 2), 'nil);
  protect!* (frme, 'w);
  put (getmetric (1), 'gamma, frme);	% store name on tensor metric
%  put (frme, 'altmetric, currentmetric);
%  put (frme, 'altconnection, currentconnection);
  cleaner ('gamma);
  return (frme . 1);
end;

frriemann := 'frri;
put ('frriemann, 'simpfn, 'frriemann!*);

% frriemann* computes the fully covariant Riemann curvature tensor in a frame.

symbolic procedure frriemann!* (u);
begin scalar frme, lex, lex1;
  frme := mycar getnme (mycar (u), '(nil . nil), 'frriemann);
  lex := get (getmetric (1), 'frriemann);	% see if it exists
  if not frme and indexed (lex) then return (lex . 1);
  frme := newnme (frme, frriemann);		% give it a name
  tabprint (list ("computing ", frme));% so user knows what the name will be
  lex1 := mycar (gamma!* ('nil));
  lex := list ('plus,
         list ('times,
           list ('rdr, lex1, '(a!# b!# d!# !*br e!#)),
           list ('rdr, getcon (2,1), '((!*at!- c!#) (!*at!+ e!#)))),
         list ('minus, list ('times, 
           list ('rdr, lex1, '(a!# b!# c!# !*br e!#)),
           list ('rdr, getcon (2,1), '((!*at!- d!#) (!*at!+ e!#))))),
         list ('times,
           list ('rdr, lex1, '((!*at!* e!#) a!# d!#)),
           list ('rdr, lex1, '(e!# b!# c!#))),  
         list ('minus, list ('times, 
           list ('rdr, lex1, '((!*at!* e!#) a!# c!#)),
           list ('rdr, lex1, '(e!# b!# d!#)))),  
         list ('times,
           list ('rdr, lex1, '(a!# b!# e!#)),
             list ('plus,
             list ('rdr, lex1, '((!*at!* e!#) c!# d!#)),
             list ('minus,
             list ('rdr, lex1, '((!*at!* e!#) d!# c!#))))));

  mktnsr!* (frme, '(-2 -2 -2 -2), ifmtsym '((-1 1 2)(-1 3 4)(2 1 3)), '(),
                   'frriemann,
	    mkmsg list("Riemann tensor in frame for metric %", getmetric(1))); 
  put (frme, 'printname, frriemann);
  evaltnsr1 (frme, '(a!# b!# c!# d!#), lex, 'nil);
  protect!* (frme, 'w);
  put (getmetric (1), 'frriemann, frme);	% save name on tensor metric
  if not get (frme, 'tvalue) then <<
    tabthenprint ("** this space is flat");
    terpri ()
    >>;
  cleaner ('frriemann);
%  put (frme, 'altmetric, currentmetric);
%  put (frme, 'altconnection, currentconnection);
  return (frme . 1);
end;

frricci := 'frric;
put ('frricci, 'simpfn, 'frricci!*);

% frricci* computes the fully covariant Ricci tensor in a frame.

symbolic procedure frricci!* (u);
begin scalar frme, lex;
  frme := mycar getnme (mycar (u), '(nil . nil), 'frricci);
  lex := get (getmetric (1), 'frricci);	% see if it exists
  if not frme and indexed (lex) then return (lex . 1);
  frme := newnme (frme, frricci);	% give it a name
  tabprint (list ("computing ", frme));% so user knows what the name will be
  getcon (2,1);				% see if connection is there 
  lex := list ('times, list ('rdr, getmetric (-2), '(c!# d!#)),
        list ('rdr, mycar (frriemann!* ('nil)), '(c!# a!# b!# d!#)));

  mktnsr!* (frme, '(-2 -2), ifmtsym '((1 1 2)), '(), 'frricci,
	    mkmsg list("Ricci tensor in frame for metric %", getmetric(1))); 
  put (frme, 'printname, frricci);
  evaltnsr1 (frme, '(a!# b!#), lex, 'nil);
  protect!* (frme, 'w);
  if not get (frme, 'tvalue) then <<
%    tabthenprint ("** this metric is a vacuum solution.");
    terpri ()
    >>;
  put (getmetric (1), 'frricci, frme);	% store name on tensor metric
  cleaner ('frricci);
%  put (frme, 'altmetric, currentmetric);
%  put (frme, 'altconnection, currentconnection);
  return (frme . 1);
end;

frriccisc := 'frricsc;
put ('frriccisc, 'simpfn, 'frriccisc!*);

% frriccisc* computes the Ricci scalar from the frame version of the
% Ricci tensor. the result should come out the same as the tensor version.

symbolic procedure frriccisc!* (u);
begin scalar ex1, lex;
  ex1 := mycar getnme (mycar u, '(nil . nil), 'frriccisc);
  lex := get (getmetric(2), 'riccisc);
  if not ex1 and indexed (lex) then return (readtnsr (lex, 'nil));
  ex1 := newnme (mycar (u), frriccisc);	% get a name to put it in
  tabprint (list ("computing ", ex1));% so user knows what the name will be
  getmetric (-2);				% check for metric 

  mktnsr!* (ex1, 'nil, 'nil, 'nil, 'frriccisc,
	    mkmsg list("Ricci scalar created from frame metric %", 
		    getmetric(2)));
  lex := evaltnsr1 (ex1, 'nil, list ('times,
        list ('rdr, getmetric (-2), '(a!# b!#)),
        list ('rdr, mycar (frricci!* ('nil)), '(a!# b!#))), 'nil);
  cleaner ('frriccisc);
  put (getmetric(2), 'riccisc, ex1);	% store value on metric
  return (readtnsr (ex1, 'nil));
end;

freinstein := 'frei;
put ('freinstein, 'simpfn, 'freinstein!*);

% freinstein* computes the fully covariant Einstein tensor in a frame.

symbolic procedure freinstein!* (u);
begin scalar frme, lex;
  frme := mycar getnme (mycar (u), '(nil . nil), 'freinstein);
  lex := get (getmetric (1), 'freinstein);	% see if it exists
  if not frme and indexed (lex) then return (lex . 1);
  frme := newnme (frme, freinstein);
  tabprint (list ("computing ", frme));% so user knows what the name will be
  lex :=  list ('plus, list ('rdr, mycar (frricci!* ('nil)), '(a!# b!#)),
        list ('minus, list ('times, 
                       mk!*sq (quotsq (frriccisc!* ('nil), 2 . 1)),
        list ('rdr, getmetric (2), '(a!# b!#)))));

  mktnsr!* (frme, '(-2 -2), ifmtsym '((1 1 2)), '(), 'freinstein,
	    mkmsg list("Einstein tensor in frame for metric %", getmetric(1))); 
  put (frme, 'printname, freinstein);
  evaltnsr1 (frme, '(a!# b!#), lex, 'nil);
  protect!* (frme, 'w);
  put (getmetric (1), 'freinstein, frme);	% store name on tensor metric
  cleaner ('freinstein);
%  put (frme, 'altmetric, currentmetric);
%  put (frme, 'altconnection, currentconnection);
  put (frme, 'div, 0);
  return (frme . 1);
end;

frweyl := 'frc;
put ('frweyl, 'simpfn, 'frweyl!*);

% frweyl* computes the fully covariant Weyl conformal curvature tensor in a
% frame.

symbolic procedure frweyl!* (u);
begin scalar frme, lex, lex1, lex2, dim;
  frme := mycar getnme (mycar u, '(nil . nil), 'frweyl);
  lex := get (getmetric (1), 'frweyl);	% see if it exists
  if not frme and indexed (lex) then return (lex . 1);
  lex := getindices (1);
  dim := mycadr (lex) - mycar (lex) + 1;  % space dimen
  lex2 := dim - 2;
  lex1 := (dim - 1) * lex2;
  frme := mycar (u);
  frme := newnme (frme, frweyl);	% give it a name
  tabprint (list ("computing ", frme));% so user knows what the name will be
  lex1 := mk!*sq (quotsq (frriccisc!* ('nil), lex1 . 1));
  lex := list ('plus,
        list ('rdr, mycar (frriemann!* ('nil)), '(a!# b!# c!# d!#)),
     list ('quotient, list ('times, list ('rdr, getmetric (2), '(a!# c!#)),
     list ('rdr, mycar (frricci!* ('nil)), '(b!# d!#))), lex2),
     list ('quotient, list ('times, list ('rdr, getmetric (2), '(b!# d!#)),
     list ('rdr, mycar (frricci!* ('nil)), '(a!# c!#))), lex2),
      list ('minus,
     list ('quotient, list ('times, list ('rdr, getmetric (2), '(b!# c!#)),
     list ('rdr, mycar (frricci!* ('nil)), '(a!# d!#))), lex2)),
      list ('minus,
     list ('quotient, list ('times, list ('rdr, getmetric (2), '(a!# d!#)),
     list ('rdr, mycar (frricci!* ('nil)), '(b!# c!#))), lex2)),
      list ('minus,
     list ('times, list ('rdr, getmetric (2), '(a!# c!#)),
                   list ('rdr, getmetric (2), '(b!# d!#)),
        lex1)),
     list ('times, list ('rdr, getmetric (2), '(a!# d!#)),
                   list ('rdr, getmetric (2), '(b!# c!#)),
        lex1));
  mktnsr!* (frme, '(-2 -2 -2 -2), ifmtsym '((-1 1 2)(-1 3 4)(2 1 3)), '(),
                    'frweyl,
	    mkmsg list("Weyl tensor in frame for metric %", getmetric(1))); 
  put (frme, 'printname, frweyl);
  % 2D space-times are conformally flat
  if (dim > 2) then evaltnsr1 (frme, '(a!# b!# c!# d!#), lex, 'nil);
  protect!* (frme, 'w);
  put (frme, 'itype, 'frweyl);
  put (getmetric (1), 'frweyl, frme);	% save name on tensor metric
  if not get (frme, 'tvalue) then <<
    tabthenprint ("** this space is conformally flat");
%    terpri ()
  >>;
  cleaner ('frweyl);
%  put (frme, 'altmetric, currentmetric);
%  put (frme, 'altconnection, currentconnection);
  return (frme . 1);
end;

endmodule;
;end;
