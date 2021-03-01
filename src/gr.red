%***************************************************************************
%  FILE = gr.red
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
module 'gr;
%symbolic;
%in "$redten/decl.red"$

flag ('(metric christoffel1 christoffel2 riemann 
	ricci riccisc einstein weyl killing geodesic), 'indexedfn);	%

% note that g has props assigned by the HEPHYS package, but that these
% will be destroyed when the object is made generic.
metric := '!g;
metricseq := 1;		 % sequence number for making default metric names 
put ('metric, 'simpfn, 'metric!*);

% metric* constructs a metric tensor from the line element provided.
% metrics are assumed to be at least symmetric, and will be given a 
% diagonal symmetry if appropriate.
% Unless a name is given, the default name is constructed from the value of 
% METRIC and the METRICSEQ variable.
% If an indexed object name is given, that object is made into a metric.
% If no name is given, an empty metric object is created, which needs
% components, and a later full metric qualification.

symbolic procedure metric!* (u);
begin scalar lex, lex1, diag, tnsr2, lnel, tnsr, elmn, lnelname;
  lnelname := mycar (u);
  if not lnelname then <<
    lex := makename (append (explode (metric), 
			     for each x in explode (metricseq)
			     collect mascii (x)));
    metricseq := metricseq + 1;		% does not decrement. 
    tnsr := newnme (mycadr (u), lex);	% default or given name 
    tabprint (list ("creating ", tnsr));% so user knows what the name will be
    mktnsr!* (tnsr, '(-1 -1), ifmtsym '((1 1 2)), 'nil, 'metric,
	      "empty metric (to be filled)");
    put (tnsr, 'printname, mycadr u or metric);
    return tnsr . 1
    >>
  else if indexed (lnelname) then <<
    tnsr := lnelname;
% this check is too restrictive.
%    IF NOT (GET (TNSR, 'INDEXTYPE) = '(-1 -1)) THEN
%      MERROR (LIST (TNSR, "does not have metric structure."), 'T, 'METRIC);
     % check if it is a rank-2 covariant object
    if mycar (get (tnsr, 'indices)) neq 2 
       or memq (1, mapcar (get (tnsr, 'indextype), 'sign)) then 
       merror (mkmsg list ("% does not have metric structure.",
			   tnsr), 't);
    lex1 := get (tnsr, 'tvalue);	% determine if its diagonal
    while (lex1 and mycaaar (lex1) = mycadaar (lex1)) do lex1 := mycdr (lex1);
    % implicit object are not diagonal, unless declared by the user.
    if not lex1 and not get (tnsr, 'implicit) 
       % object is implicit, but user said its diagonal
       or (get (tnsr, 'implicit) and mycaaar (get (tnsr, 'symmetry)) eq 0)
    then diag := 't	% metric is diagonal
    else diag := 'nil;			% metric is not diagonal
    put (tnsr, 'itype, 'metric);
    put (tnsr, 'metric, tnsr)		% refers back to self for generic 
  >> else if lnelname then <<
    lnel := reval (lnelname);
    if atom (lnel) then
       merror (mkmsg list ("improper line-element: %.",
			   lnelname), 'nil);

    lex := makename (append (explode (metric), 
			     for each x in explode (metricseq)
			     collect mascii (x)));
    metricseq := metricseq + 1;		% does not decrement. 
    tnsr := newnme (mycadr (u), lex);	% default or given name 
    tabprint (list ("computing ", tnsr));% so user knows what the name will be
    mktnsr!* (tnsr, '(-1 -1), ifmtsym '((1 1 2)), 'nil, 'metric,
	      mkmsg list("metric created from %", lnelname));
    put (tnsr, 'printname, mycadr (u) or metric);
    put (tnsr, 'metric, tnsr);		% refers back to self for generic 
    lex := igen ('(a!# b!#), indexlim ('(-1 -1)), ifmtsym '((0 1 2)), 'nil);
    while lex and not (lnel = 0) do <<    % first run down the diagonal
      lex1 := elmmet (lnel, mycar (lex));
%      lnel := mk!*sq addsq (mycadr (lnel), negsq (multsq (mycar (lex1),
%                   simp!* ('times . mycdr (lex1)))));   % update line-element
%     writetnsr (tnsr, mycar (lex), mycar (lex1), 't);
      lnel := reval list ('plus, lnel, list ('minus, list ('times, mycar lex1,
		'times . mycdr lex1))); 
      writetnsr (tnsr, mycar (lex), simp mycar (lex1), 't);
      lex := mycdr (lex)
    >>;
    if lnel = 0 then diag := 't     % if nothing left, then metric is diagonal
    else <<
      diag := 'nil;                 % otherwise, look at off-diag elements
      lex := igen ('(a!# b!#), indexlim ('(-1 -1)), ifmtsym '((-1 1 2)), 'nil);
      while lex and not (lnel = 0) do <<
        lex1 := elmmet (lnel, mycar (lex));
%        lnel := mk!*sq addsq (mycadr (lnel), negsq (multsq (mycar (lex1),
%                     simp!* ('times . mycdr (lex1)))));
%        writetnsr (tnsr, mycar (lex), quotsq (mycar (lex1), 2 . 1), 't);
        lnel := reval list ('plus, lnel, list ('minus, list ('times, mycar lex1,
		'times . mycdr lex1))); 
        writetnsr (tnsr, mycar (lex), simp list ('quotient, mycar (lex1), 2), 't);
        lex := mycdr (lex)
      >>
    >>;
    if not (lnel = 0) then 
       merror (mkmsg list("invalid line element: %.", lnelname), 't)
  >> else <<		% build metric from frame metric and connection
%this section removed and placed in tenmetric()
  >>;
  if diag then put (tnsr, 'symmetry, ifmtsym '((0 1 2)));	% is diagonal
  tnsr2 := mycar (invert!* (list (tnsr)));	% construct the inverse metric
  put (tnsr, 'shift, list ('t, tnsr, tnsr2, '!d1));
  protect!* (tnsr, 'w);				% protect
  protect!* (tnsr2, 'w);
  put (tnsr, 'cov, '(0 nil 0));			% 0 covariant derivative
  put (tnsr2, 'printname, get (tnsr, 'printname));

  setmetric (tnsr);
  cleaner ('metric);
  return (tnsr . 1);
end;

put ('!d, 'simpfn, 'simpd!*);

symbolic procedure simpd!* (u);
% simpd* simplifies coordinate differentials used in building a line element.
% if the u in d(u) is a coordinate name, the unevaled form is returned, 
% otherwise the total derivative is computed.
begin scalar val, lex, lis;
  val := reval (mycar (u));
  if numberp (val) then return ('nil . 1)
  else if memq (val, coords!*) or (not atom (val) and indexed (mycadr (val))) then 
                 return (mksq (list ('!d, val), 1))    % coord differential
  else <<		% find total derivative of argument to d
    lex := coords!*;
    while lex do <<
      lis := list ('times, 
        list ('df, val, mycar (lex)),	% partial derivative wrt a coordinate
        list ('!d, mycar (lex))) . lis;	% corresponding differential.
      lex := mycdr (lex)
    >>;
    lis := reval ('plus . lis);
    if lis = 0 then 		
      merror (mkmsg list ("missing differential: %.", '!d . u), 'nil);
    return (simp (lis))
  >>;
end;

% elmmet finds and returns the element of the metric corresponding to index.
% it substitutes 0's and 1's for the d() forms and evals the line-element
% to see whats left. this makes it possible to run this thing on non-expanded
% line-elements (which was not possible before).

symbolic procedure elmmet (lnel, indexx);
begin scalar lex, lex1;
  lex := for each x in coords!* collect list ('equal, list ('!d, x), 
         iselm (x, indexx));
  lex1 := for each x in indexx collect 
              list ('!d, mynth (coords!*, x - mycar (getindices(1)) + 1));
  return (subeval (append (lex, list (lnel))) . lex1);
%  return (simpsub (append (lex, list (lnel))) . lex1);
end;

% iselm returns the 1's and 0's required in elmmet. ie. if crd's tensor index
% is in the index, we get 1 else 0.

symbolic procedure iselm (crd, indexx);
  if memq (look (coords!*, crd, mycar (getindices(1))), indexx) then 1
  else 0;

christoffel1 := 'c1;
put ('christoffel1, 'simpfn, 'christoffel1!*);

% christoffel1* computes the Christoffel symbols of the first kind, which
% are symmetric in their first 2 indices.

symbolic procedure christoffel1!* (u);
begin scalar tnsr, lex, lex1;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'christoffel1);
  lex1 := get (getmetric (1), 'christoffel1);	% see if its already been made
  if not tnsr and indexed (lex1) then return (lex1 . 1);
  tnsr := newnme (tnsr, christoffel1);		% get a name for it
  tabprint (list ("computing ", tnsr));% so user knows what the name will be
  mktnsr!* (tnsr, '(-1 -1 -1), ifmtsym '((1 1 2)), '(), 'christoffel1,
	    mkmsg list("Type 1 Christoffel symbol created from metric %", 
		    getmetric(1)));
  put (tnsr, 'printname, christoffel1);
  if (not (get (getmetric(1), 'multiplier) = '(1 . 1))) then 
     merror (mkmsg list ("metric % not simplified.",
			 getmetric(1)), 'nil);
  if (not (get (getmetric(-1), 'multiplier) = '(1 . 1))) then 
     merror (mkmsg list ("metric inverse % not simplified.", 
		   getmetric(-1)), 'nil);
  lex := list ('plus,				% defining expression
        list ('rdr, getmetric (1), '(a!# c!# !*br b!#)),
        list ('rdr, getmetric (1), '(b!# c!# !*br a!#)),
                list ('minus,
        list ('rdr, getmetric (1), '(a!# b!# !*br c!#))
                ));
  evaltnsr1 (tnsr, '(a!# b!# c!#), list ('quotient, lex, 2), 'nil);
  put (tnsr, 'shift, '(t));			% no shifts allowed
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  protect!* (tnsr, 'w);
  put (getmetric (1), 'christoffel1, tnsr);	% store name on metric
  cleaner ('christoffel1);
  return (tnsr . 1);
end;

christoffel2 := 'c2;
put ('christoffel2, 'simpfn, 'christoffel2!*);

% christoffel2* computes the Christoffel symbols of the second kind. the
% first index is up and it is symmetric in its second and third indices.

symbolic procedure christoffel2!* (u);
begin scalar tnsr, lex1;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'christoffel2);
  lex1 := get (getmetric (1), 'christoffel2);	% see if its been made 
  if not tnsr and indexed (lex1) then return (lex1 . 1);
  tnsr := newnme (tnsr, christoffel2);
  tabprint (list ("computing ", tnsr));% so user knows what the name will be
  mktnsr!* (tnsr, '(1 -1 -1), ifmtsym '((1 2 3)), '(), 'christoffel2,
	    mkmsg list("Type 2 Christoffel symbol created from metric %", 
		    getmetric(1)));
  put (tnsr, 'printname, christoffel2);
  evaltnsr1 (tnsr, '(a!# b!# c!#), list ('times, % defining expression
        list ('rdr, getmetric (-1), '(a!# d!#)),
        list ('rdr, mycar (christoffel1!* ('nil)), '(b!# c!# d!#))
        ), 'nil);
  put (tnsr, 'shift, '(t));			% no shifts allowed
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  protect!* (tnsr, 'w);
  put (getmetric (1), 'christoffel2, tnsr);	% store name on metric
  cleaner ('christoffel2);
  return (tnsr . 1);
end;

riemann := 'ri;
put ('riemann, 'simpfn, 'riemann!*);

% riemann* computes the fully covariant Riemann curvature tensor.

symbolic procedure riemann!* (u);
begin scalar tnsr, lex;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'riemann);
  lex := get (getmetric (1), 'riemann);	% see if it exists
  if not tnsr and indexed (lex) then return (lex . 1);
  tnsr := newnme (tnsr, riemann);	% get a name for it
  tabprint (list ("computing ", tnsr));% so user knows what the name will be
  mktnsr!* (tnsr, '(-1 -1 -1 -1), ifmtsym '((-1 1 2)(-1 3 4)(2 1 3)), '(),
                    'riemann,
	    mkmsg list("Riemann tensor created from metric %", 
		    getmetric(1)));
  put (tnsr, 'printname, riemann);
  lex := list ('plus,
        list ('rdr, mycar (christoffel1!* ('nil)), '(b!# d!# a!# !*br c!#)),
           list ('minus,
        list ('rdr, mycar (christoffel1!* ('nil)), '(b!# c!# a!# !*br d!#))),
           list ('times,
        list ('rdr, mycar (christoffel2!* ('nil)), '(e!# b!# c!#)),
        list ('rdr, mycar (christoffel1!* ('nil)), '(a!# d!# e!#))),
           list ('minus,
           list ('times,
        list ('rdr, mycar (christoffel2!* ('nil)), '(e!# b!# d!#)),
        list ('rdr, mycar (christoffel1!* ('nil)), '(a!# c!# e!#)))));
  evaltnsr1 (tnsr, '(a!# b!# c!# d!#), lex, 'nil);
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  protect!* (tnsr, 'w);
  put (getmetric (1), 'riemann, tnsr);	% store name on metric
  if not get (tnsr, 'tvalue) then <<
    tabthenprint ("** this space is flat");
    terpri ()
    >>;
  cleaner ('riemann);
  return (tnsr . 1);
end;

ricci := 'ric;
put ('ricci, 'simpfn, 'ricci!*);

% ricci* computes the fully covariant Ricci tensor.

symbolic procedure ricci!* (u);
begin scalar tnsr, lex;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'ricci);
  lex := get (getmetric (1), 'ricci);	% see if it exists
  if not tnsr and indexed (lex) then return (lex . 1);
  tnsr := newnme (tnsr, ricci);		% get a name for it
  tabprint (list ("computing ", tnsr));% so user knows what the name will be
  mktnsr!* (tnsr, '(-1 -1), ifmtsym '((1 1 2)), '(), 'ricci,
	    mkmsg list("Ricci tensor created from metric %", 
	     getmetric(1)));

  put (tnsr, 'printname, riemann);	% Use R for both  

  if (!*newriccistyle) then
    evaltnsr1 (tnsr, '(a!# b!#), list ('times,
          list ('rdr, getmetric (-1), '(c!# d!#)),
    	      list ('rdr, mycar (riemann!* ('nil)), '(c!# a!# d!# b!#))), 'nil)
  else 	      
    evaltnsr1 (tnsr, '(a!# b!#), list ('times,
          list ('rdr, getmetric (-1), '(c!# d!#)),
    	      list ('rdr, mycar (riemann!* ('nil)), '(c!# a!# b!# d!#))), 'nil);


%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  protect!* (tnsr, 'w);
  if not get (tnsr, 'tvalue) then <<
    tabthenprint ("** this metric is a vacuum solution.");
%    terpri ()
    >>;
  put (getmetric (1), 'ricci, tnsr);	% store name on metric
  cleaner ('ricci);
  return (tnsr . 1);
end;

riccisc := 'ricsc;
put ('riccisc, 'simpfn, 'riccisc!*);

% riccisc* computes the Ricci scalar.

symbolic procedure riccisc!* (u);
begin scalar ex1, lex;
  ex1 := mycar getnme (mycar (u), '(nil . nil), 'riccisc);
  lex := get (getmetric(1), 'riccisc);
  if not ex1 and indexed (lex) then return (readtnsr (lex, 'nil));
  ex1 := newnme (mycar (u), riccisc);		% get a name to put it in
  tabprint (list ("computing ", ex1));% so user knows what the name will be
  mktnsr!* (ex1, 'nil, 'nil, 'nil, 'riccisc,
	    mkmsg list("Ricci scalar created from metric %", 
		    getmetric(1)));
  evaltnsr1 (ex1, 'nil, list ('times,
        list ('rdr, getmetric (-1), '(a!# b!#)),
        list ('rdr, mycar (ricci!* ('nil)), '(a!# b!#))), 'nil);
  cleaner ('riccisc);
  put (getmetric(1), 'riccisc, ex1);	% store value on metric
  return (readtnsr (ex1, 'nil));
end;

einstein := 'ei;
put ('einstein, 'simpfn, 'einstein!*);

% einstein* computes the fully covariant Einstein tensor.

symbolic procedure einstein!* (u);
begin scalar tnsr, lex;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'einstein);
  lex := get (getmetric (1), 'einstein);		% see if it exits
  if not tnsr and indexed (lex) then return (lex . 1);
  tnsr := newnme (tnsr, einstein);		% get a name for it
  tabprint (list ("computing ", tnsr));% so user knows what the name will be
  mktnsr!* (tnsr, '(-1 -1), ifmtsym '((1 1 2)), '(), 'einstein,
	    mkmsg list("Einstein tensor created from metric %", 
		    getmetric(1)));
  put (tnsr, 'printname, einstein);
  evaltnsr1 (tnsr, '(a!# b!#), list ('plus,
        list ('rdr, mycar (ricci!* ('nil)), '(a!# b!#)),
        list ('minus, list ('times, mk!*sq (quotsq (riccisc!* ('nil),
				 2 . 1)),
        list ('rdr, getmetric (1), '(a!# b!#))))), 'nil);
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  protect!* (tnsr, 'w);
  put (getmetric (1), 'einstein, tnsr);		% store name on metric
  put (tnsr, 'div, 0);
  cleaner ('einstein);
  return (tnsr . 1);
end;

weyl := 'c;
put ('weyl, 'simpfn, 'weyl!*);

% weyl* computes the fully covariant Weyl conformal curvature tensor.

symbolic procedure weyl!* (u);
begin scalar tnsr, lex, lex1, lex2, dim;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'weyl);
  lex := get (getmetric (1), 'weyl);	% see if it exists
  if not tnsr and indexed (lex) then return (lex . 1);
  lex := getindices(1);
  dim := mycadr (lex) - mycar (lex) + 1;    % space dimen
  lex2 := dim - 2;
  lex1 := (dim - 1) * lex2;
  tnsr := mycar (u);
  tnsr := newnme (tnsr, weyl);		% get a name for it
  tabprint (list ("computing ", tnsr));% so user knows what the name will be
  lex1 := mk!*sq (quotsq (riccisc!* ('nil), lex1 . 1));
  lex := list ('plus,
        list ('rdr, mycar (riemann!* ('nil)), '(a!# b!# c!# d!#)),
     list ('quotient, list ('times, list ('rdr, getmetric (1), '(a!# c!#)),
     list ('rdr, mycar (ricci!* ('nil)), '(b!# d!#))), lex2),
     list ('quotient, list ('times, list ('rdr, getmetric (1), '(b!# d!#)),
     list ('rdr, mycar (ricci!* ('nil)), '(a!# c!#))), lex2),
      list ('minus,
     list ('quotient, list ('times, list ('rdr, getmetric (1), '(b!# c!#)),
     list ('rdr, mycar (ricci!* ('nil)), '(a!# d!#))), lex2)),
      list ('minus,
     list ('quotient, list ('times, list ('rdr, getmetric (1), '(a!# d!#)),
     list ('rdr, mycar (ricci!* ('nil)), '(b!# c!#))), lex2)),
      list ('minus,
     list ('times, list ('rdr, getmetric (1), '(a!# c!#)),
                   list ('rdr, getmetric (1), '(b!# d!#)),
        lex1)),
     list ('times, list ('rdr, getmetric (1), '(a!# d!#)),
                   list ('rdr, getmetric (1), '(b!# c!#)),
        lex1));
  mktnsr!* (tnsr, '(-1 -1 -1 -1), ifmtsym '((-1 1 2)(-1 3 4)(2 1 3)), '(),
                   'weyl, mkmsg list("Weyl tensor created from metric %",
		    getmetric(1)));
  put (tnsr, 'printname, weyl);
  % 2D space-times are conformally flat
  if (dim > 2) then evaltnsr1 (tnsr, '(a!# b!# c!# d!#), lex, 'nil);
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  protect!* (tnsr, 'w);
  put (getmetric (1), 'weyl, tnsr);	% put name on metric
  if not get (tnsr, 'tvalue) then <<
    tabthenprint ("** this space is conformally flat");
%    terpri ()
  >>;
  cleaner ('weyl);
  return (tnsr . 1);
end;

put ('dot, 'simpfn, 'dot!*);

symbolic procedure dot!*(u);
begin scalar tnsr1, tnsr2, indx1, indx2, lex;
  lex := getnme (mycar u, '(t . t), 'dot);
  tnsr1 := mycar lex; indx1 := mycadr lex;
  lex := getnme (mycadr u, '(t . t), 'dot);
  tnsr2 := mycar lex; indx2 := mycadr lex;
  if not indx1 then indx1 := head (alphalist!*, mycar get (tnsr1, 'indices));
  if not indx2 then indx2 := head (alphalist!*, mycar get (tnsr2, 'indices));
  indx1 := for each x in indx1 collect 
	if memq(x, alphalist!*) then list ('!*at!-, x) else x;
  indx2 := for each x in indx2 collect 
	if memq(x, alphalist!*) then list ('!*at!+, x) else x;
  lex := list ('times, list ('rdr, tnsr1, indx1), list ('rdr, tnsr2, indx2));
  return simp evaltnsr1 ('dot, 'nil, lex, 't);
end;

killing := '!k;		% default name for killing vector
put ('killing, 'simpfn, 'killing!*);

% killing* computes either the Killing equations or the conformal Killing
% equations depending on whether the second argument is 'nil or 't.
% the first argument is the name of the array that will be created to
% hold the equations.

symbolic procedure killing!* (u);
begin scalar tnsr, conf, lex;
  tnsr := mycar getnme (mycar (u), '(nil . t), 'killing);		% array name
  conf := mycadr (u);		% conformal flag (value not important)
  if not (indexed (killing) and get (killing, 'itype) eq 
         'killingvec) then	% make the killing vector (it's implicit)
    mktnsr!* (killing, '(-1), '(), killing, 'killingvec, "Killing vector");

  mktnsr!* (tnsr, '(-1 -1), ifmtsym '((1 1 2)), '(), 'killing, 
	    (conf and mkmsg list("Conformal killing equations for metric %", 
		    getmetric(1)))  or 
	    mkmsg list("Killing equations for metric %", 
		    getmetric(1)));
	    
%  put (tnsr, 'symmetry, '(((1) 1 2)));
  if not conf then conf := 0
  else <<
      conf := mycar div!* (list killing); % determine conformal factor
      conf := mk!*sq if indexed (conf) then readtnsr (conf, '())
                                          else 'nil . 1
  >>;
  evaltnsr1 (tnsr, '(a!# b!#), list ('plus,
        list ('rdr, killing, '(a!# !*br b!#)),
        list ('rdr, killing, '(b!# !*br a!#)),
        list ('times, -2,
                list ('rdr, mycar (christoffel2!* ('nil)), '(z!# a!# b!#)),
                list ('rdr, killing, '(z!#))),
        list ('times, -2, conf, list ('rdr, getmetric (1), 
                             '(a!# b!#)))), 'nil);
  put (tnsr, 'itype, if not (conf = 0) then 'ckilling else 'killing);
  put (tnsr, 'indexed, 'array);
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  cleaner ('killing);
  return (tnsr . 1);
end;

geodesic := '!s;		% default name for affine parameter
put ('geodesic, 'simpfn, 'geodesic!*);

% geodesic* computes the geodesic equations. first arg is a name for
% a array to put them in, optional second arg is a name for the
% affine parameter.

symbolic procedure geodesic!* (u);
begin scalar tnsr, param, lex, lex1;
  tnsr := mycar getnme (mycar (u), '(nil . t), 'geodesic);
  param := mycar getnme (mycadr (u), '(nil . nil), 'geodesic) or geodesic;	% affine parameter
  if get (param, 'avalue) then
     merror (mkmsg list ("% invalid as affine connection.",
			 param), 't);
%  tnsr := getnme (tnsr, '(nil . nil), 'geodesic);
  mktnsr!* (tnsr, '(1), '(), 'nil, 'geodesic,
	    mkmsg list("Geodesic equations for metric %", 
		    getmetric(1)));
  for each x in coords!* do depend1 (x, param, 't);
  lex := mkcoords!*!* (tmpnames (), 'nil);
  lex1 := list ('plus,
        list ('df, list ('rdr, lex, '(a!#)), param, param),
        list ('times,
        list ('rdr, mycar (christoffel2!* ('nil)), '(a!# b!# c!#)),
        list ('df, list ('rdr, lex, '(b!#)), param),
        list ('df, list ('rdr, lex, '(c!#)), param)));
  evaltnsr1 (tnsr, '(a!#), lex1, 'nil);
  put (tnsr, 'itype, 'geodesic);
  put (tnsr, 'indexed, 'array);
%  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  cleaner ('geodesic);
  return (tnsr . 1);
end;

put ('div, 'simpfn, 'div!*);

symbolic procedure div!* (u);
% computes the divergence of arg1, output into optional arg2
begin scalar lex, lex1, lex2, tnsr, n, tnsr1, value;
  tnsr := mycar getnme (mycar u, '(t . t), 'div);
  if get (tnsr, 'itype) eq 'generic then return mksq ('div . u, 1);
  if (lex := get (tnsr, 'div)) and (indexed (lex) or lex = 0) then
      return (lex . 1);		% name or value already computed
  tnsr1 := mycadr (u);  % optional output name
  n:= mycar (get (tnsr, 'indices)); 
  if not tnsr1 then tnsr1 := makename (append (explode (tnsr),
	      explode ('!_!D)));

  lex := insert (get (tnsr, 'indextype), 'nil, n, t);
  change!-tnsr!-environment (tnsr);    % change metrics and coords
  mktnsr!* (tnsr1, lex,
    % new symmetry is found from those left over when first index goes, and then
    % roll them 1 place to the left.
	roll!-sym (new!-symmetry (get (tnsr, 'symmetry), 0 . lex), -1),  %determine new symmetry
	 '(), 'divergence, mkmsg list("Divergence of %", tnsr));

  lex2 := head (alphalist!*, n-1);  % will be output index
  if mynth (get (tnsr, 'indextype), n) > 0 then
    << % index already raised, just contract
      value := list ('rdr, tnsr, append (lex2, '(!#z !*dbr !#z)))
    >> else <<  % write in metric contraction.
      lex1 := append (lex2, '(!#y !*dbr !#z));
      value := list ('times, list ('rdr, tnsr, lex1), 
	list ('rdr, getmetric (mynth (get (tnsr, 'indextype), n)), 
		 	'(!#y !#z)))
    >>;
  lex := evaltnsr1 (tnsr1, lex2, value, 'nil);
  
  restore!-tnsr!-environment ();
  if length (get (tnsr1, 'tvalue)) = 0 then <<
    kill!* (tnsr1);
    tnsr1 := 0	% is 0
   >> else <<
    protect!* (tnsr1, 'w);
    put (tnsr1, 'printname, makename (append 
			      (explode (get (tnsr, 'printname)),
			       explode ('!_!D)))) % div printname
   >>;
  put (tnsr, 'div, tnsr1);
  cleaner ('div);
  return tnsr1 . 1;
end;

put ('dalembert, 'simpfn, 'simpdalem);

symbolic procedure simpdalem (u);
begin scalar lex;
  u := reval (mycar (u));
  lex := list ('quotient, list ('minus, list ('pdf, list ('times,
        list ('sqrt, list ('minus, list ('det, getmetric (1)))),
        list ('rdr, getmetric (-1), '(a!# b!#)), list ('pdf, u,
        '(findex a!#))), '(findex b!#))),
         list ('sqrt, list ('minus, list ('det, getmetric (1)))));
  lex := evaltnsr1 ('lex, 'nil, lex, 'nil);
  cleaner ('dalembert);
% use aeval?
  return (simp lex);
end;

flag ('(getmetric), 'opfn);		% user and lisp callable

% getmetric returns the metric of type n from currentmetric.
symbolic procedure getmetric (n); getmetric!* (n, currentmetric, 't);

symbolic procedure getmetric!* (n, metlist, loudflag);
begin scalar lex;
  metlist := metlist or currentmetric; 
  if n < 0 then <<
    if not indexed (lex := makename (append (explode (
				   getmetric!* (abs (n), metlist, loudflag)),
      explode (invertextension!*)))) and loudflag then
      merror (mkmsg list ("missing inverse: %.", lex), 't);
    return (lex)
  >>
  else if not indexed (lex := mynth (metlist, n)) and  loudflag then
    merror (mkmsg list ("metric type % does not exist.", n), 't)
  else return (lex);
end;

flag ('(getcon), 'opfn);

symbolic procedure getcon (n, m); getcon!* (n, m, 't);

% getcon returns the connection of type n from currentconnection.
symbolic procedure getcon!* (n, m, loudflag);
begin scalar lex;
  lex := mapindextype (list (n, m));
  n := abs mycar lex; m := abs mycadr lex;
%  if (n >= m) then 
%    merror (mkmsg list ("connection type in wrong order: % % (from getcon).",
%	 n, m), 't);
  lex := mynth (mynth (currentconnection, n), m);
  if not indexed (lex) and loudflag then
    merror (mkmsg list ("connection type % % does not exist.", n, m), 't)
  else return (lex);
end;

flag ('(setmetric), 'opfn);

% setmetric causes the named metric to be placed in the proper location
% in currentmetric. the object must have 2 covariant indices and be
% type metric. It also sets the COORDS list, and checks the 'nodir flags.
% any cometric is also made current
symbolic procedure setmetric (tnsr);
begin scalar lex, lex1;
  tnsr := mycar getnme (tnsr, '(t . t), 'setmetric);
  if get (tnsr, 'itype) neq 'metric or
        % need the covariant metric
     (lex := mycar (get (tnsr, 'indextype))) > 0 then
     return setmetric get (tnsr, 'parent);
%    merror (mkmsg list ("bad metric: %.", tnsr), 't);
  % hide the old metric
  if (lex1 := getmetric!* (-lex, currentmetric, 'nil)) then 
       flag (list lex1, 'nodir);
  currentmetric := insert (currentmetric, tnsr, -lex, 't);
  % unhide the new metric
  if (lex1 := getmetric!* (-lex, currentmetric, 'nil)) then
	 remflag (list lex1, 'nodir);
  % set the co-metrics
  foreach x in get (tnsr, 'cometric) do
	if x neq tnsr and not memq (x, currentmetric) then
		setmetric (x);
  % set the co-connections
  foreach x in get (tnsr, 'coconnection) do
	if x neq tnsr and not memq (x, currentconnection) then
		setcon (x);
  % if setting the tensor metric, also set the coords.
  if lex eq -1 then coords!* := get (tnsr, 'coords);
  return (tnsr);
end;


flag ('(setcon), 'opfn);

% setcon places the named connection in the currentconnection list 
% The object must be of type connection. 
% currentconnection is now a list of lists, of the form
% ((tensor-frame tensor-spinor tensor-dyad)(frame-tensor frame-spinor frame-dyad)..)

symbolic procedure setcon (conn);
begin scalar n, m, lex;
  conn := mycar getnme (conn, '(t . t), 'setcon);
  if not (get (conn, 'itype) eq 'connection) then
    merror (mkmsg list ("bad connection %.", conn), 't);
  lex := mapindextype get (conn, 'indextype);
  n := abs mycar lex; m := abs mynth (lex, length lex);
%  if ((n := abs mycar lex) >= (m := abs mynth (lex, length lex))) then
%    merror (mkmsg list ("connection type in wrong order: % % (from setcon).",
%	 n, m), 't);
  lex := mynth (currentconnection, n);
  lex := insert (lex, conn, m, 't);
  currentconnection := insert (currentconnection, lex, n, 't);
  % set the co-metrics
  foreach x in get (conn, 'cometric) do
	if x neq conn and not memq (x, currentmetric) then
		setmetric (x);
  % set the co-connections
  foreach x in get (conn, 'coconnection) do
	if x neq conn and not memq (x, currentconnection) then
		setcon (x);
  return (conn);
end;

% newnme generates the default name if none was given and prints
% the "computing <name>" message.

symbolic procedure newnme (tnsr, ex);
begin scalar met;
  if (met := get (ex, 'generic)) then met := getmetric (mycar met);
  if (not tnsr) then
	if (not met) then tnsr := ex
	else  tnsr := makename (append (append (explode (met), explode ('!_)),
					       explode (ex)));
  if isprotect (tnsr, 2) then	% trying to overwrite, user must rem it.
    merror (mkmsg list ("% is write-protected.", tnsr), 't);
   
   % if EX is a generic object (so MET was assigned above) then it also
   % has a GENERIC prop which names the prop key to examine on the
   % metric. Note that this key is the same as that used by the gr
   % functions to find the name of the object for the current metric,
   % and that they also do a PUT on the metric. 
  if (met) then  put (met, mycdr get (ex, 'generic), tnsr);	% generic name link
  return (tnsr);
end;

change!-tnsr!-flag!* := 0;   % depth counter for nested calls

symbolic procedure change!-tnsr!-environment (tnsr);
begin scalar lex, lex1;
     change!-tnsr!-flag!* := change!-tnsr!-flag!* + 1;
     if (change!-tnsr!-flag!* eq 1) then <<
        oldcurrentmetric := currentmetric;   % save value
        lex := get (tnsr, 'altmetric) or currentmetric;
        oldcoords!* := coords!*;
        lex1 := get (tnsr, 'coords);  % 
% should check that the coords match the currentmetrics
        if not (oldcurrentmetric = lex or coords!* = lex1) then <<
          write "Temporarily changing to metric ",lex, !$eol!$,
              "and coordinates ", lex1,".",!$eol!$;
          currentmetric := lex;
          coords!* := lex1
          >>
      >> else <<  % test to be sure the envs are the same
        if not (currentmetric = (get (tnsr, 'altmetric) or currentmetric))
	  then merror (mkmsg list (
	     "environments do not match: %", tnsr), 'nil)
    >>;
end;

symbolic procedure restore!-tnsr!-environment ();
  <<
    change!-tnsr!-flag!* := change!-tnsr!-flag!* - 1;
    if (change!-tnsr!-flag!* eq 0) then <<
      if not (oldcurrentmetric = currentmetric) then
        write "Restoring metric ", oldcurrentmetric, !$eol!$,
              "and coordinates ", oldcoords!*,".",!$eol!$;
      coords!* := oldcoords!*;
      currentmetric := oldcurrentmetric   % restore value
     >> else if change!-tnsr!-flag!* < 0 then
        merror ("internal error.",'nil)
   >>;

endmodule;
;end;
