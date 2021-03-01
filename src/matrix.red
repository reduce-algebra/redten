%***************************************************************************
%  FILE = matrix.red
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
module 'imat;
%symbolic;
%in "$redten/decl.red"$

%put ('mdet, 'simpfn, 'simpdet);  % move  determinant function to mdet
put ('idet, 'simpfn, 'det!*);

% det* computes the determinant of the rank-2 object given. it uses
% a cofactor method. the scalar value is added to the objects property
% list under the key 'det.

symbolic procedure det!* (u);
begin scalar tnsr, lex;
  tnsr := mycar getnme (mycar (u), '(t . t), 'det);
  if not (mycar (get (tnsr, 'indices)) = 2) then
    merror (mkmsg list ("object % must have two indices.", tnsr), 't)
  else if get (tnsr, 'itype) eq 'generic then return mksq ('det . u, 1)
  else if (lex := resimpscalar (mycadr (u), tnsr, 'det))
    then return (lex); % already done
  lex := determ1 (tnsr, igen ('(a!# b!#),
			      get (tnsr, 'restricted) or get (tnsr, 'indices), 
			      'nil, 'nil));
  if not mycar (lex) then
    merror (mkmsg list ("% is a singular matrix.", tnsr), 'nil);
  put (tnsr, 'det, lex);
  cleaner ('det);
  return (lex);
end;

put ('determ, 'simpfn, 'determ!*);

% determ* computes the determinant of the given rank-2 object from the
% cofactor matrix supplied as the second argument (see cofactor).

symbolic procedure determ!* (u);
begin scalar lex, summ, lex2, tnsr, tnsr1, transflg;
  tnsr := mycar getnme (mycar (u), '(t . t), 'determ);	% object name
  tnsr1 := mycar getnme (mycadr (u), '(t . t), 'determ);	% cofactor matrix name
  transflg := mycaddr (u);		% transpose flag
  if not (mycar (get (tnsr, 'indices)) = 2) then
    merror (mkmsg list ("object % must have two indices.", tnsr), 't)
  else if (lex := get (tnsr, 'det)) then return (lex); % already done
  lex := mycar (getindices (mycar (get (tnsr, 'indextype))));
       % generate indices for top row of object.
  lex := igen (list (lex, 'a!#), get (tnsr, 'restricted) or get (tnsr, 'indices),
	       'nil, 'nil);
  summ := 'nil . 1;
  loop:	% run over top row of cofactor matrix
    if transflg then lex2 := list (mycadar (lex), mycaar (lex))	% transpose too.
    else lex2 := mycar (lex);
    if not lex then go to afterloop;
       % note: the alternating sign is incorporated in the cofactor matrix.
    summ := addsq (summ, multsq (readtnsr (tnsr1, lex2), 
                                 readtnsr (tnsr, mycar (lex))));
    lex := mycdr (lex);
  go to loop;
  afterloop:
  if not mycar (summ) then
    merror (mkmsg list ("% is a singular matrix.", tnsr), 'nil);
  put (tnsr, 'det, summ);
  cleaner ('determ);
  return (summ);
end;

put ('cofactor, 'simpfn, 'cofactor!*);

% cofactor* generates a cofactor matrix of its first argument, and places
% the result in its second. 

symbolic procedure cofactor!* (u);
begin scalar lex, lex1, lex2, tnsr, tnsr1, transflg, sgn;
  tnsr := mycar getnme (mycar (u), '(t . t), 'cofactor);	% input object
  tnsr1 := mycar getnme (mycadr (u), '(nil . t), 'cofactor);	% output name
  transflg := mycaddr (u);		% transpose flag
  if not (mycar (get (tnsr, 'indices)) = 2) then
    merror (mkmsg list ("object % must have two indices.", tnsr), 't);
  lex := igen ('(a!# b!#), get (tnsr, 'restricted) or get (tnsr, 'indices),  % generate object indices
                get (tnsr, 'symmetry), 'nil);
  lex1 := igen ('(a!# b!#), get (tnsr, 'restricted) or get (tnsr, 'indices),
		'nil, 'nil);
  mktnsr!* (tnsr1, list (-mycar (get (tnsr, 'indextype)),
            -mycadr (get (tnsr, 'indextype))), get (tnsr, 'symmetry),
            'nil, 'cofactor, mkmsg list("Cofactor matrix of %", tnsr));
  if length (lex1) = 4 then <<	% faster for 2x2 matrices
    writetnsr (tnsr1, mycar (lex1), readtnsr (tnsr, mycadddr (lex1)), 'nil);
    writetnsr (tnsr1, mycadddr (lex1), readtnsr (tnsr, mycar (lex1)), 'nil);
    writetnsr (tnsr1, mycadr (lex1), negsq (readtnsr (tnsr, mycadr (lex1))), 'nil);
    writetnsr (tnsr1, mycaddr (lex1), negsq(readtnsr (tnsr, mycaddr (lex1))), 'nil);
    return (tnsr1 . 1)
  >>;
  while lex do <<	% computes determinants of minors
    if transflg then lex2 := list (mycadar (lex), mycaar (lex))
    else lex2 := mycar (lex);
     % NOTE: the alternating sign is included in the cofactor matrix.
    if remainder (mycaar (lex) + mycadar (lex), 2) = 0 then 
      writetnsr (tnsr1, lex2, cofactor1 (tnsr, mycar (lex), lex1), 'nil)
    else 
      writetnsr (tnsr1, lex2, negsq (cofactor1 (tnsr, mycar (lex), lex1)), 'nil);

    lex := mycdr (lex)
  >>;
  cleaner ('cofactor);
  return (tnsr1 . 1);
end;

%DELETE global '(invertextension!*);
put ('invert, 'simpfn, 'invert!*);

% invert* computes the matrix inverse of the object given as input, the
% inverse goes into an object with a name of the form <name>_inv. if
% the matrix is singular, a zero divide error will occur.
% the algorithm involves the usual minor cofactor expansion.
% the inverse object has the indices raised or lowered as required, and
% is placed on the parents 'shift list, along with the proper delta fnc.

symbolic procedure invert!* (u);
begin scalar tnsr, tnsr1, lex, lex1, flg;
  tnsr := mycar getnme (mycar (u), '(nil . t), 'invert);  % should this err out?
  if not indexed (tnsr) then return (simp (list ('quotient, 1, tnsr)));
  tnsr1 := makename (append (explode (tnsr), explode (invertextension!*))); % inverse name
  lex1 := get (tnsr, 'indextype);
  % need flg to ensure a proper value when setting the deltas
  if mycar (lex1) * mycadr (lex1) > 0 then flg := 't;
  if (lex := get (tnsr, 'symmetry)) = ifmtsym '((0 1 2)) then <<
     % if its diagonal, the inverse is too and elements are reciprocals.
    mktnsr!* (tnsr1, list (-mycar (get (tnsr, 'indextype)),
            -mycadr (get (tnsr, 'indextype))), lex, 'nil, 'nil, 'nil);
    put (tnsr1, 'printname, get (tnsr, 'printname));
    put (tnsr1, 'parent, tnsr);
    lex := igen ('(a!# b!#), get (tnsr, 'restricted) or get (tnsr, 'indices),
		 lex, 'nil);
    for each x in lex do writetnsr (tnsr1, x, 
                    invsq (readtnsr (tnsr, x)), 'nil);
  >> else <<	% have to do it the long way.
    % if one index is up and the other down, transpose so a valid sum
    % can be formed that leads to a delta. if we dont do this, then the
    % contraction indices are either both up or both down.
    cofactor!* (list (tnsr, tnsr1, flg));
    put (tnsr1, 'printname, get (tnsr, 'printname));
    put (tnsr1, 'parent, tnsr);
    put (tnsr1, 'multiplier, invsq (determ!* (list (tnsr, tnsr1, flg))))
  >>;
  put (tnsr1, 'itype, get (tnsr, 'itype));
  describe!* (tnsr1, mkmsg list("Matrix inverse of %", tnsr), 'nil);
  if indexed (tnsr) eq 'mixed then lex := 'nil
  else <<    % find the appropriate delta function for a half shift.
    lex := makename (list ('!d, abs (mycar (get (tnsr, 'indextype))) + 48));
    if not flg then lex := list (makename (append (explode (lex), explode ('!_!b))),
                          makename (append (explode (lex), explode ('!_!c))))
    else lex := list (lex)
  >>;
  put (tnsr, 'shift, append (list ('nil, tnsr, tnsr1), lex));
  cleaner ('invert);
  return (tnsr1 . 1);
end;

% cofactor1 produces the indices for the current minor, and calls
% determ1 to compute the determinant of this minor. of course, determ1
% in turn calls cofactor1 to find the lower minors.
% elmnts is a list of indices describing the current minor, loc is a single
% index describing the current location, and the while loop strikes out
% all elements having a common row or column to produce a list describing
% the minor.

symbolic procedure cofactor1 (tnsr, loc, elmnts);
begin scalar lis;
  while elmnts do <<	% indices in minor
    if not (mycaar (elmnts) = mycar (loc) or mycadar (elmnts) = mycadr (loc)) then
         lis := mycar (elmnts) . lis;
    elmnts := mycdr (elmnts)
  >>;
  return (determ1 (tnsr, reverse (lis)));	% determinant of minor
end;

% determ1 computes the determinat of the minor described by the list
% of indices elmnts. when this list gets down to 4 elements, we stop the
% recursion and use the standard method for determinants.

symbolic procedure determ1 (tnsr, elmnts);
begin scalar lex, n, lex1, sgn, summ;
  if length (elmnts) = 4 then    % minor is 2x2
     return (addsq (multsq (readtnsr (tnsr, mycar (elmnts)),
        readtnsr (tnsr, mycadddr (elmnts))), negsq (multsq (
        readtnsr (tnsr, mycadr (elmnts)), readtnsr (tnsr, mycaddr (elmnts))))));
     
  sgn := 1;
  n := mycaar (elmnts);
  lex := elmnts;
  summ := 'nil . 1;
  while n = mycaar (lex) do <<	% multiply value by cofactor element of minor.
    lex1 := readtnsr (tnsr, mycar (lex));
    if mycar (lex1) then
      summ := addsq (summ, multsq (multsq ((sgn . 1), lex1),
		cofactor1 (tnsr, mycar (lex), elmnts)));
    lex := mycdr (lex);
    sgn := -sgn		% alternating sign for minor expansion.
  >>;
  return (summ);
end;

put ('mtrace, 'simpfn, 'simptrace);     % move matrix trace function.
put ('trace, 'simpfn, 'trace!*);

% trace* computes the trace of the rank-2 object given. 

symbolic procedure trace!* (u);
begin scalar tnsr, lex, lex1;
  tnsr := mycar getnme (mycar (u), '(t . t), 'trace);
  if not (mycar (get (tnsr, 'indices)) = 2) then
    merror (mkmsg list ("object % must have two indices.", tnsr), 't)
  else if get (tnsr, 'itype) eq 'generic then return mksq ('trace . u, 1);
  lex := igen ('(a!# b!#), get (tnsr, 'restricted) or get (tnsr, 'indices),
	       ifmtsym '((0 1 2)), 'nil);
  lex := 'plus . for each x in lex collect mk!*sq (readtnsr (tnsr, x));
  return (simp (lex));
end;

endmodule;
;end;
