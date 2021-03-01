%***************************************************************************
%  FILE = shift.red
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
module 'shift;
%symbolic;
%in "$redten/decl.red"$

flag ('(shift), 'opfn);     % parsing declaration.

symbolic procedure shift (u);  % user interface to shift routine.
  shift!* (u, 'nil);    % flag is off,  make a new object. (reverse this meaning)

% shift* recursively decends into an expression, applying shift**()
symbolic procedure shift!* (inp, flg);
begin scalar lex, neg;
  if atom inp then return inp
  else if checktype (inp, 'rdr) then return shift!*!* (inp, flg);
  return foreach x in inp collect shift!*(x, flg);
end;

% shift** is the routine which computes or finds the shifted objects
% generated from a parent indexed object.
% if flg is off and the requested object does not exist, it will be
% created, otherwise shift* returns an unevaluated form.
% Nov 2009 JFH
% this will accept a deriv index and ignore it, passing it back, but there
% should not be a shift on the deriv index - that's taken out in preprocess
symbolic procedure shift!*!* (inp, flg);
begin scalar tnsr, indexx, indexb, indext, lex, indextype, lis, tnsr1, tnsr2, tnsrp,
       gen, neg, lex1;
  if free1 (mycaddr (inp), '(!*at!*)) then return (inp);  % no shifts
  tnsr :=  resolvegeneric mycadr (inp);
  if not flg and get (tnsr, 'subobj) then <<
     inp := 'rdr . apply ('resolve!-subobj, mycdr inp);
     return shift!* (symi inp, flg)
  >>;
  if get (tnsr, 'generic) then    % should return unevaled
      flg := 't;   % let it look (useful for metric, connected to delta)
    % conjugate shift of parent of conjugate object.
%  if mycdr (lex := get (tnsr, 'conjugate)) then 
%    return (conjrdr (shift!* (list ('rdr, mycar (lex), 
%                mycaddr (inp), mycadddr (inp)), flg)));
  tnsrp := get (tnsr, 'parent) or tnsr;		% parent name of the object.
  indexx := mycaddr (inp);
  % this is the base index, ie that which matches the rank of the object
  % indexx could be longer if there are derivs, we ingore those here and pass them back out
  indexb := head (indexx,  mycar get (tnsrp, 'indices));
  indext := mypnth (indexx, mycar get (tnsrp, 'indices)+1); % this is the part of the index after the base
%write "indexb = ", indexb, !$eol!$;  
  if not indexb then return ('nil);
  flg := mycar (get (tnsrp, 'shift)) or flg; % cant shift if car of shift is 't
  lex := shftc (indexb, fill!-indextype (indexb, get (tnsr, 'indextype))); % generate a new indextype, 
                                               % and clear the index of shifts.
  indexb := mycar (lex);
  indextype := mycadr (lex);
  if (tnsr neq tnsrp) then  % the index was not symmed properly based on the symmetries of the parent
    <<
	lex := genshft (indexb, indextype, get (tnsrp, 'indextype));
	return shift!* (symi list ('rdr, tnsrp, lex), flg)
    >>;
	
      % look for an object that matches, or the nearest.
  lex := shftfnd (tnsrp, head (indextype, mycar get (tnsrp, 'indices)));
                % why this? don't we just want the index of the object, leaving out the derivs	
		% - but thats just the head to the object rank.. 2009 JFH
                %(mycar fderiv (indexx) or (length
		%(indexx)+ 1) - 1)));    % cut the index back to the part that matters
  indexx := append (indh (indexb), indext);  % output index, no shift ops in base, deriv part left as is.
%write "indexx = ", indexx, " ",indexb," ",mycadddr (inp),!$eol!$;
  
  if not mycadr (lex) then return (list ('rdr, mycar (lex), indexx, mycadddr (inp)))
  else if flg then return (inp);   % found it, or cant make it.
%write "still here!",!$eol!$;
  % check the altmetric prop on tnsrp and upgrade it to include the 
  % currentmetric if parts are missing.
  lex1 := foreach x in pair (get (tnsrp, 'altmetric), currentmetric) collect
              car x or cdr x;
  foreach x in getfam (tnsrp) do put (x, 'altmetric, lex1);
  change!-tnsr!-environment (tnsrp);
  tnsr1 := mycar (lex);
  lex := mkshft (tnsr1, mycadr (lex)); % generate metric contractions.
  tnsr2 := mkshftnme (tnsrp, indextype, get (tnsrp, 'indextype)); % new name
  mktnsr!* (tnsr2, indextype, new!-symmetry (get (tnsrp, 'symmetry), indextype),
	    'nil, get (tnsrp, 'itype), mkmsg list("Shifted from %", tnsrp));
%  put (tnsr2, 'symmetry, new!-symmetry (get (tnsrp, 'symmetry), indextype));
  tabprint (list ("computing ", tnsr2));
  
  evaltnsr1 (tnsr2, mycar (lex), mycadr (lex), 'nil); % generate elements
  put (tnsr2, 'indextype, indextype);
  put (tnsr2, 'parent, tnsrp);     % give it a parent
  put (tnsr2, 'printname, get (tnsrp, 'printname) or tnsrp);  % and a print name
  protect!* (tnsr2, 'w);            % protect it and the parent
  protect!* (tnsr, 'w);
%  put (tnsr2, 'itype, get (tnsrp, 'itype));
  put (tnsrp, 'shift, append (append (list ('nil, tnsrp), % add offspring to the
         mycddr (get (tnsrp, 'shift))), list (tnsr2))); % parent list
  restore!-tnsr!-environment ();
  cleaner ('shift);
  return (list ('rdr, tnsr2, indexx, mycadddr (inp)));
end; 

% mkshft generates a times list of the given object and metric contractions
% in the slots indicated.


symbolic procedure mkshft (tnsr, slot);
begin scalar indexx, indexo, indextype, i, k, indice, lex, lex1,
                value, altmet;
  indextype := get (tnsr, 'indextype);
  indexo := indexx := head (alphalist!*, 
                     i := mycar (get (tnsr, 'indices)));
  value := list ('rdr, tnsr, indexx) . value;
  altmet := get (tnsr, 'altmetric);
  i := i + 1;
  while slot do <<
    k := mycar (slot);
    slot := mycdr (slot);
    % the environment has been chnaged to the almet of the parent object.
    lex := getmetric (mynth (indextype, k));
%    lex := getmetric!* (mynth (indextype, k), altmet, 't);
%    lex := mynth (altmet,k) or getmetric (mynth (indextype, k));   % get appropriate metric
    indice := mynth (alphalist!*, i);    % get contraction indice
    value := list ('rdr, lex, 
               list (mynth (indexx, k), indice)) . value;
    indexo := insert (indexo, indice, k, 't);  % replace output indice
    i := i + 1
  >>;
  if not altmet then put (tnsr, 'altmetric, currentmetric);
  return (list (indexo, 'times . reverse (value)));
end;

% shftc takes an index with shift operators and a indextype list and
% return a list of the clean index and the indextype list generated by
% the shifts.
symbolic procedure shftc (indexx, indextype);
begin scalar lex, lex1;
  while indexx and indextype do <<
    if checktype (mycar (indexx), '!*at!*) then <<  % shift op
      lex := (-1 * mycar(indextype)) . lex;
      lex1 := mycadar indexx . lex1
%      push (-pop (indextype), lex);
%      push (mycadr pop (indexx), lex1)
    >> else <<			% normal indice
      lex := mycar indextype . lex;
      lex1 := mycar indexx . lex1
%      push (pop (indextype), lex);
%      push (pop (indexx), lex1)
    >>;
   indexx := mycdr indexx;
   indextype := mycdr indextype
  >>;
  return (list (append (reverse (lex1), indexx), reverse (lex)));
end;

% shftfnd locates an object which most nearly matches the one we
% are looking for by searching through the *at* property list on
% the parent. it returns the name of the closest relative and a list
% of pointers to where metric contractions must be made to get to the
% object we want. if the pointer list is empty, the object we want
% already exists.

symbolic procedure shftfnd (tnsr, indextype);
begin scalar lex, lex1, lex2, lex3, lis, flg;
  lex := get (tnsr, 'shift);% list of all existing offspring, parent name 1st
  flg := mycar (lex); 
  lex := mycddr (lex);
  lex1 := tnsr;
  lex2 := cmpindextype (indextype, get (tnsr, 'indextype)); % compare indextype lists
  while lex do <<  % check all remaining objects in list.
    if not indexed (mycar (lex)) then lex := mycdr (lex) % drop deleted object names
    else if length (lex2) > length (lex3 :=  % found a closer match
                cmpindextype (indextype, get (mycar (lex), 'indextype))) then <<
      lex1 := mycar (lex);
      lex2 := lex3;
      lis := mycar (lex) . lis;
      lex := mycdr (lex)
    >> else <<
      lis := mycar (lex) . lis;
      lex := mycdr (lex)
    >>
  >>;
  put (tnsr, 'shift, append (list (flg, tnsr), lis)); % reset offsping list
  return (list (lex1, lex2));  % name and pointers
end;

% cmpindextype compares indextype list element by element and returns a list
% of pointers to where they differ.

symbolic procedure cmpindextype (ex, ex1);
begin scalar lex, k, lex2;
  k := 1;
  while ex do <<
    if (lex := mycar ex) then		% a real index, not an op
    <<
      if not (lex = mycar (ex1)) then lex2 := k . lex2;
      ex1 := mycdr ex1;
      k := k + 1     % position does not include any index ops.
    >>;
    ex := mycdr ex
  >>;
  return (reverse (lex2));
end;

% genshft takes an index and 2 indextype lists and returns an index
% with shift ops written in where the indextype lists differ.
% it's like shftc in reverse.

symbolic procedure genshft (indexx, indextype1, indextype2);
begin scalar lis;
  while indexx do <<
    if mycar (indextype1) = mycar (indextype2) then lis := mycar (indexx) . lis
    else lis := list ('!*at!*, mycar (indexx)) . lis;
    indextype1 := mycdr (indextype1);
    indextype2 := mycdr (indextype2);
    indexx := mycdr (indexx)
  >>;
  return (append (reverse (lis), indexx));
end;


% mkshftnme generates a unique name based on the parent name and
% the difference between the parent indextype list and the offspring
% indextype list expressed as a base 16 number. its kinda complex to
% explain here. (well where else?)
% indextype1 is the child, indextype2 is the parent
fluid '(!*longshift);  % this is a switch
  % if t then names are made in the _udud form indicating which is up or down
!*longshift := 'nil;

symbolic procedure mkshftnme (tnsr, indextype1, indextype2);
begin scalar lis, lex;
  if !*longshift then
    if indextype1 = indextype2 then return tnsr 
    else return (makename (append (append (explode (tnsr), explode ('!_)), 
	foreach x in indextype1 collect if x >0 then '!u else '!d)));
  lis := cmpindextype (indextype1, indextype2);
  if not lis then return (tnsr);
  lex := 0;
  while lis do <<  % build a number to rep tail of name.
    lex := lex + expt (2, mycar (lis) - 1);
    lis := mycdr lis
  >>;
  while not (lex = 0) do <<  % convert above number to lowercase chars.
    lis := mascii (remainder (lex, 16) + offspringextcase!*) . lis;
%    lis := "!!" . lis;  % makename will do it ok now.
    lex := quotient (lex, 16)
  >>;
  return (makename (append (append (explode (tnsr), explode ('!_)), lis)));
end;

% new!-symmetry constructs the symmetry list for the new object from the
% parent symmetry. 

symbolic procedure new!-symmetry (sym, indextype);
  foreach x in sym join (new!-symmetry1 (x, indextype));

% new!-symmetry1 looks at each independent symmetry and sees if any part of it
% survives having indices shifted.

symbolic procedure new!-symmetry1 (sym, indextype);
begin scalar len, lex, sgn, cblk, lex1, cflg, ex1, herm;
  if atom (mycar (sym)) then  herm := 't
  else <<
    sgn := sgnsym (sym);    	% sign of block
    cflg := cnjflg (sym)           % conjugate flag
  >>;
  sym := mycdr (sym); 		% pointer list
    % for each pointer, create an assoc pair with the appropriate sublist
    % of the indextype as the key, and the pointer as the value. if a pair
    % with the same key exists, append the pointer to those already there.
    % note we dont delete the old pair, hence the member test below.
  foreach x in sym do <<
    lex := mapindextype (foreach y in x collect mynth (indextype, y));
    cblk := (lex . append (mycdr (assoc (lex, cblk)), list (x)))
                        . cblk
  >>;
  % all pairs with 2 or more pointer sets are valid independent symmetry lists
  % can't hermitian have just 1 pointer pair? (or is that just a regular sym?)
  while cblk do <<
    if not member (mycaar (cblk), lex1) and mycddar (cblk) then
      if herm then push (('h . mycdar (cblk)), ex1)
      else push (((sgn . cflg) . mycdar (cblk)), ex1);
    push (mycar pop(cblk), lex1)
  >>;
  return (ex1);
end;

put ('altmetric, 'simpfn, 'altmetric!*);

symbolic procedure altmetric!* (u);
% set the alternate metric for the first arg to the second arg.
% If the second arg is nil return the altmetric, if it is an integer, remove
% the altmetric name for the kind of index.
begin scalar tnsr, met, lex;
  tnsr := mycar getnme (mycar (u), '(t . t), 'altmetric);
  if not (met := mycadr (u)) then <<
     write !$eol!$, get (tnsr, 'altmetric), !$eol!$;
     return (tnsr . 1)
  >> else if not fixp (met := reval met) then <<
	  met := mycar getnme (met, '(t . t), 'altmetric);
	  if get (met, 'itype) neq 'metric or % need the covariant metric
	     (lex := mycar (get (met, 'indextype))) > 0 then
	    merror (mkmsg list ("bad metric: %.", met), 't)
  >> else <<   % if a number is given, remove the alt definition for that type
     lex := abs met;
     met := 'nil
  >>;
  put (tnsr, 'altmetric, insert (get (tnsr, 'altmetric), met, abs lex, 't));
  return (tnsr . 1);
end;

symbolic procedure fixat (indexx, indextype);
% fixat assumes the indextype has been filled with fill!-indextype.
begin scalar op, x, lis;
  while indextype do 
   <<
     x := mycar indexx; indexx := mycdr indexx;
     if (op := mycar checktype (x, shift!-iops!*)) then
       <<
         if (op eq '!*at!*) then lis := x . lis
         else if (op eq '!*at!+ and mycar (indextype) < 0) then 
		lis := list ('!*at!*, mycadr x) . lis
         else if (op eq '!*at!- and mycar (indextype) > 0) then
		lis := list ('!*at!*, mycadr x) . lis
         else lis := mycadr x . lis
       >> else lis := x . lis;
       indextype := mycdr indextype;
    >>;
  return append (reverse lis, indexx);
end;

endmodule;
;end;
