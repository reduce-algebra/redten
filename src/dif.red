%***************************************************************************
%  FILE = dif.red
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
module 'idif;
%symbolic;
%in "$redten/decl.red"$

flag ('(cov lie pdf odf), 'indexedfn);    % 

% idiff handles the derivative operations indicated in the object index
% by successively applying the operations indicated. idiff is called only
% from preprocess.

fluid '(dfindex!*);

symbolic procedure idiff (tnsri, indexx, flg);
begin scalar lex, dfindex!*, indexo;
  lex := mycar fderiv (indexx);   % loc of first deriv op
  indexo := head (indexx, lex - 1);
  dfindex!* := mypnth (indexx, lex);

  % the first cov deriv index on a scalar can be changed to an ordinary deriv
  if not indexo and mycar (dfindex!*) eq '!*dbr then <<
    dfindex!* := '!*br . mycdr (dfindex!*);
    if mycaddr (dfindex!*) and mycaddr (dfindex!*) neq '!*dbr and 
            mycaddr (dfindex!*) neq '!*br then
      dfindex!* := append (head (dfindex!*, 2), '!*dbr . mycddr (dfindex!*))
  >>;
  loop:
    if not dfindex!* then goto afterloop;
    lex := getdfindex!* ();
    if mycdr (lex) then <<    % doing cov deriv, one at a time
      tnsri := cov!* (tnsri);
      if not indexed (tnsri) then return (tnsri)      % got 0
    >> else <<   % doing ordinary derivs, in bunches.
      % only if required do we construct a full object, otherwise it is
      % more efficient to allow the odf to be filled on the fly, since
      % usually only some parts are required.
      if (deriv (dfindex!*, 'nil)) or flg then 
        tnsri := mycar simpodf!* (list (tnsri)) % more ops coming, build df fully
      else return ndiff (tnsri, indexo, mycar (lex))
    >>;
    indexo := append (indexo, mycar lex);
  goto loop;
afterloop:
  return (list ('rdr, tnsri, indexo));
end;

symbolic procedure getdfindex!* ();
begin scalar lex;
  if checktype (dfindex!*, '!*dbr) then <<
    lex := list (mycadr dfindex!*) . 't;   % one cov index and flag
    dfindex!* := mypnth (dfindex!*, 3);   % rest of index after cov index
    if not checktype (dfindex!*, '(!*br !*dbr)) and dfindex!*
	then dfindex!* := '!*dbr . dfindex!*; % with #dbr stuck back on for next time
    return lex
  >> else <<
   lex := '();
   begin; loop: % recall, loops can't be in group statements (well, goto's actually)
     dfindex!* := mycdr dfindex!*;  
     if not dfindex!* or checktype (dfindex!*, '!*dbr) then goto afterloop;
     % skip repeat operator
     if checktype (dfindex!*, '!*br) then goto loop;
     lex := mycar dfindex!* . lex;
     goto loop;
   afterloop:
    end;
    return reverse lex . 'nil
  >>;
end;

unfluid '(dfindex!*);

% ndiff handles ordinary derivatives of indexed objects. 

symbolic procedure ndiff (tnsri, indx, indxd);
begin scalar lis, lex, lex1, lex2, i, tnsrp;
  % note, the only use of the temp coords is for processvalue to check index
  % strucuture, the are never read out by simpodf**().
  lex := mkcoords!*!* (tmpnames(), 'nil);		% coordinate vector
%  put (lex, 'indextype, '(-1));            % fudge the indextype to get it covariant
  lis := 'odf!* . lis;			% unevaled form begins with 'odf*
  %find parent of derivative chain and rewrite in terms of that
  tnsrp := tnsri;
  i := 0;
  while lex1 := mycadr get (tnsrp, 'odf) do << tnsrp := lex1; i := i + 1>>;
  % transfer i indices from the end of indx to the front of indxd
  lex1 := indx;
  indx := head (lex1, length (lex1) - i);
  indxd := append (mypnth (lex1, length (lex1) - i + 1), indxd);

  protect!* (tnsrp, 'w);  % protect parent so changes will cause an error message
  put (tnsrp, 'odfmsg, 
       mkmsg list ("Update or remove derivatives after changing %.", tnsrp));

  if not indx and not indexed (tnsrp) then lis := tnsrp . lis  % scalar derivative
  else lis := list ('rdr, tnsrp, indx) . lis;  % put the object in

  while indxd do <<			% all the deriv indices
    lis := list ('mrdr, lex, list (mycar (indxd))) . lis;
    indxd := mycdr (indxd)
  >>;
  lis := reverse (lis);
return lis;
end;

put ('odf, 'simpfn, 'simpodf!*);

symbolic procedure simpodf!* (u);
begin scalar tnsrp, tnsrd, n, lex, lex1, lex2, i;
  tnsrp := mycar getnme (mycar u, '(t . t), 'odf);
  if get (tnsrp, 'itype) eq 'generic then return mksq ('odf . u, 1)
  else if not indexed tnsrp then return 'nil . 1;
%  if mycdr (lex := get (tnsrp, 'conjugate)) then 
%      return (mycar get (mycar (simpodf!* (list (mycar (lex)))), 
%			  'conjugate) . 1);
  i := 0;
% find parent to take deriv of
  while lex1 := mycadr get (tnsrp, 'odf) do << tnsrp := lex1; i := i + 1>>;
  n := (mycadr u or 1) + i;
  protect!* (tnsrp, 'w);  % protect parent so changes will cause an error message
  put (tnsrp, 'odfmsg, 
       mkmsg list ("Update or remove derivatives after changing %.", tnsrp));
  change!-tnsr!-environment (tnsrp);    % change metrics and coords

  tnsrd := find!-odf!-name (tnsrp, n);
  tabprint (list ("computing ", tnsrd));

% cannot return here if indexed as it may be incomplete.
  lex := igen (head (alphalist!*, car get (tnsrp, 'indices)),
	get (tnsrp, 'restricted) or get (tnsrp, 'indices), get (tnsrp, 'symmetry),
	get (tnsrp, 'internal!-mapping));
  if not lex then lex := list 'nil;   % index for an indexed scalar
  lex1 := igen (head (alphalist!*, n), indexlim (cnstn(-1, n)),
	if n = 1 then nil else ifmtsym list (1 . zpn (1, n, 1)), 'nil);
  while lex do <<   % for each parent index
    lex2 := lex1;
    while lex2 do <<  % for each deriv index
      get!-odf!-val (tnsrp, car lex, tnsrd, car lex2);  % recursive value finder
      lex2 := cdr lex2
   >>;
   lex := cdr lex
  >>;
  restore!-tnsr!-environment ();
  fast!-writetnsr!-cleanup();
  % protect parent and all derivs previous to this one.
  tnsrp := tnsrd;
  while tnsrp do 
    <<protect!* (tnsrp, 'w); tnsrp := mycadr (get (tnsrp, 'odf))>>;
  if cleaner ('odf) then remflag (list tnsrd, 'nodir);  % if user asked for it then make it visible

  return tnsrd . 1;
end;

put ('odf!*, 'simpfn, 'simpodf!*!*);

symbolic procedure simpodf!*!* (u);
begin scalar lex, tnsrp, n, indx, indxd;
  lex := car u;
  tnsrp := mycadr lex;
  indx := mycaddr lex;

  indxd := foreach x in cdr u collect caaddr x; % derivative indices joined together
  n := length (indxd);
  % recursive value finder
  return get!-odf!-val (tnsrp, indx, find!-odf!-name (tnsrp, n), indxd);
end;

symbolic procedure get!-odf!-val (tnsrp, indx, tnsrd, indxd);
begin scalar lex, prv, n, !*read!-undef!-flag!*;
  !*read!-undef!-flag!* := 't;  % so readtnsr() returns nil, not <undefined>.
  spread (resolve!-subobj (tnsrp, indx), tnsrp, indx);
  tnsrd := mycar get (tnsrd, 'subobj) or tnsrd;   % just in case
  n := length (indxd);
  if not (lex := readtnsr (tnsrd, append (indx, indxd))) then <<
     % no value, must get val from prev object and diff it (recursively)
     prv := mycadr (get (tnsrd, 'odf));
     lex := simpdf (list (reval mk!*sq get!-odf!-val (tnsrp, indx, prv,
		 head (indxd, n - 1)), 
	mynth (coords!*, mynth (indxd, n) + 1 - caaddr getindextype (-1))));
     fast!-writetnsr (tnsrd, append (indx, indxd), lex, 'nil)
   >>;
   return lex;
end;

symbolic procedure find!-odf!-name (tnsrp, n);
begin scalar i, cur, prv, nxt, lex1;
  i := 1;
  cur := tnsrp := mycar get (tnsrp, 'subobj) or tnsrp;
  prv := 'nil; % name of prev object, nxt is name of next object
  while i <= n do <<
    if not indexed (nxt := mycaddr (get (cur, 'odf))) then <<
       % next df is not made, must make it and reset 'odf prop
       nxt := makeextname (tnsrp, '!_!D!F, i);
       mktnsr!* (nxt, append (get (tnsrp, 'indextype), cnstn (-1, i)),
	     makedifsym (get (tnsrp, 'symmetry), car get (tnsrp, 'indices), i),
	     'nil, 'odf,
	     mkmsg list("order % derivative of %", i, tnsrp));
       put (cur, 'odf, list (i-1, prv, nxt));
       put (nxt, 'odf, list (i, cur, 'nil));
       put (nxt, 'printname, get (tnsrp,'printname));
       flag (list nxt, 'nodir);
% should use full!-igen and resticted set from tnsr.
       lex1 := igen (head (alphalist!*, car get (nxt, 'indices)),
	     get (nxt, 'indices), get (nxt, 'symmetry), 'nil);
       put (nxt, 'tvalue, pair (lex1, mapcar (lex1, 'atom))); % nil values.
%       subobj!-odf()  % call only if a new object is made
    >>;
    i := i + 1;
    prv := cur;
    cur := nxt
  >>;
  return nxt;
end;


symbolic procedure makedifsym (symlst, rn, n);
% constructs a new symmetry for a derivative object of order n
% rn is rank of parent
begin scalar lex, lis, symsgnone!*;
  symsgnone!* := 't;   % makes sgnsym() regard 0 size as 1
  if n = 1 then return symlst;
  lex := '(1) . foreach x in zpn (rn + 1, rn + n, 1) collect list x;
% run down over the size 1 symmetries.
  while symlst and length cadar symlst = 1 do  push (pop symlst, lis);
  return append (append (reverse lis, list lex), symlst);
end;

symbolic procedure makeextname (tnsr, ext, n);
begin scalar lex;
  lex := append (explode (tnsr), explode (ext));
  if n > 1 then lex := append (lex, explode (n));
  return makename (lex);
end;

flag ('(cov), 'opfn);     % parsing declaration.

symbolic procedure cov (inp);
begin scalar lex, neg;
  if checktype (inp, 'minus) then <<neg := 't; inp := mycadr (inp)>>
  else if checktype (inp, 'rdr) or idp (inp) then neg := 'nil
  else merror (mkmsg list ("invalid input: %.", inp), 't);
  if atom inp then inp := resolvegeneric inp;
  lex := cov!* (inp);
  return ((neg and list ('minus, lex)) or lex);
end;

% cov* computes covariant derivatives of objects (tensors and spinors,
% there is no christoffel symbol for frame indices???). If the object
% is shifted from a parent, then the covariant derivative of the parent
% is computed and shifted to match the object.
symbolic procedure cov!* (u);
begin scalar tnsr, tnsrd, lex, lex1, lex2, lex3, lex4, n, lis, indexx, 
	symlst, tnsrp, ord;
%  tnsr := getnme (reval (mycar (u)), 't, 'cov);
% cannot use getnme because it evals shifts and we want to catch them here.
   u := reval  u;  
   if atom u then tnsr := u
   else <<   % is an rdr form.
     tnsr := mycadr u;
     indexx := mycaddr u;
     symlst := mycadddr u
   >>;
  if get (tnsr, 'generic) then 
         merror (mkmsg 
            list ("cannot compute cov deriv of generic object: %.", 
	     tnsr), 't);  % error exit
  if not indexed (tnsr) then return ('nil);  % why was this commented out?

  tnsrp := get (tnsr, 'parent) or tnsr;
  lex1 := indexx and mycadr shftc (indexx, get (tnsr, 'indextype)) 
	or get (tnsr, 'indextype);
  n := mycar (get (tnsr, 'indices));
  if lex1 neq get (tnsrp, 'indextype) or 
      tnsrp neq tnsr then <<	% input is not parent, i.e. its shifted
    lex := cov!* (tnsrp);
    if lex eq 'nil then tnsrd := 0
    else tnsrd := mycadr (shift!* (list ('rdr, lex,	% shift to match
             genshft (head (alphalist!*, n + 1), 
                     get (lex, 'indextype), %indextype of cov parent.
                     append (lex1, list (-1)))),
                        'nil));
%    put (tnsr, 'cov, tnsrd);	% store name or value on object
    return (tnsrd)
  >> else <<  % we do not need this else!
    if mycdr (lex := get (tnsr, 'conjugate)) then % cov is a real op
      return (mycar (get (mycar (cov!* (mycar (lex))), 'conjugate)));

    if (lex := mycaddr get (tnsr, 'cov)) and (indexed (lex) or lex = 0) then
      return (lex);		% name or value already computed
    ord := 1;
    if indexed (tnsr) eq 'scalar then 
      % the cov of a scalar is just the ordinary df
      tnsrd := mycar simpodf!* (list (tnsr))
    else <<      
      tnsrp := tnsr;   % find original object in chain of covs
    % find parent to take deriv of
      while lex1 := mycadr get (tnsrp, 'cov) do << tnsrp := lex1; 
		ord := ord + 1>>;
   
      tnsrd := makeextname (tnsrp, '!_!C!D, ord);
      tabprint (list ("computing ", tnsrd));
      lex := head (alphalist!*, n or 0);
      lex1 := mynth (alphalist!*, n + 1);
      lex2 := append (lex, list (lex1));
  
      change!-tnsr!-environment (tnsr);    % change metrics and coords
      lex4 := foreach x in get (tnsr, 'indextype) collect abs (x);
      lex4 := foreach x in defindextype!* collect 
	 memq (mycadr x, lex4) and mynth (x, 5) and apply (mynth (x, 5), 'nil);
  
      lex3 := 'plus .		% generate expression for derivative
	    list ('rdr, tnsr, append (lex, list ('!*br, lex1)))
		 . difcon (tnsr, lex4, lex, list (lex1));
      mktnsr!* (tnsrd, append (get (tnsr, 'indextype), '(-1)),
		get (tnsr, 'symmetry), 'nil, 'cov,
		mkmsg list("Order % covariant derivative of %", ord, tnsrp));
      put (tnsrd, 'printname, tnsrp);
      evaltnsr1 (tnsrd, lex2, lex3, 'nil);
      restore!-tnsr!-environment ()
    >>;
    if length (get (tnsrd, 'tvalue)) = 0 then <<
      kill!* (tnsrd);
      tnsrd := 0	% is 0
    >> else <<
      protect!* (tnsrd, 'w);
      % fix printname, except for cov of scalar, leave as a df
%      if not mycar (get (tnsrd, 'indices)) = 1 then put (tnsrd, 'printname,
%	 makeextname (get (tnsrp, 'printname), '!_!C!D, ord));
      put (tnsrd, 'cov, list (ord, tnsr, 'nil))	% store name or value on object
    >>;
    put (tnsr, 'cov, list (ord-1, mycadr get (tnsr, 'cov), tnsrd));	% store name or value on object
    cleaner ('cov);
    return (tnsrd)
  >>;
end;

% difcon creates a list of contractions with various christoffel symbols
% provided in ltnsr1 for use by the covariant derivative routine. the object
% name is tnsr, its index is index, and the covariant derivative index
% is index1.

symbolic procedure difcon (tnsr, ltnsr1, indexx, index1);
  begin scalar i, lex, lis, indextype;
  if not indexx then return ('nil);	% scalar (?), no contractions
  indextype := get (tnsr, 'indextype); 
  i := 1;
  while indextype do << 		% do for each index of the object
    if (lex := difcon1 (i, mycar (indextype), tnsr, ltnsr1, indexx, index1))
      then lis := lex . lis;	% there is a contraction, add it to the list
    i := i + 1;			% pointer to contraction indice
    indextype := mycdr (indextype)
  >>;
  return (reverse (lis));
end;

% difcon1 creates a product of an object and a contraction with
% a christoffel symbol in the given index.
% note all christoffel symbols used here (second tensor kind and
% spinor) have an index structure (+ - -).

symbolic procedure difcon1 (n, cn, tnsr, ltnsr1, indexx, index1);
begin scalar lex, lex2;
  lex2 := insert (indexx, '!#1, n, 't);	% contraction indice
  if not (lex := mynth (ltnsr1, abs (cn)+1)) then return ('nil) % no op
  else if cn > 0 then		% contravariant indice
    return (list ('times, list ('rdr, tnsr, lex2), 
      list ('rdr, lex, 
      append (list (mynth (indexx, n), '!#1), index1))))
  else				% covariant indice
    return (list ('minus, list ('times, 	% with change of sign
       list ('rdr, tnsr, lex2),
       list ('rdr, lex,
       append (list ('!#1, mynth (indexx, n)), index1)))));
end;

put ('lie, 'simpfn, 'lie!*);

% lis* computes the lie derivative of the given object in the direction
% of the given vector. if the object
% is shifted from a parent, then the lie derivative of the parent
% is computed and shifted to match the object.

symbolic procedure lie!* (u);
begin scalar tnsr, vec, tnsr1, lex, lex1, lex2, lex3, lex4, n, lis;
  tnsr := mycar getnme (mycar (u), '(t . t), 'lie);
  if get (tnsr, 'itype) eq 'generic then return mksq ('lie . u, 1);
  vec := mycar getnme (mycadr (u), '(t . t), 'lie);
  if not (mycar (get (vec, 'indices)) = 1) then
    merror (mkmsg list ("% is not a vector.", vec), 't);
  if mycdr (lex := get (tnsr, 'conjugate)) then
    return (mycar (get (lie!* (list (mycar (lex), vec)), 'conjugate)));
  n := mycar (get (tnsr, 'indices));
  tnsr1 := makename (append (append (explode (tnsr), explode (vec)),
                            explode ('!_lie)));
  tabprint ( list ("computing ", tnsr1));
  change!-tnsr!-environment (tnsr);
  if mycar (get (vec, 'indextype)) < 0 then 	% need contravariant vector
    vec := mycadr (shift!* (list ('rdr, vec, '((!*at!* a!#))), 'nil));
  lex := head (alphalist!*, n or 0);
   % converts a trace sym into a normal sym
  mktnsr!* (tnsr1, get (tnsr, 'indextype), subst (1, 0, get (tnsr, 'symmetry)),
                'nil, 'nil, mkmsg list("Lie derivative of %", tnsr));
  lex3 := 'plus . list ('times, 
                  list ('rdr, tnsr, append (lex, '(!*br !#1))),
		  list ('rdr, vec, '(!#1)))
  		  . ldifcon (tnsr, vec, lex);

  evaltnsr1 (tnsr1, lex, lex3, 'nil);
  restore!-tnsr!-environment ();
  protect!* (tnsr1, 'w);
  cleaner ('lie);
  return (tnsr1 . 1);
end;

% ldifcon creates a list of contractions with the vector tnsr1.

symbolic procedure ldifcon (tnsr, tnsr1, indexx);
begin scalar i, lex, lis, indextype;
  if not indexx then return ('nil);
  indextype := get (tnsr, 'indextype);
  i := 1;
  while indextype do <<
    if (lex := ldifcon1 (i, mycar (indextype), tnsr, tnsr1, indexx)) then <<
       lis := lex . lis;
       indextype := mycdr (indextype)
    >>;
    i := i + 1
  >>;
  return (reverse (lis));
end;

% ldifcon1 generates the contractions for each indice of the object whose
% lie derivative is being computed (tnsr) with the indices of the vector's
% derivative.

symbolic procedure ldifcon1 (n, cn, tnsr, tnsr1, indexx);
begin scalar lex, lex2;
  lex2 := insert (indexx, '!#1, n, 't);
  if cn > 0 then		% contravariant index
    return (list ('minus, list ('times,
		list ('rdr, tnsr, lex2),
	   list ('rdr, tnsr1, list (mynth (indexx, n), '!*br, '!#1)))))
  else				% covariant index
    return (list ('times,
		list ('rdr, tnsr, lex2),
	   list ('rdr, tnsr1, list ('!#1, '!*br, mynth (indexx, n)))));
end;

put ('df, 'specprn, 'printdif);	% attach the print function
put ('df, 'prifn, 'printdif);	% attach the print function for 3.3

% printdf is not strictly part of the tensor system, (although it has a
% required hook for indexed objects) but is intended to pretty-up 
% the output of Reduce derivative forms.
% In reduce 3.4 code is provided in dfprintfn() for this.

symbolic procedure printdif (u);
begin;
  if free1 (u, '(rdr mrdr)) then <<
    if !*fancydf then return prindf!-fancy (u)
    else if reduce!-version = 34 then return dfprintfn (u)>>;
  if (mycar (u) eq 'df) then u := mycdr (u);	% kill name in 3.3+
  if !*nat and checktype (mycar (u), '(rdr mrdr)) then return (iprtdf (u)) % hook for indexed obj
  else if !*nat and not free1 (mycdr u, '(mrdr)) then return prindf!-fancy ('df . u);
  % throw a newline if args to big to fit. 
  if (flatsizec (u) - 2) > (linelength (nil) - 10 - posn!*) then terpri!* ('t);
  if not !*nat then prin2!* ('df!();	% dont pretty print
  maprint (mycar (u), 0);			% print object
  if not !*nat then prin2!* (',);
  u := mycdr (u);
  ycoord!* := ycoord!* - 1;
  if ycoord!* < ymin!* then ymin!* := ycoord!*;
  while mycdr (u) do <<			% print derivs subscripted (nat on)
    prin2!* (mycar (u));
    prin2!* (",");
    u := mycdr (u)
  >>;
  prin2!* (mycar (u));
  if not !*nat then prin2!* ('));
  ycoord!* := ycoord!* + 1;
  if ycoord!* > ymax!* then ymax!* := ycoord!*;
end;

symbolic procedure prindf!-fancy u;
begin scalar lex, lex1, n, lis;
  u := cdr u;  % skip fn name
  lex1 := car u;  % this is the guy who is being df'd
  n := 0;   % this many times (determined below)
  u := cdr u;
  while u do <<
    if fixp mycadr u then <<
        lis := list ('noop, 'd, list ('expt, mycar u, mycadr u)) . lis;
        n := n + mycadr u;
        u := mycddr u
    >> else <<
       lis := list ('noop, 'd, mycar u) . lis;
       n := n + 1;
       u := mycdr u
    >>
  >>;
  if n = 1 then lex1 := list ('noop, 'd, lex1)
  else lex1 := list ('noop, list ('expt, 'd, n), lex1);
  maprin (list ('quotient, lex1,
		'noop . reverse lis));
end;

%this exists to print several args side-by-side.
put ('noop, 'prifn, 'nooppr);

symbolic procedure nooppr (u);
begin;  % set up so that a space is not printed after the last arg
  u := cdr u;   % eat op
  while mycdr u do <<
     maprin mycar u; 
     prin2!*(" ");
     u := mycdr u
  >>;
  maprin mycar u;  % last arg
end;

% iprtdf is the pretty-print routine for derivatives of indexed objects.
% this is only used when implicit objects have had derivatives taken that
% necessarily remain unevaluated.

symbolic procedure iprtdf (u);
begin scalar tnsr, indexx, difl, difi, i;
  tnsr := mycadar (u);		% object name
  indexx := mycaddar (u);		% object index
  u := mycdr (u);			% deriv wrt these
  while u do <<			% look at each deriv name
    i := look (coords!*, mycar (u), mycar (getindices(1)));
    if not i then difl := mycar (u) . difl	% not a coord name
    else <<	% is a coordinate name, use an index from the coord vector.
      if fixp (mycadr (u)) then <<	% repeat count
        difi := append (cnstn (i, mycadr (u)), difi);
        u := mycdr (u)
      >>
      else difi := i . difi	% only 1
    >>;
    u := mycdr (u)
  >>;
  if difi then indexx := append (indexx, '!*br . reverse (difi));
  if not difl then return (printrdr (list ('rdr, tnsr, indexx)));
  prin2!* ("df (");	% need to messy-print the non-coord derivs.
  printrdr (list ('rdr, tnsr, indexx));
  prin2!* (",");
  prin2!* (reverse (difl));
  prin2!* (")");
end;

%
% apply df to indexed objects
%

symbolic procedure dfrdr (ex1, indet);
% indet can now be an indexed object
begin scalar lex;
    if checktype (indet, 'rdr) and not (get (mycadr indet, 'itype) 
                eq 'coordinates) then <<
		merror (mkmsg list
	 ("% not of itype coordinates.", mycadr indet), 'nil);
	 return 'nil
    >>;
    if checktype (ex1, 'df) then <<
        if not (lex := dfrdr (mycadr (ex1), indet)) then return ('nil);
        if mycar (lex) eq 'df then return ('df . (mycadr (lex) .
% derad gets the deriv ops in a canonical order
			 derad (mycaddr (lex), mycddr (ex1))))
        else return ('df . (lex . mycddr (ex1)))
    >> else if not checktype (ex1, 'rdr) then
   % only way to be here is if the indet is indexed
        if memq ('nil,
         foreach x in coords!* collect (depends (ex1, x) eq 'nil)) then
	return list ('df, ex1, 'mrdr . cdr indet)
        else return 'nil;
    if fixedindex (mycaddr (ex1)) and get (mycadr (ex1), 'implicit) then <<
        % added to get df's of unevaled generics to remain unevaled.
	if get (mycadr (ex1), 'generic) then return dfrdrmerge (ex1, indet)
        else if not depends (mycadr (ex1), indet) then return ('nil)
    >>;
    return (dfrdrmerge (ex1, indet));
end;

% this function merges the derivative ops applied to an indexed object
% via a call to df. The ops are sorted by SYMI if they are members of the
% coordinates. 

symbolic procedure dfrdrmerge (form, indet);
begin scalar lex; integer i;
   % merge things if form is not an implicit object with a fixed index,
    % and either indet is a coord or is itself indexed
   if (not (fixedindex (mycaddr (form)) and get (mycadr (form), 'implicit))
          and memq (indet, coords!*)) or checktype (indet, 'rdr) then <<
       if checktype (indet, 'rdr) then
          i := mycar mycaddr indet  % coord index
       else i := look (coords!*, indet, mycar (getindices(1)));
       lex := reverse (mycaddr (form));
       if (mycadr (fderiv (lex)) eq '!*br) then
           return (mycar (fkern (symi (list ('rdr, mycadr (form),
                    append (mycaddr (form), list (i)))))))
       else
	   return (mycar (fkern (list ('rdr, mycadr (form), append (mycaddr (form), 
                              list ('!*br, i))))))
   >> else return (list ('df, form, indet));
end;

put ('pdf, 'simpfn, 'simppdf);

symbolic procedure simppdf (u);
begin scalar exp, indexx;
  exp := mycar (u);
  indexx := mycadr u;
  if atom (indexx) or mycar (indexx) neq 'findex then
    merror (mkmsg list ("% invalid as index.", 
			index!-string indexx), 't);
  indexx := mycar stripops (cdr indexx, '(!*dbr !*br));
  if not free1 (indexx, symz!-iops!*) then 
		return simp!* symz!*!* ('pdf . u);
  indexx := mycar syma (indexx, 
	makedifsym ('nil, 0, length (indexx)), 'nil,
	 fill!-indextype (indexx, 'nil));
  exp := reval (exp);
  if fixedindex (indexx) then
	  return (simp  ('df . (exp . foreach x in indexx
	collect mynth (coords!*, x + mycar getindices(1)+1))))
  else return (mksq (list ('pdf, exp, 'findex . indexx), 1));
end;

put ('pdf, 'specprn, 'printpdf);	% attach the print function
put ('pdf, 'prifn, 'printpdf);	% attach the print function for 3.3

symbolic procedure printpdf (u);
begin scalar lex;
  if (mycar (u) eq 'pdf) then u := mycdr (u);	% kill name in 3.3 
  lex := '!*br . mycdadr u;
  if not !*nat then <<
    prin2!* (base!-case!-string "PDF(");
    maprint (mycar (u), 0);
    prin2!* (", ");
    print!-index (lex, 'nil);   % dont care about indextype with nat off
    prin2!* (")")
  >> else <<
    prin2!* ("(");
    maprint (mycar (u), 0);
    prin2!* (")");
    print!-index (lex, fill!-indextype (lex, 'nil));
  >>
end;

% If we call this routine, then INDEXX has a normal derivative operator,
% does not have a covariant derivative op, and has an integer index.
% This routine converts the k[0,|1] form to the df ((RDR k (0)), t) form
% If tnsr is generic, an unevaled op is returned. v3.15
symbolic procedure cnvrtdif (tnsr, indexx);
begin scalar lex, lex1, tnsrd;
    % if tnsr is still generic, someone typed eg R[1,2,1,2,|1] before 
    % making any objects. The generic name has not been resolved yet.
    if get (tnsr, 'generic) then return list ('qrdr, tnsr, indexx);
    lex := fderiv (indexx);
    lex1 := mypnth (indexx, mycar (lex) + 1); % deriv index
    tnsrd := find!-odf!-name (tnsr, length (lex1)); % df name
    lex := get!-odf!-val (tnsr, head (indexx, mycar (lex) - 1), tnsrd, lex1);
    fast!-writetnsr!-cleanup();
    return mk!*sq lex;
end;

endmodule;
;end;
