%***************************************************************************
%  FILE = sym.red
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

module 'sym;

symsgnone!* := 'nil;

% symi applies symmetry relations to an indexed object and returns
% the new object with a canonical index, or 0.

symbolic procedure symi (inp);
begin scalar lex, lex1, symsgnone!*, tnsr;
   % symi *must* not be applied to an object with pending symz ops
   % consider R[:[1,1:],a,d] :  symi will set this to 0, even though only
   % some of the terms are 0.
  if not free1 (mycaddr inp, symz!-iops!*) or
	(not mycaddr (inp) or 
     not (lex1 := get (tnsr := mycadr (inp), 'symmetry)))
%     or fixedindex (mycaddr (inp)) )  % 'splain? must be able to sym fixed indices
% this line allows syms to be applied to deriv indices even if the object
% has no symmetry of its own
     and not deriv (mycaddr (inp), 'nil)
    then return (inp);    			% no index or no symmetry.
  lex := syma (mycaddr (inp), makedifsym!* (mycaddr (inp), lex1),
	       get (tnsr, 'internal!-mapping), 
	fill!-indextype (mycaddr inp, get (tnsr, 'indextype)));  % do the index
  lex1 := formrdr (tnsr, mycar (lex));  % new form
  if mycaddr (lex) then lex1 := conjrdr (lex1);  % conjugate flag set
  if mycadr (lex) = 0 then return (0)    % sym sez 0
  else if mycadr (lex) < 0 then return (list ('minus, lex1)) % got a minus
  else return (lex1);
end;

% syma applies symmetries to a normal index, by using cnvrtindex and
% calling sym. Returns new index, sym sign, and conjugation flag.
symbolic procedure syma (indexx, symlst, internal!-mapping, indextype);
begin scalar symsgnone!*, lex;
  % indextype is just passed into cnvrtindex, so some routines pass 't instead
  % of something real. I don't think this fixat() call is needed, it is
  % taken care of by the one in mkrdr().
  if not atom (indextype) then indexx := fixat (indexx, indextype);
  if not symlst then return (list (indexx, 1, 'nil));
  if not fixedindex (indexx) then 
      symsgnone!* := 't;    % dont want 0 if diagonal and its given e.g [a,b]
  lex := full!-sym (cnvrtindex (indexx, indextype), symlst,
		    internal!-mapping);
  return (list (cnvrtindex (mycar (lex), 'nil), mycadr (lex), mycaddr (lex)));
end;

symbolic procedure full!-sym (indexx, symlist, internal!-mapping);
% This routine calls sym to do the usual symemtrization of the index with
% the symmetry list, then does the mapping indicated by internal!-mapping,
% with the required change of sign and/or conjugation flag. Output is in
% the same format as sym itself.
begin scalar lis, lex, lex1, n, repl;
   lis := sym (indexx, symlist); 		% do the usual operation
   if null internal!-mapping then return lis;		% nothing else to do
   indexx := mycar (lis);    	% the new, symmed, index
   n := length (mycaar (internal!-mapping));
   lex := head (indexx, n);	% intrinsic index part
   lex1 := mypnth (indexx, n + 1); % trailer stuff, deriative indices.
   if not fixedindex (lex) then return (lis); % cant make a match.
   if (repl := mycdr assoc (lex, internal!-mapping)) then   % found a replacement
      return list (append (mycar repl, lex1),   % rebuilt index
		mycadr (lis) * mycadr (repl),  % sign of op, or 0
	if mycadr (repl) then not mycaddr (lis) else mycaddr lis)  % conj flag
   else return (lis);
end;

% sym applies the symmetries described in the symlist to the fixed
% index supplied. 
% sym returns a list of the form (index, sign, cflag),
% where index is the canonical index, sign is the net sign of the symmetries
% applied (or 0 if they force it), and cflag indicates the need for 
% conjugation.

symbolic procedure sym (indexx, symlst);
begin scalar sgncflg, i, n, lex, bsym, lex1, vindexx;
  if not symlst then return (list (indexx, 1));

  vindexx := mkvect (length (indexx));  % define vector (index from 1)
  i := 1;
  foreach x in indexx do << putv (vindexx, i, pop indexx); i := i + 1>>;
  spread (sym1 (vindexx, symlst), vindexx, sgncflg);
  while not (i = 1) do <<
    i := i - 1;
    push (getv (vindexx, i), indexx)  % stuff index back into list form
  >>;
  return (list (indexx, car sgncflg, cdr sgncflg));
end;

fluid '(force!-sym);

% sym1 applies the symmetries to the index written in the vector vindexx.
symbolic procedure sym1 (vindexx, symlst);
begin scalar sgncflg, i, n, lex, bsym, bindex, lex1, vindexx;
  sgncflg := 1 . 'nil;
  if not symlst then return list (vindexx, sgncflg);
  bsym := symlst;
  loop:
    if atom (mycaar (symlst)) then go to afterloop;
    lex := pop (symlst);
    sgncflg := bubsrt (vindexx, mycdr (lex), sgnsym (lex),
                cnjflg (lex), sgncflg);
    if zerop (car sgncflg) then return (list (vindexx, 0 . 'nil));
  go to loop;
  afterloop:
  if mycar (symlst) then <<  	% there is also a hermitian symmetry.
    lex := hermitian (vindexx, mycdar (symlst));  % flip each pair indicated
    if force!-sym then vindexx := mycar lex   % for use by chksym()
    else if mycdr (lex) then <<	% the flip is ordered below what it was,
	 	                % has it violated the other symmetries?
% re-sym without the hermitian list, using the new vector created in hermitian
      lex1 := sym1 (mycar (lex), reverse (mycdr (reverse (bsym))));
      if mycar (lex1) = mycar (lex) then <<  % its still the same, so ok.
        vindexx := mycar lex;   % new index
        sgncflg := car sgncflg . not cdr sgncflg % hermitian means another conjugate.
      >>
    >>
  >>;
  return (list (vindexx, sgncflg));
end;

% bubsrt implements a bubble sort algorithm to sort an index into
% canonical form. bubsrt is called by sym for each independent symmetry
% the object has. the index is in a  vector, and bubsrt returns
% the net sign of the symmetrizations so far applied. 
symbolic procedure bubsrt (vindexx, lis, sgns, lsymcflg, sgncflg);
begin scalar n, i, j, k, l, sze, lex, plis, sgn, symcflg;
  sgn := car sgncflg;
  symcflg := cdr sgncflg;
  n := length (lis);		% lis = pointer list.
  i := 1;
  while not (i = n) do <<      % this is a standard algorithm.
    j := i;
    begin;
      loop:
      lex := orderindex1 (vindexx, plis := pair (mynth (lis, j),  % see if blocks are ordered
                          mynth (lis, j + 1)));
      if ((sgns < 0) and (lex = 0)) or ((sgns = 0) and not (lex = 0))
              then <<   % antisymmetry and blocks =, or diagonal and !=
                      sgn := 0;
                      i := n - 1;  % below i gets inc'ed, and we leave the while
                      lex := 1;
                      go to afterloop
              >>;
      j := j - 1;
      if not (lex = -1) then go to afterloop;	% if lex is 1 or 0 its done.
      exchange (vindexx, plis);     	% exchange blocks
      lsymcflg and (symcflg := not symcflg);   % and update the conjugate flag
      sgn := sgn * sgns;		% and update the net sign.
      if j < 1 then go to afterloop;
      go to loop;
      afterloop:
    end;
    i := i + 1
  >>;
  return (sgn . symcflg); 	% net sign and cflg so far.
end;

% hermitian applies the hermitian symmetry to an index by exchanging
% pairs of indices pointed to by the pointer list plst. if the result
% of this operation is ordered less than the original index, then
% it is returned, along with a flag set to 't to indicate that something
% was done.

symbolic procedure hermitian (vindexx, plst);
begin scalar lis, lex, i, n;
  lex := mkvect (n := upbv vindexx); % make new vector
  i := 1;
  while (i <= n) do <<putv (lex, i, getv (vindexx, i)); i := i + 1>>;  % copy elements
  exchange (lex, foreach x in plst collect car x . cadr x);
  i := 1;
  if force!-sym then return lex . 'nil;   %  for use by chksym
  loop:   % check the ordering of the new index, and report this back to sym1
    if (i > n) then goto afterloop;
    if getv (lex, i) < getv (vindexx, i) then return lex . 't
    else if getv (lex, i) > getv (vindexx, i) then return lex . 'nil;
    i := i + 1;
    goto loop;
  afterloop:
  return (lex . 'nil);
end;

% orderindex1 determines if the elements of an index pointed to
% by i and j and of size sze are canonically ordered. it returns
% -1, 0, or 1 depending on whether the i block is less than, 
% equal to, or greater than the j block, respectively.
% note that the index has been written into a vector for faster
% accessing.
symbolic procedure orderindex1 (vindexx, lis);
begin;
  % force!-sym is a fluid used by chksym to force swapping
  if force!-sym then return -1;   
  loop:
    if not lis then return (0)
    else if getv (vindexx, caar lis) < getv (vindexx, cdar lis) then return (1)
    else if getv (vindexx, caar lis) > getv (vindexx, cdar lis) then return (-1);
    popq lis;
    go to loop;
end;

symbolic procedure exchange (vindexx, lis);
begin scalar tmp;
  foreach x in lis do <<
    tmp := getv (vindexx, car x);
    putv (vindexx, car x, getv (vindexx, cdr x));
    putv (vindexx, cdr x, tmp)
  >>;
end;

% cnvrtn takes its input and does one of 3 things to it depending
% on the form of the input:
% 1. if the input is a number less than 32, the input is returned.
% 2. if the input is a number not less than 32, it is converted to
%    a character string.
% 3. if the input is a character string, it is converted to a number.
% in all cases cnvrtn (cnvrtn (input)) = input. (input is never a list). 
% essentially, the number is a decimal equivalent of the base 128 representation
% of the ascii character string. (or something like that)

symbolic procedure cnvrtn (inp);
begin scalar lex, lex1;
  % the limit of 32 is also the limit to the allowed index runs.
  if fixp (inp) and inp < 32 then return (inp)   % these are never touched.
  else if idp (inp) then <<	% input is a string.
    lex := explode (inp);
    if length (lex) = 1 then return (mascii (inp)); % single char
    lex1 := 0;
    foreach x in lex do << lex1 := lex1 * 128 + mascii (x) >>;
    return (lex1)
  >>
  else if inp < 127 then return (mascii (inp))  % result is a single char.
  else if fixp (inp) then <<
    while not (inp = 0) do <<	% chop number up to generate chars of string.
      lex := mascii (remainder (inp, 128)) . lex;
      inp := quotient (inp, 128)
    >>;
    return (makename (lex))
  >>;
end;


% in psl 3.2a this number set to 10^9 will cause illegal instructions,
% although newer psl's seem to be ok.
% This value (10^8) should still be sufficient.
offset!* := 100000000;  % used to push shifted indices around.

% cnvrtindex applies cnvrtn to a whole index to translate it to or from
% a form that sym can use (i.e strictly integer indices). the indextype list
% is only used to decide which way a shifted index will be pushed (if its
% going up, it moves left, otherwise it moves right, this is accomplished
% by adding or subtracting that huge number above to the integer equivalent
% of the indice). the presence of the indextype also acts as a flag to indicate
% which way the conversion is applied, since cnvrtindex is similar to cnvrtn;
% it goes both ways.

symbolic procedure cnvrtindex (indexx, indextype);
begin scalar lis;
  if indextype then <<   % convert from ordinary index to integer equivalent.
    while indexx do <<
      if mycar (indexx) eq '!*br or mycar (indexx) eq '!*dbr then
	lis := mycar (indexx) . lis  % no change
      else if checktype (mycar (indexx), '!*at!*) then <<  % handle shifts
        if mycar (indextype) > 0 then       % going right.
           lis := (offset!* + cnvrtn (mycadar (indexx))) . lis
        else			       % going left
           lis := (cnvrtn (mycadar (indexx)) - offset!*) . lis;
      >>
         % this handles (nthelmnt index n). i'm not sure how.
      else if not atom (mycar (indexx)) then lis := (cnvrtn (mycadar (indexx)) +
                cnvrtn (mycaddar (indexx))) . lis 
      else lis := cnvrtn (mycar (indexx)) . lis;
      if (not (atom (indextype))) then indextype := mycdr (indextype);
      indexx := mycdr (indexx);
    >>;
    return (reverse (lis));
  >>
  else <<	% convert back to normal form.
    while indexx do <<
      if mycar (indexx) eq '!*br or mycar (indexx) eq '!*dbr then
	lis := mycar (indexx) . lis  % no change
      else if mycar (indexx) < 0 then   % only negs come from move left shifts
         lis := list ('!*at!*, cnvrtn (offset!* + mycar (indexx))) . lis
      else if mycar (indexx) >= offset!* then  % move right shift.
         lis := list ('!*at!*, cnvrtn (mycar (indexx) - offset!*)) . lis
      else
         lis := cnvrtn (mycar (indexx)) . lis;	% ordinary index
      indexx := mycdr (indexx);
    >>;
    return (reverse (lis));
  >>;
end;

% indxn returns the n'th pointer group of the indep symmetry list. should be a macro.

symbolic procedure indxn (lis, n);
  mynth (lis, n + 1);

symbolic procedure roll!-sym (sym, n);
% take the pointers of each sym and roll them n places (+ to the right,
% - to the left).
   foreach x in sym collect 
        mycar x . foreach y in mycdr x collect foreach z in y collect z + n;

symbolic procedure sgnsym (lis);
% sgnsym returns the sign of the indep symmetry.
% should be a macro.
  if zerop mycaar (lis) and  symsgnone!* then 1
  else mycaar (lis);

% cnjflg returns the conjugation flag of the indep symmetry.
% should be a macro
symbolic procedure cnjflg (sym);
  mycdar (sym);


symbolic procedure multip (indexx, symlst);
% multip determines the multiplicities of a given index in the given symmetry.
% does not work for hermitian symmetries yet.
  if not symlst then 1
  else eval ('times . for each x in symlst collect multip1 (indexx, x));

symbolic procedure multip1 (indexx, symt);
begin scalar symsgnone!*, sgn, lex, len, ptr, mltp, lp, s, pf;
  symsgnone!* := 't;
  sgn := sgnsym (symt);
  ptr := mycdr (symt);
  lp := length (ptr);
  while ptr do <<
    lex := foreach x in mycar ptr collect mynth (indexx, x);
    mltp := (lex . ((mycdr (assoc (lex, mltp)) or 0) + 1)) . mltp;
    ptr := mycdr (ptr)
  >>;
  s := 0;
  pf := 1;
  while (s < lp) do <<
    lex := mycdar (mltp);
    if sgn < 0 and lex > 1 then lp := 0;  % anti-symmetry and same indices
    s := s + lex;
    pf := pf * factorial (lex);
    mltp := mycdr (mltp)
  >>;
  return (factorial (lp) / pf);
end;

% makedifsym!* constructs a symmetry list for the portion of INDEXX which follows
% the derivative operator, and appends it to the intrinsic symmetry list SYMLST
% this is done because normal dif ops are symmetric.
% used only for input canonicalization of indices by symi().
% not related, except in a general way, to makedifsym().
symbolic procedure makedifsym!* (indexx, symlst);
begin scalar lex, lex1, i;
  lex := fderiv (indexx);
  if not lex or mycadr (lex) eq '!*dbr then return (symlst)
  else if mycadr (lex) eq '!*br then <<
    i := mycar (lex) + 1;
    lex1 := fderiv (mypnth (indexx, i));
    lex1 := cons ('(1), foreach x in zpn (i,
            	i - 2 + (mycar (lex1) or (length (indexx) - i + 2)), 1)
	 collect list x);
    if length (lex1) = 2 then return (symlst);
    return (append (symlst, list (lex1)))
  >>;
end;

% ifmtsym takes the symmetry list as typed at the user level (i.e to
% mktnsr) and translates it into the internal format used.
% mappings are thus:
% ((b p1 p2 ..) --> (((b) (p1 ..) (p2 ..) ..)
% ((c b p1 p2 ..) --> ((b . t) (p1 ..) (p2 ..) ..)
% ((h p1 p2 ..)) --> ((h (p1 p1+1) (p2 p2+1) ..)) 
% where b is a block size with sign, and p1, p2, .. are pointers.
% c and h are literal characters indicating conjugate and hermitian
% repectively.
% eg. ((2 1 3) --> ((1) (1 2)(3 4));
% New internal format as of V4.1
% will also accept single syms not correctly listed: eg (1 1 2)
symbolic procedure ifmtsym (symlst);
begin;
  if not symlst then return 'nil;
  if atom car symlst then symlst := list symlst;  % wrap it properly
  symlst := foreach x in symlst collect 
	if idp (car x) then dncase car x . cdr x else x;
  symlst := foreach x in symlst collect 
	if idp (car x) then
	   if not memq (car x, '(!h !c)) then <<
		merror (mkmsg list ("Unknown symmetry key-letter %, ignored.",
			car x),'nil);
                cdr x
            >>
 	   % a hermitian sym with 1 pointer is converted into a normal sym with
	   % a conjugation
   	   else if car x eq 'h and not cddr x then 
		list ('c, 1, cadr x, cadr x +1)
           else x
        else x;
  symlst := foreach x in symlst collect <<
     if not atom (car x) then x   % already in internal format
     else if car x eq '!c then   % conjuate symmetry (cannot also be trace)
        (sign cadr (x) . 't) . foreach y in cddr x collect
		zpn (y, y + max (abs cadr x, 1) - 1, 1)
     else if car x eq '!h then
        car x . foreach y in cdr x collect << list (y, y+1)>> 
     else
       ((zerop (car x) and car x or sign car x) . 'nil) . 
	foreach y in cdr x collect
		zpn (y, y + max (abs car x,1) - 1, 1)
   >>;
  return sort!-sym symlst;
end;

symbolic procedure sort!-sym1 (lis, cmp);
begin scalar v, i, n, lex;
  if not mycdr lis then return lis;   % only 1 element
  v:= mkvect (n := (length (lis)-1));
  i := 0;
  while lis do << 
    % check for a repeat futher down, and skip if there is.
    if car lis and not member (car lis, cdr lis) then <<putv(v,i,car lis); i:=i+1>>;
     popq lis>>;
  i:= i - 1;   % how many pointers (may be < n if a repeat is removed)
  rqsort (v, 'nil, 0, i, cmp);
  lis := 'nil;
  while (i >= 0) do << push (getv (v, i), lis); i := i - 1 >>;
  return lis;
end;


symbolic procedure sort!-sym (symlst);
% ensures that all elemets of the sym lists are in the right order.
begin scalar v, i, n, lis, lex;
  % first, get pointers in order for larger groups
  symlst := for each x in symlst collect 
	mycar x . foreach y in mycdr x collect
		sort!-sym1 (y, 'lessp);
  % then get the pointer groups in order
  symlst := for each x in symlst collect 
       car x . sort!-sym1 (cdr x, 'orderindex);
  %  now order by block size, forcing hermitian to the end.
  symlst := sort!-sym1 (symlst, quote (lambda (a, b);
	  if car a eq 'h and not (car b eq 'h) then 'nil
	  else if car b eq 'h and not (car a eq 'h) then 't
	  else if length (cadr a) < length (cadr b) then 't
	  else if length (cadr a) > length (cadr b) then 'nil
	  else if caadr a < caadr b then 't
	  else 'nil));
  return symlst;
end;

symbolic procedure ufmtsym (symlst);
% converts symmetries from internal to user format (unless the subsym can't
% be specified in user format, then its left. Thats what the call to 
% ifmtsym is for below)
begin scalar lex;
 return foreach x in symlst collect <<
   lex := append (if mycar x eq 'h then list ('h)
        else if cnjflg x then list ('c, mycaar x * length mycadr x) 
	else list (mycaar x * length (mycadr x)),
	   foreach y in cdr x collect car y);
	%check if can be spec'd in u-format
   if not (x = car ifmtsym list lex) then x else lex 
  >>;
end;

symbolic procedure chksym (symlst, indextype);
begin scalar n, indexx, force!-sym, symsgnone!*, lex, lex1, lex2, s;
% note the foreach does not run if the symlst is empty
  symlst := foreach x in symlst join if not cddr x then
	<<merror (mkmsg list ("Not enough pointers in symmetry group: %",
		ufmtsym list x), 'nil); nil>> else list x;
  if not symlst then return 'nil;  % in case the above check deleted everything
  % check for overlapping pointers in an indep sym
  n := 0;  % will end up as the largest pointer
  % this is a bit stupid: we need the pair because one get destroyed by the joi
  foreach x in pair (symlst, copystruct symlst) do <<
	lex := foreach y in cddr x join y;
        while lex do << if memq (car lex, cdr lex) then
  	merror (mkmsg list ("overlapping blocks: %", ufmtsym list car x), 't)
		else n := max (n, car lex);
		popq (lex)
        >> >>;

  lex := symlst;
  s := length mycadar lex;    % block size of first group
  while not atom mycaar lex do <<  % run the sym check for groups of the same block size
     push (pop lex, lex1);
% check for repeated pointers in indep syms of the same size.
     if not (length mycadar (lex) = s) then <<
        lex1 := reverse lex1;
	lex2 := foreach x in pair (lex1, copystruct lex1) join
 	    foreach y in cddr x join y;
            while lex2 do << if memq (car lex2, cdr lex2) then
  merror (mkmsg list ("overlapping symmetries: %", ufmtsym lex1), 't);
	    popq (lex2)
          >> ;
        lex1 := 'nil;
     >>;
     s := mycadar lex
  >>;
  if lex then   % apply the hermitian
	lex2 := foreach x in pair (lex, copystruct lex) join
 	    foreach y in cddr x join y;
            while lex2 do << if memq (car lex2, cdr lex2) then
  merror (mkmsg list ("overlapping Hermitian symmetries: %", ufmtsym lex), 't);
	    popq (lex2)
          >> ;
  % the method of testing for consistency is simple: take an index and
  % apply all indep syms (i.e. swap all elements regardless of actual
  % ordering), then apply again to the result. If the original index
  % is not recovered, there is a problem. Does not catch all cases,
  % and does not detect errors in sym signs or cflgs.
  symsgnone!* := 't;
  force!-sym := 't;   % causes orderindex1 and hermitian to always force swaps
  indexx := zpn (1,n,1);   % index to swap around
  if not (mycar sym (mycar sym (indexx, symlst), symlst) = indexx) then
	merror (mkmsg list ("inconsistent nesting of symmetry: %", 
		ufmtsym symlst), 't);
  if indextype then <<
    indextype := mapindextype (indextype);   % map spinor indices.
    if not (n <= length (indextype)) then 
	merror (mkmsg list ("symmetry too big: %", ufmtsym symlst), 't);
    foreach x in symlst do <<
      lex := foreach y in cdr x	collect
	 foreach z in y collect mynth (indextype, z);
      while mycdr lex do <<
        if not (mycar lex = mycadr lex) then
   merror (mkmsg list ("symmetry group does not match index structure: %",
			ufmtsym list x), 'nil);
        pop (lex)
      >>
    >>
   >>;
  return symlst;
end;
endmodule;


module 'igen;

symbolic procedure igen (indexx, indices, symlst, internal!-mapping);
  mycar igen!-full (indexx, indices, symlst, internal!-mapping);

symbolic procedure igen!-full (indexx, indices, symlst, internal!-mapping);
begin scalar lex, lis, lis1, lex1;
  if (not indexx) or zerop (mycar (indices)) then return list ('nil) . 'nil;
  lex := igen!* (igenn (indexx, pair (mycadr indices, mycaddr indices)));
  if not lex then return 'nil;   % error exit
  foreach x in lex do <<   % errorset return is wrapped in a list
    lex1 := full!-sym (x, symlst, internal!-mapping);
    if not member (mycar lex1, lis) and not zerop (mycadr lex1) 
	then <<push (mycar lex1, lis); push (mycdr lex1, lis1)>>
  >>;
  % only need to re-sort if the index contains a fixed element,
  % but also if hermitians are involved, or internal!-mapping, 
  % so always do it.
  return sort!-indices (reverse lis, reverse lis1);
end;

symbolic procedure igen!* (lis);
begin scalar lex;
if not mycdr lis then return mycar lis;
lex := igen!* (mycdr lis);
return foreach x in mycar lis  join foreach y in lex collect
	 append (x, y);
end;

% igenn generates all the possible index values for each element of the
% index according to the value of the corresponding indextype element.
symbolic procedure igenn (indexx, indices);
begin scalar lis, lex, lex1, lex2, i;
  loop:
    if not indexx then go to afterloop;
    lex := pop (indexx);
    lex1 := pop (indices);
    if fixp (lex) then <<
       if lex < car lex1 or lex > cdr lex1 then return 'nil
       else push (list (list (lex)), lis)
    >>
   else				% pattern indice, generate possible values.
     push (igen1 (car lex1, cdr lex1), lis);
    go to loop;
  afterloop:
  return (reverse (lis));
end;

% igen1 is called from igenn to generate the list of (lists of) possible
% values for each indice. inputs are the lower and upper bounds to the
% indice run. the reason the values are in lists is so they can be appended
% together to form an index. oughta be a lambda.

symbolic procedure igen1 (n, m);
begin scalar lis;
  while not (n > m) do <<
    push (list (n), lis);
    n := n + 1
  >>;
  return ((reverse (lis)));
end;

symbolic procedure sort!-indices (indexxs, sgns);
begin scalar n, lex, lex1, ilis, slis, i;
  ilis := mkvect (n := length indexxs);
  slis := mkvect (n);
  i := 0;
  foreach x in pair (indexxs, sgns) do << 
	putv (ilis, i, car x);
	putv (slis, i, cdr x); i := i + 1>>;
  rqsort (ilis, slis, 0, n -1, 'orderindex);
  i := 0;
  while (i < n) do <<
    push (getv (ilis, i), lex);
    push (getv (slis, i), lex1);
    i := i + 1
  >>;
  return list (reverse lex, reverse lex1);
end;

% standard qsort() lifted right out of The C Prog. Lang., Chpt 4.
% The real question is why we use a bubble sort in sym, and a qsort here. 
% sort is applied to vector ilis, with slis moving in concert if defined.
symbolic procedure rqsort (ilis, slis, left, right, sortfn);
begin scalar i, last;
  if (left >= right) then return;
  swap (ilis, slis, left, (left + right) / 2);
  last := left;
  i := left + 1;
  while (i <= right) do <<
    if apply (sortfn, list (getv (ilis, i), getv (ilis, left))) then
	swap (ilis, slis, last := last + 1, i);
    i := i + 1
  >>;
  swap (ilis, slis, left, last);
  rqsort (ilis, slis, left, last-1, sortfn);
  rqsort (ilis, slis, last+1, right, sortfn);
end;

symbolic procedure swap (ilis, slis, i, j);
begin scalar lex;
  lex := getv (ilis, i);
  putv (ilis, i, getv (ilis, j));
  putv (ilis, j, lex);
  if slis then <<
    lex := getv (slis, i);
    putv (slis, i, getv (slis, j));
    putv (slis, j, lex)
  >>;
end;

endmodule;

;end;
