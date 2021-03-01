%***************************************************************************
%  FILE = indexed.red 				
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
module 'indexed;
%symbolic;
%in "$redten/decl.red"$

flag ('(mktnsr mkobj), 'opfn);  % make it directly callable 
indexed!-names := '();

symbolic macro procedure mkobj (u); list ('real!-mktnsr, mkquote u);
symbolic macro procedure mktnsr (u); list ('real!-mktnsr, mkquote u);

%global '(depl!*);  % is this always global? (No)

symbolic procedure real!-mktnsr (u);
% accepts a list of names and maps mktnsr**() over them.
begin;
  u := mapcar (mycdr u, 'eval);  % eval args and skip funtion name
  terpri ();
  if atom mycar u then mktnsr!*!* (u)
  % loop over multiple input names
  else foreach x in mycar u do mktnsr!*!* (append (list x, mycdr u));
end;

global '(last!-input!-to!-mkobj);

% mktnsr** is the sub-user level routine that accepts information about the
% structure of an indexed object that is to be created (by mktnsr*)
% mktnsr** displays an indexed form to show exactly what was created.

symbolic procedure mktnsr!*!* (u);
begin scalar lex;
  % this test is also in mktnsr*(), but we do it here for the bare decl done below.
      % its got a value or dependencies or is used
      % used!* flag includes avalue and depends, but we have a choice as to how to proceed
  if (mycar u) neq last!-input!-to!-mkobj and %repeat call, override switch
     !*mkobjsafe and (get (mycar u, 'avalue) or (not indexed (mycar u) and
          (assoc (mycar u, depl!*) or flagp (mycar u, 'used!*)))) then <<
     last!-input!-to!-mkobj := mycar u;
     merror (mkmsg list ("% is already in use.", car u), 't)
  >>;
  % if there is only one arg, make a bare declaration. To make a scalar 
  % requires typing the '() for the empty indextype list.
  last!-input!-to!-mkobj := mycar u;
  if onep (length (u)) then <<
%     remprop (lex := mycar (u));	% kill all props. 
     mysetprop (lex := mycar (u), 'nil);   % kill all props.
     put (lex, 'simpfn, 'mkrdr);
     flag (u, 'full)   % U is already LIST (LEX)
  >> else
    lex := mktnsr!* (mycar (u), inject!-obj (mycadr (u), 'indextype),
 			 ifmtsym (inject!-obj (mycaddr (u), 'symmetry)), 
		     % implicit is always set to obj name in user call
		     mycadddr (u) and mycar(u),
          base!-case!-name mycadddr (mycdr (u)), mycadddr (mycddr (u)));   % have mktnsr* make the thing
  if lex then <<
    printrdr list ('rdr, lex, 
	foreach x in head (alphalist!*, car get (lex, 'indices))
		collect car explode x);
    terpri!* ('t)
   >>;
    return ('nil)              % but theres no return value.
end;

% mktnsr* is the primitive routine which builds the structure for
% an indexed object. it returns the name of the object.
% the indextype list describes the index structure.
% positive values are contravariant, negative are covariant.
% If INDEXTYPE is nil, a scalar object is made

symbolic procedure mktnsr!* (tnsr, indextype, sym, imp, type, desc);
begin scalar lex, lavalue, killed!*;
  tnsr := mycar getnme (tnsr, '(nil . t), 'mktnsr);
  % we must test here for calls to mktnsr* from user callable routines
      % its got a value or dependencies or is used
  if tnsr neq last!-input!-to!-mkobj and %repeat call, override switch
      !*mkobjsafe and (get (tnsr, 'avalue) or (not indexed (tnsr) and
          (assoc (tnsr, depl!*) or flagp (tnsr, 'used!*)))) then
     merror (mkmsg list ("% is already in use.", tnsr), 't);
  if (get (tnsr, 'generic)) then 
         merror (mkmsg list ("% is no longer a generic object.", tnsr), 'nil);
  if indexed (tnsr) and not kill (tnsr) or flagp (tnsr, 'reserved) then << 
    merror (mkmsg list ("cannot create object: %", tnsr), 'nil); 
    return ('nil)
  >>;
  if indextype and atom indextype or memq ('nil, for each x in indextype 
			     collect atom (x)) then
      merror (mkmsg list ("invalid indextype % for %.", 
			  indextype, tnsr), 't);
  lavalue := get (tnsr, 'avalue);    % save in case it is a scalar
  mysetprop (tnsr, 'nil);   % kill everything about this object
  remprop (tnsr, 'avalue); % a bizarre bug, see Changelog for july 3,1991.
  put (tnsr, 'simpfn, 'mkrdr);	% simplification function
  put (tnsr, 'indexed, 't);   % so indexed() will say yes even if this aborts early
  flag (list (tnsr), 'full);	% causes name to be passed to mkrdr too.
  set (tnsr, tnsr);		% so we can use unquoted name.
  sym := chksym (sym, indextype);
  put (tnsr, 'symmetry, sym);

  lex := getindices (1);
  if coords!* and not (length (coords!*) = (mycadr (lex) -
          mycar (lex) + 1)) then
     merror (mkmsg list ("coord-indextype mis-match %, %.",
			 coords!*, lex), 'nil);
  put (tnsr, 'indices, indexlim (indextype));  % place other properties
  put (tnsr, 'indextype, indextype);
  put (tnsr, 'coords, coords!*);
  put (tnsr, 'altmetric, currentmetric);  % save metric environment
  put (tnsr, 'altconnection, currentconnection);
  put (tnsr, 'multiplier, 1 . 1);
  put (tnsr, 'itype, type);
  put (tnsr, 'printname, tnsr);
  describe!* (tnsr, desc, 'nil);   % does error checking
%  flag (list (tnsr), 'reserved);

  if imp and (not atom (imp) or (not fixp (imp) and not (imp eq tnsr)
     and (not indexed (imp) or not (get (imp, 'indextype) = indextype)))) then
    merror (mkmsg list ("bad implicit value: %, %", imp, tnsr), 'nil)
  else <<
    put (tnsr, 'implicit, imp);
    if (imp eq tnsr) then  % is implicit and must depend on coords
      for each x in coords!* do depend1 (tnsr, x, 't)
  >>;  

  indextype := foreach x in indextype collect mycar (getindextype (abs x));
  lex := mycar (indextype);
  indextype := mycdr (indextype);    % find out what to place under 'indexed prop
  indextype := foreach x in indextype collect lex eq x;
  if memq ('nil, indextype) then lex := 'mixed
  else if not lex then lex := 'scalar;

  put (tnsr, 'indexed, lex);
  mkconj (tnsr);  % if it's a spinor or dyad, make its conjugate
  indexed!-names := tnsr . indexed!-names;		% add this object to the list

  % save avalue for scalar object.
  if not get (tnsr, 'indextype) and lavalue then <<
     % in 3.3 there is an atomic indicator (eg SCALAR) in the avalue
     % I don't know what other values it can have, but anything other than
     % scalar will probably break something.
     if mycar (lavalue) eq 'scalar then lex := mycdr (lavalue)
     else lex := lavalue;
     writetnsr (tnsr, 'nil, simpcar (lex), 't)   % move the value (3.3)
  >> else put (tnsr, 'tvalue, 'nil);		% and give a nil value
  return (tnsr);
end;
 
%unglobal '(last!-input!-to!-mkobj);

% mkconj is called by mktnsr* to generate a conjugate object for a spinor or
% dyad. 
% The conjugate is really a subobject of the parent,
% and a flag so printrdr can put a bar over the name. it never
% has a 'tvalue, since its elements are obtained by conjugating the elements
% of the parent spinor.
% Any kind of object may be passed to mkconj(), but only those with an
% indextype in the conjugateindextypes!* list will have a conjugate created.

symbolic procedure mkconj (tnsr);
begin scalar lex, tnsr1, indextype, verbose!*;
  indextype := get (tnsr, 'indextype);

  % if there are no spinor or dyad indices, leave
  if not indextype or not memq ('t, foreach x in indextype 
	       collect pairp (assoc (x, conjugateindextypes!*))) then return;
  % if this is a subobj, it our conjugate already formed by mktnsr, this
  % prevents an infinite loop
  if get (tnsr, 'itype) eq 'subobj then return;
  tnsr1 := makename (append (explode (tnsr), explode ('!_cnj))); % name of conjugate
  if indexed (tnsr1) and not kill (tnsr1) then
    merror (mkmsg list ("cannot create conjugate %.",
			tnsr1), 't);
  lex := head (alphalist!*, car get (tnsr, 'indices));  
  subobj!*!* (tnsr1, lex, tnsr, lex, 1 ./ 1, 't);   % make the conjuate
  put (tnsr1, 'indextype, foreach x in indextype join 
     list (mycdr assoc (x, conjugateindextypes!*) or x) );

  put (tnsr1, 'printname, get (tnsr, 'printname));
  put (tnsr, 'conjugate, tnsr1 . 'nil);
  put (tnsr1, 'conjugate, tnsr . 't);
  flag (list (tnsr1), 'nodir);	% so directories don't get too cluttered.
end;

symbolic procedure inject!-obj (lis, prop);
% This routine is used in mktnsr() to inject the properties of a named
% indexed object into params of the object being created, either the
% indextype or symmetry. lis is the user input and prop is the property key 
% in question.
begin scalar lex;
  if indexed lis then return get (lis, prop)
  else if atom lis then return nil
  else while lis do <<
    if indexed mycar lis then lex := append (reverse get (mycar lis, prop),
						 lex)
    else lex := mycar lis . lex;
    lis := mycdr lis
  >>;
  return reverse lex;
end;

% chkindex determines whether the integers in an index are in
% the range described by the 'indices property of the object.
% it returns 't or 'nil depending on what it finds.

symbolic procedure chkindex (indexx, indices);
begin scalar lex, lex1, lex2;
  if not indices then return ('nil);
  lex := mycadr (indices);     % upper bound
  lex1 := mycaddr (indices);   % lower bound
  lex2 := indexx;
  loop:
    if (not indexx) or (not lex) then return ('t);  % got all the way through
    if fixp (mycar (indexx)) and (mycar (lex) > mycar (indexx) or
            mycar (indexx) > mycar (lex1)) then     % number out of range
        return ('nil);
    indexx := mycdr (indexx);
    lex := mycdr (lex);
    lex1 := mycdr (lex1);
    go to loop;
end;

% indexlim creates the 'indices property of an indexed object.
% it returns a list of the form (rank (lower-bound) (upper-bound)).
% rank is obvious; the bounds are created by placing the appropriate 
% index runs in each list.

symbolic procedure indexlim (indextype);
begin scalar lex, lex1, n, lex2;
  n := length (indextype);    	% this is the rank
  while indextype do <<
    lex2 := getindices (mycar (indextype));   % index run for this slot.
    indextype := mycdr (indextype);
    lex := mycar (lex2) . lex;
    lex1 := mycadr (lex2) . lex1
  >>;
  return (list (n, reverse (lex), reverse (lex1)));
end;

flag ('(indexed), 'opfn);   % user and lisp callable

symbolic procedure indexed (ex1); % determines if an object is indexed.
  idp (ex1) and get (ex1, 'indexed);

symbolic procedure isittype (tnsr, typ);
% determine if the object has indices entirely of type TYP.
begin;
  if indexed (tnsr) eq 'scalar then	% handle scalars separately 
    if typ eq 'scalar then return ('t)
    else return ('nil);
  if memq ('nil, 
    foreach x in get (tnsr, 'indextype) collect mycar getindextype (abs x)
	 eq typ) then return 'nil
  else return 't;
end;

put ('rdr, 'conjfn, 'conjrdr);
put ('qrdr, 'conjfn, 'conjrdr);

% conjrdr determines the conjugate object for a spinor by looking
% for the conjugate property.

symbolic procedure conjrdr (u);
begin scalar lex, lex1, tnsr;
  if (lex := mycar (get (tnsr := mycadr (u), 'conjugate))) then <<
    if not indexed (lex) then <<  % some dummy rem'ed it, make it again.
      merror (mkmsg list ("missing conjugate for % being created.", tnsr), 'nil);
      mkconj (tnsr)
    >>;
    lex1 := (list (mycar (u), lex, mycaddr (u), mycadddr (u)));
    return (lex1)
  >>
  else return (list ('cnj, u));
end;

!*xeval := 'nil;       % flag for extra simplification in readtnsr
!*read!-undef!-flag!* := 'nil;  % makes readtnsr return <undefined>

% readtnsr is the primitive routine which reads indexed object values.
% it accesses the assoc list which is the object tvalue, and returns 
% the result.

symbolic procedure readtnsr (tnsr, indexx);
begin scalar indx, pos, tensor, lex, mltp, val, cflg;
  spread4 (resolve!-subobj (tnsr, indexx), tnsr, indexx, mltp, cflg);
  if ((lex := get (tnsr, 'restricted)) and not chkindex (indexx, lex)) then
    return ('nil . 1);   % can't access outside the restricted range

%  if mycdr (lex := get (tnsr, 'conjugate)) then
%    return (cnjsq (readtnsr (mycar (lex), indexx)));  % we always read the parent 
% and return the conjugate of that value. conjugate objects never have 'tvalues.


  indx := full!-sym (indexx, get (tnsr, 'symmetry),
		     get (tnsr, 'internal!-mapping)); % apply symmetry to index
  if mycadr (indx) = 0 then return ('nil . 1);   % sym sez 0
  mltp := multsq (mltp, mycadr (indx) ./ 1);
  % need an xor for this
  cflg := if mycaddr indx then not cflg else cflg;
  if pos := mycdr assoc (mycar indx, get (tnsr, 'external!-mapping))
	then return cmv!* (readtnsr (mycar pos, mycadr pos),
		 multsq (mltp, mycaddr pos), 
		if mycadddr pos then not cflg else cflg);
     % why not use tvalue()?
  pos := assoc (mycar (indx), get (tnsr, 'tvalue));    % get the value

  if pos then <<
    if not mycdr pos then val := 
	<<if !*read!-undef!-flag!* then 'nil else 
              simp makename explode "<undefined>">>
    else
      val := multsq (mltp, mycdr (pos));

%  add aeval and resimp for substitutions here...
     % get out quickly if no defined value
    if not val and !*read!-undef!-flag!* then return 'nil
    else if !*xeval then
       return (cv!* (simp!* (list ('!*sq, val, 'nil)), cflg))
    else return (cv!* (val, cflg))
  >>
  else if not (lex := get (tnsr, 'implicit)) then return ('nil . 1)
  else if fixp (lex) then return (multsq (mltp, (lex . 1)));
  mltp := mycadr (indx) . 1;
  if lex neq tnsr then 
    return (cv!* (multsq (mltp,
               simp (list ('rdr, lex, mycar (indx)))), cflg))
  else return (cv!* (multsq (mltp,
               simp (list ('qrdr, lex, mycar (indx)))), cflg));
end;

% writetnsr is the primitive routine which writes values into an
% indexed object. it returns the value written (not necessarily the
% value input). if flg is on, then the index will not be sym'ed (i.e
% its already in canonical form).

symbolic procedure writetnsr (tnsr, indexx, value, flg);
begin scalar pos, indx, tensor, val, lex, mltp, cflg;
  if get (tnsr, 'subobj) then flg := 'nil;
  if not isprotect (tnsr, 2) then  % if it is protected, then dont resolve
				% and let it err out below
  spread4 (resolve!-subobj (tnsr, indexx), tnsr, indexx, mltp, cflg);
  if ((lex := get (tnsr, 'restricted)) and not chkindex (indexx, lex)) then
    return ('nil . 1);   % can't access outside the restricted range

% conjugate objects don't have values, we write the conjugate value
% to the parent object.
%  if mycdr (lex := get (tnsr, 'conjugate)) then
%    return (writetnsr (mycar (lex), indexx, cnjsq (value), flg));

  if isprotect (tnsr, 2) then <<
    merror (mkmsg list ("% is write-protected.", tnsr), 'nil);
    if get (tnsr, 'odfmsg) then merror (get (tnsr, 'odfmsg), 'nil);
    return readtnsr (tnsr, indexx)  % return what is there. is this ok?
  >>;
  tensor := get (tnsr, 'tvalue);  % value list

  if flg then indx := list (indexx, 1)  % apply symmetries if flg is nil.
  else indx := full!-sym (indexx, get (tnsr, 'symmetry),
			  get (tnsr, 'internal!-mapping));
  if mycadr (indx) = 0 then return ('nil . 1);  % sym sez 0
  cflg := if mycaddr indx then not cflg else cflg;
  mltp := multsq (mltp, mycadr (indx) ./ 1);
  if pos := mycdr assoc (mycar indx, get (tnsr, 'external!-mapping))
	then return writetnsr (mycar pos, mycadr pos, cqv!* (value,
		multsq (mltp, mycaddr pos),
		if mycadddr pos then not cflg else cflg),  'nil);
  pos := fndcmp (tensor, mycar (indx));
  val := cqv!* (value, mltp, cflg);
  if mycadr (pos) then <<
% 0 looks like nil . 1;
    if not mycar val and not get (tnsr, 'implicit) then
      put (tnsr, 'tvalue, insert (tensor, 'nil, mycar (pos), 't))
    else
      put (tnsr, 'tvalue, insert (tensor, mycar (indx) . val, mycar (pos), 't));
    return (val)
    >>
  else if not mycar (val) and not get (tnsr, 'implicit) then
    return ('nil)
  else if not tensor then <<
    put (tnsr, 'tvalue, list (mycar (indx) . val ));
    return (val)
  >>
  else if mycar (pos) > length (tensor) then <<
    put (tnsr, 'tvalue, append (tensor, list (mycar (indx) . val)));
    return (val)
  >> else <<
    put (tnsr, 'tvalue, insert (tensor, mycar (indx) . val, mycar (pos), 'nil));
    return (val)
  >>;
end;

% fndcmp (FiND CoMPonent) is called by writetnsr to locate the
% position where an element is to be placed in the value list of
% an object. it returns a list of the form (pos, flg) where
% flg indicates if the element already exists (and thus should be
% overwritten), and pos is the location of that element, or the location
% of the element that will preceed the one we are writing.

symbolic procedure fndcmp (tnsr, indexx);
begin scalar knt;
  knt := 1;     % position counter
  loop:
    if (not tnsr) then return (list (knt, 'nil))  % ran off end, append.
    else if indexx = mycaar (tnsr) then return (list (knt, 't)) % is there
    else if orderindex (indexx, mycaar (tnsr)) then  % isnt there
        return (list (knt, 'nil));
    knt := knt + 1;
    tnsr := mycdr (tnsr);
  go to loop;
end;

% cv* either returns a conjugate value or just the value, depending on the
% flag. should be a macro.

symbolic procedure cv!* (value, flg);
  if flg then cnjsq (value)
  else value;

symbolic procedure cmv!* (val, mul, cflg);
if cflg then cnjsq multsq (val, mul)
else multsq (val, mul);

symbolic procedure cqv!* (val, mul, cflg); 
if cflg then cnjsq quotsq (val, mul)
else quotsq (val, mul);

put ('protect, 'formfn, 'protect);  % somehow prevents evaluations

% protect is the user interface for protect*

symbolic procedure protect (lis, vars, mode);
<<
  if (mycar(lis) eq 'protect) then lis := mycdr (lis);	% kill name in 3.3 
  protect!* (mycar (lis), mycadr (lis))
>>;

symbolic procedure protect!* (tnsr, key);
begin;
  % if user quotes args
%  if listp (tnsr) and mycar (tnsr) eq 'quote then tnsr := mycadr tnsr;
%% ya but nil is listp and then it doesnt do anything.
%  if listp (key) and mycar (key) eq 'quote then key := mycadr key;
  tnsr := mycar getnme (tnsr, '(t . t), 'protect);
%  IF NOT INDEXED (TNSR) THEN RETURN (NIL);
  if memq (key, '(!W !w)) then key := 2
  else if memq (key, '(!K !k)) then key := 3
  else if memq (key, '(!K!W !W!K !k!w !w!k)) then key := 6
  else if key then key := get (tnsr, 'protection)   % to avoid screw-ups 
  else key := 'nil;
  put (tnsr, 'protection, key);
  put (tnsr, 'odfmsg, 'nil);    % get rid of message
  return (tnsr);
end;

% isprotect checks for a particular type of protection on an object.
% values for N mean:
% 2 -- write protected
% 3 -- kill protected
% 6 -- write and kill protected
% see protect*

symbolic procedure isprotect (tnsr, n);
  remainder (get(mycar getnme (tnsr, '(nil . t), 'isprotect), 'protection) or 5, n) = 0;


generic!-names := 'nil;

% this routine puts the minimum set of properties on the generic names
% so that they can be parsed. INDEXTYPE is the defining list for the object, 
%  FLG is the type of metric to check for the generic link and the prop 
% key for the link , eg '(1 . RIEMANN).
% INDEXTYPE and SYM are the usual things, and CONFN is a construction 
% function that creates the real object, eg riemann().
% The lookup is made in RESOLVEGENERIC, actual generic refs are created by
% NEWNME .

symbolic procedure makegeneric (tnsr, flg, indextype, sym, confn);
begin scalar coords!*;  % coords are nil for making generics, so no depends
  mktnsr!* (tnsr, indextype, ifmtsym sym, tnsr, 'generic, "Generic name");
  indexed!-names := mycdr (indexed!-names);   % pop this name off the list, mktnsr just put it there
  generic!-names := tnsr . generic!-names;    % but put it on the list of generics.
  put (tnsr, 'generic, flg);  % type of metric and prop key for generic link
  put (tnsr, 'protection, 6);		% full delete and write protection 
%  put (tnsr, 'coords, 'nil);		% remove coords 
  if getd (confn) then put (tnsr, 'constructfn, confn);	% function to create real object with  
  protect!* (tnsr, 'w);       % if no generic refs, prevents writing to tnsr
  return tnsr					% return name 
end;

% This routine is used to 
% determine if the name of the object is generic and should be 
% replaced by looking at the current metric.

symbolic procedure resolvegeneric (tnsr);
begin scalar met, lex, lex1, met, confn, i, parent;
  if not idp (tnsr) then return (tnsr)
  else if not indexed (tnsr) then <<
     % it might be a non-indexed generic ref to a shifted object.
     % Look for the parent
    lex := explode (tnsr);
      % check for !* is for pattern match code
    if (i := (look (lex, '!_, 0) or look (lex, '!*, 0))) eq 'nil then
	return (tnsr);
    if mynth (lex, i) eq '!! then i := i - 1;
    parent := head (lex, i);
    if not parent then return (tnsr);
    parent := makename (parent);
    if not indexed (parent) or not get(parent, 'generic) then return (tnsr);
    return (makename (append (explode (resolvegeneric (parent)),
	 mypnth (lex, i+1))))
  >>
  else if not (lex1 := get (tnsr, 'generic))
	   then return (tnsr);	% no op
  lex := get (met := getmetric!* (mycar lex1, currentmetric, 'nil), mycdr lex1);
  if (not lex) then
    % construct if there is a metric and we are inside evaltnsr1
    if (teneval!* and met and (confn := get (tnsr, 'constructfn)))
        then lex := mycar apply (confn, '(nil));
  return (indexed (lex) and lex or tnsr);
end;

put ('generics, 'simpfn, 'generics!*);

symbolic procedure generics!* (u);
begin scalar lex;
  if not atom u and not mycar (u) then u := 'nil;
  foreach x in u or generic!-names do <<
%     write x; spaces (8 - flatsizec (x));
%     write ((lex := resolvegeneric (x)) eq x) and "     " or " --> ",
%       (lex eq x) and "no target" or lex, !$eol!$
     prin2!* x; posn!* := posn!* := 8;
     lex := resolvegeneric x;
     prin2!* mkmsg list ("%%", lex eq x and "     " or " --> ",
       (lex eq x) and "no target" or lex);
     terpri!* 'nil
    >>;
  return 't . 1;
end;

flag ('(restrict), 'opfn);

symbolic macro procedure restrict (u); list ('real!-restrict, mkquote u);

symbolic procedure real!-restrict (u);
% User callable procedure to restrict the index run of TNSR. LB and UB
% are lists of lower and upper bounds, which must lie in the inclusive range
% defined by TNSR's INDICES list.
<<  u := mapcar (mycdr u, 'eval);
  restrict!* (mycar u, mycadr u, mycaddr u)>>;

symbolic procedure restrict!* (tnsr, lb, ub);
begin scalar lex, itype;
  tnsr := mycar getnme (tnsr, '(t . t), 'restrict);
  if get (tnsr, 'itype) eq 'generic then return 'nil;
  lex := get (tnsr, 'indices);
  itype := get (tnsr, 'indextype);
  lb := lb or mycadr (lex);    % defaults are what is there now
  ub := ub or mycaddr (lex);
  if length (lb) neq length (ub) or length (ub) neq mycar (lex) then goto err;
  if memq ('nil, append (append (
     foreach x in pair (pair (mycadr (lex), lb), itype) collect 
       mycaar(x) <= mycdar(x) or (mycar getindextype (abs mycdr x) eq 'array),
     foreach x in pair (pair (lb, ub), itype) collect 
       mycaar(x) <= mycdar(x) or (mycar getindextype (abs mycdr x) eq 'array)),
     foreach x in pair (pair (ub, mycaddr (lex)), itype) collect 
       mycaar(x) <= mycdar(x) or (mycar getindextype (abs mycdr x) eq 'array)))
	then goto err;
  put (tnsr, 'restricted, list (length (lb), lb, ub));
  return (tnsr);
err:
   merror (mkmsg list ("restricted indices invalid: % %.", lb, ub), 't);
end;

flag ('(defindextype), 'opfn);
symbolic macro procedure defindextype (u);
   list ('real!-defindextype, mkquote cdr u);

symbolic procedure real!-defindextype (u);
% make a indextype declaration. args are range, n, name, fmt, case flag,
% and the function that generates the Christoffel symbols for use by cov().
% (put range first so parsing will be symbolic).
begin scalar n, nme, rng, fmt, flg, ch2sym, lex;
  if not u then <<    % no args, show all defns
     n := 0;
     foreach x in defindextype!* do << 
        if x then <<
          n := n + 1;
          write mycadr (x), " ", mycar (x), " ", mynth (x, 3), " ";
	  lex := mynth (x, 4);   % print the format specially
          prin1 (mycar lex);%spaces(1);prin2 (mycdr lex);
          write " ", mynth (x, 5), !$eol!$   % christoffel function
	>> >>;
     return n;
  >>;
  u := mapcar (u, 'eval);
  if not fixp (n := mycadr (u)) then goto err;
  lex := getindextype (n := abs n);  % get existing defn
  rng := mycar (u) or mycaddr (lex) or getindices(1);
  % rng has to be a list of 2 elements, both integers, ordered, 
  % and not more than 32.
  if (not (listp (rng) and length (rng) = 2 
	   and fixp (mycar (rng)) and fixp (mycadr (rng))
	   and mycar (rng) < mycadr (rng)
	   and mycadr (rng) <= 32)) then goto err;
   % get defaults (type default is USER<N>)
  nme := mycar (lex) or makename (append (explode ('user), explode(n)));
  fmt := mycar (mynth (lex, 4)) or "%";
%  flg := mycdr (mynth (lex, 4));
  ch2sym := mynth (lex, 5);
  if n > initlendefindextype!* then << % can only change the range for pre-defined types.
    nme := mynth (u, 3) or nme;
    fmt := mynth (u, 4) or fmt;
%    flg := mynth (u, 5) or flg;
    ch2sym := mynth (u, 5) or ch2sym
  >>;
err:
  if not fixp (n) or not stringp (fmt) or not idp (nme) or not (
     fixp mycar (rng) and fixp mycadr (rng)) or ch2sym and not 
         (atom (ch2sym) and getd (ch2sym)
		      or checktype (ch2sym, 'lambda)) then
    merror (mkmsg list ("invalid input: % % % '%' %.",
			     rng, n, nme, fmt, ch2sym), 't);
   defindextype!* := insert (defindextype!*, 
	list (nme, n, rng, fmt . flg, ch2sym),
	 n+1, 't);
  % create delta functions even if they do exist (clears protection first).
  delta!* (list (makename (append (explode('!d), explode(n))), n));
  return nme;
end;

symbolic procedure getindextype (u);
% mynth does not complain if asked to go way off the end of the list.
  mynth (defindextype!*, abs u + 1);


symbolic procedure fast!-writetnsr (tnsr, indexx, value, flg);
% This is a faster version of writetnsr that does not care about keeping
% the 'tvalue prop in order, it just cons'es values onto the front of the 
% list. readtnsr() will be happy, but the user may not be since the values
% can end up in any order, with repeats too. The object is flagged 'fast
% and the routine fast!-writetnsr!-cleanup() can be used to fixup the tvalue.
% observe that we can't toss 0 values (they must be placed in the tvalue), 
% because they may be replacements for current non-zero values
begin scalar pos, indx, tensor, val, lex, mltp, cflg;
  if get (tnsr, 'subobj) then flg := 'nil;
  if not isprotect (tnsr, 2) then 
     spread4 (resolve!-subobj (tnsr, indexx), tnsr, indexx, mltp, cflg);
  if ((lex := get (tnsr, 'restricted)) and not chkindex (indexx, lex)) then
    return ('nil . 1);   % can't access outside the restricted range

% conjugate objects don't have values, we write the conjugate value
% to the parent object.
%  if mycdr (lex := get (tnsr, 'conjugate)) then
%    return (fast!-writetnsr (mycar (lex), indexx, cnjsq (value), flg));

  if isprotect (tnsr, 2) then <<
    merror (mkmsg list ("% is write-protected", tnsr), 'nil);
    readtnsr (tnsr, indexx)  % return what is there. is this ok?
  >>;
  tensor := get (tnsr, 'tvalue);  % value list

  if flg then indx := list (indexx, 1)  % apply symmetries.
  else indx := full!-sym (indexx, get (tnsr, 'symmetry),
			  get (tnsr, 'internal!-mapping));
  if mycadr (indx) = 0 then return ('nil . 1);  % sym sez 0
  cflg := if mycaddr indx then not cflg else cflg;
  mltp := multsq (mltp, mycadr (indx) ./ 1);
  if pos := mycdr assoc (mycar indx, get (tnsr, 'external!-mapping))
	then return writetnsr (mycar pos, mycadr pos, cqv!* (value,
		multsq (mltp, mycaddr pos),
		if mycadddr pos then not cflg else cflg),  'nil);
  val := cqv!* (value, mltp, cflg);
%  val := cv!* (quotsq (multsq (mycadr (indx) . 1, value), 
%     get (tnsr, 'multiplier)), mycaddr (indx));
  put (tnsr, 'tvalue, (mycar indx . val) . tensor);
  flag (list tnsr, 'fast);
  if not memq (tnsr, fast!-writetnsr!-cleanup!-names) then fast!-writetnsr!-cleanup!-names := tnsr . fast!-writetnsr!-cleanup!-names;
  return (val);
end;

%fluid '(fast!-writetnsr!-cleanup!-names); %in decl.red

fast!-writetnsr!-cleanup!-names := '();

symbolic procedure fast!-writetnsr!-cleanup ();
<<
  foreach x in fast!-writetnsr!-cleanup!-names do fast!-writetnsr!-cleanup!* (x);
  fast!-writetnsr!-cleanup!-names := '()
>>;

symbolic procedure fast!-writetnsr!-cleanup!* (tnsr);
begin scalar tv, indx, lex, lis;
  if not indexed (tnsr) or not flagp (tnsr, 'fast) then return tnsr;
  tv := get (tnsr, 'tvalue);
  indx := igen (head (alphalist!*, mycar (get (tnsr, 'indices))),
	get (tnsr, 'restricted) or get (tnsr, 'indices), 
	get (tnsr, 'symmetry), get (tnsr, 'internal!-mapping));
  while indx do << % loop through possible indices getting current values.
    lex := assoc (mycar indx, tv);
    if not lex or (mycdr (lex) = '(nil . 1) and not get (tnsr, 'implicit))
	 then <<>>  % no value or a 0 and object not implicit.
    else lis := lex . lis;
    indx := mycdr indx;
  >>;
  put (tnsr, 'tvalue, reverse lis);
  remflag (list (tnsr), 'fast);
  return tnsr;
end;

flag ('(coords), 'opfn);
symbolic macro procedure coords (u);
   list ('real!-coords, mkquote cdr u);

symbolic procedure real!-coords (u);
begin scalar lb;
  if not u then << write coords!*,!$eol!$; return>>;
  u := mapcar (u, 'eval);  
  if not mycar u then return 'nil;
  oldcoords!* := coords!*;
  coords!* := mycar u;
  if mycadr u and fixp mycadr u then lb := mycadr u else lb := 0;
  real!-defindextype list (mkquote list (lb, length (coords!*) - 1 + lb), 1);
  if indexed mkcoords then protect!* (mkcoords, 'nil);
  mkcoords!*!* (mkcoords, 'nil);
  protect!* (mkcoords, 'w);
  write coords!*,!$eol!$;
end;

symbolic procedure stripops (indexx, ops);
begin scalar lex, lex1, i;
   if not ops then ops := iops!*;
   i := 1;
   for each x in indexx do <<
	if checktype (x, '(!*at!* !*at!- !*at!+)) then
	  <<
		if memq (mycar x, ops) then 
                  <<
		    lex := mycadr x . lex;
                    lex1 := (i . mycar x) . lex1
                  >>
		else lex := x . lex
          >>
        else if not memq (x, ops) then lex := x . lex
        else lex1 := (i . x) . lex1; 
        i := i + 1
   >>;
  return list (reverse lex, reverse lex1);
end;

symbolic procedure tvalue (tnsr);
begin scalar lex, tv, lex1, indexx;
  lex := resolve!-subobj (tnsr, indexx := head (alphalist!*, car get (tnsr, 'indices)));
  tv := get (car lex, 'tvalue);
  if car lex eq tnsr then return tv . cddr lex
  else <<     % must make indices
       return (foreach x in igen (indexx, get (tnsr, 'indices), 
		get (tnsr, 'symmetry), 'nil) join 
	   if (lex1 := assoc (sublis (pair (indexx, x), cadr lex), tv))
	     then list (x  . cdr lex1) else 'nil) . cddr lex
  >>;
end;


endmodule;
;end;
