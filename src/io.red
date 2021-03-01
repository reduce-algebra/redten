%***************************************************************************
%  FILE = io.red
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
module 'iio;
%symbolic;
%in "$redten/decl.red"$

%fluid '(readflg!*);
readflg!* := 'nil;  % reader control flag
verbose!* := 't;    % when set, causes some routines to print messages
no!-index!-err!* := 'nil;  % fluid, when set an empty index is an error
put('![, 'stat, 'parselsqb);

flag('(!]),'delim);

flag('(!]),'nodel);   % what does this mean anyway?

% making these into new tokens is much easier than the old way of writing
% a parse function for each
newtok '((!: ![) !*lsqb);
newtok '((!: !]) !*rsqb);
newtok '((!: !{) !*lcub);
newtok '((!: !}) !*rcub);
newtok '((!: !&) !*bach);
newtok '((!|) !*br);
newtok '((!| !|) !*dbr);
newtok '((!@) !*at!*);
newtok '((!@ !-) !*at!-);
newtok '((!@ !+) !*at!+);

put('!*lsqb, 'iprec, '(-20 -20))$
put('!*lcub, 'iprec, '(-20 -20))$
put('!*bach, 'iprec, '(-15 15))$
put('!*br, 'iprec, '(-10 -10))$
put('!*dbr, 'iprec, '(-10 -10))$
put('!*at!*, 'iprec, '(-5 -5))$
put('!*at!-, 'iprec, '(-5 -5))$
put('!*at!+, 'iprec, '(-5 -5))$
put('!*rsqb, 'iprec, '(20 20))$
put('!*rcub, 'iprec, '(20 20))$
flag ('(!*lsqb !*lcub !*rsqb !*rcub), 'repd)$  % these ops can be repeated

put('!*lsqb, 'prtch, "[")$
put('!*lcub, 'prtch, "{")$
put('!*bach, 'prtch, "&")$
put('!*br, 'prtch, "|")$
put('!*dbr, 'prtch, "||")$
put('!*rsqb, 'prtch, "]")$
put('!*rcub, 'prtch, "}")$
%reduce needs a way to specify separate print chars for on and off nat modes
put('!*lsqb, 'prtch2, ":[")$
put('!*lcub, 'prtch2, ":{")$
put('!*bach, 'prtch2, ":&")$
put('!*rsqb, 'prtch2, ":]")$
put('!*rcub, 'prtch2, ":}")$

put ('!*lsqb, 'match, '!*rsqb);
put ('!*lcub, 'match, '!*rcub);
iops!* := '(!*lsqb !*lcub !*bach !*br !*dbr !*at!* !*at!- !*at!+ !*rsqb !*rcub)$
shift!-iops!* := '(!*at!* !*at!- !*at!+)$
dif!-iops!* := '(!*br !*dbr)$
symz!-iops!* := '(!*lsqb !*lcub !*bach !*rsqb !*rcub)$



put ('fn, 'simpfn, 'mkrdr);  % for functional objects
flag ('(fn ), 'indexedfn);	%

!*evalindex := 'nil;    % set the switch off
put ('rdr, 'simpfn, 'simprdr);  % simplification properties
put ('mrdr, 'simpfn, 'simprdr);  % for objects in df's whose indextypes 
	                         % should be negated
put ('qrdr, 'simpfn, 'simprdr); % for 'quoted' indexed objects

flag ('(rdr mrdr qrdr), 'full);

put ('rdr, 'infix, 31);

put ('mrdr, 'infix, 31);  %?
put ('rdr, 'prifn, 'printrdr);
put ('mrdr, 'prifn, 'printrdr);


% mkrdr is the simplification routine for all indexed objects.
% It builds the ('rdr name (index)) form of the object.
% note that indexed objects are flagged 'full, so that mkrdr gets
% the object name too (except for 'fn above, which is a function 
% caller).
% this routine also handles the display format calls (as of v3.0).
symbolic procedure mkrdr (u);
begin scalar tnsr, indexx, lex, lex1, dispf2flg;
  tnsr := mycar (u);
  if not idp (tnsr) then <<   % is from fn, i.e its a function call
    if checktype (tnsr, 'findex) then   % this is bad: no 'full flag on name
      merror (mkmsg list "Internal error: name not passed to mkrdr.", t);
    tnsr := mycar (simp (tnsr));  % eval algebraic function.
    cleartmp ();		% clean the trash
    if not idp (tnsr) then return (tnsr . 1) % it may return 0
  >>;
  tnsr := resolvegeneric (tnsr);	% check for generic name
% why does parselsqb need a special flag???
  if not indexed tnsr then <<
%  if flagp (tnsr, 'checkfromlsqb) then <<
%     % we should save the prop list (in PARSELSQB) for restoration if needed.
%     remflag (list tnsr, 'checkfromlsqb);
     remprop (tnsr, 'simpfn);	% clear the parse props
     remflag (list (tnsr), 'full);	
     if terminalp() and yesp (list ("Declare", tnsr, "indexed?")) 
       then <<
          write ("Enter INDEXTYPE list and SYMMETRY list (on separate lines): ", !$eol!$);
          mktnsr!* (tnsr, 
	         setpchar ("indextype: ") and   % NOTE: bad input can cause aborts
		eval (xread ('group)),
	         setpchar ("symmetry: ") and
	      ifmtsym (eval (xread ('group))), 'nil, 'nil, 'nil)
       >> else <<
	 error1()			% abort 
%         MERROR (LIST (TNSR, "not declared indexed."), 'T, 'MKRDR)
       >>
  >>;
  indexx := evalindex (mycdadr (u));

  if not mycar (indexx) then indexx := 'nil
  else if memq ('nil, mapcar (indh (indexx), 'atom)) then
    merror (mkmsg list ("non-atomic index element: %.",
		  rdr!-string list ('rdr, tnsr, indexx)), 't)
  else if checktype (reverse indexx, dif!-iops!*) then
    merror (mkmsg list ("dif op without an index: %.",
		rdr!-string list ('rdr, tnsr, indexx)), t)
  else if indexed (tnsr) and
          not (chkindex (indexx, get (tnsr, 'restricted)) or
          chkindex (indexx, get (tnsr, 'indices))) then <<
    merror (mkmsg list ("subscript out of range: %.", 
		rdr!-string list ('rdr, tnsr, indexx)),
                 'nil);
    return ('nil . 1)
  >>;
% if no index is given, and this fluid is set, then err out rather than
% doing a display format
  if not no!-index!-err!* then   
    if not indexx and not (indexed (tnsr) eq 'scalar) then
	 return (mycadr (aeval (dispf1 (tnsr))))
    else if memq ('!?, indexx) then <<
      indexx := head (indexx, look (indexx, '!?, 0));    % strip ? from index and
      indexx := append (indexx, head (alphalist!*, mycar (get (tnsr, 'indices)) 
  				    - length (indexx)));
      dispf2flg := 't                   % set flag for later action.
    >>;

  lex := mycar (get (tnsr, 'indices));

%  if not (((lex or 0) + 1) = (mycar (fderiv (indexx)) or ((length (indexx)) + 1)))
  if not (((lex or 0) + 1) = mycar index!-len (indexx)+1)
    then merror (mkmsg list ("index % wrong length for %.",
			     index!-string indexx, tnsr), 't);

  indexx := fixat (indexx, get (tnsr, 'indextype));
  lex1 := symi list ('rdr, tnsr, indexx);
  if lex1 = 0 then return ('nil . 1); % no call to symi now
  if dispf2flg then
    return simp if mycar (lex1) eq 'minus then
                                 dispf2 (shift!* (mycadr (lex1), 't))
               else dispf2 (shift!* (lex1, 't));
  if mycar (lex1) eq 'minus then 
    lex1 := list ('minus, symz!*!* (shift!* (mycadr (lex1), 't)))
  else lex1 := symz!*!* (shift!* (lex1, 't));
  if lex1 = 0 then return ('nil . 1)
  else return (simp (lex1));
end;

% simprdr is the simplification routine for rdr forms.
% it either returns unevaluated, or gets an object value if
% there is an integer index. 
% if READFLG!* is on, then things are still being parsed and we don't want
% to evaluate the object if that were possible (eg. integer index or scalar
% object)
symbolic procedure simprdr (u);
begin scalar tnsr, indexx, lex, lex1;
  u := shift!*!* (u, 't);
  tnsr := mycadr (u);     
  indexx := mycaddr (u);

  % if symzexp switch is off when the object is created, the symz!*!()
  % call in mkrdr() will leave symz ops in the index. If the switch is
  % then reset and the expression is reval'd, this code will expand
  % the symz.
  if !*symzexp and not free1 (indexx, symz!-iops!*) then
	return simp symz!*!* (list ('rdr, tnsr, indexx));
  if mycar (u) eq 'qrdr or not indexed (tnsr) % noeval op
	then return (list ((formrdr (tnsr, indexx) . 1) . 1) . 1)
  else if not indexx then <<
    if readflg!* then return (list ((formrdr (tnsr, indexx) . 1) . 1) . 1)
    else if indexed (tnsr) eq 'scalar then return (readtnsr (tnsr, 'nil))
    else merror ("empty index!",'t)
  >>;
  lex := mycar (get (tnsr, 'indices));
  lex1 := car stripops (indexx, symz!-iops!*);  % remove symz ops for length check
  if not (((lex or 0) + 1) = (mycar (fderiv (lex1)) or ((length (lex1)) + 1)))
    then merror (mkmsg list ("index % wrong length for %.",
			     index!-string lex1, tnsr), 't)
  else if not fixedindex (indexx) or readflg!* then
% this causes the failure of implicit evals
%OR GET (TNSR, 'IMPLICIT) THEN  % unevaled form
    return (list ((formrdr (tnsr, indexx) . 1) . 1) . 1)
  else if not free1 (indexx, '(!*at!* '!*at!- !*at!+)) and 
           not deriv (indexx, '!*dbr) then <<  
%    merror (mkmsg list ("no such offspring for %", tnsr), 'nil);
%    return ('nil . 1)
% no reason we can't return this unevaled.
    return (list ((formrdr (tnsr, indexx) . 1) . 1) . 1)
  >> else <<  % fixed index, read and return value.
    if deriv (indexx, '!*br) and not deriv (indexx, '!*dbr) then
	return (simp!* (cnvrtdif (tnsr, indexx)))
    else if deriv (indexx, '!*dbr) then 
% if only a single index after the || and the cov exists, should return a value
         if length (indexx) eq (lex := mycar get (tnsr, 'indices)) + 2 
            and (lex1 := mycaddr get (tnsr, 'cov)) then <<
                lex1 := shift!* (list ('rdr, lex1,  % could still have a shift
	                  append (head (indexx, lex),
                                  mypnth (indexx, length (indexx)))), 't);
	     if not free1 (lex1, shift!-iops!*) then <<
%		    merror (mkmsg list (" no such offspring for %.",
%					tnsr), 'nil);
%			return ('nil . 1)
	    return (list ((formrdr (cadr lex1, caddr lex1) . 1) . 1) . 1)
             >>;
	     return readtnsr (mycadr lex1, mycaddr lex1)
	     >>
         % otherwise return unevaled.
         else return (list ((formrdr (tnsr, indexx) . 1) . 1) . 1)
    else return (readtnsr (tnsr, indexx));
  >>;
end;


% If the switch EVALINDEX is on, this routine evaluates the elements of
% an index. Error checking is done in MKRDR.
symbolic procedure evalindex (indexx);
begin scalar lex, lis, op;
  if not (mycar (indexx)) or not !*evalindex then return (indexx);
  lis := '();
  while indexx do <<
      lex := mycar (indexx);
      indexx := mycdr (indexx);
%      if not atom (lex) and mycar (lex) eq '!*at!* then
%	lis := aconc (lis, list ('!*at!*, reval aeval (mycadr (lex))))
      if (op := mycar (checktype (lex, shift!-iops!*))) then
        lis := aconc (lis, list (op, reval aeval (mycadr (lex))))
      else if memq (lex, iops!*) then lis := aconc (lis, lex)
      else lis := aconc (lis, reval (aeval (lex)))
  >>;
  return (lis);
end;

symbolic procedure formrdr (tnsr, indexx);  % should be macro
 car (fkern (list ('rdr, tnsr, indexx)));

putd ('oldscan, car getd ('scan), cdr getd ('scan));
remflag ('(scan), 'lose);

% save the last two scanned inputs. If we get into PARSELSQB, then
% these are the name and the '[ symbol.
symbolic procedure scan ();
  << oldscanval!* := scanval!*; scanval!* := oldscan()>>;

%PUTD ('SCAN, CAR GETD ('NEWSCAN), CDR GETD ('NEWSCAN));


% parselsqb is the parsing routine for object indices and symmetrization
% operations. i.e it collects up things between [].
% Entirely rewritten as of V4.0 to make use of new tokens for index ops.

symbolic procedure parselsqb ();
begin scalar lex, lst, tnsr;
  tnsr := oldscanval!*;	% the name is the second last scan, last is the '[
  % this will get it into mkrdr, where we can then decide what to do.
  if idp (tnsr) and get (tnsr, 'simpfn) neq 'mkrdr then
    <<
      put (tnsr, 'simpfn, 'mkrdr);
%      flag (list (tnsr), 'checkfromlsqb);
      flag (list (tnsr), 'full)	% causes name to be passed to mkrdr too.
    >>;
  loop: 	% collect the stuff between the brackets
    lex := check!-index!-ops (top xread ('group));
    lst := append (lst, lex);
    if not (cursym!* eq '!]) then go to loop;

  scan (); 
		% NOTE: a name MUST appear as the car of the index, so integer
                % indices might mess this up. Therefore, we place the name
		% 'FINDEX there to keep the parser happy.
  lex := 'findex . lst;  % set up the index and
%  lex := 'findex . ('symlst . symlst!*) . lst;  % set up the index and
  return (lex)
end;

put ('findex, 'simpfn, 'simpfindex);
symbolic procedure simpfindex u;  % this catches users who get goofy
  merror (mkmsg list "index without a name.", 't);

symbolic procedure check!-index!-ops (u);
begin scalar lex, lex1, lex2, flg, curprec, lst;
  lex := u;
  curprec := -100;
  while lex do
   <<
     lex1 := get (mycar lex, 'iprec);
     lex2 := mycadr lex1 or 0;
     lex1 := mycar lex1 or 0;
     flg := get (mycar lex, 'repd) or 't;
%     lex1 := assoc (mycar lex, index!-preclis) or '(a (0 0) t);
%write assoc (mycar lex, index!-preclis),!$eol!$;
%write lex,"     ", lex1,!$eol!$;
     if (curprec < 0) then 
      <<
        if ((flg and lex1 >= curprec)
		or lex1 > curprec) then
	 curprec := lex1
 	 else merror (mkmsg list ("mis-matched index ops"), 't)
      >> else <<
        if ((flg and lex2 >= curprec)
		or lex2 > curprec) then
          curprec := lex2
	 else merror (mkmsg list ("mis-matched index ops"), 't)

     >>;
      lst := mycar lex . lst;
      lex := mycdr lex
%     push (pop (lex), lst)
   >>;
  while lst do <<
    if memq (mycadr lst, shift!-iops!*) then
      <<
%	push (list (mycadr lst, mycar lst), lex);
%        pop (lst)    % don't put this in the line above, eval order indeterminate
	lex := list (mycadr lst, mycar lst) . lex;
	lst := mycdr lst
      >> else lex := mycar lst . lex;
      lst := mycdr lst;
  >>;
  return lex;
end;

symbolic procedure index!-len (indexx);
begin scalar lex, i, j;
  lex := indexx;
  i:= j:= 0;
  while (lex and not memq (mycar lex, dif!-iops!*)) do
      <<if not get (mycar lex, 'iprec) then i := i + 1; lex := mycdr lex>>;
  while lex do 
      <<if not get (mycar lex, 'iprec) then j := j + 1; lex := mycdr lex>>;
  return list (i,  j);
end;

newtok '((!= !=)  equalparse);  % define == operator

infix ==;      % will have lowest precedence in system

put ('equalparse, 'simpfn, 'equalparse1);

% equalparse is the routine that receives the right- and left-hand
% sides of an == operation and begins the evaluation process.
% it returns the value written if it is a scalar, or the indexed object
% that was written to.

symbolic procedure equalparse1 (u);
begin scalar ex1, ex2, lex, lex1, readflg!*;
  readflg!* := 't;  % indicates a read in progress, see RDR for use.
  if atom (mycar (u)) then ex1 := mycar (u)  % scalar output expected
  else ex1 := reval (mycar (u));     % otherwise its indexed, 
                                   % so get mkrdr to do its stuff.
  readflg!* := 'nil;
  ex2 := mycadr (u);        % right-hand side of ==
  if ex1 = 0 then return ('nil . 1)  % symmetry sez no way.
  else if not atom (ex1) and mycar (ex1) eq 'minus then <<
    ex1 := mycadr (ex1);    % transfer symmetry sign from left to right sides
    ex2 := list ('minus, ex2)
  >>; 
  if idp (ex1) then       % evaluate scalar, i.e no index.
    return (evaltnsr (ex1, 'nil, ex2))
%  ELSE IF NOT IDP (MYCADR (EX1)) THEN  % not a valid object (e.g might be a sum)
  else if not checktype (ex1, 'rdr) then  % not a valid object (e.g might be a sum)
    merror (mkmsg list ("cannot assign to %.", ex1), 't)
  else if fixedindex (mycaddr (ex1)) then <<   % single element to be written
    if deriv (mycaddr (ex1), 'nil) then
        merror (mkmsg list ("cannot assign to %.", ex1), 't);
    evaltnsr1 (mycadr (ex1), mycaddr (ex1), reval (ex2), 'nil);
    return (readtnsr (mycadr (ex1), mycaddr (ex1)))  % reread to find what went in.
    >>
%  ELSE IF NOT INDEXED (MYCADR (EX1)) AND NOT MYCADDR (EX1) THEN <<
%    MKSCALAR!* (LIST (MYCADR (EX1)));	% make the scalar object automatically 
%    RETURN (EVALTNSR (MYCADR (EX1), 'NIL, EX2))
%  >>
  else return (evaltnsr (mycadr (ex1), mycaddr (ex1), ex2)); % a whole object
end;


% dispf1 displays the contents of an indexed object in the 'first'
% format, i.e it prints out the explicit elements.

symbolic procedure dispf1 (tnsr);
begin scalar lex, mlt, cflg;
  spread3 (tvalue (tnsr), lex, mlt, cflg);
  terpri!* ('t);
  foreach x in lex do <<
    if not !*nero and mycdr x = ('nil ./ 1) then <<>>
    else <<
      maprint (list ('rdr, tnsr, car x), 0);  % print the object and index
      prin2!* (" = ");
      if not mycdr x then prin2!* ("<undefined>")
      else if (!*hide) then prin2!* ("<value>")
      else maprint (mk!*sq (cmv!* (cdr x, mlt, cflg)), 0);
      terpri!* ('t)
    >>
   >>;   
  return (tnsr);
end;

% dispf2 is the other function for displaying the contents of
% indexed objects (in format '2'). it calls igen to generate all
% possible indices for the object and reads to find the values. 
% unless nero is set zeroes are printed as well (unlike dispf1,
% which never sees a zero unless the object is implicit).
% if !*hide is on, values are printed as <value>.

symbolic procedure dispf2 (u);
begin scalar lis, lex, tnsr, indexx;
  tnsr := mycadr u;
  indexx := mycaddr u;
  terpri!* ('t);
  lis := igen (indexx, get (tnsr, 'restricted) or get (tnsr, 'indices),
	       get (tnsr, 'symmetry), get (tnsr, 'internal!-mapping));
  while lis do <<
    lex := readtnsr (tnsr, mycar (lis)); % read the value
    if not !*nero or (!*nero and not (lex = '(nil . 1))) then <<
      maprint (list ('rdr, tnsr, mycar (lis)), 0);
      prin2!* (" = "); 
      if (not (lex = '(nil . 1)) and !*hide) then prin2!* ("<value>")
      else maprint (mk!*sq (lex), 0);
      terpri!* ('t)
    >>;
    lis := mycdr (lis)
  >>;
  return (list ('rdr, tnsr, indexx)); % return a valid indexed object
end;


symbolic procedure fill!-indextype (indexx, indextype);
% place 'nil in indextype at locations corresponding to index ops.
% fills out with -1 for deriv indices
begin scalar lex;
  while indexx do <<
    if get (pop indexx, 'iprec) then lex := 'nil . lex
    else <<push((pop indextype or -1), lex)>>
  >>;
  return reverse lex;
end;

% printrdr is the function the system asks to print indexed objects.
% it does some setting up and then calls either rdrp or rdr1 to do the
% actual output in 'pretty' or 'not pretty' format, respectively.

symbolic procedure printrdr (u);
begin scalar pname, tnsr, indexx, indextype, i, n, symlst, cflg, printname;
  u := cdr u;   % skip rdr or mrdr
  tnsr := mycar (u);
  cflg := mycdr (get (tnsr, 'conjugate)); % need bar if its conjugate.
  indexx := mycadr (u);
  indextype := get (tnsr, 'indextype);
  printname := get (tnsr, 'printname) or tnsr;  % print name of object

  % modify index and indextype for deriv objects (insert new op)
  if numberp (n := mycar get (tnsr, 'cov)) and n > 0 then <<
     indexx := insert (indexx, '!*dbr,
		 mycar (get (tnsr, 'indices)) - n + 1,'nil);
     indextype := insert (indextype, -1, 
		mycar (get (tnsr, 'indices)) - n + 1,'nil)
   >>
  else if numberp (n := mycar get (tnsr, 'odf)) and n > 0 then <<
     indexx := insert (indexx, '!*br, 
		mycar (get (tnsr, 'indices)) - n + 1,'nil); 
     indextype := insert (indextype, -1, 
		mycar (get (tnsr, 'indices)) - n + 1,'nil)
  >>;
  if (not indextype and indexed (tnsr) neq 'scalar) or not !*nat then
    << prin2!* rdr!-string (list ('rdr, printname, indexx))>>
  else rdrp (printname, indexx, fill!-indextype (indexx, indextype), cflg);
  return ('t);
end;

% rdrp is the pretty printer for indexed objects; it is called by
% printrdr.

symbolic procedure rdrp (printname, indexx, indextype, cflg);
begin scalar posl;
  testwidth (printname, indexx, indextype);  % will it fit on the line?
  if cflg then <<  	% print a bar over the conjugate
    posl := posn!*;
    if (ycoord!* := ycoord!* + 1) > ymax!* then ymax!* := ycoord!*;
    for i := flatsizec (printname) step -1 until 1 do prin2!* ("_");
    ycoord!* := ycoord!* - 1;
    posn!* := posl
  >>;
  prin2!* (printname);	% print the name of the object
  if not indextype then <<prin2!*("[]"); return>>;  % scalar object needs the []
  print!-index (indexx, indextype);
end;

symbolic procedure print!-index (indexx, indextype);
begin  scalar lex, lex1, lex2, fmt, nxt!-lev, sop!-lev, last!-lev;
  lex := shftc (indexx, indextype);
  indexx := mycar lex;	    % remove shift ops and fix up indextype
  indextype := mycadr lex;
  if not !*nat then <<
    prin2!* (index!-string indexx);
    return
  >>;

  while indextype do <<    % for each indice, print it up or down as specified.
    lex := pop (indextype);
    lex1 := pop (indexx); 	% thing to print
    lex2 := indextype;  % do look ahead
    while lex2 and not (nxt!-lev := pop (lex2)) do <<>>;    % find first non-nil value

    if memq (lex1, '(!*lsqb !*lcub)) and not sop!-lev then 
      lex := sop!-lev := nxt!-lev
    else if memq (lex1, '(!*bach !*rsqb !*rcub)) then 
		lex := sop!-lev or last!-lev
    else if memq (lex1, dif!-iops!*) then lex := nxt!-lev;
    last!-lev := lex;
    ycoord!* := ycoord!* + sign (lex);   % set up coordinate for indice
    if ycoord!* > ymax!* then ymax!* := ycoord!*
    else if ycoord!* < ymin!* then ymin!* := ycoord!*;
    
    lex2 := get (lex1, 'prtch);
    if (lex2) then prin2!* lex2	     % print index op
    else <<
       fmt := mycadddr (getindextype (abs lex));  % get print format 
       prin2!* mkmsg list (mycar fmt, lex1)
    >>;
    if not (memq (lex1, '(!*br !*dbr !*lsqb !*lcub)) 
       or memq (mycar indexx, '(!*rsqb !*rcub))) then prin2!* (" ");
    ycoord!* := ycoord!* - sign (lex)
  >>;
end;

symbolic procedure rdrprintwidth (pname, indexx, indextype);
begin scalar wid, lex;
      % count print length of name and each indice.
  wid := flatsizec (pname) + flatsizec (indh (indexx));
  while indexx do <<  % count other special chars used by rdrp, and spaces.
    lex := abs (pop (indextype) or 1);
%    indextype := mycdr indextype;
    wid := wid + length (explode (mycar mycadddr
                          getindextype (lex))) - 2;
    if mycar (indexx) eq '!*br then wid := wid - 3  % these guys print smaller
    else if mycar (indexx) eq '!*dbr then wid := wid - 4;
    popq (indexx)
  >>;
 return wid;
end;

% testwidth determines the print width of an indexed object and
% forces a newline if it won't fit on whats left of the current line.
symbolic procedure testwidth (pname, indexx, indextype);
  if rdrprintwidth (pname, indexx, indextype) 
	> (linelength (nil) - 5 - posn!*) then terpri!* ('t);

% dncase shifts an upper case character to lower case.

symbolic procedure dncase (ex);
begin scalar lex;
  lex := mascii (ex);
  if lex > 90 or lex < 65 then return (ex)
  else return (mascii (lex + 32));
end;

% upcase shifts a lower case character to upper case.

symbolic procedure upcase (ex);
begin scalar lex;
  lex := mascii (ex);
  if lex > 123 or lex < 97 then return (ex)
  else return (mascii (lex - 32));
end;

% dnname shifts an entire name to lower case.

symbolic procedure dnname (ex);
  if not idp (ex) then ex
  else makename (mapcar (explode (ex), 'dncase));

% upname shifts an entire name to upper case.

symbolic procedure upname (ex);
  if not idp (ex) then ex
  else makename (mapcar (explode (ex), 'upcase));


flag ('(mclear), 'opfn);  % make it directly callable

% mclear is used to clean up the flags in case an error has left them
% in a peculiar state. 

% should use the 'initl prop to reset
symbolic procedure mclear ();
<<
  readflg!* := 'nil;
%  parseflag!* := 'nil;
  no!-index!-err!* := 'nil;
  symzflg!* := 'nil;
  !*nat := 't;   % this might cause a prob, but better so than not done
  !*mode := 'algebraic;
  tabbing!* := 0;
  posn!* := 0;
  cleartmp();
  change!-tnsr!-flag!* := 0;
  linelength (80)
>>;

%unfluid '(readflg!*);

endmodule;
;end;
