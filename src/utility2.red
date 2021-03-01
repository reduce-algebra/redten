%***************************************************************************
%  FILE = utility2.red
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
module 'util2;
%symbolic;
%in "$redten/decl.red"$

flag ('(icopy mapfi mkcoords delta), 'indexedfn);	%

% dir is the routine with which the user can see the names and some
% attributes of indexed objects in the system. objects flagged 'nodir are
% not displayed, but are counted into the final summary.

put ('dir, 'simpfn, 'dir!*);

symbolic procedure dir!* (lex);
begin scalar lex1, lex2, i, n, asked, linelen, 
      parent, gparent, tnsr;
  lex := foreach u in lex collect if checktype (u,'!*sq) then reval u else u;
  if not mycar (lex) and not indexed!-names then     % nothing yet made by the user.
    <<
      prin2!* ("no objects");
      terpri!* 'nil;
      return 't . 1
    >>;
  linelen := linelength (100);   % lengthen line to avoid premature wraps
  n := i := 0;		% number of elements and number of objects.
  if not mycar (lex) then 
     lex := if !*reversedir then reverse indexed!-names else indexed!-names
  else if base!-case!-name mycar (lex) eq 'all or mycar lex eq '!* 
	then << % show all names
     lex := if !*reversedir then reverse indexed!-names else indexed!-names;   
     asked:= 'a  % this is non-nil but distict from a true request (asked = 't)
  >>  else <<
    lex := match!-names (lex, indexed!-names);
    if !*reversedir then lex := reverse lex;
    asked:= 't
  >>;
  lex := for each x in lex collect resolvegeneric (x);
  if not lex then return 't . 1;    % message here??
  posn!* := 2;
  prin2!* ("name");
  posn!* := 16;
  prin2!* ("type");
  posn!* := 29;
  prin2!* (" comp   ");
  posn!* := 38;
  prin2!* ("prot");
  posn!* := 44;
  prin2!* ("coordinates");
  posn!* := 60;
  prin2!* ("indextype");
  terpri!* 'nil;

  while lex do <<
    tnsr := mycar (lex);		% current name
    lex := mycdr (lex);
    begin scalar i, j, v, u;   % find parent name if any
      u := explode (tnsr);

      if (i := look (u, '!_, 0)) eq 'nil  then gparent := 'nil
      else <<
        % get the grandparent name
        gparent := makename head (u, i); % is there a left over '!!'?
        % check for another object name (will be a shifted object parent).
        if (j := look (mypnth (u, i), '!_, 0)) then 
            parent := makename (head (u, i + j))
        else parent := 'nil;
      >>;
    end;
    posn!* := 0;
    if not indexed (tnsr) then <<>>	% not indexed, no action 
    else if not asked and (flagp (parent, 'nodir)
			   or flagp (gparent, 'nodir)
                           or flagp (tnsr, 'nodir)) then << % dont print, but add to summary
      i := i + 1;
      n := n + length (get (tnsr, 'tvalue))
    >>
%    else if indexed (tnsr) eq 'scalar then scnames := tnsr . scnames % scalar object
    else <<
      % if it is flagged 'nodir and we are here the user asked explicitly, so
      % clear the flag (this is the only way to undo the nodir function).
      if asked eq 't and flagp (tnsr, 'nodir) then
                   remflag (list tnsr, 'nodir);
      i := i + 1;
      n := n + length (get (tnsr, 'tvalue));
      if (tnsr eq getmetric!* (-1*(mycar get (tnsr, 'indextype) or 0), 
			       currentmetric, 'nil)) then
            prin2!* ("*");
      posn!* := 2;
      prin2!* tnsr;
      if (lex1 := get (tnsr, 'subobj)) then <<
        prin2!* index!-string 
		% this converts a!# to a which looks nicer on output
		for each x in mycadr lex1 collect mycar explode x;
	posn!* := if posn!* < 16 then 16 else posn!* +3;
        prin2!* "--> ";
	if not !:onep numr get (tnsr, 'multiplier) then prin2!* "-";
        if flagp (tnsr, 'cnj) then prin2!* "cnj ";
        prin2!* (mycar lex1);
        prin2!* (index!-string 
		foreach x in mycaddr lex1 collect mycar explode x);
      >> else <<
       posn!* := 16;
      lex2 := get (tnsr, 'itype);
      prin2!* (lex2 or "");
      posn!* := 31;
      prin2!* (length (get (tnsr, 'tvalue)));
      if get (tnsr, 'implicit) or 
	     get (tnsr, 'external!-mapping) then prin2!* ("+");
      if get (tnsr, 'tvalue) and memq ('nil, foreach x in
			       get (tnsr, 'tvalue) collect mycdr x) then 
                       prin2!* ("?"); % object has undefined comp.
      >>;
      posn!* := 39;
	prin2!* (lambda x; if x eq 2 then "w" else if x eq 3 then "k" else
	if x eq 6 then "kw" else "  ")(get (tnsr, 'protection));
      posn!* := 44;
      if (lex2 := get (tnsr, 'coords)) then prin2!* (lex2)
      else prin2!* ("none");
      posn!* := 61;
      prin2!* (get (tnsr, 'indextype) or "()");
      terpri!* 'nil
    >>
  >>;
  terpri!* 't;
  prin2!* mkmsg list (" % object%,    Total components: %", i,
	onep (i) and "" or "s", n);
  terpri!* 'nil; terpri!* 'nil;
  linelength (linelen);
  return 't . 1;
end;

put ('nodir, 'simpfn, 'nodir!*);
% this was an rlis function, but you can't get help on it then.
symbolic procedure nodir!* (u);
% nodir declares a list of names to be not eligible for display by dir.
<<
  write !$eol!$;
  foreach x in match!-names (u, indexed!-names) do 
    if indexed (x) then <<
      flag (list (x), 'nodir);
      write x," "
    >>;
  write !$eol!$;
  't . 1
>>;

flag ('(help), 'opfn);			% is this needed?? 
put ('help, 'formfn, 'help);

% HELP is used to obtain on-line help about functions in the
% tensor system. given no arguments help* prints a list of all
% functions for which help is available. 
% Otherwise the associated help string is printed

symbolic procedure help (lis, vars, mode);
begin scalar ex, i, lex, u, pos;
  if (mycar (lis) eq 'help) then ex := mycdr (lis)   % 3.3 gets name  ...
  else ex := lis;			% but 3.2 doesn't. 
%  if not atom (ex) then ex := mycar(ex);	% for RLIS fns.
  if not ex then <<
      prin2 ("Help is available on:");
      terpri ();
      pos := 0;
      foreach x in helplist!* do <<
	 write mycar x, " ";
	 pos := pos + flatsizec (mycar x) + 1;
         if (pos > linelength ('nil) - 10) then <<write !$eol!$; pos := 0>>
      >>;
      return 't;
  >>;
  foreach x in match!-names (ex, foreach x in helplist!* collect car x) do 
    if not (lex := mycadr (assoc (x, helplist!*))) then 
% note that if a pattern does not match the helplist!*, it will be lost
% so this message will never appear.
      write mkmsg list ("no help available on %", x),!$eol!$
    else  write lex,!$eol!$;  % just print the assoc string
  terpri ();
  return 't;
end;

put ('rem, 'formfn, 'rem);   % easy way to get an unevaled list.
put ('remi, 'formfn, 'rem);

symbolic procedure rem (lis, vars, mode);
begin scalar killed!*, lex;
%  if (mycar (lis) eq 'rem) then lex := mycdr (lis); % kill name in 3.3 
  lex := mycdr (lis); % kill name  (3.2 no longer supported)
%  if not atom mycar lex then lex := mycar lex; %%if user forgets commas
  killed!* := 'nil;
  lex := match!-names (lex, indexed!-names);
  if mycar lis eq 'rem then <<
    for each x in lex do kill (x);
    terpri ();
    write (" ", killed!*);
    terpri ();
    return 't;
  >>
  else return rem1 (lex);
end;

% REM1 is the interactive routine called by REM. it guides the user through
% the process of deleting objects.

symbolic procedure rem1 (lis);
begin scalar a;
  a := readch ();       % eat last newline
  setpchar ("");        % kill off the prompt
  while lis do <<	% list of names to try for.
    prin2 (mycar (lis));
    prin2 (":");
    spaces (16 - flatsizec (mycar (lis)));
    prin2 ("Delete? (Y/N/G/Q) ");	% prompt
    a := readch ();
    if a neq !$eol!$ then readch (); % newline

    if a eq '!Y or a eq '!y then <<		% yes, kill it
      kill (mycar (lis));
      lis := mycdr (lis)
    >>
    else if a eq '!Q or a eq '!q then lis := 'nil	% leave now, no more to do.
    else if a eq '!G or a eq '!g then <<	% go non-interactive and kill remaining.
      prin2 ("Are you sure? "); % check if user really wants this.
      a := readch ();
      readch ();
      if a eq '!Y or a eq '!y then <<	% must answer 'y, or nothing happens.
        mapcar (lis, 'kill);
        lis := 'nil
      >>
    >>
    else lis := mycdr (lis)
  >>;
  write (killed!*);
  terpri ();
  return 't;
end;

% kill is the primitive routine that removes indexed objects from the
% system by removing all properties and deleting the name from the indexed!-names
% list. if the object is kill-protected, kill will fail. kill removes the
% conjugate, covariant derivative, divergence and all shifted offspring of 
% any object it kills.
% kill now kills metric families too. v3.12
 
symbolic procedure kill (inp);
begin;
  inp := resolvegeneric (inp);
%  if get (inp, 'generic) then return 'nil; % can't remove generic names at all
  if not inp or not indexed inp or memq (inp, killed!*) then return ('nil);
  foreach x in getfam (inp) do kill!* (x);
  return 't;
end;

symbolic procedure kill!* (inp);
begin scalar i, lex, lav;
  inp := resolvegeneric (inp);
  if not inp or not indexed inp or memq (inp, killed!*) then return ('nil);
  if isprotect (inp, 3) then return ('nil);  % can't remove a protected name.
  indexed!-names := delete (inp, indexed!-names);
  if not indexed (inp) then return ('nil);
  foreach x in indexed!-names do if mycar get (x, 'subobj) eq inp then
	kill!* x;  % wipe out subobjects that had inp as target.
  killed!* := inp . killed!*;	% list of deceased objects, printed by rem()
  foreach x in get (inp, 'corem) do kill!* x;   % kill co-removed objects
  if indexed (inp) eq 'scalar then lav := get (inp, 'tvalue);
  mysetprop (inp, 'nil);			% remove all properties
  if lav then setk (inp, mk!*sq (mycdar lav));  % reset scalar avalue
  return (inp);
end;

put ('ias, 'simpfn, 'ias!*);

% ias allows the user to assign elements to an indexed object in a convenient
% fashion. it prompts for input for each possible element the object
% may have, or those indicated by the given pattern index.
symbolic procedure ias!* (u);
begin scalar tnsr, lex, lex1, lis, natold, indices, tvalue, overwriteflg;
  overwriteflg := mycadr (u);  % second arg non-nil sets flag
  readflg!* := 't;	% keeps SIMPRDR from over-eval'ing

  if atom (tnsr := mycar (u)) then <<			% just the object name
    tnsr := resolvegeneric (tnsr);	% might be generic name, and not yet resolved 
    if not indexed (tnsr) then return (tnsr . 1);		% not indexed, no op
    indices := igen (head (alphalist!*, mycar (get (tnsr, 'indices))),
			get (tnsr, 'restricted) or get (tnsr, 'indices),
		     get (tnsr, 'symmetry), get (tnsr, 'internal!-mapping));
    tnsr := mycar getnme (mycar (u), '(t . t), 'ias!*);
  >> else if indexed (mycaar (u)) then <<		% a referenece
    tnsr := mycar getnme (lex := reval (mycar (u)), '(t . t), 'ias);	% name of object from reference
    if not atom (lex) and mycar (lex) eq 'minus then lex := mycadr (lex);
    indices := igen (indh (mycaddr (lex)), 	% indices requested
		get (tnsr, 'restricted) or get (tnsr, 'indices),
		     get (tnsr, 'symmetry), get (tnsr, 'internal!-mapping));
  >> else merror (mkmsg list ("bad input: %.", mycar u), 't); % else an error

  if get (tnsr, 'itype) eq 'generic then return 'nil;

  if isprotect (tnsr, 2) then <<
    merror (mkmsg list ("% is write-protected", tnsr), 'nil);
    return (tnsr . 1)
  >>;

  saveobj (tnsr);   % save object
  tvalue := get (tnsr, 'tvalue);
  if overwriteflg then put (tnsr, 'tvalue, 'nil);  % we're committed now
  natold := !*nat;
  !*nat := 'nil;
  setpchar ("");  % kill off the prompt
  readflg!* := 'nil;
  % if the object has elements and the multiplier is not 1, combine them
  % (what if its implicit and the mulitplier is not 1? then its a mess).
  if tvalue and not (get (tnsr, 'multiplier) = '(1 . 1)) then
    begin scalar shwind;
      shwind := !*showindices; !*showindices := 'nil;
      mapfi!* (list (tnsr));    % wants a list of args
      !*showindices := shwind;
    end;
  loop:
    if not indices then goto afterloop;
    maprint (list ('rdr, tnsr, mycar (indices)), 0); % print object and index
    if not overwriteflg and assoc (mycar (indices), tvalue)
	 then prin2!* (" (=) ")
    else prin2!* (" = ");
    terpri!* ('nil);
    lex1 := xread ('t);
    % user typed NIL; that means exit.
    if oldscanval!* eq 'nil then goto afterloop 
    else if lex1 then <<  % if no entry, no change
      lex1 := simp (lex1);	% simplify input value
      fast!-writetnsr (tnsr, mycar indices, lex1, 't)
    >>;
    indices := mycdr (indices);
  goto loop;
afterloop:
  !*nat := natold;
  fast!-writetnsr!-cleanup();
  return (tnsr . 1);
end;

put ('icopy, 'simpfn, 'icopy!*!*);

symbolic procedure icopy!*!* (u);	% interface to copy*, this is dumb
  icopy!* (mycar (u), mycadr (u));

% copy* is the routine which copies indexed objects.

symbolic procedure icopy!* (inn, outt);
begin scalar lex;
  inn := mycar getnme (inn, '(t . t), 'icopy);
  outt := mycar getnme (outt, '(nil . t), 'icopy);
  if get (outt, 'protection) then
    merror (mkmsg list ("output % is protected", outt), 't);
  saveobj (outt);   % save current values
  kill!* (outt);
  mktnsr!* (outt, get (inn, 'indextype), get (inn,'symmetry),
	get (inn, 'implicit), 'nil, 'nil);
  lex := tvalue (inn);
  put (outt, 'tvalue, uniqkern car lex);   % place tvalue;
  put (outt, 'multiplier, uniqkern cadr lex);
  remflag (outt, 'cnj);    % just in case, it should not be there
  if caddr lex then flag (outt, 'cnj);
  put (outt, 'internal!-mapping, get (inn, 'internal!-mapping));
  put (outt, 'external!-mapping, get (inn, 'external!-mapping));
  return (outt . 1);
end;

put ('iclear, 'simpfn, 'iclear);

symbolic procedure iclear (u);
<<
  write foreach x in u collect iclear!*(x);
  't . 1
>>;

symbolic procedure iclear!* (tnsr);
begin
   if isprotect (tnsr, 2) or isprotect (tnsr, 3) or get (tnsr, 'subobj) 
	then return nil;
   remprop (tnsr, 'tvalue);
   put (tnsr, 'multiplier, '(1 . 1));
   return tnsr
end;

put ('copyfam, 'simpfn, 'copyfam!*);
fluid '(name!-to!-change);  % a dotted pair of exploded names: root . rep

symbolic procedure copyfam!* (u);
begin scalar tnsr, newtnsr, lex, lex1, lex2, name!-to!-change;
  tnsr := mycar getnme (mycar u, '(t . t), 'copyfam);
  newtnsr := mycadr u;
  if get (tnsr, 'itype) eq 'metric and not newtnsr then <<
     newtnsr := makename (append (explode (metric), 
			     for each x in explode (metricseq)
			     collect mascii (x)));
     metricseq := metricseq + 1		% does not decrement. 
  >> else newtnsr := mycar getnme (newtnsr, '(nil . nil), 'copyfam);
  name!-to!-change := explode tnsr . explode newtnsr;  % this is fluid and seen by the recusrive
  copyfam!*!* (tnsr);
  return newtnsr . 1;
end;

symbolic procedure copyfam!*!* (tnsr);
begin scalar lex;
  if not indexed tnsr or
      not (lex := build!-new!-name (explode tnsr)) then return tnsr;
  if indexed lex then return lex;   % already copied
  icopy!* (tnsr, lex);    % copy object
  foreach x in prop (tnsr) do <<
	if atom x then flag (list lex, x)   % a flag
        else if car x eq 'shift then
		put (lex, car x, foreach u in cdr x collect
			copyfam!*!* (u))
        else if car x eq 'altmetric then
	      put (lex, car x, foreach u in cdr x collect
			build!-new!-name (explode u) or u)
        else if checktype (x, '(odf cov)) then
              put (lex, car x, list (cadr x, caddr x, copyfam!*!* cadddr x))
        else if car x eq 'conjugate then <<
	   if not cddr x then put (lex, car x, copyfam!*!* cadr x . 'nil) 
	   else put (lex, car x, (build!-new!-name (explode cadr x)
				  or cadr x) . t)
         >>
        else if indexed cdr x and not (car x eq 'printname) then 
	   put (lex, car x, copyfam!*!* cdr x)
        else if atom cdr x then put (lex, car x, cdr x)
        else put (lex, car x, cdr x)
   >>;
  return lex;
end;

symbolic procedure build!-new!-name (tnsr);
  if head (tnsr, length car name!-to!-change) = car name!-to!-change then 
	 makename (append (cdr name!-to!-change,
			  mypnth (tnsr, length (car name!-to!-change) + 1)))
  else nil;

unfluid '(name!-to!-change);

put ('mapfi, 'simpfn, 'mapfi!*);

% mapfi* maps a function, (or just simp*) onto an indexed object, 
% rewriting that object. The original value is saved.
% The multiplier of the object always becomes 1 after mapfi is called.
% Either just the name of the object, or an object reference may be
% given, in which case simp!* is mapped. If a function call is made,
% then that function is used: eg mapfi (sub(r=a,f[a,s])); maps sub
% over all elements of f. neat eh!?

symbolic procedure mapfi!* (u);
begin scalar oprnd, lex, lex1, lex2, tvalue, stck!*, prt, inn, indices, indexx;
  inn := indices := 'nil;
  spread3 (mapfi!-args(car u), oprnd, inn, indexx);  % this sets inn and indices
  indices := igen (indexx,
			get (inn, 'restricted) or get (inn, 'indices),
		     get (inn, 'symmetry), get (inn, 'internal!-mapping));
  % this will get messed up with recursive calls to mapfi no possible
  % with externally mapped indices.
  if inn then saveobj (inn);  % save object
  tvalue := get (inn, 'tvalue);
  setlis (alphalist!*, alphalist!*);	% clear

  if not inn then % no indexed obj in expression
    return simp!* (aeval list ('!*sq, simp!* (oprnd), 'nil));
  if inn and not mycar indices then <<
    prt := get (inn, 'protection);	% if its protected the write will fail
    put (inn, 'protection, 'nil);
    writetnsr (inn, 'nil, simp!* (aeval list ('!*sq, simp!* (oprnd), 'nil)), 't);
    put (inn, 'protection, prt);        % restore protection
    return (inn . 1)
    >>;
  foreach indexx in indices do <<		% for each explicit element, apply function.
    if !*showindices or !*peek then pbol (indexx);

     % if car indices in the external!-mapping, then call mapfi here?
    if lex := mycdr assoc (indexx, get (inn, 'external!-mapping)) then
    <<
       % this is dumb, but easier than rewriting mapfi!-args to handle rdr's
       mapfi!* (list (list (car lex, 'findex . cadr lex)));
% delete this line if multipliers are removed.
       ext!-map (inn, indexx, car lex, cadr lex,  % rewrite link
	   multsq (caddr lex, get (inn, 'multiplier)), 
		if flagp (inn, 'cnj) then not cadddr lex else cadddr lex);
    >> else <<
      setlis (alphalist!*, indexx);
      % The outer SIMP!* IS needed!
      lex2 := simp!* aeval (list ('!*sq, simp!* (pre!-eval (oprnd, 'nil)), 'nil));
      if !*peek then <<spaces(tabbing!*); prin1 (indexx);
	    if not mycar lex2 then write " is zero.",!$eol!$ else
				write " is not zero.",!$eol!$>>;
      if assoc (indexx, tvalue) then 
      <<
	  % run down tvalue to find matching index, copy all values until match.
	  while (not (mycaar (tvalue) = indexx)) do
	  <<
	    stck!* := (mycaar (tvalue) . readtnsr (inn, mycaar (tvalue))) . stck!*;
	    tvalue := mycdr (tvalue)
	  >>;
	tvalue := mycdr (tvalue)
      >>;
      if get (inn, 'implicit) or mycar (lex2) then
	stck!* := (indexx . lex2) . stck!* % insert new value (if not 0)
  >> >>;
%  terpri();
  setlis (alphalist!*, alphalist!*);
  while tvalue do <<	% read out remaining elements to get multiplier
    stck!* := (mycaar (tvalue) . readtnsr (inn, mycaar (tvalue))) . stck!*;
    tvalue := mycdr (tvalue)
  >>;
  put (inn, 'tvalue, reverse (stck!*));	% place new value
  put (inn, 'multiplier, 1 ./ 1);	% clear multiplier
  remflag (inn, 'cnj); 			% clear conjugation flag
  return (inn . 1);
end;

symbolic procedure mapfi!-args (u);
% This routine parses the input to mapfi*() looking for indexed objects.
% The input is completely unevaluated as yet, and indexed object references
% (ie things with an index) are still in the form where the object name
% is in a function location, and the index has 'FINDEX in it (ie it
% has not passed through mkrdr()). The recursive hunt for an indexed object
% leaves an 'rdr form in place of the object, and isolates the name and the 
% index.
begin scalar lex, indexx, readflg!*, dum, inn, indexx;
  readflg!* := 't;	% keeps SIMPRDR from over-eval'ing
  if not u then return 'nil
  else if indexed (u) then <<
    if inn then <<lex := u; goto a>>; % if inn is set, there is another obj in input
    spread4 (resolve!-subobj (u, 
	head (alphalist!*, mycar (get (u, 'indices)))), inn, indexx, dum, dum);
    return list (list ('rdr, inn, head (alphalist!*,
			mycar (get (inn, 'indices)))), inn, indexx)
  >>
  else if atom (u) then  
% it is possible for a non-indexed atom to be a generic shift 
    if indexed (lex := resolvegeneric (u)) then <<
      if inn then goto a;
      inn := lex;
      indexx := head (alphalist!*, mycar (get (inn, 'indices)));
    return list (list ('rdr, inn, head (alphalist!*,
			mycar (get (inn, 'indices)))), inn, indexx)
    >> else return list (u, 'nil, 'nil)
  else if not atom u and indexed (car u) % indexed ref, in parser form (not simped)
	and not atom (cadr u) and (caadr u eq 'findex) then <<  
    lex := reval u;    % apply mkrdr and simprdr to ref.
        % the arg is totally unevaled until the reval. A minus may be
        % introduced by the symmetries, but it has no meaning and is ignored.
    if mycar (lex) eq 'minus then lex := mycadr (lex);
    lex := getnme (lex, '(t . t), 'mapfi);	% name of object from reference
    if inn then goto a;
    spread4 (resolve!-subobj (mycar lex, mycadr lex), inn, indexx, dum, dum);
    return list (list ('rdr, inn, head (alphalist!*,
			mycar (get (inn, 'indices)))), inn, indexx)
  >> else <<
    lex := foreach x in u collect mapfi!-args (x);
    lex := foreach x in lex collect <<
       if cadr x then <<inn := cadr x; indexx := caddr x>>;
	car x >>;
    return list (lex, inn, indexx)
  >>;
a:
  merror (mkmsg list ("too many indexed objects in arg: % %.",
		      inn, lex), 't);
end;

put ('mkcoords, 'simpfn, 'mkcoords!*);

% mkcoords* sets up the call to mkcoords!*!*.

symbolic procedure mkcoords!* (u);
  mkcoords!*!* (mycar getnme (mycar (u), '(nil . t), 'mkcoords), mycadr (u)) . 1;

% mkcoords!*!* constructs a vector from the coordinates list, primarily for
% use by the derivative routines, although the user can call it too.
% if crds is non-'nil, then this coordinate list is used instead of the
% global one. 

symbolic procedure mkcoords!*!* (tnsr, crds);
begin scalar i, lex;
  mktnsr!* (tnsr, list (1), 'nil, 'nil, 'coordinates,
	    "Coordinate vector");
  crds := coords!*;
  put (tnsr, 'coords, crds);
  i := mycar (getindices(1));
  lex := crds;  % this was COORDS
  while lex do <<	% place each element
    writetnsr (tnsr, list (i), simp (mycar (lex)), 't);
    lex := mycdr (lex);
    i := i + 1
  >>;
  protect!* (tnsr, 'w);
  return (tnsr);
end;

put ('delta, 'simpfn, 'delta!*);

% delta* creates the delta function (really an indexed object) for the 
% type of index given as the second argument. this function really doesn't
% need to be user callable since the system sets up its own delta functions
% when sys.env is read-in. these objects are not seen in the indexed!-names list.

symbolic procedure delta!* (u);
begin scalar tnsr, ex, lex, lex1;
  tnsr := mycar getnme (mycar (u), '(nil . nil), 'delta);
  if (ex := mycadr (u)) then ex := abs (ex)
  else ex := 1;	% default is a tensor delta.	
  if indexed (tnsr) then protect!* (tnsr, 'nil);
  lex := mktnsr!* (tnsr, list (ex, -ex), 'nil, 'nil, 'delta,
	    "Delta function");
  if mycar (indexed!-names) eq tnsr then indexed!-names := mycdr (indexed!-names);
  lex1 := igen ('(a!# b!#), indexlim (list (ex, -ex)), 
	ifmtsym '((0 1 2)), 'nil);
  while lex1 do <<
     writetnsr (lex, mycar (lex1), '(1 . 1), 't);
     lex1 := mycdr (lex1)
  >>;
  lex := makename (append (explode (tnsr), explode ('!_!c)));
  if indexed (lex) then protect!* (lex, 'nil);
  lex := mktnsr!* (lex,
                list (ex, ex), ifmtsym '((0 1 2)), 1, 'deltau,
		   "Raised index delta function");   % make offspring
  if mycar (indexed!-names) eq lex then indexed!-names := mycdr (indexed!-names);

  lex1 := makename (append (explode (tnsr), explode ('!_!d)));
  if indexed (lex1) then protect!* (lex1, 'nil);
  lex1 := mktnsr!* (lex1,
                list (-ex, -ex), ifmtsym '((0 1 2)), 1, 'deltad,
		    "Lowered index delta function");
  if mycar (indexed!-names) eq lex1 then indexed!-names := mycdr (indexed!-names);
  protect!* (tnsr, 'kw);
  protect!* (lex, 'kw);
  protect!* (lex1, 'kw);
  put (tnsr, 'coords, 'nil);
  put (lex, 'coords, 'nil);
  put (lex1, 'coords, 'nil);
  put (lex, 'printname, tnsr);
  put (lex1, 'printname, tnsr);
  put (lex, 'shift, list ('t, lex, tnsr, lex1));
  put (tnsr, 'parent, lex);
  put (lex1, 'parent, lex);
  return (tnsr . 1);
end;

put ('multiplier, 'simpfn, 'multiplier!*);

% multiplier* allows the user easy access to read or replace
% the multiplier of an indexed object.

symbolic procedure multiplier!* (u);
  resimpscalar (mycadr (u), mycar getnme (mycar (u), '(t . 't), 'multiplier),
		'multiplier);


put ('describe, 'simpfn, 'describe);

symbolic procedure describe (u);
  describe!* (mycar getnme (mycar (u), '(t . t), 'describe), mycadr (u), 't)  . 1;

% describe!* allows the user to set or examine the description string
% attached to an object

symbolic procedure describe!* (tnsr, desc, prn);
begin;
  if (desc and not (stringp (desc) or idp (desc))) then <<
    merror (mkmsg list(
      "description is not a string or atom: %", desc), 't)
  >>;
  % If nil string get value, otherwise set it.
  desc and put (tnsr, 'description, mkmsg list("%",desc));
  prn and <<write (get (tnsr, 'description)); terpri!*('t)>>;
  return (tnsr);
end;

flag ('(saveobj restoreobj), 'opfn);

symbolic procedure saveobj (obj);
  <<
     put ('saveobj!*, 'prop, uniqkern (prop (obj)));
     put ('saveobj!*, 'name, obj);
     if not unboundp (obj) then set ('saveobj!*, eval (obj));
     obj
  >>;

symbolic procedure restoreobj ();
begin scalar obj;
   write "restoring ", obj := get ('saveobj!*, 'name), !$eol!$;
   mysetprop (obj, get ('saveobj!*, 'prop));
   if not unboundp ('saveobj!*) then set (obj, eval ('saveobj!*));
   return obj;
end;

put ('info, 'simpfn, 'info!*);

symbolic procedure info!* (u);
<<
  foreach x in match!-names (u, append (indexed!-names, generic!-names))
	 do info!*!* x;
  't ./ 1
>>;

symbolic procedure info!*!* (tnsr);
begin scalar lex, lex1, lex2, indexx, force!-sym, wid; 
  if not indexed tnsr then return;
  indexx := foreach x in head (alphalist!*, car get (tnsr, 'indices))
	collect car explode x; 
  wid := rdrprintwidth (get (tnsr, 'printname), indexx, get (tnsr,'indextype));
  lex1 := list ('rdr, tnsr, indexx);

  prin2!* mkmsg list ("INFORMATION ABOUT  %:", tnsr);
  terpri!* 'nil;
  prin2!* mkmsg list (
       "is a % with indextype %",
        (lambda x; if x eq 'mixed then
	"mixed object" else x)(get(tnsr, 'indexed)), get (tnsr, 'indextype));
%  terpri!* 'nil;
  prin2!* " and looks like   ";
  maprint (lex1, 0);
  ymin!* := -1;   % ensure some elbow room
  ymax!* := 1;
  terpri!* 'nil;
  prin2!* mkmsg list ("has coordinates %", get (tnsr, 'coords));
  terpri!* 'nil;
  if get (tnsr, 'restricted) then <<prin2!* mkmsg 
      list ("has indices restricted to run from % to %.",
	index!-string cadr get (tnsr, 'restricted),
               index!-string caddr get (tnsr, 'restricted));
      terpri!* 'nil 
  >> else <<
	  prin2!* mkmsg list ("has indices running from % to %",
		index!-string cadr get (tnsr, 'indices), 
                             index!-string caddr get (tnsr, 'indices));
	  terpri!* 'nil
  >>;
  if lex := get (tnsr, 'symmetry) then <<
    prin2!* mkmsg list ("has symmetries % which mean: ", ufmtsym lex);
    terpri!* 'nil;
    force!-sym := 't;   % causes orderindex1 and hermitian to always force swaps
    foreach x in lex do
     <<
       if (2 * wid + 5) > (linelength (nil) - 1 - posn!*) then terpri!* 'nil;
       maprint (lex1, 0);
       % sgnsym() breaks when applied to hermitians
       if car x neq 'h and sgnsym x eq 0 then
         << 
           prin2!* mkmsg list ("= 0 for %", mynth (indexx, caadr x));
		% mkmsg will not print !'s
           foreach y in cddr x do <<prin2!* " != "; 
		prin2!* mynth (indexx, car y)>>
       >> else <<
         prin2!* " = ";
         lex := syma (indexx, list x, 'nil, 't);
         lex2 := list ('rdr, tnsr, car lex);
         if mycaddr lex then lex2 := list ('cnj, lex2);
         if minusp cadr lex then lex2 := list ('minus, lex2);
         maprint (lex2,0);
         if length x > 3 then prin2!* "..." ; % there are more permutations 
         if car x eq 'h then prin2!* "Hermitian"
       >>;
       prin2!* (";  ");
       ymin!* := -1;   % ensure some elbow room
       ymax!* := 1;
     >>;
    terpri!* ('t)
  >>;
  
  if (lex :=  get (tnsr, 'internal!-mapping)) then
  <<
    prin2!* "has the following indices mapped internally:";
    terpri!* 'nil;
    foreach x in lex do <<
       if (2 * wid + 5) > (linelength (nil) - 5 - posn!*) then terpri!* 'nil;
       maprint (list ('rdr, tnsr, car x), 0); 
       prin2!* " --> ";
       lex2 := list ('rdr, tnsr, cadr x);
       if mycadddr x then lex2 := list ('cnj, lex2);
       if minusp mycaddr x then lex2 := list ('minus, lex2)
       else if zerop mycaddr x then lex2 := 0;
       maprint (lex2, 0);
       prin2!* (";  ")
     >>;
    terpri!* 'nil
  >>;
  if (lex :=  get (tnsr, 'external!-mapping)) then
  <<
    prin2!* "has the following indices mapped externally:";
    terpri!* 'nil;
    foreach x in lex do <<
       if (2 * wid + 5) > (linelength (nil) - 5 - posn!*) then terpri!* 'nil;
       maprint (list ('rdr, tnsr, car x), 0); 
       prin2!* " --> ";
       lex2 := list ('rdr, cadr x, caddr x);
       if mycadddr mycdr x then lex2 := list ('cnj, lex2);
       lex2 := (lambda (x,y); begin scalar lex; 
        lex := reval mk!*sq y;
	if zerop lex then return 0
        else if lex = 1 then return x
        else if lex = -1 then return list ('minus, x)
        else return list ('times, lex, x); end)(lex2, mycadddr x);
       maprint (lex2, 0);
       prin2!* (";  ")
     >>;
    terpri!* 'nil
  >>;
  if (lex := get (tnsr, 'generic)) then <<
    prin2!* "is a generic object ";
    lex := resolvegeneric tnsr;	
    if lex neq tnsr then prin2!* mkmsg list ("referring to %", lex)
    else prin2!* "with no target"
  >>
  else if (lex := get (tnsr, 'subobj)) then <<
    prin2!* mkmsg list ("is a sub-object of % with this mapping: ",
	car lex);
    if (2 * wid + 5) > (linelength (nil) - posn!*) then terpri!* 'nil;
    maprint (list ('rdr, tnsr, foreach x in cadr lex collect car explode x), 0); 
    prin2!* " --> ",
    lex2 := list ('rdr, car lex, foreach x in caddr lex collect car explode x);
    if mycar mycddddr lex then lex2 := list ('cnj, lex2);
    lex2 := (lambda (x,y); begin scalar lex; lex := reval mk!*sq y;
	if zerop lex then return 0
        else if lex = 1 then return x
        else if lex = -1 then return list ('minus, x)
        else return list ('times, lex, x); end)(lex2, mycadddr lex);
    maprint (lex2, 0)
  >> else <<
    prin2!* mkmsg list ("has % explicit components", length get (tnsr, 'tvalue));
  if get (tnsr, 'implicit) then prin2!* " and there are also implicit components"
  >>;
  terpri!* 'nil;
%  prin2!* "has mulitplier ";
%  maprint (mk!*sq get (tnsr, 'multiplier), 0);
%  if get (tnsr, 'cnj) then prin2!* " and the conjugation flag is on";
%  terpri!* 'nil;
  if (tnsr eq getmetric!* (-1*(mycar get (tnsr, 'indextype) or 0), 
			       currentmetric, 'nil)) then <<
    prin2!* mkmsg list ("is the current metric for %s", get (tnsr, 'indexed));
    terpri!* 'nil
   >>;
  if lex := get (tnsr, 'cometric) then <<
	prin2!* "is a co-metric with ";
	foreach x in lex do <<prin2!* x; prin2!* " ">>;
	terpri!* 'nil
  >>;
  if get (tnsr, 'parent) then <<
	prin2!* mkmsg list ("is a child of %.", get (tnsr, 'parent));
        terpri!* 'nil
  >> else if mycdr get (tnsr, 'shift) then <<
	prin2!* "is the parent of: ";
	foreach x in mycddr get (tnsr, 'shift) do <<prin2!* x; prin2!* " ">>;
        terpri!* 'nil
  >>;
  % change this when the shift flag moves to a sep prop -V
%  if get (tnsr, 'altmetric) and not mycar get (tnsr, 'shift) then <<
%    prin2!* mkmsg list ("has indices shifted by the metric %", car get (tnsr, 'altmetric));
%    terpri!* 'nil
%  >>;
  terpri!* 'nil;  
  if get (tnsr, 'cov) then <<
    prin2!* mkmsg list ("has covariant derivative %", caddr get (tnsr, 'cov));
    terpri!* 'nil
  >>;
  if get (tnsr, 'odf) then <<
    prin2!* mkmsg list ("has ordinary derivative %", caddr get (tnsr, 'odf));
    terpri!* 'nil
  >>;
  if get (tnsr, 'conjugate) then <<
    prin2!* mkmsg list ("is conjugate to %", car get (tnsr, 'conjugate));
    terpri!* 'nil
  >>;
%  prin2!* mkmsg list ("itype: %,", get (tnsr, 'itype) or "none");
%  posn!* := (posn!* < 20 and 20 or (posn!* + 3));
  prin2!* mkmsg list ("is % protected.", 
	(lambda x; if x eq 2 then "write" else if x eq 3 then "kill" else
	if x eq 6 then "kill and write" else "not")(get (tnsr, 'protection)));
  terpri!* 'nil;
  if get (tnsr, 'description) then <<
    prin2!* mkmsg list ("is described as: %", get (tnsr, 'description));
    terpri!* 'nil
  >>;
  terpri!* ('nil);
  terpri();
  return tnsr;
end;

endmodule;
;end;
