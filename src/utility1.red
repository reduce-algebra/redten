%***************************************************************************
%  FILE = utility1.red
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
module 'util1;
%symbolic;
%in "$redten/decl.red"$


% alphalist* contains all the indices ever used by the system for its
% work. The user should NEVER fiddle with these guys. 


alphalist!* := '(a!# b!# c!# d!# e!# f!# g!# h!# i!# j!# k!# l!# m!# n!# 
                 o!# p!# q!# r!# s!# t!# u!# v!# w!# x!# y!# z!# !#1); 

% patternindex determines whether the given index is a pattern i.e. not
% all the indices reduce to integers.
% I'm not sure right now, but i dont think patternindex is the same as 
% not fixedindex. otherwise, why would i write it??

symbolic procedure patternindex (indexx);
begin;
  indexx := indh (indexx);	% clear out shift ops.
  loop:
    if not idp (mycar (indexx)) and not (mycar (fderiv (indexx)) = 1) then
        return ('nil);
    indexx := mycdr (indexx);
    if not indexx then return ('t);
  go to loop;
end;

% CANONINDEX produces a canonical form for an index by replacing each
% pattern index with a choice from the ALPHALIST!*. The result
% should be the same for any choice of pattern indices. Integer
% indices and derivative ops are passed through. This function does
% not know about shifted indices. 

symbolic procedure canonindex (indexx);
begin scalar lis, lis1, lex, lex1; integer i;
    i := 0;
    while indexx do <<
        if fixp (lex := mycar (indexx)) or (lex eq '!*br)
            or (lex eq '!*dbr) then lis := lex . lis
	else if (lex1 := assoc (lex, lis1)) then
           lis := cdr (lex1) . lis
	else <<
           lex1 := mynth (alphalist!*, i := i + 1);
           lis1 := (lex . lex1) . lis1;
           lis := lex1 . lis
        >>;
	indexx := mycdr (indexx)
    >>;
    return (reverse (lis) . lis1);
end;

% checktype checks whether a given expression has a car equal to type,
% avoiding a problem with taking the car of an atom 
% type can be a list of types to check

symbolic procedure checktype (ex, type);
  if atom (ex) then 'nil
  else if atom type then mycar ex eq type
  else memq (mycar (ex), type);

% cleaner prints the finished banner from many functions if they were not
% called at the top level, and calls cleartmp if they were.

symbolic procedure cleaner (name);
begin scalar lex;
% on function calls program!* has the form (aeval (list (quote <function>)))
  subobj!-shift();
  subobj!-odf();
  if car program!* eq 'aeval and caadr program!* eq 'list and
	car cadadr program!* eq 'quote and 
	(cadr cadadr program!* eq name
	   or mycadr cadadr program!* eq get (name, 'newnam)) 
    then <<
      untabprint (nil);
      fast!-writetnsr!-cleanup();   % get everyone in order.
      cleartmp();
      return 't;
  >> else <<
    untabprint (list (name, " finished."));
    return nil
  >>;
end;

flag ('(cleartmp), 'opfn);

% cleartmp removes temporary objects created 


symbolic procedure cleartmp ();
begin scalar lis, lex, killed!*;
  tmpnames!* := 0;
  setlis (alphalist!*, alphalist!*);
  lex := indexed!-names;
  while lex do << 	% look for temps among indexed objects.
    if head (explode (mycar (lex)), 4) = head (explode ('!#tmp), 4) then
      lis := mycar (lex) . lis;
    lex := mycdr (lex)
  >>;
  mapcar (lis, 'kill!*);
  return ('t);
end;

% cnstn generates a list of n repetitions of indice.

symbolic procedure cnstn (indice, n);
begin scalar indexx;
  while not (n = 0) do <<
    indexx := indice . indexx;
    n := n - 1
  >>;
  return (indexx);
end;

% deriv looks into the given index and returns either the location of
% the indicated derivative operator (ex) or, if ex is 'nil, whether
% any derivative operator exists in the index.

symbolic procedure deriv (indexx, ex);
  if ex then look (indexx, ex, 1)
  else look (indexx, '!*br, 1) or look (indexx, '!*dbr, 1);

% fderiv looks into an index and returns the location and type of the
% first derivative operator.

symbolic procedure fderiv (indexx);
begin scalar lex, lex1;
  lex := deriv (indexx, '!*br);
  lex1 := deriv (indexx, '!*dbr);
  if (not lex and not lex1) then return ('nil)
  else if (not lex or lex1 and lex1 < lex) then
    return (list (lex1, '!*dbr))
  else return (list (lex, '!*br));
end;

flag ('(getfam killfam), 'opfn);


symbolic procedure getfam (u);
begin scalar tnsr, lis, lex, lex1, n;
  tnsr := mycar getnme (u, '(t . nil), 'getfam);
  if not tnsr then return 'nil;
  lex := indexed!-names;
  % all family names have the form <parent>_, we must explode the makename
  % because the explosion of a name containing special chars is not always
  % the same as just appending the chars in a list.
  lex1 := explode makename append (explode (tnsr), list ('!_)); 
  n := length (lex1);
  lis := list (tnsr);   % so this name is first
  while lex do <<
    if head (explode mycar lex, n) = lex1 then
	if not memq (mycar lex, lis) then  lis := mycar lex . lis;
    lex := cdr lex;
  >>;
  return reverse lis;
end;

symbolic procedure remfam (u);
begin scalar killed!*, lex;
  for each x in mycdr getfam (u) do kill (x);
  terpri ();
  write (" ", killed!*);
  terpri ()
end;



% free1 checks ex1 to see if the atoms in ex2 are not present anywhere.
symbolic procedure free1 (ex1, ex2);
begin;
  if memq (ex1, ex2) then return 'nil;
%  if ex1 = ex2 then return ('nil);
    loop:
      if atom (ex1) then return ('t)
      else if not free1 (mycar (ex1), ex2) then return ('nil);
      ex1 := mycdr (ex1);
    go to loop;
end;

% getindices returns the index run for the given indextype element.

symbolic procedure getindices (n);
begin scalar lex;
  if not fixp (n) or not (lex := getindextype (abs (n))) then
    merror (mkmsg list ("bad indextype element: %", n), 't)
  else return (mycaddr (lex));
end;

% getnme detemines what the object name is from the given input 
% which may be just the name, an indexed form,  a shift request,
% or a function call eg, christoffel1();
% flgs car set means err out if the name is not indexed.
% flgs cdr set means a name is required
% from is the name of the calling routine.
% return is (nil), or (name), or (name index)

symbolic procedure getnme (ex, flgs, from);
begin scalar lex, used, mltp, cflg, readflg!*, no!-index!-err!*;
  readflg!* := 't;   % keep simp from over evaling
  no!-index!-err!* := 't;   % mkrdr will err rather than do a display if no index
  % see if incoming atom already has a used!* flag. The revel() below
  % will set it if it was not already there.
  if atom ex and flagp (ex, 'used!*) then used := 't;
  % catch unevaled indexed refs to not yet created objects
  if not atom ex and not atom cadr ex and caadr ex eq 'findex and
	not indexed (car ex) then ex := list ('rdr, car ex, cdadr ex)
  else ex := reval ex;    % goes to prefix form and evals args

  mltp := 1 ./ 1;
  cflg := 'nil;   % yes its redundant..
  while checktype (ex, '(minus cnj)) do <<
     if mycar ex eq 'minus then mltp := multsq (mltp, -1 ./ 1)
          else if mycar ex eq 'cnj then cflg := not cflg;
          ex := mycadr ex
  >>;
  if not ex or ex eq 0 then
    if cdr flgs then merror (mkmsg list ("input name required by %", from), 't)
    else return (list (nil))
  else if idp (ex) then 
    <<
        lex := resolvegeneric (ex);
	if not indexed (lex) and car flgs then 
                merror (mkmsg list (" % not indexed (from %).", lex, from), 't)
        else <<
           % remove used!* flag if not there initially
           if not used then remflag (list (lex), 'used!*);
	   return list (lex, 'nil, 'nil, 'nil)
        >>
    >>
  else if checktype (ex, 'rdr) then <<  % is an indexed object.
      % note shift takes care of the generic check.
%    if not free1 (mycaddr (ex), '(!*at!* !*at!- !*at!+)) then 
        return append (mycdr (shift!*!* (ex, 'nil)), list (mltp, cflg))
%    else return (mycdr (ex))
    >>
  else merror (mkmsg list ("bad input: % (from %).", ex, from ), 't);
end;

% head returns the first n elements of the list lis, or all of lis if it
% has fewer than n elements.

symbolic procedure head (lis, n);
begin scalar lex;
  while lis and not (n = 0) do <<
    lex := mycar (lis) . lex;
    lis := mycdr (lis);
    n := n - 1
  >>;
  return (reverse (lex));
end;

% ind returns the actual indice, regardless of whether it was buried
% in a list (by tracesym). i.e.  a -->a, (a) --> a.

symbolic procedure ind (ex);
  if atom (ex) then ex
  else mycar (ex);

% indh is similar to, but smarter than ind. it returns the actual indice
% from a shifted form, and can map itself over an index.
% so: (a (*at* b) (c)) --> (a b (c))
% it doesn't handle the case ind does.

symbolic procedure indh (ex);
begin scalar lex;
  if atom (ex) or not ex then return (ex)
  else if checktype (ex, '(!*at!* !*at!- !*at!+)) then return (mycadr (ex));
  lex := for each x in ex collect indh (x);
  return (lex);
end;

% insert inserts an element into a list  at position n, either overwritting
% the element already there (cutout = 't) or going just after that element.
% if cutout is 't and inp is 'nil, the n'th element is removed.

symbolic procedure insert (lis, inp, n, cutout);
begin scalar lex;
  if n > length (lis) then <<  % just append the element (at pos N)
%    IF INP AND NOT CUTOUT THEN 
	% the MAPCAR (CNSTN ()) is a cheap way of getting a list of NILs
	return (append (lis, append (mapcar (cnstn (1, n - length (lis) - 1),
	     'idp), list (inp))));
%    ELSE RETURN (LIS)
  >>;
  while lis and not (n = 1) do <<  % stack up the first n - 1 elements.
    lex := mycar (lis) . lex;
    lis := mycdr (lis);
    n := n - 1
  >>;
  if cutout then <<    		% remove the n'th and discard.
    lis := mycdr (lis);
    if inp then lis := inp . lis   % if inp is not 'nil, put it in.
    >>
  else lis := inp . lis;	% just add the new element.
  return (append (reverse (lex), lis));  % put the list back together.
end;

% fixedindex determines whether the given index is a fixed index, i.e.
% whether all indices reduce to integers. 

symbolic procedure fixedindex (indexx);
  if memq ('nil, mapcar (indexx, 'fixp)) then 'nil else 't;

symbolic procedure sloppy!-fixedindex (indexx);
  fixedindex (car stripops (indexx, iops!*));


% look looks into a list for the element el, and returns its location
% (where the first element is at location n).  if the element is not there,
% look returns 'nil.

symbolic procedure look (lis, el, n);
begin scalar i;
  i := length (member (el, lis));
  if i = 0 then return ('nil)
  else return (length (lis) - i + n);
end;

%global '(!*raise !*lower); 

% makename compresses a list into a name and interns it.
% we play with raise and lower because compress ('(a s d)) will change the
% case of the input if someone changes the switches.
symbolic procedure makename (u);
begin scalar raise, lower, lex;
  raise := !*raise; !*raise := 'nil;
  lower := !*lower; !*lower := 'nil;
  lex := intern (compress (u));
  !*raise := raise; !*lower := lower;
  return (lex);
end;

symbolic procedure index!-string (indexx);
% this routine converts an index to a string (flat format).
begin scalar lst, lex;
  lst := list '![;
  while indexx do <<
     lex := pop indexx;
     if checktype (lex, shift!-iops!*) then
       <<
         nconc (lst, explode (get (mycar lex, 'prtch2) 
				or get (mycar lex, 'prtch)));
         lex := mycadr lex
       >>;
     nconc (lst, explode (get (lex, 'prtch2) or get (lex, 'prtch) or lex));
     if indexx and not memq (lex, '(!*lsqb !*rsqb !*br !*dbr))
	and not memq (mycar indexx, '(!*rsqb !*rcub)) 
	then nconc (lst, list '!,);
  >>;
  nconc (lst, list '!]);
  lex := 'nil;
  while lst do <<  % remove !! and interior !"
    if mycar lst neq '!! and mycar lst neq '!" then lex := mycar lst . lex;
    lst := mycdr lst
  >>;
  return compress ('!" . reverse ('!" . lex));
end;

symbolic procedure rdr!-string (exp);
%  mkmsg list ("%%", get (mycadr exp, 'printname) or mycadr exp,
% prints as a string, so the full name should be used, since the index
% structure can't be seen
  mkmsg list ("%%", mycadr exp, index!-string mycaddr exp);

symbolic procedure mkmsg (u);
begin scalar format, lis, x, lex;
  lis := '();
  format := pop u;
  if not stringp (format) then
     merror ("format not a string.", 't)
  else format := explode format;

  while format do <<
     x := pop format;
     if x eq '!\ and mycar format eq '!% then % \% gets a literal %
	<<push ('!%, lis); pop format>>
     else if x neq '!% or not u then push (x, lis)
     else <<
	% char is a % and there are still args to look at.
       lex := reverse explode mycar u;
       if stringp (pop u) then lex := delete ('!", delete ('!", lex));
       lis := append (lex, lis)
     >>
  >>;
  lex := reverse foreach x in lis join 
	if x eq '!! then 'nil
        else if x eq !$eol!$ then list '! % there's a space here!!
	else list x ;
  return (compress lex);
end;

symbolic procedure mapindextype (u);
% MAPINDEXTYPE converts primed spinor indices to unprimed indices, to make
% it easier to compare indextype lists etc. Other equiv type are also mapped.
% It should also check the index runs to make sure they are compatible
% (if not, then dont map).
begin scalar lex;
  if atom (u) then return ('nil);
  lex := foreach x in u collect (mycar (getindextype (abs x)) or x) . sign (x);
  lex := foreach x in lex collect (mycadr assoc (mycar x, defindextype!*) 
     or mycar x)  * mycdr x;
  return lex;
end;

% mascii will convert numbers to ascii chars, or chars to their
% equivalents. in franz there are routines that can be combined into
% another routine for this.
% For portability, we shall always use our own code. 22/05/91

%SYMBOLIC PROCEDURE MASCII (X);   % for Franz
%  IF FIXP (X) THEN ASCII (X)
%  ELSE GETCHARN (X, 1);

%SYMBOLIC PROCEDURE MASCII (EX);   % for PSL
%  IF FIXP (EX) THEN INT2ID (EX)
%  ELSE ID2INT (EX);

symbolic procedure mascii (ex);
begin scalar lex;
  if fixp (ex) then <<
    lex := atsoc (ex,
                     '((32 . ! ) (33 . !!) (34 . !") (35 . !#) (36 . !$)
               (37 . !%) (38 . !&) (39 . !') (40 . !() (41 . !)) (42 . !*)
               (43 . !+) (44 . !,) (45 . !-) (46 . !.) (47 . !/) (48 . !0)
               (49 . !1) (50 . !2) (51 . !3) (52 . !4) (53 . !5) (54 . !6)
               (55 . !7) (56 . !8) (57 . !9) (58 . !:) (59 . !;) (60 . !<)
               (61 . !=) (62 . !>) (63 . !?) (64 . !@) (65 . !A) (66 . !B)
               (67 . !C) (68 . !D) (69 . !E) (70 . !F) (71 . !G) (72 . !H)
               (73 . !I) (74 . !J) (75 . !K) (76 . !L) (77 . !M)
               (78 . !N) (79 . !O) (80 . !P) (81 . !Q) (82 . !R) (83 . !S)
               (84 . !T) (85 . !U) (86 . !V) (87 . !W) (88 . !X) (89 . !Y)
               (90 . !Z) (91 . ![) (92 . !\) (93 . !]) (94 . !^) (95 . !_)
               (96 . !`) (97 . !a) (98 . !b) (99 . !c) (100 . !d) (101 . !e)
        (102 . !f) (103 . !g) (104 . !h) (105 . !i) (106 . !j) (107 . !k)
        (108 . !l) (109 . !m) (110 . !n) (111 . !o) (112 . !p) (113 . !q)
        (114 . !r) (115 . !s) (116 . !t) (117 . !u) (118 . !v) (119 . !w)
        (120 . !x) (121 . !y) (122 . !z) (123 . !{) (124 . !|) (125 . !})
        (126 . !~)) );
    if not lex then return ('nil)
    else return (mycdr (lex))
    >> else <<
    lex := atsoc (ex,
             '((!  . 32) (!! . 33) (!" . 34) (!# . 35) (!$ . 36)
               (!% . 37) (!& . 38) (!' . 39) (!( . 40) (!) . 41) (!* . 42)
               (!+ . 43) (!, . 44) (!- . 45) (!. . 46) (!/ . 47) (!0 . 48)
	       (!0 . 48) (!1 . 49) (!2 . 50) (!3 . 51) (!4 . 52) (!5 . 53) (!6 . 54)
               (!7 . 55) (!8 . 56) (!9 . 57) (!: . 58) (!; . 59) (!< . 60)
               (!= . 61) (!> . 62) (!? . 63) (!@ . 64) (!A . 65) (!B . 66)
               (!C . 67) (!D . 68) (!E . 69) (!F . 70) (!G . 71) (!H . 72)
               (!I . 73) (!J . 74) (!K . 75) (!L . 76) (!M . 77)
               (!N . 78) (!O . 79) (!P . 80) (!Q . 81) (!R . 82) (!S . 83)
               (!T . 84) (!U . 85) (!V . 86) (!W . 87) (!X . 88) (!Y . 89)
               (!Z . 90) (![ . 91) (!\ . 92) (!] . 93) (!^ . 94) (!_ . 95)
               (!` . 96) (!a . 97) (!b . 98) (!c . 99) (!d . 100) (!e . 101)
        (!f . 102) (!g . 103) (!h . 104) (!i . 105) (!j . 106) (!k . 107)
        (!l . 108) (!m . 109) (!n . 110) (!o . 111) (!p . 112) (!q . 113)
        (!r . 114) (!s . 115) (!t . 116) (!u . 117) (!v . 118) (!w . 119)
        (!x . 120) (!y . 121) (!z . 122) (!{ . 123) (!| . 124) (!} . 125)
        (!~ . 126)) );
    if not lex then return (-1)
    else return (mycdr (lex))
    >>;
end;

% merror is the system error routine. given a message in list form, it
% prints each element, and if stat is 't then it calls a real error routine.
% if from is non-'nil, the name of the routine calling merror (i.e from)
% is also printed.
symbolic procedure merror (mes,  stat);
  if stat or !*allerr then  % if backtrace is on then allow tracing of errors
    if !*backtrace then << lpriw ("Error:", mes); mclear(); error(95,"")>>
    else << lpriw ("Error:", mes); mclear(); error1()>>
  else lpriw ("Warning:", mes);


% lifted from alg1.red and modified.
symbolic procedure mynth (u,n);
   mycar mypnth(u,n);

% this version of PNTH acts like that in psl: MYPNTH ('(a s f), 4) returns
% nil and not an error as the reduce pnth does.

symbolic procedure mypnth (u,n);
    if n=1 or null u then u
    else mypnth (cdr u,n-1);

symbolic procedure mysetprop (u, v);
% reliably set the new property list of u to be v. The setprop() in 3.3 under
% psl 3.4(?) does not seem to clear the AVALUE prop correctly.
<<
  foreach x in prop(u) do if atom x then remflag (list u,x)
	else remprop(u, car x);
  foreach x in v do if atom x then flag (list u, x) 
	else put (u, car x, cdr x)
>>;

% orderindex compares the index lis1 to the index lis2 and reports on whether
% lis1 is <,= or > than lis2. it runs down the indices and compares elements.

symbolic procedure orderindex (lis1, lis2);
begin;
  % ya know we could return '!= here...
%  if lis1 = lis2 or not lis2 then return ('e);
  if not lis2 then return ('e);
  loop:
    if not lis2 then return ('nil)
    else if not lis1 then return ('t)
    else if mycar (lis1) > mycar (lis2) then return ('nil)
    else if mycar (lis1) < mycar (lis2) then return ('t)
    else <<
      lis1 := mycdr (lis1);
      lis2 := mycdr (lis2)
    >>;
   go to loop;
   return 'e;
end;

% print arg at beg of line, and dont move down. UPCURSOR!* defined in sys.env
symbolic procedure pbol (u);
    <<spaces (tabbing!*);prin1 (u); 
           terpri(); foreach x in upcursor!* do prin2 x>>;

% replacindex looks through an expression and replaces object indices 
% with the values indicated in the association list replac.

symbolic procedure replacindex (value, replac);
  if not replac or free1 (value, '(rdr mrdr)) then value
  else if checktype (value, '(rdr mrdr)) then	 % replace indices
    list (mycar value, mycadr (value), sublis (replac, mycaddr (value)))
  else for each x in value collect replacindex (x, replac);

% resimpscalar is called by routines which store scalar
% quantities on the property list of an indexed object
% (eg det, riccisc). the name of the object and the key
% under which the value is stored form the second and
% third arguments. if the first argument is 'nil, the
% value is read-out, if it is 't, simp!* is applied to
% the value, otherwise, it replaces the value.
symbolic procedure resimpscalar (u, tnsr, key);
  if not u then get (tnsr, key)
  else put (tnsr, key, simp!* (u));

% there probably exits a routine like this in reduce but i can't find it.
symbolic procedure sign (num);   % note: want sign(0) = 1
  if num < 0 then -1 else 1;

symbolic procedure set!-defaults!-from!-environment ();
% read environment vars to get default values.
begin scalar lex;
   if lex := getenv ("UPCURSOR") then upcursor!* := list lex;
% must convert a string into a list to get coords from env.
%   if lex := getenv ("COORDS") then coords!* := lex;
   if lex := getenv ("LINES") then 
     <<
       lex := compress delete ('!", delete ('!", explode lex));
       if not fixp (lex) or lex < 0 then
          merror ("LINES env not valid.", 'nil)
       else screenlines!* := lex
     >>;
end;

symbolic procedure begin!-redten ();
<<
   set!-defaults!-from!-environment();
   !*raise := 'nil;
   !*lower := 'nil;
   !*mode := 'algebraic;  % make sure we start in the right mode
   save!-environment ('(!i!n!i!t!i!a!l));
   write version,!$eol!$;
   begin1()  % restart with new prompt support.
>>;


% setlis assigns the elements of the first list with the corresponding
% elements of the second list.

symbolic procedure setlis (lis1, lis2);
begin;
  while lis1 and lis2 do <<
    set (mycar (lis1), mycar (lis2));
    lis1 := mycdr (lis1);
    lis2 := mycdr (lis2)
%	set (pop (lis1), pop(lis2))   % does not compile in CSL!?
  >>;
end;

% sublist returns a segments of a list beginning at position n, and running
% for len elements. the first element of the list corresponds to n = 1.

symbolic procedure sublist (lis, n, len);
  if n < 0 or len < 1 or n > length (lis) then 'nil
  else head (mypnth (lis, n), len);

tmpnames!* := 0; 	% global integer used to generate temp names.

% tmpnames generates a sequence of temporary names of the form #tmp<n>.
% the counter is reset when cleartmp is called.

symbolic procedure tmpnames ();
  makename (append (explode ('!#tmp),
        explode (tmpnames!* := tmpnames!* + 1)));

% top rewrites a multi-depth list at the top-level
symbolic procedure top (u);
begin scalar lex;
  if atom u then return list u
  else foreach x in u do lex := append (lex, top x);
  return lex;
end;

% zpn returns a list of numbers from i to j by k.

symbolic procedure zpn (i, j, k);
begin scalar lis;
  while not (j < i) do <<
    lis := j . lis;
    j := j - k
  >>;
  return (lis);
end;


put ('tabbing!*, 'initl, 0);
tabbing!* := 0;   % tabbing for computing.. messages

symbolic procedure tabthenprint (u);
<<
    spaces (tabbing!* - 2);  % tabbing!* is set for next level down
    write u, !$eol!$
>>;

symbolic procedure tabprint (u);
<<
    spaces (tabbing!*);
    for each x in u do write x;
    terpri();
    tabbing!* := tabbing!* + 2
>>;

symbolic procedure untabprint (u);
<<
    tabbing!* := tabbing!* - 2;
    if (tabbing!* < 0) then tabbing!* := 0; % should not happen, but...
    if u then <<
      spaces (tabbing!*);
      for each x in u do write x;
      terpri()
    >>
>>;

symbolic procedure base!-case!-name (u);
  if base!-case eq '!u!p!p!e!r then upname u
  else if base!-case eq '!l!o!w!e!r then dnname u
  else u;

symbolic procedure match!-names (pats, lis);
begin scalar lex, lex1;
  for each x in pats do begin
    if x eq '!* or x eq 'all then <<lex := reverse lis; return>>;
    lex1 := lis;
    % a name like !R is not resolved
    if car explode x neq'!! then x := resolvegeneric x;
    while lex1 do <<
      if match!-name (x, mycar lex1) and not memq (mycar lex1, lex)
	 then lex := mycar lex1 . lex;
      lex1 := mycdr lex1
    >>
  end;
  return reverse lex;
end;

symbolic procedure prep!-pat (pat);
begin scalar lex, lis, n;
  lex := explode pat;
  n := 0;
  while lex do <<
    if mycar lex eq '!! then <<>>
    else if mycar lex eq '!* then <<
       lis := 'nil . ('!* . lis);
       if mycadr lex eq '!* then lex := mycdr lex   % reduce ** to *
    >> else <<
       lis := aconc (mycar lis, mycar lex) . mycdr lis;
       n := n + 1
    >>;
    lex := mycdr lex
  >>;
  if not mycar lis then lis := mycdr lis;   % eat nil put in after trailing *
  return reverse lis . n;  % n is the # of real chars that must match
end;

symbolic procedure match!-string (string, name);
% must handle ? embedded in string, so 1 char at a time compare needed.
begin;
   loop;
     if not string then return if not name then 't else name;
     if not name then return 'nil
     else if mycar string eq '!? then <<>>
     else if mycar string neq mycar name then return 'nil;
     string := mycdr string;
     name := mycdr name;
   goto loop;
end;

symbolic procedure match!-name (pat, name);
begin scalar lex, lex1, lex2, n, anchored, lex3;
  lex := prep!-pat (pat);
  lex1 := explode (name);

  n := mycdr lex;   % # of real  chars to match
  pat := mycar lex; % prep'ed pattern
  % we first check for anchored matches at the start and end of the word.
  if n > length (lex1) then return 'nil;  % not enough real chars  

  if not atom (mycar pat) then <<
    lex2 := match!-string (mycar pat, lex1);
    n := n - length mycar pat;
    pat := mycdr pat;
    if not lex2 then return 'nil  % no match, bye!
    else if atom lex2 then << % matched full lex1, better not be any 
			      % pat left (unless *)
      if pat and (length pat > 1 or mycar pat neq '!*) then return 'nil
      else return 't;   % no pat left or last part is *
    >> else <<
	lex1 := lex2  % carry on with this
    >>
  >>;
  if not atom (lex3 :=mynth (pat, length (pat))) then <<
    lex2 := match!-string (lex3, mypnth (lex1, length lex1 - length lex3 + 1));
    n := n - length lex3;
    pat := head (pat, length (pat) - 1);
    if not lex2 then return 'nil  % no match, bye!
    % if lex2 is not 't we have an internal error
    else <<
	lex1 := head (lex1, length lex1 - length lex3); % carry on with this
    >>
  >>;
  if not pat and lex1 then return 'nil;
%write pat,!$eol!$;
  loop:
    if n > length (lex1) then return 'nil;  % not enough real chars
    pat := mycdr pat;  % eat off the !*
    if not pat then return 't;    % trailing * and a match so far == full match
%write "start", lex1, " " ,pat," ", n,!$eol!$;    
    while lex1 and n <= length lex1 and not (lex2 := 
		match!-string (mycar pat, lex1))
      do lex1 := mycdr lex1;	    % eat along looking for a match
%write lex2," ",pat," ",n," ",lex1,!$eol!$;
    if not lex1 or n > length lex1 then return 'nil;  % these are the same
    if not lex2 then return 'nil  % match failed
       % match exact
    else if atom lex2 and (not mycdr pat or mycadr pat eq '!*) then return 't
       % match exact so far but more pattern to look at than lex1
    else if atom lex2 and mycdr pat then return 'nil
       % match ok, but more lex1 than pattern
    else if not mycdr pat and lex2 then return 'nil;
    lex1 := lex2;
    n := n - length (mycar pat);
    pat := mycdr pat;
  goto loop;
end;

% As a "sloppy" lisp programmer, I expect car (nil) and cdr (nil) to return
% nil, not an error. Since Slisp does not assume this, we have to make our
% own routines to check for nil input.

symbolic procedure mycar (u);
  if u then car(u)
  else u;

symbolic procedure mycdr (u);
  if u then cdr (u)
  else u;

symbolic procedure mycaar (u);
  mycar (mycar (u));

symbolic procedure mycadr (u);
  mycar (mycdr (u));

symbolic procedure mycdar (u);
  mycdr (mycar (u));
  
symbolic procedure mycddr (u);
  mycdr (mycdr (u));

%%%%%%%%%%%%%%%%%%%%%%

symbolic procedure mycaaar (u);
  mycar (mycar (mycar (u)));

symbolic procedure mycaadr (u);
  mycar (mycar (mycdr (u)));

symbolic procedure mycaddr (u);
  mycar (mycdr (mycdr (u)));

symbolic procedure mycadar (u);
  mycar (mycdr (mycar (u)));

symbolic procedure mycdaar (u);
  mycdr (mycar (mycar (u)));

symbolic procedure mycdadr (u);
  mycdr (mycar (mycdr (u)));

symbolic procedure mycddar (u);
  mycdr (mycdr (mycar (u)));

symbolic procedure mycdddr (u);
  mycdr (mycdr (mycdr (u)));

%%%%%%%%%%%%%%%%%%%%%%%%%%

symbolic procedure mycaaaar (u);
  mycar (mycaaar (u));

symbolic procedure mycaaadr (u);
  mycar (mycaadr (u));

symbolic procedure mycaaddr (u);
  mycar (mycaddr (u));

symbolic procedure mycaadar (u);
  mycar (mycadar (u));

symbolic procedure mycadaar (u);
  mycar (mycdaar (u));

symbolic procedure mycadadr (u);
  mycar (mycdadr (u));

symbolic procedure mycaddar (u);
  mycar (mycddar (u));

symbolic procedure mycadddr (u);
  mycar (mycdddr (u));

symbolic procedure mycdaaar (u);
  mycdr (mycaaar (u));

symbolic procedure mycdaadr (u);
  mycdr (mycaadr (u));

symbolic procedure mycdaddr (u);
  mycdr (mycaddr (u));

symbolic procedure mycdadar (u);
  mycdr (mycadar (u));

symbolic procedure mycddaar (u);
  mycdr (mycdaar (u));

symbolic procedure mycddadr (u);
  mycdr (mycdadr (u));

symbolic procedure mycdddar (u);
  mycdr (mycddar (u));

symbolic procedure mycddddr (u);
  mycdr (mycdddr (u));


% These routines allow one to time larger blocks of commands, rather than
% one at a time as with the time switch.

global '(block!-time!* block!-gctime!*);
flag ('(stime etime), 'opfn);

symbolic procedure stime ();
  <<block!-gctime!* := gctime(); block!-time!* := time(), 't>>;

% this should be in local.red...
symbolic procedure etime (); % some code lifted from showtime() for 3.8
   begin scalar x,y;
      x := time() - block!-time!*;
      y := gctime() - block!-gctime!*;
      if 'psl memq lispsystem!* then x := x - y;
      terpri();
      prin2 "Elapsed Time: "; prin2 x; prin2 " ms";
      if null (y = 0) then return terpri();
      prin2 "  plus GC time: "; prin2 y; prin2 " ms";
   end;

endmodule;
;end;

