%***************************************************************************
%  FILE = save.red
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
% If used as a separate source file then these routines must also be
% defined: mycar mycdr mycaar mycadr mycdar mycddr mysetprop
% upcase dncase makestring mascii
module 'save;
%symbolic;

smacro procedure makenvname (u);
  makename (append (explode '!*save!-, explode  u));

global '(base!-case);
base!-case := 'nil;		% must be set for each system (in basecase.red)

smacro procedure upstring (u);
  mkstrng compress foreach x in explode u collect upcase x;

smacro procedure dnstring (u);
  mkstrng compress foreach x in explode u collect dncase x;

symbolic procedure base!-case!-string (u);
  if base!-case eq '!u!p!p!e!r then upstring u
  else if base!-case eq '!l!o!w!e!r then dnstring u
  else u;
 
global '(!*reduce!-environment 
	 last!-saved!-env!* 
	 current!-env!*
	 named!-env!-list!*
	 swap!-env!*);

fluid '(env!-grown!-flag!*);  % used to indicate if := has been used 
                              % so that the current environment is a superset
                              % of a named env.
env!-grown!-flag!* := 'nil;

swap!-env!* := '(!i!n!i!t!i!a!l . !i!n!i!t!i!a!l);
named!-env!-list!* := 'nil; % these are separate so each env does 
                          % not save all the others in itself

flag ('(!*reduce!-environment last!-saved!-env!* current!-env!*
        swap!-env!* named!-env!-list!*), 'keep);

!*reduce!-environment := '(
!*reduce!-environment
named!-env!-list!*
swap!-env!*
depl!*    % dependencies list
powlis!*  % where some let rules are stored
powlis1!* % and others.
asymplis!*
!*match
kord!*    % kernel ordering
df        % where lets of df's are stored (in property list)
	% reduce operators that may have lets on them
erf exp expt dilog asin asinh atan atanh cos cosh cot
log sin sinh sqrt tan tanh int
)$

% can add all switch with this command, done in sys.env
%apply('add!-to!-environment, list switchlist!*);

global '(indexed!-names title);
title := 'nil;
put ('savei, 'simpfn, 'savei!*);
put ('savec, 'simpfn, 'savec!*);

% savei* saves indexed objects into a file in a form that allows them
% to be re-read in to the system as indexed objects (as opposed to
% savec, see below). the filename is the first argument, usually it is
% a string.
symbolic procedure savei!* (u);
  saveic (mycar u, 'savei2, match!-names (mycdr u, indexed!-names));

% savec* saves indexed objects in component form, see savec2 for a more
% complete description. the filename is the first argument.

symbolic procedure savec!* (u);
  saveic (mycar u, 'savec2, match!-names (mycdr u, indexed!-names));

global '(loadlist);     % list of other files to load with this one
loadlist := 'nil;

% saveic calls the appropriate save routine for each object the user
% wishes to save. it also saves the environment of the system.

symbolic procedure saveic (filnme, fnc, lis);
begin scalar lex, lex1, filehandle;
  if not (filehandle := open (filnme, 'output)) then <<
    lpriw ("Warning:", list ("cannot open save file:", filnme));
    return ('nil)
  >>;
  write !$eol!$, "Use", base!-case!-string " in(";
  princ ('!");
  write filnme;
  princ ('!");
  write ")$ to reload.", !$eol!$,!$eol!$;
  wrs (filehandle);	% send output to save file.
  prin2(base!-case!-string "symbolic$ off time, echo $");
  if title then <<
    prin2 (base!-case!-string "prin1(");	% echo title when the file is loaded.
    prin1 (mkmsg list("%",title));
    prin2 (")$");
    prin2 (base!-case!-string "terpri()$");
    prin2(!$eol!$)
  >>;
  if getd ('date) then <<
    prin2 (base!-case!-string "prin1 (");		% echo save date when file is loaded.
    prin1 (mkmsg list("%", date ()));
    prin2 (")$");
    prin2 (base!-case!-string "terpri()$");
    prin2 (!$eol!$)>>;  % newline
  if (lex := loadlist) then <<
    while lex do <<
      prin2 (base!-case!-string "in (");
      prin1 (mkmsg list("%", mycar (lex)));
      prin2 (")$"); 
      wrs ('nil);
      write "IN'ing ", mycar (lex), !$eol!$;
      wrs (filehandle);
      lex := mycdr (lex)
    >>;
    prin2(!$eol!$)
  >>;
  for each x in !*reduce!-environment do savei2 (x, filehandle);
  for each x in named!-env!-list!* do savei2 (makenvname (x), filehandle);
  for each x in findkern (lis) do savei2 (x, filehandle);
  for each x in lis do apply (fnc, list (x, filehandle));
  prin2 (base!-case!-string "terpri()$algebraic$end$");
  prin2 (!$eol!$);
  close (filehandle);
  wrs ('nil);
  terpri ();
  return (filnme . 1);	% return file name
end;

% savei2() is the primitive routine which saves indexed objects in their internal
% form so that they may be re-loaded into the system. Reload with in()$
% This routine will save anything, not just indexed objects.

symbolic procedure savei2 (ex, filehandle);
begin;
  ex := resolvegeneric (ex);
  if not unboundp (ex) then <<	% if it has a value, dump this too.
%    prin2 (base!-case!-string "remflag ('(");
%    prin1 (ex);
%    prin2 (base!-case!-string "), 'reserved); setq (");
    prin2 (base!-case!-string "setq (");    % this is the last part of the prev line 
    prin1 (ex);
    prin2 (base!-case!-string ", uniqkern ('");
    prin1 (eval (ex));
    prin2 ("))$");
    prin2 (!$eol!$)
  >>;
  if prop (ex) then <<
    prin2 (base!-case!-string "mysetprop ('");
    prin1 (ex);
    prin2 (base!-case!-string ", uniqkern ('");
    prin1 (prop (ex));	% dump property list if it's there.
    prin2 ("))$");
    prin2 (!$eol!$)
  >>;
  if indexed (ex) then <<  % if it's indexed, make sure it gets back on indexed!-names.
    prin2 (base!-case!-string "and (not (memq ('");
    prin1 (ex);
    prin2 (base!-case!-string ", indexed!-names)), setq (indexed!-names, cons ('");
    prin1 (ex);
    prin2 (base!-case!-string ", indexed!-names)))$");
    prin2 (!$eol!$);
  >>;
  prin2 (base!-case!-string "prin1 ('");	% echo name when the file is loaded.
  prin1 (ex);
  prin2 (")$");
  prin2 (base!-case!-string "spaces (1)$");
  prin2 (!$eol!$);
  wrs ('nil);
  write (ex, " ");
  wrs (filehandle);
end;

% This routine saves indexed objects in component form, such objects cannot
% be reloaded as indexed objects. It creates names of the form
% <objname><index> for each element of the object and causes an assignment
% of the element to this name, e.g. q[0,1] will be saved as q01.

symbolic procedure savec2 (ex, filehandle);
begin scalar lex, lex1, lex2;
  ex := resolvegeneric (ex);
  if not indexed (ex) then return (savei2 (ex, filehandle));
  lex := get (ex, 'tvalue);
  lex1 := get (ex, 'multiplier);
  while lex do <<	% save all elements in the 'tvalue, no implicit values.
    prin2 (base!-case!-string "setk ('");
    prin2 (mkmsg list("%%", ex, compress (for each x in mycaar (lex)
				     collect mascii (x+48))));
    lex2 := mk!*sq (multsq (lex1, mycdar (lex)));
    prin2 (", '");
    prin1 (lex2);
    prin2 (")$");
    prin2 (!$eol!$);
    lex := mycdr (lex)
  >>;
  prin2 (base!-case!-string "prin1 ('");	% echo name when the file is loaded.
  prin1 (ex);
  prin2 (")$");
  prin2 (base!-case!-string "spaces (1)$");
  prin2 (!$eol!$);
  wrs ('nil);
  write (ex, " ");
  wrs (filehandle);
end;

symbolic procedure uniqkern (u);
begin scalar lex;
  if atom (u) then return (u)
  else if atom (lex := mycar (u)) then <<
    if get (lex, 'klist) or get (lex, 'kvalue) then <<    % operators MUST already exist!
      return (car (fkern (lex . uniqkern (mycdr (u)))))
    >>
    else return (uniqkern (mycar (u)) . uniqkern (mycdr (u)))
  >> 
  else return (uniqkern (mycar (u)) . uniqkern (mycdr (u)));
end;

fluid '(kernels sysops!*);
sysops!* := '(t nil df erf exp expt dilog asin asinh atan atanh cos cosh cot
              log sin sinh sqrt tan tanh int);

symbolic procedure findkern (u);
begin scalar kernels;
  for each x in u do findkern1 (x);
  return (kernels);
end;

symbolic procedure findkern1 (u);
<<
  findkern2 (get (u, 'tvalue));
  findkern2 (get (u, 'avalue));
  if flagp (u, 'share) then findkern2 (eval (u))
>>;

symbolic procedure findkern2 (u);
begin scalar lex;
  if atom (u) then return ()
  else if idp (lex := mycar (u)) then <<
    if (get (lex, 'klist) or not get (lex, 'simpfn)) and  % operator or var.
        not memq (lex, kernels) and not memq (lex, sysops!*) then
        kernels := lex . kernels;
    findkern2 (mycdr (u))
  >> else << findkern2 (mycar (u)); findkern2 (mycdr (u)) >>;
end;

unfluid '(kernels sysops!*);

put ('savenv, 'simpfn, 'save!-environment);

symbolic procedure save!-environment (u);
begin scalar lex;
     if not u then <<foreach x in named!-env!-list!* do write x,!$eol!$;
	 return 't . 1>>;
     lex := makenvname (car u);
     set (lex,
	 foreach x in !*reduce!-environment collect 
%if flagged keep should not save a value!
        if flagp (x, 'keep) then x . 'keep
	else if unboundp (x) then x . ('nil . uniqkern prop (x)) 
        else x . (uniqkern eval(x) . uniqkern prop (x)));
     if not memq (car u, named!-env!-list!*) then named!-env!-list!* := 
            car u . named!-env!-list!*;
     current!-env!* := last!-saved!-env!* := car u;  
     env!-grown!-flag!* := 'nil;
     return car u . 1
end;

put ('restorenv, 'simpfn, 'restore!-environment);

symbolic procedure restore!-environment (u);
begin scalar lex, lex1;
  if not u then u := list (last!-saved!-env!*);
  lex := makenvname (car u);
  if unboundp (lex) or not eval lex 
      then <<write "No such environment saved.",!$eol!$;
	 return 'nil . 1>>;
  % if restoring current env, the save will overwrite before it is restored!
  if car u neq '!c!u!r!r!e!n!t then save!-environment ('(!c!u!r!r!e!n!t));
  foreach x in !*reduce!-environment do << 
            if not flagp (x, 'keep) then <<
                 lex1 := assoc (x, eval lex);
		 set (x, uniqkern mycadr lex1);
		 mysetprop (x, uniqkern mycddr lex1)>> >>;
  env!-grown!-flag!* := 'nil; % there are no extra assigns in the current env
  current!-env!* := car u;
  return car u . 1;
end;

put ('addtoenv, 'simpfn, 'add!-to!-environment);
 
symbolic procedure add!-to!-environment (u);
<<
  if not u then foreach x in !*reduce!-environment do write x," "
  else <<	 
    env!-grown!-flag!* := 't;
    foreach x in u do if not memq (x, !*reduce!-environment) then 
	!*reduce!-environment := x . !*reduce!-environment
  >>;
  't . 1
>>;

put ('newenv, 'simpfn, 'new!-environment);

symbolic procedure new!-environment (u);
<<
  if u then save!-environment u else save!-environment ('(!c!u!r!r!e!n!t));
  restore!-environment ('(!i!n!i!t!i!a!l))
>>;

put ('keep, 'simpfn, 'keep!*);

symbolic procedure keep!* (u);
<<
  flag (u, 'keep);
  't . 1
>>;

symbolic procedure copystruct (u);
% copies the list tree so it is a copy that will not be altered when
% destructive things are done to the original.
if atom u then u
else copystruct car u . copystruct cdr u;

%redefine the operator command

remprop ('operator, 'stat);
symbolic procedure operator u; for each j in u do 
	<<add!-to!-environment (list j); mkop j>>;

rlistat '(operator);


%redefine setk1() to catch new algebraic definitions 
symbolic putd ('oldsetk1, car getd ('setk1), cdr getd ('setk1));
remflag ('(setk1), 'lose);

symbolic procedure setk1 (u,v,b);
<<
   if indexed (u) then merror (mkmsg list ("% cannot be assigned.", u), 't);
   if atom u then add!-to!-environment (list u)
   else if atom car u then add!-to!-environment (list car u);
   oldsetk1 (u, v, b)
>>;

put ('swapenv, 'simpfn, 'swap!-environment);

symbolic procedure swap!-environment (u);
<<
   if not u then u := list (mycdr swap!-env!*);
   restore!-environment (list mycar u);
   swap!-env!* := mycar u . (mycadr u or mycar swap!-env!*);
   mycar u . 1
>>;

put ('delenv, 'simpfn, 'delete!-environment);

symbolic procedure delete!-environment (u);
begin scalar lex;
  if car u eq '!i!n!i!t!i!a!l then <<
    write "Can't delete initial environment",!$eol!$; return 'nil . 1>>;
  lex := makenvname (car u);
  if unboundp (lex) or not eval lex 
      then <<write "No such environment saved.",!$eol!$;
	 return 'nil . 1>>;
  delete (lex, named!-env!-list!*);
  set (lex, 'nil);
  return mycar u . 1;
end;

put ('renamenv, 'simpfn, 'rename!-environment);

symbolic procedure rename!-environment (u);
begin scalar lex, lex1;
  lex := makenvname (car u);
  if unboundp (lex) or not eval lex 
      then <<write "No such environment saved.",!$eol!$;
	 return 'nil . 1>>;
  lex1 := makenvname (cadr u);
  if not mycadr u then <<write "Need two arguments",!$eol!$; return 'nil . 1>>;
  if not unboundp (lex1) then <<
      write "Can't overwrite existing environment",!$eol!$;
          return 'nil . 1>>;
  set (lex1, eval lex);
  set (lex, 'nil);
  !*reduce!-environment := 
      foreach x in !*reduce!-environment collect 
              if x eq mycar u then mycadr u else x;    % replace changed name
  if last!-saved!-env!* eq mycar u then last!-saved!-env!* := mycadr u;    % replace changed name
  if current!-env!* eq mycar u then current!-env!* := mycadr u;    % replace changed name
  named!-env!-list!* := 
      foreach x in named!-env!-list!* collect 
              if x eq mycar u then mycadr u else x;    % replace changed name
  swap!-env!* := 
      if car swap!-env!* eq mycar u then mycadr u else car swap!-env!* .
      if cdr swap!-env!* eq mycar u then mycadr u else cdr swap!-env!*;
  return mycadr u . 1;
end;	 
	 
endmodule;
;end;
