%***************************************************************************
% FILE = local.red
% For Reduce 3.8 .
%
% Procedures in this file:
% 
%  initrlisp inprint diffp xread1 prin2!* terpri* begin1
%
% Some routines Copyright (c) 1987 The Rand Corporation. All rights reserved.
%
%***************************************************************************
symbolic;
%in "$redten/decl.red"$

remflag ('(xread1 prin2!* inprint initrlisp terpri!* begin1), 'lose);
reduce!-version := 38;     % version number for coded tests
fluid '(!*promptenv);
!*promptenv := 'nil;

% add switch decl for 3.3 (and up) (not done in 3.2)
switch rewrite, extendedsum, showindices, xeval, 
        evalindex, hide, promptenv, reversedir, paging, mkobjsafe,
        peek, fancydf, symzexp, allerr, longshift, newriccistyle;


put ('times, 'prtch, " "); % a*s displays as "a s", but in off nat mode too!
put ('orig!*, 'initl, 1);  %??


% in 3.4 initrlisp() is used to define initreduce()

%putd ('oldinitrlisp, car getd ('initrlisp), cdr getd ('initrlisp));
%
%symbolic procedure initrlisp;
%<<
%   oldinitrlisp();
%   begin!-redten()
%>>;

% copied from mathpr/mprint.red
flag ('(inprint), 'lose);

symbolic procedure inprint(op,p,l);
   begin scalar x,y,z;
        if op='times and !*nat and null !*asterisk then
        <<op:='times2; put('times2,'infix,get('times,'infix));
          put('times2,'prtch," ")>>;
	if op eq 'plus and !*revpri then l := reverse l;
	    % print sum arguments in reverse order.
	if not get(op,'alt) then <<
	if op eq 'not then oprin op else
	  if op eq 'setq and not atom (x := car reverse l)
	     and idp car x and (y := getrtype x)
	     and (y := get(get(y,'tag),'setprifn))
	    then return apply2(y,car l,x);
% hook to print indexed objects in redten. jfh
if op eq 'rdr or op eq 'mrdr then <<
  printrdr ('rdr . l);
  return ('nil)
>>;
	  if null atom car l and idp caar l
	      and !*nat and
	      ((x := get(caar l,'prifn)) or (x := get(caar l,'pprifn)))
              and (get(x,op) eq 'inbrackets)
            % to avoid mix up of indices and exponents.
	    then<<prin2!* "("; maprint(car l,p); prin2!* ")">>
           else if !*nosplit and not testing!-width!* then
                prinfit(car l, p, nil)
           else maprint(car l, p);
          l := cdr l >>;
        if !*nosplit and not testing!-width!* then
% The code here goes to a certain amount of trouble to try to arrange
% that terms are never split across lines. This will slow
% printing down a bit, but I hope the improvement in formatting will
% be worth that.
              for each v in l do
	       if atom v or not(op eq get(car v,'alt))
                then <<
% It seems to me that it looks nicer to put +, - etc on the second
% line, but := and comma usually look better on the first one when I
% need to split things.
		   if op memq '(setq !*comma!*) then <<
                      oprin op;
                      prinfit(negnumberchk v, p, nil) >>
                    else prinfit(negnumberchk v, p, op) >>
                else prinfit(v, p, nil)
         else for each v in l do <<
	       if atom v or not(op eq get(car v,'alt))
                then <<oprin op; maprint(negnumberchk v,p)>>
              % difficult problem of negative numbers needing to be in
              % prefix form for pattern matching.
               else maprint(v,p) >>
   end;

% from odesolve/odepatch.red
symbolic procedure diffp(u,v);
   % U is a standard power, V a kernel.
   % Value is the standard quotient derivative of U wrt V.
   begin scalar n,w,x,y,z; integer m;
	n := cdr u;     % integer power.
	u := car u;     % main variable.
	if u eq v and (w := 1 ./ 1) then go to e
	 else if atom u then go to f
	 %else if (x := assoc(u,dsubl!*)) and (x := atsoc(v,cdr x))
%               and (w := cdr x) then go to e   % deriv known.
	     % DSUBL!* not used for now.
	 else if (not atom car u and (w:= difff(u,v)))
		  or (car u eq '!*sq and (w:= diffsq(cadr u,v)))
	  then go to c  % extended kernel found.
	 else if x := get(car u,'dfform) then return apply3(x,u,v,n)
	 else if x:= get(car u,dfn_prop u) then nil
	 else if car u eq 'plus and (w := diffsq(simp u,v))
	  then go to c
% note that both checks are needed else the system will set derivs wrt to
% other vars to 0 (JFH)
         else if checktype (u, 'rdr) or (checktype (u, 'df) and 
                                 checktype (mycadr (u), 'rdr))
         or checktype (v, 'rdr) or (checktype (v, 'df) and 
                                 checktype (mycadr (v), 'rdr))  % this needed?
                     then <<  % hook for indexed objects
	    if not (w := dfrdr (u, v)) then return ('nil ./ 1)
            else go to j
         >>
% end redten addin
	 else go to h;  % unknown derivative.
	y := x;
	z := cdr u;
    a:  w := diffsq(simp car z,v) . w;
	if caar w and null car y then go to h;  % unknown deriv.
	y := cdr y;
	z := cdr z;
	if z and y then go to a
	 else if z or y then go to h;  % arguments do not match.
	y := reverse w;
	z := cdr u;
	w := nil ./ 1;
    b:  % computation of kernel derivative.
	if caar y
	  then w := addsq(multsq(car y,simp subla(pair(caar x,z),
						   cdar x)),
			  w);
	x := cdr x;
	y := cdr y;
	if y then go to b;
    c:  % save calculated deriv in case it is used again.
	% if x := atsoc(u,dsubl!*) then go to d
	%  else x := u . nil;
	% dsubl!* := x . dsubl!*;
  % d:   rplacd(x,xadd(v . w,cdr x,t));
    e:  % allowance for power.
	% first check to see if kernel has weight.
	if (x := atsoc(u,wtl!*))
	  then w := multpq('k!* .** (-cdr x),w);
	m := n-1;
	% Evaluation is far more efficient if results are rationalized.
	return rationalizesq if n=1 then w
		else if flagp(dmode!*,'convert)
		     and null(n := int!-equiv!-chk
					   apply1(get(dmode!*,'i2d),n))
		 then nil ./ 1
		else multsq(!*t2q((u .** m) .* n),w);
    f:  % Check for possible unused substitution rule.
	if not depends(u,v)
	   and (not (x:= atsoc(u,powlis!*))
		 or not depends(cadddr x,v))
	   and null !*depend
	  then return nil ./ 1;
        % Derivative of a dependent identifier via the chain rule.
        % Suppose u(v) = u(a(v),b(v),...), i.e. given depend {u}, a,
        % b, {a, b}, v; then (essentially) depl!* = ((b v) (a v) (u b
        % a))
        if !*expanddf and not(v memq (x:=cdr atsoc(u, depl!*))) then <<
           w := nil ./ 1;
           for each a in x do
              w := addsq(w, multsq(simp{'df,u,a},simp{'df,a,v}));
           go to e
        >>;
	w := list('df,u,v);
	w := if x := opmtch w then simp x else mksq(w,1);
	go to e;
    h:  % Final check for possible kernel deriv.
	if car u eq 'df then <<         % multiple derivative
           if cadr u eq v then
              % (df (df v x y z ...) v) ==> 0 if commutedf
              if !*commutedf and null !*depend then return nil ./ 1
              else if !*simpnoncomdf and (w:=atsoc(v, depl!*))
                 and null cddr w % and (cadr w eq (x:=caddr u))
              then
                 % (df (df v x) v) ==> (df v x 2)/(df v x) etc.
                 % if single independent variable
                 <<
                    x := caddr u;
                    % w := simp {'quotient, {'df,u,x}, {'df,v,x}};
                    w := quotsq(simp{'df,u,x},simp{'df,v,x});
                    go to e
                 >>
           else if eqcar(cadr u, 'int) then
              % (df (df (int F x) A) v) ==> (df (df (int F x) v) A) ?
              % Commute the derivatives to differentiate the integral?
              if caddr cadr u eq v then
                 % Evaluating (df u v) where u = (df (int F v) A)
                 % Just return (df F A) - derivative absorbed
                 << w := 'df . cadr cadr u . cddr u;  go to j >>
              else if !*allowdfint and
                 % Evaluating (df u v) where u = (df (int F x) A)
                 % (If dfint is also on then this will not arise!)
                 % Commute only if the result simplifies:
                 not_df_p(w := diffsq(simp!* cadr cadr u, v))
              then <<
                 % Generally must re-evaluate the integral (carefully!)
                 w := 'df . reval{'int, mk!*sq w, caddr cadr u} . cddr u;
                 go to j >>;  % derivative absorbed
	   if (x := find_sub_df(w:= cadr u . merge!-ind!-vars(u,v),
					   get('df,'kvalue)))
			  then <<w := simp car x;
				 for each el in cdr x do
				    for i := 1:cdr el do
					w := diffsq(w,car el);
				 go to e>>
		       else w := 'df . w
        >> else if !*expanddf and not atom cadr u then <<
           % Derivative of an algebraic operator u(a(v),...) via the
           % chain rule: df(u(v),v) = u_1(a(v),b(v),...)*df(a,v) + ...
           x := intern compress nconc(explode car u, '(!! !! !_));
           y := cdr u;  w := nil ./ 1;  m := 0;
           for each a in y do
           begin scalar b;
              m:=m#+1;
              if numr(b:=simp{'df,a,v}) then <<
                 z := mkid(x, m);
                 put(z, 'simpfn, 'simpiden);
                 w := addsq(w, multsq(simp(z . y), b))
              >>
           end;
           go to e
        >> else w := {'df,u,v};
   j:   if (x := opmtch w) then w := simp x
	 else if not depends(u,v) and null !*depend then return nil ./ 1
	 else w := mksq(w,1);
      go to e
   end$


%from rlisp/xread.red
% I dunno why this is here - do we change anything??

%symbolic procedure xread1 u;
%   begin scalar v,w,x,y,z,z1,z2,commentlist;
%        % This is the basic function for parsing RLISP input, once
%        % tokens have been read by TOKEN and SCAN.  Its one argument
%        % U can take a number of values:
%        %   FOR:     Parsing of FOR statements
%        %   GROUP:   Parsing of group statements after keyword <<
%        %   LAMBDA:  Parsing of lambda expressions after keyword lambda
%        %   NIL:     Parsing of expressions which can have a comma at
%        %            the end for example.
%        %   PROC:    Parsing of procedures after keyword PROCEDURE
%        %   T:       Default case with standard parsing.
%        % Also, if U is flagged STRUCT, it is assumed that the arguments
%        % are lists of lists, and so commas are removed.  At present,
%        % only MAT is tagged in this manner.
%        % The local variables are used as follows:
%        % v: expression being built
%        % w: prefix operator stack
%        % x: infix operator stack
%        % y: infix value or stat property
%        % z: current symbol
%        % z1: next symbol
%        % z2: temporary storage;
%	% commentlist: association list of read comments.
%	if commentlist!*
%	  then progn(commentlist := commentlist!*,
%		     commentlist!* := nil);
%  a:    z := cursym!*;
%  a1:   if null idp z then nil
%         else if z eq '!*lpar!* then go to lparen
%         else if z eq '!*rpar!* then go to rparen
%         else if y := get(z,'infix) then go to infx
%         % The next line now commented out was intended to allow a STAT
%         % to be used as a label. However, it prevents the definition of
%         % a diphthong whose first character is a colon.
%%        else if nxtsym!* eq '!: then nil
%         else if flagp(z,'delim) then go to delimit
%         else if y := get(z,'stat) then go to stat
%         else if null !*reduce4 and flagp(z,'type)
%          then progn(w := lispapply('decstat,nil) . w, go to a);
%  a2:   y := nil;
%  a3:   w := z . w;
%        % allow for implicit * after a number.
%        if toknump z
%           and null(z1 eq !$eol!$)
%           and idp (z1 := chknewnam nxtsym!*)
%           and null flagp(z1,'delim)
%           and null(get(z1,'switch!*) and null(z1 eq '!())
%           and null get(z1,'infix)
%           and null (!*eoldelimp and z1 eq !$eol!$)
%          then progn(cursym!* := 'times, go to a)
%         else if u eq 'proc and length w > 2
%          then symerr("Syntax error in procedure header",nil);
%  next: z := scan();
%        go to a1;
%  lparen:
%        eolcheck();
%        y := nil;
%        if scan() eq '!*rpar!* then go to lp1    % no args
%         else if flagpcar(w,'struct) then z := xread1 car w
%         else z := xread1 'paren;
%        if flagp(u,'struct) then progn(z := remcomma z, go to a3)
%         else if null eqcar(z,'!*comma!*) then go to a3
%         else if null w         % then go to a3
%           then (if u eq 'lambda then go to a3
%                 else symerr("Improper delimiter",nil))
%         else w := (car w . cdr z) . cdr w;
%        go to next;
%  lp1:  if w then w := list car w . cdr w;  % Function of no args.
%        go to next;
%  rparen:
%        if null u or u eq 'group
%           or u eq 'proc % and null !*reduce4
%          then symerr("Too many right parentheses",nil)
%         else go to end1;
%  infx: eolcheck();
%        if z eq '!*comma!* or null atom (z1 := scan())
%                or toknump z1 then go to in1
%         else if z1 eq '!*rpar!* % Infix operator used as variable.
%                or z1 eq '!*comma!*
%                or flagp(z1,'delim)
%          then go to in2
%         else if z1 eq '!*lpar!* % Infix operator in prefix position.
%                    and null eolcheck()     % Side effect important
%                    and null atom(z1 := xread 'paren)
%                    and car z1 eq '!*comma!*
%                    and (z := z . cdr z1)
%          then go to a1;
%  in1:  if w then go to unwind
%         else if null(z := get(z,'unary))
%          then symerr("Redundant operator",nil);
%        v := '!*!*un!*!* . v;
%        go to pr1;
%% in2:  if y then if !*ignoreeol then y := nil
%%                  else symerr("Redundant operator",nil);
%  in2:  if y then y := nil;
%        w := z . w;
%  in3:  z := z1;
%        go to a1;
%  unwind:
%        % Null w implies a delimiter was found, say, after a comma.
%        if null w then symerr("Improper delimiter",nil);
%        z2 := mkvar(car w,z);
%  un1:  w:= cdr w;
%        if null w then go to un2
%        % Next line used to be toknump car w, but this test catches more
%%        else if null idp car w and null eqcar(car w,'lambda)
%         else if atom car w and null idp car w
%%           and null eqcar(car w,'lambda)
%          then symerr("Missing operator",nil);
%        z2 := list(car w,z2);
%        go to un1;
%  un2:  v:= z2 . v;
%  preced:
%        if null x then if y=0 then go to end2 else nil
%%        else if z eq 'setq then nil
%        % Makes parsing a + b := c more natural.
%         else if y<caar x
%           or (y=caar x
%               and ((z eq cdar x and null flagp(z,'nary)
%                                 and null flagp(z,'right))
%                             or get(cdar x,'alt)))
%          then go to pr2;
%  pr1:  x:= (y . z) . x;
%        if null(z eq '!*comma!*) then go to in3
%         else if cdr x or null u or u memq '(lambda paren)
%            or flagp(u,'struct)
%          then go to next
%         else go to end2;
%  pr2:  %if cdar x eq 'setq then go to assign else;
%        % Check for NOT used as infix operator.
%        if eqcar(cadr v,'not) and caar x >= get('member,'infix)
%          then typerr("NOT","infix operator");
%        if cadr v eq '!*!*un!*!*
%          then (if car v eq '!*!*un!*!* then go to pr1
%                else z2 := list(cdar x,car v))
%         else z2 := cdar x .
%                     if eqcar(car v,cdar x) and flagp(cdar x,'nary)
%                       then (cadr v . cdar v)
%                      else list(cadr v,car v);
%        x:= cdr x;
%        v := z2 . cddr v;
%        go to preced;
%  stat: if null(y eq 'endstat) then eolcheck();
%        if null(flagp(z,'go)
%%          or (flagp(y,'endstatfn)
%           or null(u eq 'proc) and (flagp(y,'endstatfn)
%                or (null delcp nxtsym!* and null (nxtsym!* eq '!,))))
%          then go to a2;
%        if z eq 'procedure and !*reduce4
%          then if w then if cdr w or !*reduce4
%                           then symerr("proc form",nil)
%                          else w := list procstat1 car w
%                else w := list procstat1 nil
%         else w := lispapply(y,nil) . w;
%        y := nil;
%        go to a;
%  delimit:
%        if null(cursym!* eq '!*semicol!*) then eolcheck();
%        if z eq '!*colon!* and null(u eq 'for)
%              and (null !*blockp or null w or null atom car w or cdr w)
%           or flagp(z,'nodel)
%              and (null u
%                      or u eq 'group
%                        and null(z memq
%                                   '(!*rsqbkt!* !*rcbkt!* !*rsqb!*)))
%          then symerr("Improper delimiter",nil)
%         else if idp u and (u eq 'paren or flagp(u,'struct))
%          then symerr("Too few right parentheses",nil);
%  end1:
%        if y then symerr("Improper delimiter",nil) % Probably ,).
%         else if null v and null w and null x
%	  then return xcomment(nil,commentlist);
%        y := 0;
%        go to unwind;
%  end2: if null cdr v then return xcomment(car v,commentlist)
%         else print "Please send hearn@rand.org your program!!";
%        symerr("Improper delimiter",nil)
%   end;
%

flag ('(prin2!*),'lose);  %now that most objects use _ instead of #, no need to redef
%+%symbolic procedure prin2!* u;
%+%   begin integer m,n;
%+%        if overflowed!* then return 'overflowed
%+%        else if !*fort then return fprin2 u
%+%        else if !*nat then <<
%+%          if u = 'pi then u := symbol '!.pi
%+%           else if u = 'infinity then u := symbol 'infinity >>;
%+%        n := lengthc u;
%+%        if n<=(linelength nil-spare!*) then <<
%+%           m := posn!*+n;
%+%        % I somewhat dislike having the side-effect of a call to
%+%        % terpri!* in the condition tested here, but that is maybe what
%+%        % the problem calls for.
%+%           if m<=(linelength nil-spare!*) or
%+%              (not testing!-width!* and
%+%                 << terpri!* t;
%+%                    (m := posn!*+n)<=(linelength nil-spare!*) >>)
%+%             then <<if not !*nat then  %fjw%  prin2 u
%+%                     prin2 u  % output should not be readable jfh
%+%%                    % output should be REDUCE-readable  %% begin{fjw}
%+%%                       if stringp u or get(u,'switch!*) or digit u
%+%%                          or get(car explode2 u,'switch!*) then prin2 u
%+%%                        else prin1 u                        %% end{fjw}
%+%                     else pline!* := (((posn!* . m) . ycoord!*) . u)
%+%                                        .  pline!*;
%+%                    return (posn!* := m)>>>>;
%+%        %identifier longer than one line;
%+%        if testing!-width!* then <<
%+%            overflowed!* := t;
%+%            return 'overflowed >>
%+%        else if !*fort
%+%         then rerror(mathpr,1,list(u,"too long for FORTRAN"));
%+%        % Let LISP print the atom.
%+%        terpri!* nil;
%+%        prin2t u;
%+%%       if !*clisp then m := posn() else
%+%        % I think this is what is really wanted.
%+%        m := remainder(n,(linelength nil-spare!*));
%+%        return (posn!* := m)
%+%   end;
%+%
%+%global '(ofl!*);

% from mathpr/mprint.red
symbolic procedure terpri!* u;
% This redefinition of terpri*() implements a rudimentary pager for Reduce
% output. When more than screenlines!* lines have been output, a pause is made.
% If the user enters a 'q' or 'n', an error throw to top level is made; if the user
% enters a 'c', output continues without interruption. A 'd' makes the next
% page only half a screen high. Any other char continues 
% the output. Paging is controlled by the switch !*paging. Input from 
% non-terminal devices prohibits paging of the output.
   begin integer n;
	if outputhandler!* then return apply2(outputhandler!*,'terpri,u)
	 else if testing!-width!* then return overflowed!* := t
         else if !*fort then return fterpri(u)
	 else if !*nat and pline!*
	  then <<
           pline!* := reverse pline!*;
           for n := ymax!* step -1 until ymin!* do <<
             scprint(pline!*,n);
             terpri();
% added jfh for redten pager.
  terpricount!* := terpricount!* + 1;
  if (!*paging and terminalp() and not ofl!* 
      and terpricount!* > screenlines!*) then 
    begin scalar a;
      terpricount!* := 0;
      setpchar "";
      prin2 "Continue? ";
      while ((a := readch()) eq !$eol!$) do << >>;
      if (a eq '!q or a eq '!Q or a eq '!n or a eq '!N) then <<mclear();error1 ()>> % could leave things all messed up
      else if (a eq '!d or a eq '!D) then terpricount!* := screenlines!* / 2
      else if (a eq '!c or a eq '!C) then terpricount!* := -1000000;
      foreach x in upcursor!* do prin2 x; % backup and overwrite the "Continue?" message.
      prin2 "            ";  
      terpri();        % then reset, 
      foreach x in upcursor!* do prin2 x; % and backup so the output goes were it should.
    end
 >>;
           pline!* := nil >>;
	if u then terpri();
        posn!* := orig!*;
        ycoord!* := ymax!* := ymin!* := 0
   end;


global '(bell!*!*);
bell!*!* := '!;  % bell code
fluid '(beep otime!*!*);
beep := 60;

%from rlisp/superv.red

symbolic procedure update!_prompt;
   begin
      statcounter := statcounter + 1;
      promptexp!* :=
	 compress('!! . append(explode statcounter,
		     explode if null symchar!* or !*mode eq 'algebraic
			       then '!:!  else '!*! ));
% added jfh for redten feature support (environments and pager)
    if !*promptenv then 
      promptexp!* := mkmsg list("(%)% %", 
        current!-env!*,
	if env!-grown!-flag!* then "+" else "", promptexp!*);
	terpricount!* := 0;   % pager line counter reset at each prompt.
% end redten

      setpchar promptexp!*
   end;

%;end;
