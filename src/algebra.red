%***************************************************************************
%  FILE = algebra.red
% 
%  REDTEN source code
%  Copyright (c) 1986-1994,2006,2009 University of Toronto.
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
module 'ialg;
%symbolic;
%in "$redten/decl.red"$

fluid '(aindextype notcon!*);

!*extendedsum := 'nil;
notcon!* := 'nil;    % if contract() is called from places not below evaltnsr1

symbolic procedure evaltnsr (tnsr, indexx, value);
% EVALTNSR() is called from EQUALPARSE() and SIMPSEVAL!*() to set up the
% evaluation of an indexed expression and its assignment to an indexed object.
% INDEX will never be a fixed index, that case is handled by calling
% evaltnsr1() directly from equalparse().
begin;
  setk ('backvalue, aeval (value := reval (value)));	% copy value to backup
  if !*rewrite then				% pretty-print input value
    <<
        terpri ();
        if not indexx then prin2!* (tnsr)		% lhs a scalar
        else printrdr (list ('rdr, tnsr, indexx));		% lhs an indexed object
        prin2!* (" = ");
        maprint (value, 0);				% rhs
        terpri!* ('t)
    >>;
  value := evaltnsr1 (tnsr, indexx, value, 'nil);	% evaluate input
  cleartmp ();					% clean trash
  if indexx then return (simp (list ('rdr, tnsr, indexx))) % indexed obj output
%  ELSE IF INDEXED (TNSR) THEN                             % indexed scalar
%          RETURN (SIMP (MK!*SQ (WRITETNSR (TNSR, 'NIL, VALUE, 'NIL))))
%  else return (simp (value));	% scalar output
  else return (simp aeval (value));	% scalar output
end;

!*showindices := 'nil;	% user flag to print indices (default don't print)
teneval!* := 'nil;

symbolic procedure evaltnsr1 (tnsr, indexx, value, noshowindices);
% evaltnsr1() is the primitive routine that processes the input value and
% evaluates it; assigning it to either a scalar or an indexed object as
% required. Inputs are the output object name, its index ('nil for a 
% scalar), and a flag to indicate that the progress of the calculation
% is to be shown by printing indices as each element is computed.
% This flag is not used as of version 3.0
% flag meaning reverse in v4.1
begin scalar notcon!*, indexout, indextype, aindextype, lex, lex1, lex2,
           pindex, linelength, teneval!*, asym!-flg, verbose!*, showindices;
  teneval!* := 't;    % indicates that we are in evaltnsr1().
  if not free1 (indexx, shift!-iops!*) then 
	merror (mkmsg list ("this shifted object does not exist: %",
	rdr!-string list ('rdr, tnsr, indexx)), 't);
  showindices := if noshowindices then 'nil else !*showindices;		% print indices ?
  if indexed (tnsr) and isprotect (tnsr, 2) then 
    <<
       merror (mkmsg list ("% is write-protected.", tnsr), 'nil);
       if get (tnsr, 'odfmsg) then merror (get (tnsr, 'odfmsg), 'nil);
       return (tnsr)			% can't write to protected object
    >>;
  lex1 := contract (indexx, 'nil);  % look for apparent contractions in output
  lex := append (mycar (lex1), mycadr (lex1)); % these indicate diagonal writes
  notcon!* := mycadr (lex1);   % indices NOT involved in contractions if repeated
  setlis (alphalist!*, alphalist!*);	% clear the alphalist* and ..
	% .. set up the connections between its elements and the input index.
  pindex := pair (lex, lex1 := head (alphalist!*, length (lex)));
    		% call the preprocessor and the processor to format the value.
  value := processvalue (preprocess (value, indexx), pindex, 'nil);
  if not indexx then 
   <<
      if showindices then <<spaces (tabbing!*);princ ("*"); terpri()>>;	% show user we've begun.
      value := pre!-eval (value, 'nil);
      if indexed (tnsr) then
        if not zerop car get (tnsr, 'indices) then
		merror (mkmsg list ("cannot scalar assign to %", tnsr), 't)
        else return (writetnsr (tnsr, 'nil, simp aeval (value), 't)) % scalar object
      else return (setk (tnsr,  (aeval value)));	% scalar output
   >>;
  indextype := for each x in indexx
          collect (mycdr (assoc (x, aindextype)) or -1);
  if not aindextype then		% must make object accordingly
     indextype := get (tnsr, 'indextype) or indextype;
  if not indexed (tnsr) then
     tnsr := mktnsr!* (tnsr, indextype, get (tnsr, 'symmetry), 
		       'nil, 'nil, 'nil)
            % expression structure does not match objects'
% this should be changed to do the test and error message inside
% the foreach.
  else if memq ('nil, foreach x in 
	pair (pair (get (tnsr, 'indextype), indextype), indexx) 
	collect fixp (cdr x) or caar x eq cdar x) then
                   % check only non-fixed index elements, to avoid errors
                   % on things like q[0,a] == z[a];
    merror ("indices do not match.", 'nil);  
            % save current value
  saveobj (tnsr);   % save in case of a massive screw up.
  if value = 0 and showindices then 	% we are writing zeroes, let user ..
      <<prin2 ("=0"); terpri()>>;	% know the expression went to 0
%  if not mycar (get (tnsr, 'multiplier)) = 1 then  % divide by multiplier
%    value := list ('quotient, value, mk!*sq (get (tnsr, 'multiplier)));

     % output indices for the object, derived from its symmetries.
  indexout := igen!-full (lex, get (tnsr, 'restricted) or get (tnsr, 'indices),
		      get (tnsr, 'symmetry), get (tnsr, 'internal!-mapping));
  indexx := lex1;   % this was realy messed up before.
  foreach x in pair (car indexout, cadr indexout) do
   <<	
      setlis (lex1, car x);
      if showindices or !*peek then pbol (mapcar (indexx, 'eval));
      lex2:= cv!* (simp aeval pre!-eval (if minusp (mycadr x) then 
		list ('minus, value) else value, 'nil), mycaddr x);
      if !*peek then <<spaces(tabbing!*); prin1 (mapcar (indexx, 'eval));
         if not mycar lex2 then write " is zero.",!$eol!$ else
                            write " is not zero.",!$eol!$>>;
      fast!-writetnsr (tnsr, mapcar (indexx, 'eval), lex2, 't)
   >>;
  if showindices or !*peek then terpri();
  setlis (alphalist!*, alphalist!*);	% clear
  fast!-writetnsr!-cleanup();   % get everyone in order.
  return (tnsr);
end;

fluid '(nindex  nindextype);	% to store things in from below

symbolic procedure pre!-eval (value, flg);
% descend into an expression looking for rdr forms. Look at only those
% things that have atomic cars, others are sq forms and can be ignored.
% If a 0 occurs in a times form, replace the whole thing with 0.
% flg nil means fully replace indexed obj, t mean eval index, but leave
% rdr-form (this ensures each version of the exp. is different
% when seen by the algebraic simplifier, so there is no problem with the 
% cached values in alglist!*).
begin scalar lex, lis;
  if atom value then return value
  else if checktype (value, '(rdr)) then <<
    lex := mapcar (mycaddr (value), 'eval);
    if not fixedindex (lex) then 
     merror (mkmsg list ("bad index: %", 
			 rdr!-string list ('rdr, mycadr (value), lex)), 't);
    if not flg then <<
    lex := readtnsr (mycadr (value), lex);
    return if checktype (lex, 'nil) then 0 else mk!*sq lex>>
    else return list ('rdr, mycadr value, lex)
  >>
  else if checktype (value, 'odf!*) then return foreach x in value
	 collect pre!-eval (x, 't)
  else if checktype (value, 'times) then return begin
    loop:
      if not value then return reverse lis;
      lex := pre!-eval (pop value, flg);
      if lex = 0 then return 0 else push (lex, lis);
    goto loop
  end
  else if checktype (value, '!*sq) then return value
  else if atom mycar value then 
    return foreach x in value collect pre!-eval (x, flg)
  else return value;
end;


symbolic procedure processvalue (value, indexx, indexc);
% PROCESSVALUE is the routine which translates an indexed expression into
% a form that can be evaluated easily.
begin scalar lex, lex1, lex2, nindex, nindextype, lex4, indexo;
  if atom (value) or checktype (value, '!*sq) or	% dont touch
     free1 (value, '(rdr mrdr)) then return (value)
  else if checktype (value, '(rdr mrdr)) then <<	% indexed object
    if (lex := get (mycadr (value), 'coords)) and not (coords!* = lex) then
      merror (mkmsg list ("unmatched coordinates: %, %.",
			  lex, value), 'nil); 	% warning error
					% look for internal contractions
    if checktype (value, 'mrdr) then 
 	   lex := contract (mycaddr (value),
	 mapcar (get (mycadr (value), 'indextype), 'minus))
    else lex := contract (mycaddr (value), get (mycadr (value), 'indextype));
    chkindextype (mycar (lex), mycaddr (lex), indexc, value);
    if not get (mycadr (value), 'tvalue) and not  % replace empty object by 0
       get (mycadr (value), 'implicit) and 	% (subject to constraints)
       not get (mycadr value, 'subobj) and
%       not mycdr (get (mycadr (value), 'conjugate)) and 
       not (indexed (mycadr (value)) eq 'scalar) then return (0);
    if mycadr (lex) then <<		% there is an internal contraction
      lex4 := mapindex (mycaddr (value), append (indexx, pair (mycadr (lex),
              (lex2 := head (mypnth (alphalist!*, length (indexx) 
                  + length (indexc) + 1), length (mycadr (lex)))))),
              value);
      return (conprod (list ('rdr, mycadr (value), lex4), lex2,
                list (mycadr (lex), mycadddr (lex))))
    >> else <<				% no internal contraction
       					% map index and check for free indicies
      lex4 := mapindex (mycaddr (value), indexx, value);
      return (list ('rdr, mycadr (value), lex4)) % replace 'rdr with 'evalc
    >>
  >>				% expression is either a product or a 'df form
  else if checktype (value, '(times df odf!*))
%      AND INDEXED (MYCADR (MYCADDR (VALUE))) THEN <<
       then <<
    collecterms (mycdr (value));    % net index structure in nindex & nindextype
    lex := contract (nindex, nindextype);		% contractions among objects
    chkindextype (mycar (lex), mycaddr (lex), indexc, value);
    lex4 := head (mypnth (alphalist!*, length (indexx) + length (indexc) + 1),
                   length (mycadr (lex)));
    lex1:= mycadr (lex);
    lex2:='nil;
%    while lex1 do <<
%      if not assoc (mycar (lex1), indexx) then <<
%        indexx := append (indexx, list (mycar (lex1) . mycar (lex4)));
%        indexc := append (indexc, list (mycar (lex1)));
%        lex2 := mycar (lex4) . lex2
%      >>;
%      lex4:= mycdr (lex4);
%      lex1:= mycdr (lex1)
%    >>;
    foreach x in lex1 do <<
      if not assoc (x, indexx) then <<
        indexx := append (indexx, list (x . mycar (lex4)));
        indexc := append (indexc, list (x));
        push (mycar (lex4), lex2)
      >>;
      popq (lex4)
    >>;
 				% recursively look into form
    value := for each x in value collect processvalue (x, indexx, indexc);
    if lex2 then
      return (conprod (value, reverse (lex2),
                list (mycadr (lex), mycadddr (lex))))
    else return (value)
  >>
  else return (for each x in value collect processvalue (x, indexx, indexc));
end;

symbolic procedure preprocess (value, indexx);
% PREPROCESS handles various unevaled functions and operators in an 
% expression. The required actions are taken and the results are placed
% into the expression. These operations include derivatives, shifts operators,
% and symmetrization operations. Also, TRACESYM is called to try to find
% places where trace symmetries can be used to speed the evaluation.
begin scalar lex, op, i1, i2, !*symzexp;  
  !*symzexp := 't;     % must expand any symz's remaining.
  if atom (value) or checktype (value, '!*sq) then return (value); % dont touch
  if checktype (value, 'symz) then   % unevaled multi-object symz
     return for each x in symz!*!* cdr value collect preprocess (x, indexx);
  if checktype (value, 'pdf) then
  <<    % partial derivative operator
    lex := mkcoords!*!* (tmpnames (), 'nil);
    value := append (list ('df, mycadr (value)),
                for each x in mycdaddr (value)
                     collect list ('mrdr, lex, list (x)))
  >>;
  if checktype (value, '(rdr mrdr)) then
   <<
    op := mycar value;  % save the 'mrdr
    value := resolvegeneric (mycadr (value)) . mycddr (value);
     % this bit gets fixat() to rewrite the index with regular shift ops
    value := list (mycar value, fixat (mycadr (value), 
	get (mycar value, 'indextype)));
   % Note: value lacks a leading 'rdr until after the call to shift!*
    %    REMPROP (TNSR, 'AVALUE);   % do we want this???
%Here: check if a shift and a cov op both: if so then do cov first, then
% shift. At this point
%      tnsr = mycar value
%      index = mycadr value

% make !*symzexp local and set to nil
    if not free1 (value, symz!-iops!*) then
       return (for each x in symz!*!* (op . value)
		collect preprocess (x, indexx));

    % split off the head and tail of the index. Put it back together below
    % with shift ops removed from the deriv part, them put them back
    % after the derivs are done.
    lex := deriv (mycadr value, 'nil) or length (mycadr value);
    i1 := head (mycadr value, lex);
    i2 := mypnth (mycadr value, lex + 1);
%write value, " ", i1, " ", i2, !$eol!$;
    % get rid of shifts in the derivative indices for now.
    value := list (mycar value, append (i1, indh(i2)));    
%write "new value = ", value, !$eol!$;
	
    % this next is done to avoid shifting an object whose cov is to be done
    % since that is done by shifting the cov of the parent, thus we avoid
    % a useless shift.
    if length (mycadr value) = (mycar (get (mycar value, 'indices)) + 2)
       and deriv (mycadr value, '!*dbr)   % has 1 cov derive
       and not free1 (mycadr value, '(!*at!*))   % and a shift
       then 
	       value :=  mycdr formrdr (cov!* ('rdr . value), 
		      delete ('!*dbr, indh (mycadr value)));
    value := shift!* ('rdr . value, 'nil);	% any last shifts ..
%write "value after shift = ", value, !$eol!$;
    if op eq 'mrdr then value := 'mrdr . cdr value;
    % if a shift remains to be done in the deriv indice, we must force 
    % the production of an indexed object. Otherwise value may not be an
    % indexed object (?)
    if deriv (mycaddr (value), 'nil) then		% derivatives
      % if there are shifts in the deriv index, then idiff must produce
      % a full object, not just an odf form.
      value :=  idiff (mycadr (value), mycaddr (value), not (indh(i2) = i2));
%write "value after deriv = ", value, !$eol!$;
    % final shifts of derivative indices
    if not free1 (i2, '(!*at!*)) then
      <<
	lex := '();
        foreach x in append (indh (i1), i2) do 
		if x neq '!*br and x neq '!*dbr then lex := x . lex;
%write "lex = ", lex, !$eol!$;	
	value := shift!* (list (mycar value, mycadr value,
			 reverse lex), 'nil); 
%write "value after shift2 = ", value, !$eol!$;
      >>;
    return value
  >>
  else if not free1 (value, '(rdr mrdr)) then % this check is a waste of time
  <<
    value := for each x in value collect preprocess (x, indexx);
    if checktype (value, '(times df odf!*)) then 
    <<
      if memq (0, value) then return (0)	% a zero inside ==> all 0
      else return value
    >>
    else return (value)
  >>
  else return (value);
end;

symbolic procedure contract (indexx, indextype);
% CONTRACT receives an index and a corresponding indextype list and returns
% a list of four lists: uncontracted indices, contracted indices, an
% uncontracted indextype list, and a contracted indextype list. The contracted
% lists represent those indices and their indextype values which are involved
% in a contraction operation, the other two lists contain everything but
% these. eg. ((a b a c)(1 1 -1 -1)) --> ((b c)(a)(1 -1)(1)).
% Note: the signs of the elements in the last list are irrelevant.
begin scalar lex1, lex2, lex3, lex4, lex5, i;
  if fixedindex (indexx) then return (list (indexx, 'nil, indextype, 'nil));

  spread (shftc (indexx, indextype), indexx, indextype);  % clean up shift ops
  lex5 := indexx; 		% a copy of the index for error output

  while indexx do <<		% look at every indice
   % indice is hidden for tracesyms or is already listed as a contraction indice
    if member (mycar (indexx), lex2) or not (atom (mycar (indexx))) then <<
      popq (indexx); popq (indextype)
    >>   				% skip a deriv op
    else if mycar (fderiv (indexx)) = 1 then popq (indexx)
   			% an integer indice cannot be a contraction indice.
    else if fixp (mycar (indexx)) then <<
      push (pop (indexx), lex1);
      push ((pop (indextype) or -1), lex3)
    >> 	% look for a repeat further down the index, if its there and not
        % in the notcon!* list (and not repeated yet again) its an almost valid
        % contraction (must check indextype's too).
    else if (i := look (mycdr (indexx), mycar (indexx), 1)) and
         not member (mycar (indexx), notcon!*) then <<
      if member (mycar (indexx), mypnth (indexx, i + 2)) then
        merror (mkmsg list ("too many contraction indices: %, %", 
			    index!-string lex5, mycar (indexx)), 't)
      else if indextype and ((!*extendedsum and not (abs (mycar (indextype)) =
          abs (mynth (mycdr (indextype), i)))) or (not !*extendedsum and 
	not (mycar (indextype) = -mynth (mycdr (indextype), i)))) then  % bad indextype pair
        merror (mkmsg list ("improper contraction: %, %", 
			index!-string lex5, mycar (indexx)), 't);
      push (pop (indexx), lex2);	% save as contraction indice
      push ((pop (indextype) or -1), lex4)
    >> else <<				% a regular indice
      push (pop (indexx), lex1);
      push ((pop (indextype) or -1), lex3)
    >>
  >>;
  return (list (reverse (lex1), reverse (lex2), reverse (lex3),
                reverse (lex4)));
end;

symbolic procedure mapindex (indexx, aindex, exp);
% MAPINDEX replaces the user input indices with the corresponding ones
% from the association list AINDEX. The new indices are from the
% ALPHALIST!* and are not supposed to appear anywhere in the original value.
% exp is used only for error messages
begin;
  indexx := sublis (aindex, indexx);   % make replacements
  foreach x in indh indexx do 
    if not memq (x, iops!*) and not fixp x and not assoc2 (x, aindex) then
      merror (mkmsg list ("free index element % in %.",
			  x, rdr!-string exp), 't);
  return (indexx);
end;

global '(conprod!-warning!-limit!* !*use!-get!-con!-sym);

symbolic (conprod!-warning!-limit!* := 511);  % print a message if contraction is bigger
!*use!-get!-con!-sym := 't;

symbolic procedure conprod (value, indexc, lis);
% CONPROD CONstructs PRODucts of indexed objects, and expands any contraction
% operations that have been indicated.
%?% LIS is a set of igen'ed indices to
%?% be used in expanding the contraction. INDEX is a mapped index.
begin scalar lex, lex1, symlst, nivalue, mp, len;
  if checktype (value, 'times) then <<    % split up if a product
    lex := mycdr (value);
    value := 'nil;
    while lex do <<   % separate indexed stuff from scalar stuff
      if free1 (mycar (lex), '(rdr)) then nivalue := mycar (lex) . nivalue
      else value := mycar (lex) . value;  % all things indexed
      lex := mycdr (lex)
    >>;
    value := 'times . value
  >>;
  symlst := !*use!-get!-con!-sym and get!-con!-sym (value, indexc);   % determine common symmetry
  if symlst = 0 then return (0);        % found ident zero
%we dont need to do this and the return value from get!-con!-sym should be fixed.
%  indexc := mycdr symlst;    % reset contraction indices
  symlst := mycar symlst;
% if symlst then write "using this symmetry in contraction: ", symlst,!$eol!$;
  nivalue := nivalue or '(1);
  lis := igen (mycar (lis), indexlim mycadr (lis), symlst, 'nil);
  if (len := length (lis)) > conprod!-warning!-limit!* then   % let user know it will be a while
    write mkmsg list ("Contraction of % terms being processed.",len),!$eol!$;
  loop:				%  must be done once, even if lis = 'nil
    setlis (indexc, mycar (lis));	% first contraction index
    if (lex1 := eval1 (value)) then <<
      mp := multip (mycar (lis), symlst);  % multiplicity of index
      if mp = 1 then lex := lex1 . lex
      else lex := list ('times, mp, lex1) . lex  % nonzero value
    >>;
    lis := mycdr (lis);
    if not lis then go to afterloop;
  go to loop;
  afterloop:
  if len > conprod!-warning!-limit!* then 
          write mkmsg list ("Reduced to % terms.", length lex), !$eol!$;
  setlis (indexc, indexc);	% clear indices
  if not lex then return ('nil)				% whole thing is 0
  else if not mycdr (lex) then   % only 1 term
          return ('times . append (nivalue, list (mycar (lex))))
  else return ('times . append (nivalue, list ('plus . lex)));
end;

%unglobal '(conprod!-warning!-limit!* !*use!-get!-con!-sym);

symbolic procedure get!-con!-sym (value, indexc);
begin scalar lex;
  lex := match!-con!-sym (find!-con!-sym (value, indexc));
  if lex = 0 then return 0 
  else return make!-con!-sym (lex, indexc);
end;

symbolic procedure find!-con!-sym (value, indexc);
begin scalar lex;
  if checktype (value, 'rdr) then return find!-con!-sym1 (value, indexc);
  foreach x in value do lex := nconc (find!-con!-sym1 (x, indexc), lex);
  return lex;
end;

symbolic procedure find!-con!-sym1 (term, indexc);
begin scalar lex, lis, lis1, indexx, herm, sze, cflg, len;
  % results from a single object internal contraction.
  if checktype (term, 'times) and mycadr term = 1 and 
	checktype (mycaddr term, 'plus) then term := mycadr mycaddr term;
  if checktype (term, 'rdr) then <<
    lis1 := foreach sym in get (mycadr term, 'symmetry) join <<
      if atom (mycar (sym)) then <<   % hermitian syms are ignored
        herm := 't;
        sze := 2
      >> else <<
        sze := sgnsym (sym);    	% sign of sym
        cflg := cnjflg (sym)           % conjugate flag
      >>;
      popq (sym); 		% pointer list
      lis := 'nil;
	 % must be symed into canonical order
      indexx := mycar syma (mycaddr term, get (mycadr term, 'symmetry), '(),
	    fill!-indextype (mycaddr term, get (mycadr term, 'indextype)));
      while sym do <<   % run over pointers
        lex := foreach x in pop sym collect mynth (indexx, x);
        % determine if all members of the block are in the contraction.
        if not memq ('nil, foreach x in lex collect memq (x, indexc)) 
	   then    % all members are in contraction, add to list
             push (lex, lis)
      >>;
      if not mycdr lis then 'nil
      else  list (reverse lis . (sze . cflg))
    >>
  >>;
  return reverse lis1;  % back in order of syms (small to large block sizes)
end;

symbolic procedure make!-con!-sym (lis, indexc);
begin scalar lex, lex1;
  lex := foreach x in lis collect <<      % look at each sym group
         mycdr x .     % start sym with sign and cnj flg
       foreach y in mycar x collect    % loop over block lists
         foreach z in y collect look (indexc, z, 1)
  >>;  
  % this errorset catches errors from merror() calls in chksym.
  lex := errorset (list ('chksym, mkquote reverse lex, 
	mkquote cnstn (1, length indexc)), 'nil, 'nil);
  if not lex then merror (
	"internal error (continuing with no contraction symmetry)",
	 'nil);
% drop the indexc and fix conprod
  return mycar lex . indexc;  % recall errorset returns the listed value
end;

%upgrade this code.
symbolic procedure match!-con!-sym (lis);
begin scalar lex, lex1;
 loop:
  if not lis then goto afterloop;  
  if lex1 := assoc (mycaar lis, mycdr lis) then <<
%now that igen() can return the signs and cnj flags, can we do it for
% conjugate syms?
      if mycddar lis or mycddr lex1 then <<>>  % cnj flag on, no joy
      else if mycadar lis = mycadr lex1 then lex := mycar lis . lex
      else if mycadar lis = -mycadr lex1 then return 0
  >>;
  lis := mycdr lis;
  goto loop;
 afterloop:
  return reverse lex;
end;


symbolic procedure eval1 (value);
begin scalar lex, lis, lex1;
  % will this ever not be a product?
  if not checktype (value, 'times) then return eval2 (value, 'nil);
  lex1 := value;
  loop:
    if not lex1 then goto afterloop;
    lex := eval2 (mycar lex1, 'nil);
    if not lex then return 'nil   % if we find a nil in the product leave immed.
    else lis := lex . lis;
    lex1 := mycdr lex1;
    goto loop;
  afterloop:
  return reverse lis;
end;

symbolic procedure eval2 (value, op);
begin scalar lex, lex1, lex2, tnsr;
  if atom value then return value
  else if free1 (value, '(rdr)) then return (value)  % no op (expensive??)
  else if checktype (value, 'rdr) then <<	% an indexed form
    tnsr := mycadr (value);			% object name
    lex := mapcar (mycaddr (value), 'eval);
    if op neq 'odf!* and fixedindex (lex) then <<
	% can read a value to replace object (but not stuff in odf*, to
        % keep simpodf** happy)
      lex2 := readtnsr (tnsr, lex);
      if mycar (lex2) then return (mk!*sq (lex2))  % so simp leaves it alone
      else return ('nil)
    >>
        % symmetries say 0 for this subs of contraction indices
    else if mycadr (syma (lex, get (tnsr, 'symmetry), 
			  get (tnsr, 'internal!-mapping), 
		fill!-indextype (lex,'()))) = 0 then
      return ('nil)
    else return (list ('rdr, tnsr, lex))   	% return form
  >>
  else if get (mycar value, 'simpfn) then
    return foreach x in value collect eval2 (x, mycar value)
  else return value;
end;

symbolic procedure collecterms (ex);
% COLLECTERMS looks down through an expression (a product or 'df) 
% to discover what the net index structure is. This can be tricky.
% it leaves its findings in the fluids nindex and nindextype (set nil 
% from the calling routine)
begin scalar lex1, lex2;
  while ex do <<				% all terms in expression
    if checktype (mycar (ex), '(rdr mrdr)) then <<	% an indexed object
  	 	% internal contractions don't contribute to the net structure
      lex1 := 'nil;
      foreach x in mycaddar (ex) do <<
		if not (x eq '!*br or x eq '!*dbr) then lex1 := x . lex1>>;
      lex2 := get (mycadar (ex), 'indextype);
      lex2 := append (lex2, cnstn (-1, length(lex1) - length(lex2)));
      lex1 := contract (reverse (lex1), lex2);
      nindex := append (nindex, mycar (lex1));
      if checktype (mycar ex, 'mrdr) then 
           nindextype := append (nindextype, mapcar (mycaddr (lex1), 'minus))
      else nindextype := append (nindextype, mycaddr (lex1))
    >>		% is a sum with indexed objects in it
    else if checktype (mycar (ex), 'plus) and 
             not free1 (mycar (ex), '(rdr mrdr)) then <<
      lex1 := collecterms1 (mycdar (ex));		% look into the sum
      nindex := append (nindex, mycar (lex1));
      nindextype := append (nindextype, mycadr (lex1))
    >>
    else if checktype (mycar (ex), '(times df odf!* minus)) % recurse down products
                then collecterms (mycdar (ex))
    else if not atom (mycar (ex)) then <<
      lex1 := collecterms1 (mycdar (ex));		% look into other forms
      nindex := append (nindex, mycar (lex1));
      nindextype := append (nindextype, mycadr (lex1))
    >>;
    ex := mycdr (ex)
  >>;
end;

symbolic procedure collecterms1 (ex);
% COLLECTERMS1 looks through a sum to determine the index structure.
% It only looks at the first term, as the rest will be seen at some
% later recursion by processvalue (?).
begin scalar lex, lex1, nindex, nindextype;
  if checktype (mycar (ex), '(rdr mrdr)) then <<	
% I can't see that there should ever be a 'mrdr here, since df(a,x+p) 
% is not allowed.
    lex := contract (mycaddar (ex), get (mycadar (ex), 'indextype));
    return (list (mycar (lex), mycaddr (lex)))
  >>
  else if checktype (mycar (ex), '(times df odf!* minus))
            and not (free1 (mycar (ex), '(rdr mrdr))) then <<
    collecterms (mycdar (ex));		% recurse down products
    return (list (nindex, nindextype))
  >>;
end;

unfluid '(nindex nindextype);


symbolic procedure chkindextype (indexx, indextype, indexc, exp);
% CHKINDEXTYPE compares the current indextype value associated with each input
% indice (in the global variable AINDEXTYPE) with the value associated in the
% current index. If they are not the same, the expression has an inconsistent
% index structure.
begin scalar lex, lex1;
  while indexx do <<
    lex1 := mycar (indexx);
    indexx := mycdr (indexx);
    if (lex := mycdr (assoc (lex1, aindextype))) and not (lex = mycar (indextype)) then
      merror (mkmsg list ("inconsistent indices: %, %",
			  lex1, exp), 't);
    if not lex and idp (lex1) and not memq (lex1, indexc) then
      aindextype := (lex1 . (mycar (indextype) or -1)) . aindextype;
    indextype := mycdr (indextype)
  >>;
end;

put ('seval, 'simpfn, 'simpseval!*);

symbolic procedure simpseval!* (val);
% SEVAL allows the user to evaluate scalar expressions without assigning
% them to some name with ==. In fact, the name SEVAL is used.
  evaltnsr ('seval, 'nil,  (mycar (val)));

unfluid '(aindextype notcon!*);   % could be higher up

endmodule;
;end;
