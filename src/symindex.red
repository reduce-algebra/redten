%******************************************************************************
%  FILE = symindex.red
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
module 'symindex;
%symbolic;
%in "$redten/decl.red"$

fluid '(!*oppos !*elpos icnt ipos indexx sgn newindexx symzflg!*);
symzflg!* := 'nil;

put ('symz, 'simpfn, 'symz!*);

symbolic procedure symz!* (u);
 simp symz!*!* (car u);

put ('symz, 'prifn, 'printsymz);

symbolic procedure printsymz (u); maprint (cadr u, 0);

symbolic procedure symz!*!* (exp);
begin scalar !*oppos, !*elpos, icnt, lex, lst, ipos, lex2,
	indexx, sgn, n, l, newindexx;
  if atom (exp) then return exp;
  find!-index (exp);   % writes value into indexx
  symzop1 (indexx, 'nil, symzflg!*);  
  symzflg!* := 'nil; % clear flag
  !*oppos := reverse !*oppos;
  !*elpos := reverse !*elpos;

  if not !*symzexp then <<
     return ( % do not expand
	if checktype (exp, 'times) then
	  list ('!*sq, mksq (list ('symz, foreach x in exp collect
	     <<symzflg!*:='t; reval x>>), 1), 't)
	else reval exp )
  >>;
  if not !*oppos then 
	return if not atom mycar exp then mycar exp else exp  % no ops
  else if not mycdr !*oppos then
	merror (mkmsg list ("Invalid index ops: %",
            if checktype (exp, 'rdr) then rdr!-string exp else exp), 't);
  if not mycdr !*elpos then !*elpos := '();  % cancel 1-index op
  icnt := 1;  % counters used in map!-index
  ipos := 1;
  exp := map!-index (exp, indexx);
  indexx := reverse newindexx;
  if not atom mycar exp then exp := mycar exp;  % single rdr
  if not indexx then return exp;
  lex := gensymz (indexx); % permuted indices list
  n := length (lex);    % how many terms (is really length (indexx)!)
%  setlis (alphalist!*, pop lex);
  setlis (alphalist!*, mycar lex);
  popq lex;

  lex2 := list symz!*!* (revalindex (exp));
  l := sgn;
   % see gensymz() for an explanation of why this loop is written this way
  while mycdr lex do <<     % run over swap lists 
  setlis (alphalist!*, mycar lex);
popq lex;
     push (list ('times, l, symz!*!* (revalindex (exp))), lex2);
  setlis (alphalist!*, mycar lex);
popq lex;
     push (list ('times, l, symz!*!* (revalindex (exp))), lex2);
     l := l * sgn;
   >>;
  setlis (alphalist!*, mycar lex);
popq lex;
   push (list ('times, l, symz!*!* (revalindex (exp))), lex2);
  setlis (alphalist!*, alphalist!*);    % reset for safety
  return reval list ('quotient, 'plus . lex2, n);
end;

symbolic procedure revalindex (value);
 if atom value then value
 else if checktype (value, '(rdr mrdr)) then	 % replace indices
    symi list (mycar value, mycadr (value), revalindex1 (mycaddr value))
      % handle unsimped objects
  else if checktype (value, 'findex) then revalindex1 (value)
  else for each x in value collect revalindex (x);

symbolic procedure revalindex1 (u);
  foreach x in u collect <<
    if atom (x) and memq (x, alphalist!*) then eval x
    else if checktype (x, shift!-iops!*) then
	list (mycar x, if memq (mycadr x, alphalist!*) then
		 eval mycadr x else mycadr x)
    else x >>;

symbolic procedure symzop1 (indexx, op, passflg);
begin scalar flg, fmatch;
  if not op then << icnt := 1; !*oppos := '() >> 
  else << !*oppos := list icnt; icnt := icnt + 1 >>;
  if (op eq '!*lsqb) then sgn := 1 else sgn := -1;
  !*elpos := '();
  flg := 't;		% when 't collect indices
  loop:
     if not indexx then return;
     if memq (mycar indexx, '(!*lsqb !*lcub)) then 
	return symzop1 (mycdr indexx, mycar indexx, passflg)
     else if op and mycar (indexx) eq get (op, 'match) then
      << push (icnt, !*oppos); fmatch := t; return >>  % found matching op
    else if memq (mycar indexx, '(!*rsqb !*rcub)) and not passflg then 
	merror (mkmsg list ("invalid index ops"), 't)
     else if (mycar (indexx) eq '!*bach) then
      << flg := not flg; push (icnt, !*oppos) >>
     else if flg and not get (mycar indexx, 'iprec) then push (icnt, !*elpos);
     icnt := icnt + 1;
     popq indexx;
    go to loop;
   if not fmatch and not passflg then merror (mkmsg list ("invalid index ops"), 't);
   return
end;

fluid '(ilist);

symbolic procedure gensymz (indexx);
% gensymz() creates the index lists representing the symmetrized
% indices. This algorithm generates indices recursively in the obvious
% way, and the indices so created are anti-symmetrized with the
% following pattern of signs: 1 -1 -1 1 1 -1 -1 1 1 -1 -1 ... 1
begin scalar ilist;     % indices are collected here
  if length (indexx) > 5 then write "(This will take a while...)",!$eol!$;
  gensymz1 ('(), indexx);
  return reverse ilist;
end;

symbolic procedure gensymz1 (indexx, lis);
begin scalar lex;
  if not lis then push (indexx, ilist);
  for each x in lis do <<
	gensymz1 (append (indexx,list x), delete (x, lis))>>;
end;

symbolic procedure map!-index (exp, indexx);
  if atom exp then exp
  else if checktype (exp, '(rdr mrdr)) then 
      list (mycar exp, mycadr exp, map!-index1 (mycaddr exp))
  else if checktype (exp, 'findex) then 'findex . map!-index1 (cdr exp)
  else foreach x in exp collect map!-index (x, indexx);

symbolic procedure map!-index1 (indexx);
begin scalar lst;
  foreach y in indexx do
  <<
    if (icnt = mycar !*oppos) then popq !*oppos  % eat past ops in current symz
    else if (icnt = mycar !*elpos) then  % this index is involved in the sym
      <<
	popq !*elpos;
        if checktype (y, shift!-iops!*) then
         <<
	    push (list (mycar y, mynth (alphalist!*, ipos)), lst);
            push (mycadr y, newindexx)
         >> else << 
	     push (mynth (alphalist!*, ipos), lst);
            push (y, newindexx)
         >>;
       ipos := ipos + 1
      >> else push (y, lst);
    icnt := icnt + 1
  >>;
  return reverse lst;
end;

% uses fluid indexx to save expression index
symbolic procedure find!-index (exp);
  if checktype (exp, 'rdr) then indexx := append (indexx, mycaddr exp)
  else if checktype (exp, 'findex) then indexx := append (indexx, mycdr exp)
  else if not atom exp then foreach x in exp do find!-index (x);

endmodule;
;end;
