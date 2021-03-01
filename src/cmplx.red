%***************************************************************************
%  FILE = cmplx.red
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
module 'cmplx;
%symbolic;
%in "$redten/decl.red"$


put ('cnj, 'specprn, 'printcnj);	% for 3.2, harmless under 3.3

% new for reduce 3.3, replaces prev line
% however, this method hands the function name to PRINTCNJ too,
% unlike the 3.2 version.
put ('cnj, 'prifn, 'printcnj);	

put ('cnj, 'simpfn, 'simpcnj);

% printcnj is the routine which prints a conjugate form nicely. if the
% conjugation is applied to an atom, a bar is printed over the atom's
% name, otherwise it appears as an uneval'ed form.

symbolic procedure printcnj (u);
begin integer i, posl;
  if (mycar (u) eq 'cnj) then u := mycdr (u); % name given in 3.3, but not in 3.2
  if not !*nat or not atom (mycar (u)) then <<
    prin2!* (base!-case!-string "cnj (");		% operator
    maprint (mycar (u), 0);	% operand
    prin2!* (")")
  >> else <<
    testwidth (mycar u, 'nil, 'nil);   % see if it fits
    posl := posn!*;
    ycoord!* := ycoord!* + 1;		% move up a line to make bar
    if ycoord!* > ymax!* then ymax!* := ycoord!*;
    for i := flatsizec (mycar (u)) step -1 	% print _ for length of name
      until 1 do prin2!*("_");
    ycoord!* := ycoord!* - 1;
    posn!* := posl;
    maprint (mycar (u), 0)	% print it
  >>;
end;

% simpcnj is the routine which applies the conjugation operator to an
% expression. to do a conjugate, the expression is searched for complex
% objects and 'i, these are then replaced by conjugate operations.
% since the conjugation cannot change the form of the expression, no
% reevaluation is required.

symbolic procedure simpcnj (u);
  if checktype (mycar (u), 'cnj) then simp!* (mycadar (u)) % conj (conj (x)) -> x
  else cnjsq (simp!* (mycar (u)));	% conjugate the standard quotient.

% conjsq applies the conjugation to the numerator and denominator of the
% standard quotient.

symbolic procedure cnjsq (u);
  cnjf (reorder numr (u)) . reorder cnjf (denr (u));

fluid '(cmplxflag);	% flag 't says 'i appears in this form, negate it.

% conjf conjugates standard forms. if a form contains i, it is negated
% to form the conjugate.

symbolic procedure cnjf (u);
begin scalar lex, cmplxflag;
  if atom (u) then return (u);
  lex := cnjt (mycar (u));	% conjugate terms
  if cmplxflag then lex := mycar (multd (-1, !*t2f (lex)));
  return (lex . cnjf (mycdr (u)))
end;

% conjt conjugates terms, it applies conjd to domain elements.

symbolic procedure cnjt (u);
  if atom (u) then u	% end of recursion
  else if mycdr (u) then cnjd (mycar (u)) . cnjf (mycdr (u))
  else cnjd (mycar (u)) . list (cnjt (mycadr (u)));

% conjd conjugates domain elements. if the main variable is 'i, the
% flag is set so that conjf can negate the term. if the main variable is
% a name flagged 'complex, it is replaced by an unevaled function call to
% conj: (conj <main variable>). if the main variable begins with 'conj,
% it is replaced by the operand. Atoms that are not flagged 'complex are
% not touched. if the main variable is not an atom, then if the car of
% the main variable has a 'cnjfn property, the function named is applied,
% otherwise nothing happens.

symbolic procedure cnjd (u);
begin scalar mnvar, pwer, lex;
  mnvar := mycar (u);		% main variable
  pwer := mycdr (u);		% integer power
  if mnvar eq 'i then cmplxflag := 't
  else if atom (mnvar) and flagp (mnvar, 'complex) then 
    mnvar := car (fkern (list ('cnj, mnvar)))
  else if atom (mnvar) then 't   % dont want to change anything, just avoid ifs
  else if mycar (mnvar) eq 'cnj then mnvar := mycadr (mnvar)
            % this can happen if factor switch is on, 
            % then forms can appear in kernel locations
  else if not atom (mycar (mnvar)) then mnvar := cnjf(mnvar)
  else if (lex := get (mycar (mnvar), 'cnjfn)) then 
    mnvar := apply (lex, list (mnvar))
  else <<				% function 
    if mapcar (for each x in mycdr (mnvar) collect list (x), 'simpcnj) = 
       mapcar (mycdr (mnvar), 'simp!*) then 't
    else mnvar := car (fkern (list ('cnj, mnvar)))
  >>;
  return (mnvar . pwer);		% put it back together and return
end;

unfluid '(cmplxflag);

algebraic procedure re (u);
  (u + cnj (u))/2;

algebraic procedure im (u);
  (u - cnj (u))/(2*i);

algebraic procedure cmod (u);
  sqrt (u*cnj(u));


%put ('re, 'simpfn, 'simpreal);
%
%% simpreal computes the real part of an expression.
%
%symbolic procedure simpreal (u);
%  simp (list ('quotient, list ('plus, mycar (u), 
%       list ('cnj, mycar (u))), 2));
%
%put ('im, 'simpfn, 'simpimg);
%
%% simpimg computes the imaginary part of an expression.
%
%symbolic procedure simpimg (u);
%  simp (list ('quotient, list ('plus, mycar (u), 
%       list ('minus, list ('cnj, mycar (u)))), '(times i 2)));
%
%put ('cmod, 'simpfn, 'simpcmod);
%
%% simpcmod computes the modulus of an expression.
%
%symbolic procedure simpcmod (u);
%  simp (list ('sqrt, list ('times, mycar (u), list ('cnj, mycar (u)))));
%
%put ('rat, 'simpfn, 'simprat);
%
%% simprat rationalizes an expression. it will not work if names flagged
%% 'complex occur in the expression, since the conjugates cancel out again.
%
%symbolic procedure simprat (u);
%begin scalar lex, lex1, l!*factor;
%  u := simp (mycar (u));
%  if atom (lex1 := denr (u)) then return (u);
%  l!*factor := !*factor; !*factor := 'nil;  % save switch, and turn it off.
%  lex := cnjf (lex1);	% conjugate of denominator.
%  lex1 := (quotsq (subs2 !*f2q (multf (numr (u), lex)), 
%      subs2 !*f2q (multf (lex1, lex))));
%  !*factor := l!*factor;
%  return (lex1);
%end;
%

% This version works better than the above, since the factor switch setting
% is irrelevant
algebraic procedure rat(u);
num(u)*cnj(den(u))/(re(den(u))^2+im(den(u))^2);

put ('complex, 'simpfn, 'complex!*);

% complex declares each member of the given list to be 'complex.
symbolic procedure complex!* u;
<<
  flag (u, 'complex);
  write u,!$eol!$;
  't . 1
>>;


put ('nocomplex, 'simpfn, 'nocomplex!*);

% nocomplex removes the 'complex declaration from each member of the given
% list.

symbolic procedure nocomplex!* u;
<<
  remflag (u, 'complex);
  write u, !$eol!$;
  't . 1
>>;

put ('expt, 'cnjfn, 'cnjexpt);

% conjexpt handles the conjugation of powers where the power is not an
% integer.

symbolic procedure cnjexpt (u);
  if not flagp (mycadr (u), 'complex) then
     car (fkern (list ('expt, mycadr (u), reval (list ('cnj, (mk!*sq (simp (mycaddr (u)))))))))
  else if flagp (mycadr (u), 'complex) and not flagp (mycaddr (u), 'complex) then
     car (fkern (list ('expt, list ('cnj, mycadr (u)), mycaddr (u))))
  else u;

put('rdr, 'cnjfn, 'cnjrdr);

symbolic procedure cnjrdr (u);   % used for unevaled index refs
begin scalar lex;
  if lex := get (mycadr u, 'conjugate) then return list ('rdr, mycar lex, mycaddr u)
%  else if not flagp (mycadr u, 'complex) then return u
  else return list ('cnj, u);
end;


endmodule;
;end;

