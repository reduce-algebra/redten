%******************************************************************************
%  FILE = math.red				Sun May 17 20:07:37 EDT 1987
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
symbolic;

put ('taylor, 'simpfn, 'simptaylor);

% compute a taylor series of an expression. based on the taylor function
% in muMATH.

symbolic procedure simptaylor (u);
begin scalar ex, var, pt, pw, nvar, lex, lex1, lex2, lex3;
  ex := mycar (u);
  if not (var := mycadr (u)) then return (simp ex);
  if idp (var) then pt := 0
  else <<
    pt := mycaddr (var);
    var := mycadr (var)
  >>;
  pw := mycaddr (u) or 6;
  if not fixp (pw) then return (mksq ('taylor . u, 1));
  nvar := aeval (list ('difference, var, pt));
  lex := 1;
  lex1 := lex2 := 0;
  loop:
    lex3 := aeval (list ('sub, list ('equal, var, pt), ex));
    lex2 := aeval (list ('plus, lex2, list ('times, list ('expt, nvar, lex1),
                   list ('quotient, lex3, lex))));
    if (lex1 := lex1 + 1) > pw then return (simp lex2);
    ex := aeval (list ('df, ex, var));
    if ex = 0 then return (simp lex2);
    lex := lex * lex1;
  goto loop;
end;

put ('!t!a!y!l!o!r, 'newnam, 'taylor);
;end;
