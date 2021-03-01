% usual copyright notice applies
% System deps for csl.
symbolic;
flag ('(setpchar), 'lose);

symbolic procedure unboundp (ex);
% determine if if the atom EX is unbound
% csl boundp does not seem to work
% CCD: actually boundp works, while the other kludge does not work. (24/12/98)
  not boundp (ex);
%    if eval (ex) = eval ('indefinite!-value!*) then 't else 'nil;

symbolic procedure prop (u);
% return the entire property list of U
  plist (u);

;end;
