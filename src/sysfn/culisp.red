% usual copyright notice applies
% useful for CUlisp and and maybe Franz
symbolic;

%in CUlisp I can't get a routine to call a fexpr proc properly. Apply
% works, but not the same as in psl, so we define the proc here
symbolic fexpr procedure mkobj (u)
  apply ('mktnsr, u);  % in psl we must use list(u).

flag ('(mkobj), 'lose);   % so we don't redefine it in indexed.red

symbolic procedure unboundp (ex);
% determine if if the atom EX is unbound
  not boundp (ex);

symbolic procedure prop (u);
% return the entire property list of U
  plist (u);

symbolic procedure factorial n;   
% simple factorial (lifted from mathlib.red)
   if n<0 or not fixp n
     then error(50,list(n,"Invalid factorial argument"))
   else begin scalar m;
       m:=1;
       for i:=1:n do m:=m*i;
       return m;
   end;

;end;
