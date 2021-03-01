
% GETENVFX.RED  F. J. Wright, CBPF, Rio, 03/06/93
% Fix getenv in PSL-REDUCE for MS-DOS/MS-Windows only if necessary.
% It is necessary for REDUCE 3.4/3.4.1

symbolic(
if getenv("") then << % it's buggy
   copyd('getenv!%, 'getenv);
   procedure getenv(x);
      begin scalar val;
         if (val := getenv!%(x)) and not
            val = compress('!" . '!\ . cdr explode x) then
            return val
      end;
   >>
);

$END$
