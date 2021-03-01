symbolic macro procedure test (u);
  test!* u;

fluid '(errval);

symbolic procedure merror (mes,  stat);
  if stat then << lpriw ("Error:", mes); error1()>>
  else lpriw ("Warning:", mes);


symbolic procedure test!* u;
begin scalar lex;
  lex := errorset (cadr u, 'nil, 'nil);
  if errorp lex then <<
    if not mycadddr u then <<
      write "Should not be an error: ", cadr u, !$eol!$;
      errval := 't
    >>
    else write "(OK)",!$eol!$
  >>
  else if not car (lex) = eval caddr u then <<
    errval := 't;
    write "TEST FAILED: ", cadr u, " = ", lex, " not ", eval caddr u,!$eol!$
  >>
  else if mycadddr u then <<
   write "TEST FAILED: ", cadr u, " should have caused error",!$eol!$;
   errval := 't
  >>;
  return 'nil;
end;

symbolic procedure start(u);
<<
  errval := 'nil;
  !*mode := 'symbolic;
  write !$eol!$,"TESTING ",u,"....";
>>;

symbolic procedure stats;
<<
   if errval then write "FAILED!",!$eol!$
   else write "PASSED",!$eol!$;
   !*mode := algebraic;
   errval := 'nil
>>;

;end;
