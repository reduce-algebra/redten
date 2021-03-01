%***************************************************************************
%  FILE = np.red 				
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
module 'np;
flag ('(nulltetrad npspin npmetric npweyl npricci ), 'indexedfn);	%

nulltet := '!z;			% nulltetrad connection
npt1 	:= '!l;			% nulltetrad vectors
npt2 	:= '!n;
npt3 	:= '!m;
npt4 	:= '!m!c;		% conjugate of m
npspin 	:= '!n!p!s!p!c;  	% name for spin coeffs
npweyl!_sp 	:= '!n!p!C;  	% name for weyl spinor
npweyl 	:= '!P;          	% name for NP shorthand name of weyl spinor
npricci!_sp 	:= '!n!p!r!i!c;	% name for ricci spinor
npricci := '!F!I;		% name for NP shorthand name of ricci spinor

put ('nulltet, 'simpfn, 'nulltet!*);

symbolic procedure nulltet!* (u);
(lambda x;<<
  prin2 mkmsg list ("Fill in values for % (or %, %, and %)", nulltet, 
		npt1, npt2, npt3);
  terpri();
  prin2 mkmsg list ("and do setcon(%); then call tenmetric().", nulltet);
  terpri(); x>>)(nulltet!*!* (u));

% set up the tetrad relations, but the user must enter the components
symbolic procedure nulltet!*!* (u);
begin scalar npcon, t1, t2, t3, t4, verbose!*;
  frmetric!* ('nil);  % get the metric made before the generics are checked

  npcon := mycar getnme (mycar u, '(nil . nil), 'nulltet);
  npcon := newnme (npcon, nulltet);
  t1 := mycar getnme (mycar u, '(nil . nil), 'nulltet);
  t1 := newnme (t1, npt1);
  t2 := mycar getnme (mycar u, '(nil . nil), 'nulltet);
  t2 := newnme (t2, npt2);
  t3 := mycar getnme (mycar u, '(nil . nil), 'nulltet);
  t3 := newnme (t3, npt3);
  t4 := mycar getnme (mycar u, '(nil . nil), 'nulltet);
  t4 := newnme (t4, npt4);
  tabprint list mkmsg list ("Creating % (with %, %, % and %)",
	npcon, t1, t2, t3, t4);
  mktnsr!* (npcon, '(-2 -1),'nil, 'nil, 'connection, "Null connection");
  int!-map (npcon, '(3 a!#), '(2 a!#), 1 ./ 1, 't);   % last column is cnj m
% rewrite to remove explicit refs to indices 0-3.
  subobj!*!* (t1, '(a!#), npcon, '(0 a!#), 1 ./ 1, 'nil);
  subobj!*!* (t2, '(a!#), npcon, '(1 a!#), 1 ./ 1, 'nil);
  subobj!*!* (t3, '(a!#), npcon, '(2 a!#), 1 ./ 1, 'nil);
  subobj!*!* (t4, '(a!#), npcon, '(3 a!#), 1 ./ 1, 'nil);  % no cnj!!!!
  put (npcon, 'printname, nulltet);
  put (t1, 'printname, npt1);
  put (t2, 'printname, npt2);
  put (t3, 'printname, npt3);
  put (t4, 'printname, npt3);  % yes this is t3!
  put (t4, 'conjugate, list (t3, 't));
  put (t3, 'conjugate, list (t4, 'nil));
  foreach x in list (t1, t2, t3, t4) do describe!* (x, "Null tetrad vector", 'nil);
  put (getmetric (2), 'nulltet, npcon);
  put (getmetric (2), 'npt1, t1);
  put (getmetric (2), 'npt2, t2);
  put (getmetric (2), 'npt3, t3);
  put (getmetric (2), 'npt4, t4);
  return npcon ./ 1;
end;

put ('nulltetrad, 'simpfn, 'nulltetrad!*);

symbolic procedure nulltetrad!* (u);
begin scalar lex, lex1, npcon, met;
  npcon := mycar nulltet!*!* (u);
  met := getmetric (1);
  if get (met, 'symmetry) = ifmtsym '((0 1 2)) then << % done by hand essentially
    evaltnsr1 (npcon, '(0 0), list ('sqrt, list ('rdr, met, '(0 0))), 'nil);
    evaltnsr1 (npcon, '(0 1), list ('sqrt, list ('minus, list ('rdr, met, '(1 1)))), 'nil);
    evaltnsr1 (npcon, '(1 0), list ('sqrt, list ('rdr, met, '(0 0))), 'nil);
    evaltnsr1 (npcon, '(1 1), list ('minus, list ('sqrt, list ('minus, list ('rdr, met, '(1 1))))), 'nil);
    evaltnsr1 (npcon, '(2 2), list ('sqrt, list ('minus, list ('rdr, met, '(2 2)))), 'nil);
    evaltnsr1 (npcon, '(2 3), list ('times, 'i, list ('sqrt, list ('minus, list ('rdr, met, '(3 3))))), 'nil);
    multiplier!* (list (npcon, '(quotient 1 (sqrt 2))));
  >>
  else merror ("Sorry I can't handle non-diagonal metrics", 't);
  protect!* (npcon, 'w);
  setcon (npcon);
  put (met, 'cometric, list (getmetric (2)));
  put (getmetric (2), 'cometric, list met);
  cleaner ('nulltetrad);
  return (npcon . 1);
end;

put ('npspin, 'simpfn, 'npspin!*);
symbolic procedure npspin!* (u);
begin scalar nptnsr, lex, lex1, conn;
   nptnsr := mycar getnme (mycar (u), '(nil . nil), 'npspin);
   lex1 := get (getmetric (2), 'npspin);	% see if its already been made
   if not nptnsr and indexed (lex1) then return (lex1 . 1);
   nptnsr := newnme (nptnsr, npspin);		% get a name for it
   tabprint (list ("computing ", nptnsr));% so user knows what the name will be
   cov!* (conn := getcon (2, 1));   % compute covariant derivatives.
   mktnsr!* (nptnsr, '(-3 -3 -3 -4), ifmtsym '((1 1 2)), 'nil, 'spin,
		"Newman-Penrose spin coefficients");
   put (nptnsr, 'printname, npspin);

  lex := igen ('(a!# b!# c!# d!#), get (nptnsr, 'indices),
		get (nptnsr, 'symmetry), 'nil);

%   if (!*showindices) then tabthenprint ("computing kappa");
   evaltnsr1 (nptnsr, pop lex,   % kappa
	      list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
		    list ('rdr, conn, '((!*at!- 2) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 0) (!*at!+ b!#)))), 'nil);
%   if (!*showindices) then tabthenprint ("computing sigma");
   evaltnsr1 (nptnsr, pop lex,   % sigma (1112)
	      list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
		     list ('rdr, conn, '((!*at!- 2) (!*at!+ a!#))), 
		     list ('rdr, conn, '((!*at!- 2) (!*at!+ b!#)))), 'nil);
%   if (!*showindices) then tabthenprint ("computing rho");
   evaltnsr1 (nptnsr, pop lex,   % rho (1121)
	      list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
		    list ('rdr, conn, '((!*at!- 2) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 3) (!*at!+ b!#)))), 'nil);
%   if (!*showindices) then tabthenprint ("computing tau");
   evaltnsr1 (nptnsr, pop lex,   % tau (1122)
	      list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
		     list ('rdr, conn, '((!*at!- 2) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 1) (!*at!+ b!#)))), 'nil);
%   if (!*showindices) then tabthenprint ("computing eps");
   evaltnsr1 (nptnsr, pop lex, % eps (1211)
	      list ('quotient, 
		    list ('plus, 
	  list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
			list ('rdr, conn, '((!*at!- 1) (!*at!+ a!#))),
			list ('rdr, conn, '((!*at!- 0) (!*at!+ b!#)))),
	  list ('minus,
	  list ('times, list ('rdr, conn, '((!*at!- 2) (!*at!- a!#) !*dbr b!#)),
		list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))),
		list ('rdr, conn, '((!*at!- 0) (!*at!+ b!#)))))
			  ), 2), 
	      'nil);
%   if (!*showindices) then tabthenprint ("computing beta");
   evaltnsr1 (nptnsr, pop lex,   % beta (1212)
	      list ('quotient, 
		    list ('plus, 
		  list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
				list ('rdr, conn, '((!*at!- 1) (!*at!+ a!#))),
				list('rdr, conn, '((!*at!- 2) (!*at!+ b!#)))),
		  list ('minus,
		list ('times, list ('rdr, conn, '((!*at!- 2) (!*at!- a!#) !*dbr b!#)),
			      list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))),
			      list ('rdr, conn, '((!*at!- 2) (!*at!+ b!#)))))
			  ), 2), 
	      'nil);
%   if (!*showindices) then tabthenprint ("computing alpha");
   evaltnsr1 (nptnsr, pop lex, % alpha (1221)
	      list ('quotient, 
		    list ('plus, 
		  list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
			list ('rdr, conn, '((!*at!- 1) (!*at!+ a!#))),
			list('rdr, conn, '((!*at!- 3) (!*at!+ b!#)))),
			list ('minus,
	  list ('times, list ('rdr, conn, '((!*at!- 2) (!*at!- a!#) !*dbr b!#)),
	  list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))),
	  list ('rdr, conn, '((!*at!- 3) (!*at!+ b!#)))))
				     ), 2), 
	      'nil);
%   if (!*showindices) then tabthenprint ("computing gamma");
   evaltnsr1 (nptnsr, pop lex, %gam (1222)
	      list ('quotient, 
		    list ('plus, 
	  list ('times, list ('rdr, conn, '((!*at!- 0) (!*at!- a!#) !*dbr b!#)),
			list ('rdr, conn, '((!*at!- 1) (!*at!+ a!#))),
			list ('rdr, conn, '((!*at!- 1) (!*at!+ b!#)))),
	  list ('minus,
	  list ('times, list ('rdr, conn, '((!*at!- 2) (!*at!- a!#) !*dbr b!#)),
		list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))),
		list ('rdr, conn, '((!*at!- 1) (!*at!+ b!#)))))
			  ), 2), 
	      'nil);
%   if (!*showindices) then tabthenprint ("computing pi");
   evaltnsr1 (nptnsr, pop lex,   % pi (2211)
	      list ('minus, list ('times, list ('rdr, conn, '((!*at!- 1) (!*at!- a!#) !*dbr b!#)),
		    list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 0) (!*at!+ b!#))))), 'nil);
%   if (!*showindices) then tabthenprint ("computing mu");
   evaltnsr1 (nptnsr, pop lex,   % mu (2212)
	      list ('minus, list ('times, list ('rdr, conn, '((!*at!- 1) (!*at!- a!#) !*dbr b!#)),
		    list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 2) (!*at!+ b!#))))), 'nil);
%   if (!*showindices) then tabthenprint ("computing lambda");
   evaltnsr1 (nptnsr, pop lex,   % lambda (2221)
	      list ('minus, list ('times, 
			     list ('rdr, conn, '((!*at!- 1) (!*at!- a!#) !*dbr b!#)),
		    list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 3) (!*at!+ b!#))))), 'nil);
%   if (!*showindices) then tabthenprint ("computing nu");
   evaltnsr1 (nptnsr, pop lex,   % nu (2222)
	      list ('minus, list ('times, list ('rdr, conn, '((!*at!- 1) (!*at!- a!#) !*dbr b!#)),
		    list ('rdr, conn, '((!*at!- 3) (!*at!+ a!#))), 
		    list ('rdr, conn, '((!*at!- 1) (!*at!+ b!#))))), 'nil);

%   put (nptnsr, 'altmetric, currentmetric);  % save metric environment
   protect!* (nptnsr, 'w);
   put (getmetric (2), 'npspin, nptnsr);	% store name on metric
   cleaner ('npspin);
   return (nptnsr . 1);
end;

put ('!n!p!D, 'simpfn, 'npd!*);

symbolic procedure npd!* (u);
  simp npop!* (car u, 0);

put ('!n!p!D!E!L, 'simpfn, 'npdelta!*);
symbolic procedure npdelta!* (u);
  simp npop!* (car u, 1);

put ('!n!p!d!e!l, 'simpfn, 'npdel!*);
symbolic procedure npdel!* (u);
  simp npop!* (car u, 2);

put ('!n!p!d!e!l!c, 'simpfn, 'npdelc!*);
symbolic procedure npdelc!* (u);
  simp npop!* (car u, 3);

symbolic procedure npop!* (u, ex);
begin scalar lex;
  u := reval (u); 
  lex := list ('times, list ('rdr, getcon(2,1), 
			     list (list ('!*at!-, ex), '(!*at!+ a!#))), 
	       list ('pdf, u, '(findex  a!#)));
  lex := evaltnsr1 ('lex, 'nil, lex, 't);
%  cleaner ('npop);
  return (lex);
end;

put ('npweyl, 'simpfn, 'npweyl!*);

symbolic procedure npweyl!* (u);
begin scalar nptnsr, nptnsr1, lex, lex1, lex2,
   npalpha, npbeta, npgam, npeps, npkappa, npmu, npnu, nppi,
   nplam, npsig, nptau, nprho,
   cnpalpha, cnpbeta, cnpgam, cnpeps, cnpkappa, cnpmu, cnpnu, cnppi,
   cnplam, cnpsig, cnptau, cnprho;

   nptnsr := mycar getnme (mycar (u), '(nil . nil), 'npweyl);
   lex1 := get (getmetric (2), 'npweyl);	% see if its already been made
   if not nptnsr and indexed (lex1) then return (lex1 . 1);
   nptnsr := newnme (nptnsr, npweyl);		% get a name for it
   nptnsr1 := newnme ('nil, npweyl!_sp);
   tabprint (list ("computing ", nptnsr, " and ", nptnsr1));% so user knows what the name will be

% Can't do this compiled in CSL
%  foreach x in pair ('(npkappa npsig nprho nptau npeps npbeta 
%	npalpha npgam nppi npmu nplam npnu), 
%		igen ('(a!# b!# c!# d!#), get (lex1, 'indices),
%	get (lex1, 'symmetry),'nil)) do 
%	set (car x, reval mk!*sq readtnsr (lex1, cdr x));
%  foreach x in pair (
%	'(npkappa npsig nprho nptau npeps npbeta 
%		npalpha npgam nppi npmu nplam npnu), 
%	'(cnpkappa cnpsig cnprho cnptau cnpeps cnpbeta 
%		cnpalpha cnpgam cnppi cnpmu cnplam cnpnu)) 
%     do set (cdr x, reval list ('cnj, eval car x));

  lex1 := car npspin!* ('nil);
  lex := igen ('(a!# b!# c!# d!#), get (lex1, 'indices),
		 get (lex1, 'symmetry),'nil);
  npkappa	:= reval mk!*sq readtnsr (lex1, pop lex);
  npsig		:= reval mk!*sq readtnsr (lex1, pop lex);
  nprho		:= reval mk!*sq readtnsr (lex1, pop lex);
  nptau		:= reval mk!*sq readtnsr (lex1, pop lex);
  npeps		:= reval mk!*sq readtnsr (lex1, pop lex);
  npbeta	:= reval mk!*sq readtnsr (lex1, pop lex);
  npalpha	:= reval mk!*sq readtnsr (lex1, pop lex);
  npgam		:= reval mk!*sq readtnsr (lex1, pop lex);
  nppi		:= reval mk!*sq readtnsr (lex1, pop lex);
  npmu		:= reval mk!*sq readtnsr (lex1, pop lex);
  nplam		:= reval mk!*sq readtnsr (lex1, pop lex);
  npnu		:= reval mk!*sq readtnsr (lex1, pop lex);
  cnpkappa	:= reval list ('cnj, npkappa);
  cnpsig	:= reval list ('cnj, npsig);
  cnprho	:= reval list ('cnj, nprho);
  cnptau	:= reval list ('cnj, nptau);
  cnpeps	:= reval list ('cnj, npeps);
  cnpbeta	:= reval list ('cnj, npbeta);
  cnpalpha	:= reval list ('cnj, npalpha);
  cnpgam	:= reval list ('cnj, npgam);
  cnppi		:= reval list ('cnj, nppi);
  cnpmu		:= reval list ('cnj, npmu);
  cnplam	:= reval list ('cnj, nplam);
  cnpnu		:= reval list ('cnj, npnu);
  
  mktnsr!* (nptnsr, '(0), '(), 'nil, 'npweyl,
		"Newman-Penrose Weyl spinor");
  restrict!* (npweyl, '(0), '(4))$
  put (nptnsr, 'printname, npweyl);
  mktnsr!* (nptnsr1, '(-3 -3 -3 -3), ifmtsym '((1 1 2 3 4)), 'nil, 'npweyl,
		"Newman-Penrose Weyl spinor");
  put (nptnsr1, 'printname, npweyl!_sp);
  put (nptnsr, 'corem, list (nptnsr1));  % so kill takes out both
  put (nptnsr1, 'corem, list (nptnsr));

  lex := igen ('(a!#), get (nptnsr, 'restricted) or get (nptnsr, 'indices),
	 get (nptnsr, 'symmetry), 'nil);
  lex1 := igen ('(a!# b!# c!# d!#), get (nptnsr1, 'indices), 
	get (nptnsr1, 'symmetry), 'nil);

  %P[0],  from NP 4.2b
  evaltnsr1 (nptnsr, car lex, 
	list ('plus,
	     reval (npop!* (npsig, 0)),
	     list ('minus, reval (npop!* (npkappa, 2))),
             list ('minus,
                list ('times, npsig,
		      list ('plus, 
			    nprho,
			    cnprho,
			    list ('times, 3, npeps),
			    list ('minus, cnpeps)))),
             list ('times, npkappa,
		   list ('plus, 
			 nptau,
			 list ('minus, cnppi),
			 cnpalpha,
			 list ('times, 3, npbeta)))), 'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

  %P[1] from NP 4.2e
  evaltnsr1 (nptnsr, car lex, 
	list ('plus, reval (npop!* (npbeta, 0)),
	     list ('minus, reval (npop!* (npeps, 2))),
             list ('minus, list ('times,
				npsig,
				 list ('plus, npalpha, nppi))),
  	     list ('minus, list ('times,
				 npbeta,
				 list ('plus, cnprho,
				       list ('minus, cnpeps)))),
	     list ('times, npkappa, list ('plus,
					  npmu, npgam)),
	     list ('times, npeps, list ('plus,
					cnpalpha,
					list ('minus, cnppi)))),
		'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

  % the expression below is obtained from NP equations 4.2f+4.2l-4.2h
  evaltnsr1 (nptnsr, car lex,
    list ('quotient, list ('plus, reval (npop!* (npgam, 0)),
	list ('minus, reval (npop!* (npeps, 1))),
	reval (npop!* (npmu, 0)),
        list ('minus, reval (npop!* (nppi,2))),
        reval (npop!* (npbeta, 3)),
        list ('minus, npop!* (npalpha, 2)),
        list ('times, list ('plus, npalpha, nppi),
		list ('plus, cnpalpha, list ('minus, list ('times, 2, npbeta)),
			list ('minus, nptau), list ('minus, cnppi))),
        list ('times, list ('plus, npgam, npmu),
		list ('plus, list ('times, 2, npeps), cnpeps, nprho,
			list ('minus, cnprho))),
        list ('times, npeps, list ('plus, cnpgam, list ('minus, cnpmu))),
        list ('times, npbeta, list ('plus, cnpbeta, list ('minus, cnptau))),
        list ('times, 2, npnu, npkappa),
        list ('minus, list ('times, 2, npsig, nplam))), 3), 'nil);


  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

  %P[3]  from NP 4.2r
  evaltnsr1 (nptnsr, car lex, 
	list ('plus, list ('minus, reval (npop!* (npalpha, 1))),
	     reval (npop!* (npgam, 3)),
	     list ('times, npnu, list ('plus, nprho, npeps)),
             list ('minus, list ('times, nplam, list ('plus,
						      nptau, npbeta))),
             list ('times, npalpha, list ('plus,
					  cnpgam,
% NP paper has only mu here (type, Chandra has it correct)
					  list ('minus, cnpmu))),
             list ('times, npgam, list ('plus, 
					cnpbeta,
					list ('minus, cnptau)))), 
	'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

  %P[4] from NP 4.2j
  evaltnsr1 (nptnsr, car lex, 
	 list ('plus, list ('minus, reval (npop!* (nplam, 1))),
	     reval (npop!* (npnu, 3)),
             list ('minus, list ('times, nplam, 
				 list ('plus, npmu,
				       cnpmu,
				       list ('times, 3, npgam),
				       list ('minus, cnpgam)))),
	     list ('times, npnu, list ('plus, 
				       list ('times, 3, npalpha),
				       cnpbeta,
				       nppi,
				       list ('minus, cnptau)))),
		'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link
  if not get (nptnsr, 'tvalue) then 
    tabthenprint ("** this metric is conformally flat.");

%   put (nptnsr, 'altmetric, currentmetric);  % save metric environment
   protect!* (nptnsr, 'w);
   protect!* (nptnsr1, 'w);
   put (getmetric (2), 'npweyl, nptnsr);	% store name on metric
   cleaner ('npweyl);
   return (nptnsr . 1);
end;

put ('npricci, 'simpfn, 'npricci!*);

symbolic procedure npricci!* (u);
begin scalar nptnsr, nptnsr1, lex, lex1, lex2,
  npalpha, npbeta, npgam, npeps, npkappa, npmu, npnu, nppi,
  nplam, npsig, nptau, nprho,
  cnpalpha, cnpbeta, cnpgam, cnpeps, cnpkappa, cnpmu, cnpnu, cnppi,
  cnplam, cnpsig, cnptau, cnprho;

  nptnsr := mycar getnme (mycar (u), '(nil . nil), 'npricci);
  lex1 := get (getmetric (2), 'npricci);	% see if its already been made
  if not nptnsr and indexed (lex1) then return (lex1 . 1);
  nptnsr := newnme (nptnsr, npricci);		% get a name for it
  nptnsr1 := newnme ('nil, npricci!_sp);
  tabprint (list ("computing ", nptnsr, " and ", nptnsr1));% so user knows what the name will be

  lex1 := car npspin!* ('nil);
  lex := igen ('(a!# b!# c!# d!#), get (lex1, 'indices),
		 get (lex1, 'symmetry),'nil);
  npkappa	:= reval mk!*sq readtnsr (lex1, pop lex);
  npsig		:= reval mk!*sq readtnsr (lex1, pop lex);
  nprho		:= reval mk!*sq readtnsr (lex1, pop lex);
  nptau		:= reval mk!*sq readtnsr (lex1, pop lex);
  npeps		:= reval mk!*sq readtnsr (lex1, pop lex);
  npbeta	:= reval mk!*sq readtnsr (lex1, pop lex);
  npalpha	:= reval mk!*sq readtnsr (lex1, pop lex);
  npgam		:= reval mk!*sq readtnsr (lex1, pop lex);
  nppi		:= reval mk!*sq readtnsr (lex1, pop lex);
  npmu		:= reval mk!*sq readtnsr (lex1, pop lex);
  nplam		:= reval mk!*sq readtnsr (lex1, pop lex);
  npnu		:= reval mk!*sq readtnsr (lex1, pop lex);
  cnpkappa	:= reval list ('cnj, npkappa);
  cnpsig	:= reval list ('cnj, npsig);
  cnprho	:= reval list ('cnj, nprho);
  cnptau	:= reval list ('cnj, nptau);
  cnpeps	:= reval list ('cnj, npeps);
  cnpbeta	:= reval list ('cnj, npbeta);
  cnpalpha	:= reval list ('cnj, npalpha);
  cnpgam	:= reval list ('cnj, npgam);
  cnppi		:= reval list ('cnj, nppi);
  cnpmu		:= reval list ('cnj, npmu);
  cnplam	:= reval list ('cnj, nplam);
  cnpnu		:= reval list ('cnj, npnu);

  mktnsr!* (nptnsr, '(0 0), ifmtsym '((c 1 1 2)), 'nil, 'npricci,
		"Newman-Penrose Ricci projection");
  restrict!* (npricci, '(0 0), '(2 2))$
  mktnsr!* (nptnsr1, '(-3 -3 -4 -4), ifmtsym '((1 1 2)(1 3 4)(c 2 1 3)),
			 'nil, 'npricci,
		"Newman-Penrose Ricci projection");
  put (nptnsr, 'printname, npricci);
  put (nptnsr1, 'printname, npricci!_sp);
  put (nptnsr, 'corem, list (nptnsr1));  % so kill takes out both
  put (nptnsr1, 'corem, list (nptnsr));
  lex := igen ('(a!# b!#), get (nptnsr, 'restricted) or get (nptnsr, 'indices),
	 get (nptnsr, 'symmetry), 'nil);
  lex1 := igen ('(a!# b!# c!# d!#), get (nptnsr1, 'indices), 
	get (nptnsr1, 'symmetry), 'nil);

%  if (!*showindices) then tabthenprint (mkmsg list ("computing %[0 0]", nptnsr));
  % FI[0,0], from NP 4.2a
  evaltnsr1  (nptnsr, car lex,
     list ('plus,
	     reval (npop!* (nprho, 0)),
	     list ('minus, reval (npop!* (npkappa, 3))),
	     list ('minus, list ('times, nprho, nprho)),
             list ('minus, list ('times, npsig, cnpsig)),
	     list ('minus, list ('times, nprho, 
				 list ('plus, npeps, cnpeps))),
	     list ('times, cnpkappa, nptau),
             list ('times, npkappa, list ('plus,
					  list ('times, 3, npalpha),
					  cnpbeta,
					  list ('minus, nppi)))), 'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link


%  if (!*showindices) then tabthenprint (mkmsg list ("computing %[0 1]", nptnsr));
% FI[0,1] from NP conjugate of 4.2d
  evaltnsr1 (nptnsr, car lex,
	list ('cnj,	 list ('plus,
	     reval (npop!* (npalpha, 0)),
	     list ('minus, reval (npop!* (npeps, 3))),
             list ('minus, list ('times, npalpha,
			 list ('plus, nprho, cnpeps,
			       list ('minus, list ('times, 2, npeps))))),
             list ('minus, list ('times, npbeta, cnpsig)),
             list ('times, cnpbeta, npeps),
	     list ('times, npkappa, nplam),
             list ('times, cnpkappa, npgam),
	     list ('minus, list ('times, nppi, list ('plus, npeps, nprho))))),
	      'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link


%  if (!*showindices) then tabthenprint (mkmsg list ("computing %[0 2]", nptnsr));
% FI[0,2] from NP conjugate 4.2g
  evaltnsr1  (nptnsr, car lex,
	list ('cnj, list ('plus,
	     reval (npop!* (nplam, 0)),
	     list ('minus, reval (npop!* (nppi, 3))),
             list ('minus,  list ('times, nprho, nplam)),
	     list ('minus,  list ('times, cnpsig, npmu)),
             list ('minus, list ('times, nppi,
				 list ('plus, nppi,
				       npalpha,
				       list ('minus, cnpbeta)))),
%NP paper has kappa here (Chandra has it correct)
             list ('times, npnu, cnpkappa),
             list ('times, nplam, 
				 list ('plus, list ('times, 3, npeps),
				 list ('minus, cnpeps))))), 'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

%  if (!*showindices) then tabthenprint (mkmsg list ("computing %[1 1]", nptnsr));
% FI[1,1] from NP 4.2f+4.2l
  evaltnsr1 (nptnsr, car lex,
      list ('quotient, list ('plus,
	     reval (npop!* (npgam, 0)),
	     list ('minus, reval (npop!* (npeps, 1))),
	     reval (npop!* (npalpha, 2)),
	     list ('minus, reval (npop!* (npbeta, 3))),
             list ('minus, list ('times, npalpha,
				 list ('plus, nptau, cnppi, cnpalpha,
				       list ('minus, list ('times, 2, npbeta))))),
             list ('minus, list ('times, npbeta, 
				 list ('plus, cnptau, nppi, cnpbeta))),
             list ('times, npgam, list ('plus, npeps, cnpeps,
					cnprho, list ('minus, nprho))),
             list ('times, npeps, list ('plus, npgam, cnpgam, 
					list ('minus, npmu), cnpmu)),
             list ('minus, list ('times, nptau, nppi)),
             list ('times, npnu, npkappa),
             list ('minus, list ('plus, list ('times, npmu, nprho),
				 list ('minus, list ('times, nplam, npsig))))),
					   2), 'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

%  if (!*showindices) then tabthenprint (mkmsg list ("computing %[1 2]", nptnsr));
% FI[1,2] from NP 4.2o
  evaltnsr1  (nptnsr, car lex,
	 list ('plus,
	     reval (npop!* (npgam, 2)),
	     list ('minus, reval (npop!* (npbeta, 1))),
             list ('minus, list ('times, npgam, 
				 list ('plus, nptau, list ('minus, cnpalpha),
				       list ('minus, npbeta)))),
             list ('minus, list ('times, npmu, nptau)),
             list ('times, npsig, npnu),
             list ('times, npeps, cnpnu),
             list ('times, npbeta, list ('plus, npgam, list ('minus, cnpgam),
					 list ('minus, npmu))),
             list ('minus, list ('times, npalpha, cnplam))), 'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

%  if (!*showindices) then tabthenprint (mkmsg list ("computing %[2 2]", nptnsr));
% FI[2,2] from NP 4.2n
  evaltnsr1 (nptnsr, car lex, 
	list ('plus,
	     reval (npop!* (npnu, 2)),
	     list ('minus, reval (npop!* (npmu, 1))),
             list ('minus, list ('plus, list ('times, npmu, npmu),
				 list ('times, nplam, cnplam))),
             list ('minus, list ('times, npmu, list ('plus, npgam, cnpgam))),
             list ('times, cnpnu, nppi),
             list ('minus, list ('times, npnu, list ('plus, nptau,
			     list ('minus, list ('times, 3, npbeta)),
					     list ('minus, cnpalpha))))), 'nil);
  ext!-map (nptnsr1, pop lex1, nptnsr, pop lex, 1 ./ 1, 'nil);  % external link

  if not get (nptnsr, 'tvalue) then 
    tabthenprint ("** this metric is a vacuum solution.");
%   put (nptnsr, 'altmetric, currentmetric);  % save metric environment
   protect!* (nptnsr, 'w);
   protect!* (nptnsr1, 'w);
   put (getmetric (2), 'npricci, nptnsr);	% store name on metric
   cleaner ('npricci);
   return (nptnsr . 1);
end;

put ('npnames, 'simpfn, 'npnames!*);

symbolic procedure npnames!* (u);
% alternate access to the spin coeffs.
begin;
  if mycar u then
     foreach x in pair ('(!k!a!p!p!a !s!i!g!m!a !r!h!o !t!a!u !e!p!s !b!e!t!a 
	!a!l!p!h!a !g!a!m!m!a !p!i !m!u !l!a!m!b!d!a !n!u), 
		igen ('(a!# b!# c!# d!#), get (npspin, 'indices),
	get (npspin, 'symmetry),'nil)) do 
% make references to the generic name.
	put (car x, 'newnam, list(npspin, 'findex . cdr x))
  else 
     foreach x in '(!k!a!p!p!a !s!i!g!m!a !r!h!o !t!a!u !e!p!s !b!e!t!a 
	!a!l!p!h!a !g!a!m!m!a !p!i !m!u !l!a!m!b!d!a !n!u) do 
           remprop (x, 'newnam);
  return t . 1;
end;

global '(petrov!-terms!*);
petrov!-terms!* := 10000000;    % more than this in I^2-27*J^2 and we cheat

put ('petrov, 'simpfn, 'petrov!*);

fluid '(petrov);
fluid '(!*read!-undef!-flag!*);
petrov := 'pet;

% Code based on R.A. D'Inverno and R.A. Russel-Clark, JMP, 12, p1258, 1971
symbolic procedure petrov!* (u);
begin scalar npc, nptest, p0, p1, p2, p3, p4, lex, zero!*, ptype,
	 p03, p04, p13, p22, p11, ii, jj, hh, gg, hell, nterms,
	 flg, store, !*read!-undef!-flag!*, mes;
  !*read!-undef!-flag!* := 't;
  npc := get (getmetric (2), 'npweyl);	% see if its already been made
  if not indexed (npc) then <<
    write "I won't make ", npweyl, " for you, make it yourself and ensure all substitutions";
    return 't ./ 1
  >>;
  p0 := mk!*sq readtnsr (npc, '(0));
  p1 := mk!*sq readtnsr (npc, '(1));
  p2 := mk!*sq readtnsr (npc, '(2));
  p3 := mk!*sq readtnsr (npc, '(3));
  p4 := mk!*sq readtnsr (npc, '(4));
  if u then <<
        write "making substitutions...", !$eol!$;
	p0 := subeval append (u, list p0);
	p1 := subeval append (u, list p1);
	p2 := subeval append (u, list p2);
	p3 := subeval append (u, list p3);
	p4 := subeval append (u, list p4);
  >>;
  zero!* := 0;
  % if p0 = 0, and p4 neq 0, then swap p0,p4, and p1,p3
  if p0 = zero!* and not (p4 = zero!*) then 
  <<
     lex := p4; p4 := p0; p0 := lex;
     lex := p3; p3 := p1; p1 := lex
  >>;
% need some user indication to make fresh (or just have them rem it)
  if not indexed (store := get (getmetric (2), 'petrov)) then
  <<
     store := newnme ('nil, petrov);
     mktnsr!* (store, '(0), 'nil, 'nil, 'petrov, "Petrov algorithm components");
     restrict!* (store, '(0), '(5));
     put (store, 'tvalue, foreach x in igen ('(a!#), get (store, 'restricted),
		'nil, 'nil) collect list x);
     put (store, 'subst, u);  % save the user subs used
     put (getmetric(2), 'petrov, store)
  >>;

  mes := nil;
  if p0 = zero!* and p4 = zero!* then <<
   % this is the easy case, corresponding to table 1 in D'Inverno and Russell-Clark
     if p1 = zero!* then <<
       if p2 = zero!* then
         if p3 = zero!* then ptype := "0"
         else <<
           mes := mkmsg (list ("Please ensure that %% is non-zero.",
				npc, index!-string '(3)));
	   ptype := "III"
         >>
       else
         if p3 = zero!* then ptype := "D"
         else <<
           mes := mkmsg (list ("Please ensure that %% and %% are non-zero.",
			npc, index!-string '(3), npc, index!-string '(2)));
	   ptype := "II"
         >>
     >> else <<    % p1 != 0
       if p2 = zero!* then
         if p3 = zero!* then <<
           mes := mkmsg (list ("Please ensure that %% is non-zero.",
		npc, index!-string '(1)));

	  ptype := "III"
         >> else <<
           mes := mkmsg (list ("Please ensure that %% and %% are non-zero.",
		npc, index!-string '(1), npc, npc, index!-string '(3)));
	   ptype := "I"
         >>
       else    % p2 != 0
         if p3 = zero!* then ptype := "II"
         else begin scalar dd;
           if not (dd := readtnsr (store, '(5))) then
               dd:=  addsq (multsq (9 ./ 1, exptsq (p2,2)), negsq (multsq (16,
			multsq (p1, p3))));
           dd := mk!*sq dd;
           if dd = zero!* then <<
             mes := mkmsg (list ("Please ensure that %%, %% and %% are non-zero.",
		npc, index!-string '(1), npc, index!-string '(2), npc, index!-string '(3)));
	     ptype := "II"
 	   >> else <<
             mes := mkmsg (list ("Please ensure that %%, %%, %% and D are non-zero.",
		npc, index!-string '(1), npc, index!-string '(2), npc, index!-string '(3)));
	     ptype := "I"
	 >>;
         end
     >>;
   goto a;
  >>;

  p04 := mk!*sq simp list ('times, p0, p4);
  p03 := mk!*sq simp list ('times, p0, p3);
  p13 := mk!*sq simp list ('times, p1, p3);
  p22 := mk!*sq simp list ('expt, p2, 2);
  p11 := mk!*sq simp list ('expt, p1, 2);
  if not (ii := readtnsr (store, '(0))) then <<
    write "computing I", !$eol!$;
    writetnsr (store, '(0), ii :=  simp list ('plus, p04, 
	list ('minus, list ('times, 4, p13)),
		list ('times, 3, p22)), 't)
  >>;
  ii := mk!*sq ii;
  if not (jj := readtnsr (store, '(1))) then <<
    write "computing J", !$eol!$;
    jj := writetnsr (store, '(1), simp list ('plus, list ('times, p04, p2), 
	list('minus, list ('times, p03, p3)),
	list ('minus, list ('times, p11, p4)),
      list ('times, 2, p13, p2),
      list ('minus, list ('times, p22, p2))), 't)
  >>;
  jj := mk!*sq jj;
  if not (hell := readtnsr (store, '(2))) then <<
    write "computing I^3-27 J^2", !$eol!$;
    nterms := sizeofexp (atom ii and ii or prepsq cadr ii, 
			atom jj and jj or prepsq cadr jj);
    if nterms < petrov!-terms!* then 
      hell := simp (list ('plus, list ('expt, ii, 3), 
	  list ('minus, list ('times, 27, list ('expt, jj, 2)))))
    else begin scalar lex, lex1;
      write "Cannot compute I^3-27 J^2 directly, it has ",
	   nterms, " terms (max).", !$eol!$;
      % pick a coord to subs a value for, and re-evaluate I and J
  loop:
      lex := '(0 . nil);
      foreach y in 		% find coords that is most used
  % what is the safe way to get the guts of a !*sq ?
	 countvars (cadr ii . cadr jj, coords!*) do
	  if car y > car lex then lex := y;
      if not cdr lex then 
      <<
	  tabthenprint "Sorry - no further subs are possible, do it by hand";
	  ptype := "unknown";
	  return
      >>;
      lex1 := list ('equal, cdr lex, list ('quotient, random (256)+1, 16));   % value to subs for
      prin2!* "Making this coordinate substitution: ";
      maprint (lex1, 0); terpri!* 'nil;
      write "into I ...", !$eol!$;
      ii := subeval list (lex1, ii);   % new !*sq's with coord sub'd
      write "and into J ...", !$eol!$;
      jj := subeval list (lex1, jj);
      write "done.", !$eol!$;
      nterms := sizeofexp (prepsq cadr ii, prepsq cadr jj);
      if nterms < petrov!-terms!* then 
      <<
	  write "Reduced I^3-27 J^2 to ",
		   nterms, " terms, computing...", !$eol!$;
	  writetnsr (store, '(2), hell := simp (list ('plus, list ('expt, ii, 3), 
		  list ('minus, list ('times, 27, list ('expt, jj, 2))))), 't);
	  flg := 't;    % flag indicating a subs was made
	  goto afterloop
      >>;
      goto loop;
  afterloop:    
    end;
    if ptype then goto a;   % error out for unknown type;
  >>;

  hell := mk!*sq hell;
  if not (hell = zero!*) then
   <<
        mes := "Please ensure that I^3-27J^2 is non-zero.";
	ptype := "I";
        goto a
   >>;
   if flg then write "Suggest you rerun petrov() to test another coordinate subs";

   if not (gg := readtnsr (store, '(3))) then <<
     write "computing G", !$eol!$;
     writetnsr (store, '(3), gg := simp list ('plus, list ('times, p0, p03),
		list ('minus,  list ('times, 3, p0, p1, p2)),
		list ('times, 2, p1, p11)), 't)
   >>;
   gg := mk!*sq gg;

   if not (ii = zero!* and jj = zero!*) then
     if gg = zero!* then <<
        mes := "Please ensure that I and J are both non-zero";
	ptype := "D"
     >> else <<
        mes := "Please ensure that I, J and G are all non-zero";
        ptype := "II"
     >>
   else <<
     if not (hh := readtnsr (store, '(4))) then <<
       write "computing H", !$eol!$;
       writetnsr (store, '(4), hh := simp list ('plus, list ('times, p0, p2), 
    	  list ('minus, p11)), 't)
     >>;
     hh := mk!*sq hh;
     if gg = zero!* and hh = zero!* then 
        ptype := "N"
     else <<
        mes := "Please ensure that G and H are non-zero";
        ptype := "III"
     >>
   >>;
a:
  if mes then <<
    write mes,!$eol!$;
    write "If so, then the Petrov type is ", ptype, !$eol!$
  >> else  write "The Petrov type is ", ptype,!$eol!$;
  return ptype ./ 1;
end;


symbolic procedure sizeofexp (rii, rjj);
begin scalar n1, n2, n3, n4;
  if not atom rii and mycar rii eq 'quotient then << n1 := length cadr rii; 
		n2 := length caddr rii>> else << n1 := length rii; n2 :=1>>;
  if not atom rjj and mycar rjj eq 'quotient then << n3 := length cadr rjj; 
		n4 := length caddr rjj>> else << n3 := length rjj; n4 :=1>>;
  % compute number of terms
  return n1*(n1+1)*(n1+2)/6*n4*(n4+1)/2+
  			n2*(n2+1)*(n2+2)/6*n3*(n3+1)/2;
end;

fluid '(counts);

symbolic procedure countvars (exp, vars);
begin scalar counts, i, n, lis;
  counts := mkvect (n := length(vars));
  i := 1;
  while (i <= n) do <<putv(counts, i, 0); i := i + 1>>;
  countvars1 (exp, reverse vars);
  while (i > 1) do <<i := i - 1; push (getv (counts, i), lis)>>;
  return pair (lis, vars);
end;

symbolic procedure countvars1 (exp, vars);
begin scalar lex;
  if lex := memq (exp, vars) then putv (counts, length (lex), 
	getv(counts, length (lex)) + 1)
  else if not atom (exp) then
  <<
    if car exp eq '!*sq then exp := cadr exp;
    countvars1 (car exp, vars); countvars1 (cdr exp, vars)
  >>;
end;

endmodule;
;end;
