%***************************************************************************
%  FILE = subobj.red
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
module 'subobj;

% which is the principle ref: the multiplier and cnj flag, or the
% end of the subobj prop? Both are being used.

put ('subobj, 'simpfn, 'subobj!*);

symbolic procedure subobj!* (u);
begin scalar mltp, cflg, lex, lex1, readflg!*, tnsr1, tnsr2, indx1, indx2;
  if not checktype (mycar u, '(equal equalparse)) then return 'nil ./ 1;
  u := mycdar u;
  spread4 (getnme (car u, '(nil . t), 'subobj), tnsr1, indx1, mltp, cflg);
  if not mycar indx1 then indx1 := 'nil;     % convert (nil) to nil
  lex1 := cadr u;
  while checktype (lex1, '(minus cnj)) do <<
     if mycar lex1 eq 'minus then mltp := multsq (mltp, -1 ./ 1)
          else if mycar lex1 eq 'cnj then cflg := not cflg;
          lex1 := mycadr lex1
  >>;
  spread4 (getnme (lex1, '(nil . t), 'subobj), tnsr2, indx2, lex, lex1);
  if not mycar indx2 then indx2 := 'nil;     % convert (nil) to nil
  mltp := multsq (mltp, lex or (1 ./ 1));
  cflg := if lex1 then not cflg else cflg;

  % now decide what is wanted based on the indices and objects:
  % tnsr1 eq tnsr2 -> internal mapping
  % both indices fixed  -> external mapping
  % indx1 a complete pattern -> subobj (if tnsr1 already indexed ?)
  % all others are errors

  if tnsr1 eq tnsr2 then
         int!-map (tnsr1, indx1, indx2, mltp, cflg)
  else if fixedindex indx1 and fixedindex indx2 then
    ext!-map (tnsr1, indx1, tnsr2, indx2, mltp, cflg)
  else <<
     subobj!*!* (tnsr1, indx1, tnsr2, indx2, mltp, cflg);
     subobj!-shift!*(mycaar u);
     subobj!-odf!*(mycaar u)
  >>;
  return tnsr1 ./ 1;
end;

symbolic procedure subobj!*!* (tnsr1, indx1, tnsr2, indx2, mltp, cflg);
begin scalar lex, lex1, lex2;
  if not free1 (indx1, iops!*) then 
        merror (mkmsg list ("target % must not have op in index", tnsr2), 't);
  if not indexed (tnsr2) then 
        merror (mkmsg list ("target % must be indexed", tnsr2), 't);
  spread4 (resolve!-subobj (tnsr2, indx2), tnsr2, indx2, lex1, lex2);
  mltp := multsq (mltp, lex1);
  cflg := if lex2 then not cflg else cflg;
  if get (tnsr2, 'generic) then 
        merror (mkmsg list ("cannot link to generic object %", tnsr2), 't);

% indx2 is already symmed
%  lex := syma (indx2, get (tnsr2, 'symmetry), 'nil, 't);
%  indx2 := mycar lex;
%  mltp := multsq (mycadr (lex) ./ 1, mltp);
%  cflg := if mycaddr lex then not cflg else cflg;
  lex := canonindex (indx1);
  if length cdr lex neq length cdr canonindex (indx2) then
        merror (mkmsg list ("subobj indices do not match: %, %", indx1,
         indx2), 't);
  lex1 := sublis (mycdr lex, indx2);
  if not patternindex mycar lex then 
      merror (mkmsg list ("Index % for % is not a complete pattern",
                        index!-string indx1, tnsr1), 't);

  lex2 := sublis (pair (lex1, get (tnsr2, 'indextype)), 
        foreach x in mycar lex collect if fixp x then -1 else x);
  mktnsr!*  (tnsr1, lex2, 
        subobj!-symmetry (indx1, indx2, get (tnsr2, 'symmetry)), 'nil,
        'subobj, mkmsg list ("sub-object of %", tnsr2));
  put (tnsr1, 'subobj, list (tnsr2, mycar lex, sublis (mycdr lex, indx2),
         mltp, cflg));
  put (tnsr1, 'multiplier, mltp);
  if cflg then flag (list tnsr1, 'cnj);
  if verbose!* then write "Linking ", tnsr1, index!-string (foreach x in indx1 
                collect mycar explode x),
                " to ", 
                if onep numr mltp then "" else "-", % only support sign changes
        if cflg then "cnj " else "", 
        tnsr2, index!-string (foreach x in indx2 collect mycar explode x),!$eol!$;
  put (tnsr1, 'offspring, subobj!-offspring (tnsr1));
  return tnsr1;
end;

symbolic procedure int!-map (tnsr1, indx1, indx2, mltp, cflg);
begin scalar lex, lex1;
  lex := canonindex (indx1);
  if not (length cdr lex eq length cdr canonindex indx2) then
        merror (mkmsg list ("invalid mapping %% -> %%", 
        tnsr1, index!-string indx1, tnsr1, index!-string indx2), 't);
  indx1 := car lex;
  indx2 := sublis (cdr lex, indx2);
  % these are the indices based on the pattern part of the first index
  lex1 := igen (foreach x in cdr lex collect cdr x,
        indexlim (foreach x in pair (indx1, get (tnsr1, 'indextype)) join
        if fixp car x then 'nil else list cdr x), 'nil, 'nil);
  % lex is a list of pairs of indices (and multipliers/cflgs)
  lex := foreach x in lex1 collect <<
    setlis (alphalist!*, x);
     (sym (foreach x in indx1 collect eval x, get (tnsr1, 'symmetry)) .
          sym (foreach x in indx2 collect eval x, get (tnsr1, 'symmetry)))
  >>;
  setlis (alphalist!*, alphalist!*);
  lex1 := get (tnsr1, 'internal!-mapping);
  foreach x in lex do begin scalar lex2, lex3;
    if orderindex (caar x, cadr x) then lex2 := cdr (x) . car (x)
    else lex2 := x;  % get things in order
    if lex3 := assoc (caar lex2, lex1) then lex1 := delete (lex3, lex1);
% should re-target the map based on where this was pointing.
    if lex3 := assoc (cadr lex2, lex1) then 
	lex2 := car lex2 . cdr lex3;
    if not zerop car cdar lex2 then 
       lex1 := list (caar lex2, cadr lex2, numr mltp * car cdar lex2 
		* car cddr lex2,
  (lambda v; if v eq -1 then 't else 'nil)(
	(cflg and -1 or 1) * (mycadr cdar lex2 and -1 or 1) *
		 (mycadr cddr lex2 and -1 or 1))) . lex1;
   end;
  put (tnsr1, 'internal!-mapping, lex1);
  return tnsr1;
end;

symbolic procedure ext!-map (tnsr1, indx1, tnsr2, indx2, mltp, cflg);
begin scalar lex, lex1;
  if lex := assoc (indx1, lex1 := get (tnsr1, 'external!-mapping))
	then lex1 := delete (lex, lex1);
% if tnsr2 is nil, then just delete the link
  if tnsr2 then put (tnsr1, 'external!-mapping, 
        list (indx1, tnsr2, indx2, mltp, cflg) . lex1);
end;


symbolic procedure subobj!-symmetry (indx1, indx2, symm);
begin scalar lex, lex1;
   lex := foreach x in symm collect
	mycar x . foreach y in mycdr x collect
		foreach z in y collect  mynth (indx2, z);
   lex:= foreach x in lex collect 
	    (mycar x . 
			foreach y in mycdr x join 
        % if the pointer list is reduced, the sym goes away.
        % i.e. ((1)(1 2)(3 4)) with mapping (a b) -> (a 1 b 2) does not
	% become ((1)(1)(3))
	(lambda a; not memq ('nil, a) and list a or 'nil)(
                  foreach z in y collect
			look (indx1, z, 1)));
   lex:= sort!-sym foreach z in  lex
	        join if not mycddr z then 
% have to convert a hermitian with 1 pointer to a normal sym with conjugation
		if mycar z eq 'h then 
		    list ('(1 . t) . foreach xx in mycadr z collect list xx)
		else nil else list z;
   lex := errorset (list ('chksym, mkquote lex, mkquote 'nil), 'nil, 'nil);
% well, CSL does not follow the Standard LIsp report in the return value from
% an erroset if error() has been called. It's supposed to be the err number.
   if not lex then <<
	merror ("internal error in subobj!-symmetry", nil);
        return 'nil >>
   else return car lex;
end;


symbolic procedure resolve!-subobj (tnsr, indexx);
begin scalar lex, lex1, dindx, mltp, cflg;
  % generics can refer to subobjs, but subobjs cannot refer to generics.
  tnsr := resolvegeneric (tnsr);
  if (lex1 := mycar fderiv indexx) then <<
	dindx := mypnth (indexx, lex1);
	indexx := head (indexx, lex1-1)
  >>;
  mltp := get (tnsr, 'multiplier);
  cflg := flagp (tnsr, 'cnj);
  if (lex := get (tnsr, 'subobj)) then <<   % a subobjd object
    tnsr := mycar lex;
    if not indexed (tnsr) then merror ("target is gone!",'t);
    mltp := multsq (mltp, get (tnsr, 'multiplier));
    cflg := if get (tnsr, 'cnj) then not cflg else cflg;   
    indexx := sublis (pair (head (alphalist!*, length(indexx)), indexx), mycaddr lex);
  >>;
  return list (tnsr, append (indexx, dindx), mltp, cflg);
end;

symbolic procedure all!-shifts (indextype);
begin scalar lex;
  if not indextype then return 'nil;    % scalar subobj
  if not mycdr indextype then return list (list mycar indextype,
	 list (-1* mycar indextype));
  lex := all!-shifts (mycdr indextype);
  return append (for each x in lex collect mycar indextype . x,
  for each x in lex collect (-1*mycar indextype) . x);
end;

symbolic procedure subobj!-offspring (tnsr);
begin scalar lis, lex, lex1, lex2, lex3, lex4, parent,
	target, mapin, mapout, indextype, targetindextype, mltp, cflg;
  lex := get (tnsr, 'subobj);
  target := mycar lex;
  parent := get (target, 'parent) or target;
  mapin := mycadr lex;    % input index 
  mapout := mycaddr lex;  % output index for use with target (already symmed)
  mltp := mycadddr lex;
  cflg := mycar mycddddr lex;
  indextype := get (tnsr, 'indextype);
  targetindextype := get (target, 'indextype);
  foreach x in  all!-shifts (indextype) do <<
    %create a shifted index for the subobj, based on the indextype
    lex := genshft (mapin, indextype, x);
    % now map that to the target object
    lex1 := sublis (pair (mapin, lex), mapout);
    % now sym both to get canonical forms 
    lex := syma (lex, get (tnsr, 'symmetry), 'nil, indextype);
    lex1 := syma (lex1, get (target, 'symmetry), 'nil, targetindextype);
    % combine all the multipliers and cflgs:
    mltp := multsq (mltp, (mycadr lex * mycadr lex1) ./ 1);
    cflg := if mycaddr lex then not cflg else cflg;
    cflg := if mycaddr lex1 then not cflg else cflg;  % this is stupid...
    lex := shftc (car lex, indextype);  
    lex1 := shftc (car lex1, targetindextype);
    % we don't use x to gen the names, 'cause of the syms
    push (list (mkshftnme (tnsr, cadr lex, indextype), car lex,
	        mkshftnme (parent, cadr lex1, get (parent, 'indextype)),
		 car lex1, mltp, cflg), lis)
  >>;
  return lis;
end;

symbolic procedure subobj!-shift!* (tnsrp);
 foreach x in get (tnsrp, 'offspring) do 
   if indexed (mycaddr x) and not indexed (mycar x) then 
     <<
        apply ('subobj!*!*, x);
        put (tnsrp, 'shift, append (append (list ('nil, tnsrp), % add offspring to the
        mycddr (get (tnsrp, 'shift))), list (mycar x))); % parent list
        put (mycar x, 'parent, tnsrp);
        put (mycar x, 'printname, get (tnsrp, 'printname));
        remprop (mycar x, 'offspring);  % no shifts of shifts!!
        flag (list (mycar x), 'nodir);
        subobj!-odf!* (mycar x)
     >>;

symbolic procedure subobj!-odf();
   foreach tnsr in indexed!-names do if get (tnsr, 'subobj)
	then subobj!-odf!* (tnsr);

symbolic procedure subobj!-shift();
   foreach tnsr in indexed!-names do if get (tnsr, 'subobj)
	then subobj!-shift!* (tnsr);

symbolic procedure subobj!-odf!* (tnsrp);
begin scalar i, cur, prv, nxt, lex1, target, mapin, mapout, lex, obj;
  lex := get (tnsrp, 'subobj);
  target := mycar lex;
  mapin := mycadr lex;
  mapout := mycaddr lex;
  i := 1;
  cur := tnsrp;
  prv := 'nil; % name of prev object, nxt is name of next object
%write target, " ", cur, " ", prv,!$eol!$;
  obj := target;
  while (lex := mycaddr get (obj, 'odf)) do <<
%write "target = ",target, " ", cur, " ", prv, " ",obj, " ",lex,!$eol!$;
    nxt := makeextname (tnsrp, '!_!D!F, i);
%write "nxt = ", nxt,!$eol!$;
      % next df is not made, must make it and reset 'odf prop
    mapin := append (mapin, list mynth (alphalist!*, length (mapout)+1));
    mapout := append (mapout, list mynth (alphalist!*, length (mapout)+1));
    if not indexed (nxt) then <<
       subobj!*!*(nxt, mapin, lex, mapout, get (tnsrp, 'multiplier),
		flagp (tnsrp, 'cnj));
       subobj!-shift!* (nxt);
%write "linking ", nxt, " to ", lex,!$eol!$;
       put (cur, 'odf, list (i-1, prv, nxt));
       put (nxt, 'odf, list (i, cur, 'nil));
       put (nxt, 'printname, get (tnsrp,'printname));
       flag (list nxt, 'nodir);
    >>;
    obj := lex; i := i + 1; prv := cur; cur := nxt
  >>;
  return nxt;
end;

endmodule;
;end;
