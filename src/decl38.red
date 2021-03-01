% This macro implements the usual list pop function: the first element
% is removed from the list and returned.
% It would be better implemented using prog1()
% My CSL compiler is broken: 1) prog1() doesn't compile, and 2) using pop()
% as the second (or later) arg to a function destroys the previous args.
% It's ok as the first arg. A PSL compiler does it right.
% So for now, using pop() must be done with care.
%(Oh, and this CSL won't compile lambda functions with no args either...)
symbolic macro procedure pop (u);
 list ('prog, '(!*pop!-var!*), 
	list ('setq, '!*pop!-var!*, list ('mycar, cadr u)), 
	list('setq, cadr u, list ('mycdr, cadr u)),
	list ('return, '!*pop!-var!*));

% This macro is like pop() above, except the first element is discarded.
symbolic macro procedure popq (u);
  list ('setq, cadr u, list ('mycdr, cadr u));

% The push() macro adds the first argument as the first element of the
% second argument. (I suppose one could make use of rplacd())
symbolic macro procedure push (u);
  list ('setq, caddr u, list ('cons, cadr u, caddr u));

% Many redten functions bundle up several return values into a list,
% which are then spread over the appropriate local vars. The spread()
% macros do this cleanly for functions returning 2, 3, or 4 values.
symbolic macro procedure spread (u);
  list ('prog,'(!*spread!-var!*), list ('setq, '!*spread!-var!*, cadr u),
	list ('setq, caddr u, list ('car, '!*spread!-var!*)),
	list ('setq, cadddr u, list ('cadr, '!*spread!-var!*)));

symbolic macro procedure spread3 (u);
  list ('prog, '(!*spread!-var!*), list ('setq, '!*spread!-var!*, cadr u),
	list ('setq, caddr u, list ('car, '!*spread!-var!*)),
	list ('setq, cadddr u, list ('cadr, '!*spread!-var!*)),
	list ('setq, cadddr cdr u, list ('caddr, '!*spread!-var!*)));

symbolic macro procedure spread4 (u);
  list ('prog,'(!*spread!-var!*), list ('setq, '!*spread!-var!*, cadr u),
	list ('setq, caddr u, list ('car, '!*spread!-var!*)),
	list ('setq, cadddr u, list ('cadr, '!*spread!-var!*)),
	list ('setq, cadddr cdr u, list ('caddr, '!*spread!-var!*)),
	list ('setq, cadddr cddr u, list ('cadddr, '!*spread!-var!*)));

% These are the Reduce globals and fluids used in Redten.

% these changed between 3.3 and 3.4
fluid '(
	 !*factor
	 !*fort
	 !*nat
	 !*nero
	 orig!*
	 posn!*
	 ymax!*
	 ymin!*
	 ycoord!*
	 !*int
	 !*list
	 promptstring!*
	 )$
global '(
	 date!*
	 output!*
	 program!*
	 promptexp
 	 cursym!*
	 )$

fluid '(
	!*usermode
	!*backtrace
       )$

% These are the Redten globals and fluids used widely.
global '(
        reduce!-version
	!*allerr
	!*evalindex
	!*extendedsum
	!*hide
	!*reversedir
	!*rewrite
	!*showindices
	!*xeval
	!*mkobjsafe
	!*peek
        !*fancydf
	!*newriccistyle
	iops!*
	shift!-iops!*
	dif!-iops!*
	symz!-iops!*
	alphalist!*
	base!-case
	christoffel1
	christoffel2
	conjugateindextypes!*
	currentconnection
	currentmetric
	current!-env!*
	defindextype!*
	einstein
	frmetric
	frmetricseq
	frricci
	frriccisc
	frriemann
	freinstein
	frweyl
	gamma
	geodesic
	generic!-names
	helplist!*	
	indexed!-names
	initlendefindextype!*
	invertextension!*
	killing
	metric
	metricseq
	mkcoords
	nulltet
	npt1
	npt2
	npt3
	npt4
	npspin
	npweyl!_sp
	npweyl
	npricci!_sp
	npricci
	offset!*
	offspringextcase!*
	oldcoords!*
	oldcurrentconnection
	oldcurrentmetric
	oldscanval!*
	parseflag!*
	ricci
	riccisc
	riemann
	saveobj!*
	scanval!*
	screenlines!*
	spchristoffel
	spinmat
	spmetric
%%	stck!*	
	symgen!*
	tabbing!*
        terpricount!*
	tmpnames!*
	upcursor!*
	version
	weyl
       )$

% Many Redten fluids are used only between a few functions and are declared
% only in the vicinity (using fluid and unfluid). They are the ones commented
% out below.

fluid '(	
	!*promptenv
        !*paging
	!*symzexp     % this is a switch
        symzflg!*     % only here so mclear finds out about it
%	aindextype
	backvalue
%	bubsrt!*
        change!-tnsr!-flag!*
%	cmplxflag
	coords!*
%	ex1
	env!-grown!-flag!*
	fast!-writetnsr!-cleanup!-names
%	flg
%	indexout
%	indextype
%%	indexx
%	indx1
	killed!*
%	nindex
%	nindextype
%	notcon!*
 	no!-index!-err!*       % used to control mkrdr() and empty indices
	!*read!-undef!-flag!*  % makes readtnsr return nil or <undefined>
	readflg!*
	symsgnone!*
%	symcflg
%	symm
%%	tnsr
	teneval!*
        verbose!*
       )$
	
$end$
	
