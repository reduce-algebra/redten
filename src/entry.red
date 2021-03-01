%redten entry points
symbolic macro procedure mkobj (u); list ('real!-mktnsr, mkquote u);
defautoload (real!-mktnsr, redten);
put('![, 'stat, 'parselsqb);
defautoload (parselsqb, redten, expr, 0);
put ('!d, 'simpfn, 'simpd!*);
defautoload (simpd!*, redten);
