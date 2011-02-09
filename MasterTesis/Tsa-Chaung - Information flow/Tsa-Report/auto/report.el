(TeX-add-style-hook "report"
 (lambda ()
    (LaTeX-add-bibliographies
     "literature")
    (LaTeX-add-labels
     "Chap:Introduction"
     "chap2:noninterference"
     "chap2:example:multithread"
     "chap3:lattice"
     "chap3:flowarrow"
     "chap4:CSL"
     "fig:types"
     "fig:cst"
     "fig:extract"
     "fig:subtyping"
     "fig:tagup"
     "fig:decl"
     "chap4:flowarrowref:concept"
     "chap4:flowarrowref:typesystem"
     "fig:flowarrowref:typesystem0"
     "fig:flowarrowref:typesystem1"
     "fig:flowarrowref:typesystem2"
     "fig:flowarrowref:certify"
     "fig:flowarrowref:sleql"
     "fig:flowarrowref:lleqs"
     "fig:flowarrowref:guard"
     "fig:deduce"
     "chap4:reference"
     "fig:reference:typesystem"
     "chap4:unification"
     "fig:unif:lt"
     "fig:unif:st"
     "fig:unif:ul"
     "fig:unif:us"
     "fig:unif:ct"
     "fig:unif:ce"
     "chap4:unification:flowarrowref"
     "chap4:pure"
     "chap4:lower")
    (TeX-add-symbols
     '("unify" 1)
     '("res" 2)
     '("typn" 1)
     '("sts" 1)
     '("co" 1)
     '("arrowop" 1)
     "st"
     "guard"
     "sleql"
     "lleqs"
     "tagup"
     "decl"
     "typ"
     "ct")
    (TeX-run-style-hooks
     "semantic"
     "wasysym"
     "amssymb"
     "amsmath"
     "latexsym"
     "stmaryrd"
     "times"
     "latex2e"
     "rep10"
     "declarations")))

