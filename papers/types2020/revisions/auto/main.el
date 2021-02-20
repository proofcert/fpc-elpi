(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("lipics-v2019" "a4paper" "USenglish" "cleveref" "autoref" "thm-restate")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "../head"
    "preamble"
    "intro"
    "cultures"
    "sec3"
    "pbt"
    "elab"
    "conc"
    "app"
    "lipics-v2019"
    "lipics-v201910")
   (LaTeX-add-bibliographies
    "../l"))
 :latex)

