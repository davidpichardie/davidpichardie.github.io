(TeX-add-style-hook "TP5corrige"
 (function
  (lambda ()
    (LaTeX-add-environments
     "definition"
     "proposition"
     "question")
    (TeX-run-style-hooks
     "babel"
     "inputenc"
     "amsmath"
     "theorem"
     "pstcol"
     "graphicx"
     "gastex"
     "color"
     "fancyheadings"
     "latex2e"
     "art12"
     "article"
     "12pt"
     "a4paper"
     "solution"
     "dragons"
     "dragon_inverse"))))

