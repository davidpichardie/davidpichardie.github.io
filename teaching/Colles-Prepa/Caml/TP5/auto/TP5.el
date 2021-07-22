(TeX-add-style-hook "TP5"
 (function
  (lambda ()
    (LaTeX-add-environments
     "question")
    (TeX-run-style-hooks
     "gastex"
     "babel"
     "inputenc"
     "amsmath"
     "graphicx"
     "color"
     "fancyheadings"
     "latex2e"
     "art12"
     "article"
     "12pt"
     "a4paper"
     "dragon"))))

