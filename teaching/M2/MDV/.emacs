(setq visible-bell t)
(setq kill-ring-max 3000)
(setq fill-column 110)
(auto-fill-mode -1)
(setq paren-mode 'sexp)

;; colorisation de la syntaxe
 (global-font-lock-mode t)

;; mettre en surligné la zone de selection
 (transient-mark-mode t)

;; modification des couleurs
(set-background-color "ivory")
(set-foreground-color "slateblue")
(set-cursor-color "brown")
(set-mouse-color "orangered")
(set-face-foreground 'bold "black")
(set-face-background 'bold "lightpink")
(set-face-foreground 'bold-italic "red")
(set-face-background 'bold-italic "wheat")
(set-face-foreground 'italic "darkolivegreen")
(set-face-background 'default "ivory")
(set-face-foreground 'default "black")
(set-face-foreground 'modeline "black")
(set-face-background 'modeline "slateblue")
(set-face-foreground 'underline "violet")
(set-face-background 'region "purple")
(set-face-foreground 'region "yellow")

(set-face-foreground font-lock-reference-face     "orange")
(set-face-foreground font-lock-comment-face       "light slate blue")
(set-face-foreground font-lock-string-face        "green3")
(set-face-foreground font-lock-function-name-face "blue1")
(set-face-foreground font-lock-variable-name-face "blue3")
(set-face-foreground font-lock-keyword-face       "orange")

(require 'paren)
(show-paren-mode)
(set-face-background 'show-paren-match-face       "PaleTurquoise1")
(setq show-paren-style 'expression)
(setq blink-matching-paren-dont-ignore-comments t)

;;(define-key global-map ,"M-f" ,'goto-line)

(fset 'insert-double-braces
   [?{ ?} left])


;; quelques redefinitions pratiques
(defmacro dk      (k f) `(define-key global-map            ,k ,f))
(dk      [home]              'beginning-of-line)
(dk      [end]               'end-of-line)  
(dk      [delete]            'delete-char)
(dk      [M-delete]          'kill-word)
(dk      [M-up]           'backward-up-list)
(dk      [M-right]           'forward-sexp)
(dk      [M-left]            'backward-sexp)
(dk      [M-c]            'compile)
(dk      [M-f]            'goto-line)
(dk      [C-x x]            'insert-double-braces)

(global-set-key [C-x x] 'insert-double-braces)
(global-set-key [M-g] 'goto-line)

;(require 'power-macros)
;(power-macros-mode)
;(pm-load)

(load-file "~/soft/src/ProofGeneral/generic/proof-site.el")

(add-hook 'proof-mode-hook '(lambda ()                                 
(define-key proof-mode-map [(control down)] 'proof-assert-next-command-interactive)
; commande suivante (lance le process Coq si necessaire)

(define-key proof-mode-map [(control up)] 'proof-undo-last-successful-command)
;(define-key proof-mode-map [(control up)] 'proof-toolbar-undo)
; undo, revient une commande en arriere

(define-key proof-mode-map [(control right)] 'proof-assert-until-point-interactive)
; lire le script jusqu'au curseur (lance le process Coq si necessaire)

(define-key proof-mode-map [(control left)] 'proof-retract-until-point-interactive)
; undo jusqu'au curseur

(define-key proof-mode-map [(control delete)] 'proof-shell-exit)
; tuer le process Coq, utile car il ne peut y avoir
; qu'un seul process Coq a la fois (1 process par Emacs)

(define-key proof-mode-map [(control insert)] 'proof-interrupt-process)
; Pour interrompre le script en cours, le script s'arrete la ou
; il en etait, cette commande peut compromettre la coherence
; avec la partie read-only du buffer (apparemment c'est rare)

(define-key proof-mode-map [(control home)] 'proof-retract-buffer)
; reset du script

(define-key proof-mode-map [(control end)] 'proof-process-buffer)
; effectuer le script jusqu'a la fin du buffer

(define-key proof-mode-map [(control return)] 'proof-minibuffer-cmd)
; pour taper une commande directement, mais sans qu'elle soit ajoutee
; au script

(define-key proof-mode-map [(meta up)] 'scroll-other-window)
(define-key proof-mode-map [(meta down)] 'scroll-other-window-down)

))

(custom-set-variables
 '(load-home-init-file t t))
(custom-set-faces)
