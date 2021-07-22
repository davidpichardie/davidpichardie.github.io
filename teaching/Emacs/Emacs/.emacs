;; Tuareg mode (pour Caml)

(setq load-path (cons "~pichardy/tuareg" load-path))
(setq auto-mode-alist (cons '("\\.ml\\w?" . tuareg-mode) auto-mode-alist))
(autoload 'tuareg-mode "tuareg" "Major mode for editing Caml code" t)
(autoload 'camldebug "camldebug" "Run the Caml debugger" t)
(if (and (boundp 'window-system) window-system
         (string-match "XEmacs" emacs-version))
    (require 'sym-lock))

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



;; quelques redefinitions pratiques
(defmacro dk      (k f) `(define-key global-map            ,k ,f))
(dk      [home]              'beginning-of-line)
(dk      [end]               'end-of-line)  
(dk      [delete]            'delete-char)
(dk      [M-delete]          'kill-word)
(dk      [M-up]           'backward-up-list)
(dk      [M-right]           'forward-sexp)
(dk      [M-left]            'backward-sexp)
