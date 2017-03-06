;;; orca-mode.el --- Orca major mode

;; Copyright (C) 2017, Francisco Ferreira
;; Copyright (C) 2015-2016, Larry Diehl
;; License: MIT

;; To use this mode add the follwing to your emacs initialization file:
;; (load-file "/path/to/orca-mode.el")
;; (require 'orca-mode)

(require 'generic-x)
(require 'comint)

;; (defun orca-bind-keys ()
;;   (global-set-key (kbd "C-c C-l") 'orca-check-file)
;;   )

(defconst orca-font-lock-symbols-alist
  ;; Not sure about fn → λ, since we could also have \ → λ.
  '(("\\" . ?λ)
    ("|-" . ?⊢)
    (":>" . ?▷)
;;    ("->>"    . ?↠) ;; It is really difficult to distinguish from the other one
    ("->"    . ?→)
    ("=>"    . ?⇒)
    ("\\0"   . ?∅)
    )
  "Alist mapping Orca symbols to chars.
Each element has the form (STRING . CHAR) or (STRING CHAR PREDICATE).
STRING is the symbol.
CHAR is the character with which to represent this symbol.
PREDICATE if present is a function of one argument (the start position
of the symbol) which should return non-nil if this mapping should be disabled
at that position.")

(defun orca-chars ()
  (progn
    (setq prettify-symbols-alist (append prettify-symbols-alist orca-font-lock-symbols-alist))
    (prettify-symbols-mode)))

(define-generic-mode 'orca-mode
  '("(*)") ;; comments
  '("data" "syn" "lf" "def" "where" "|" "=>" "fn" "\\" ":>" "|-") ;; keywords
  '()
  '("\\.kw$") ;; file extension
  (list 'orca-chars) ;; other functions to call
  "A mode for Orca programs." ;; doc string
  )

(defconst *orca* "*Orca*"
  "Buffer used by Orca")


;; (defun orca-check-file ()
;;   "Type check a file using Orca as an inferior mode."
;;   (interactive)
;;   (save-buffer 0)
;;   (when (get-buffer *orca*)
;;     (with-current-buffer *orca*
;;       (when (comint-check-proc *orca*)
;;         (comint-kill-subjob))
;;       (delete-region (point-min) (point-max))
;;       )
;;     )

;;   (apply 'make-comint "Orca" "stack" nil
;;          (list "exec" "dtt" "--" "-t" (buffer-file-name))
;;          )
;;   ;; Turn on compilation mode so that, e.g., 'C-x `' can be used to
;;   ;; jump to the next error.  This depends on compilation mode being
;;   ;; able to recognize the location information in the error messages.
;;   ;; Regexps associated with compilation mode define the location
;;   ;; patterns; one built-in pattern is "<file>:<line>:<column>:".
;;   (with-current-buffer *orca*
;;     (compilation-minor-mode 1))
;;   (display-buffer *orca*)
;;   )


(provide 'orca-mode)
