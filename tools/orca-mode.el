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

(define-generic-mode 'orca-mode
  '("(*)") ;; comments
  '("data" "syn" "lf" "def" "where" "|" "=>" "fn" "\\" ":>" "|-") ;; keywords
  '()
  '("\\.kw$") ;; file extension
  nil ;; (list 'orca-bind-keys) ;; other functions to call
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
