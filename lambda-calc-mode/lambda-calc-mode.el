;;; lambda-calc-mode.el --- Major mode for editing lambda calculus (.lamb) files  

;; -*- lexical-binding: t; -*-  
;; Enable lexical scoping (better variable handling in modern Emacs)  

;; Define a customization group for lambda-calc-mode  
(defgroup lambda-calc nil  
  "Customizations for lambda-calc-mode."  
  :group 'languages)  

;; Define a custom face for the lambda symbol (λ)  
(defface lambda-calc-lambda-char  
  '((t (:inherit font-lock-keyword-face :bold t :foreground "purple")))  
  "Face for the lambda symbol (λ).")  

;; Create a syntax table for special character handling  
(defvar lambda-calc-mode-syntax-table  
  (let ((table (make-syntax-table))) ; Create a new empty syntax table  
    (modify-syntax-entry ?\/ ". 12" table) ; Treat "//" as comment start  
    (modify-syntax-entry ?\n ">" table)    ; Newline ends comment  
    table)  
  "Syntax table for `lambda-calc-mode'.")  

;; Define keybindings for the mode  
(defvar lambda-calc-mode-map  
  (let ((map (make-sparse-keymap))) ; Create a new empty keymap  
    ;; Bind "l <tab>" to insert "λ"  
    (define-key map (kbd "l <tab>")  
      (lambda () (interactive) (insert "λ")))  
    map)  
  "Keymap for `lambda-calc-mode'.")  

;; Define syntax highlighting rules  
(defconst lambda-calc-font-lock-keywords  
  '(  
    ("λ" . 'lambda-calc-lambda-char)       ; Highlight λ in custom face  
    ("//.*" . 'font-lock-comment-face)     ; Highlight comments  
    ("\\<\\(TRUE\\|FALSE\\)\\>" . font-lock-constant-face)) ; Highlight macros  
  "Highlighting rules for lambda calculus.")  

;; Define the major mode  
(define-derived-mode lambda-calc-mode fundamental-mode "λ-Calc"  
  "Major mode for editing lambda calculus (.lamb) files."  
  :group 'lambda-calc  
  (setq-local font-lock-defaults '(lambda-calc-font-lock-keywords)) ; Apply highlighting  
  (setq-local comment-start "// ") ; Set comment prefix  
  (setq-local comment-end "")      ; Comments don’t need an end marker  

;; Automatically use this mode for .lamb files  
(add-to-list 'auto-mode-alist '("\\.lamb\\'" . lambda-calc-mode))  

;; Provide the mode for use  
(provide 'lambda-calc-mode)  
