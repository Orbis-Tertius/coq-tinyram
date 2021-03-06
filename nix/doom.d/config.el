(setq doom-font (font-spec :family "monospace" :size 10 :weight 'semi-light)
      doom-variable-pitch-font (font-spec :family "sans" :size 12))
;; There are two ways to load a theme. Both assume the theme is installed and
;; available. You can either set `doom-theme' or manually load a theme with the
;; `load-theme' function. This is the default:
; (setq doom-theme 'doom-manegarm)


(custom-set-variables `(coq-prog-name "coqtop"))

(add-hook `pdf-view-mode-hook `pdf-view-themed-minor-mode)
