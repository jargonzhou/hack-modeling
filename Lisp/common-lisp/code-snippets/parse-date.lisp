;;;; 解释日期

(in-package :com.spike.language.cl.snippets)

(defun tokens (str test start)
  (let ((p1 (position-if test str :start start)))
    (if p1
	;; 当前字符满足条件
	(let ((p2 (position-if #'(lambda (c) (not (funcall test c)))
			       str :start p1)))
	  (cons (subseq str p1 p2)
		(if p2
		    ;; 继续串接
		    (tokens str test p2)
		    nil)))
	nil)))

;;; 谓词: 是否是要素字符
(defun constituent (c)
  (and (graphic-char-p c)
       (not (char= c #\ ))))

(tokens "ab12 3cde.f" #'alpha-char-p 0)
(tokens "ab12 3cde.f
gh" #'constituent 0)


(defun parse-date (str)
  (let ((toks (tokens str #'constituent 0)))
    (list (parse-integer (first toks))
	  (parse-month (second toks))
	  (parse-integer (third toks)))))

(defconstant month-names
  #("jan" "feb" "mar" "apr" "may" "jun"
    "jul" "aug" "sep" "oct" "nov" "dec"))

(defun parse-month (str)
  (let ((p (position str month-names
		    :test #'string-equal)))
    (if p
	(+ p 1)
	nil)))

(parse-date "16 Aug 1980")

