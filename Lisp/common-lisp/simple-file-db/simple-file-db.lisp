(in-package :com.spike.language.cl.simple-file-db)

(defun info ()
  (write-line "hello, simple-file-db"))

(defun make-cd (title artist rating ripped)
  (list :title title :artist artist :rating rating :ripped ripped))

; ---------------------------------------------------------------------------
; 全局变量
; ---------------------------------------------------------------------------
(defvar *db* nil)


; ---------------------------------------------------------------------------
; UI
; ---------------------------------------------------------------------------

(defun add-record (cd)
  "添加记录"
  (push cd *db*))

(defun dump-db ()
  "查看记录"
  (dolist (cd *db*)
          (format t "~{~a: ~10t~a~%~}" cd)))

(defun prompt-read (prompt)
  (format *query-io* "~a: " prompt)
  (force-output *query-io*)
  (read-line *query-io*))

(defun prompt-for-cd ()
  (make-cd
   (prompt-read "Title")
   (prompt-read "Artist")
   ;(prompt-read "Rating")
   (or (parse-integer (prompt-read "Rarting") :junk-allowed t) 0)
   (y-or-n-p "Ripped [y/n]")))

(defun add-cds ()
  "交互式添加CD"
  (loop (add-record (prompt-for-cd))
    (if (not (y-or-n-p "Another [y/n]: ")) (return))))

; ---------------------------------------------------------------------------
; 保存和加载文件
; ---------------------------------------------------------------------------

(defun save-db (filename)
  "保存为文件"
  (with-open-file (out filename
                       :direction :output
                       :if-exists :supersede)
    (with-standard-io-syntax
      (print *db* out))))

(defun load-db (filename)
  "从文件加载"
  (with-open-file (in filename)
    (with-standard-io-syntax
      (setf *db* (read in)))))


; ---------------------------------------------------------------------------
; 查找,更新,删除
; ---------------------------------------------------------------------------
; (remove-if-not #'evenp '(1 2 3 4))
(defun select (selector-fn)
  (remove-if-not selector-fn *db*))

(defun artist-selector (artist)
  #'(lambda (cd) (equal (getf cd :artist) artist)))

; (select (artist-selector "Title2"))

(defun where (&key title artist rating (ripped nil ripped-p))
  #'(lambda (cd)
            (and
             (if title (equal (getf cd :title) title))
             (if artist (equal (getf cd :artist) artist))
             (if rating (equal (getf cd :rating) rating))
             (if ripped-p (equal (getf cd :ripped) ripped))))) ; DUPLICATION

(defun update (selector-fn &key title artist rating (ripped nil ripped-p))
  (setf *db*
        (mapcar
         #'(lambda (row)
                   (when (funcall selector-fn row)
                     (if title (setf (getf row :title) title))
                     (if artist (setf (getf row :artist) artist))
                     (if rating (setf (getf row :rating) rating))
                     (if ripped-p (setf (getf row :ripped) ripped))) ; DUPLICATION
                   row) *db*)))

(defun delete-rows (selector-fn)
  (setf *db* (remove-if selector-fn *db*)))

;; 去除冗余的努力: 引入宏

(defun make-comparison-expr (field value)
  (list 'equal (list 'getf 'cd field) value))

(defun make-comparison-exprs (fields)
  (loop while fields
    collecting (make-comparison-expr (pop fields) (pop fields))))

;; where-m宏
; (macroexpand-1 '(where-m :title "Title" :ripped t))
; (select (where-m :title "title2" :ripped nil))
(defmacro where-m (&rest clauses)
  `#'(lambda (cd) (and ,@(make-comparison-exprs clauses))))
