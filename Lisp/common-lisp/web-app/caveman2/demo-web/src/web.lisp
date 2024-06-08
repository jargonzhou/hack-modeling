(in-package :cl-user)
(defpackage demo-web.web
  (:use :cl
        :caveman2
        :demo-web.config
        :demo-web.view
        :demo-web.db
        :datafly
        :sxql)
  (:export :*web*))
(in-package :demo-web.web)

;; for @route annotation
(syntax:use-syntax :annot)

;;
;; Application

(defclass <web> (<app>) ())
(defvar *web* (make-instance '<web>))
(clear-routing-rules *web*)

;;
;; Routing rules

(defroute "/" ()
  (render #P"index.html"))

(defroute "/user.json" (&key |id|)
  (let ((movies (find-movies-from-db |id|)))
    (render-json (car movies))))

;;
;; Error pages

(defmethod on-exception ((app <web>) (code (eql 404)))
  (declare (ignore app))
  (merge-pathnames #P"_errors/404.html"
                   *template-directory*))
