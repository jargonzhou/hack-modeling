(in-package :cl-user)
(defpackage demo-web.db
  (:use :cl)
  (:import-from :demo-web.config
                :config)
  (:import-from :datafly
                :*connection*)
  (:import-from :cl-dbi
                :connect-cached)
  (:export :connection-settings
           :db
           :with-connection
	   :find-movies-from-db))
(in-package :demo-web.db)

(defun connection-settings (&optional (db :maindb))
  (cdr (assoc db (config :databases))))

(defun db (&optional (db :maindb))
  (apply #'connect-cached (connection-settings db)))

(defmacro with-connection (conn &body body)
  `(let ((*connection* ,conn))
     ,@body))


(defun find-movies-from-db (|id|)
  (with-connection (db)
    (let* ((query (dbi:prepare *connection*
                               "SELECT * FROM Movies WHERE `producerC#` = ?"))
	   (query (dbi:execute query |id|))
	   (result nil))
      (loop for row = (dbi:fetch query)
         while row
         do (push row result))
      result)))
    
