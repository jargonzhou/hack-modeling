(in-package :cl-user)
(defpackage demo-web.config
  (:use :cl)
  (:import-from :envy
                :config-env-var
                :defconfig)
  (:export :config
           :*application-root*
           :*static-directory*
           :*template-directory*
           :appenv
           :developmentp
           :productionp))
(in-package :demo-web.config)

(setf (config-env-var) "APP_ENV")

(defparameter *application-root*   (asdf:system-source-directory :demo-web))
(defparameter *static-directory*   (merge-pathnames #P"static/" *application-root*))
(defparameter *template-directory* (merge-pathnames #P"templates/" *application-root*))

(defconfig :common
    `(:databases
      ((:maindb :mysql
		:host "127.0.0.1"
		:port 3306
		:database-name "movies"
		:username "root"
		:password "admin"))))

(defconfig |development|
    '(:databases
      ((:maindb :mysql
	:host "127.0.0.1"
	:port 3306
	:database-name "movies"
	:username "root"
	:passowrd "admin"))))

(defconfig |production|
  '())

(defconfig |test|
  '())

(defun config (&optional key)
  (envy:config #.(package-name *package*) key))

(defun appenv ()
  (print (uiop:getenv (config-env-var #.(package-name *package*))))
  (uiop:getenv (config-env-var #.(package-name *package*))))

(defun developmentp ()
  (string= (appenv) "development"))

(defun productionp ()
  (string= (appenv) "production"))
