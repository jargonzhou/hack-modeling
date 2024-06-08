;;;; CLOS(Common Lisp对象系统)的示例

(in-package :com.spike.language.cl.snippets)


;;; area with structures and function

;; (defstruct rectangle
;;   height width)

;; (defstruct circle
;;   radius)

;; (defun area (x)
;;   (cond ((rectangle-p x)
;; 	 (* (rectangle-height x) (rectangle-width x)))
;; 	((circle-p x)
;; 	 (* pi (expt (circle-radius x) 2)))))

;; (let ((r (make-rectangle)))
;;   (setf (rectangle-height r) 2
;; 	(rectangle-width r) 3)
;;   (area r))

;;; area with classes and methods
(defclass rectangle ()
  (height width))

(defclass circle ()
  (radius))

(defmethod area ((x rectangle))
  (* (slot-value x 'height) (slot-value x 'width)))

(defmethod area ((x circle))
  (* pi (expt (slot-value x 'radius) 2)))

(let ((r (make-instance 'rectangle)))
  (setf (slot-value r 'height) 2
	(slot-value r 'width) 3)
  (area r))


;;; 初始化传递参数规则: HyperSpec 7.1.4
(defclass q () ((x :initarg a)))
(defclass r (q) ((x :initarg b))
  (:default-initargs a 1 b 2))

(let ((i (make-instance 'r 'a 11 'b 22)))
  (slot-value i 'x))


(defclass colored ()
  (color))

(defclass colored-circle (circle colored)
  ())


;;; classes and instances

(defclass circle ()
  (radius
   center))

(let ((c (make-instance 'circle)))
  (if (slot-boundp c 'radius)
      (format t "~A.~%" (slot-value c 'radius)))
  (setf (slot-value c 'radius) 1)
  (format t "~A..~%" (slot-value c 'radius)))


;;; 槽属性
;; :accessor
(defclass circle ()
  ((radius :accessor circle-radius)
   (center :accessor circle-center)))

(let ((c (make-instance 'circle)))
  (setf (circle-radius c) 1)
  (circle-radius c))

;; :initform, :initarg
(defclass circle ()
  ((radius :accessor circle-raduis
	   :initarg :radius
	   :initform 1)
   (center :accessor circle-center
	   :initarg :center
	   :initform (cons 0 0))))

(let ((c (make-instance 'circle :radius 3)))
  (format t "~A~%" (circle-raduis c))
  (format t "~A~%" (circle-center c)))

;; :allocation :class
;; 共享字段: 被所有实例共享
(defclass tabloid ()
  ((top-story :accessor tabloid-story
	      :allocation :class)))

(let ((daily-blab (make-instance 'tabloid))
      (unsolicited-mail (make-instance 'tabloid)))
  (setf (tabloid-story daily-blab) 'adultery-of-senator)
  (tabloid-story unsolicited-mail))

;; others: :documentation, :type


;;; 超类

(defclass graphic ()
  ((color :accessor graphic-color
	  :initarg :color
	  :initform 'purple)
   (visible :accessor graphic-visible
	    :initarg :visible
	    :initform t)))

(defclass screen-circle (circle graphic)
  ())

(graphic-color (make-instance 'screen-circle))			    

(graphic-color (make-instance 'screen-circle
			      :color 'red
			      :radius 3))

;;; 优先级

(defclass sculpture () (height width depth)
  (:documentation "雕刻品"))
(defclass statue (sculpture) (subject)
  (:documentation "雕像"))
(defclass metalwork () (metal-type)
  (:documentation "金属制品"))
(defclass casting (metalwork) ()
  (:documentation "铸造品"))

;; 类优先级列表: cast-statue, statue, sculpture, casting, metalwork, standard-object, t
(defclass cast-statue (statue casting) ()
  (:documentation "铸造雕像"))


;;; 广义函数

(defgeneric combine (x y)
  (:documentation "组合"))

(defmethod combine (x y)
  (list x y))

(combine 'x 'y)


;; 方法中引用的一些类
(defclass stuff () ((name :accessor name :initarg :name)))
(defclass ice-cream (stuff) ())
(defclass topping (stuff) ())

; 在类上特化
(defmethod combine ((ic ice-cream) (top topping))
  (format nil "~A ice-cream with ~A topping"
	  (name ic)
	  (name top)))

(defmethod combine ((ic ice-cream) x)
  (format nil "~A ice-cream with ~A.."
	  (name ic)
	  x))

(combine (make-instance 'ice-cream :name 'fig)
	 (make-instance 'topping :name 'treacle))

(combine (make-instance 'ice-cream :name 'grape)
	 (make-instance 'topping :name 'marshamallow))

(combine (make-instance 'ice-cream :name 'clam)
	 'reluctance)

; 在类型上特化
(defmethod combine ((x number) (y number))
  (+ x y))

(combine 1 2)

; 在单独对象上特化
(defmethod combine ((x (eql 'power)) (y (eql 'spark)))
  'boom)

(combine 'power 'spark)


;;; 辅助方法: before, after, around

(defclass speaker () ())

; [speaker-primary]
(defmethod speak ((s speaker) string)
  (format t "~A" string))

; I'm hungry
(speak (make-instance 'speaker)
       "I'm hungry")

(defclass intellectual (speaker) ())

; [intellectural-before]
(defmethod speak :before ((i intellectual) string)
  (princ "Perhaps "))

; [intellectural-after]
(defmethod speak :after ((i intellectual) string)
  (princ " in some sense"))

; Perhaps I'm hungry in some sense
(speak (make-instance 'intellectual)
       "I'm hungry")

; [speaker-before]
(defmethod speak :before ((s speaker) string)
  (princ "I think "))

; Perhaps I think I'm hungry in some sense
; 参考变准方法组合
(speak (make-instance 'intellectual)
       "I'm hungry")


(defclass courtier (speaker) ())

; [courtier-around]
(defmethod speak :around ((c courtier) string)
  (format t "Does the King believe that ~A? " string)
  (if (eql (read) 'yes)
      (if (next-method-p) (call-next-method))
      (format t "Indeed, it is a preposterous idea.~%"))
  'bow)

; input yes
; Does the King believe that kings will last? I think kings will last
; [courtier-around] -> [speaker-before] -> [speaker-primary]
(speak (make-instance 'courtier) "kings will last")
; input no
; Does the King believe that the world is round? Indeed, it is a preposterous idea.
; [courtier-around]
(speak (make-instance 'courtier) "the world is round")



;;; 方法组合

(defgeneric price (x)
  (:method-combination +))

(defclass jacket () ())
(defclass trousers () ())
(defclass suit (jacket trousers) ())

(defmethod price + ((jk jacket)) 350)
(defmethod price + ((tr trousers)) 200)

(price (make-instance 'suit))

