(defun count-words-buffer ( )
  "Count the number of words in the current buffer;
print a message in the minibuffer with the result."
  (interactive)
  (save-excursion
    (let ((count 0))
      (goto-char (point-min))
      (while (< (point) (point-max))
	(forward-word 1)
	(setq count (1+ count)))
      (message "buffer contains %d words." count))))

(count-words-buffer)
;; buffer contains 57 words.

(defun goto-percent (pct)
  (interactive "nPercent: ")
  (goto-char (/ (* pct (point-max)) 100)))

(goto-percent 50)

(defun pluralize (word count)
  (if (= count 1)
      word
    (concat word "s")))

(pluralize "goat" 5)   ;; goats
(pluralize "change" 1) ;; change

(defun find-library-file (library)
  "Takes a single argument LIBRARY, being a library file to search for.
Searches for LIBRARY directly (in case relative to current directory,
or absolute) and then searches directories in load-path in order. It
will test LIBRARY with no added extension, then with .el, and finally
with .elc. If a file is found in the search, it is visited. If none
is found, an error is signaled. Note that order of extension searching
is reversed from that of the load function."
  (interactive "sFind library file: ")
  (let ((path (cons "" load-path)) exact match elc test found)
    (while (and (not match) path)
      (setq test (concat (car path) "/" library)
	    match (if (condition-case nil
			  (file-readable-p test)
			(error nil))
		      test)
	    path (cdr path)))
    (setq path (cons "" load-path))
    (or match
	(while (and (not elc) path)
	  (setq test (concat (car path) "/" library ".elc")
		elc (if (condition-case nil
			    (file-readable-p test)
			  (error nil))
			test)
		path (cdr path))))
    (setq path (cons "" load-path))
    (while (and (not match) path)
      (setq test (concat (car path) "/" library ".el")
	    match (if (condition-case nil
			  (file-readable-p test)
			(error nil))
		      test)
	    path (cdr path)))
    (setq found (or match elc))
    (if found
	(progn
	  (find-file found)
	  (and match elc
	       (message "(library file %s exists)" elc)
	       (sit-for 1))
	  (message "Found library file %s" found))
      (error "Library file \"%s\" not found." library))))

(find-library-file "abbrev")
