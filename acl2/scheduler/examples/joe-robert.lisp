(in-package "ACL2")
(include-book "../top")
; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

; Test 1 ----------------------------------------------------------------------

; Let Robert and Joe be two processes that want to communicate. 
; - Robert sends greetings to Joe.
; - Joe returns the greeting, then sends a goodbye message. 
; - Robert receives the message, also sends a goodbye message, and terminates. 
; - Joe receives the goodbye message and terminates.

#| Robert exectues:
  Joe ! hello_joe,
  receive
    {Joe, hello_robert} ->
      receive {Joe, goodbye_robert} ->
        Joe ! goodbye_joe
        robert_ok
      end
  end

  His pid is 0, and he knows that Joe's pid is 1.
|#
(defconst *robert*
  (make-proc
    :s (make-erl-state :bind '((Joe :pid 1)) :self '(:pid 0))
    :klst
      (list
        (make-erl-k 
          :fuel 10000 
          :kont
            (make-kont-exprs
              :exprs
                '((:binop
                    !
                    (:var Joe)
                    (:tuple (:cons (:call self (:nil))
                                   (:cons (:atom hello_joe) (:nil)))))
                  (:receive
                    (((cases (:tuple (:cons (:var Joe) (:cons (:atom hello_robert) (:nil)))))
                      (guards)
                      (body
                        (:receive
                          (((cases (:tuple (:cons (:var Joe) (:cons (:atom goodbye_robert) (:nil)))))
                            (guards)
                            (body 
                              (:binop
                                !
                                (:var Joe)
                                  (:tuple (:cons (:call self (:nil))
                                                 (:cons (:atom goodbye_joe) (:nil)))))
                              (:atom robert_ok)))))))))))))))

#| Joe exectues:
  receive
    {Robert, hello_joe} ->
      Robert ! hello_robert,
      Robert ! goodbye_robert,
      receive {Robert, goodbye_joe} ->
        joe_ok
      end
  end

  His pid is 1, and he knows that Robert's pid is 0.
|#
(defconst *joe*
  (make-proc
    :s (make-erl-state :bind '((Robert :pid 0)) :self '(:pid 1))
    :klst
      (list
        (make-erl-k 
          :fuel 10000 
          :kont
            (make-kont-expr
              :expr
                '(:receive
                    (((cases (:tuple (:cons (:var Robert) (:cons (:atom hello_joe) (:nil)))))
                      (guards)
                      (body
                        (:binop
                          !
                          (:var Robert)
                          (:tuple (:cons (:call self (:nil)) (:cons (:atom hello_robert) (:nil)))))
                        (:binop
                          !
                          (:var Robert)
                          (:tuple (:cons (:call self (:nil)) (:cons (:atom goodbye_robert) (:nil)))))
                        (:receive
                          (((cases (:tuple (:cons (:var Robert) (:cons (:atom goodbye_joe) (:nil)))))
                            (guards)
                            (body (:atom joe_ok))))))))))))))



(defconst *network* (omap::from-lists '((:pid 0) (:pid 1)) (list *robert* *joe*)))

;; Test with: (erl-runner *network* 20)