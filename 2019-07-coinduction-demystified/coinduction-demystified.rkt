#lang racket

(require racket/draw)
(require slideshow)
(require slideshow/play)

(current-main-font "Bree Serif")
(define current-math-style (make-parameter "GFS Didot"))
(define current-code-style (make-parameter "Iosevka SS05"))
(current-font-size 30)
(define current-math-size (make-parameter 1.0))

(current-titlet
 (lambda (s)
   (colorize (text s (cons 'bold (current-main-font)) 40)
             (current-title-color))))

(define (to-subscript char)
  (match char
    [#\0 #\₀]
    [#\1 #\₁]
    [#\2 #\₂]
    [#\3 #\₃]
    [#\4 #\₄]
    [#\5 #\₅]
    [#\6 #\₆]
    [#\7 #\₇]
    [#\8 #\₈]
    [#\9 #\₉]
    [other other]))

(define (digit? c)
  (if (member c '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
      #t
      #f))

(define (with-subscript str)
  (list->string
   (reverse
    (let loop ((cs (reverse (string->list str))))
      (cond
        ((null? cs) '())
        ((digit? (car cs))
         (cons (to-subscript (car cs)) (loop (cdr cs))))
        (else cs))))))

(define (codet txt)
  (text txt
        (current-code-style)
        (current-font-size)))

(define (math-text str)
  (text str (current-math-style)))
; (floor (* (current-font-size) (current-math-size)))))

(define (meta e)
  (parameterize ((current-code-style (cons 'italic (current-code-style))))
    (codet e)))

(define (emph txt)
  (text txt
        (cons 'italic (current-main-font))
        (current-font-size)))

(define (strong txt)
  (text txt
        (cons 'bold (current-main-font))
        (current-font-size)))

(define (my-text str)
  (text str))

(define (my-name x)
  (define name (symbol->string x))
  (if (and (> (string-length name) 0)
           (eqv? (string-ref name 0) #\_))
      (meta (with-subscript (substring name 1)))
      (my-text (with-subscript name))))

(define (premise-space)
  (pict-width (codet "    ")))

(define (coinference conclusion . premises)
  (define above (apply hbl-append
                       (premise-space)
                       premises))
  (vc-append
   (* (pict-width (codet " ")) 0.5)
   above
   (linewidth 4 (hline (max (pict-width above) (pict-width conclusion)) 2))
   (linewidth 4 (hline (max (pict-width above) (pict-width conclusion)) 2))
   conclusion))

(define (inference conclusion . premises)
  (define above (apply hbl-append
                       (premise-space)
                       premises))
  (vc-append
   (* (pict-width (codet " ")) 0.5)
   above
   (linewidth 4 (hline (max (pict-width above) (pict-width conclusion)) 2))
   conclusion))

(define code-color      "black")
(define construct-color (make-color 203 41 123))
(define keyword-color   (make-color 0 118 186))
(define logic-color     (make-color 128 128 128))
(define inductive-color   "darkgreen")
(define coinductive-color "red")

(define (code t)
  (colorize (codet t) code-color))
(define (construct t)
  (colorize (codet t) construct-color))
(define (keyword t)
  (colorize (codet t) keyword-color))
(define (logic t)
  (colorize (codet t) logic-color))
(define (inductive t)
  (colorize (emph t) inductive-color))
(define (coinductive t)
  (colorize (emph t) coinductive-color))

(define (intersperse x xs)
  (match xs
    ['() '()]
    [(list y) (list y)]
    [(cons y more)
     (cons y (cons x (intersperse x more)))]))

(define (paren e)
  (hbl-append (keyword "(") e (keyword ")")))

(define (draw-expr e)
  (match e

    [`(: ,t ,T)
     (hbl-append (paren (hbl-append (draw-expr t) (keyword " : ") (draw-expr T))))]

    [`(+ ,a ,b)
     (hbl-append (hbl-append (draw-expr a) (construct " + ") (draw-expr b)))]

    [`(-> . ,es)
     (hbl-append
      (apply hbl-append
             (intersperse (keyword " -> ") (map draw-expr es))))]

    [`(app . ,es)
     (hbl-append
      (apply hbl-append
             (intersperse (codet " ") (map draw-expr es))))]

    [`(def-eq ,a ,b)
     (hbl-append (draw-expr a) (logic " ≡ ") (draw-expr b))]

    [`(def-neq ,a ,b)
     (hbl-append (draw-expr a) (logic " ≢ ") (draw-expr b))]

    [`(forall ,x in ,T ,r)
     (hbl-append
      (keyword "∀ ")
      (paren (hbl-append (draw-expr x) (logic " ") (draw-expr `in) (logic " ") (draw-expr T)))
      (keyword ", ")
      (draw-expr r))]

    [`(hasType ,e ,T)
     (hbl-append (logic "· ⊢ ") (draw-expr e) (logic " ") (draw-expr `in) (logic " ") (draw-expr T))]

    [`(par ,e) (hbl-append (paren (draw-expr e)))]

    [`(pipe . ,es)
     (hbl-append (keyword "| ") (apply hbl-append (intersperse (codet " ") (map draw-expr es))))]

    [`(prop-eq ,a ,b)
     (hbl-append (draw-expr a) (logic " = ") (draw-expr b))]

    [`(prop-neq ,a ,b)
     (hbl-append (draw-expr a) (logic " ≠ ") (draw-expr b))]

    [`(set . ,es)
     (hbl-append
      (logic "{")
      (apply hbl-append
             (intersperse (logic ", ") (map draw-expr es)))
      (logic "}"))]

    [`(sim-eq ,a ,b)
     (hbl-append (draw-expr a) (logic " ≈ ") (draw-expr b))]

    [`comma     (logic     ",")]
    [`dot       (keyword   ".")]
    [`dots      (logic     "...")]
    [`:         (keyword   ":")]
    [`:=        (keyword   "≔")]
    [`comap     (construct "comap")]
    [`CoCons    (construct "CoCons")]
    [`CoList    (construct "CoList")]
    [`CoNat     (construct "CoNat")]
    [`CoNil     (construct "CoNil")]
    [`CoSucc    (construct "CoSucc")]
    [`CoZero    (construct "CoZero")]
    [`Cons      (construct "Cons")]
    [`EmptySet  (logic     "{}")]
    [`Forall    (logic     "∀")]
    [`implies   (logic     "=>")]
    [`in        (logic     "∈")]
    [`Inductive (keyword   "Inductive")]
    [`Nat       (construct "Nat")]
    [`Nil       (construct "Nil")]
    [`One       (construct "1")]
    [`List      (construct "List")]
    [`Plus      (construct "+")]
    [`S         (construct "S")]
    [`space     (codet     "")]
    [`st        (logic     "|")]
    [`Two       (construct "2")]
    [`Type      (construct "Type")]
    [`Union     (logic     "∪")]
    [`Zero      (construct "0")]

    [(? symbol? x) (my-name x)]

    [other (t (format "didn't understand `~v'" other))]
    ))

(define (test-slide)
  (slide (draw-expr '(rule 0 1))))

(define (title-slide)
  (slide
   (scale (vc-append
           (titlet "Coinduction")
           (titlet "demystified"))
          3)
   (scale (titlet "Valentin Robert")
          1.5)
   (scale (titlet "Galois, Inc") 1.5)))

(define (lets-talk-about-induction)

  (slide
   (scale (vc-append
           (t "Let's talk")
           (hbl-append (t "about ") (inductive "induction"))
          ) 3))

  (play-n
   (animate-slide
    (para "In discrete mathematics, you may have learned about natural number induction, while trying to prove:")
    'next
    (draw-expr `(forall _n in Nat (app _P _n)))
    'next
    (para "and with it, a proof method along the lines of:")
    'next
    (item "Prove " (draw-expr `(app _P Zero)))
    'next
    (item "Prove that for any number "
          (draw-expr `_n)
          ",")
    'next
    (para (codet "     ")
          (draw-expr `(app _P _n))
          "   implies   "
          (draw-expr `(app _P (par (app S _n)))))))

  (play-n
   (animate-slide
    (para "Then, you may have learned about lists in a programming class, and tried to prove some property:")
    'next
    (draw-expr `(forall _l in (app List _T) (app _P _l)))
    'next
    (para "and learned to prove it by induction:")
    'next
    (item "Prove " (draw-expr `(app _P Nil)))
    'next
    (item "Prove that for any head "
          (draw-expr `_h)
          ", and for any tail "
          (draw-expr `_t)
          ",")
    'next
    (para (codet "     ")
          (draw-expr `(app _P _t))
          "   implies   "
          (draw-expr `(app _P (par (app Cons _h _t))))
          )))

   )

(define (inductive-item-1 dual)
  (item #:bullet (t "1.")
        "all values that have "
        (if dual (coinductive "finite or infinite ") (inductive "finite "))
        "proofs using those rules"))

(define (inductive-item-2 dual)
  (item #:bullet (t "2.")
         "the "
         (if dual (coinductive "largest ") (inductive "smallest "))
         "set closed under those rules"))

(define (inductive-item-3 dual)
  (item #:bullet (t "3.")
        "the "
        (if dual (coinductive "greatest ") (inductive "least "))
        "fixed point of the underlying endofunctor"))

(define (inductive-types)

  (slide
   (vc-append
    (scale (t "Why is this") 4)
    (scale (t "sane?") 4)))

  (play-n
   (lambda (a)
     (vc-append 60
                (scale (t "Let's put on our proof theory hats! ") 2)
                (scale (rotate (hbl-append (codet "(-:") (cellophane (logic "⊢") a)) (/ pi 2)) 5))
     )
   )

  (play-n
   (lambda (frame-type frame-nil frame-cons)
     (vc-append 60

                (vl-append
                 (hbl-append
                  (draw-expr `(app Inductive List)) (codet " ")
                  (cellophane (keyword "(")                     frame-type)
                  (draw-expr `_T) (codet " ")
                  (cellophane (draw-expr `(app : Type))         frame-type)
                  (cellophane (keyword ")")                     frame-type)
                  (codet " ") (draw-expr `:=)
                  )
                 (cellophane (draw-expr `(pipe Nil space : List _T))  frame-nil)
                 (cellophane (draw-expr `(pipe Cons : (-> (: _h _T) (: _t (app List _T)) (app List _T)))) frame-cons)
                 (cellophane (draw-expr `dot)                   frame-cons)
                 )

                (rule-nil `_T `_x 1 frame-type frame-nil)

                (rule-cons `_T `_x `_h `_t frame-cons #t)

                )
     )
   )

  (play-n
   (animate-slide
    (para (hbl-append (t "This gives us three perspective on ") (inductive "inductive") (t " types.")))
    'next
    (para (hbl-append
           (t "Given a set of rules, to be read ")
           (colorize (t "forward") inductive-color)
           (t ",")))
    'next
    (para "their values can be thought of as either:")
    'next
    (inductive-item-1 #f)
    'next
    (inductive-item-2 #f)
    'next
    (inductive-item-3 #f)
    'next
    (para "I will give you an intuition for all three definitions now.")
    ))

  (inductive-1)
  (inductive-2)
  (inductive-3)

  )

(define (proof-by-induction)

  (play-n
   (lambda (a b c)
     (vc-append
      60
      (para (hbl-append (t "The ") (inductive "induction")
                        (t " proof method can therefore be abstracted as such:")))

      (vc-append
       (cellophane
        (para (hbl-append
               (t "In order to prove ")
               (draw-expr `(app Forall _x comma (par (app _x in _T)) implies (par (app _x in _P))))))
        a)
        (cellophane
         (para (hbl-append (t "by ") (inductive "induction") (t " on ")
               (draw-expr `_T)
               (t ",")
               ))
        b)
        (cellophane
         (para (hbl-append
                (t "it suffices to prove that ")
                (draw-expr `_P)
                (t " is closed under ")
                (draw-expr `_T)
                (t "'s rules!")
                ))
         c)
       ))))

  (slide
   (rule-nil  `Nat `_x 1 1 1)
   (rule-cons `Nat `_x `_h `_t 1 1)
   )

  (slide
   (rule-nil-generalized  (lambda (v) `(hasType ,v _P)) `Nat `_x 1 1 1)
   (rule-cons-generalized (lambda (v) `(hasType ,v _P)) `Nat `_x `_h `_t 1 1)
   )

  (play-n
   (lambda (a b)
     (vc-append
      50
      (para (strong "Proof-theoretic argument"))
      (para "The structure of the term guides the structure of a proof!")

      (cellophane
       (inference
        (draw-expr `(hasType (app Cons Zero Nil) (app List Nat)))
        (inference
         (draw-expr `(hasType Nat Type))
         )
        (inference
         (draw-expr `(hasType Zero Nat))
         (inference (draw-expr `(hasType Nat Type)))
         )
        (inference
         (draw-expr `(hasType Nil (app List Nat)))
         (inference (draw-expr `(hasType Nat Type)))
         )
        )
       a)

      (cellophane
       (inference
        (draw-expr `(hasType (app Cons Zero Nil) _P))
        (inference
         (draw-expr `(hasType Nat Type))
         )
        (inference
         (draw-expr `(hasType Zero Nat))
         (inference (draw-expr `(hasType Nat Type)))
         )
        (inference
         (draw-expr `(hasType Nil _P))
         (inference (draw-expr `(hasType Nat Type)))
         )
        )
       b)

    )))

  (slide (vc-append
          (para (strong "Set-theoretic argument"))
          (para (hbl-append
                 (t "Because ") (draw-expr `_T) (t " is the ") (inductive "smallest ")
                 (t " set closed under its rules, ")))
          (para (hbl-append (draw-expr `(app _T space)) (logic "⊆")
                            (draw-expr `(app space _P))
                            (t " and therefore ")
                            (draw-expr `(app _T space)) (logic "=")
                            (draw-expr `(app space _P))
                            ))
          ))


  )

(define (coinductive-types)

  (slide
   (scale (vc-append
           (t "Let's now")
           (hbl-append (t "consider ") (coinductive "coinduction"))
          ) 3))

  (slide
    (para (my-quote "Coinductive types model infinite structures unfolded on demand, like politicians' excuses: for each attack, there is a defence but no likelihood of resolution."))
    (para "- Conor McBride"))

  (play-n
   (animate-slide
    (para (hbl-append (t "Let's think about ")
                      (coinductive "coinductive")
                      (t " types in the dual way.")))
    'next
    (para (hbl-append
           (t "Given a set of rules, to be read ")
           (colorize (t "backward") coinductive-color)
           (t ",")))
    'next
    (para "their values can be thought of as either:")
    'next
    (inductive-item-1 #t)
    'next
    (inductive-item-2 #t)
    'next
    (inductive-item-3 #t)
    ))

  (slide
   (hbl-append
    100
    (coinference
     (draw-expr `(hasType _x CoNat))
     (draw-expr `(def-eq _x  CoZero))
     )
    (coinference
     (draw-expr `(hasType _x CoNat))
     (draw-expr `(hasType _n CoNat))
     (draw-expr `(def-eq _x  (app CoSucc _n)))
     )
    )
   #:title "Read backward!?")

  (slide
   (vc-append
    100
    (coinference
     (draw-expr `(hasType _x (app CoList _T)))
     (draw-expr `(hasType _T Type))
     (draw-expr `(def-eq _x  CoNil))
     )
    (coinference
     (draw-expr `(hasType _x (app CoList _T)))
     (draw-expr `(hasType _T Type))
     (draw-expr `(hasType _h _T))
     (draw-expr `(hasType _t (app CoList _T)))
     (draw-expr `(def-eq _x  (app CoCons _h _t)))
     )
    )
   #:title "Coinductive lists")

  (slide
   (vc-append
    100
    (cellophane (coinference
     (draw-expr `(hasType _x (app CoList _T)))
     (draw-expr `(hasType _T Type))
     (draw-expr `(def-eq _x  CoNil))
     ) 0)
    (coinference
     (draw-expr `(hasType _x (app CoList _T)))
     (draw-expr `(hasType _T Type))
     (draw-expr `(hasType _h _T))
     (draw-expr `(hasType _t (app CoList _T)))
     (draw-expr `(def-eq _x  (app CoCons _h _t)))
     )
    )
   #:title "Coinductive streams")

  )

(define (proof-by-coinduction)

  (play-n
   (lambda (a b c d)
     (vc-append
      60
      (para (hbl-append (t "The ") (coinductive "coinduction")
                        (t " proof method can therefore be abstracted as such:")))

      (vc-append
       (cellophane
        (para (hbl-append
               (t "In order to prove ")
               (draw-expr `(app Forall _x comma (par (app _x in _P)) implies (par (app _x in _T))))))
        a)
        (cellophane
         (para (hbl-append (t "by ") (coinductive "coinduction") (t " on ")
               (draw-expr `_T)
               (t ",")
               ))
        b)
       (cellophane
         (para (hbl-append
                (t "it suffices to prove that ")
                (draw-expr `_P)
                (t " is closed under ")
                (draw-expr `_T)
                (t "'s rules!")
                ))
         c)
      (cellophane
         (para (hbl-append
                (t "(again, read ")
                (coinductive " backward")
                (t ")")
                ))
         d)
      ))))

  )

(define (strengthening)

  (play-n
   (lambda (a b c)
     (vl-append
      60
      (vl-append
       (para
        (hbl-append
         (t "When doing a proof by ") (inductive "induction") (t ","))
        )
       (para
        (hbl-append
         (t "you might have had to strengthen your ") (inductive "inductive") (t " hypothesis."))
        )
       )
      (vl-append
       20
       (cellophane (draw-expr `(app Forall _x comma (par (app _x in _T)) implies (par (app _x in _P)))) a)
       (cellophane (para
                    (hbl-append (draw-expr `_P)
                                (t " was not closed under the ")
                                (inductive "constructors")
                                (t " of ")
                                (draw-expr `_T))
                                (t ".")
                    )
                   b)
       (cellophane (para "Intuitively, your property was undershooting the type.") c)
       )
      )
     )
   #:title "Strengthening")

  (play-n
   (lambda (a b c)
     (vl-append
      60
      (vl-append
       (para
        (hbl-append
         (t "When doing a proof by ") (coinductive "coinduction") (t ","))
        )
       (para
        (hbl-append
         (t "you might have had to strengthen your ") (coinductive "coinductive") (t " hypothesis."))
        )
       )
      (vl-append
       20
       (cellophane
        (draw-expr `(app Forall _x comma (par (app _x in _P)) implies (par (app _x in _T))))
        a)
       (cellophane (para
                    (hbl-append (draw-expr `_P)
                                (t " was not closed under the ")
                                (coinductive "destructors")
                                (t " of ")
                                (draw-expr `_T))
                                (t ".")
                    )
                   b)
       (cellophane (para "Intuitively, your property was overshooting the type.") c)
       )
      )
     )
   #:title "Strengthening")

  )

(define (inductive-1)

  (play-n
   (lambda (a b c d e)
     (vc-append 60
                (inductive-item-1 #f)

                (inference
                 (draw-expr `(hasType (app Cons Zero Nil) (app List Nat)))
                 (cellophane
                  (inference
                   (draw-expr `(hasType Nat Type))
                   )
                  a)
                 (cellophane
                  (inference
                   (draw-expr `(hasType Zero Nat))
                   (cellophane (inference (draw-expr `(hasType Nat Type))) c)
                   )
                  b)
                 (cellophane
                  (inference
                   (draw-expr `(hasType Nil (app List Nat)))
                   (cellophane (inference (draw-expr `(hasType Nat Type))) e)
                   )
                  d)
                 )

                ))))

(define (rule-nil-generalized P T x frame frame-type frame-nil)
  (cellophane (inference
               (draw-expr (P x))
               (cellophane (draw-expr `(hasType ,T Type)) frame-type)
               (cellophane (draw-expr `(def-eq ,x Nil))   frame-nil)
               ) frame))

(define (rule-nil T x a b c)
  (rule-nil-generalized (lambda (v) `(hasType ,v (app List ,T))) T x a b c))

(define (rule-cons-generalized P T x h t frame-cons b)
  (cellophane
   (if b
       (inference
        (draw-expr (P x))
        (cellophane (draw-expr `(hasType ,T Type))            frame-cons)
        (cellophane (draw-expr `(hasType ,h ,T))              frame-cons)
        (cellophane (draw-expr (P t)) frame-cons)
        (cellophane (draw-expr `(def-eq ,x (app Cons ,h ,t))) frame-cons)
        )
       (inference
        (draw-expr `(hasType ,x (app List ,T)))
        (cellophane (draw-expr `(hasType ,T Type))            frame-cons)
        (cellophane (draw-expr `(hasType ,h ,T))              frame-cons)
        (cellophane (draw-expr (P t)) frame-cons)
        ))
       frame-cons
       ))

(define (rule-cons T x a b c d)
  (rule-cons-generalized (lambda (v) `(hasType ,v (app List ,T))) T x a b c d))

(define (inductive-2)

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (para "Let's try to compute "
                    (draw-expr `(app List Nat))
                    " starting with "
                    (draw-expr `EmptySet)
                    ", assuming "
                    (draw-expr `(hasType Nat Type))
                    " and "
                    (draw-expr `(prop-eq Nat (set Zero One Two dots)))
                    )))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) EmptySet))
              (rule-nil `_T `_x 1 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) EmptySet))
              (rule-nil `Nat `_x 1 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) EmptySet))
              (rule-nil `Nat `Nil 1 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil)))
              (rule-nil `Nat `Nil 1 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil)))
              (rule-cons `_T `(app Cons _h _t) `_h `_t 1 #f)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil)))
              (rule-cons `Nat `(app Cons _h _t) `_h `_t 1 #f)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil)))
              (rule-cons `Nat `(app Cons Zero _t) `Zero `_t 1 #f)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil)))
              (rule-cons `Nat `(app Cons Zero Nil) `Zero `Nil 1 #f)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil (app Cons Zero Nil))))
              (rule-cons `Nat `(app Cons Zero Nil) `Zero `Nil 1 #f)
              ))

  (play-n
   (animate-slide
    (inductive-item-2 #f)
    (para (draw-expr `(app List Nat)) (logic " = { ") (draw-expr `Nil))
    'next
    (para (logic "           , ") (draw-expr `(app Cons Zero Nil)))
    'next
    (para (logic "           , ") (draw-expr `(app Cons One Nil)))
    'next
    (para (logic "           , ") (draw-expr `dots))
    'next
    (para (logic "           , ") (draw-expr `(app Cons Zero (par (app Cons Zero Nil)))))
    'next
    (para (logic "           , ") (draw-expr `(app Cons One (par (app Cons Zero Nil)))))
    'next
    (para (logic "           , ") (draw-expr `dots))
    (para (logic "           } "))
    )
   )

  (play-n
   (animate-slide
    (inductive-item-2 #f)
    (para "Now that's a pretty big " (inductive "smallest ") "set...")
    'next
    (para "We will shortly see in what sense it could be larger!")))

  )

(define (inductive-3)

  (play-n
   (lambda (a b c d)
     (vc-append 60
                (inductive-item-3 #f)
                (vc-append

                 (para (draw-expr
                        `(prop-eq
                          (app _F _S) space))
                       (cellophane
                        (draw-expr
                         `(app _S Union
                               (set
                                (app _x st (def-eq _x Nil)
                                ))))
                        a))

                 (para (codet "        ")
                       (cellophane
                        (hbl-append
                         (draw-expr `Union)
                         (logic " {")
                         (draw-expr `(app _x st _h in _T))
                         )
                        b))

                 (para (codet "             ")
                       (cellophane
                        (hbl-append
                         (draw-expr `(app comma _t in List _T))
                         )
                        c))

                 (para (codet "             ")
                       (cellophane
                        (hbl-append
                         (draw-expr `(app comma (def-eq _x (app Cons _h _t))))
                         )
                        d))

                 (para (codet "             ")
                       (cellophane
                        (logic "}")
                        d))

                 ))))
   )

(define (assumptions)
  (play-n
   (animate-slide
    (hbl-append
           (t "This talk assumes a bit of familiarity with ")
           (emph "data type declarations")
           (t "."))
    'next
    (hbl-append
           (t "Familiarity with ")
           (codet "GADT")
           (t "s will help, but is not mandatory!"))
    'next
    (hbl-append
     (t "There will also be ")
     (emph "inference rules")
     (t ".")))
  #:title "Assumptions about the audience"))

(define (category-theory)
  (play-n
   (animate-slide
    (para "Finally, because this is a Galois talk:")
    'next
    (para "There is yet another, categorical, interpretation of ")
    (para
     (hbl-append
      (inductive "inductive") (t " and ") (coinductive "coinductive") (t " types.")
      )
     )
   )
   )

  (define shape-ta (codet " T A "))
  (define shape-a  (codet " A "))
  (define shape-algebra   (hc-append 80 shape-ta shape-a))
  (define shape-coalgebra (hc-append 80 shape-a shape-ta))

  (define (algebra)
    (pin-arrow-line 16 shape-algebra shape-ta rc-find shape-a lc-find #:line-width 3))

  (define (coalgebra)
    (pin-arrow-line 16 shape-coalgebra shape-a rc-find shape-ta lc-find #:line-width 3))

  (play-n
   (lambda (a b c)
     (vc-append 60
                (para (hbl-append (inductive "Inductive") (t " types are ")
                                  (inductive "initial") (t " algebras:")))
      (algebra)
      (cellophane (para "of functors like:") a)
      (para
       (hbl-append 240
        (vl-append 40
         (cellophane (codet "T X = 1 + X") b)
         (cellophane (codet "T X = 1 + T × X") c)
         )
        (vr-append 40
         (cellophane (t "(natural numbers)") b)
         (cellophane (hbl-append (t "(lists of ") (codet "T") (t "s)")) c)
         )
        )
       )
      )
     )
   )

  (play-n
   (lambda (a b c)
     (vc-append 60
                (para (hbl-append (coinductive "Coinductive") (t " types are ")
                                  (coinductive "final co") (t "algebras:")))
      (coalgebra)
      (cellophane (para "of functors like:") a)
      (para
       (hbl-append 100
        (vl-append 40
         (cellophane (codet "T X = 1 + X") b)
         (cellophane (codet "T X = 1 + T × X") c)
         )
        (vr-append 40
         (cellophane (t "(predecessor function)") b)
         (cellophane (hbl-append (t "(possibly-finite streams of ") (codet "T") (t "s)")) c)
         )
        )
       )
      )
     )
   )

  (play-n
   (animate-slide
    (hbl-append 100 (algebra) (coalgebra))
    'next
    (item "Gives a great intuition for the constructor / destructor roles")
    'next
    (item "The duality story is very crisp")
    'next
    (item "Justifies case analysis by the existence of a homomorphism")
    'next
    (item (t "Justifies ") (inductive "induction") (t " and ")
           (coinductive "coinduction") (t " by the uniqueness of said homomorphism"))
    )
   #:title "Great things about the categorical intuition")

  )

(define (my-quote txt)
  (string-append "“" txt "”"))

(define (why)
  (play-n
   (animate-slide
    (para "When I first tried to learn about coinductive types,")
    (para "I found many sentences I did not comprehend:")
    'next
    (item (my-quote "like inductive types, but the greatest fixed point"))
    'next
    (item (my-quote "like inductive types, but read the rules backward"))
    'next
    (item (t "and the classic: ")
          (my-quote "just the dual!"))
    'next
    (para "Additionally, I was utterly confused by coinduction proof principles.")
    'next
    (para "I hope I can make it feel less inscrutable!")
    )
  #:title "Why this talk?"))

(define (equality)

  (slide
   (scale (vc-append
    (t "The lack of power")
    (t "of equality")
    ) 3
   ))

  (play-n
   (lambda (a b c d e f g h i)
     (vc-append
      (para (hbl-append
             (logic "≡ ")
             (t "stands for \"definitional equality\".")))
      (para "It is the smallest congruence that typically includes:")
      (cellophane (item "α: safe renaming of bound variables") a)
      (cellophane (item "β: reduction of applied λ-terms") b)
      (cellophane (item "δ: unfolding of definitions") c)
      (cellophane (item "ζ: reduction of let-bindings") d)
      (cellophane (item "η: f ≡ λ x . f x") e)
      (cellophane (item "ι: reduction of:") f)
      (cellophane (subitem "pattern-matching over known constructs") g)
      (cellophane (subitem "fixpoints over known producers") h)
      (cellophane (subitem "cofixpoints under known consumers") i)
      )
     )
   )

  (play-n
   (animate-slide
    (para "Sadly, this does not capture everything we consider equal! For instance:")
    (draw-expr `(def-neq (+ One _n) (+ _n One)))
    'next
    (para "Solution: propositional equality")
    'next
    (inference
     (draw-expr `(prop-eq _x _x))
     (draw-expr `(app _T in Type))
     (draw-expr `(app _x in _T))
     )
    'next
    (para "Huh!?")
    )
   )

  (play-n
   (lambda (x y z xx yy zz aa bb)

     (vc-append

      60

      (vc-append
       (para "Let us prove:")
       (draw-expr `(forall _n in Nat (prop-eq (+ One _n) (+ _n One))))
       (para (hbl-append (t "by ") (inductive "induction") (t " on ") (draw-expr `Nat))))

      (cellophane
       (inference
        (draw-expr `(prop-eq (+ One Zero) (+ Zero One)))
        (cellophane
         (inference
          (draw-expr `(prop-eq One One))
          (cellophane
           (inference
            (draw-expr `(def-eq One One))
            )
           z))
         y))
       x)

      (cellophane
       (inference
        (draw-expr `(app (prop-eq (+ One _n) (+ _n One))
                         implies
                         (prop-eq (+ One (app S _n)) (+ (app S _n) One))))
        (cellophane
         (inference
          (draw-expr `(app (prop-eq (+ One _n) (+ _n One))
                           implies
                           (prop-eq (app S (par (app S _n))) (app S (par (+ _n One))))))
          (cellophane
           (inference
            (draw-expr `(app (prop-eq (+ One _n) (+ _n One))
                             implies
                             (prop-eq (app S (par (app S _n))) (app S (par (+ One _n))))))
            (cellophane
             (inference
              (draw-expr `(app (prop-eq (+ One _n) (+ _n One))
                               implies
                               (prop-eq (app S (par (app S _n))) (app S (par (app S _n))))))
              (cellophane
               (inference
                (draw-expr `(app (prop-eq (+ One _n) (+ _n One))
                                 implies
                                 (def-eq (app S (par (app S _n))) (app S (par (app S _n)))))))
                bb))
              aa))
           zz))
         yy))
       xx)
      )

     ))

  (play-n
   (animate-slide
   (para "Co-fixpoints are not judgmentally equal either! :-(")
   (draw-expr `(def-neq (app comap  (par (app Plus One)) _zeroes) _ones))
   (draw-expr `(prop-neq (app comap (par (app Plus One)) _zeroes) _ones))
   'next
   (para "Solutions")
   'next
   (item "Build an " (inductive "inductive") "argument for finite observations")
   'next
   (item "Build a " (coinductive "coinductive") "argument for infinite observations")
   )
   #:title "More values, more problems!"
   )

  (slide
   (coinference
    (draw-expr `(sim-eq (app CoCons _h1 _t1) (app CoCons _h2 _t2)))
    (draw-expr `(def-eq _h1 _h2))
    (draw-expr `(sim-eq _t1 _t2))
    )
   #:title "Stream \"equality\""
   )

  )

(define (bisimulation)

  (play-n
   (lambda (a b)
   (vl-append
    60

    (vl-append
     (para "In practice, the coinduction principle I presented earlier is rarely what we are interested in.")
     (para (hbl-append (t "Many proofs on ") (coinductive "coinductive") (t " data types are instead relational.")))
     )

    (cellophane (vl-append
     (para
      (hbl-append
       (coinductive "Bisimulation")
       (t " techniques demonstrate how some binary relations"))
      )
     (para
      (hbl-append
       (t "are closed under the ")
       (coinductive "destructors")
       (t " of a type.")
      )
     )
     ) a)

    (cellophane (vl-append
     (para
      (hbl-append
       (t "There is a dual proof technique,")
       (inductive " congruence")
       (t ",")
      ))
     (para
      (hbl-append
       (t "capturing binary relations closed under the ")
       (inductive "constructors")
       (t " of a type.")
      )
     )
     ) b)

    ))))

(define (reading)

  (slide
   (scale
    (vl-append
     (para "Jacobs, B. and Rutten, J., 1997.")
     (para "A tutorial on (co) algebras and (co) induction.")
     (para (emph "Bulletin-European Association for Theoretical Computer Science, 62, pp.222-259."))
     )
    0.75)
   #:title "Learn more!")

  )

(define (show)
  (title-slide)
  (assumptions)
  (why)
  (lets-talk-about-induction)
  (inductive-types)
  (proof-by-induction)
  (coinductive-types)
  (proof-by-coinduction)
  (strengthening)
  (equality)
  (bisimulation)
  (category-theory)
  (reading)
  )

(module+ main
  (show))
