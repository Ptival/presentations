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

    [`(: ,t ,T) (hbl-append (paren (hbl-append (draw-expr t) (keyword " : ") (draw-expr T))))]

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

    [`(forall ,x in ,T ,r)
     (hbl-append
      (keyword "∀ ")
      (paren (hbl-append (draw-expr x) (keyword " ∈ ") (draw-expr T)))
      (keyword ", ")
      (draw-expr r))]

    [`(hasType ,e ,T)
     (hbl-append (logic "· ⊢ ") (draw-expr e) (logic " ∈ ") (draw-expr T))]

    [`(par ,e) (hbl-append (paren (draw-expr e)))]

    [`(pipe . ,es)
     (hbl-append (keyword "| ") (apply hbl-append (intersperse (codet " ") (map draw-expr es))))]

    [`(prop-eq ,a ,b)
     (hbl-append (draw-expr a) (logic " = ") (draw-expr b))]

    [`(set . ,es)
     (hbl-append
      (logic "{")
      (apply hbl-append
             (intersperse (logic ", ") (map draw-expr es)))
      (logic "}"))]

    [`dot       (keyword   ".")]
    [`dots      (logic     "...")]
    [`:         (keyword   ":")]
    [`:=        (keyword   "≔")]
    [`Cons      (construct "Cons")]
    [`EmptySet  (logic     "{}")]
    [`Inductive (keyword   "Inductive")]
    [`Nat       (construct "Nat")]
    [`Nil       (construct "Nil")]
    [`One       (construct "1")]
    [`List      (construct "List")]
    [`S         (construct "S")]
    [`space     (codet     "")]
    [`Two       (construct "2")]
    [`Type      (construct "Type")]
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
           (titlet "Let's talk")
           (titlet "about induction"))
          3))

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
    (draw-expr `(forall _l in (app List _T) (app _P _n)))
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

                (rule-nil `_T `_x frame-type frame-nil)

                (rule-cons `_T `_x `_h `_t frame-cons #t)

                )
     )
   )

  (play-n
   (animate-slide
    (para "This gives us a new perspective on inductive types.")
    'next
    (para "Their values can be thought of as either:")
    'next
    (inductive-item-1 #f)
    'next
    (inductive-item-2 #f)
    'next
    (inductive-item-3 #f)
    'next
    (para "I will give you an intuition for all three definitions now.")
    ))

  (play-n
   (animate-slide
    (para (hbl-append (t "This gives us a new perspective on ")
                      (colorize (t "co") coinductive-color)
                      (t"inductive types.")))
    'next
    (para "Their values can be thought of as either:")
    'next
    (inductive-item-1 #t)
    'next
    (inductive-item-2 #t)
    'next
    (inductive-item-3 #t)
    ))

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

(define (rule-nil T x frame-type frame-nil)
  (inference
   (draw-expr `(hasType ,x (app List ,T)))
   (cellophane (draw-expr `(hasType ,T Type)) frame-type)
   (cellophane (draw-expr `(def-eq ,x Nil))   frame-nil)
   ))

(define (rule-cons T x h t frame-cons b)
  (cellophane
   (if b
       (inference
        (draw-expr `(hasType ,x (app List ,T)))
        (cellophane (draw-expr `(hasType ,T Type))            frame-cons)
        (cellophane (draw-expr `(hasType ,h ,T))              frame-cons)
        (cellophane (draw-expr `(hasType ,t (app List ,T)))   frame-cons)
        (cellophane (draw-expr `(def-eq ,x (app Cons ,h ,t))) frame-cons)
        )
       (inference
        (draw-expr `(hasType ,x (app List ,T)))
        (cellophane (draw-expr `(hasType ,T Type))            frame-cons)
        (cellophane (draw-expr `(hasType ,h ,T))              frame-cons)
        (cellophane (draw-expr `(hasType ,t (app List ,T)))   frame-cons)
        ))
       frame-cons
       ))


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
              (rule-nil `_T `_x 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) EmptySet))
              (rule-nil `Nat `_x 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) EmptySet))
              (rule-nil `Nat `Nil 1 1)
              ))

  (slide
   (vc-append 60
              (inductive-item-2 #f)
              (draw-expr `(prop-eq (app List Nat) (set Nil)))
              (rule-nil `Nat `Nil 1 1)
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

(define (introduction-slide)
  (slide (scale (titlet "In(tro)duction") 3)))

(define (show)
  (title-slide)
  (assumptions)
  (lets-talk-about-induction)
  (inductive-types))

(module+ main
  (show))
