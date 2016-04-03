theory Chapter9_1
imports "~~/src/HOL/IMP/Types"
begin

text{*
\section*{Chapter 9}

\exercise
Reformulate the inductive predicates \ @{prop"\<Gamma> \<turnstile> a : \<tau>"},
\ @{prop"\<Gamma> \<turnstile> (b::bexp)"} \
and \ \mbox{@{prop"\<Gamma> \<turnstile> (c::com)"}} \ as three recursive functions
*}

fun atype :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty option" where
  "atype \<Gamma> (Ic i) = Some Ity"
| "atype \<Gamma> (Rc i) = Some Rty"
| "atype \<Gamma> (V x) = Some (\<Gamma> x)"
| "atype \<Gamma> (Plus a\<^sub>1 a\<^sub>2) = (if (atype \<Gamma> a\<^sub>1) = (atype \<Gamma> a\<^sub>2) then atype \<Gamma> a\<^sub>1 else None)"

fun bok :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" where
  "bok \<Gamma> (Bc v) = True"
| "bok \<Gamma> (Not b) = bok \<Gamma> b"
| "bok \<Gamma> (And b\<^sub>1 b\<^sub>2) = (bok \<Gamma> b\<^sub>1 \<and> bok \<Gamma> b\<^sub>2)"
| "bok \<Gamma> (Less a\<^sub>1 a\<^sub>2) = (if (atype \<Gamma> a\<^sub>1) = (atype \<Gamma> a\<^sub>2) then (\<exists>a. atype \<Gamma> a\<^sub>1 = Some a) else False)"

fun cok :: "tyenv \<Rightarrow> com \<Rightarrow> bool" where
  "cok \<Gamma> SKIP = True"
| "cok \<Gamma> (x ::= a) = (Some (\<Gamma> x) = atype \<Gamma> a)"
| "cok \<Gamma> (c\<^sub>1;; c\<^sub>2) = (cok \<Gamma> c\<^sub>1 \<and> cok \<Gamma> c\<^sub>2)"
| "cok \<Gamma> (IF b THEN t ELSE e) = (bok \<Gamma> b \<and> cok \<Gamma> t \<and> cok \<Gamma> e)"
| "cok \<Gamma> (WHILE b DO c) = (bok \<Gamma> b \<and> cok \<Gamma> c)"

text{* and prove *}

lemma atyping_atype: "(\<Gamma> \<turnstile> a : \<tau>) = (atype \<Gamma> a = Some \<tau>)"
by (induction a; auto)

lemma btyping_bok: "(\<Gamma> \<turnstile> b) = bok \<Gamma> b"
by (induction b; auto simp add: atyping_atype)

lemma ctyping_cok: "(\<Gamma> \<turnstile> c) = cok \<Gamma> c"
by (induction c; auto simp add: atyping_atype btyping_bok)

text{*
\endexercise

\exercise
Modify the evaluation and typing of @{typ aexp} by allowing @{typ int}s to be coerced
to @{typ real}s with the predefined coercion function
\noquotes{@{term[source] "int_to_real :: int \<Rightarrow> real"}} where necessary.
Now every @{typ aexp} has a value. Define an evaluation function:
*}

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (Ic i) s = (Iv i)"
| "aval (Rc r) s = (Rv r)"
| "aval (V x) s = s x" 
| "aval (Plus a\<^sub>1 a\<^sub>2) s = 
    (case (aval a\<^sub>1 s, aval a\<^sub>2 s) of
      (Iv i\<^sub>1, Iv i\<^sub>2) \<Rightarrow> Iv (i\<^sub>1 + i\<^sub>2)
    | (Rv r\<^sub>1, Rv r\<^sub>2) \<Rightarrow> Rv (r\<^sub>1 + r\<^sub>2)
    | (Rv r, Iv i) \<Rightarrow> Rv (r + i)
    | (Iv i, Rv r) \<Rightarrow> Rv (i + r))"

text{*
Similarly, every @{typ aexp} has a type.
Define a function that computes the type of an @{typ aexp}
*}

fun atyp :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty" where
  "atyp \<Gamma> (Ic i) = Ity"
| "atyp \<Gamma> (Rc r) = Rty"
| "atyp \<Gamma> (V x) = \<Gamma> x"
| "atyp \<Gamma> (Plus a\<^sub>1 a\<^sub>2) = (case (atyp \<Gamma> a\<^sub>1, atyp \<Gamma> a\<^sub>2) of
    (Ity, Ity) \<Rightarrow> Ity
  | (Rty, Rty) \<Rightarrow> Rty
  | (Rty, Ity) \<Rightarrow> Rty
  | (Ity, Rty) \<Rightarrow> Rty)"

text{* and prove that it computes the correct type: *}

lemma
atyp_plus:
fixes \<Gamma> s a1 a2
assumes "atyp \<Gamma> a1 = type (aval a1 s)"
    and "atyp \<Gamma> a2 = type (aval a2 s)"
    and "\<forall>x. type (s x) = \<Gamma> x"
shows "(case type (aval a1 s) of Ity \<Rightarrow> case type (aval a2 s) of Ity \<Rightarrow> Ity | Rty \<Rightarrow> Rty
                  | Rty \<Rightarrow> case type (aval a2 s) of Ity \<Rightarrow> Rty | _ \<Rightarrow> Rty) =
                 type (case aval a1 s of Iv i\<^sub>1 \<Rightarrow> case aval a2 s of Iv i\<^sub>2 \<Rightarrow> Iv (i\<^sub>1 + i\<^sub>2) | Rv r \<Rightarrow> Rv (real_of_int i\<^sub>1 + r)
                       | Rv r\<^sub>1 \<Rightarrow> case aval a2 s of Iv i \<Rightarrow> Rv (r\<^sub>1 + real_of_int i) | Rv r\<^sub>2 \<Rightarrow> Rv (r\<^sub>1 + r\<^sub>2))"
by (smt ty.exhaust ty.simps(3) ty.simps(4) type_eq_Ity type_eq_Rty val.simps(5) val.simps(6))

lemma  "\<Gamma> \<turnstile> s \<Longrightarrow>  atyp \<Gamma> a = type (aval a s)"
by (induction a; auto simp add: styping_def atyp_plus)

text{*
Note that Isabelle inserts the coercion @{typ real} automatically.
For example, if you write @{term "Rv(i+r)"} where @{text"i::  int"} and
@{text "r :: real"} then it becomes @{term "Rv(real i + x)"}.
\endexercise
\bigskip

For the following two exercises copy theory @{theory Types} and modify it as required.

\begin{exercise}
Add a @{text REPEAT} loop (see Exercise~\ref{exe:IMP:REPEAT}) to the typed version of IMP
and update the type soundness proof.
\end{exercise}

\begin{exercise}
Modify the typed version of IMP as follows. Values are now either integers or booleans.
Thus variables can have boolean values too. Merge the two expressions types
@{typ aexp} and @{typ bexp} into one new type @{text exp} of expressions
that has the constructors of both types (of course without real constants).
Combine @{const taval} and @{const tbval} into one evaluation predicate
@{text "eval :: exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"}. Similarly combine the two typing predicates
into one: @{text "\<Gamma> \<turnstile> e : \<tau>"} where @{text "e :: exp"} and the IMP-type @{text \<tau>} can
be one of @{text Ity} or @{text Bty}. 
Adjust the small-step semantics and the type soundness proof.
\end{exercise}
*}

end

