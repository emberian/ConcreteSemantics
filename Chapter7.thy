theory Chapter7
imports "~~/src/HOL/IMP/Small_Step"
begin

text{*
\section*{Chapter 7}

\exercise
Define a function that computes the set of variables that are assigned to
in a command:
*}

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (a ::= e) = {a}" |
"assigned (a;; b) = assigned a \<union> assigned b" |
"assigned (IF a THEN b ELSE c) = assigned b \<union> assigned c" |
"assigned (WHILE a DO b) = assigned b"

text{*
Prove that if some variable is not assigned to in a command,
then that variable is never modified by the command:
*}

lemma "\<lbrakk> (c, s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"
by (induction rule: big_step_induct) auto

text {*
\endexercise

\exercise
Define a recursive function that determines if a command behaves like @{const SKIP}
and prove its correctness:
*}

fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (a ::= e) = False" |
"skip (a;; b) = (skip a \<and> skip b)" |
"skip (IF a THEN b ELSE c) = (skip b \<and> skip c)" |
(* I initially had skip (WHILE a DO b) = skip b, however consider the case where b = SKIP and
   a = Bc True. We would need to show that, \<forall>s t. (SKIP, s) \<Rightarrow> t \<longrightarrow> (WHILE a DO b, s) \<Rightarrow> t,
   however this is not the case since there exists no t that that command reduces to (as it doesn't
   terminate. Since the exercise wants the type signature to be com \<Rightarrow> bool, and I don't feel like
   handling only statically-false cases, I just define it to be false. *)
"skip (WHILE a DO b) = False"

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
proof (induction c)
  case SKIP thus ?case by simp (* trivial *)
next 
  case Assign thus ?case by simp (* contradiction *)
next 
  case (Seq a b)
  hence "a \<sim> SKIP" and "b \<sim> SKIP" by auto
  moreover hence "(a;; b) \<sim> (SKIP;; SKIP)" by blast
  moreover hence "(SKIP;; SKIP) \<sim> SKIP" by auto
  ultimately show ?case by auto
next 
  case (If a b c)
  hence "b \<sim> SKIP \<and> c \<sim> SKIP" by auto
  thus ?case by blast
next
  case While thus ?case by auto (* contradiction *)
qed

text{*
\endexercise

\exercise
Define a recursive function
*}

fun deskip :: "com \<Rightarrow> com" where
"deskip SKIP = SKIP" |
"deskip (a ::= b) = a ::= b" |
"deskip (a;; b) = (if deskip a = SKIP then deskip b else (if deskip b = SKIP then deskip a else deskip a;; deskip b))" |
"deskip (IF a THEN b ELSE c) = IF a THEN deskip b ELSE deskip c" |
"deskip (WHILE a DO b) = WHILE a DO deskip b"

text{*
that eliminates as many @{const SKIP}s as possible from a command. For example:
@{prop[display]"deskip (SKIP;; WHILE b DO (x::=a;; SKIP)) = WHILE b DO x::=a"}
Prove its correctness by induction on @{text c}: *}

lemma "deskip c \<sim> c"
proof (induction c)
  case SKIP show ?case by simp
next
  case Assign show ?case by simp
next
  case (Seq a b)
  hence "a;; b \<sim> deskip a;; deskip b" by auto
  moreover have "deskip (a;; b) \<sim> deskip a;; deskip b" by auto
  ultimately show ?case by auto
next
  case If thus ?case by auto
next
  case While
  thus ?case by (simp add: sim_while_cong)
qed

text{*
Remember lemma @{thm[source]sim_while_cong} for the @{text WHILE} case.
\endexercise

\exercise
A small-step semantics for the evaluation of arithmetic expressions
can be defined like this:
*}

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x, s) \<leadsto> N (s x)" |
"(Plus (N i) (N j), s) \<leadsto> N (i + j)" |
"(a, s) \<leadsto> a' \<Longrightarrow> (Plus a b, s) \<leadsto> Plus a' b" |
"(b, s) \<leadsto> b' \<Longrightarrow> (Plus (N i) b, s) \<leadsto> Plus (N i) b'"

(* your definition/proof here *)

text{*
Complete the definition with two rules for @{const Plus}
that model a left-to-right evaluation strategy:
reduce the first argument with @{text"\<leadsto>"} if possible,
reduce the second argument with @{text"\<leadsto>"} if the first argument is a number.
Prove that each @{text"\<leadsto>"} step preserves the value of the expression:
*}

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep.induct [split_format (complete)])

fix x s
show "aval (V x) s = aval (N (s x)) s" by auto

fix i j s
show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by auto

fix a s a' b
assume 0: "aval a s = aval a' s"
from 0 show "aval (Plus a b) s = aval (Plus a' b) s" by auto

fix b s b' i
assume 0: "aval b s = aval b' s"
from 0 show "aval (Plus (N i) b) s = aval (Plus (N i) b') s" by auto

qed

(* ok, I lied, I love case. some of those hairier proofs would have been pretty impossible to
   read without it. writing out certain steps explicitly can make the structure of the proof
   clear while still leaving the meat to the automation. *)

text{*
Do not use the \isacom{case} idiom but write down explicitly what you assume
and show in each case: \isacom{fix} \dots \isacom{assume} \dots \isacom{show} \dots.
\endexercise

\exercise
Prove or disprove (by giving a counterexample):
*}

lemma "IF And b\<^sub>1 b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 \<sim>
          IF b\<^sub>1 THEN IF b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 ELSE c\<^sub>2" (is "?Small \<sim> ?Big")
proof -
  
  {fix s t
  have lower: "bval (And b\<^sub>1 b\<^sub>2) s = (if bval b\<^sub>1 s then bval b\<^sub>2 s else False)" by auto
  {
    assume ltr: "(?Small, s) \<Rightarrow> t" (is "?P")
    {
      assume b1: "bval b\<^sub>1 s"
      assume b2: "bval b\<^sub>2 s"
      from b1 b2 ltr have fst: "(c\<^sub>1, s) \<Rightarrow> t" by auto
    }
    note fst = this

    {
      assume b1: "bval b\<^sub>1 s"
      assume b3: "\<not>bval b\<^sub>2 s"
      from b1 b3 ltr have snd: "(c\<^sub>2, s) \<Rightarrow> t" by auto
    }
    note snd = this

    {
      assume b4: "\<not>bval b\<^sub>1 s"
      from b4 ltr have thd: "(c\<^sub>2, s) \<Rightarrow> t" by auto
    }
    note thd = this
    
    from fst snd thd lower have "(?Big, s) \<Rightarrow> t" by auto
  }
  note ltr = this
  
  {
  assume rtl: "(?Big, s) \<Rightarrow> t" (is "?P")
    
    {
      assume b1: "bval b\<^sub>1 s"
      assume b2: "bval b\<^sub>2 s"
      from b1 b2 rtl have fst: "(c\<^sub>1, s) \<Rightarrow> t" by auto
    }
    note fst = this
    
    {
      assume b1: "bval b\<^sub>1 s"
      assume b3: "\<not>bval b\<^sub>2 s"
      from b1 b3 rtl have snd: "(c\<^sub>2, s) \<Rightarrow> t" by auto
    }
    note snd = this
    
    {
      assume b4: "\<not>bval b\<^sub>1 s"
      from b4 rtl have thd: "(c\<^sub>2, s) \<Rightarrow> t" by auto
    }
    note thd = this
  
    from fst snd thd lower have "(?Big, s) \<Rightarrow> t" by auto
  }
  note rtl = this
  
  from ltr rtl have "(?Small, s) \<Rightarrow> t = (?Big, s) \<Rightarrow> t" by auto
  }
  from this show ?thesis by auto
qed

(* ... Wow that is ugly. I'm not sure how to improve it, though. I tried using "moreover have"
  unsuccessfully. A next/case shorthand for this sort of thing would be nice. I think part of the
  problem is that it's phrased in terms of = of booleans, which here I decompose into 
  P \<longrightarrow> Q \<and> Q \<longrightarrow> P \<Longrightarrow> P = Q (some of that reasoning is hidden behind auto). Alas,
  sledgehammer finds a metis proof quite quickly. I was hoping writing out the structured proof
  would provide some deeper insight into Isar, but I ended up using really low-level things. *)

(* note: needed to explicitly add quantifiers, since the free variables didn't seem to want to
   unify with the concrete counterexample *)
lemma "\<not> (\<forall>b\<^sub>1 b\<^sub>2 c. WHILE And b\<^sub>1 b\<^sub>2 DO c \<sim> WHILE b\<^sub>1 DO WHILE b\<^sub>2 DO c)" (is "\<not> ?P")
proof
  assume are_sim: ?P
  (* concrete counterexample: the first program terminates while the second does not. 
     if we assume the second *does* terminate because the first does, we can show by rule
     induction that this is a contradiction (no rule can derive that (second, s) \<Rightarrow> t) *)
  have conc: "WHILE And (Bc True) (Bc False) DO SKIP \<sim> WHILE (Bc True) DO WHILE (Bc False) DO SKIP"
    using are_sim by simp
  have is_skip: "(WHILE And (Bc True) (Bc False) DO SKIP, s) \<Rightarrow> s" by auto
  hence "(WHILE (Bc True) DO WHILE (Bc False) DO SKIP, s) \<Rightarrow> s" using conc by simp
  thus False 
  by (induction "(WHILE (Bc True) DO WHILE (Bc False) DO SKIP)" s s rule: big_step_induct, simp)
qed

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b\<^sub>1 b\<^sub>2 = Not (And (Not b\<^sub>1) (Not b\<^sub>2))"


lemma
while_terminates_then_cond_false:
assumes a: "(WHILE b DO c, s) \<Rightarrow> t" (is "(?C, s) \<Rightarrow> t")
shows "\<not> bval b t"
proof -
  (* it seems using "assumes" statements instead of explicit P \<Longrightarrow> Q makes you need to
     name it explicitly if you want to use it. It doesn't become a "this" at the start of the proof
  *)
  from a show ?thesis by (induction ?C s t rule: big_step_induct, auto)
qed

lemma "WHILE Or b\<^sub>1 b\<^sub>2 DO c \<sim>
          WHILE Or b\<^sub>1 b\<^sub>2 DO c;; WHILE b\<^sub>1 DO c" (is "?P \<sim> ?P;; ?Q")
proof -
  have ltr: "\<forall>s t. (?P, s) \<Rightarrow> t \<longrightarrow> (?P;; ?Q, s) \<Rightarrow> t"
  proof -
      {fix s t
      assume terminates: "(?P, s) \<Rightarrow> t"
      hence "\<not> bval (Or b\<^sub>1 b\<^sub>2) t" using while_terminates_then_cond_false by auto
      hence "(?Q, t) \<Rightarrow> t" by (auto simp add: Or_def)
      from this have "(?P;; ?Q, s) \<Rightarrow> t" using terminates by auto
      } thus ?thesis by auto
  qed

  have rtl: "\<forall>s t. (?P;; ?Q, s) \<Rightarrow> t \<longrightarrow> (?P, s) \<Rightarrow> t"
  proof -
    {fix s t
    assume terminates: "(?P;; ?Q, s) \<Rightarrow> t"
    then obtain t1 where seq1: "(?P, s) \<Rightarrow> t1" and seq2: "(?Q, t1) \<Rightarrow> t" by auto
    hence "\<not> bval (Or b\<^sub>1 b\<^sub>2) t1" using while_terminates_then_cond_false terminates by auto
    hence nb1: "\<not> bval b\<^sub>1 t1" by (auto simp add: Or_def)
    hence "t1 = t" using seq2 by auto
    hence "(?P, s) \<Rightarrow> t" using terminates seq1 seq2 nb1 by auto
    } thus ?thesis by auto
  qed

  show ?thesis using ltr rtl by blast
qed
  
text{*
\endexercise

\exercise
Define a new loop construct @{text "DO c WHILE b"} (where @{text c} is
executed once before @{text b} is tested) in terms of the
existing constructs in @{typ com}:
*}

definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
"DO c WHILE b = c ;; WHILE b DO c" 

text{*
Define a translation on commands that replaces all @{term "WHILE b DO c"}
by suitable commands that use @{term "DO c WHILE b"} instead:
*}

fun dewhile :: "com \<Rightarrow> com" where
"dewhile SKIP = SKIP" |
"dewhile (a ::= b) = a ::= b" |
"dewhile (a;; b) = dewhile a;; dewhile b" |
"dewhile (IF a THEN b ELSE c) = IF a THEN dewhile b ELSE dewhile c" |
"dewhile (WHILE a DO b) = IF Not a THEN SKIP ELSE (DO dewhile b WHILE a)"

text{* Prove that your translation preserves the semantics: *}

lemma "dewhile c \<sim> c"
proof (induction c)
  case SKIP thus ?case by simp
  next case Assign thus ?case by simp
  next case Seq thus ?case by auto
  next case If thus ?case by auto
  next
    case (While b c)
    hence "WHILE b DO c \<sim> WHILE b DO dewhile c" using sim_while_cong by simp
    thus ?case using Do_def while_unfold by auto
qed

text{*
\endexercise

\exercise
Let @{text "C :: nat \<Rightarrow> com"} be an infinite sequence of commands and
@{text "S :: nat \<Rightarrow> state"} an infinite sequence of states such that
@{prop"C(0::nat) = c;;d"} and \mbox{@{prop"\<forall>n. (C n, S n) \<rightarrow> (C(Suc n), S(Suc n))"}}.
Then either all @{text"C n"} are of the form \mbox{@{term"c\<^sub>n;;d"}}
and it is always @{text c\<^sub>n} that is reduced or @{text c\<^sub>n} eventually becomes @{const SKIP}.
Prove
*}


lemma assumes "C 0 = c;;d" and "\<forall>n. (C n, S n) \<rightarrow> (C(Suc n), S(Suc n))"
shows "(\<forall>n. \<exists>c\<^sub>1 c\<^sub>2. C n = c\<^sub>1;;d \<and> C(Suc n) = c\<^sub>2;;d \<and> (c\<^sub>1, S n) \<rightarrow> (c\<^sub>2, S(Suc n)))
     \<or> (\<exists>k. C k = SKIP;;d)" (is "(\<forall>i. ?P i) \<or> ?Q")
proof cases
  assume ?Q
  thus ?thesis by simp
next
  assume not: "\<not>?Q"
  {fix i
  have "\<exists>c1 c2. C i = c1;; d \<and> C (Suc i) = c2;; d \<and> (c1, S i) \<rightarrow> (c2, S (Suc i))"
  proof (induction i)
    case 0
    have "C 1 \<noteq> SKIP;; d" using not by simp
    thus ?case using assms by (metis Small_Step.SeqE not prod.sel(1) prod.sel(2))
  next
    case (Suc n)
    (* Relatively straightforward - use the induction hypothesis to chain forward another step
       from original c1 and c2, show that this c3 has the necessary properties. Since c2 \<rightarrow> SKIP
       is not possible, there will always be something in front of the ;; that prevents the ;; from
       reducing away. *)
    then obtain c1 c2 where "C n = c1;; d \<and> C (Suc n) = c2;; d \<and> (c1, S n) \<rightarrow> (c2, S (Suc n))" by auto
    moreover have "C (Suc (Suc n)) \<noteq> SKIP;; d" using not by simp
    moreover obtain c3 where "C (Suc (Suc n)) = c3;; d" using not calculation by (metis Pair_inject Small_Step.SeqE assms(2))
    moreover have "(C (Suc n), S (Suc n)) \<rightarrow> (C (Suc (Suc n)), S (Suc (Suc n)))" using assms by auto
    moreover have "C (Suc n) = c2;; d \<and> C (Suc (Suc n)) = c3 ;; d \<and> (c2, S (Suc n)) \<rightarrow> (c3, S (Suc (Suc n)))" using calculation not by auto
    ultimately show ?case using not by auto
  qed
  }
  thus ?thesis by auto
qed
    
(* your definition/proof here *)

text{*
\endexercise
\bigskip

For the following exercises copy theories
@{theory Com}, @{theory Big_Step} and @{theory Small_Step}
and modify them as required. Those parts of the theories
that do not contribute to the results required in the exercise can be discarded.
If there are multiple proofs of the same result, you may update any one of them.

\begin{exercise}\label{exe:IMP:REPEAT}
Extend IMP with a @{text "REPEAT c UNTIL b"} command by adding the constructor
\begin{alltt}
  Repeat com bexp   ("(REPEAT _/ UNTIL _)"  [0, 61] 61)
\end{alltt}
to datatype @{typ com}.
Adjust the definitions of big-step and small-step semantics,
the proof that the big-step semantics is deterministic and
the equivalence proof between the two semantics.
\end{exercise}

\begin{exercise}\label{exe:IMP:OR}
Extend IMP with a new command @{text "c\<^sub>1 OR c\<^sub>2"} that is a
nondeterministic choice: it may execute either @{text
"c\<^sub>1"} or @{text "c\<^sub>2"}. Add the constructor
\begin{alltt}
  Or com com   ("_ OR/ _" [60, 61] 60)
\end{alltt}
to datatype @{typ com}. Adjust the definitions of big-step
and small-step semantics, prove @{text"(c\<^sub>1 OR c\<^sub>2) \<sim> (c\<^sub>2 OR c\<^sub>1)"}
and update the equivalence proof between the two semantics.
\end{exercise}

\begin{exercise}
Extend IMP with exceptions. Add two constructors @{text THROW} and
@{text "TRY c\<^sub>1 CATCH c\<^sub>2"} to datatype @{typ com}:
\begin{alltt}
  THROW  |  Try com com   ("(TRY _/ CATCH _)"  [0, 61] 61)
\end{alltt}
Command @{text THROW} throws an exception. The only command that can
catch an execption is @{text "TRY c\<^sub>1 CATCH c\<^sub>2"}: if an execption
is thrown by @{text c\<^sub>1}, execution continues with @{text c\<^sub>2},
otherwise @{text c\<^sub>2} is ignored.
Adjust the definitions of big-step and small-step semantics as follows.

The big-step semantics is now of type @{typ "com \<times> state \<Rightarrow> com \<times> state"}.
In a big step @{text "(c,s) \<Rightarrow> (x,t)"}, @{text x} can only be @{term SKIP}
(signalling normal termination) or @{text THROW} (signalling that an exception
was thrown but not caught).

The small-step semantics is of the same type as before. There are two final
configurations now, @{term "(SKIP, t)"} and @{term "(THROW, t)"}.
Exceptions propagate upwards until an enclosing handler is found.
That is, until a configuration @{text "(TRY THROW CATCH c, s)"}
is reached and @{text THROW} can be caught.

Adjust the equivalence proof between the two semantics such that you obtain
@{text "cs \<Rightarrow> (SKIP,t)  \<longleftrightarrow>  cs \<rightarrow>* (SKIP,t)"}
and @{text "cs \<Rightarrow> (THROW,t)  \<longleftrightarrow>  cs \<rightarrow>* (THROW,t)"}.
Also revise the proof of
\noquotes{@{prop [source] "(\<exists>cs'. cs \<Rightarrow> cs')  \<longleftrightarrow>  (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"}}.
\end{exercise}
*}

end

