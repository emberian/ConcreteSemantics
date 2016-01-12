(* Author: Gerwin Klein, Tobias Nipkow *)

theory Big_Step imports Com begin

subsection "Big-Step Semantics of Commands"

text {*
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first parameter is a tuple,
so the syntax becomes @{text "(c,s) \<Rightarrow> s'"}.
*}

text_raw{*\snip{BigStepdef}{0}{1}{% *}
inductive
  big_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> (SKIP, s)" |
Assign: "(x ::= a,s) \<Rightarrow> (SKIP, s(x := aval a s))" |
Seq1: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> (SKIP, s\<^sub>2);  (c\<^sub>2,s\<^sub>2) \<Rightarrow>  s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
Seq2: "(c1, s1) \<Rightarrow> (THROW, s2) \<Longrightarrow> (c1;; c2, s1) \<Rightarrow> (THROW, s2)" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> (SKIP, s)" |
WhileTrue1:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> (SKIP, s\<^sub>2);  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
WhileTrue2: "\<lbrakk>bval b s1; (c, s1) \<Rightarrow> (THROW, s2)\<rbrakk> \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> (THROW, s2)" |
Throw: "(THROW, s) \<Rightarrow> (THROW, s)" |
TryOk: "(c, s) \<Rightarrow> (SKIP, t) \<Longrightarrow> (TRY c CATCH c2, s) \<Rightarrow> (SKIP, t)" |
TryBad: "\<lbrakk>(c, s) \<Rightarrow> (THROW, t); (c2, t) \<Rightarrow> ct\<rbrakk> \<Longrightarrow> (TRY c CATCH c2, s) \<Rightarrow> ct"
text_raw{*}%endsnip*}

text_raw{*\snip{BigStepEx}{1}{2}{% *}
schematic_lemma ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply(rule Seq1)
apply(rule Assign)
apply simp
apply(rule Assign)
done
text_raw{*}%endsnip*}

thm ex[simplified]

text{* We want to execute the big-step rules: *}

code_pred big_step .

text{* For inductive definitions we need command
       \texttt{values} instead of \texttt{value}. *}

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

text{* We need to translate the result state into a list
to display it. *}

values "{map t [''x''] |c t. (SKIP, <''x'' := 42>) \<Rightarrow> (c, t)}"

values "{map t [''x''] |c t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> (c, t)}"

values "{map t [''x'',''y''] |c t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> (c, t)}"

text{* Proof automation: *}

text {* The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules. *}
declare big_step.intros [intro]

text{* The standard induction rule 
@{thm [display] big_step.induct [no_vars]} *}

thm big_step.induct

text{*
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the @{text c}, @{text s},
and @{text s'} that we are likely to encounter. Splitting
the tuple parameter fixes this:
*}
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text {*
@{thm [display] big_step_induct [no_vars]}
*}


subsection "Rule inversion"

text{* What can we deduce from @{prop "(SKIP,s) \<Rightarrow> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it: *}

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE

text{* This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands: *}

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
text{* Only [elim]: [elim!] would not terminate. *}

inductive_cases ThrowE[elim!]: "(THROW, s) \<Rightarrow> t"
inductive_cases TryE[elim!]: "(TRY c1 CATCH c2, s) \<Rightarrow> t"
text{* An automatic example: *}

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> (c, t) \<Longrightarrow> t = s"
by blast

text{* Rule inversion by hand via the ``cases'' method: *}

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> (c, t)"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  --"inverting assms"
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> (SKIP, s') \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text {* An example combining rule inversion and derivations *}
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> (SKIP, s') \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> (SKIP, s')"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> (SKIP, s')"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> (SKIP, s1)" and
    c2: "(c2, s1) \<Rightarrow> (SKIP, s2)" and
    c3: "(c3, s2) \<Rightarrow> (SKIP, s')" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> (SKIP, s')" by (rule Seq1)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> (SKIP, s')" by (rule Seq1)
next
  -- "The other direction is analogous"
  assume "(c1;; (c2;; c3), s) \<Rightarrow> (SKIP, s')"
  thus "(c1;; c2;; c3, s) \<Rightarrow> (SKIP, s')" by auto
qed


subsection "Command Equivalence"

text {*
  We call two statements @{text c} and @{text c'} equivalent wrt.\ the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
*}
text_raw{*\snip{BigStepEquiv}{0}{1}{% *}
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"
text_raw{*}%endsnip*}

text {*
Warning: @{text"\<sim>"} is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
*}

text {* Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.  *}

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> (c1, t)  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> (c1, t)"
by (induction "WHILE b DO c" s c1 t arbitrary: b c rule: big_step_induct) blast+

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
using sim_while_cong_aux by auto

text {* Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically. *}

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

subsection "Execution is deterministic"

text {* This proof is automatic. *}

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

end
