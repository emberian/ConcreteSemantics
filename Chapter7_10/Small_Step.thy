section "Small-Step Semantics of Commands"

theory Small_Step imports "~~/src/HOL/IMP/Star" "./Big_Step" begin

subsection "The transition relation"

inductive
  small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(THROW;; c\<^sub>2, s) \<rightarrow> (THROW, s)" |
Seq3:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |

TryStep: "(c, s) \<rightarrow> (c', t) \<Longrightarrow> (TRY c CATCH c2, s) \<rightarrow> (TRY c' CATCH c2, t)" |
TryGood: "(TRY SKIP CATCH c2, s) \<rightarrow> (SKIP, s)" |
TryBad: "(TRY THROW CATCH c2, s) \<rightarrow> (c2, s)"

abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

subsection{* Executability *}

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
   (''x'' ::= V ''z'';; ''y'' ::= V ''x'',
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"

values "{(c', map t [''x'']) |c' t. (TRY ''x'' ::= N 2;; 
THROW;; ''x'' ::= N 4 CATCH ''x'' ::= N 3, <>) \<rightarrow>* (c', t)}"

subsection{* Proof infrastructure *}

subsubsection{* Induction rules *}

text{* The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form @{text"a \<rightarrow> b \<Longrightarrow> \<dots>"} where @{text a} and @{text b} are
not already pairs @{text"(DUMMY,DUMMY)"}. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
@{text"\<rightarrow>"} into pairs: *}
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection{* Proof automation *}

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
inductive_cases ThrowE[elim!]: "(THROW,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
inductive_cases TryE[elim!]: "(TRY c CATCH c2, s) \<rightarrow> ct"

text{* A simple property: *}
lemma deterministic:
  "(cs, s) \<rightarrow> t1 \<Longrightarrow> (cs, s) \<rightarrow> t2 \<Longrightarrow> t1 = t2"
by (induction arbitrary: t2 rule: small_step.induct) blast+

subsection "Equivalence with big-step semantics"

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq3 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (c3,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (c3,s3)"
by(blast intro: star.step star_seq2 star_trans)

lemma seq_comp2:
  "\<lbrakk> (c1,s1) \<rightarrow>* (THROW,s2); (c2,s2) \<rightarrow>* (c3,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (THROW,s2)"
by(blast intro: star.step star_seq2 star_trans)

lemma always_execute_inner:
assumes "(c, s) \<rightarrow>* (c', s')"
shows "(TRY c CATCH c2, s) \<rightarrow>* (TRY c' CATCH c2, s')"
using assms
proof (induction rule: star_induct)
  case refl show ?case by simp
next
  case step thus ?case by (meson TryStep star.step)
qed

text{* Each case of the induction can be proved automatically: *}
lemma big_to_small: "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* t"
proof (induction rule: big_step.induct)
  case Seq1 thus ?case using seq_comp by (meson star.refl star_trans)
next
  case Seq2 thus ?case using seq_comp2 by blast
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue1
  thus ?case using seq_comp 
    by (meson While small_step.IfTrue star.refl star_step1 star_trans)
next
  case WhileTrue2
  thus ?case using seq_comp2
    by (meson While small_step.IfTrue star.refl star_step1 star_trans)
next
  case (TryOk c s t c2)
  from `(c, s) \<rightarrow>* (SKIP, t)` have "(TRY c CATCH c2, s) \<rightarrow>* (TRY SKIP CATCH c2, t)" 
    using always_execute_inner by auto
  moreover have "(TRY SKIP CATCH c2, t) \<rightarrow>* (SKIP, t)" using TryGood by auto
  ultimately show ?case using star_trans by fastforce
next
  case (TryBad c s t c2 ct)
  thus ?case by (meson always_execute_inner star_step1 star_trans  small_step.TryBad)
qed blast+

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_to_big_skip:
  "cs \<rightarrow>* (SKIP, t) \<Longrightarrow> cs \<Rightarrow> (SKIP, t)"
apply (induction cs "(SKIP, t)" rule: star.induct)
apply (auto intro: small1_big_continue)
done

lemma small_to_big_throw:
  "cs \<rightarrow>* (THROW, t) \<Longrightarrow> cs \<Rightarrow> (THROW, t)"
apply (induction cs "(THROW, t)" rule: star.induct)
apply (auto intro: small1_big_continue)
done

text {*
  Finally, the equivalence theorem:
*}

lemma big_iff_small_skip:
  "cs \<Rightarrow> (SKIP, t) = cs \<rightarrow>* (SKIP, t)"
by(metis big_to_small small_to_big_skip)

lemma big_iff_small_throw:
  "cs \<Rightarrow> (THROW, t) = cs \<rightarrow>* (THROW, t)"
by(metis big_to_small small_to_big_throw)

subsection "Final configurations and infinite reductions"

definition "final cs \<longleftrightarrow> \<not>(EX cs'. cs \<rightarrow> cs')"

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP \<or> c = THROW"
apply(simp add: final_def)
apply(induction c)
apply blast+
done

lemma final_iff_SKIP_or_THROW: "final (c,s) = (c = SKIP \<or> c = THROW)"
using finalD final_def by blast

lemma big_is_final:
  "cs \<Rightarrow> t \<Longrightarrow> final t"
by (induction rule: big_step.induct, auto simp add: final_iff_SKIP_or_THROW)

lemma big_iff_small_termination:
assumes "cs \<rightarrow>* t" and "final t"
shows "cs \<Rightarrow> t"
proof -
  from `cs \<rightarrow>* t` obtain c' t' where 1: "t = (c', t')" by fastforce
  from `final t` have 2: "t = (THROW, t') \<or> t = (SKIP, t')" 
    using final_iff_SKIP_or_THROW 1 by auto
  moreover have "t = (THROW, t') \<Longrightarrow> cs \<Rightarrow> t" proof - 
    assume "t = (THROW, t')"
    then show "cs \<Rightarrow> t" using `cs \<rightarrow>* t` small_to_big_throw by auto
  qed
  moreover have "t = (SKIP, t') \<Longrightarrow> cs \<Rightarrow> t" proof -
    assume "t = (SKIP, t')"
    then show "cs \<Rightarrow> t" using `cs \<rightarrow>* t` small_to_big_skip by auto
  qed
  ultimately show "cs \<Rightarrow> t" using 2 by auto
qed

text{* Now we can show that @{text"\<Rightarrow>"} yields a final state iff @{text"\<rightarrow>"}
terminates: *}

lemma big_iff_small_termination_weird_exists_form:
  "(EX t. cs \<Rightarrow> t) \<longleftrightarrow> (EX cs'. cs \<rightarrow>* cs' \<and> final cs')" 
by (meson big_is_final big_iff_small_termination final_iff_SKIP_or_THROW big_to_small)

text{* This is the same as saying that the absence of a big step result is
equivalent with absence of a terminating small step sequence, i.e.\ with
nontermination.  Since @{text"\<rightarrow>"} is determininistic, there is no difference
between may and must terminate. *}

end
