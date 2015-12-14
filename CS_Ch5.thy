theory CS_Ch5
imports Main
begin

lemma "\<not> surj (f :: 'a \<Rightarrow> 'a set)"
proof
  assume 0: "surj f"
  from 0 have 1: "\<forall>A. \<exists> a. A = f a" by (simp add: surj_def)
  from 1 have 2: "\<exists>a. {x. x \<notin> f x} = f a" by blast
  from 2 show "False" by blast
qed

lemma
fixes a b :: int
assumes "b dvd (a + b)"
shows "b dvd a"
proof -
  { fix k assume k: "a + b = b * k"
    have "\<exists>k'. a = b*k'"
    proof
      show "a = b*(k - 1)" using k by (simp add: algebra_simps)
    qed }
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

(* 5.1 *)

lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  hence "T y x" using T by auto
  hence "A y x" using TA by simp
  hence "x = y" using assms by simp
  hence "T x x" using assms by (auto)
  hence "T x y" using assms and `x = y` by (auto)
  thus "False" using `\<not> T x y` by auto
qed

(* 5.2 *)

lemma not2k_is_2y_plus_1: "\<exists>l. a = 2 * l + 1 \<Longrightarrow> \<forall>k. (a :: nat) \<noteq> 2 * k" by presburger

lemma shows "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)" (is "?L \<or> ?R")
proof cases
  assume k2: "even (length xs)"
  then obtain k where "length xs = 2 * k" using evenE by metis
  let ?x = "take k xs"
  let ?y = "drop k xs"
  have "(xs = ?x @ ?y \<and> length ?x = length ?y)" by (simp add: `length xs = 2 * k`)
  thus ?thesis by metis
next
  assume nk2: "odd (length xs)"
  then obtain l where "length xs = 2 * l + 1" using oddE by metis
  let ?x = "take (l+1) xs"
  let ?y = "drop (l+1) xs"
  have "length ?x = length ?y + 1" using `length xs = 2 * l + 1` by simp
  moreover have "xs = ?x @ ?y" by simp
  ultimately have "(xs = ?x @ ?y \<and> length ?x = length ?y + 1)" by simp
  hence th: "?L \<or> ?R" by metis
  thus ?thesis by metis
qed

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

(* 5.3 *)

lemma
assumes a: "ev (Suc (Suc n))"
shows "ev n"
proof -
  from a show "ev n"
  proof cases
    case evSS thus "ev n" by simp
  qed
qed

(* 5.4 *)

lemma
shows "\<not>ev (Suc (Suc (Suc 0)))"
proof
  assume "ev (Suc (Suc (Suc 0)))" thus False
  proof cases
    assume "ev (Suc 0)" thus False by cases
  qed
qed

(* 5.5 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
iter0: "iter r 0 x x" |
iterstep: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

lemma
shows "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case iter0 show ?case by (rule star.refl)
next
  case iterstep thus ?case by (auto intro: star.step)
qed

(* 5.6 *)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x # xs) = {x} \<union> elems xs"

(* I don't think I like the case shorthand, but it sure does shorten proofs *)
lemma
fixes xs :: "'a list"
shows "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  (* personally I would have wanted to do a proof-by-contradiction here, but the simplifier
     seems to be able to handle this sort of case when it's simple enough *)
  thus ?case by simp
next
  case (Cons a as)
  show ?case
  proof cases
    (* a and as (such that xs = a # as) becomes a "Skolem variable". I don't know precisely what this means yet, 
       but it seems to behave normally *)
    assume "x = a"
    then obtain zs where ac: "a # as = x # zs" by simp
    let ?ys = "[] :: 'a list"
    from ac have "a # as = ?ys @ x # zs" by simp
    have s: "x \<notin> elems ?ys" by simp
    from ac s show ?case by blast 
    (* seems to be the easiest way to get the existential introduced.
       unfortunately/fortunately, blast also knows how to solve the goal outright without any
       of this manual fluffery! I think the point of this exercise is practice with structured
       proofs, so I'll leave it in.*)
   next
    assume "x \<noteq> a"
    from this `x \<in> elems (a # as)` have "x \<in> elems as" by simp
    from this Cons.IH obtain ys zs where "as = ys @ x # zs \<and> x \<notin> elems ys" by auto
    (* interestingly, this is a case where auto works but simp doesn't.
       I need to check the manual to see precisely what these proof methods do.
    *)
    from this `x \<noteq> a` Cons.IH obtain ys' where "a # as = ys' @ x # zs \<and> x \<notin> elems ys'" by force
    thus ?case by blast
  qed
qed
  

end