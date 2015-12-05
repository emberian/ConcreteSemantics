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
  
end