theory CS_Ch3
imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) = (case (asimp_const a1, asimp_const a2) of
  (N n1, N n2) \<Rightarrow> N (n1+n2) |
  (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
apply(induction a)
apply(auto split: aexp.split)
done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply(auto)
done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
apply(induction a)
apply(auto simp add: aval_plus)
done

(* 3.1 *)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N a) (N b)) = False" |
"optimal (Plus a b) = (optimal a \<and> optimal b)"

lemma "optimal (asimp_const a)"
apply(induction a)
apply(auto split: aexp.split)
done

(* 3.2 *)

(* If you view this as a rewriting system that is designed to work only in conjunction
   with full_asimp, the structure of this function makes sense. We apply full_asimp recursively,
   so this function can look as few layers deep as it wants into the expression and full_asimp will
   glue it together. That is, its correctness can be inductively proven. *)
fun full_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"full_plus (N i1) (N i2) = N (i1 + i2)" |
"full_plus (N i1) (Plus a (N i2)) = Plus a (N (i1 + i2))" |
"full_plus (Plus a (N i1)) (N i2) = Plus a (N (i1 + i2))" |
"full_plus a (Plus b (N i1)) = Plus (Plus a b) (N i1)" |
"full_plus (Plus a (N i1)) b = Plus (Plus a b) (N i1)" |
"full_plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"full_plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"full_plus a1 a2 = Plus a1 a2"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N a) = N a" |
"full_asimp (V x) = V x" |
"full_asimp (Plus a b) = full_plus (full_asimp a) (full_asimp b)"

lemma aval_full_plus: "aval (full_plus a b) s = aval a s + aval b s"
apply(induction rule: full_plus.induct)
apply(auto)
done

lemma "aval (full_asimp a) s = aval a s"
apply(induction a)
apply(auto simp add: aval_full_plus)
done

(* 3.3 *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N i1) = N i1" |
"subst x a (V y) = (if x = y then a else (V y))" |
"subst x a (Plus b1 b2) = Plus (subst x a b1) (subst x a b2)"

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
apply(induction e)
apply(auto)
done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
apply(induction e)
apply(auto)
done

end