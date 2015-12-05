theory CS_Ch4
imports Main "./CS_Ch3"
begin

(* 4.1 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l v r) = (set l) \<union> {v} \<union> (set r)"

(* the hint says to use quantifiers. I initially tried doing this with a recursive definition for
   the "treele" and "treege" but ran into issues trying to do the proof. I needed more lemmas than
   I thought necessary. The set-based definition seems to work around this, probably by having all
   the properties that need to be proved about custom functions implied by the quantifier and the
   fanciness that 'auto' does. *)
fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l v r) = ((ord l) \<and> (ord r) \<and> (\<forall>x\<in>(set l). x \<le> v) \<and> (\<forall>x\<in>(set r). x \<ge> v))"

fun ins :: "int tree \<Rightarrow> int \<Rightarrow> int tree" where
"ins Tip a = Node Tip a Tip" |
"ins (Node l v r) a = (if a \<le> v then Node (ins l a) v r else Node l v (ins r a))"

lemma ins_lem: "set (ins t x) = {x} \<union> set t"
apply(induction t)
apply(auto)
done

value "ins (Node Tip (-1) Tip) 0"

lemma "ord t \<Longrightarrow> ord (ins t x)"
apply(induction t arbitrary: x)
apply(auto simp add: ins_lem)
done

inductive ev :: "nat \<Rightarrow> bool" where
ev0 : "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev(Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

lemma "ev m \<Longrightarrow> evn m"
apply(induction rule: ev.induct)
by(simp_all)

declare ev.intros[simp, intro]

lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
by(simp_all)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
apply(metis step)
done

(* 4.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
empty: "palindrome []" |
singleton: "palindrome [a]" |
step: "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma palindrome_invariant_under_rev: "palindrome xs \<Longrightarrow> rev xs = xs"
apply(induction xs rule: palindrome.induct)
apply(auto)
done

(* 4.3 *)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

(* this lemma is required to prove the right-hand side of a subgoal, but we need to separate it
   out to apply the rule induction *)
lemma star'_rightmost_bit: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(auto intro: star.refl star.step)
done

lemma "star' r x y \<Longrightarrow> star r x y"
apply(induction rule: star'.induct)
apply(rule star.refl)
apply(auto simp add: star'_rightmost_bit)
done

(* this lemma is required to reorder the implications to allow induction to proceed *)
lemma star_reordered_bit: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
apply(induction rule: star'.induct)
apply(auto intro: refl' step')
done

lemma "star r x y \<Longrightarrow> star' r x y"
apply(induction rule: star.induct)
apply(auto simp add: star_reordered_bit intro: star'.refl')
done

(* 4.4 *)

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
iter0: "iter r 0 x x" |
iterstep: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

(* the "correction" is the introduction of the existential. not sure what the "implicit"
   meaning of a free variable is. I expect it to be a meta-\<forall> though. *)
lemma "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
apply(induction rule: star.induct)
apply(auto intro: iter0 iterstep)
done

(* 4.5 *)

datatype alpha = a | b | c
inductive S :: "alpha list \<Rightarrow> bool" where
empty: "S []" |
fst: "S s \<Longrightarrow> S (a # s @ [b])" |
snd: "S s\<^sub>1 \<Longrightarrow> S s\<^sub>2 \<Longrightarrow> S (s\<^sub>1 @ s\<^sub>2)"

inductive T :: "alpha list \<Rightarrow> bool" where
empty: "T []" |
fst: "T t\<^sub>1 \<Longrightarrow> T t\<^sub>2 \<Longrightarrow> T (t\<^sub>1 @ [a] @ t\<^sub>2 @ [b])"

lemma t_implies_s: "T w \<Longrightarrow> S w"
apply(induction w rule: T.induct)
apply(auto intro: S.empty S.fst S.snd T.fst)
done

lemma t_same_form_as_s: "T s \<Longrightarrow> T (a # s @ [b])"
apply(induction s)
(* thanks try! *)
apply(metis T.empty T.fst append_Nil append_Cons)
apply(metis T.empty T.fst append_Nil append_Cons)
done

lemma t_append: "T t\<^sub>1 \<Longrightarrow> T t\<^sub>2 \<Longrightarrow> T (t\<^sub>2 @ t\<^sub>1)"
apply(induction t\<^sub>1 rule: T.induct)
apply(simp)
(* simplifying this subgoal causes metis to not terminate. additionally, trying to prove T (t\<^sub>1 @ t\<^sub>2)
   also causes non-termintation. (at least, I assume it won't terminate, I left it running in the
   background and forgot about it for a few hours... I'd be curious to dig deeper into the cause
   of the non-termination. In fact, it's even sensitive to the order of the antecedents! *)
apply (metis append_assoc T.fst)
done

(* but, this consequence is a straightforward unification with t_append! *)
lemma "T t\<^sub>1 \<Longrightarrow> T t\<^sub>2 \<Longrightarrow> T (t\<^sub>1 @ t\<^sub>2)"
apply(rule t_append)
apply(simp_all)
done

lemma s_implies_t: "S w \<Longrightarrow> T w"
apply(induction w rule: S.induct)
apply(auto simp add: T.empty t_same_form_as_s t_append)
done

lemma s_equiv_t: "S w = T w"
apply(auto simp add: s_implies_t t_implies_s)
done

(* 4.6 *)

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
inN: "aval_rel (N n) s n" |
inV: "s x = n \<Longrightarrow> aval_rel (V x) s n" |
inPlus: "aval_rel e\<^sub>1 s v\<^sub>1 \<Longrightarrow> aval_rel e\<^sub>2 s v\<^sub>2 \<Longrightarrow> aval_rel (Plus e\<^sub>1 e\<^sub>2) s (v\<^sub>1 + v\<^sub>2)"

lemma aval_rel_is_aval: "aval_rel e s v \<Longrightarrow> aval e s = v"
apply(induction rule: aval_rel.induct)
apply(auto)
done

lemma aval_is_aval_rel: "aval e s = v \<Longrightarrow> aval_rel e s v"
apply(induction e arbitrary: v)
(* The third subgoal here has a very interesting structure - the v is quantified in each antecedent,
   separately from the v generated by the induction. This makes sense, but initially surprised me. *)
apply(auto intro: inN inV inPlus)
done

lemma "aval_rel e s v \<longleftrightarrow> aval e s = v"
apply(auto) (* split the \<longleftrightarrow> *)
(* if you try to do both of these at once, it will not terminate for obvious reasons *)
apply(auto simp add: aval_rel_is_aval)
apply(auto simp add: aval_is_aval_rel)
done

(* 4.7 *)

(* copying defn's to tear out the option *)

datatype instr = LOADI val | LOAD vname | ADD

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = n # stk" |
"exec1 (LOAD x) s stk = (s x) # stk" |
"exec1 ADD _ stk = (hd stk + hd2 stk) # tl2 stk"

(* I tried using Option.bind etc but I can't seem to get anything proven when I'm using it.
   Expanding it manually works, though. Oh well. *)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i # is) s stk = (exec is s (exec1 i s stk))"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

(* I originally tried to formulate these lemmas like,
"case (exec is\<^sub>1 s stk) of Some stk' \<Rightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s stk' 
                        | None \<Rightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = None"
but was unable to prove them. *)
lemma exec_append: "exec is\<^sub>1 s stk = stk' \<Longrightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s stk'"
apply(induction is\<^sub>1 arbitrary: stk)
apply(auto)
done

lemma "exec (comp e) s stk =  aval e s # stk"
apply(induction e arbitrary: stk)
apply(auto simp add: exec_append)
done

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
okempty: "ok n [] n" |
okLOADI: "ok n is n' \<Longrightarrow> ok n (is @ [LOADI _]) (Suc n')" |
okLOAD: "ok n is n' \<Longrightarrow> ok n (is @ [LOAD _]) (Suc n')" |
(* protip: unbound variables are universally quantified. So if you say, for example is @ [PLUS], you
   gotta prove that sucker for all values of PLUS. Pay attention to the quantifiers when things
   don't work as expected! *)
okADD: "ok n is (Suc (Suc n')) \<Longrightarrow> ok n (is @ [ADD]) (Suc n')"

lemma "\<lbrakk>ok n is n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"
apply(induction rule: ok.induct)
apply(auto simp add: exec_append intro: okempty okLOADI okLOAD okADD)
done

lemma ok_append: "ok n (e2) n' \<Longrightarrow> ok n'' (e1) n \<Longrightarrow> ok n'' (e1 @ e2) n'"
apply(induction rule: ok.induct)
apply(simp)
apply (metis append_assoc ok.simps)
apply (metis append_assoc ok.simps)
apply (metis append_assoc ok.simps)
done

(* if we start with any stack, executing the result of compiling an aexp will leave one more elt
   on the stack. *)
lemma "ok n (comp e) (Suc n)"
apply(induction e arbitrary: n)
using okLOADI okempty apply fastforce
using okLOAD okempty apply fastforce
using okADD ok_append apply fastforce
done

end