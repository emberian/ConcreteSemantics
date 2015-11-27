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

(* 3.4 is a separate theory, CS_Ch3_Ex4 *)

(* 3.5 *)
datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PostIncr2 vname | Div2 aexp2 aexp2
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N2 i) s = Some (i, s)" |
"aval2 (V2 x) s = Some (s x, s)" |
"aval2 (Plus2 a b) s = (case (aval2 a s) of Some (a', s') \<Rightarrow> 
  (case (aval2 b s') of Some (b', s'') \<Rightarrow> Some (a' + b', s'') | None \<Rightarrow> None) | None \<Rightarrow> None)" |
"aval2 (PostIncr2 x) s = Some (s x, s(x := (s x) + 1))" |
"aval2 (Div2 a b) s = (case (aval2 b s) of Some (b', s') \<Rightarrow> (if b' = 0 then None else Some (
  case (aval2 a s') of Some (a', s'') \<Rightarrow> (a' div b', s''))) | None \<Rightarrow> None)"

lemma "aval2 (Div2 (N2 3) (Plus2 (N2 1) (V2 ''x''))) (\<lambda>x. -1) = None"
apply(auto)
done

lemma "case aval2 (Div2 (N2 3) (PostIncr2 ''x'')) (\<lambda>x. 1) of Some (a, b) \<Rightarrow> (a = 3 \<and> b(''x'') = 2) | None \<Rightarrow> False"
apply(auto)
done

(* 3.6 *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp
fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl i) s = i" |
"lval (Vl x) s = s x" |
"lval (Plusl a b) s = lval a s + lval b s" |
"lval (LET x val body) s = lval body (s(x := lval val s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl i) = (N i)" |
"inline (Vl x) = (V x)" |
"inline (Plusl a b) = Plus (inline a) (inline b)" |
"inline (LET x val body) = subst x (inline val) (inline body)"

lemma "lval e s = aval (inline e) s"
apply(induction e arbitrary: s)
apply(auto simp add: subst_lemma)
done

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (aexp.N n\<^sub>1) (aexp.N n\<^sub>2) = Bc (n\<^sub>1 < n\<^sub>2)" |
"less a\<^sub>1 a\<^sub>2 = Less a\<^sub>1 a\<^sub>2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not (bsimp b)" |
"bsimp (And b\<^sub>1 b\<^sub>2) = and (bsimp b\<^sub>1) (bsimp b\<^sub>2)" |
"bsimp (Less a\<^sub>1 a\<^sub>2) = less (asimp a\<^sub>1) (asimp a\<^sub>2)"

(* 3.7 *)

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Not (Less a b)) (Not (Less b a))"

lemma "bval (Eq a b) s = (aval a s = aval b s)"
apply(auto)
done

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (And (Not (Less a b)) (Not (Eq a b)))"

lemma "bval (Le a b) s = (aval a s \<le> aval b s)"
apply(auto)
done

(* 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) s = b" |
"ifval (If a b c) s = (if ifval a s then ifval b s else ifval c s)" |
"ifval (Less2 a b) s = (aval a s < aval b s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Less a b) = (Less2 a b)" |
"b2ifexp (Not a) = If (b2ifexp a) (Bc2 False) (Bc2 True)" |
"b2ifexp (And a b) = If (b2ifexp a) (b2ifexp b) (Bc2 False)" |
"b2ifexp (Bc b) = Bc2 b"

lemma "bval b s = ifval (b2ifexp b) s"
apply(induction b)
apply(auto)
done

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = Bc b" |
"if2bexp (If c t f) = And (Not (And (if2bexp c) (Not (if2bexp t)))) (Not (And (Not (if2bexp c)) (Not (if2bexp f))))" |
"if2bexp (Less2 a b) = Less a b"

lemma "ifval i s = bval (if2bexp i) s"
apply(induction i)
apply(auto)
done

(* 3.9 *)

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<and> pbval b\<^sub>2 s)" |
"pbval (OR b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<or> pbval b\<^sub>2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT y) = False" |
"is_nnf (OR a b) = (is_nnf a \<and> is_nnf b)" |
"is_nnf (AND a b) = (is_nnf a \<and> is_nnf b)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = VAR x" |
"nnf (NOT (VAR x)) = (NOT (VAR x))" |
"nnf (NOT (AND a b)) = OR (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (OR a b)) = AND (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (NOT b)) = nnf b " |
"nnf (AND a b) = AND (nnf a) (nnf b)" |
"nnf (OR a b) = OR (nnf a) (nnf b)"

lemma "is_nnf (nnf b)"
apply(induction b rule: nnf.induct)
apply(auto)
done

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
(* since we assume NNF, we don't need to handle NOT *)
"is_dnf (NOT x) = True" |
"is_dnf (AND (OR _ _) _) = False" |
"is_dnf (AND _ (OR _ _)) = False" |
"is_dnf (AND a b) = (is_dnf a \<and> is_dnf b)" |
"is_dnf (OR a b) = (is_dnf a \<and> is_dnf b)"


fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NOT x) = NOT x" |
"dnf_of_nnf (OR a b) = OR (dnf_of_nnf a) (dnf_of_nnf b)" |
"dnf_of_nnf (AND (OR o\<^sub>1 o\<^sub>2) a) = OR (AND o\<^sub>1 a) (AND o\<^sub>2 a)" |
"dnf_of_nnf (AND a (OR o\<^sub>1 o\<^sub>2)) = OR (AND o\<^sub>1 a) (AND o\<^sub>2 a)" |
"dnf_of_nnf (AND a b) = AND (dnf_of_nnf a) (dnf_of_nnf b)"

lemma "pbval (dnf_of_nnf b) s = pbval b s"
apply(induction b rule: dnf_of_nnf.induct)
apply(auto)
done

lemma "is_nnf b \<Longrightarrow> is_nnf (dnf_of_nnf b)"
apply(induction b rule: dnf_of_nnf.induct)
apply(auto)
done

datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"
abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 (LOAD x) s stk = Some ((s x) # stk)" |
"exec1 ADD _ (h # h2 # rst) = Some ((h2 + h) # rst)" |
"exec1 ADD _ _ = None"

(* I tried using Option.bind etc but I can't seem to get anything proven when I'm using it.
   Expanding it manually works, though. Oh well. *)
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some (stk)" |
"exec (i # is) s stk = (case (exec1 i s stk) of Some stk' \<Rightarrow> exec is s stk' | None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

(* I originally tried to formulate these lemmas like,
"case (exec is\<^sub>1 s stk) of Some stk' \<Rightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s stk' 
                        | None \<Rightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = None"
but was unable to prove them. *)
lemma exec_append: "exec is\<^sub>1 s stk = Some stk' \<Longrightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s stk'"
apply(induction is\<^sub>1 arbitrary: stk)
apply(auto split: option.split)
done

lemma "exec (comp a) s stk = Some (aval a s # stk)"
apply(induction a arbitrary: stk)
apply(auto simp add: exec_append)
done

(* 3.11 *)
type_synonym reg = nat
datatype reginstr = LDI int reg | LD vname reg | ADD reg reg

fun regexec1 :: "reginstr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"regexec1 (LDI v r) s file = file(r := v)" |
"regexec1 (LD x r) s file = file(r := s x)" |
"regexec1 (ADD r\<^sub>1 r\<^sub>2) s file = file(r\<^sub>1 := (file r\<^sub>1) + (file r\<^sub>2))"

fun regexec :: "reginstr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"regexec [] s file = file" |
"regexec (i # is) s file = regexec is s (regexec1 i s file)"

fun regcomp :: "aexp \<Rightarrow> reg \<Rightarrow> reginstr list" where
"regcomp (N n) r = [LDI n r]" |
"regcomp (V x) r = [LD x r]" |
"regcomp (Plus e\<^sub>1 e\<^sub>2) r = regcomp e\<^sub>1 r @ regcomp e\<^sub>2 (r+1) @ [ADD r (r+1)]"

lemma regexec_append: "regexec (is\<^sub>1 @ is\<^sub>2) s file = regexec is\<^sub>2 s (regexec is\<^sub>1 s file)"
apply(induction is\<^sub>1 arbitrary: "file")
apply(auto)
done

lemma regcomp_dont_touch_small_regs: "q < r \<Longrightarrow> regexec (regcomp a r) s file q = file q"
apply(induction a arbitrary: r "file")
apply(auto simp add: regexec_append)
done

lemma "(regexec (regcomp a r) s file) r = aval a s"
apply(induction a arbitrary: s r "file")
apply(auto simp add: regexec_append regcomp_dont_touch_small_regs)
done

(* 3.12 *)
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec10 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec10 (LDI0 val) s file = file(0 := val)" |
"exec10 (LD0 vname) s file = file(0 := s vname)" |
"exec10 (MV0 reg) s file = file(reg := file 0)" |
"exec10 (ADD0 reg) s file = file(0 := (file 0) + (file reg))"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec0 [] s file = file" |
"exec0 (i # is) s file = exec0 is s (exec10 i s file)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N n) r = [LDI0 n]" |
"comp0 (V x) r = [LD0 x]" |
"comp0 (Plus e\<^sub>1 e\<^sub>2) r = (comp0 e\<^sub>1 (r+1)) @ [MV0 (r+1)] @ (comp0 e\<^sub>2 (r+2)) @ [ADD0 (r+1)]"

lemma exec0_append: "exec0 (is\<^sub>1 @ is\<^sub>2) s file = exec0 is\<^sub>2 s (exec0 is\<^sub>1 s file)"
apply(induction is\<^sub>1 arbitrary: "file")
apply(auto)
done

lemma comp0_register_preservation: "0 \<noteq> q \<Longrightarrow> q < r \<Longrightarrow> exec0 (comp0 a r) s file q = file q"
apply(induction a arbitrary: r q "file")
apply(auto simp add: exec0_append)
done

lemma "exec0 (comp0 a r) s rs 0 = aval a s"
apply(induction a arbitrary: r s rs)
apply(auto simp add: exec0_append comp0_register_preservation)
done