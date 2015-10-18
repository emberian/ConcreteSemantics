theory CS_Ch2
imports Main
begin

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_assoc: "add (add a b) c = add a (add b c)"
apply(induction a)
apply(auto)
done

lemma add_zero_does_nothing[simp]: "add a 0 = a"
apply(induction a)
apply(auto)
done

lemma add_succ[simp]: "add a (Suc b) = Suc(add a b)"
  apply(induction a)
  apply auto
done

lemma add_comm: "add a b = add b a"
apply(induction a)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma double_is_add_self: "double m = add m m"
apply(induction m)
apply(auto)
done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ [] = 0" |
"count e (x # xs) = (if e = x then Suc (count e xs) else count e xs)"

lemma count_less_than_length: "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (x # xs) a = x # (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = (reverse xs) @ [x]"

lemma rev_distributes_over_app: "reverse (xs @ ys) = (reverse ys) @ (reverse xs)"
apply(induction xs)
apply(auto)
done

lemma rev_undos_self: "reverse (reverse xs) = xs"
apply(induction xs)
apply(auto)
apply(simp add: rev_distributes_over_app)
done

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = add (Suc n) (sum n)"

lemma add_doubles_under_div: "add n (m div 2) = (n + n + m) div 2"
apply(induction n)
apply(auto)
done

lemma euler_is_cheeky: "sum n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
apply(simp add: add_doubles_under_div)
done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node a b c) = b # (contents a) @ (contents c)"

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0" |
"treesum (Node a b c) = b + (treesum a) + (treesum c)"

lemma sum_preserved: "treesum t = listsum (contents t)"
apply(induction t)
apply(auto)
done

datatype 'a tree2  = Node "'a tree2" 'a "'a tree2" | Leaf "'a option"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 (Leaf a) = Leaf a"  |
"mirror2 (Node a b c) = Node (mirror2 c) b (mirror2 a)"

lemma "mirror2(mirror2(t)) = t"
apply(induction t)
apply(auto)
done

fun pre_order :: "'a tree2 \<Rightarrow> 'a option list" where
"pre_order (Leaf a) = [a]" |
"pre_order (Node a b c) = (Some b) # (pre_order a) @ (pre_order c)"

fun post_order :: "'a tree2 \<Rightarrow> 'a option list" where
"post_order (Leaf a) = [a]" |
"post_order (Node a b c) = (post_order a) @ (post_order c) @ [Some b]"

lemma "pre_order (mirror2 t) = rev (post_order t)"
apply(induction t)
apply(auto)
done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # []) = [a, x]" |
"intersperse a (x # xs) = [a, x] @ intersperse a xs"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs rule: intersperse.induct)
apply(auto)
done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = add n m"
apply(induction m arbitrary: n)
apply(auto)
done

datatype tree0 = Leaf | Node tree0 tree0

(* note: using "+" and "1" here is important for algebra_simps to kick in! *)

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Leaf = 1" |
  "nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

theorem "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
  apply (induction n arbitrary: t)
  apply (auto simp add: algebra_simps)
done

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const a) _ = a" |
"eval (Add a b) x = (eval a x) + (eval b x)" |
"eval (Mult a b) x = (eval a x) * (eval b x)"

fun evalp' :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
"evalp' [] _ _ = 0" |
"evalp' (x # xs) val exp = (val^exp)*x + (evalp' xs val (Suc exp))"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp xs val = evalp' xs val 0"

fun coeff_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"coeff_add (x # xs) (y # ys) = (x + y) # (coeff_add xs ys)" |
"coeff_add [] ys = ys" |
"coeff_add xs [] = xs"

fun shift_list_by :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"shift_list_by 0 val xs = xs" |
"shift_list_by (Suc n) val xs = val # (shift_list_by n val xs)"

fun list_sum :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"list_sum (x # xs) (y # ys) = (x+y) # list_sum xs ys" |
"list_sum [] ys = ys" |
"list_sum xs [] = xs"

lemma "list_sum xs xs = map (\<lambda>x. x+x) xs"
apply(induction xs)
apply(auto)
done

fun fill_with :: "int list \<Rightarrow> int \<Rightarrow> int list" where
"fill_with (x # xs) val = val # fill_with xs val" |
"fill_with [] _ = []"
(*
fun coeff_mult' :: "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
"coeff_mult' [] n ys = []" |
"coeff_mult' (x # xs) n ys = list_sum (coeff_mult' xs (Suc n) ys) (shift_list_by n 0 (map (\<lambda>v. x*v) ys))"

fun coeff_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"coeff_mult xs ys = coeff_mult' xs 0 ys"
*)

fun coeff_mult_constant :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"coeff_mult_constant a [] = []" |
"coeff_mult_constant a (x # xs) = (a * x) # coeff_mult_constant a xs"

fun coeff_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"coeff_mult [] ys = []" |
"coeff_mult (x # xs) ys = coeff_add (coeff_mult_constant x ys) (coeff_mult xs (0 # ys))"

(* I originally used a map instead of coeff_mult_constant, but I had a
   hard time trying to prove anything involving map. *)
lemma "coeff_mult_constant a xs = coeff_mult [a] xs"
apply(induction xs arbitrary: a)
apply(auto simp add: algebra_simps map_add_def)
done

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const a) = [a]" |
"coeffs (Add a b) = coeff_add (coeffs a) (coeffs b)" |
"coeffs (Mult a b) = coeff_mult (coeffs a) (coeffs b)"

lemma add_is_plus: "evalp' (coeff_add a b) x d = evalp' a x d + evalp' b x d"
apply(induction a b arbitrary: d rule: coeff_add.induct)
apply(auto simp add: algebra_simps)
done

lemma multiplying_by_a_constant_distributes: "evalp' (coeff_mult_constant a xs) x d = a * (evalp' xs x d)"
apply(induction xs arbitrary: d)
apply(auto simp add: algebra_simps add_is_plus)
done

lemma multiplying_by_x_extends_coeff_list: "x * evalp' a x d = evalp' (0 # a) x d"
apply(induction a arbitrary: d)
apply(auto simp add: algebra_simps)
done
lemma succ_of_exponent_mults_by_x: "evalp' a x (Suc d) = x * evalp' a x d"
apply(induction d)
apply(auto simp add: algebra_simps multiplying_by_x_extends_coeff_list)
done

lemma evalp_mult_can_swap: "evalp' a x 0 * evalp' b x n = evalp' b x 0 * evalp' a x n"
apply(induction n)
apply(auto simp add: algebra_simps succ_of_exponent_mults_by_x)
done

lemma mult_is_star: "evalp' (coeff_mult a b) x 0 = (evalp' a x 0) * (evalp' b x 0)"
apply(induction a arbitrary: b)
apply(auto simp add: algebra_simps add_is_plus multiplying_by_a_constant_distributes 
  evalp_mult_can_swap)
done

lemma "evalp (coeffs poly) x = eval poly x"
apply(induction poly rule: coeffs.induct)
apply(auto simp add: algebra_simps mult_is_star add_is_plus)
done

end