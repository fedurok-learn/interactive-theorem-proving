theory Scratch
  imports Main
begin

(*
  Add
*)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)"

lemma add_assoc: "add (add x y) z = add x (add y z)"
  apply(induction x)
  apply(auto)
  done

lemma [simp]: "add x 0 = x"
  apply(induction x)
   apply(auto)
  done

lemma [simp]: "add x (Suc y) = Suc (add x y)"
  apply(induction x)
   apply(auto)
  done

lemma add_commut: "add x y = add y x"
  apply(induction x)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"

lemma double_to_add: "double n = add n n"
  apply(induction n)
  apply(auto)
  done

(*
  Count
*)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count el [] = 0" |
  "count el (x#xs) = (if el = x then Suc (count el xs) else count el xs)"

lemma count_le_length: "count el xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(*
  Snoc
*)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] el = [el]" |
  "snoc (x#xs) el = x#(snoc xs el)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x#xs) = snoc (reverse xs) x"

lemma [simp]: "reverse (snoc xs el) = el # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

lemma reverse_reverse: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

(*
  Sum up to
*)

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = add (Suc n) (sum_upto n)"

lemma [simp]: "add x y = x + y"
  apply(induction x)
  apply(auto)
  done

lemma sum_upto_formula: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
  done

end