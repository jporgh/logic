theory ZFCmodel
imports Parity
begin

definition elem :: "nat \<Rightarrow> nat \<Rightarrow> bool"
 where "elem k n \<equiv> odd (n div 2^k)"

lemma elemZero:
 "elem 0 n = odd n"
by (metis div_by_1 elem_def power_0)

lemma elemSuc:
 "elem (Suc k) n = elem k (n div 2)"
apply (auto simp: elem_def)
apply (metis Divides.div_mult2_eq)
by (metis Divides.div_mult2_eq)

declare elemZero elemSuc [simp]

lemma elem2k:
 "elem k (2 * n) = (k \<noteq> 0 \<and> elem (k - 1) n)"
apply (cases "k")
apply (metis Suc_eq_plus1 div_by_1 elem_def even_Suc even_product odd_1_nat one_add_one power_0)
by auto

lemma elemSuc2k1:
 "elem (Suc k) (2 * n + 1) = elem k n"
by (metis add_self_div_2 elemSuc lemma_even_div2 mult_2 odd_add)

lemma elem2k1:
 "elem k (2 * n + 1) = (k = 0 \<or> elem (k - 1) n)"
apply (cases k)
apply (metis (poly_guards_query) Suc_eq_plus1 div_by_1 elem_def even_Suc even_sum_nat mult_2 power_0)
apply simp_all
by (metis Suc_eq_plus1 add_self_div_2 even_sum_nat lemma_even_div2 mult_2)

lemma nat_div1:
 "(n::nat) = k * (n div k) + n mod k"
by simp

lemma nat_div2:
  "2 \<le> k \<Longrightarrow> 1 \<le> n \<Longrightarrow> n div k < (n::nat)"
by simp

lemma nat_div3:
  "2 \<le> k \<Longrightarrow> n mod k < (k::nat)"
by simp

lemma nat_div4:
  "1 \<le> j \<Longrightarrow>
   \<forall>m<j. P m \<Longrightarrow>
   2 \<le> k \<Longrightarrow>
   (\<And>n m. m < k \<Longrightarrow> P n \<Longrightarrow> P (k * n + m)) \<Longrightarrow>
   P (j::nat)"
by (metis nat_div1 nat_div2 nat_div3)

lemma ind_k:
 "2 \<le> k \<Longrightarrow> P 0 \<Longrightarrow> (\<And>n m. m < k \<Longrightarrow> P n \<Longrightarrow> P (k * n + m)) \<Longrightarrow> P (x::nat)"
apply (induct "x" rule: nat_less_induct)
apply auto
apply (case_tac "n")
apply auto
apply (induct_tac rule: nat_div4)
by auto

lemma ind_k2:
 "P 0 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (2 * n)) \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (2 * n + 1)) \<Longrightarrow> P (x::nat)"
apply (induct "x" rule: ind_k[of "2"])
apply clarify
apply simp
apply (case_tac "m")
by auto

lemma null:
  "\<not>elem k 0"
by (metis Divides.div_mult2_eq elem_def even_zero nat_mult_div_cancel_disj)

lemma null_ext:
  "(!k. \<not>elem k n) \<Longrightarrow> n = 0"
apply (induction "n" rule: ind_k2)
apply simp_all
apply (subst (asm) elem2k)
apply (metis Suc_eq_plus1 diff_Suc_Suc diff_zero monoid_add_class.add.left_neutral old.nat.distinct(2))
by (metis Suc_eq_plus1 elem2k1)

lemma div2even:
  "even m \<Longrightarrow> m = 2 * (m div 2)"
by (metis dvd_mult_div_cancel even_iff_2_dvd)

lemma div2odd:
  "odd m \<Longrightarrow> m = 2 * (m div 2) + 1"
by (metis add.commute even_def mult.commute not_mod_2_eq_0_eq_1 semiring_div_class.mod_div_equality')

lemma ext_1:
 "\<forall>m. (\<forall>k. elem k m = elem k n) \<longrightarrow> m = n"
apply (induct_tac "n" rule: ind_k2)
apply simp_all
apply (metis null null_ext)
apply auto
apply (subst div2even)
apply auto
apply (metis div_by_1 elem_def even_sum_nat mult.commute mult_2_right power_0)
apply (insert elemSuc)
apply (subst (asm) elem2k)
apply (metis diff_Suc_1 old.nat.distinct(2))
apply auto
apply (subst div2odd)
apply auto
apply (metis Suc_eq_plus1 elem2k elem2k1 even_mult_two_ex)
apply (insert elem2k1 elemSuc)
apply auto
by (metis Suc_eq_plus1 diff_Suc_1 elemSuc monoid_add_class.add.left_neutral old.nat.distinct(2))

lemma elem_ext:
 "(\<forall>k. elem k m = elem k n) \<Longrightarrow> m = n"
by (metis (poly_guards_query) ext_1)

lemma ZFC_extensionality:
 "\<forall>m n. (\<forall>k. elem k m = elem k n) \<longrightarrow> m = n"
by (metis (poly_guards_query) elem_ext)

lemma ZFC_null_set:
  "\<exists>x. \<not> (\<exists>k. elem k x)"
by (metis null)

definition pair :: "nat \<Rightarrow> nat \<Rightarrow> nat"
 where "pair m n \<equiv> if m = n then 2^m else 2^m + 2^n"

lemma pair_sym:
 "pair m n = pair n m"
by (metis add.commute pair_def)

lemma nat_diff:
 "EX k::nat. m = n + k \<or> n = m + k"
by presburger

lemma nat_ne_diff:
 "m \<noteq> n \<Longrightarrow> (EX k::nat. m = n + Suc k) \<or> (EX k::nat. n = m + Suc k)"
by presburger

lemma pow_div:
 "0 < (k::nat) \<Longrightarrow> (2::nat) ^ (m + k) div 2 ^ m = 2 ^ k"
by (metis Suc_eq_plus1 add.commute div_mult_self2_is_id nat_zero_less_power_iff neq0_conv one_add_one power_add zero_less_Suc)

lemma elem_pair_left:
 "elem m (pair m n)"
apply (insert nat_diff[of "m" "n"])
apply (auto simp add: elem_def pair_def)
by (metis Suc_eq_plus1 div_mult_self2_is_id even_numeral_nat even_power_nat mult.commute nat_zero_less_power_iff neq0_conv one_add_one power_add zero_less_Suc)

lemma elem_pair_right:
 "elem n (pair m n)"
by (metis elem_pair_left pair_sym)

lemma pow_div_0:
 "0 < (k::nat) \<Longrightarrow> (2::nat) ^ m div 2 ^ (m + k) = 0"
by simp

lemma elem_pair_1:
 "elem k (2 ^ n) \<Longrightarrow> k = n"
apply (auto simp add: elem_def)
apply (rule ccontr)
apply (drule nat_ne_diff)
apply (erule disjE)
apply (erule exE)
apply clarify
apply (subst (asm) pow_div_0)
apply simp
apply simp
apply clarify
apply (subst (asm) pow_div)
by auto

lemma elem_plus:
  "elem k s = elem (k + n) (s * 2 ^ n)"
apply (induction "n")
by simp_all

lemma nat_le_diff:
 "m \<le> n \<Longrightarrow> EX k::nat. n = k + m"
by presburger

lemma elem_minus:
  "n \<le> k \<Longrightarrow> elem (k - n) s = elem k (s * 2 ^ n)"
apply (drule nat_le_diff)
apply clarify
apply (subst elem_plus[symmetric])
by simp

lemma elem_size:
 "m < 2 ^ k \<Longrightarrow> \<not> elem k m"
by (simp add: elem_def)

lemma pow_succ:
 "2 * (n::nat) + 2 ^ Suc m = 2 * (n + 2 ^ m)"
by simp

lemma suc_div:
  "Suc (2 * n) div 2 = n"
by simp

lemma elem_plus_pow:
 "\<And>n k. k < n \<Longrightarrow> elem k (m + 2 ^ n) = elem k m"
apply (induction "m" rule: ind_k2)
apply simp_all
apply (metis elem_pair_1 less_not_refl null)
apply (case_tac "k")
apply simp
apply (metis elem2k even_mult_two_ex even_numeral_nat even_power_nat even_sum_nat)
apply (case_tac "na")
apply simp
apply clarify
apply (subst pow_succ)
apply (subst elem2k)+
apply simp
apply (case_tac "na")
apply simp
apply simp
apply (case_tac "k")
apply (simp add: elemZero)
apply clarify
apply (subst elemSuc)+
apply (subst suc_div)
by (metis comm_semiring_1_class.normalizing_semiring_rules(27) pow_succ suc_div)

lemma elem_plus_n_pow:
 "\<And>m. k < n \<Longrightarrow> elem k (m + s * 2 ^ n) = elem k m"
apply (induction "s")
apply simp_all
apply (subst add.assoc[symmetric])
by (metis elem_plus_pow)

lemma pow_less:
 "n \<le> (k::nat) \<Longrightarrow> (m::nat) < 2 ^ n \<Longrightarrow> m < 2 ^ k"
proof -
  assume a1: "m < 2 ^ n"
  assume "n \<le> k"
  hence "\<not> (2\<Colon>nat) ^ k < 2 ^ n" by (metis (no_types) nat_power_less_imp_less not_less zero_less_numeral)
  thus "m < 2 ^ k" using a1 by linarith
qed

lemma ind_div2:
 "P 0 \<Longrightarrow> (\<And>n. P (n div 2) \<Longrightarrow> P n) \<Longrightarrow> P (x::nat)"
apply (induct_tac "x" rule: nat_less_induct)
by (metis Suc_eq_plus1 Suc_leI lessI monoid_add_class.add.left_neutral nat_div2 neq0_conv one_add_one)

lemma elem_pair_3x:
  "((m::nat) + s * (2 * 2 ^ n)) div 2 = m div 2 + s * 2 ^ n"
by simp

lemma elem_pair_2x:
 "\<And>m. m < 2 ^ n \<Longrightarrow> elem (k + n) (m + s * 2 ^ n) = elem k s"
apply (induct "n")
apply simp
apply simp_all
apply (case_tac "m div 2 < 2 ^ n")
apply (metis elem_pair_3x)
by simp

lemma elem_pair_4x:
 "m < 2 ^ n \<Longrightarrow> elem k (m + s * 2 ^ n) \<Longrightarrow> elem k m \<or> elem (k - n) s"
apply (case_tac "k < n")
apply (metis elem_plus_n_pow)
apply (rule disjI2)
by (metis Nat.add_diff_inverse comm_semiring_1_class.normalizing_semiring_rules(24) elem_pair_2x)

lemma sym_lt:
   "\<And>(P::nat \<Rightarrow> nat \<Rightarrow> bool). (!m n. P m n = P n m) \<Longrightarrow> (!m n. m < n \<longrightarrow> P m n) \<Longrightarrow> (!m. P m m) \<Longrightarrow> P x y"
by (metis nat_neq_iff)

lemma elem_pair_5x:
 "!k. elem k (pair m n) \<longrightarrow> k = m \<or> k = n"
apply (rule sym_lt)
apply (metis pair_sym)
apply (simp add: pair_def)
apply auto
apply (subgoal_tac "2 ^ m < 2 ^ n")
apply (drule_tac s = 1 in elem_pair_4x)
apply simp
apply simp
apply (metis Nat.add_diff_inverse One_nat_def elem_pair_1 elem_plus_pow monoid_add_class.add.right_neutral power_0)
apply simp
by (metis elem_pair_1 pair_def)

lemma elem_pair:
 "elem k (pair m n) = (k = m \<or> k = n)"
by (metis elem_pair_5x elem_pair_left elem_pair_right)

lemma ZFC_pairs:
 "\<exists>z. \<forall>w. elem w z = (w = x \<or> w = y)"
by (metis elem_pair)

definition union_sing :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "union_sing n x \<equiv> if elem n x then x else x + 2 ^ n"

lemma elem_union_sing_1 :
 "!x. elem n (union_sing n x)"
apply (simp add: union_sing_def)
apply (induct_tac "n")
apply (metis Suc_eq_plus1 div_by_1 elem_def even_Suc power_0)
apply simp
by (metis comm_semiring_1_class.normalizing_semiring_rules(24))

lemma elem_union_sing_2 :
 "!k x. k \<noteq> n \<longrightarrow> elem k (union_sing n x) = elem k x"
apply (induct_tac "n")
apply (intro allI impI)
apply (simp add: union_sing_def)
apply (intro impI)
apply (case_tac "k")
apply simp
apply simp
apply (metis Suc_eq_plus1 div_by_1 elem_def lemma_even_div2 power_0)
apply (intro allI impI)
apply (simp add: union_sing_def)
apply clarify
apply (case_tac "k")
apply (simp add: elemZero)
apply simp
apply (thin_tac "k = Suc nat")
apply (subgoal_tac "elem nat (x div 2) =
                    elem nat (if elem n (x div 2) then (x div 2)
                              else (x div 2) + 2 ^ n)")
apply (erule ssubst)
apply simp
apply (metis comm_semiring_1_class.normalizing_semiring_rules(24))
by blast

lemma elem_union_sing :
 "elem k (union_sing n x) = (k = n \<or> elem k x)"
apply (case_tac "k = n")
apply (metis elem_union_sing_1)
by (metis elem_union_sing_2)

lemma elem_size_2:
 "elem k m \<Longrightarrow> 2 ^ k \<le> m"
by (metis elem_size not_less)

lemma pow_size:
 "k < 2 ^ k"
apply (induct_tac "k")
by auto

lemma elem_size_3:
 "elem k m \<Longrightarrow> k < m"
by (metis elem_size less_le_trans not_less pow_size)

fun elem_map_1 :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
 "elem_map_1 P n 0 = (if elem 0 n
                then union_sing (P 0) 0
                else 0)" |
 "elem_map_1 P n (Suc m) = (let r = elem_map_1 P n m in if elem (Suc m) n
                      then union_sing (P (Suc m)) r
                      else r)"

definition elem_map :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
 "elem_map P n \<equiv> elem_map_1 P n n"

lemma elem_elem_map_1:
 "!k n. elem k (elem_map_1 P n m) = (\<exists>x. elem x n \<and> x \<le> m \<and> P x = k)"
apply (induct_tac "m")
apply (simp add: elem_union_sing)
apply (metis null)
apply (intro allI)
apply (simp del: elemSuc)
apply (case_tac "elem (Suc n) na")
apply (simp del: elemSuc add: elem_union_sing)
apply (auto simp del: elemSuc)
apply (metis le_Suc_eq)
by (metis le_Suc_eq)

lemma elem_elem_map:
 "elem k (elem_map P n) = (\<exists>x. elem x n \<and> P x = k)"
apply (simp add: elem_map_def)
by (metis (poly_guards_query) Suc_leI Suc_le_mono elem_elem_map_1 elem_size_3 le_Suc_eq)

definition img :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
 "img P n \<equiv> elem_map (\<lambda>n. (SOME m. (P n m))) n"

lemma elem_img:
 "(\<forall>x. \<exists>!y. P x y) \<Longrightarrow>
  elem r (img P w) = (\<exists>s. elem s w \<and> P s r)"
apply (simp add: img_def elem_elem_map)
by (metis someI)

lemma ZFC_replacement:
 "(\<forall>x. \<exists>!y. P x y) \<longrightarrow>
  (\<forall>w. \<exists>v. \<forall>r. elem r v = (\<exists>s. elem s w \<and> P s r))"
apply clarify
apply (rule_tac x="img P w" in exI)
by (simp add: elem_img)

lemma notempty_1:
 "n \<noteq> 0 \<Longrightarrow> \<exists>x. elem x n"
by (metis null_ext)

lemma notempty_4:
 "((na::nat) - 2 * 2 ^ n) div 2 = (na div 2) - 2 ^ n"
by simp

lemma notempty_3:
 "\<forall>n. elem x n \<longrightarrow> \<not> elem x (n - 2 ^ x)"
apply (induct_tac "x")
apply (metis (poly_guards_query) Nat.add_diff_inverse div_by_1 elem_def elem_size even_sum_nat odd_1_nat power_0)
apply simp
by (metis notempty_4)

lemma notempty_2:
 "elem x n \<Longrightarrow> \<exists>y. \<not>elem x y \<and> n = union_sing x y"
apply (simp add: union_sing_def)
apply (rule_tac x="n - 2 ^ x" in exI)
apply auto
apply (metis notempty_3)
by (metis Nat.add_diff_inverse comm_semiring_1_class.normalizing_semiring_rules(24) elem_size)

lemma notempty:
 "n \<noteq> 0 \<Longrightarrow> \<exists>x y. ~elem x y \<and> n = union_sing x y"
by (metis (poly_guards_query) notempty_2 null_ext)

lemma size_union_sing:
 "\<not>elem x y \<Longrightarrow> y < union_sing x y"
by (simp add: union_sing_def)

lemma ind_sing:
 "P 0 \<Longrightarrow> (\<And>n x. \<not>elem n x \<Longrightarrow> P x \<Longrightarrow> P (union_sing n x)) \<Longrightarrow> P (x::nat)"
apply (induct_tac "x" rule: nat_less_induct)
apply (case_tac "n = 0")
apply simp
apply (drule_tac notempty)
apply clarify
by (metis size_union_sing)

definition power_set :: "nat \<Rightarrow> nat" where
  "power_set x \<equiv> (\<Prod>k\<in>{m. elem m x}. 1 + 2 ^ 2 ^ k)"

lemma power_set_zero:
 "power_set 0 = 1"
by (simp add: power_set_def null)

lemma insert_union_sing:
 "{m. elem m (union_sing n x)} = insert n {m. elem m x}"
apply (simp add: elem_union_sing)
by auto

lemma finite_elem:
 "finite {m. elem m x}"
apply (subgoal_tac "finite {..<x}")
apply (erule rev_finite_subset)
apply auto
by (metis elem_size_3)

lemma power_set_union_sing:
  "\<not> elem n x \<Longrightarrow> power_set (union_sing n x) = power_set x * (1 + 2 ^ (2 ^ n))"
apply (simp add: power_set_def insert_union_sing)
apply (subst Groups_Big.comm_monoid_mult_class.setprod.insert_remove)
apply (metis finite_elem)
by simp

lemma union_sing_swap:
  "union_sing x (union_sing x1 y1) = union_sing x1 (union_sing x y1)"
apply (rule elem_ext)
by (metis elem_union_sing)

lemma notempty_max:
 "n \<noteq> 0 \<Longrightarrow> \<exists>x y. (\<forall>z. elem z y \<longrightarrow> z < x) \<and> n = union_sing x y"
apply (induction "n" rule: nat_less_induct)
apply (drule_tac notempty)
apply clarify
apply (case_tac " \<forall>z. elem z y \<longrightarrow> z < x")
apply auto[1]
apply auto
apply (subgoal_tac "\<exists>x1 y1. (\<forall>z. elem z y1 \<longrightarrow> z < x1) \<and> y = union_sing x1 y1")
apply clarify
apply (rule_tac x = "x1" in exI)
apply (rule_tac x = "union_sing x y1" in exI)
apply safe
apply (simp add: elem_union_sing)
apply auto[1]
apply (metis union_sing_swap)
apply (subgoal_tac "y \<noteq> 0")
apply (subgoal_tac "y < union_sing x y")
apply auto[1]
apply (rule size_union_sing)
apply simp
apply (rule ccontr)
by (simp add: null)

lemma ind_sing_max:
 "P 0 \<Longrightarrow> (\<And>n x. (!y. elem y x \<longrightarrow> y < n) \<Longrightarrow> P x \<Longrightarrow> P (union_sing n x)) \<Longrightarrow> P (x::nat)"
apply (induct_tac "x" rule: nat_less_induct)
apply (case_tac "n = 0")
apply simp
apply (drule_tac notempty_max)
apply clarify
by (metis less_not_refl size_union_sing)

lemma elem_power_set_2:
  "elem n (k + 2 ^ n) \<Longrightarrow> elem w (k + 2 ^ n) \<Longrightarrow> \<not> elem w k \<Longrightarrow> w = n"
by (metis add_diff_cancel_right' elem_union_sing notempty_3 union_sing_def)

lemma elem_power_set_1:
  "elem n k \<Longrightarrow> elem w k \<Longrightarrow> \<not> elem w (k - 2 ^ n) \<Longrightarrow> w = n"
by (metis add.commute elem_power_set_2 elem_size_2 le_add_diff_inverse)

lemma power_set_size_2:
 "(z::nat) \<le> 2 ^ x \<Longrightarrow> x \<le> m \<Longrightarrow> z \<le> 2 ^ m"
apply (induction "z")
apply auto
by (metis Suc_1 le_antisym lessI not_less_eq_eq power_increasing_iff)

lemma power_set_size_1:
  "x \<le> 2 ^ n \<Longrightarrow>
   (z::nat) \<le> 2 ^ x \<Longrightarrow>
   z * (1 + 2 ^ 2 ^ n) \<le> (1 + z) * 2 ^ 2 ^ n"
by (auto simp add: power_set_size_2)

lemma power_set_size_4:
 "(z::nat) \<le> x \<Longrightarrow>
  b \<le> (1+z) * a \<Longrightarrow>
  b \<le> (1+x) * a"
proof -
  assume a1: "b \<le> (1 + z) * a"
  assume a2: "z \<le> x"
  have "\<And>x\<^sub>1. b \<le> x\<^sub>1 + a * (1 + z)" using a1 by (simp add: mult.commute trans_le_add2)
  thus "b \<le> (1 + x) * a" using a2 by (metis Nat.le_iff_add add.assoc add.commute distrib_left mult.commute)
qed

lemma power_set_size_3:
 "(z::nat) \<le> 2 ^ x \<Longrightarrow>
   x  \<le> 2 ^ n \<Longrightarrow>
   z * (1 + 2 ^ 2 ^ n) \<le> (1 + 2 ^ x) * 2 ^ 2 ^ n"
by (metis power_set_size_1 power_set_size_4)

lemma elem_size_bound:
 "!n. (\<forall>y. elem y x \<longrightarrow> y < n) \<longrightarrow>
      x + 1 \<le> 2 ^ n"
apply (induct_tac "x" rule: ind_div2)
apply auto
apply (subst (asm) elemSuc[symmetric])
apply (case_tac "na")
apply auto
apply (metis null_ext)
apply (subgoal_tac "2 * Suc (n div 2) \<le> 2 * 2 ^ nat")
apply simp
apply (subst (asm) elemSuc[symmetric])
by (metis Suc_less_eq mult_le_cancel1)

lemma power_set_size:
 "power_set x + 1 \<le> 2 ^ (x + 1)"
apply (induct_tac "x" rule: ind_sing_max)
apply (simp add: power_set_zero)
apply (subst power_set_union_sing)
apply auto[1]
apply (subgoal_tac "x + 1 \<le> 2 ^ n")
apply (drule power_set_size_3)
apply assumption
apply (auto simp add: union_sing_def)
apply (metis (erased, hide_lams) Suc_eq_plus1 add.assoc add.left_commute comm_semiring_1_class.normalizing_semiring_rules(24) mult_Suc_right power_Suc power_add)
by (metis Suc_eq_plus1 elem_size_bound)

lemma elem_mul_2k:
 "elem k (s * 2 ^ n) \<Longrightarrow> elem (k - n) s"
by (metis elem_pair_4x monoid_add_class.add.left_neutral mult_0_right neq0_conv null)

lemma div_pow_minus:
 "\<And>x. (x::nat) \<le> (k::nat) \<Longrightarrow> (2::nat) ^ k div 2 ^ x = 2 ^ (k - x)"
apply (induction "k")
apply auto
apply (case_tac "x")
by auto


lemma div_pow_minus_mult:
 "\<And>x. (x::nat) \<le> (k::nat) \<Longrightarrow> s * (2::nat) ^ k div 2 ^ x = s * 2 ^ (k - x)"
apply (induction "k")
apply auto
apply (case_tac "x")
by auto

lemma size_mul_2k:
 "elem x (m * 2 ^ k) \<Longrightarrow> k \<le> x"
apply (rule ccontr)
apply (simp add: elem_def)
apply (subst (asm) div_pow_minus_mult)
by auto

lemma mul_2k:
  "!w. elem w x \<longrightarrow> \<not> elem k w \<Longrightarrow>
   x * 2 ^ 2 ^ k = elem_map (union_sing k) x"
apply (rule elem_ext)
apply (simp add: elem_elem_map)
apply auto
apply (rule_tac x = "ka - 2 ^ k" in exI)
apply rule
apply (metis elem_mul_2k)
apply (simp add: union_sing_def)
apply auto
apply (metis elem_mul_2k)
apply (metis comm_semiring_1_class.normalizing_semiring_rules(24) le_add_diff_inverse size_mul_2k)
apply (subst elem_minus[symmetric])
apply (metis elem_size_2 elem_union_sing_1)
by (metis add_diff_cancel_right' union_sing_def)

lemma not_odd_div:
 "\<not>(odd n \<and> odd m) \<Longrightarrow> (n + m) div 2 = (n div 2) + (m div 2)"
apply (subgoal_tac "\<And>m n. even m \<Longrightarrow> (n + m) div 2 = n div 2 + m div 2")
apply auto[1]
apply (metis add.commute)
by (metis add.commute div2even div_by_0 div_mult_self2 monoid_add_class.add.right_neutral)

lemma disjunct_union:
 "\<And>k n. \<forall>x. elem x m \<longrightarrow> \<not> elem x n \<Longrightarrow>
      elem k (m + n) = (elem k m \<or> elem k n)"
apply (induction "m" rule: ind_div2)
apply (metis monoid_add_class.add.left_neutral null)
apply (case_tac "k")
apply clarify
apply (metis div_by_1 elem_def even_sum_nat power_0)
apply clarify
apply simp
apply (subst not_odd_div)
apply (metis div_by_1 elem_def power_0)
apply (subgoal_tac " \<forall>x. elem x (n div 2) \<longrightarrow> \<not> elem x (na div 2)")
apply auto
by (metis elemSuc)

lemma elem_power_set:
 "!k. elem k (power_set n) = (\<forall>w. elem w k \<longrightarrow> elem w n)"
apply (induct_tac "n" rule: ind_sing_max)
apply (metis elem_pair_1 null null_ext power_0 power_set_zero zero_neq_one)
apply clarify
apply (subst power_set_union_sing)
apply auto[1]
apply simp
apply (subst mul_2k)
apply auto[1]
apply (subst disjunct_union)
apply (metis elem_elem_map elem_union_sing_1 less_not_refl)
apply (simp add: elem_elem_map)
apply auto
apply (metis elem_union_sing)
apply (metis elem_union_sing)
by (metis elem_union_sing notempty_2)

lemma ZFC_power_set:
 "\<forall>x. \<exists>y. \<forall>z. elem z y = (\<forall>w. elem w z \<longrightarrow> elem w x)"
by (metis (poly_guards_query) elem_power_set)

definition set_filter :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat" where
 "set_filter P n \<equiv> (elem_map (\<lambda> k. if P k then Suc k else 0) n) div 2"

lemma elem_set_filter:
 "elem k (set_filter P n) = (P k \<and> elem k n)"
apply (simp add: set_filter_def)
apply (subst elemSuc[symmetric])
apply (subst elem_elem_map)
by auto

definition set_diff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "set_diff m n \<equiv> set_filter (\<lambda> k. \<not> elem k n) m"

lemma elem_set_diff:
 "elem k (set_diff m n) = (elem k m \<and> \<not> elem k n)"
by (metis elem_set_filter set_diff_def)

definition set_intersect :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "set_intersect m n \<equiv> set_diff m (set_diff m n)"

lemma elem_set_intersect:
 "elem k (set_intersect m n) = (elem k m \<and> elem k n)"
by (metis (poly_guards_query) elem_set_diff set_intersect_def)

definition set_union :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "set_union m n \<equiv> (set_diff m n) + n"

lemma elem_set_union:
  "elem k (set_union m n) = (elem k m \<or> elem k n)"
apply (simp add: set_union_def)
apply (subst disjunct_union)
apply (metis elem_set_diff)
by (metis elem_set_diff)

fun sum_set_1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "sum_set_1 n 0 = 0" |
 "sum_set_1 n (Suc m) = (let r = sum_set_1 n m in
                      if elem (Suc m) n
                      then set_union (Suc m) r
                      else r)"

definition sum_set :: "nat \<Rightarrow> nat" where
 "sum_set n \<equiv> sum_set_1 n n"

lemma elem_sum_set_1:
 "!k n. elem k (sum_set_1 n m) = (\<exists>x. elem x n \<and> x \<le> m \<and> elem k x)"
apply (induct_tac "m")
apply (simp add: elem_union_sing)
apply (metis null)
apply (intro allI)
apply (simp del: elemSuc)
apply (case_tac "elem (Suc n) na")
apply (simp del: elemSuc add: elem_set_union)
apply (auto simp del: elemSuc)
apply (metis le_Suc_eq)
by (metis le_Suc_eq)

lemma elem_sum_set:
 "elem k (sum_set n) = (\<exists>x. elem x n \<and> elem k x)"
apply (simp add: sum_set_def)
by (metis (poly_guards_query) Suc_leI Suc_le_mono elem_sum_set_1 elem_size_3 le_Suc_eq)

lemma ZFC_sum_set:
 "\<forall>x. \<exists>y. \<forall>u. elem u y = (\<exists>z. elem z x \<and> elem u z)"
by (metis elem_sum_set)

lemma disjoint_intersect:
 "(set_intersect v u = 0) = (\<not>(\<exists>w. elem w v \<and> elem w u))"
by (metis elem_set_intersect null null_ext)

lemma set_intersect_sym:
 "set_intersect u v = set_intersect v u"
by (metis elem_set_intersect elem_ext)

lemma notempty_eqv:
 "(n \<noteq> 0) = (\<exists>w. elem w n)"
by (metis null null_ext)

fun max_elem_1 :: "nat => nat => nat" where
 "max_elem_1 m 0 = 0" |
 "max_elem_1 m (Suc n) = (if elem (Suc n) m
                          then (Suc n)
                          else max_elem_1 m n)"

definition max_elem :: "nat \<Rightarrow> nat" where
 "max_elem m \<equiv> max_elem_1 m m"

lemma elem_max_elem_1:
 "(\<exists>x. elem x m \<and> x \<le> k) \<Longrightarrow>
  elem (max_elem_1 m k) m"
apply (induction "k")
apply simp
by (metis le_Suc_eq max_elem_1.simps(2))

lemma max_elem_1_max:
 "elem w m \<Longrightarrow>
  w \<le> k \<Longrightarrow>
  w \<le> max_elem_1 m k"
apply (induction "k")
apply simp
by (metis le_Suc_eq max_elem_1.simps(2))

lemma elem_max_elem:
 "m \<noteq> 0 \<Longrightarrow>
  elem (max_elem m) m"
apply (subst (asm) notempty_eqv)
apply (simp add:  max_elem_def)
apply clarify
by (metis (poly_guards_query) Suc_leI Suc_le_mono elem_max_elem_1 elem_size_3 le_Suc_eq)

lemma max_elem_max:
 "elem w m \<Longrightarrow> w \<le> max_elem m"
by (metis Suc_leD Suc_leI elem_size_3 max_elem_1_max max_elem_def)

definition choice :: "nat \<Rightarrow> nat" where
 "choice m \<equiv> elem_map max_elem m"

lemma elem_choice_1:
 "\<forall>u. elem u x \<longrightarrow>
           (\<exists>w. elem w u) \<and>
           (\<forall>v. elem v x \<and> v \<noteq> u \<longrightarrow> (\<forall>w. elem w v \<longrightarrow> \<not> elem w u)) \<Longrightarrow>
       elem u x \<Longrightarrow>
       elem (max_elem w) u \<Longrightarrow> elem w x \<Longrightarrow> w = u"
apply (subgoal_tac "elem (max_elem w) w")
apply auto[1]
by (metis elem_max_elem null)

lemma elem_choice:
 " (\<forall>u. elem u x \<longrightarrow>
            (\<exists>w. elem w u) \<and>
            (\<forall>v. elem v x \<and> v \<noteq> u \<longrightarrow> \<not> (\<exists>w. elem w v \<and> elem w u))) \<Longrightarrow>
        (\<forall>u. elem u x \<longrightarrow> (\<exists>!w. elem w u \<and> elem w (choice x)))"
apply (simp add: choice_def elem_elem_map)
apply safe
apply (metis (poly_guards_query) elem_max_elem_1 elem_size_3 max_elem_def nat_le_linear not_less)
apply (subgoal_tac "xa = u")
apply (subgoal_tac "xaa = u")
apply simp
apply (erule elem_choice_1)
apply simp
apply simp
apply simp
apply (erule elem_choice_1)
by simp

lemma ZFC_CAC:
 " \<forall>x. (\<forall>u. elem u x \<longrightarrow>
            (\<exists>w. elem w u) \<and>
            (\<forall>v. elem v x \<and> v \<noteq> u \<longrightarrow> \<not> (\<exists>w. elem w v \<and> elem w u))) \<longrightarrow>
        (\<exists>y. \<forall>u. elem u x \<longrightarrow> (\<exists>!w. elem w u \<and> elem w y))"
apply (intro allI impI)
apply (rule_tac x = "choice x" in exI)
apply (rule elem_choice)
by metis

end
