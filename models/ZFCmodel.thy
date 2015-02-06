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

lemma ZFC_extensionality:
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

end
