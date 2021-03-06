theory Interval_Integral
  imports Probability
begin

lemma tendsto_at_within_iff_tendsto_nhds:
  "(g ---> g l) (at l within S) \<longleftrightarrow> (g ---> g l) (inf (nhds l) (principal S))"
  unfolding tendsto_def eventually_at_filter eventually_inf_principal
  by (intro ext all_cong imp_cong) (auto elim!: eventually_elim1)

lemma tendsto_at_iff_sequentially:
  fixes f :: "'a :: first_countable_topology \<Rightarrow> _"
  shows "(f ---> a) (at x within s) \<longleftrightarrow> (\<forall>X. (\<forall>i. X i \<in> s - {x}) \<longrightarrow> X ----> x \<longrightarrow> ((f \<circ> X) ----> a))"
  unfolding filterlim_def[of _ "nhds a"] le_filter_def eventually_filtermap at_within_def eventually_nhds_within_iff_sequentially comp_def
  by metis

lemma eventually_at_right':
  fixes x :: "'a :: linorder_topology"
  assumes gt_ex: "x < y"
  shows "eventually P (at_right x) \<longleftrightarrow> (\<exists>b. x < b \<and> (\<forall>z. x < z \<and> z < b \<longrightarrow> P z))"
  unfolding eventually_at_topological
proof safe
  note gt_ex
  moreover fix S assume "open S" "x \<in> S" note open_right[OF this, of y]
  moreover assume "\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {x<..} \<longrightarrow> P s"
  ultimately show "\<exists>b>x. \<forall>z. x < z \<and> z < b \<longrightarrow> P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b assume "x < b" "\<forall>z. x < z \<and> z < b \<longrightarrow> P z"
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>xa\<in>S. xa \<noteq> x \<longrightarrow> xa \<in> {x<..} \<longrightarrow> P xa)"
    by (intro exI[of _ "{..< b}"]) auto
qed

lemma eventually_at_left':
  fixes x :: "'a :: linorder_topology"
  assumes lt_ex: "y < x"
  shows "eventually P (at_left x) \<longleftrightarrow> (\<exists>b. x > b \<and> (\<forall>z. b < z \<and> z < x \<longrightarrow> P z))"
  unfolding eventually_at_topological
proof safe
  note lt_ex
  moreover fix S assume "open S" "x \<in> S" note open_left[OF this, of y]
  moreover assume "\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {..<x} \<longrightarrow> P s"
  ultimately show "\<exists>b<x. \<forall>z. b < z \<and> z < x \<longrightarrow> P z"
    by (auto simp: subset_eq Ball_def)
next
  fix b assume "b < x" "\<forall>z. b < z \<and> z < x \<longrightarrow> P z"
  then show "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>s\<in>S. s \<noteq> x \<longrightarrow> s \<in> {..<x} \<longrightarrow> P s)"
    by (intro exI[of _ "{b <..}"]) auto
qed

lemma eventually_at_right_top: "at_right (top::_::{order_top, linorder_topology}) = bot"
  unfolding filter_eq_iff eventually_at_topological by auto

lemma eventually_at_left_bot: "at_left (bot::_::{order_bot, linorder_topology}) = bot"
  unfolding filter_eq_iff eventually_at_topological by auto

definition "einterval a b = {x. a < ereal x \<and> ereal x < b}"

lemma einterval_eq[simp]:
  shows einterval_eq_Icc: "einterval (ereal a) (ereal b) = {a <..< b}"
    and einterval_eq_Ici: "einterval (ereal a) \<infinity> = {a <..}"
    and einterval_eq_Iic: "einterval (- \<infinity>) (ereal b) = {..< b}"
    and einterval_eq_UNIV: "einterval (- \<infinity>) \<infinity> = UNIV"
  by (auto simp: einterval_def)

lemma einterval_iff: "x \<in> einterval a b \<longleftrightarrow> a < ereal x \<and> ereal x < b"
  by (simp add: einterval_def)

lemma open_Collect_conj: assumes "open {x. P x}" "open {x. Q x}" shows "open {x. P x \<and> Q x}"
  using open_Int[OF assms] by (simp add: Int_def)

lemma open_einterval[simp]: "open (einterval a b)"
  by (cases a b rule: ereal2_cases)
     (auto simp: einterval_def intro!: open_Collect_conj open_Collect_less continuous_on_intros)

lemma filterlim_sup1: "(LIM x F. f x :> G1) \<Longrightarrow> (LIM x F. f x :> (sup G1 G2))"
 unfolding filterlim_def by (auto intro: le_supI1)

lemma eventually_sequentially_Suc: "eventually (\<lambda>i. P (Suc i)) sequentially \<longleftrightarrow> eventually P sequentially"
  apply (auto simp: eventually_sequentially)
  apply (metis Suc_le_D Suc_le_mono)
  apply (metis le_Suc_eq)
  done

lemma filterlim_sequentially_Suc:
  "(LIM x sequentially. f (Suc x) :> F) \<longleftrightarrow> (LIM x sequentially. f x :> F)"
  unfolding filterlim_def le_filter_def eventually_filtermap
  by (subst eventually_sequentially_Suc) simp

lemma ereal_incseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "incseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> b"
proof (cases b)
  case PInf
  with `a < b` have "a = -\<infinity> \<or> (\<exists>r. a = ereal r)"
    by (cases a) auto
  moreover have " (\<lambda>x. ereal (real (Suc x))) ----> \<infinity>"
    using natceiling_le_eq by (subst LIMSEQ_Suc_iff) (auto simp: Lim_PInfty)
  moreover have "\<And>r. (\<lambda>x. ereal (r + real (Suc x))) ----> \<infinity>"
    apply (subst LIMSEQ_Suc_iff)
    apply (subst Lim_PInfty)
    apply (metis add_commute diff_le_eq natceiling_le_eq ereal_less_eq(3))
    done
  ultimately show thesis
    by (intro that[of "\<lambda>i. real a + Suc i"])
       (auto simp: incseq_def PInf)
next
  case (real b')
  def d \<equiv> "b' - (if a = -\<infinity> then b' - 1 else real a)"
  with `a < b` have a': "0 < d"
    by (cases a) (auto simp: real)
  moreover
  have "\<And>i r. r < b' \<Longrightarrow> (b' - r) * 1 < (b' - r) * real (Suc (Suc i))"
    by (intro mult_strict_left_mono) auto
  with `a < b` a' have "\<And>i. a < ereal (b' - d / real (Suc (Suc i)))"
    by (cases a) (auto simp: real d_def field_simps)
  moreover have "(\<lambda>i. b' - d / Suc (Suc i)) ----> b'"
    apply (subst filterlim_sequentially_Suc)
    apply (subst filterlim_sequentially_Suc)
    apply (rule tendsto_eq_intros)
    apply (auto intro!: tendsto_divide_0[OF tendsto_const] filterlim_sup1
                simp: at_infinity_eq_at_top_bot filterlim_real_sequentially)
    done
  ultimately show thesis
    by (intro that[of "\<lambda>i. b' - d / Suc (Suc i)"])
       (auto simp add: real incseq_def divide_pos_pos mult_pos_pos intro!: divide_left_mono)
qed (insert `a < b`, auto)

lemma ereal_decseq_approx:
  fixes a b :: ereal
  assumes "a < b"
  obtains X :: "nat \<Rightarrow> real" where 
    "decseq X" "\<And>i. a < X i" "\<And>i. X i < b" "X ----> a"
proof -
  have "-b < -a" using `a < b` by simp
  from ereal_incseq_approx[OF this] guess X .
  then show thesis
    apply (intro that[of "\<lambda>i. - X i"])
    apply (auto simp add: uminus_ereal.simps[symmetric] decseq_def incseq_def
                simp del: uminus_ereal.simps)
    apply (metis ereal_minus_less_minus ereal_uminus_uminus ereal_Lim_uminus)+
    done
qed

lemma einterval_Icc_approximation:
  fixes a b :: ereal
  assumes "a < b"
  obtains u l :: "nat \<Rightarrow> real" where 
    "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
proof -
  from dense[OF `a < b`] obtain c where "a < c" "c < b" by safe
  from ereal_incseq_approx[OF `c < b`] guess u . note u = this
  from ereal_decseq_approx[OF `a < c`] guess l . note l = this
  { fix i from less_trans[OF `l i < c` `c < u i`] have "l i < u i" by simp }
  have "einterval a b = (\<Union>i. {l i .. u i})"
  proof (auto simp: einterval_iff)
    fix x assume "a < ereal x" "ereal x < b"
    have "eventually (\<lambda>i. ereal (l i) < ereal x) sequentially"
      using l(4) `a < ereal x` by (rule order_tendstoD)
    moreover 
    have "eventually (\<lambda>i. ereal x < ereal (u i)) sequentially"
      using u(4) `ereal x< b` by (rule order_tendstoD)
    ultimately have "eventually (\<lambda>i. l i < x \<and> x < u i) sequentially"
      by eventually_elim auto
    then show "\<exists>i. l i \<le> x \<and> x \<le> u i"
      by (auto intro: less_imp_le simp: eventually_sequentially)
  next
    fix x i assume "l i \<le> x" "x \<le> u i" 
    with `a < ereal (l i)` `ereal (u i) < b`
    show "a < ereal x" "ereal x < b"
      by (auto simp del: ereal_less_eq(3) simp add: ereal_less_eq(3)[symmetric])
  qed
  show thesis
    by (intro that) fact+
qed

lemma filtermap_nhds_open_map:
  assumes cont: "isCont f a" and open_map: "\<And>S. open S \<Longrightarrow> open (f`S)"
  shows "filtermap f (nhds a) = nhds (f a)"
  unfolding filter_eq_iff
proof safe
  fix P assume "eventually P (filtermap f (nhds a))"
  then guess S unfolding eventually_filtermap eventually_nhds ..
  then show "eventually P (nhds (f a))"
    unfolding eventually_nhds by (intro exI[of _ "f`S"]) (auto intro!: open_map)
qed (metis filterlim_iff tendsto_at_iff_tendsto_nhds isCont_def eventually_filtermap cont)

lemma filtermap_mono_strong: "inj f \<Longrightarrow> filtermap f F \<le> filtermap f G \<longleftrightarrow> F \<le> G"
  apply (auto intro!: filtermap_mono) []
  apply (auto simp: le_filter_def eventually_filtermap)
  apply (erule_tac x="\<lambda>x. P (inv f x)" in allE)
  apply auto
  done

lemma filtermap_eq_strong: "inj f \<Longrightarrow> filtermap f F = filtermap f G \<longleftrightarrow> F = G"
  by (simp add: filtermap_mono_strong eq_iff)

lemma ereal_all_split: "\<And>P. (\<forall>x::ereal. P x) \<longleftrightarrow> P \<infinity> \<and> (\<forall>x. P (ereal x)) \<and> P (-\<infinity>)"
  by (metis ereal_cases)

lemma ereal_ex_split: "\<And>P. (\<exists>x::ereal. P x) \<longleftrightarrow> P \<infinity> \<or> (\<exists>x. P (ereal x)) \<or> P (-\<infinity>)"
  by (metis ereal_cases)

lemma nhds_ereal: "nhds (ereal r) = filtermap ereal (nhds r)"
  by (simp add: filtermap_nhds_open_map open_ereal continuous_at_of_ereal)

lemma at_ereal: "at (ereal r) = filtermap ereal (at r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma at_left_ereal: "at_left (ereal r) = filtermap ereal (at_left r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma at_right_ereal: "at_right (ereal r) = filtermap ereal (at_right r)"
  by (simp add: filter_eq_iff eventually_at_filter nhds_ereal eventually_filtermap)

lemma
  shows at_left_PInf: "at_left \<infinity> = filtermap ereal at_top"
    and at_right_MInf: "at_right (-\<infinity>) = filtermap ereal at_bot"
  unfolding filter_eq_iff eventually_filtermap
    eventually_at_left'[OF ereal_less(3)] eventually_at_top_dense
    eventually_at_right'[OF ereal_less(4)] eventually_at_bot_dense
  by (auto simp add: ereal_all_split ereal_ex_split)

lemma tendsto_compose_filtermap: "((g \<circ> f) ---> T) F \<longleftrightarrow> (g ---> T) (filtermap f F)"
  by (simp add: filterlim_def filtermap_filtermap comp_def)

lemma ereal_tendsto_simps1:
  "((f \<circ> real) ---> y) (at_left (ereal x)) \<longleftrightarrow> (f ---> y) (at_left x)"
  "((f \<circ> real) ---> y) (at_right (ereal x)) \<longleftrightarrow> (f ---> y) (at_right x)"
  "((f \<circ> real) ---> y) (at_left (\<infinity>::ereal)) \<longleftrightarrow> (f ---> y) at_top"
  "((f \<circ> real) ---> y) (at_right (-\<infinity>::ereal)) \<longleftrightarrow> (f ---> y) at_bot"
  unfolding tendsto_compose_filtermap at_left_ereal at_right_ereal at_left_PInf at_right_MInf
  by (auto simp: filtermap_filtermap filtermap_ident)

lemma filterlim_at_bot_dense:
  fixes f :: "'a \<Rightarrow> ('b::dense_linorder)"
  shows "(LIM x F. f x :> at_bot) \<longleftrightarrow> (\<forall>Z. eventually (\<lambda>x. f x < Z) F)"
  by (metis eventually_elim1[of _ F] order_less_imp_le eventually_gt_at_bot
            filterlim_at_bot[of f F] filterlim_iff[of f at_bot F]) (* FIXME! *)

lemma ereal_tendsto_simps2:
  "((ereal \<circ> f) ---> ereal a) F \<longleftrightarrow> (f ---> a) F"
  "((ereal \<circ> f) ---> \<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_top)"
  "((ereal \<circ> f) ---> -\<infinity>) F \<longleftrightarrow> (LIM x F. f x :> at_bot)"
  unfolding tendsto_PInfty filterlim_at_top_dense tendsto_MInfty filterlim_at_bot_dense
  using lim_ereal by (simp_all add: comp_def)

lemmas ereal_tendsto_simps = ereal_tendsto_simps1 ereal_tendsto_simps2

(*
  Useful abbreviations for restricting attention to a set, wrt a general measure.

  TODO: introduce better notation for these, or get rid of them?
*)

abbreviation "set_integrable M A f \<equiv> integrable M (\<lambda>x. f x * indicator A x)"

abbreviation "set_lebesgue_integral M A f \<equiv> lebesgue_integral M (\<lambda>x. f x * indicator A x)"

abbreviation "set_borel_measurable M A f \<equiv> (\<lambda>x. f x * indicator A x) \<in> borel_measurable M"

lemma set_integrable_subset: 
  fixes M A B f
  assumes "set_integrable M A f" "B \<in> sets M" "B \<subseteq> A"  
  shows "set_integrable M B f"
proof -
  have "set_integrable M B (\<lambda>x. f x * indicator A x)"
    by (rule integrable_mult_indicator, rule assms, rule assms)
  also have "(\<lambda>x. f x * indicator A x * indicator B x) = (\<lambda>x. f x * indicator B x)"
    apply (rule ext)
    using `B \<subseteq> A` by (auto simp add: indicator_def)
  finally show ?thesis .
qed

syntax
"_ascii_lebesgue_integral" :: "pttrn \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(3LINT _|_. _)" [0,110,60] 60)

translations
"LINT x|M. f" == "CONST lebesgue_integral M (\<lambda>x. f)"

syntax
"_set_lebesgue_integral" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'a measure \<Rightarrow> real \<Rightarrow> real"
("(4LINT _:_|_. _)" [0,60,110,61] 60)

translations
"LINT x:A|M. f" == "CONST set_lebesgue_integral M A (\<lambda>x. f)"

(*
  Notation for integration wrt lebesgue measure on the reals:

  LBINT x. f
  LBINT x : A. f
  LBINT x=a..b. f

  In the last one, a and b are ereals, so they can be \<infinity> or -\<infinity>.

  TODO: keep all these? Introduce more notation?
*)

syntax
"_ascii_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real"
("(2LBINT _. _)" [0,60] 60)

translations
"LBINT x. f" == "CONST lebesgue_integral CONST lborel (\<lambda>x. f)"

syntax
"_ascii_set_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real set \<Rightarrow> real \<Rightarrow> real"
("(3LBINT _:_. _)" [0,60,61] 60)

translations
"LBINT x:A. f" == "CONST set_lebesgue_integral CONST lborel A (\<lambda>x. f)"

(* TODO: for this, it would be more natural if einterval a b included a and b when they are real. *)
definition interval_lebesgue_integral :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "interval_lebesgue_integral M a b f = (if a \<le> b
    then (\<integral>x. f x * indicator (einterval a b) x \<partial>M)
    else - (\<integral>x. f x * indicator (einterval b a) x \<partial>M))"

definition interval_lebesgue_integrable :: "real measure \<Rightarrow> ereal \<Rightarrow> ereal \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "interval_lebesgue_integrable M a b f = (if a \<le> b
    then integrable M (\<lambda>x. f x * indicator (einterval a b) x)
    else integrable M (\<lambda>x. f x * indicator (einterval b a) x))"

syntax
  "_ascii_interval_lebesgue_borel_integral" :: "pttrn \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  ("(4LBINT _=_.._. _)" [0,60,60,61] 60)

translations
  "LBINT x=a..b. f" == "CONST interval_lebesgue_integral CONST lborel a b (\<lambda>x. f)"

(*
  Basic properties of integration over an interval.
*)

lemma interval_lb_integral_eq: 
  fixes a b f
  assumes "a \<le> b"
  shows "(LBINT x=a..b. f x) = (LBINT x : einterval a b. f x)"

  using assms by (auto simp add: interval_lebesgue_integral_def)

lemma interval_lb_integral_add: 
  assumes "interval_lebesgue_integrable M a b f"
    "interval_lebesgue_integrable M a b g"
  shows "interval_lebesgue_integral M a b (\<lambda>x. f x + g x) = 
   interval_lebesgue_integral M a b f + interval_lebesgue_integral M a b g"
  using assms by (auto simp add: interval_lebesgue_integral_def interval_lebesgue_integrable_def 
    field_simps)

lemma interval_lb_integral_endpoints_same [simp]: "(LBINT x=a..a. f x) = 0"
  unfolding interval_lebesgue_integral_def einterval_def apply simp
  by (cases a rule: ereal2_cases, auto)

lemma interval_lb_integral_endpoints_reverse: "(LBINT x=a..b. f x) = -(LBINT x=b..a. f x)"
  apply (case_tac "a = b", auto)
  by (case_tac "a \<le> b", auto simp add: interval_lebesgue_integral_def)

lemma interval_lb_integral_Icc:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {a..b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (rule integral_cong_AE)
  apply (rule AE_I [where N = "{a} \<union> {b}"])
  apply (auto simp add: indicator_def)
  by (metis lmeasure_eq_0 negligible_insert negligible_sing)

lemma interval_lb_integral_Iic:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {a<..b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (rule integral_cong_AE)
  apply (rule AE_I [where N = "{b}"])
  by (auto simp add: indicator_def)

lemma interval_lb_integral_Ici:
  fixes a b :: real
  assumes "a \<le> b" 
  shows "(LBINT x=a..b. f x) = (LBINT x : {a..<b}. f x)"
  
  using assms unfolding interval_lebesgue_integral_def einterval_def apply simp
  apply (rule integral_cong_AE)
  apply (rule AE_I [where N = "{a}"])
  by (auto simp add: indicator_def)

lemma interval_lb_integral_sum: 
  fixes a b c :: real
  assumes integrable: "interval_lebesgue_integrable lborel (min a (min b c)) (max a (max b c)) f" 

  shows "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) = (LBINT x=a..c. f x)"
proof -
  {
    fix a b c :: real
    assume local: "a \<le> b" "b \<le> c" "interval_lebesgue_integrable lborel a c f"
    have "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) = (LBINT x=a..c. f x)"
      apply (case_tac "b = c", simp) 
      apply (subst interval_lb_integral_Iic)
      using local apply (auto simp add: interval_lebesgue_integral_def einterval_def
        interval_lebesgue_integrable_def)
      apply (subst integral_add(2) [symmetric])
      apply (erule set_integrable_subset, auto)+
      apply (rule integral_cong)
      apply (subst ring_distribs [symmetric])
      apply (subst indicator_add)
      apply force
      apply (rule arg_cong) back
      apply (rule arg_cong) back
      by auto
  } note 1 = this
  {
    fix a b c :: real
    assume local: "a \<le> min b c" and
      integ: "interval_lebesgue_integrable lborel (min a (min b c)) (max a (max b c)) f"
    then have
      integ1: "interval_lebesgue_integrable lborel a (max b c) f"
      by (auto simp del: ereal_min ereal_max 
        simp add: ereal_min [symmetric] ereal_max [symmetric] max_absorb2 min_absorb1)
    have "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
      apply (case_tac "b \<le> c")
      apply (subst interval_lb_integral_endpoints_reverse [of c a], simp)
      apply (rule 1)
      (* why aren't max_absorb1 and max_absorb2 simplifier rules?? *)
      (* ereal_min and ereal_max go the wrong way when we have comparisons for the reals *)
      using local integ1 apply (auto simp del: ereal_min ereal_max 
        simp add: ereal_min [symmetric] ereal_max [symmetric] max_absorb2) [3]
      apply (subst interval_lb_integral_endpoints_reverse [of c a], 
        subst interval_lb_integral_endpoints_reverse [of b c], simp add: field_simps)
      apply (subst 1)
      using local integ1 by (auto simp del: ereal_min ereal_max 
        simp add: ereal_min [symmetric] ereal_max [symmetric] max_absorb1)
  } note 2 = this
  have "a \<le> min b c | b \<le> min a c | c \<le> min a b" by auto
  moreover have "a \<le> min b c \<Longrightarrow> 
      (LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    by (frule 2, rule integrable, auto)
  moreover have "b \<le> min a c \<Longrightarrow> 
      (LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    apply (frule 2)
    (* the ac rules for min and max should be added to the simplifier, no? *)
    using integrable by (auto simp add: min.commute min.left_commute min.assoc
      max.commute max.left_commute max.assoc interval_lb_integral_endpoints_reverse [of c a]
      interval_lb_integral_endpoints_reverse [of b a] 
      interval_lb_integral_endpoints_reverse [of c b])
  moreover have "c \<le> min a b \<Longrightarrow> 
      (LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    apply (frule 2)
    using integrable by (auto simp add: min.commute min.left_commute min.assoc
      max.commute max.left_commute max.assoc)
  ultimately have "(LBINT x=a..b. f x) + (LBINT x=b..c. f x) + (LBINT x=c..a. f x) = 0"
    by blast
  thus ?thesis
    by (simp add: interval_lb_integral_endpoints_reverse [of c a])
qed

lemma interval_lb_integral_Icc_approx_nonneg:
  fixes a b :: ereal
  assumes "a < b"
  fixes u l :: "nat \<Rightarrow> real"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
  fixes f :: "real \<Rightarrow> real"
  assumes f_integrable: "\<And>i. set_integrable lborel {l i..u i} f"
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes f_measurable: "set_borel_measurable lborel (einterval a b) f"
  assumes lbint_lim: "(\<lambda>i. LBINT x=l i.. u i. f x) ----> C"
  shows "(LBINT x=a..b. f x) = C"
proof -
  have "(LBINT x=a..b. f x) = 
    integral\<^isup>L lborel (\<lambda>x. f x * indicator (einterval a b) x)"
    using assms by (simp add: interval_lebesgue_integral_def less_imp_le)
  also have "... = C"
  proof (rule integral_monotone_convergence)
    fix i show "set_integrable lborel {l i..u i} f" by (rule f_integrable)
  next
    from f_nonneg have "AE x in lborel. \<forall>i. l i \<le> x \<longrightarrow> x \<le> u i \<longrightarrow> 0 \<le> f x"
      by eventually_elim
         (metis approx(5) approx(6) dual_order.strict_trans1 ereal_less_eq(3) le_less_trans)
    then show "AE x in lborel. mono (\<lambda>n. f x * indicator {l n..u n} x)"
      apply eventually_elim
      apply (auto simp: mono_def split: split_indicator)
      apply (metis approx(3) decseqD order_trans)
      apply (metis approx(2) incseqD order_trans)
      done
  next
    { fix x i assume "l i \<le> x" "x \<le> u i"
      then have "eventually (\<lambda>i. l i \<le> x \<and> x \<le> u i) sequentially"
        apply (auto simp: eventually_sequentially intro!: exI[of _ i])
        apply (metis approx(3) decseqD order_trans)
        apply (metis approx(2) incseqD order_trans)
        done
      then have "eventually (\<lambda>i. f x * indicator {l i..u i} x = f x) sequentially"
        by eventually_elim auto }
    then show "AE x in lborel. (\<lambda>i. f x * indicator {l i..u i} x) ----> f x * indicator (einterval a b) x"
      unfolding approx(1) by (auto intro!: AE_I2 Lim_eventually split: split_indicator)
  next show "(\<lambda>i. \<integral> x. f x * indicator {l i..u i} x \<partial>lborel) ----> C"
    using lbint_lim by (simp add: interval_lb_integral_Icc approx less_imp_le)
  next show "set_borel_measurable lborel (einterval a b) f" by (rule assms)
  qed
  finally show ?thesis .
qed

lemma interval_lb_integral_Icc_approx_integrable:
  fixes a b :: ereal
  assumes "a < b"
  fixes u l :: "nat \<Rightarrow> real"
  assumes  approx: "einterval a b = (\<Union>i. {l i .. u i})"
    "incseq u" "decseq l" "\<And>i. l i < u i" "\<And>i. a < l i" "\<And>i. u i < b"
    "l ----> a" "u ----> b"
  fixes f :: "real \<Rightarrow> real"
  assumes f_integrable: "set_integrable lborel (einterval a b) f"
  shows "(\<lambda>i. LBINT x=l i.. u i. f x) ----> (LBINT x=a..b. f x)"
proof -
  have indicator_abs: "\<And>A x. ((indicator A x) :: real) = abs (indicator A x)"
    by (auto simp add: indicator_def)
  have 1: "integrable lborel (\<lambda>x. abs (f x) * indicator (einterval a b) x)"
    apply (subst indicator_abs, subst abs_mult [symmetric])
    by (rule integrable_abs, rule assms)
  show ?thesis
    apply (subst interval_lb_integral_Icc, rule less_imp_le, rule approx)
    apply (simp add: interval_lb_integral_eq less_imp_le `a < b` approx(4))
    apply (rule integral_dominated_convergence)
    prefer 5 
    apply (rule borel_measurable_integrable, rule f_integrable)
    prefer 3 apply (rule 1)
    apply (rule set_integrable_subset, rule f_integrable)
    apply (auto simp add: assms) [2]
    apply (rule AE_I2, subst abs_mult, rule mult_left_mono, subst indicator_abs [symmetric])
    apply auto
    apply (simp add: indicator_def einterval_def, auto)
    apply (rule order_less_le_trans, rule approx, auto)
    apply (rule order_le_less_trans)
    prefer 2 
    apply (rule approx, auto)
    proof -
    { fix x i assume "l i \<le> x" "x \<le> u i"
      then have "eventually (\<lambda>i. l i \<le> x \<and> x \<le> u i) sequentially"
        apply (auto simp: eventually_sequentially intro!: exI[of _ i])
        apply (metis approx(3) decseqD order_trans)
        apply (metis approx(2) incseqD order_trans)
        done
      then have "eventually (\<lambda>i. f x * indicator {l i..u i} x = f x) sequentially"
        by eventually_elim auto }
    then show "AE x in lborel. (\<lambda>i. f x * indicator {l i..u i} x) ----> f x * indicator (einterval a b) x"
      unfolding approx(1) by (auto intro!: AE_I2 Lim_eventually split: split_indicator)
    qed
qed
 
lemma interval_lb_integral_FTC_finite:
  fixes f F :: "real \<Rightarrow> real" and a b :: real
  assumes "a \<le> b"
  assumes F: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> DERIV F x :> f x" 
  assumes f: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> isCont f x" 
  shows "(LBINT x=a..b. f x) = F (b) - F (a)"

  by (auto simp add: interval_lb_integral_Icc assms less_imp_le intro!: integral_FTC_atLeastAtMost)
  
lemma interval_lb_integral_FTC_nonneg:
  fixes f F :: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"
  assumes F: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F x :> f x" 
  assumes f: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f x" 
  assumes f_nonneg: "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f x"
  assumes T: "((F \<circ> real) ---> T) (at_right a)"
  assumes B: "((F \<circ> real) ---> B) (at_left b)"
  shows "(LBINT x=a..b. f x) = B - T"
proof -
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have FTCi: "\<And>i. (LBINT x=l i..u i. f x) = F (u i) - F (l i)"
    using assms approx by (auto intro!: interval_lb_integral_FTC_finite simp add: less_imp_le
      einterval_def set_eq_iff)
  show ?thesis
  proof (rule interval_lb_integral_Icc_approx_nonneg [OF `a < b` approx _ f_nonneg])
    fix i show "set_integrable lborel {l i .. u i} f"
        using `a < l i` `u i < b`
        by (intro borel_integrable_atLeastAtMost f)
           (auto simp del: ereal_less_eq simp add: ereal_less_eq(3)[symmetric])
    next  
      have "(\<lambda>x. if x \<in> einterval a b then f x else 0) \<in> borel_measurable borel"
        by (rule borel_measurable_continuous_on_open')
           (auto simp add: continuous_on_eq_continuous_at einterval_iff f)
      also have "(\<lambda>x. if x \<in> einterval a b then f x else 0) = (\<lambda>x. f x * indicator (einterval a b) x)"
        by auto
      finally show "set_borel_measurable lborel (einterval a b) f"
        by simp
    next
      show "(\<lambda>i. LBINT x=l i..u i. f x) ----> B - T"
        apply (subst FTCi)
        apply (intro tendsto_intros)
        using B approx unfolding tendsto_at_iff_sequentially comp_def
        apply (elim allE[of _ "\<lambda>i. ereal (u i)"], auto)
        using T approx unfolding tendsto_at_iff_sequentially comp_def
        by (elim allE[of _ "\<lambda>i. ereal (l i)"], auto)
  qed
qed
  
(*
  The fundamental theorem of calculus and substitution theorem for integrals over
  an interval. 

  strategy - first prove versions for finite intervals, then add limit hypotheses to get
  arbitrary intervals
*)

(* TODO: show that if

  F x = (LBINT y=a..x. f y)

and f is continuous at x then 

  DERIV F x :> f x

This will allow us to remove the fourth hypothesis in the next lemma.
*)

lemma interval_lb_integral_substitution_finite:
  fixes a b :: real
  assumes "a \<le> b"
  and "\<And>x. x\<in>{a..b} \<Longrightarrow> g x \<in> {(g a)..(g b)} \<and> isCont g' x \<and> DERIV g x :> g' x"
  and "g a \<le> g b"
  and "\<And>x. x \<in> {(g a)..(g b)} \<Longrightarrow> DERIV F x :> f x"
  and "\<And>x. x \<in> {(g a)..(g b)} \<Longrightarrow> isCont f x"
  shows "LBINT x=a..b. f (g x) * g' x = LBINT y=(g a)..(g b). f y"
proof-
  have "\<forall>x \<in> {a..b}. isCont (\<lambda>x. f (g x) * g' x) x"
  proof-
    have isCont_comp: "\<forall>x \<in> {a..b}. isCont f (g x)" using assms by auto
    have isCont_g: "\<forall>x \<in> {a..b}. isCont g x"
      using assms DERIV_isCont by blast
    hence "\<forall>x \<in> {a..b}. isCont (\<lambda>x. f (g x)) x"
      using isCont_comp isCont_g isCont_o2 by blast
    thus ?thesis using assms by simp
  qed
  hence "LBINT x=a..b. f (g x) * g' x = (F o g) b - (F o g) a"
    apply (subst interval_lb_integral_Icc, simp add: assms)
    apply (rule integral_FTC_atLeastAtMost[of a b "(F o g)"
      "\<lambda>x. f (g x) * g' x"], rule assms)
    using assms by (auto intro!: DERIV_chain)
  thus ?thesis 
    apply (elim ssubst) 
    apply (subst interval_lb_integral_Icc, simp add: assms)
    apply (subst integral_FTC_atLeastAtMost[of "g a" "g b" F f])
    using assms by auto
qed

lemma interval_lb_integral_substitution_nonneg:
  fixes F f g g':: "real \<Rightarrow> real" and a b :: ereal
  assumes "a < b"  (* change to \<le>? *)
  assumes deriv_g: "!!x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV g x :> g' x"
  assumes contf: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont f (g x)"
  assumes contg': "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont g' x"
  assumes f_nonneg: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> 0 \<le> f (g x)"  (* make these AE *)
  assumes g'_nonneg: "\<And>x. a \<le> ereal x \<Longrightarrow> ereal x \<le> b \<Longrightarrow> 0 \<le> g' x"
  assumes derivF: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> DERIV F (g x) :> f (g x)"
  assumes "((ereal \<circ> g \<circ> real) ---> T) (at_left a)"
  assumes "((ereal \<circ> g \<circ> real) ---> B) (at_right b)"
  assumes integrable: "set_integrable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)"
  shows "(LBINT x=B..T. f x) = (LBINT x=a..b. (f (g x) * g' x))"
proof -
  have [simp]: "B \<le> T" sorry
  from einterval_Icc_approximation[OF `a < b`] guess u l . note approx = this
  have g_nondec: "\<And>x y. a < x \<Longrightarrow> x \<le> y \<Longrightarrow> y < b \<Longrightarrow> g x \<le> g y"
    (* ouch! can this be automated more? *)
    apply (erule DERIV_nonneg_imp_nondecreasing, auto)
    apply (rule exI, rule conjI, rule deriv_g)
    apply (erule order_less_le_trans, auto)
    apply (rule order_le_less_trans, subst ereal_less_eq(3), assumption, auto)
    apply (rule g'_nonneg)
    apply (rule less_imp_le, erule order_less_le_trans, auto)
    by (rule less_imp_le, rule le_less_trans, subst ereal_less_eq(3), assumption, auto)
  have [simp]: "\<And>x i. l i \<le> x \<Longrightarrow> a < ereal x"
    by (rule order_less_le_trans, rule approx, force)
  have [simp]: "\<And>x i. x \<le> u i \<Longrightarrow> ereal x < b"
    by (rule order_le_less_trans, subst ereal_less_eq(3), assumption, rule approx)
  have [simp]: "\<And>x. a < ereal x \<Longrightarrow> ereal x < b \<Longrightarrow> isCont (\<lambda>x. f (g x) * g' x) x"
    apply (rule continuous_mult)
    apply (rule isCont_o2) back
    by (rule DERIV_isCont, auto intro!: deriv_g contf contg')
  have ivt: "\<And>x i. g (l i) \<le> x \<Longrightarrow> x \<le> g (u i) \<Longrightarrow> \<exists>z \<ge> l i. z \<le> u i \<and> g z = x"
    by (auto intro!: IVT DERIV_isCont deriv_g simp add: approx less_imp_le)
  have eq1: "\<And>i. (LBINT x=l i.. u i. (f (g x) * g' x)) = (LBINT y=g (l i)..g (u i). f y)"
    apply (rule interval_lb_integral_substitution_finite)
    apply (auto intro!: g_nondec deriv_g contg' simp add: less_imp_le approx)
    apply (frule (1) ivt, auto intro: derivF)
    by (frule (1) ivt, auto intro: contf)
  have 1 [simp]: "\<And>i. set_integrable lborel {l i..u i} (\<lambda>x. f (g x) * g' x)"
    by (intro borel_integrable_atLeastAtMost, auto)
  have [simp]: "set_borel_measurable borel (einterval a b) (\<lambda>x. f (g x) * g' x)"     
  proof -
    have "(\<lambda>x. if x \<in> einterval a b then f (g x) * g' x else 0) \<in> borel_measurable borel"
      apply (rule borel_measurable_continuous_on_open')
      by (auto simp add: continuous_on_eq_continuous_at einterval_iff)
    also have "(\<lambda>x. if x \<in> einterval a b then f (g x) * g' x else 0) = 
        (\<lambda>x. f (g x) * g' x * indicator (einterval a b) x)"
      by auto
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (rule sym, rule interval_lb_integral_Icc_approx_nonneg [OF `a < b` approx])
    fix i show "set_integrable lborel {l i..u i} (\<lambda>x. f (g x) * g' x)" by simp
    next show "AE x in lborel. a < ereal x \<longrightarrow> ereal x < b \<longrightarrow> 0 \<le> f (g x) * g' x"
      by (rule AE_I2, auto simp add: mult_nonneg_nonneg g'_nonneg f_nonneg)
    next show "set_borel_measurable lborel (einterval a b) (\<lambda>x. f (g x) * g' x)" by simp
    next
      have 3: "(\<lambda>i. LBINT x=l i..u i. f (g x) * g' x)
          ----> (LBINT x=a..b. f (g x) * g' x)"
        apply (rule interval_lb_integral_Icc_approx_integrable [OF `a < b` approx])
        by (rule assms)
      hence "(\<lambda>i. (LBINT y=g (l i)..g (u i). f y)) ----> (LBINT x=a..b. f (g x) * g' x)"
        by (simp add: eq1)
      hence 5: "(LBINT x=B..T. f x) = (LBINT x=a..b. f (g x) * g' x)"
        apply (auto simp add: interval_lb_integral_eq assms approx less_imp_le g_nondec)
        apply (rule integral_monotone_convergence)
        prefer 4
        apply assumption
        sorry
      show "(\<lambda>i. LBINT x=ereal (l i)..ereal (u i). f (g x) * g' x)
        ----> (LBINT x=B..T. f x)"
      by (subst 5, rule 3)
  qed
qed


(* properties of the general set interval *)

lemma set_integrable_Un:
  assumes "set_integrable M A f" "set_integrable M B f"
  shows "set_integrable M (A \<union> B) f"
  using integrable_max
  sorry
(*
by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)
*)

lemma set_integrable_UN:
  assumes "finite I" "\<And>i. i\<in>I \<Longrightarrow> set_integrable M (A i) f"
  shows "set_integrable M (\<Union>i\<in>I. A i) f"
  using assms
  by (induct I) (auto simp: set_integrable_Un)

lemma set_integral_Un:
  assumes "A \<inter> B = {}"
  and "set_integrable M A f"
  and "set_integrable M B f"
  shows "LINT x:A\<union>B|M. f x = (LINT x:A|M. f x) + (LINT x:B|M. f x)"
  by (auto simp add: indicator_union_arith indicator_inter_arith[symmetric]
      distrib_left assms)

lemma set_integral_finite_Union:
  assumes "finite I" "disjoint_family_on A I"
    and "\<And>i. i \<in> I \<Longrightarrow> set_integrable M (A i) f"
  shows "(LINT x:(\<Union>i\<in>I. A i)|M. f x) = (\<Sum>i\<in>I. LINT x:A i|M. f x)"
  using assms
  apply induct
  apply (auto intro!: set_integral_Un set_integrable_Un set_integrable_UN simp: disjoint_family_on_def)
  sorry

lemma set_integral_cmult:
  assumes "set_integrable M A f"
  shows "set_integrable M A (\<lambda>t. a * f t)"
  and "LINT t:A|M. a * f t = a * (LINT t:A|M. f t)"
  (* Expressions which are the same up to rearrangement of parentheses should be easier to identify. *)
  apply (subst mult_assoc)
  apply (auto intro: integral_cmult assms)
  apply (subst mult_assoc)
  by (auto intro: integral_cmult assms)

lemma set_integrable_abs: "set_integrable M A f \<Longrightarrow> set_integrable M A (\<lambda>x. \<bar>f x\<bar>)"
  using integrable_abs[of M "\<lambda>x. f x * indicator A x"] by (simp add: abs_mult)

lemma pos_integrable_to_top:
  fixes l::real
  assumes "\<And>i. A i \<in> sets M" "mono A"
  assumes nneg: "\<And>x i. x \<in> A i \<Longrightarrow> 0 \<le> f x"
  and intgbl: "\<And>i::nat. set_integrable M (A i) f"
  and lim: "(\<lambda>i::nat. LINT x:A i|M. f x) ----> l"
  shows "set_integrable M (\<Union>i. A i) f"
  apply (rule integral_monotone_convergence_pos[where f = "\<lambda>i::nat. \<lambda>x. f x * indicator (A i) x" and x = l])
  apply (rule intgbl)
  prefer 4 apply (rule lim)
  apply (rule AE_I2)
  using `mono A` apply (auto simp: mono_def nneg split: split_indicator) []
  apply (auto intro!: AE_I2 nneg split: split_indicator) []
proof (rule AE_I2)
  { fix x assume "x \<in> space M"
    show "(\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Union>i. A i) x"
    proof cases
      assume "\<exists>i. x \<in> A i"
      then guess i ..
      then have *: "eventually (\<lambda>i. x \<in> A i) sequentially"
        using `x \<in> A i` `mono A` by (auto simp: eventually_sequentially mono_def)
      show ?thesis
        apply (intro Lim_eventually)
        using *
        apply eventually_elim
        apply (auto split: split_indicator)
        done
    qed auto }
  then show "(\<lambda>x. f x * indicator (\<Union>i. A i) x) \<in> borel_measurable M"
    by (rule borel_measurable_LIMSEQ) (auto intro: borel_measurable_integrable intgbl)
qed

(* Proof from Royden Real Analysis, p. 91. *)
lemma lebesgue_integral_countable_add:
  assumes meas[intro]: "\<And>i::nat. A i \<in> sets M"
  and disj: "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "LINT x:(\<Union>i. A i)|M. f x = (\<Sum>i. (LINT x:(A i)|M. f x))"
  apply (subst integral_sums(2)[THEN sums_unique, symmetric])
  apply (rule set_integrable_subset[OF intgbl])
  apply auto []
  apply auto []
proof -
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. indicator (A i) x::real) sums (if \<exists>i. x \<in> A i then 1 else (0::real))"
    proof auto
      fix i assume "x \<in> A i"
      then have "\<And>j. j \<noteq> i \<Longrightarrow> indicator (A j) x = (0::real)"
        using disj[of _ i] by (auto split: split_indicator)
      with `x \<in> A i` have "(\<lambda>i. indicator (A i) x) sums (\<Sum>j\<in>{i}. indicator (A j) x)"
        by (intro sums_finite) (auto dest!: disj split: split_indicator)
      then show "(\<lambda>i. indicator (A i) x) sums 1"
        using `x \<in> A i` by simp
    qed }
  note sums = this
  from sums_summable[OF this]
  show "\<And>x. x \<in> space M \<Longrightarrow> summable (\<lambda>i. \<bar>f x * indicator (A i) x\<bar>)"
    by (simp add: abs_mult summable_mult)

  show "summable (\<lambda>i. LINT x|M. \<bar>f x * indicator (A i) x\<bar>)"
  proof (rule pos_summable)
    fix n
    show "0 \<le> LINT x|M. \<bar>f x * indicator (A n) x\<bar>"
      by (auto intro!: lebesgue_integral_nonneg)
    have "(\<Sum>i = 0..<n. LINT x|M. \<bar>f x * indicator (A i) x\<bar>) =
      (\<Sum>i = 0..<n. set_lebesgue_integral M (A i) (\<lambda>x. \<bar>f x\<bar>))"
      by (simp add: abs_mult)
    also have "\<dots> = set_lebesgue_integral M (\<Union>i<n. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (subst set_integral_finite_Union)
      apply (auto simp: disjoint_family_on_def disj atLeast0LessThan
                  intro!: set_integrable_abs)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    also have "\<dots> \<le> set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
      apply (intro integral_mono set_integrable_abs intgbl)
      apply (rule integrable_bound[OF intgbl[THEN  set_integrable_abs]])
      apply (auto intro!: AE_I2 split: split_indicator)
      apply (rule borel_measurable_integrable)
      apply (rule set_integrable_subset[OF intgbl])
      apply auto
      done
    finally show "(\<Sum>i = 0..<n. LINT x|M. \<bar>f x * indicator (A i) x\<bar>) \<le>
      set_lebesgue_integral M (\<Union>i. A i) (\<lambda>x. \<bar>f x \<bar>)"
      by simp
  qed
  show "set_lebesgue_integral M (UNION UNIV A) f = LINT x|M. (\<Sum>i. f x * indicator (A i) x)"
    apply (rule integral_cong)
    apply (subst suminf_mult[OF sums_summable[OF sums]])
  proof -
    fix x assume x: "x \<in> space M"
    from sums_unique[OF sums, OF this, symmetric]
    have "indicator (UNION UNIV A) x = (\<Sum>i. indicator (A i) x :: real)"
      by (simp split: split_indicator)
    then show "f x * indicator (UNION UNIV A) x = f x * (\<Sum>i. indicator (A i) x)"
      by simp
  qed
qed

lemma set_integral_cont_up:
  assumes A: "\<And>i. A i \<in> sets M" "incseq A"
  and intgbl: "set_integrable M (\<Union>i. A i) f"
  shows "(\<lambda>i. LINT x:(A i)|M. f x) ----> LINT x:(\<Union>i. A i)|M. f x"
proof (intro integral_dominated_convergence[of M
    "\<lambda>i. \<lambda>x. f x * indicator (A i) x"
    "\<lambda>x. \<bar>f x\<bar> * indicator (\<Union>i. A i) x"
    "\<lambda>x. f x * indicator (\<Union>i. A i) x"])
  fix i::nat show "set_integrable M (A i) f"
    using set_integrable_subset[where A = "A i" and B = "\<Union>i. A i"] A intgbl by auto
next
  fix j::nat show "AE x in M. \<bar>f x * indicator (A j) x\<bar> \<le>
    \<bar>f x\<bar> * indicator (\<Union>i. A i) x"
    apply (rule AE_I2)
    apply (subst abs_mult)
    apply (case_tac "x \<in> A j")
    apply simp
    apply (subgoal_tac "x \<in> (\<Union>i. A i)")
    apply simp apply auto
    apply (case_tac "x \<in> (\<Union>i. A i)")
    by simp_all
next
  show "set_integrable M (\<Union>i. A i) (\<lambda>x. \<bar>f x\<bar>)"
    apply (subst indicator_abs_eq[symmetric])
    apply (subst abs_mult[symmetric])
    apply (rule integrable_abs)
    using assms by auto
next
  show "AE x in M. (\<lambda>i. f x * indicator (A i) x) ---->
    f x * indicator  (\<Union>i. A i) x"
    proof (rule AE_I2)
    fix x
    assume Mx: "x \<in> space M"
    show "(\<lambda>i. f x * indicator (A i) x) ---->
      f x * indicator (\<Union>i. A i) x"
      apply (rule tendsto_mult, auto)
      apply (rule increasing_LIMSEQ)
      unfolding indicator_def using assms A by (auto simp: incseq_Suc_iff)
  qed
next
  show "(\<lambda>x. f x * indicator (\<Union>i. A i) x) \<in> borel_measurable M"
    unfolding integrable_def using assms by simp
qed
        
(* Can the int0 hypothesis be dropped? *)
lemma set_integral_cont_down:
  assumes A: "\<And>i. A i \<in> sets M" "decseq A"
  and int0: "set_integrable M (A 0) f"
  shows "(\<lambda>i::nat. LINT x:(A i)|M. f x) ----> LINT x:(\<Inter>i. A i)|M. f x"
proof (rule integral_dominated_convergence(3))
  have A_super: "\<And>i. A i \<subseteq> A 0"
    using A by (auto simp add: decseq_def)
  with A show int: "\<And>i. set_integrable M (A i) f"
    by (intro set_integrable_subset[OF int0]) auto
  show "set_integrable M (A 0) (\<lambda>x. \<bar>f x\<bar>)"
    using int0 by (rule set_integrable_abs)
  show "\<And>j. AE x in M. \<bar>f x * indicator (A j) x\<bar> \<le> \<bar>f x\<bar> * indicator (A 0) x"
    using A_super by (auto simp: abs_mult split: split_indicator)
  { fix x assume "x \<in> space M"
    have "(\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Inter>i. A i) x"
      apply (intro tendsto_intros)
      apply (cases "\<forall>i. x \<in> A i")
      apply auto
      apply (rule decreasing_tendsto)
      apply (simp_all add: eventually_sequentially)
      apply (rule_tac x=i in exI)
      using `decseq A`
      apply (auto split: split_indicator simp: decseq_def)
      done }
  note LIMSEQ = this
  then show "AE x in M. (\<lambda>i. f x * indicator (A i) x) ----> f x * indicator (\<Inter>i. A i) x"
    by simp
  show "(\<lambda>x. f x * indicator (\<Inter>i. A i) x) \<in> borel_measurable M"
    using LIMSEQ by (rule borel_measurable_LIMSEQ) (auto intro: borel_measurable_integrable int)
qed

lemma set_AE_func_int_eq:
  assumes "AE x \<in> A in M. f x = g x"
  shows "LINT x:A|M. f x = LINT x:A|M. g x"
proof-
  have "AE x in M. f x * indicator A x = g x * indicator A x"
    using assms by auto
  thus ?thesis using integral_cong_AE by metis
qed

lemma integral_at_point:
  fixes a :: real
  assumes "set_integrable M {a} f"
  and "{a} \<in> sets M" and "(emeasure M) {a} \<noteq> \<infinity>"
  shows "(LINT x:{a} | M. f x) = f a * real (emeasure M {a})"
proof-
  have eq: "{r. a \<le> r \<and> r \<le> a} = {a}" by auto
  have int_at: "set_lebesgue_integral M {a} f = set_lebesgue_integral M {a} (%x. f a)"
    by (metis (full_types) indicator_simps(2) mult_zero_right singletonE)
  also have "... = f a * real (emeasure M {a})" using assms by auto
  finally show ?thesis using int_at by (simp add: eq)
qed

end
