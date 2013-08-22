theory Helly_Selection
imports Diagonal_Subsequence Library_Misc

begin

lemma real_bdd_below_inf:
  fixes A :: "real set"
  fixes m :: real
  assumes "\<And>x. x \<in> A \<Longrightarrow> m \<le> x" "A \<noteq> {}"
  shows "\<exists>inf. Inf {ereal x |x. x \<in> A} = ereal inf"
proof (rule ccontr)
  let ?I = "Inf {ereal x |x. x \<in> A}"
  assume "\<not> (\<exists>inf. ?I = ereal inf)"
  then have spl: "?I = \<infinity> \<or> ?I = -\<infinity>" by (smt abs_neq_infinity_cases ereal_infinity_cases)
  { assume "?I = \<infinity>"
    hence "{ereal x |x. x \<in> A} = {}"
      by (subst (asm) Inf_eq_PInfty) auto
    hence False using assms by simp
  }
  hence 1: "?I = -\<infinity>" using spl by auto
  then have "\<And>x. x \<in> {ereal x |x. x \<in> A} \<Longrightarrow> -\<infinity> \<le> x" by auto
  moreover hence "\<And>r. ?I < ereal r" using 1 by simp
  ultimately have "\<And>r. \<exists>x \<in> {ereal x |x. x \<in> A}. x < ereal r"
    by (subst Inf_ereal_iff[of "{ereal x |x. x \<in> A}" "-\<infinity>"]) auto
  hence "\<exists>x \<in> {ereal x |x. x \<in> A}. x < ereal m" by auto
  then obtain x where 2: "x \<in> {ereal x |x. x \<in> A}" and 3: "x < ereal m" by auto
  then obtain r where 4: "x = ereal r" by auto
  hence "r \<in> A" using 2 by simp
  moreover have "r < m" using 3 4 by simp
  ultimately show False using assms not_le by auto
qed

(** Consider developing notions of has_sup, has_inf for arbitrary lattices, and the notion of a
conditionally complete lattice (one where every set bdd below has an inf, and every set bdd above
has a sup). [This should be in a locale.] **)

definition rcont_inc :: "(real \<Rightarrow> real) \<Rightarrow> bool"
  where "rcont_inc f \<equiv> (\<forall>x. continuous (at_right x) f) \<and> mono f"

theorem Helley_selection:
  fixes f :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes rcont_inc: "\<And>n. rcont_inc (f n)"
  and ubdd: "\<forall>n x. \<bar>f n x\<bar> \<le> M"
  shows "\<exists>s. subseq s \<and> (\<exists>F. rcont_inc F \<and> (\<forall>n x. \<bar>F x\<bar> \<le> M) \<and>
    (\<forall>x.  continuous (at x) F \<longrightarrow> (\<lambda>n. f (s n) x) ----> F x))"
proof -
  obtain m::"real \<Rightarrow> nat" where "bij_betw m \<rat> UNIV"
    apply (rule countableE_infinite)
    apply (rule countable_rat)
    apply (rule real_rats_infinite)
    by auto
  then obtain r::"nat \<Rightarrow> real" where bij: "bij_betw r UNIV \<rat>" using bij_betw_inv by blast
  let ?P = "\<lambda>n. \<lambda>s. convergent (\<lambda>k. f (s k) (r n))"
  interpret nat: subseqs ?P
  proof (unfold convergent_def, unfold subseqs_def, auto)
    fix n::nat fix s::"nat \<Rightarrow> nat" assume s: "subseq s"
    have "bounded {-M..M}" using bounded_closed_interval by auto
    moreover have "\<And>k. f (s k) (r n) \<in> {-M..M}" using ubdd abs_le_interval_iff by auto
    ultimately have "\<exists>l s'. subseq s' \<and> ((\<lambda>k. f (s k) (r n)) \<circ> s') ----> l"
      using bounded_imp_convergent_subsequence[of "{-M..M}"] by auto
    thus "\<exists>s'. subseq s' \<and> (\<exists>l. (\<lambda>k. f (s (s' k)) (r n)) ----> l)" unfolding o_def by auto
  qed
  let ?d = "nat.diagseq"
  have rat_cnv: "\<And>n. ?P n ?d"
  proof -
    fix n::nat show "?P n ?d"
    proof -
      have Pn_seqseq: "?P n (nat.seqseq (Suc n))"
        by (subst nat.seqseq_reducer) (rule nat.reducer_reduces)
      have 1: "(\<lambda>k. f ((nat.seqseq (Suc n) \<circ> (\<lambda>k. nat.fold_reduce (Suc n) k
        (Suc n + k))) k) (r n)) = (\<lambda>k. f (nat.seqseq (Suc n) k) (r n)) \<circ>
        (\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k))"
        by auto
      have 2: "?P n (?d \<circ> (op + (Suc n)))"
        apply (subst nat.diagseq_seqseq)
        apply (subst 1)
        apply (rule convergent_subseq_convergent[of "\<lambda>k. f (nat.seqseq (Suc n) k) (r n)"
          "\<lambda>k. nat.fold_reduce (Suc n) k (Suc n + k)"])
        by (rule Pn_seqseq) (rule nat.subseq_diagonal_rest)
      then obtain L where 3: "(\<lambda>k. f ((?d \<circ> (op + (Suc n))) k) (r n)) ----> L"
        using convergentD by auto
      have 4: "(\<lambda>k. f (?d (k + (Suc n))) (r n)) =
      (\<lambda>k. f ((?d \<circ> (op + (Suc n))) k) (r n))"
        by (auto simp: add_commute)
      have "(\<lambda>k. f (?d k) (r n)) ----> L" 
        apply (rule LIMSEQ_offset[of _ "Suc n"])
        by (subst 4) (rule 3)
      thus ?thesis unfolding convergent_def by auto
    qed
  qed
  have M_nonneg: "0 \<le> M" using ubdd by (metis abs_minus_le_zero less_le less_trans neg_le_0_iff_le)
  have lim_bdd: "\<And>n. lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}"
  proof -
    fix n::nat
    have "closed {-M..M}" using closed_real_atLeastAtMost by auto
    hence "(\<forall>i. (\<lambda>k. f (?d k) (r n)) i \<in> {-M..M}) \<and> (\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f (?d k) (r n))
      \<longrightarrow> lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}"
      apply (subst (asm) closed_sequential_limits)
      by (drule_tac x = "\<lambda>k. f (?d k) (r n)" in spec) blast
    moreover have "\<forall>i. (\<lambda>k. f (?d k) (r n)) i \<in> {-M..M}" using ubdd abs_le_interval_iff by auto
    moreover have "(\<lambda>k. f (?d k) (r n)) ----> lim (\<lambda>k. f (?d k) (r n))"
      using rat_cnv convergent_LIMSEQ_iff by auto
    ultimately show "lim (\<lambda>k. f (?d k) (r n)) \<in> {-M..M}" by auto
  qed
  hence "\<And>x::real. Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<in> {-M..M}"
  proof -
    fix x::real
    have M: "-M \<le> M" using M_nonneg by simp
    have bd_limset: "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<subseteq> {-M..M}" using lim_bdd by auto
    hence 1: "\<forall>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. \<bar>y - 0\<bar> \<le> M"
    proof -
      have "(\<forall>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. \<bar>y - 0\<bar> \<le> M) =
        (\<forall>y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}. y \<in> {-M..M})" by auto
      thus ?thesis using bd_limset by blast
    qed       
    have 2: "{lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<noteq> {}"
    proof -
      obtain q where q: "q \<in> \<rat> \<and> x < q" by (metis (full_types) Rats_dense_in_real linordered_field_no_ub)
      let ?n = "the_inv_into UNIV r q"
      let ?y = "lim (\<lambda>k. f (?d k) (r ?n))"
      have "x < r ?n" using f_the_inv_into_f bij q by (metis bij_betw_def)
      then have "?y \<in> {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}" by auto
      thus ?thesis by auto
    qed
    thm Inf_asclose
    have "\<bar>Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} - 0\<bar> \<le> M"
      apply (rule Inf_asclose) by (rule 2) (rule 1)
    thus "Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n} \<in> {-M..M}" by auto
  qed
  let ?F = "\<lambda>x::real. Inf {lim (\<lambda>k. f (?d k) (r n)) |n. x < r n}"
  have mono: "mono ?F"
  proof (unfold mono_def, auto)
    fix x y::real assume le: "x \<le> y"
    hence subset: "{ereal (lim (\<lambda>k. f (?d k) (r n))) |n. y < r n} \<subseteq>
      {ereal (lim (\<lambda>k. f (?d k) (r n))) |n. x < r n}"
      by auto
    show "?F x \<le> ?F y"
    proof -
      have "Inf {ereal (lim (\<lambda>k. f (?d k) (r n))) |n. x < r n} \<le>
        Inf {ereal (lim (\<lambda>k. f (?d k) (r n))) |n. y < r n}" using subset Inf_superset_mono by auto
      thus ?thesis sorry
  qed
  moreover have "\<And>x. continuous (at_right x) ?F"
    (*apply (unfold continuous_def)
    apply (unfold tendsto_def, auto)
    apply (subst eventually_within)
    proof -
      fix x::real fix S::"real set" assume opnS: "open S"
      assume ntlim_inS: "(Inf {lim (\<lambda>k. f (?d k) (r n)) |n. netlimit (at_right x) < r n}) \<in> S"
      have "netlimit (at_right x) = x" by (auto intro: netlimit_within)
      hence "?F x \<in> S" using ntlim_inS by simp
      (* Use S to get epsilon; r from the book is now d. *)*) sorry
  ultimately have rcont_inc: "rcont_inc ?F" unfolding rcont_inc_def by auto
  moreover have bdd: "\<forall>n x. \<bar>?F x\<bar> \<le> M" sorry
  moreover have lim: "\<forall>x.  continuous (at x) ?F \<longrightarrow> (\<lambda>n. f (?d n) x) ----> ?F x"
  proof auto
    fix x::real assume cnt: "continuous (at x) ?F"
    fix e::real assume e: "0 < e"
    have "?F -- x --> ?F x" using cnt continuous_at by auto
    hence "\<exists>d>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (?F y - ?F x) < e"
      by (rule LIM_D) (rule e) (* Why did auto not work here? *)
    then obtain d where "d > 0" and cnt': "\<forall>y. y \<noteq> x \<and> norm (y - x) < d \<longrightarrow> norm (?F y - ?F x) < e"
      by auto
    fix y::real assume less: "y < x" and "norm (y - x) < d"
    then have "norm (?F y - ?F x) < e" using cnt' by auto
    hence 1: "?F x - e < ?F y" using less mono by auto
    obtain n where n: "y < r n \<and> r n < x"
    proof -
      obtain q where q: "q \<in> \<rat> \<and> y < q \<and> q < x" using less Rats_dense_in_real by auto
      then obtain n where "r n = q" using bij sorry
      thus ?thesis sorry
    qed
    obtain m where m: "x < r m \<and> lim (\<lambda>k. f (?d k) (r m)) < ?F x + e" sorry
    have "?F x - e < lim (\<lambda>k. f (?d k) (r m))" sorry
  
  ultimately show ?thesis
    apply (rule_tac x = ?d in exI)
    apply (rule conjI)
    apply (rule nat.subseq_diagseq)
    by (rule_tac x = ?F in exI) auto
qed

end