theory Conditionally_Complete_Lattice

imports Complex_Main

begin

context ord
begin

definition "bdd_above A \<equiv> \<exists>M. \<forall>x \<in> A. x \<le> M"
definition "bdd_below A \<equiv> \<exists>m. \<forall>x \<in> A. m \<le> x"

end

context order
begin

abbreviation "is_Sup s A \<equiv> (\<forall>x \<in> A. x \<le> s) \<and> (\<forall>M. (\<forall>x \<in> A. x \<le> M) \<longrightarrow> s \<le> M)"
abbreviation "is_Inf i A \<equiv> (\<forall>x \<in> A. i \<le> x) \<and> (\<forall>m. (\<forall>x \<in> A. m \<le> x) \<longrightarrow> m \<le> i)"
abbreviation "has_Sup A \<equiv> \<exists>s. is_Sup s A"
abbreviation "has_Inf A \<equiv> \<exists>i. is_Inf i A"

end

context lattice
begin

lemma bdd_above_insert [simp]: "bdd_above (insert a A) = bdd_above A"
unfolding bdd_above_def apply auto
apply (rule_tac x = "sup a M" in exI)
by (auto intro: le_supI2 sup_ge1)

lemma bdd_below_insert [simp]: "bdd_below (insert a A) = bdd_below A"
unfolding bdd_below_def apply auto
apply (rule_tac x = "inf a m" in exI)
by (auto intro: le_infI2 inf_le1)

lemma bdd_above_Un [simp]: "bdd_above (A \<union> B) = (bdd_above A \<and> bdd_above B)"
proof
  assume "bdd_above (A \<union> B)"
  thus "bdd_above A \<and> bdd_above B" unfolding bdd_above_def by auto
next
  assume "bdd_above A \<and> bdd_above B"
  then obtain a b where "\<forall>x\<in>A. x \<le> a" "\<forall>x\<in>B. x \<le> b" unfolding bdd_above_def by auto
  hence "\<forall>x \<in> A \<union> B. x \<le> sup a b" by (auto intro: Un_iff le_supI1 le_supI2)
  thus "bdd_above (A \<union> B)" unfolding bdd_above_def ..
qed

lemma bdd_below_Un [simp]: "bdd_below (A \<union> B) = (bdd_below A \<and> bdd_below B)"
proof
  assume "bdd_below (A \<union> B)"
  thus "bdd_below A \<and> bdd_below B" unfolding bdd_below_def by auto
next
  assume "bdd_below A \<and> bdd_below B"
  then obtain a b where "\<forall>x\<in>A. a \<le> x" "\<forall>x\<in>B. b \<le> x" unfolding bdd_below_def by auto
  hence "\<forall>x \<in> A \<union> B. inf a b \<le> x" by (auto intro: Un_iff le_infI1 le_infI2)
  thus "bdd_below (A \<union> B)" unfolding bdd_below_def ..
qed

end

(* Why does trying to use a locale here result in superfluous types? *)
class conditionally_complete_lattice = lattice +
  assumes bdd_nonempty_Sup: "\<And>A. A \<noteq> {} \<Longrightarrow> bdd_above A \<Longrightarrow> has_Sup A"
  and bdd_nonempty_Inf: "\<And>A. A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> has_Inf A"
  begin

notation inf (infixl "\<sqinter>" 70) and sup (infixl "\<squnion>" 65)

definition Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900) where "Sup A = (THE S. is_Sup S A)"
definition Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900) where "Inf A = (THE s. is_Inf s A)"

lemma Sup_is_Sup:
  fixes A
  assumes "has_Sup A"
  shows "is_Sup (Sup A) A"
proof -
  from assms obtain s where sup_s: "is_Sup s A" by auto
  show ?thesis
    unfolding Sup_def apply (rule theI2, rule sup_s)
    using sup_s apply (metis eq_iff sup_s)
    by auto
qed

lemma Sup_unique:
  fixes A s
  assumes "is_Sup s A"
  shows "s = Sup A"
proof -
  from assms Sup_is_Sup have "Sup A \<le> s" by auto
  moreover from assms Sup_is_Sup have "s \<le> Sup A" by blast
  ultimately show ?thesis by auto
qed

lemma Inf_is_Inf: 
  fixes A
  assumes "has_Inf A"
  shows "is_Inf (Inf A) A"
proof -
  from assms obtain i where inf_i: "is_Inf i A" by auto
  show ?thesis
    unfolding Inf_def apply (rule theI2, rule inf_i)
    using inf_i apply (metis eq_iff inf_i)
    by auto
qed

lemma Inf_unique:
  fixes A i
  assumes "is_Inf i A"
  shows "i = Inf A"
proof -
  from assms Inf_is_Inf have "i \<le> Inf A" by auto
  moreover from assms Inf_is_Inf have "Inf A \<le> i" by blast
  ultimately show ?thesis by auto
qed

lemma Sup_upper:
  fixes A x
  assumes "bdd_above A" and "x \<in> A"
  shows "x \<le> Sup A"
proof -
  from assms have "A \<noteq> {}" by auto
  thus ?thesis using assms bdd_nonempty_Sup Sup_is_Sup by auto
qed

(* This also works when A = {}, provided the lattice has a bottom. *)
lemma Sup_least:
  fixes A M
  assumes "A \<noteq> {}" and M_upper: "\<And>x. x \<in> A \<Longrightarrow> x \<le> M"
  shows "Sup A \<le> M"
proof -
  from M_upper have "bdd_above A" using bdd_above_def by auto
  with assms bdd_nonempty_Sup Sup_is_Sup show ?thesis by auto
qed
    
lemma Inf_lower: 
  fixes A x
  assumes "bdd_below A" and "x \<in> A"
  shows "Inf A \<le> x"
proof -
  from assms have "A \<noteq> {}" by auto
  thus ?thesis using assms bdd_nonempty_Inf Inf_is_Inf by auto
qed

(* This also works if A = {}, provided the lattice has a top. *)
lemma Inf_greatest: 
  fixes A m
  assumes "A \<noteq> {}" and m_lower: "\<And>x. x \<in> A \<Longrightarrow> m \<le> x"
  shows "m \<le> Inf A"
proof -
  from m_lower have "bdd_below A" using bdd_below_def by auto
  with assms bdd_nonempty_Inf Inf_is_Inf show ?thesis by auto
qed

lemma bdd_nonempty_Sup_subset_mono:
  fixes A B
  assumes "A \<noteq> {}" and "bdd_above B" and "A \<subseteq> B"
  shows "Sup A \<le> Sup B"
proof -
  from assms Sup_upper have "\<forall>x\<in>A. x \<le> Sup B" by auto
  thus ?thesis using assms Sup_least by auto
qed

lemma bdd_nonempty_Inf_superset_mono:
  fixes A B
  assumes "B \<noteq> {}" and "bdd_below A" and "B \<subseteq> A"
  shows "Inf A \<le> Inf B"
proof -
  from assms Inf_lower have "\<forall>x\<in>B. Inf A \<le> x" by auto
  thus ?thesis using assms Inf_greatest by auto
qed

lemma dual_conditionally_complete_lattice:
  "class.conditionally_complete_lattice sup (op \<ge>) (op >) inf"
  apply (unfold_locales)
  apply (auto intro: Sup_is_Sup Sup_upper Sup_least Inf_is_Inf Inf_lower Inf_greatest)
  unfolding bdd_above_def bdd_below_def apply (metis less_le)
  apply (metis (lifting) bdd_below_def bdd_nonempty_Inf empty_iff ord.bdd_above_def)
  by (metis (lifting) Sup_least Sup_upper bdd_above_def empty_iff ord.bdd_below_def)

definition InfI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "InfI A f = \<Sqinter>(f ` A)"

definition SupR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where "SupR A f = \<Squnion>(f ` A)"

(** Left out "foundation_dual" lemmata from Complete_Lattices.thy; do not see how they make sense. **)

lemma InfI_lower:
  fixes A f x
  assumes "bdd_below (f ` A)" and "x \<in> A"
  shows "InfI A f \<le> f x"
by (metis InfI_def Inf_lower assms image_eqI)

lemma InfI_greatest:
  fixes A f m
  assumes "A \<noteq> {}" and "\<And>x. x \<in> A \<Longrightarrow> m \<le> f x"
  shows "m \<le> InfI A f"
by (metis (hide_lams, mono_tags) InfI_def Inf_greatest assms empty_is_image image_iff)
  
lemma SupR_upper:
  fixes A f x
  assumes "x \<in> A" and "bdd_above (f ` A)"
  shows "f x \<le> SupR A f"
by (metis (full_types) SupR_def Sup_upper assms image_eqI)

lemma SupR_least:
  fixes A f
  assumes "A \<noteq> {}" and "\<And>x. x \<in> A \<Longrightarrow> f x \<le> M"
  shows "SupR A f \<le> M"
by (metis (hide_lams, mono_tags) SupR_def Sup_least assms empty_is_image image_iff)

lemma Inf_lower2:
  fixes A u v
  assumes "bdd_below A" and "u \<in> A" and "u \<le> v"
  shows "\<Sqinter>A \<le> v"
by (metis Inf_lower assms order_trans)

lemma InfI_lower2:
  fixes A f x u
  assumes "bdd_below (f ` A)" and "x \<in> A" and "f x \<le> u"
  shows "InfI A f \<le> u"
by (auto intro: InfI_lower assms order_trans)

lemma Sup_upper2:
  fixes A u v
  assumes "bdd_above A" and "u \<in> A" and "v \<le> u"
  shows "v \<le> \<Squnion>A"
by (metis Sup_upper assms order_trans)

lemma SupR_upper2:
  fixes A f x u
  assumes "bdd_above (f ` A)" and "x \<in> A" and "u \<le> f x"
  shows "u \<le> SupR A f"
by (auto intro: SupR_upper assms order_trans)

(* Can weaken assumptions to "has_Inf A". *)
lemma le_Inf_iff:
  fixes A b
  assumes "A \<noteq> {}" and "bdd_below A"
  shows "b \<le> \<Sqinter>A \<longleftrightarrow> (\<forall>a\<in>A. b \<le> a)"
by (metis Inf_greatest Inf_lower assms order_trans)

lemma le_InfI_iff:
  fixes A f u
  assumes "A \<noteq> {}" and "bdd_below (f ` A)"
  shows "u \<le> InfI A f \<longleftrightarrow> (\<forall>x\<in>A. u \<le> f x)"
by (metis InfI_greatest InfI_lower assms order_trans)

lemma Sup_le_iff:
  fixes A b
  assumes "A \<noteq> {}" and "bdd_above A"
  shows "\<Squnion>A \<le> b \<longleftrightarrow> (\<forall>a\<in>A. a \<le> b)"
by (metis Sup_least Sup_upper assms order_trans)

lemma SupR_le_iff:
  fixes A f u
  assumes "A \<noteq> {}" and "bdd_above (f ` A)"
  shows "SupR A f \<le> u \<longleftrightarrow> (\<forall>x\<in>A. f x \<le> u)"
by (metis SupR_least SupR_upper assms order_trans)

lemma Inf_insert [simp]:
  fixes A a
  assumes "A \<noteq> {}" and "bdd_below A"
  shows "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
apply (rule antisym)
prefer 2 apply (rule Inf_greatest, auto)
apply (rule le_infI2)
apply (rule Inf_lower)
using assms apply auto [2]
by (auto simp add: assms le_Inf_iff Inf_lower)

lemma InfI_insert:
  fixes A f a
  assumes "A \<noteq> {}" and "bdd_below (f ` A)"
  shows "InfI (insert a A) f = f a \<sqinter> InfI A f"
by (smt InfI_def Inf_insert assms empty_is_image image_insert)

lemma Sup_insert [simp]:
  fixes A a
  assumes "A \<noteq> {}" and "bdd_above A"
  shows "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
apply (rule antisym)
apply (rule Sup_least, auto)
apply (rule le_supI2)
apply (rule Sup_upper)
using assms apply auto [2]
by (auto simp add: assms Sup_le_iff Sup_upper)

lemma SupR_insert: 
  fixes A a f
  assumes "A \<noteq> {}" and "bdd_above (f ` A)" 
  shows "SupR (insert a A) f = f a \<squnion> SupR A f"
by (smt SupR_def Sup_insert assms empty_is_image image_insert)

(**** More theorems to transfer from COmplete_Lattices.thy.

lemma INF_image [simp]: "(\<Sqinter>x\<in>f`A. g x) = (\<Sqinter>x\<in>A. g (f x))"
  by (simp add: INF_def image_image)

lemma SUP_image [simp]: "(\<Squnion>x\<in>f`A. g x) = (\<Squnion>x\<in>A. g (f x))"
  by (simp add: SUP_def image_image)

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<sqsubseteq> a}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<sqsubseteq> b}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma INF_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Sqinter>x\<in>A. C x) = (\<Sqinter>x\<in>B. D x)"
  by (simp add: INF_def image_def)

lemma SUP_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Squnion>x\<in>A. C x) = (\<Squnion>x\<in>B. D x)"
  by (simp add: SUP_def image_def)

lemma Inf_mono:
  assumes "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. a \<sqsubseteq> b"
  shows "\<Sqinter>A \<sqsubseteq> \<Sqinter>B"
proof (rule Inf_greatest)
  fix b assume "b \<in> B"
  with assms obtain a where "a \<in> A" and "a \<sqsubseteq> b" by blast
  from `a \<in> A` have "\<Sqinter>A \<sqsubseteq> a" by (rule Inf_lower)
  with `a \<sqsubseteq> b` show "\<Sqinter>A \<sqsubseteq> b" by auto
qed

lemma INF_mono:
  "(\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Sqinter>n\<in>A. f n) \<sqsubseteq> (\<Sqinter>n\<in>B. g n)"
  unfolding INF_def by (rule Inf_mono) fast

lemma Sup_mono:
  assumes "\<And>a. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a \<sqsubseteq> b"
  shows "\<Squnion>A \<sqsubseteq> \<Squnion>B"
proof (rule Sup_least)
  fix a assume "a \<in> A"
  with assms obtain b where "b \<in> B" and "a \<sqsubseteq> b" by blast
  from `b \<in> B` have "b \<sqsubseteq> \<Squnion>B" by (rule Sup_upper)
  with `a \<sqsubseteq> b` show "a \<sqsubseteq> \<Squnion>B" by auto
qed

lemma SUP_mono:
  "(\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<sqsubseteq> g m) \<Longrightarrow> (\<Squnion>n\<in>A. f n) \<sqsubseteq> (\<Squnion>n\<in>B. g n)"
  unfolding SUP_def by (rule Sup_mono) fast

lemma INF_superset_mono:
  "B \<subseteq> A \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x \<sqsubseteq> g x) \<Longrightarrow> (\<Sqinter>x\<in>A. f x) \<sqsubseteq> (\<Sqinter>x\<in>B. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (blast intro: INF_mono dest: subsetD)

lemma SUP_subset_mono:
  "A \<subseteq> B \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<sqsubseteq> g x) \<Longrightarrow> (\<Squnion>x\<in>A. f x) \<sqsubseteq> (\<Squnion>x\<in>B. g x)"
  by (blast intro: SUP_mono dest: subsetD)

lemma Inf_less_eq:
  assumes "\<And>v. v \<in> A \<Longrightarrow> v \<sqsubseteq> u"
    and "A \<noteq> {}"
  shows "\<Sqinter>A \<sqsubseteq> u"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "v \<sqsubseteq> u" by blast
  ultimately show ?thesis by (rule Inf_lower2)
qed

lemma less_eq_Sup:
  assumes "\<And>v. v \<in> A \<Longrightarrow> u \<sqsubseteq> v"
    and "A \<noteq> {}"
  shows "u \<sqsubseteq> \<Squnion>A"
proof -
  from `A \<noteq> {}` obtain v where "v \<in> A" by blast
  moreover with assms have "u \<sqsubseteq> v" by blast
  ultimately show ?thesis by (rule Sup_upper2)
qed

lemma less_eq_Inf_inter: "\<Sqinter>A \<squnion> \<Sqinter>B \<sqsubseteq> \<Sqinter>(A \<inter> B)"
  by (auto intro: Inf_greatest Inf_lower)

lemma Sup_inter_less_eq: "\<Squnion>(A \<inter> B) \<sqsubseteq> \<Squnion>A \<sqinter> \<Squnion>B "
  by (auto intro: Sup_least Sup_upper)

lemma Inf_union_distrib: "\<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
  by (rule antisym) (auto intro: Inf_greatest Inf_lower le_infI1 le_infI2)

lemma INF_union:
  "(\<Sqinter>i \<in> A \<union> B. M i) = (\<Sqinter>i \<in> A. M i) \<sqinter> (\<Sqinter>i\<in>B. M i)"
  by (auto intro!: antisym INF_mono intro: le_infI1 le_infI2 INF_greatest INF_lower)

lemma Sup_union_distrib: "\<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
  by (rule antisym) (auto intro: Sup_least Sup_upper le_supI1 le_supI2)

lemma SUP_union:
  "(\<Squnion>i \<in> A \<union> B. M i) = (\<Squnion>i \<in> A. M i) \<squnion> (\<Squnion>i\<in>B. M i)"
  by (auto intro!: antisym SUP_mono intro: le_supI1 le_supI2 SUP_least SUP_upper)

lemma INF_inf_distrib: "(\<Sqinter>a\<in>A. f a) \<sqinter> (\<Sqinter>a\<in>A. g a) = (\<Sqinter>a\<in>A. f a \<sqinter> g a)"
  by (rule antisym) (rule INF_greatest, auto intro: le_infI1 le_infI2 INF_lower INF_mono)

lemma SUP_sup_distrib: "(\<Squnion>a\<in>A. f a) \<squnion> (\<Squnion>a\<in>A. g a) = (\<Squnion>a\<in>A. f a \<squnion> g a)" (is "?L = ?R")
proof (rule antisym)
  show "?L \<le> ?R" by (auto intro: le_supI1 le_supI2 SUP_upper SUP_mono)
next
  show "?R \<le> ?L" by (rule SUP_least) (auto intro: le_supI1 le_supI2 SUP_upper)
qed

****)

end

instantiation real :: conditionally_complete_lattice
begin

instance proof
  fix A :: "real set" assume "A \<noteq> {}" and "bdd_above A"
  thus "has_Sup A" unfolding bdd_above_def using complete_real by auto
next
  fix A :: "real set" assume nonempty: "A \<noteq> {}" and bdd: "bdd_below A"
  have "has_Sup (uminus ` A)"
  proof -
    from bdd have "bdd_above (uminus ` A)"
      unfolding bdd_below_def bdd_above_def by (metis image_iff le_minus_iff minus_minus)
    (* Better way to use result of previous assertion in next-separated proof? *)
    thus ?thesis unfolding bdd_above_def using nonempty bdd complete_real[of "uminus ` A"] by auto
  qed
  thus "has_Inf A"
  proof -
    have "is_Inf (Inf_class.Inf A) A" using nonempty bdd
      by (metis (full_types) Inf_ge SupInf.Inf_lower bdd_below_def setgeI)
    thus ?thesis by auto
  qed
qed

end

locale conditionally_complete_lattice_with_top = conditionally_complete_lattice + top

locale conditionally_complete_lattice_with_bot = conditionally_complete_lattice + bot

end
