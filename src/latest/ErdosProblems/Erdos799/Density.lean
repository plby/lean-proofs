/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1037

/-!
# Uniform density of labelled graphs

This file supplies the finite-count/probability bridge used in the
formalization of Erdős Problem 799.  The denominator in `graphDensity` is the
number of labelled simple graphs on `Fin n`, so it is precisely the uniform
`G(n, 1/2)` probability.
-/

namespace Erdos799

open Filter
open scoped ENNReal Topology

attribute [local instance] Classical.propDecidable

/-- The proportion of labelled simple graphs on `Fin n` satisfying `P n`. -/
noncomputable def graphDensity
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (P n)).card : ℝ) /
    Fintype.card (SimpleGraph (Fin n))

/-- The density of graphs whose clique number is at least the logarithmic
threshold `Erdos1037.r_val`. -/
noncomputable def largeCliqueDensity (n : ℕ) : ℝ :=
  ((Finset.univ.filter
      (fun G : SimpleGraph (Fin n) ↦
        Erdos1037.r_val n ≤ G.cliqueNum)).card : ℝ) /
    Fintype.card (SimpleGraph (Fin n))

/-- The large-clique density is bounded by the real first-moment bound from
`Erdos1037`. -/
lemma largeCliqueDensity_le_bound (n : ℕ) :
    largeCliqueDensity n ≤ Erdos1037.bound_clique n := by
  have htop :
      (n.choose (Erdos1037.r_val n) : ENNReal) *
          (1 / 2 : ENNReal) ^ (Erdos1037.r_val n).choose 2 ≠ ⊤ := by
    norm_num [ENNReal.mul_eq_top]
  have hle := ENNReal.toReal_mono htop
    (Erdos1037.prob_cliqueNum_ge n (Erdos1037.r_val n))
  rw [Erdos1037.randomGraphMeasure_eq_card_div] at hle
  simpa [largeCliqueDensity, graphDensity, Erdos1037.bound_clique,
    ENNReal.toReal_mul, ENNReal.toReal_pow] using hle

lemma largeCliqueDensity_nonneg (n : ℕ) : 0 ≤ largeCliqueDensity n := by
  unfold largeCliqueDensity
  positivity

/-- The proportion of labelled graphs with a clique of size at least
`ceil (3 log₂ n)` tends to zero. -/
theorem largeCliqueDensity_tendsto_zero :
    Tendsto largeCliqueDensity atTop (nhds 0) := by
  exact squeeze_zero'
    (Eventually.of_forall largeCliqueDensity_nonneg)
    (Eventually.of_forall largeCliqueDensity_le_bound)
    Erdos1037.bound_clique_tendsto_zero

lemma graphDensity_nonneg
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) (n : ℕ) :
    0 ≤ graphDensity P n := by
  unfold graphDensity
  positivity

/-- Any exceptional graph family contained in the large-clique family has
asymptotic density zero. -/
theorem graphDensity_tendsto_zero_of_subset_largeClique
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (hP : ∀ n G, P n G → Erdos1037.r_val n ≤ G.cliqueNum) :
    Tendsto (graphDensity P) atTop (nhds 0) := by
  apply squeeze_zero'
      (Eventually.of_forall (graphDensity_nonneg P))
      (Eventually.of_forall fun n ↦ ?_)
      largeCliqueDensity_tendsto_zero
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      Finset.univ.filter (P n) ⊆
        Finset.univ.filter
          (fun G : SimpleGraph (Fin n) ↦
            Erdos1037.r_val n ≤ G.cliqueNum) by
      intro G hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
      exact hP n G hG)
  · positivity

/-- The density of the complementary property is one minus the original
density. -/
lemma graphDensity_not_eq_one_sub
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) (n : ℕ) :
    graphDensity (fun n G ↦ ¬ P n G) n = 1 - graphDensity P n := by
  let good : Finset (SimpleGraph (Fin n)) := Finset.univ.filter (P n)
  let bad : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter ((fun n G ↦ ¬ P n G) n)
  have hd : Disjoint good bad := by
    rw [Finset.disjoint_left]
    simp [good, bad]
  have hu : good ∪ bad = Finset.univ := by
    ext G
    simp only [good, bad, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact iff_true_intro (Classical.em (P n G))
  have hcard : good.card + bad.card = Fintype.card (SimpleGraph (Fin n)) := by
    rw [← Finset.card_union_of_disjoint hd, hu]
    simp
  calc
    graphDensity (fun n G ↦ ¬ P n G) n =
        (bad.card : ℝ) / Fintype.card (SimpleGraph (Fin n)) := by
      simp only [graphDensity, bad]
    _ = 1 - (good.card : ℝ) / Fintype.card (SimpleGraph (Fin n)) := by
      rw [eq_sub_iff_add_eq, ← add_div]
      have hcast : (bad.card : ℝ) + good.card =
          Fintype.card (SimpleGraph (Fin n)) := by
        exact_mod_cast (by omega : bad.card + good.card =
          Fintype.card (SimpleGraph (Fin n)))
      rw [hcast]
      exact div_self (by positivity)
    _ = 1 - graphDensity P n := by simp only [graphDensity, good]

/-- If the exceptional family has density zero, its complement has density
one. -/
theorem graphDensity_not_tendsto_one
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (hP : Tendsto (graphDensity P) atTop (nhds 0)) :
    Tendsto (graphDensity (fun n G ↦ ¬ P n G)) atTop (nhds 1) := by
  have hfun : graphDensity (fun n G ↦ ¬ P n G) =
      fun n ↦ 1 - graphDensity P n := by
    funext n
    exact graphDensity_not_eq_one_sub P n
  rw [hfun]
  simpa using tendsto_const_nhds.sub hP

end Erdos799
