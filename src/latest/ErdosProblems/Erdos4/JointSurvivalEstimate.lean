import ErdosProblems.Erdos4.CollisionModuli

/-!
# Uniform relative error for joint survival

This is a finite, quantitative statement. A finite set in `[0,Y]` has
joint survival mass close to the appropriate power of the single-point
density. The error depends only on its cardinality, the reciprocal-square
tail, and `log Y / w`, where every sieve prime is at least `w`.
-/

open scoped BigOperators

namespace Erdos4.JointSurvivalEstimate

open RandomResidueSieve CollisionModuli LocalSurvivalRatios

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def localError (T : Finset ℕ) (l : P) : ℝ := by
  classical
  exact 2 * (T.card : ℝ) ^ 2 / (ell l : ℝ) ^ 2 +
    if l ∈ collisionPrimes ell T then 2 * (T.card : ℝ) / ell l else 0

theorem local_relative_error (T : Finset ℕ) (l : P) (hsize : 2 * T.card ≤ ell l) :
    |(1 - (residues ell T l).card / (ell l : ℝ)) /
      (1 - 1 / (ell l : ℝ)) ^ T.card - 1| ≤ localError ell T l := by
  classical
  have hcard : (residues ell T l).card ≤ T.card := Finset.card_image_le
  have hh := local_modulus_ratio_error (ell l) T.card (residues ell T l).card
    (Fact.out : (ell l).Prime).two_le hcard hsize
  have hlpos : (0 : ℝ) < ell l := by exact_mod_cast (Fact.out : (ell l).Prime).pos
  apply hh.trans
  unfold localError
  by_cases hl : l ∈ collisionPrimes ell T
  · rw [if_pos hl]
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ hlpos.le
    have hv : (0 : ℝ) ≤ (residues ell T l).card := Nat.cast_nonneg _
    linarith
  · rw [if_neg hl]
    have hinj : Set.InjOn (fun n : ℕ => (n : ZMod (ell l))) T := by
      by_contra hn
      exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hn⟩)
    have heq : (residues ell T l).card = T.card := Finset.card_image_of_injOn hinj
    simp [heq]

theorem sum_localError (T : Finset ℕ) :
    (∑ l, localError ell T l) =
      2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) * ∑ l ∈ collisionPrimes ell T, 1 / (ell l : ℝ) := by
  classical
  unfold localError collisionPrimes
  rw [Finset.sum_add_distrib, Finset.sum_filter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun l _hl => by ring)
  · apply Finset.sum_congr rfl
    intro l _hl
    split_ifs <;> ring

theorem relative_error_le (T : Finset ℕ) (hsize : ∀ l, 2 * T.card ≤ ell l) :
    |survivalMass ell T / UnitFourier.unitDensity ell ^ T.card - 1| ≤
      Real.exp (2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) * ∑ l ∈ collisionPrimes ell T, 1 / (ell l : ℝ)) - 1 := by
  have hh := product_ratio_error_le
    (fun l => 1 - (residues ell T l).card / (ell l : ℝ))
    (fun l => (1 - 1 / (ell l : ℝ)) ^ T.card) (localError ell T)
    (fun l => local_relative_error ell T l (hsize l)) (sum_localError ell T).le
  rw [Finset.prod_pow, ← UnitFourier.unitDensity_eq_product ell] at hh
  exact hh

theorem uniform_relative_error_le (hinj : Function.Injective ell) (T : Finset ℕ)
    (hsize : ∀ l, 2 * T.card ≤ ell l) {Y : ℕ} (hY : 1 ≤ Y)
    (hT : ∀ n ∈ T, n ≤ Y) {w : ℝ} (hw : 0 < w) (hlarge : ∀ l, w ≤ ell l) :
    |survivalMass ell T / UnitFourier.unitDensity ell ^ T.card - 1| ≤
      Real.exp (2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) ^ 3 * Real.log Y / (w * Real.log 2)) - 1 := by
  have hc := collision_reciprocal_le ell hinj T hY hT hw hlarge
  apply (relative_error_le ell T hsize).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * (T.card : ℝ))
  calc
    _ ≤ 2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) +
        2 * (T.card : ℝ) * ((T.card : ℝ) ^ 2 * Real.log Y / (w * Real.log 2)) :=
      add_le_add le_rfl hh
    _ = _ := by ring

end Erdos4.JointSurvivalEstimate
