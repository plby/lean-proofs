import ErdosProblems.Erdos4.TiltedEulerMoments
import ErdosProblems.Erdos4.TiltedPowerTail
import ErdosProblems.Erdos4.TiltedDivisorSets
import ErdosProblems.Erdos4.TiltedSieve

/-! A uniform moment estimate from divisibility bounds up to the ambient scale. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

def DivisorBound {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (S : Finset ℕ) (H : Ω → Finset ℕ) (X : ℕ) (D a : ℝ) : Prop :=
  ∀ T ∈ S.powerset, T.Nonempty → (∏ p ∈ T, p) ≤ X →
    μ.prob (fun o => T ⊆ H o) ≤ D * ∏ p ∈ T, (a / (p : ℝ) ^ 2)

theorem tilt_coefficient_le {p : ℕ} (hp : 1 ≤ p) {τ a : ℝ} (hτ : τ ≤ 1 / 2)
    (ha : 0 ≤ a) :
    ((p : ℝ) ^ τ - 1) * (a / (p : ℝ) ^ 2) ≤ a * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have ht : (p : ℝ) ^ τ - 1 ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
    linarith [Real.rpow_le_rpow_of_exponent_le hp1 hτ]
  calc
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) * (a / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right ht (div_nonneg ha (sq_nonneg _))
    _ = _ := by
      rw [show -(3 / 2 : ℝ) = 1 / 2 - (2 : ℕ) by norm_num,
        Real.rpow_sub_natCast hp0]
      ring

theorem small_product_moment {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (S : Finset ℕ) (H : Ω → Finset ℕ) {W X : ℕ} (hW : 0 < W)
    (hS : ∀ p ∈ S, W < p) (hHS : ∀ o, H o ⊆ S)
    (hsmall : ∀ o, (∏ p ∈ H o, p) ≤ X) {τ D a : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hbound : DivisorBound μ S H X D a) :
    μ.mean (fun o => (((∏ p ∈ H o, p : ℕ) : ℝ)) ^ τ) ≤
      1 + D * (Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))) - 1) := by
  classical
  let f := fun p : ℕ => (p : ℝ) ^ τ - 1
  let g := fun p : ℕ => a / (p : ℝ) ^ 2
  have hp1 : ∀ p ∈ S, 1 ≤ p := fun p hp => by have := hS p hp; omega
  have hf : ∀ p ∈ S, 0 ≤ f p := fun p hp =>
    sub_nonneg.mpr (Real.one_le_rpow (by exact_mod_cast hp1 p hp) hτ0)
  have hg : ∀ p, 0 ≤ g p := fun p => div_nonneg ha (sq_nonneg _)
  have hprob : ∀ T ∈ S.powerset.erase ∅,
      μ.prob (fun o => T ⊆ H o) ≤ D * ∏ p ∈ T, g p := by
    intro T hT
    have hTS := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)
    have hTne := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT)
    by_cases hTX : (∏ p ∈ T, p) ≤ X
    · exact hbound T (Finset.mem_of_mem_erase hT) hTne hTX
    · have hnot : ∀ o, ¬T ⊆ H o := by
        intro o ho
        apply hTX
        exact (Finset.prod_le_prod_of_subset_of_one_le' ho
          (fun p hp _ => hp1 p (hHS o hp))).trans (hsmall o)
      simp only [FiniteLaw.prob, hnot, if_false, Finset.sum_const_zero]
      exact mul_nonneg hD (Finset.prod_nonneg (fun p _ => hg p))
  have hmoment := mean_prod_one_add_le μ S H hHS f g D hf hprob
  have heq : (fun o => ∏ p ∈ H o, (1 + f p)) =
      (fun o => (((∏ p ∈ H o, p : ℕ) : ℝ)) ^ τ) := by
    funext o
    simp only [f, add_sub_cancel]
    exact nat_prod_rpow (H o) τ
  rw [heq] at hmoment
  apply hmoment.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hD
  apply sub_le_sub_right
  calc
    _ ≤ Real.exp (∑ p ∈ S, f p * g p) :=
      prod_one_add_le_exp_sum S _ (fun p hp => mul_nonneg (hf p hp) (hg p))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ p ∈ S, a * (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
          Finset.sum_le_sum (fun p hp => tilt_coefficient_le (hp1 p hp) hτ ha)
        _ = a * ∑ p ∈ S, (p : ℝ) ^ (-(3 / 2 : ℝ)) := (Finset.mul_sum _ _ _).symm
        _ ≤ a * (2 * (W : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (finite_three_halves_tail hW S hS) ha
        _ = _ := by ring

theorem product_moment_with_tail {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (S : Finset ℕ) (H : Ω → Finset ℕ) {W X N : ℕ} (hW : 0 < W) (hX : 1 ≤ X)
    (hS : ∀ p ∈ S, W < p) (hHS : ∀ o, H o ⊆ S)
    (hsize : ∀ o, (∏ p ∈ H o, p) ≤ N) {τ D a : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hbound : DivisorBound μ S H X D a) :
    μ.mean (fun o => (((∏ p ∈ H o, p : ℕ) : ℝ)) ^ τ) ≤
      1 + D * (Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))) - 1) +
        (N : ℝ) ^ τ * μ.prob (fun o => X < ∏ p ∈ H o, p) := by
  classical
  let H₀ := fun o => if (∏ p ∈ H o, p) ≤ X then H o else ∅
  have hH₀ : ∀ o, H₀ o ⊆ H o := by intro o; dsimp [H₀]; split_ifs <;> simp
  have hsmall : ∀ o, (∏ p ∈ H₀ o, p) ≤ X := by
    intro o
    dsimp [H₀]
    split_ifs with ho
    · exact ho
    · simpa only [Finset.prod_empty] using hX
  have hbound₀ : DivisorBound μ S H₀ X D a := by
    intro T hT hTne hTX
    exact (μ.prob_mono (fun o ho => ho.trans (hH₀ o))).trans (hbound T hT hTne hTX)
  have hclip := small_product_moment μ S H₀ hW hS (fun o => (hH₀ o).trans (hHS o))
    hsmall hτ0 hτ hD ha hbound₀
  have hcompare : μ.mean (fun o => (((∏ p ∈ H o, p : ℕ) : ℝ)) ^ τ) ≤
      μ.mean (fun o => (((∏ p ∈ H₀ o, p : ℕ) : ℝ)) ^ τ) +
        (N : ℝ) ^ τ * μ.prob (fun o => X < ∏ p ∈ H o, p) := by
    rw [FiniteLaw.prob_eq_mean, ← μ.mean_const_mul, ← μ.mean_add]
    apply μ.mean_mono
    intro o
    dsimp [H₀]
    by_cases ho : (∏ p ∈ H o, p) ≤ X
    · simp only [if_pos ho, not_lt.mpr ho, if_false, mul_zero, add_zero, le_refl]
    · simp only [if_neg ho, Finset.prod_empty, Nat.cast_one, Real.one_rpow,
        lt_of_not_ge ho, if_true, mul_one]
      have hh := Real.rpow_le_rpow (Nat.cast_nonneg (∏ p ∈ H o, p))
        (Nat.cast_le.mpr (hsize o)) hτ0
      linarith
  exact hcompare.trans (add_le_add hclip le_rfl)

end Erdos4.Tilted
