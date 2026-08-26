import ErdosProblems.Erdos547.AllocationOperations
import ErdosProblems.Erdos547.FractionalFromMatching

/-!
# Orienting a fractional matching from separated rows

The construction scales selected rows of a symmetric matching. A local
separation condition on the row coefficients ensures both endpoint bounds.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

def ofDominatedWeight (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (f : V → V → ℝ) (hzero : ∀ u v, 0 ≤ f u v)
    (hbound : ∀ u v, (f u v + γ * f v u) / (1 + γ) ≤ μ.weight u v) :
    SkewMatching G γ where
  skew_nonneg := hγ
  weight := f
  nonnegative := hzero
  supported u v huv := by
    have hden : 0 < 1 + γ := by linarith
    have h := (div_le_iff₀ hden).mp (hbound u v)
    rw [μ.supported u v huv, zero_mul] at h
    have hi := mul_nonneg hγ (hzero v u)
    exact le_antisymm (by linarith) (hzero u v)
  capacity u := by
    have hden : 0 < 1 + γ := by linarith
    have h : (∑ v, (f u v + γ * f v u) / (1 + γ)) ≤ 1 :=
      (Finset.sum_le_sum fun v _ ↦ hbound u v).trans (μ.capacity u)
    simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum] at h
    exact (div_le_one hden).mp h

theorem ofDominatedWeight_dominated (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (f : V → V → ℝ) (hzero : ∀ u v, 0 ≤ f u v)
    (hbound : ∀ u v, (f u v + γ * f v u) / (1 + γ) ≤ μ.weight u v) :
    (ofDominatedWeight μ γ hγ f hzero hbound).DominatedByFractional μ := hbound

end SkewMatching

namespace FractionalMatching

theorem toSkew_endpointWeight (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (u v : V) : (μ.toSkew γ hγ).endpointWeight u v = μ.weight u v := by
  change (μ.weight u v + γ * μ.weight v u) / (1 + γ) = μ.weight u v
  rw [μ.symmetric v u]
  have hden : 1 + γ ≠ 0 := by linarith
  field_simp [hden]

theorem toSkew_dominated (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ) :
    (μ.toSkew γ hγ).DominatedByFractional μ :=
  fun u v ↦ (μ.toSkew_endpointWeight γ hγ u v).le

theorem toSkew_outLoad (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ) (u : V) :
    (μ.toSkew γ hγ).outLoad u = μ.load u / (1 + γ) := rfl

theorem separated_endpoint_bound (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u)
    (hsep : ∀ u v, 0 < μ.weight u v → t u + t v ≤ 1) (u v : V) :
    (((1 + γ) * (t u / max 1 γ) * μ.weight u v) +
      γ * ((1 + γ) * (t v / max 1 γ) * μ.weight v u)) / (1 + γ) ≤ μ.weight u v := by
  have hden : 1 + γ ≠ 0 := by linarith
  have hM : 0 < max 1 γ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [μ.symmetric v u]
  have heq : (((1 + γ) * (t u / max 1 γ) * μ.weight u v) +
      γ * ((1 + γ) * (t v / max 1 γ) * μ.weight u v)) / (1 + γ) =
      ((t u + γ * t v) / max 1 γ) * μ.weight u v := by
    field_simp [hden, ne_of_gt hM]
  rw [heq]
  by_cases hpos : 0 < μ.weight u v
  · have hcoef : t u + γ * t v ≤ max 1 γ := by
      have h₁ := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) γ) (ht u)
      have h₂ := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) γ) (ht v)
      have h₃ := mul_le_mul_of_nonneg_left (hsep u v hpos) hM.le
      nlinarith only [h₁, h₂, h₃]
    exact (mul_le_mul_of_nonneg_right ((div_le_one hM).mpr hcoef) hpos.le).trans_eq (one_mul _)
  · have hz : μ.weight u v = 0 := le_antisymm (le_of_not_gt hpos) (μ.nonnegative u v)
    simp only [hz, mul_zero, le_refl]

def separatedRows (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u)
    (hsep : ∀ u v, 0 < μ.weight u v → t u + t v ≤ 1) : SkewMatching G γ :=
  SkewMatching.ofDominatedWeight μ γ hγ
    (fun u v ↦ (1 + γ) * (t u / max 1 γ) * μ.weight u v)
    (fun u v ↦ mul_nonneg (mul_nonneg (by linarith)
      (div_nonneg (ht u) (le_trans zero_le_one (le_max_left _ _)))) (μ.nonnegative u v))
    (μ.separated_endpoint_bound γ hγ t ht hsep)

theorem separatedRows_dominated (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u)
    (hsep : ∀ u v, 0 < μ.weight u v → t u + t v ≤ 1) :
    (μ.separatedRows γ hγ t ht hsep).DominatedByFractional μ :=
  μ.separated_endpoint_bound γ hγ t ht hsep

theorem separatedRows_outLoad (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u)
    (hsep : ∀ u v, 0 < μ.weight u v → t u + t v ≤ 1) (u : V) :
    (μ.separatedRows γ hγ t ht hsep).outLoad u = t u * μ.load u / max 1 γ := by
  change (∑ v, (1 + γ) * (t u / max 1 γ) * μ.weight u v) / (1 + γ) = _
  rw [← Finset.mul_sum]
  have hden : 1 + γ ≠ 0 := by linarith
  dsimp [load]
  field_simp [hden]

theorem separatedRows_total (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (t : V → ℝ) (ht : ∀ u, 0 ≤ t u)
    (hsep : ∀ u v, 0 < μ.weight u v → t u + t v ≤ 1) :
    (μ.separatedRows γ hγ t ht hsep).total =
      ((1 + γ) / max 1 γ) * ∑ u, t u * μ.load u := by
  change (∑ u, ∑ v, (1 + γ) * (t u / max 1 γ) * μ.weight u v) = _
  simp only [← Finset.mul_sum, load]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

end FractionalMatching

theorem capped_ratio_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ min a b / b := div_nonneg (le_min ha hb) hb

theorem capped_ratio_le_one {a b : ℝ} (hb : 0 ≤ b) : min a b / b ≤ 1 := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  · exact (div_le_one hb).mpr (min_le_right _ _)

theorem capped_ratio_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b / b) * b = min a b := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [min_eq_right ha]
  · exact div_mul_cancel₀ _ (ne_of_gt hb)

theorem capped_ratio_eq_zero {a b : ℝ} (ha : a ≤ 0) (ha' : 0 ≤ a) (hb : 0 ≤ b) :
    min a b / b = 0 := by
  have hz : a = 0 := le_antisymm ha ha'
  simp [hz, min_eq_left hb]

/-- If no residual edge joins two positive allowance vertices, an explicit
skew allocation captures at least the entire residual saturation. -/
theorem exists_skew_of_separated_allowances (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ)
    (a : V → ℝ) (ha : ∀ u, 0 ≤ a u)
    (hsep : ∀ u v, 0 < μ.weight u v → a u ≤ 0 ∨ a v ≤ 0) :
    ∃ σ : SkewMatching G γ, σ.DominatedByFractional μ ∧
      (∀ u, σ.outLoad u ≤ a u) ∧ (∑ u, min (a u) (μ.load u)) ≤ σ.total := by
  let t := fun u ↦ min (a u) (μ.load u) / μ.load u
  have ht : ∀ u, 0 ≤ t u := fun u ↦ capped_ratio_nonneg (ha u) (μ.load_nonneg u)
  have htone : ∀ u, t u ≤ 1 := fun u ↦ capped_ratio_le_one (μ.load_nonneg u)
  have htsep : ∀ u v, 0 < μ.weight u v → t u + t v ≤ 1 := by
    intro u v huv
    rcases hsep u v huv with hu | hv
    · have hz : t u = 0 := capped_ratio_eq_zero hu (ha u) (μ.load_nonneg u)
      simpa only [hz, zero_add] using htone v
    · have hz : t v = 0 := capped_ratio_eq_zero hv (ha v) (μ.load_nonneg v)
      simpa only [hz, add_zero] using htone u
  refine ⟨μ.separatedRows γ hγ t ht htsep,
    μ.separatedRows_dominated γ hγ t ht htsep, ?_, ?_⟩
  · intro u
    rw [μ.separatedRows_outLoad]
    change (min (a u) (μ.load u) / μ.load u) * μ.load u / max 1 γ ≤ a u
    rw [capped_ratio_mul (ha u) (μ.load_nonneg u)]
    apply (div_le_self (le_min (ha u) (μ.load_nonneg u)) (le_max_left (1 : ℝ) γ)).trans
    exact min_le_left _ _
  · rw [μ.separatedRows_total]
    have hsum : (∑ u, t u * μ.load u) = ∑ u, min (a u) (μ.load u) := by
      apply Finset.sum_congr rfl
      intro u _
      exact capped_ratio_mul (ha u) (μ.load_nonneg u)
    rw [hsum]
    have hM : 0 < max 1 γ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hcoef : 1 ≤ (1 + γ) / max 1 γ := (le_div_iff₀ hM).mpr (by
      rw [one_mul]
      exact max_le (by linarith) (by linarith))
    exact le_mul_of_one_le_left (Finset.sum_nonneg fun u _ ↦ le_min (ha u) (μ.load_nonneg u)) hcoef

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_skew_of_separated_allowances
