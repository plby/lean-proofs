import Arxiv.Arxiv2411_18291.TwoTermCancellation
import Arxiv.Arxiv2411_18291.CoefficientReduction

/-! # Magnitude levels of representations with edge multiplicity at most two -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem boundary_odd_zero_of_two (D : Finset (Block V q))
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (Φ : Block V q → ℤ) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (f : ℤ → ℤ) (hf0 : f 0 = 0) (hfneg : ∀ z, f (-z) = -f z)
    (e : Block V r) (he : boundary r Φ e = 0) :
    boundary r (fun Q => f (Φ Q)) e = 0 := by
  have hs' : ∀ Q, Q ∉ D → f (Φ Q) = 0 := by
    intro Q hQ
    rw [hs Q hQ, hf0]
  rw [boundary_eq_sum_supported D _ hs' e]
  apply sum_odd_eq_zero_of_card_le_two _ (hmult e) Φ f hf0 hfneg
  rw [← boundary_eq_sum_supported D Φ hs e]
  exact he

theorem abs_boundary_magnitudeLevel_le_two (D : Finset (Block V q))
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2)
    (Φ : Block V q → ℤ) (hs : ∀ Q, Q ∉ D → Φ Q = 0) (t : ℕ) (e : Block V r) :
    |boundary r (fun Q => intMagnitudeLevel t (Φ Q)) e| ≤ 2 := by
  have hs' : ∀ Q, Q ∉ D → intMagnitudeLevel t (Φ Q) = 0 := by
    intro Q hQ
    rw [hs Q hQ, intMagnitudeLevel_zero]
  rw [boundary_eq_sum_supported D _ hs' e]
  calc
    _ ≤ ∑ Q ∈ D.filter (fun Q => e.val ⊆ Q.val), |intMagnitudeLevel t (Φ Q)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _Q ∈ D.filter (fun Q => e.val ⊆ Q.val), (1 : ℤ) :=
      sum_le_sum (fun Q _ => abs_intMagnitudeLevel_le t (Φ Q))
    _ = ((D.filter fun Q => e.val ⊆ Q.val).card : ℤ) := by simp
    _ ≤ 2 := by exact_mod_cast hmult e

theorem boundary_magnitudeLevel_sum (Φ : Block V q → ℤ) (e : Block V r) :
    (∑ t ∈ univ.image (fun Q => (Φ Q).natAbs),
      (t : ℤ) * boundary r (fun Q => intMagnitudeLevel t (Φ Q)) e) = boundary r Φ e := by
  have hΦ : Φ = ∑ t ∈ univ.image (fun Q => (Φ Q).natAbs),
      (fun Q => (t : ℤ) * intMagnitudeLevel t (Φ Q)) := by
    funext Q
    simp only [Finset.sum_apply]
    exact (sum_intMagnitudeLevel _ (Φ Q) (mem_image.mpr ⟨Q, mem_univ _, rfl⟩)).symm
  have h := congrFun (congrArg (boundary r) hΦ) e
  simp only [boundary_sum, boundary_mul, Finset.sum_apply] at h
  exact h.symm

end Arxiv2411_18291
