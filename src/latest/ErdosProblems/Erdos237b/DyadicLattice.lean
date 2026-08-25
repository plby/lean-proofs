import ErdosProblems.Erdos237b.DyadicBox
import BoundedGaps.Maynard.ConcreteFractionalRectangle

/-!
# Arithmetic box-mass limits for the dyadic candidate

The rectangular reciprocal-totient limit in `BoundedGaps` is generic in the
tuple, despite its historical `Engelsma` name. Here it evaluates the complete
finite linear combination used by our dyadic denominator. Pairwise-coprimality
corrections and the prime-weighted numerator are not part of this theorem.
-/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

/-- Boxes wholly contained in the unit simplex, specified by upper endpoints. -/
noncomputable def dyadicGoodBoxes (L k : ℕ) : Finset (Fin k → Fin L) :=
  univ.filter fun x => (∑ i, dyadicUpper L k (x i)) ≤ 1

theorem tendsto_dyadic_independent_box_mass {H : Finset ℕ} {L k : ℕ}
    (hL : 0 < L) (hk : 2 ^ L ≤ k) (e : H ≃ Fin k)
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      ∑ x ∈ dyadicGoodBoxes L k, (∏ i, dyadicHeight L (x i) ^ 2) *
        normalizedEngelsmaFractionalTupleShellMass H alpha
          (fun h => dyadicLength L k (x (e h)))
          (fun h => dyadicUpper L k (x (e h))) N)
      atTop (nhds (boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k)) := by
  have hinterval (j : Fin L) :
      dyadicLength L k j ∈ Set.Icc (0 : ℝ) 1 ∧
        dyadicUpper L k j ∈ Set.Icc (0 : ℝ) 1 ∧
          dyadicLength L k j ≤ dyadicUpper L k j := by
    have hlen := dyadicLength_nonneg L k j
    have hupper := dyadicUpper_le_half hL hk j
    have heq := dyadicUpper_eq_two_mul_length L k j
    exact ⟨⟨hlen, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩
  have hlim := tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
    halpha (dyadicGoodBoxes L k) (fun x => ∏ i, dyadicHeight L (x i) ^ 2)
    (fun x h => dyadicLength L k (x (e h)))
    (fun x h => dyadicUpper L k (x (e h)))
    (fun x _ h => (hinterval (x (e h))).1)
    (fun x _ h => (hinterval (x (e h))).2.1)
    (fun x _ h => (hinterval (x (e h))).2.2)
  have htarget :
      (∑ x ∈ dyadicGoodBoxes L k, (∏ i, dyadicHeight L (x i) ^ 2) *
        ∏ h : H, (dyadicUpper L k (x (e h)) - dyadicLength L k (x (e h)))) =
      boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k := by
    simp_rw [dyadicUpper_sub_length]
    have hprod (x : Fin k → Fin L) :
        (∏ h : H, dyadicLength L k (x (e h))) = ∏ i, dyadicLength L k (x i) :=
      e.prod_comp (fun i => dyadicLength L k (x i))
    simp_rw [hprod, ← prod_mul_distrib]
    unfold dyadicGoodBoxes boxDenominator dyadicSquareMass
    rw [sum_filter]
  rwa [htarget] at hlim

end Erdos237b
