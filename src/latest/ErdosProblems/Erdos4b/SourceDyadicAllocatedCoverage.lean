/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicAllocation
import ErdosProblems.Erdos4b.SourceDyadicProxyCoverage

/-!
# Constant coverage on the constructed intervals away from the boundary

The intervals are no longer arbitrary inputs: they are the checked
rounded prefix allocation. Residual membership supplies all pinned
arithmetic hypotheses. Only the lower boundary is excluded.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def dyadicPinnedBoundary (K a r : ℕ) : ℕ :=
  primorial (sourcePreSieveCutoff r) * K * primaryFrontier a r

theorem primorial_shift_lt_of_boundary {K w X p₀ q : ℕ} (hX : 0 < X)
    (hq : q ≤ X) (hboundary : primorial w * K * X ≤ p₀) (h : Fin K) :
    primorial w * h.val * q < p₀ := by
  have hstrict : primorial w * h.val * X < primorial w * K * X :=
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h.isLt (primorial_pos w)) hX
  exact ((Nat.mul_le_mul_left _ hq).trans_lt hstrict).trans_le hboundary

theorem eventually_dyadicAllocated_residualCoverage
    {I : Type*} {K : ℕ} (hK : 0 < K) (S : Finset I)
    (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (a : ℕ) {D : ℕ} (hD : 0 < D)
    (hmain : 0 < sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)
    (hpinned : ∀ h : Fin K, 0 < sourcePinnedFirstVariationalIntegral S F h *
      sourcePinnedCompanionVariationalIntegral K G) :
    ∀ᶠ r in atTop, ∀ (E : Finset ℕ) (N : ℕ),
      (∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ D * fullResidualCofactorCutoff r) →
      jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N →
      smoothFrontier r ≤ N →
      let A := sourceAllocatedStart E (dyadicAllocatedLength a D r) ((primaryFrontier a r + 1) / 2)
      let B := sourceAllocatedEnd E (dyadicAllocatedLength a D r) ((primaryFrontier a r + 1) / 2)
      ∀ m ∈ E, ∀ p₀ ∈ residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
        (residualPrimeFrontier a r) m, dyadicPinnedBoundary K a r ≤ p₀ →
        dyadicAllocationDensity D *
            (∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h *
              sourcePinnedCompanionVariationalIntegral K G) /
          (16 * (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)) ≤
          dyadicSourceResidueCoverage S F G a D r m p₀ (A m) (B m) N := by
  have hcover := uniform_dyadicSourceProxyCoverage_lower hK S F G hFcompact hFsmooth
    hGcompact hGsmooth hFsimplex hFceiling hGsupport a D 2
    (by norm_num : (0 : ℝ) < 1) hmain hpinned
  filter_upwards [hcover, eventually_dyadicAllocated_intervals a hD] with r hc ha
  intro E N hE hN hYN
  dsimp only
  intro m hm p₀ hp hboundary
  have hd := mem_residualPrimeFiber.mp hp
  have hmdata := hE m hm
  have hrange := (ha E hE).1 m hm
  have hT : p₀ ≤ D * intervalLength a r / m :=
    (Nat.le_div_iff_mul_le hmdata.1).mpr (by simpa only [mul_comm] using hd.2.2.2.1)
  have hdata : DyadicPinnedSourceRange a D 2 1 r m p₀
      (sourceAllocatedStart E (dyadicAllocatedLength a D r) ((primaryFrontier a r + 1) / 2) m)
      (sourceAllocatedEnd E (dyadicAllocatedLength a D r) ((primaryFrontier a r + 1) / 2) m) :=
    ⟨hmdata.1, hmdata.2.2, hd.2.1, hd.2.2.1.le, hT, hd.2.2.2.2,
      hrange.1, hrange.2.1, hrange.2.2.1, by simpa only [one_mul] using hrange.2.2.2.1⟩
  apply hc m p₀ _ _ N (dyadicAllocationDensity D) hmdata.2.1 hdata hN hYN _ hrange.2.2.2.2
  intro q hq h
  exact primorial_shift_lt_of_boundary (primaryFrontier_pos a r)
    ((mem_auxiliaryPrimeInterval.mp hq).2.1.le.trans hrange.2.2.1) hboundary h

end

end Erdos4b.SmoothParameters
