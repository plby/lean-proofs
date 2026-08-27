/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConductorWindow
import ErdosProblems.Erdos4b.FGKMTConductorCutoff

/-!
# Effective averaged prime distribution with one excluded prime

All constants precede the endpoint. At that endpoint the excluded prime is
chosen once, before any modulus cutoff and before either interval endpoint.
The estimate controls the sum of the literal endpoint/residue maxima.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem exists_effective_primePrefix_distribution :
    ∃ D a d : ℝ, 0 < D ∧ 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B : ℕ,
        1 ≤ B ∧ (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B = 1 ∨ B.Prime) ∧ ∀ L : ℕ, (L : ℝ) ≤ vaughanCubeRoot x →
          coprimePrimeDiscrepancyPrefixSum B L x ≤
            D * ((x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨D, a, d, hD, ha, hd, Xw, hXw, hwindow⟩ :=
    exists_effective_primePrefix_bound_on_conductor_window
  obtain ⟨Xc, hXc⟩ := eventually_atTop.mp (eventually_effectiveConductorCutoff_window ha)
  refine ⟨D, a, d, hD, ha, hd, max Xw Xc, hXw.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxw : Xw ≤ x := (le_max_left _ _).trans hx
  have hxc : Xc ≤ x := (le_max_right _ _).trans hx
  obtain ⟨hR2, hRlower, hRcube⟩ := hXc x hxc
  let R := effectiveConductorCutoff a x
  have hRupper := effectiveConductorCutoff_le_exp a x
  obtain ⟨B, hBpos, hBR, hB, hbound⟩ := hwindow R hR2
  refine ⟨B, hBpos, (by exact_mod_cast hBR : (B : ℝ) ≤ R).trans hRupper, hB, ?_⟩
  intro L hL
  have hmax : ((max L R : ℕ) : ℝ) ≤ vaughanCubeRoot x := by
    rw [Nat.cast_max]
    exact max_le hL hRcube
  exact (coprimePrimeDiscrepancyPrefixSum_mono_modulus (le_max_left L R) B x).trans
    (hbound x hxw hRlower hRupper (max L R) (le_max_right _ _) hmax)

theorem exists_effective_primeProgression_all_endpoints :
    ∃ D a d : ℝ, 0 < D ∧ 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B : ℕ,
        1 ≤ B ∧ (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B = 1 ∨ B.Prime) ∧ ∀ L : ℕ, (L : ℝ) ≤ vaughanCubeRoot x →
          ∀ y : ℕ, y ≤ x → coprimeModulusDiscrepancySum B L y ≤
            D * ((x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨D, a, d, hD, ha, hd, X0, hX0, hdist⟩ := exists_effective_primePrefix_distribution
  refine ⟨D, a, d, hD, ha, hd, X0, hX0, ?_⟩
  intro x hx
  obtain ⟨B, hBpos, hBbound, hB, hbound⟩ := hdist x hx
  refine ⟨B, hBpos, hBbound, hB, ?_⟩
  intro L hL y hy
  exact (coprimeModulusDiscrepancySum_le_prefix hy B L).trans (hbound L hL)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_effective_primePrefix_distribution
#print axioms Erdos4b.FGKMT.exists_effective_primeProgression_all_endpoints
