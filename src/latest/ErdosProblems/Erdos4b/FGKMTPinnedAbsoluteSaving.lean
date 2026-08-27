/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedEffectiveError
import ErdosProblems.Erdos4b.FGKMTErrorScaleAbsorption

/-!
# Uniform exponential saving for the original pinned prime mass

The dimension is allowed to grow up to log(x)^0.1. The common excluded
prime is chosen before all sieve parameters and both interval endpoints.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem exists_commonPinnedPrimeMass_absolute_saving :
    ∃ a d : ℝ, 0 < a ∧ 0 < d ∧ ∀ H : ℝ, 0 < H → ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B0 : ℕ,
        1 ≤ B0 ∧ (B0 : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B0 = 1 ∨ B0.Prime) ∧ ∀ m W M R Q A B : ℕ, ∀ y : ℝ,
          1 ≤ m → 1 < R → 0 < W → W ∣ M → B0 ∣ M → W.Coprime B0 →
          A ≤ B → B ≤ x → W * R ^ 2 ≤ A + 1 →
          ((W * R ^ 2 : ℕ) : ℝ) ≤ vaughanCubeRoot x →
          (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
          (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2) →
          Q.Prime → R < Q → (∀ q : ℕ, q.Prime → q ∣ W → q ≤ A) →
          (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
          ∀ h : Fin (m + 1) → ℕ, Function.Injective h → (∀ i, h i < 2 * (m + 1) ^ 2) →
          ∀ j : Fin (m + 1), (Q : ℝ) ≤ y → (h j : ℝ) * B ≤ y →
          |commonPinnedPrimeMass m W M R Q A B y h j -
              primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
                (commonPinnedPrimeSet A B).card * commonPinnedQuadratic m M R j| ≤
            (x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by
  obtain ⟨K, C, a, d, hK, hC, ha, hd, Xe, hXe, herror⟩ :=
    exists_commonPinnedPrimeMass_effective_error
  refine ⟨a, d / 2, ha, by positivity, ?_⟩
  intro H hH
  obtain ⟨Xg, hXg⟩ := eventually_atTop.mp (eventually_pinnedError_scale_absorbed hK hC hH hd)
  refine ⟨max Xe Xg, hXe.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxe : Xe ≤ x := (le_max_left _ _).trans hx
  have hxg : Xg ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := by omega
  obtain ⟨B0, hB0pos, hB0bound, hB0, hbound⟩ := herror x hxe
  refine ⟨B0, hB0pos, hB0bound, hB0, ?_⟩
  intro m W M R Q A B y hm hR hW hWM hB0M hWB0 hAB hBx hmod hcube hdim hWdim
    hQ hRQ hWsmall hsmall h hinj hshift j hQy hBy
  have hmodx : W * R ^ 2 ≤ x := by
    exact_mod_cast hcube.trans ((vaughanCubeRoot_le_sqrt hx1).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hx1))))
  have hRmod : R ≤ W * R ^ 2 := by
    have hRR : R ≤ R ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_right (R ^ 2) (by omega : 1 ≤ W)
    exact hRR.trans (by simpa only [one_mul] using hmul)
  exact (hbound m W M R Q A B y hm hR hW hWM hB0M hWB0 hAB hBx hmod hcube
    hQ hRQ hWsmall hsmall h hinj hshift j hQy hBy).trans
      (hXg x hxg m W R (by omega) (hRmod.trans hmodx) hdim hWdim)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedPrimeMass_absolute_saving
