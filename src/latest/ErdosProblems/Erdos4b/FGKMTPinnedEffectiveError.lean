/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTEffectivePrimeDistribution

/-!
# Effective progression error on the original pinned prime-mass scale

The two endpoints share one excluded prime. Dimension-dependent coefficient
and totient losses remain explicit; no relative error is inferred merely
from an unspecified x^(1-o(1)) lower bound.
-/

namespace Erdos4b.FGKMT

noncomputable section

open BoundedGaps.Maynard

theorem commonPinnedDiscrepancySum_le_prefix {W M R A B B0 L x : ℕ}
    (hW : 0 < W) (hB0M : B0 ∣ M) (hWB0 : W.Coprime B0) (hL : W * R ^ 2 ≤ L)
    (hAx : A ≤ x) (hBx : B ≤ x) :
    commonPinnedDiscrepancySum W M R A B ≤ 2 * coprimePrimeDiscrepancyPrefixSum B0 L x := by
  calc
    _ ≤ coprimeModulusDiscrepancySum B0 L B + coprimeModulusDiscrepancySum B0 L A :=
      commonPinnedDiscrepancySum_le_coprime hW hB0M hWB0 hL
    _ ≤ coprimePrimeDiscrepancyPrefixSum B0 L x + coprimePrimeDiscrepancyPrefixSum B0 L x :=
      add_le_add (coprimeModulusDiscrepancySum_le_prefix hBx B0 L)
        (coprimeModulusDiscrepancySum_le_prefix hAx B0 L)
    _ = _ := by ring

theorem commonPinnedCauchyEnvelope_le_expDecay {m W M R A B B0 L x : ℕ} {D d : ℝ}
    (hD : 0 ≤ D) (hx : 1 ≤ x) (hW : 0 < W) (hB0M : B0 ∣ M) (hWB0 : W.Coprime B0)
    (hL : W * R ^ 2 ≤ L) (hAx : A ≤ x) (hBx : B ≤ x)
    (hdist : coprimePrimeDiscrepancyPrefixSum B0 L x ≤
      D * ((x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ))))) :
    commonPinnedCauchyEnvelope m W M R A B ≤
      Real.sqrt (24 * D) * (x : ℝ) * (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) *
        Real.exp (-(d / 2) * Real.sqrt (Real.log (x : ℝ))) := by
  let F : ℝ := 1 + Real.log (R ^ 2 : ℕ)
  let N : ℕ := (3 * m) ^ 2
  let u : ℝ := Real.sqrt (Real.log (x : ℝ))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hA : (A : ℝ) ≤ x := by exact_mod_cast hAx
  have hB : (B : ℝ) ≤ x := by exact_mod_cast hBx
  have hfirst : 3 * ((A : ℝ) + B + 2) * F ^ (2 * N) ≤ 12 * (x : ℝ) * F ^ (2 * N) :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hF _)
  have hfirst0 : 0 ≤ 12 * (x : ℝ) * F ^ (2 * N) := by positivity
  have hV : commonPinnedDiscrepancySum W M R A B ≤ 2 * D * ((x : ℝ) * Real.exp (-d * u)) := by
    calc
      _ ≤ 2 * coprimePrimeDiscrepancyPrefixSum B0 L x :=
        commonPinnedDiscrepancySum_le_prefix hW hB0M hWB0 hL hAx hBx
      _ ≤ 2 * (D * ((x : ℝ) * Real.exp (-d * u))) := by gcongr
      _ = _ := by ring
  have hexp : Real.exp (-(d / 2) * u) ^ 2 = Real.exp (-d * u) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpower : (F ^ N) ^ 2 = F ^ (2 * N) := by rw [← pow_mul]; congr 1; omega
  change Real.sqrt (3 * ((A : ℝ) + B + 2) * F ^ (2 * N)) *
    Real.sqrt (commonPinnedDiscrepancySum W M R A B) ≤
      Real.sqrt (24 * D) * (x : ℝ) * F ^ N * Real.exp (-(d / 2) * u)
  calc
    _ = Real.sqrt ((3 * ((A : ℝ) + B + 2) * F ^ (2 * N)) *
        commonPinnedDiscrepancySum W M R A B) := by
      exact (Real.sqrt_mul (by positivity : 0 ≤ 3 * ((A : ℝ) + B + 2) * F ^ (2 * N))
        (commonPinnedDiscrepancySum W M R A B)).symm
    _ ≤ Real.sqrt ((12 * (x : ℝ) * F ^ (2 * N)) *
        (2 * D * ((x : ℝ) * Real.exp (-d * u)))) :=
      Real.sqrt_le_sqrt (mul_le_mul hfirst hV (commonPinnedDiscrepancySum_nonneg _ _ _ _ _) hfirst0)
    _ = Real.sqrt ((24 * D) * ((x : ℝ) * F ^ N * Real.exp (-(d / 2) * u)) ^ 2) := by
      congr 1
      simp only [mul_pow, hexp, hpower]
      ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring

theorem exists_commonPinnedPrimeMass_effective_error :
    ∃ K C a d : ℝ, 0 < K ∧ 0 < C ∧ 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B0 : ℕ,
        1 ≤ B0 ∧ (B0 : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B0 = 1 ∨ B0.Prime) ∧ ∀ m W M R Q A B : ℕ, ∀ y : ℝ,
          1 ≤ m → 1 < R → 0 < W → W ∣ M → B0 ∣ M → W.Coprime B0 →
          A ≤ B → B ≤ x → W * R ^ 2 ≤ A + 1 →
          ((W * R ^ 2 : ℕ) : ℝ) ≤ vaughanCubeRoot x →
          Q.Prime → R < Q → (∀ q : ℕ, q.Prime → q ∣ W → q ≤ A) →
          (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
          ∀ h : Fin (m + 1) → ℕ, Function.Injective h → (∀ i, h i < 2 * (m + 1) ^ 2) →
          ∀ j : Fin (m + 1), (Q : ℝ) ≤ y → (h j : ℝ) * B ≤ y →
          |commonPinnedPrimeMass m W M R Q A B y h j -
              primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
                (commonPinnedPrimeSet A B).card * commonPinnedQuadratic m M R j| ≤
            K * W * x * Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
              (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) *
                Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by
  obtain ⟨D, a, d, hD, ha, hd, X0, hX0, hdist⟩ := exists_effective_primePrefix_distribution
  obtain ⟨C, hC, herror⟩ := exists_commonPinnedPrimeMass_cauchy_error
  refine ⟨Real.sqrt (24 * D), C, a, d / 2, Real.sqrt_pos.mpr (by positivity),
    hC, ha, by positivity, X0, hX0, ?_⟩
  intro x hx
  obtain ⟨B0, hB0pos, hB0bound, hB0, hbound⟩ := hdist x hx
  refine ⟨B0, hB0pos, hB0bound, hB0, ?_⟩
  intro m W M R Q A B y hm hR hW hWM hB0M hWB0 hAB hBx hmod hcube
    hQ hRQ hWsmall hsmall h hinj hshift j hQy hBy
  have henv := commonPinnedCauchyEnvelope_le_expDecay (m := m) hD.le (by omega : 1 ≤ x)
    hW hB0M hWB0 le_rfl (hAB.trans hBx) hBx (hbound (W * R ^ 2) hcube)
  calc
    _ ≤ (W : ℝ) * Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
        commonPinnedCauchyEnvelope m W M R A B :=
      herror m W M R Q A B y hm hR hW hWM hAB hmod hQ hRQ hWsmall hsmall h hinj hshift j hQy hBy
    _ ≤ (W : ℝ) * Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
        (Real.sqrt (24 * D) * (x : ℝ) * (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) *
          Real.exp (-(d / 2) * Real.sqrt (Real.log (x : ℝ)))) :=
      mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedCauchyEnvelope_le_expDecay
#print axioms Erdos4b.FGKMT.exists_commonPinnedPrimeMass_effective_error
