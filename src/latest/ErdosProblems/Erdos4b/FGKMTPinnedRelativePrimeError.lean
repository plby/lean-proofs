/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedAbsoluteSaving
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeMainLower

/-!
# Relative progression error on the genuine prime main scale

The denominator includes the actual presieve density, actual upper-half
prime count, and common pinned main term. Its quantitative lower bound
preserves half of the uniform exponential distribution saving.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem div_expDecay_le_of_main_lower {E P x d u : ℝ} (hx : 0 < x)
    (hE : E ≤ x * Real.exp (-d * u))
    (hP : x * Real.exp (-(d / 2) * u) ≤ P) :
    E / P ≤ Real.exp (-(d / 2) * u) := by
  have hPpos : 0 < P := (mul_pos hx (Real.exp_pos _)).trans_le hP
  apply (div_le_iff₀ hPpos).mpr
  calc
    _ ≤ x * Real.exp (-d * u) := hE
    _ = Real.exp (-(d / 2) * u) * (x * Real.exp (-(d / 2) * u)) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le

theorem exists_commonPinnedPrimeMass_relative_progression_error :
    ∃ a d : ℝ, 0 < a ∧ 0 < d ∧ ∀ H : ℝ, 0 < H → ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B0 : ℕ,
        1 ≤ B0 ∧ (B0 : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B0 = 1 ∨ B0.Prime) ∧ ∀ m W R Q : ℕ, ∀ y : ℝ,
          1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
          1 < R → 1 ≤ Real.log (R : ℝ) → 0 < W → B0.Coprime W → Q.Coprime W →
          W * R ^ 2 ≤ x / 2 + 1 → ((W * R ^ 2 : ℕ) : ℝ) ≤ vaughanCubeRoot x →
          (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
          (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2) →
          Q.Prime → R < Q → (∀ q : ℕ, q.Prime → q ∣ W → q ≤ x / 2) →
          (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B0 * W) →
          ∀ h : Fin (m + 1) → ℕ, Function.Injective h → (∀ i, h i < 2 * (m + 1) ^ 2) →
          ∀ j : Fin (m + 1), (Q : ℝ) ≤ y → (h j : ℝ) * x ≤ y →
          ∀ n : ℤ, preSieveCondition W (fun i => (h i : ℤ)) n →
          |commonPinnedPrimeMass m W (B0 * W) R Q (x / 2) x y h j -
              primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
                (commonPinnedPrimeSet (x / 2) x).card * commonPinnedQuadratic m (B0 * W) R j| /
            commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j ≤
              Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by
  obtain ⟨a, d, ha, hd, habsolute⟩ := exists_commonPinnedPrimeMass_absolute_saving
  refine ⟨a, d / 2, ha, by positivity, ?_⟩
  intro H hH
  obtain ⟨Xa, hXa, herror⟩ := habsolute H hH
  obtain ⟨Xg, hXg⟩ := eventually_atTop.mp
    (eventually_commonPinnedPrimeMainTerm_exp_lower hH (by positivity : 0 < d / 2))
  refine ⟨max Xa Xg, hXa.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxa : Xa ≤ x := (le_max_left _ _).trans hx
  have hxg : Xg ≤ x := (le_max_right _ _).trans hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  obtain ⟨B0, hB0pos, hB0bound, hB0, hbound⟩ := herror x hxa
  refine ⟨B0, hB0pos, hB0bound, hB0, ?_⟩
  intro m W R Q y hm hlog hR hRlog hW hBW hQW hmod hcube hdim hsize
    hQ hRQ hWsmall hsmall h hinj hshift j hQy hxy n hn
  have habs := hbound m W (B0 * W) R Q (x / 2) x y hm hR hW
    (dvd_mul_left W B0) (dvd_mul_right B0 W) hBW.symm (Nat.div_le_self x 2)
    le_rfl hmod hcube hdim hsize hQ hRQ hWsmall hsmall h hinj hshift j hQy hxy
  have hmain := hXg x hxg m B0 W R Q hm hlog hdim hB0 hW hBW hQW hRlog hsmall hsize h j n hn
  exact div_expDecay_le_of_main_lower hxpos habs hmain

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedPrimeMass_relative_progression_error
