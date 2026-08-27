/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTotalMainGrowth
import ErdosProblems.Erdos4b.FGKMTPinnedPrimeMainLower

/-!
# Exact common scalars for the two sieve-weight means

The finite Euler factor and literal prime count are retained in the
gain. Neither scalar depends on a label prime or a pinned coordinate.
-/

namespace Erdos4b.FGKMT

noncomputable section

def commonWeightTau (k W M R x : ℕ) (h : Fin k → ℕ) : ℝ :=
  2 * commonWeightMassScale k W M R h * Real.log (x : ℝ) ^ k

def commonWeightGain (m B W R x : ℕ) : ℝ :=
  ((B.totient : ℝ) / B) * Real.log (R : ℝ) * commonPinnedVariationalGain m (B * W) R *
    (commonPinnedPrimeSet (x / 2) x).card / (x : ℝ)

theorem commonWeightTau_total_identity {k W M R x : ℕ}
    (hlog : Real.log (x : ℝ) ≠ 0) (h : Fin k → ℕ) (y : ℝ) :
    commonWeightTau k W M R x h * y / Real.log (x : ℝ) ^ k =
      2 * y * commonWeightMassScale k W M R h := by
  unfold commonWeightTau
  field_simp

theorem commonPinnedVariationalGain_div_dim (m M R : ℕ) :
    commonPinnedVariationalGain m M R / (m + 1 : ℕ) =
      commonPinnedDensityRatio m M R ^ 2 *
        (dimensionFaceEnergy (m + 1) m / dimensionProfileEnergy (m + 1) (m + 1)) := by
  have hk : (m + 1 : ℕ) ≠ (0 : ℝ) := by positivity
  calc
    _ = ((m + 1 : ℕ) / (m + 1 : ℕ)) *
        (commonPinnedDensityRatio m M R ^ 2 *
          (dimensionFaceEnergy (m + 1) m / dimensionProfileEnergy (m + 1) (m + 1))) := by
      dsimp only [commonPinnedVariationalGain]
      ring
    _ = _ := by rw [div_self hk, one_mul]

theorem commonPinnedPrimeMainTerm_eq_massScale_mul_gain {m B W R Q x : ℕ}
    (hm : 1 ≤ m) (hlog : 10000 ≤ Real.log (m + 1 : ℕ))
    (hB : 0 < B) (hW : 0 < W) (hBW : B.Coprime W) (hQ : Q.Coprime W)
    (hR : 1 < R) (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B * W)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    commonPinnedPrimeMainTerm m W (B * W) R Q (x / 2) x h j =
      commonWeightMassScale (m + 1) W (B * W) R h *
        (commonWeightGain m B W R x / (m + 1 : ℕ)) * x := by
  have hM := Nat.mul_pos hB hW
  have hmain := commonSieveMainTerm_pos (by omega : 2 ≤ m + 1) hlog hM hR hsmall
  have hpin := (div_eq_iff hmain.ne').mp
    (commonPinnedMainTerm_div_total hm hlog hM hR hsmall)
  have hcancel := totientDensity_presieve_cancellation hB hW hBW
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have hgain : commonWeightGain m B W R x / (m + 1 : ℕ) * x =
      ((B.totient : ℝ) / B) * Real.log R *
        (commonPinnedVariationalGain m (B * W) R / (m + 1 : ℕ)) *
          (commonPinnedPrimeSet (x / 2) x).card := by
    unfold commonWeightGain
    field_simp
  rw [mul_assoc, hgain, commonPinnedVariationalGain_div_dim]
  unfold commonPinnedPrimeMainTerm commonWeightMassScale
  rw [primePreSieveDensity_eq hW hQ, hpin]
  simp only [Nat.cast_mul]
  calc
    _ = (((W : ℝ) / W.totient) * ((B * W).totient : ℝ) / (B * W)) *
        (preSieveDensity W (fun i => (h i : ℤ)) *
          commonSieveMainTerm (m + 1) (B * W) R * Real.log R *
          commonPinnedDensityRatio m (B * W) R ^ 2 *
          (dimensionFaceEnergy (m + 1) m / dimensionProfileEnergy (m + 1) (m + 1)) *
          (commonPinnedPrimeSet (x / 2) x).card) := by ring
    _ = _ := by rw [hcancel]; ring

theorem commonPinnedPrimeMainTerm_tau_gain_identity {m B W R Q x : ℕ}
    (hm : 1 ≤ m) (hlog : 10000 ≤ Real.log (m + 1 : ℕ))
    (hB : 0 < B) (hW : 0 < W) (hBW : B.Coprime W) (hQ : Q.Coprime W)
    (hR : 1 < R) (hx : 0 < x) (hlogx : Real.log (x : ℝ) ≠ 0)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B * W)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    commonPinnedPrimeMainTerm m W (B * W) R Q (x / 2) x h j =
      commonWeightTau (m + 1) W (B * W) R x h *
        (commonWeightGain m B W R x / (m + 1 : ℕ)) * x /
          (2 * Real.log (x : ℝ) ^ (m + 1)) := by
  rw [commonPinnedPrimeMainTerm_eq_massScale_mul_gain hm hlog hB hW hBW hQ hR hx hsmall]
  unfold commonWeightTau
  field_simp

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonWeightTau_total_identity
#print axioms Erdos4b.FGKMT.commonPinnedPrimeMainTerm_tau_gain_identity
