/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredScaledPhysicalDensityTargetCertificate

/-!
# Integer division bounds for scaled CFP reserve certificates

The source splits the available scale among a fixed number of random
colours.  These elementary lemmas keep the rounding loss explicit and
discharge the three scale inequalities consumed by the contracted
Corollary 2.17 certificate.
-/

namespace Erdos186.CFP

/-- The canonical scale assigned to each of `q+1` colours. -/
def colorSourceScale (s q : ℕ) : ℕ := s / (q + 1)

theorem colorSourceScale_mul_colors_le (s q : ℕ) :
    (q + 1) * colorSourceScale s q ≤ s := by
  simpa only [colorSourceScale, Nat.mul_comm] using
    Nat.div_mul_le_self s (q + 1)

/-- Once two units of scale per colour are available, doubling the rounded
per-colour scale recovers the full source scale. -/
theorem le_two_mul_colors_mul_colorSourceScale
    {s q : ℕ} (hroom : 2 * (q + 1) ≤ s) :
    s ≤ 2 * (q + 1) * colorSourceScale s q := by
  let a := q + 1
  have ha : 0 < a := by dsimp only [a]; omega
  have hdiv : 2 ≤ s / a := by
    exact (Nat.le_div_iff_mul_le ha).2 (by simpa only [a] using hroom)
  have hmod : s % a < a := Nat.mod_lt _ ha
  have hdecomp := Nat.div_add_mod s a
  have hrem : s % a ≤ a * (s / a) := by
    have hone : 1 ≤ s / a := by omega
    exact hmod.le.trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hone)
  have hs : s ≤ 2 * a * (s / a) := by
    calc
      s = a * (s / a) + s % a := hdecomp.symm
      _ ≤ a * (s / a) + a * (s / a) := by gcongr
      _ = 2 * a * (s / a) := by ring
  simpa only [a, colorSourceScale] using hs

/-- Dividing the number of colours by a positive density constant cannot
make the contracted scale exceed the original source budget. -/
theorem colorSourceScale_mul_colors_div_le
    (s q denseConstant : ℕ) (_hdense : 0 < denseConstant) :
    colorSourceScale s q * ((q + 1) / denseConstant) ≤ s := by
  calc
    colorSourceScale s q * ((q + 1) / denseConstant) ≤
        colorSourceScale s q * (q + 1) := by
      gcongr
      exact Nat.div_le_self _ _
    _ = (q + 1) * colorSourceScale s q := by rw [Nat.mul_comm]
    _ ≤ s := colorSourceScale_mul_colors_le s q

/-- Bundled form matching the three scalar side conditions of the scaled
physical-density certificate. -/
theorem colorSourceScale_certificate_bounds
    {s q denseConstant : ℕ}
    (hroom : 2 * (q + 1) ≤ s) (hdense : 0 < denseConstant) :
    (q + 1) * colorSourceScale s q ≤ s ∧
      s ≤ 2 * (q + 1) * colorSourceScale s q ∧
      colorSourceScale s q * ((q + 1) / denseConstant) ≤ s := by
  exact ⟨colorSourceScale_mul_colors_le s q,
    le_two_mul_colors_mul_colorSourceScale hroom,
    colorSourceScale_mul_colors_div_le s q denseConstant hdense⟩

end Erdos186.CFP

#print axioms Erdos186.CFP.colorSourceScale_certificate_bounds
