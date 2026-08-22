/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianGeometricSchedule
import ErdosProblems.Erdos1165.ProfileA11FixedDeltaCertificate

/-!
# Profile-level A.11--A.12 assembly for the geometric schedule

This file combines the fixed-cutoff dyadic schedule with the uniform Taylor
certificate.  The result is the exact constrained-profile lower bound; all
remaining work is the explicit additive cost estimate for the schedule.
-/

namespace Erdos1165.GaussianGeometricProfileAssembly

noncomputable section

open AppendixFirstMoment GaussianBlockFactorization GaussianMultiBlockProfile
  AppendixA11A12OnePoint GaussianGeometricSchedule
  ProfileA11FixedDeltaCertificate

/-- The geometric schedule automatically satisfies the complete shifted
A.11 certificate once its fixed first scale is at least `18^5`. -/
theorem geometricSchedule_embeddedTailA11Certificate
    {s J n : ℕ} (hs : 18 ^ 5 ≤ s) :
    EmbeddedTailA11Certificate n s (1 / 5 : ℝ) 2 1 10
      (geometricSchedule s J n) := by
  have hcw := geometricSchedule_width_center (J := J) (n := n)
    (show 1 ≤ s by omega)
  apply embeddedTailA11Certificate_one_fifth hs hcw.1
  intro b hb l hl
  have hw := hcw.2 b hb l hl
  convert hw using 1 <;> norm_num

/-- Fully checked, cycle-free A.11--A.12 lower bound for the genuine
fixed-prefix geometric schedule. -/
theorem geometricSchedule_profileLower_le
    {s J n : ℕ} (hs : 18 ^ 5 ≤ s)
    (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s))
    (hlarge : (2560 * 4096 : ℝ) ≤ (s : ℝ) ^ (2 / 5 : ℝ)) :
    multiblockProfileLower n (1 / 5 : ℝ) 2 1 10
        (geometricSchedule s J n) ≤
      constrainedProfileWeight n (1 / 5 : ℝ) := by
  have hs32 : 32 ≤ s := by omega
  have hconsecutive := geometricSchedule_consecutive
    (show 1 ≤ s by omega) hterminal
  have hend := geometricSchedule_end hterminal
  have hscale := geometricSchedule_scale hs32 hterminal hupper hlarge
  have hcw := geometricSchedule_width_center (J := J) (n := n)
    (show 1 ≤ s by omega)
  have hstart : ∀ c ∈ geometricSchedule s J n, 0 < c.start := by
    intro c hc
    exact lt_of_lt_of_le (by omega)
      (geometricSchedule_start_ge (show 1 ≤ s by omega) c hc)
  have hpowOne : 1 ≤ 2 ^ J := Nat.one_le_pow _ _ (by omega)
  have hsn : s ≤ n := by
    have hmul : s ≤ 2 ^ J * s := by
      simpa only [one_mul] using Nat.mul_le_mul_right s hpowOne
    exact hmul.trans hterminal
  have hn2 : 2 ≤ n := (show 2 ≤ s by omega).trans hsn
  have cert := geometricSchedule_embeddedTailA11Certificate
    (J := J) (n := n) hs
  cases J with
  | zero =>
      change multiblockProfileLower n (1 / 5 : ℝ) 2 1 10
          ([terminalGeometricBlock s n]) ≤ _
      apply multiblockProfileLower_le_constrainedProfileWeight
        hn2 (show 2 ≤ (terminalGeometricBlock s n).start by simp; omega)
        hconsecutive hend hstart hscale
      · exact hcw.1
      · intro c hc l hl
        have hw := hcw.2 c hc l hl
        convert hw using 1 <;> norm_num
      · exact cert
  | succ j =>
      change multiblockProfileLower n (1 / 5 : ℝ) 2 1 10
          (completeGeometricBlock s :: geometricSchedule (2 * s) j n) ≤ _
      apply multiblockProfileLower_le_constrainedProfileWeight
        hn2 (show 2 ≤ (completeGeometricBlock s).start by simp; omega)
        hconsecutive hend hstart hscale
      · exact hcw.1
      · intro c hc l hl
        have hw := hcw.2 c hc l hl
        convert hw using 1 <;> norm_num
      · exact cert

end

end Erdos1165.GaussianGeometricProfileAssembly
