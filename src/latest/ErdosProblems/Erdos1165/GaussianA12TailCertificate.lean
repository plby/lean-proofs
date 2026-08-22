/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianA12Schedule
import ErdosProblems.Erdos1165.ProfileA11FixedDeltaCertificate
import ErdosProblems.Erdos1165.Proposition13Scales

/-! Compatibility wrapper for the finite late-block certificate. -/

namespace Erdos1165.GaussianA12TailCertificate

noncomputable section

open AppendixFirstMoment GaussianBlockFactorization GaussianMultiBlockProfile
  GaussianA12Schedule AppendixA11A12OnePoint Proposition13Scales
  ProfileA11FixedDeltaCertificate

theorem lateBlock_embeddedTailA11Certificate
    {n : ℕ} (hn : 2 * (18 ^ 5) ≤ n) :
    EmbeddedTailA11Certificate n (lateBlockStart n)
      chosenProfileDelta 2 1 10 (lateBlockSchedule n chosenProfileDelta) := by
  have hstartLarge : 18 ^ 5 ≤ lateBlockStart n := by
    unfold lateBlockStart
    omega
  have hcenter : ∀ c ∈ lateBlockSchedule n chosenProfileDelta, ∀ l,
      BlockContains c l → c.radius ≤ profileCenter l := by
    intro c hc l hl
    simp only [lateBlockSchedule, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact lateBlock_radius_le_center (show 4 ≤ n by omega)
      (by norm_num [chosenProfileDelta]) (by norm_num [chosenProfileDelta]) hl
  have hwidth : ∀ c ∈ lateBlockSchedule n chosenProfileDelta, ∀ l,
      BlockContains c l → (c.radius : ℝ) ≤ (l : ℝ) ^ (1 + (1 / 5 : ℝ)) := by
    intro c hc l hl
    simp only [lateBlockSchedule, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact lateBlock_radius_le_envelope (show 4 ≤ n by omega)
      (by norm_num [chosenProfileDelta]) (by norm_num [chosenProfileDelta]) hl
  simpa only [chosenProfileDelta] using
    embeddedTailA11Certificate_one_fifth hstartLarge hcenter hwidth

end

end Erdos1165.GaussianA12TailCertificate
