/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.CertificateExhaustion

/-!
# Efficient one-step extension of exhaustion chains

Large exhaustion tables should reuse their already-verified prefix
propositionally.  The lemmas here append one level and one transition table
without normalizing the complete prefix again.
-/

namespace Erdos76.CertificateExhaustion.ExhaustionData

open CertificateChecker

variable {n : ℕ} [NeZero n]

/-- Append one level and its incoming transition table to an exhaustion
chain. -/
def extend (d : ExhaustionData n)
    (next : Array (BitVec (edgeCount n)))
    (table : Array (Array (Option (Transition n)))) : ExhaustionData n := {
  levels := d.levels.push next
  steps := d.steps.push table
}

@[simp] lemma level_extend_lt (d : ExhaustionData n) (next table) (k : ℕ)
    (hk : k < d.levels.size) :
    (extend d next table).level k = d.level k := by
  have hne : k ≠ d.levels.size := Nat.ne_of_lt hk
  simp [extend, level, Array.getElem?_push, hk, hne]

@[simp] lemma level_extend_last (d : ExhaustionData n) (next table) :
    (extend d next table).level d.levels.size = next := by
  simp [extend, level]

@[simp] lemma step_extend_lt (d : ExhaustionData n) (next table) (k : ℕ)
    (hk : k < d.steps.size) :
    (extend d next table).step k = d.step k := by
  have hne : k ≠ d.steps.size := Nat.ne_of_lt hk
  simp [extend, step, Array.getElem?_push, hk, hne]

@[simp] lemma step_extend_last (d : ExhaustionData n) (next table) :
    (extend d next table).step d.steps.size = table := by
  simp [extend, step]

/-- Extend a valid exhaustion chain by one separately checked step. -/
theorem Valid.extend {d : ExhaustionData n} (hd : d.Valid)
    {next : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))}
    (hstep : StepValid (d.level d.steps.size) next table) :
    (extend d next table).Valid := by
  have hlevels : d.levels.size = d.steps.size + 1 := hd.1
  have hzero : 0 < d.levels.size := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (d.levels.push next).size = (d.steps.push table).size + 1
    simp only [Array.size_push]
    omega
  · rw [level_extend_lt d next table 0 hzero]
    exact hd.2.1
  · rw [level_extend_lt d next table 0 hzero]
    exact hd.2.2.1
  · rintro ⟨k, hk⟩
    have hstepsize :
        (Erdos76.CertificateExhaustion.ExhaustionData.extend
          d next table).steps.size = d.steps.size + 1 := by
      simp [Erdos76.CertificateExhaustion.ExhaustionData.extend]
    rw [hstepsize] at hk
    have hk' : k < d.steps.size + 1 := hk
    rcases Nat.lt_add_one_iff_lt_or_eq.mp hk' with hkold | rfl
    · have hklevel : k < d.levels.size := by omega
      have hksucc : k + 1 < d.levels.size := by omega
      rw [step_extend_lt d next table k hkold,
        level_extend_lt d next table k hklevel,
        level_extend_lt d next table (k + 1) hksucc]
      exact hd.stepValid k hkold
    · have hklast : d.steps.size + 1 = d.levels.size := by omega
      rw [step_extend_last d next table,
        level_extend_lt d next table d.steps.size (by omega),
        hklast, level_extend_last d next table]
      exact hstep

/-- The level at the new final step index is definitionally the appended
level, exposed propositionally to avoid unfolding a large prefix. -/
theorem Valid.extend_lastLevel {d : ExhaustionData n} (hd : d.Valid)
    {next : Array (BitVec (edgeCount n))}
    {table : Array (Array (Option (Transition n)))} :
    (Erdos76.CertificateExhaustion.ExhaustionData.extend d next table).level
        (Erdos76.CertificateExhaustion.ExhaustionData.extend
          d next table).steps.size = next := by
  have hsize :
      (Erdos76.CertificateExhaustion.ExhaustionData.extend
        d next table).steps.size = d.levels.size := by
    change (d.steps.push table).size = d.levels.size
    rw [Array.size_push, hd.1]
  rw [hsize, level_extend_last]

end Erdos76.CertificateExhaustion.ExhaustionData
