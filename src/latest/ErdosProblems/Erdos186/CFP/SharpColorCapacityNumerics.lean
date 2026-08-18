/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.LargeInputLogNumerics
import ErdosProblems.Erdos186.CFP.IntegerTheoremAssembly

/-!
# Additive sharp-colouring capacity

The populated sharp colouring loses one fixed logarithmic event term in
addition to the requested population of every colour.  A positive source
power absorbs that logarithmic term uniformly.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

set_option autoImplicit false

/-- Population reserved for one colour in the additive robust-colouring
argument. -/
def colorCap (s q C0 : ℕ) : ℕ :=
  s / (4 * C0 * (2 * q + 1))

/-- For fixed colouring and polynomial-event constants, the source lower
bound `m^eta ≤ s` eventually pays both the population term and every
obstacle event. -/
theorem exists_cutoff_sharpColorCapacity
    (q C0 E H : ℕ) (eta : ℝ)
    (hq : 0 < q) (hC0 : 0 < C0) (heta : 0 < eta) :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧
      ∀ {m n s : ℕ}, cutoff ≤ m →
        Nat.log 2 n + 1 ≤ H * (Nat.log 2 m + 1) →
        Real.rpow (m : ℝ) eta ≤ (s : ℝ) →
        (2 * q + 1) *
            ((colorCap s q C0 + 1) +
              (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)) ≤
          s / C0 + 1 := by
  let colors := 2 * q + 1
  let eventCoefficient := H * E + q + 3
  let absorptionCoefficient :=
    4 * C0 * colors * (eventCoefficient + 1)
  obtain ⟨cutoff, hcutoff, hlarge⟩ :=
    exists_cutoff_logPolynomial_le_rpow eta heta absorptionCoefficient 1
  refine ⟨cutoff, hcutoff, ?_⟩
  intro m n s hm hlogn hslow
  let ell := Nat.log 2 m + 1
  have hell : 0 < ell := by dsimp only [ell]; omega
  have hnPow : n ≤ 2 ^ (H * ell) := by
    have hnlt : n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hexponent : Nat.log 2 n + 1 ≤ H * ell := by
      simpa only [ell] using hlogn
    exact hnlt.le.trans (Nat.pow_le_pow_right (by omega) hexponent)
  have hnPower : n ^ E ≤ 2 ^ (H * ell * E) := by
    calc
      n ^ E ≤ (2 ^ (H * ell)) ^ E := Nat.pow_le_pow_left hnPow _
      _ = 2 ^ (H * ell * E) := (pow_mul 2 (H * ell) E).symm
  have hplus : n ^ E + 1 ≤ 2 ^ (H * ell * E + 1) := by
    calc
      n ^ E + 1 ≤ 2 ^ (H * ell * E) + 2 ^ (H * ell * E) := by
        exact Nat.add_le_add hnPower
          (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
      _ = 2 ^ (H * ell * E + 1) := by rw [pow_succ]; ring
  have hqPow : q + 1 ≤ 2 ^ (q + 1) :=
    PreprocessingBilu.self_le_two_pow (q + 1)
  have hevent : (n ^ E + 1) * (q + 1) ≤
      2 ^ (H * ell * E + q + 2) := by
    calc
      (n ^ E + 1) * (q + 1) ≤
          2 ^ (H * ell * E + 1) * 2 ^ (q + 1) :=
        Nat.mul_le_mul hplus hqPow
      _ = 2 ^ (H * ell * E + q + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hlogEvent :
      Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1 ≤
        eventCoefficient * ell := by
    have hlog : Nat.log 2 ((n ^ E + 1) * (q + 1)) ≤
        H * ell * E + q + 2 := by
      calc
        Nat.log 2 ((n ^ E + 1) * (q + 1)) ≤
            Nat.log 2 (2 ^ (H * ell * E + q + 2)) :=
          Nat.log_mono_right hevent
        _ = H * ell * E + q + 2 := Nat.log_pow Nat.one_lt_two _
    have hqell : q + 3 ≤ (q + 3) * ell := by
      simpa only [Nat.mul_comm] using
        Nat.le_mul_of_pos_right (q + 3) hell
    dsimp only [eventCoefficient]
    calc
      Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1 ≤
          H * ell * E + q + 3 := by omega
      _ ≤ (H * E) * ell + (q + 3) * ell := by
        rw [show H * ell * E = (H * E) * ell by ring]
        exact Nat.add_le_add_left hqell _
      _ = (H * E + q + 3) * ell := by ring
  have habsorbReal := hlarge (m := m) hm
  have habsorb : absorptionCoefficient * ell ≤ s := by
    have habsorbReal' :
        ((absorptionCoefficient * ell : ℕ) : ℝ) ≤ (s : ℝ) := by
      calc
        ((absorptionCoefficient * ell : ℕ) : ℝ) =
            ((absorptionCoefficient * (Nat.log 2 m + 1) ^ 1 : ℕ) : ℝ) := by
          simp only [ell, pow_one]
        _ ≤ Real.rpow (m : ℝ) eta := habsorbReal
        _ ≤ (s : ℝ) := hslow
    exact_mod_cast habsorbReal'
  have hoverhead :
      4 * C0 * colors *
          (1 + (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)) ≤ s := by
    calc
      4 * C0 * colors *
          (1 + (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)) ≤
        4 * C0 * colors * (1 + eventCoefficient * ell) := by
          gcongr
      _ ≤ 4 * C0 * colors * ((eventCoefficient + 1) * ell) := by
        gcongr
        have : 1 ≤ ell := hell
        nlinarith
      _ = absorptionCoefficient * ell := by
        dsimp only [absorptionCoefficient]
        ring
      _ ≤ s := habsorb
  have hcap :
      4 * C0 * colors * colorCap s q C0 ≤ s := by
    simpa only [colorCap, mul_assoc] using
      Nat.mul_div_le s (4 * C0 * colors)
  have htotalMul : C0 *
      (colors * ((colorCap s q C0 + 1) +
        (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1))) ≤ s := by
    have hfour : 4 * (C0 *
        (colors * ((colorCap s q C0 + 1) +
          (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)))) ≤ 2 * s := by
      calc
        4 * (C0 *
            (colors * ((colorCap s q C0 + 1) +
              (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)))) =
          4 * C0 * colors * colorCap s q C0 +
            4 * C0 * colors *
              (1 + (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)) := by ring
        _ ≤ s + s := Nat.add_le_add hcap hoverhead
        _ = 2 * s := by ring
    omega
  have hdiv : colors * ((colorCap s q C0 + 1) +
      (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)) ≤ s / C0 := by
    rw [Nat.le_div_iff_mul_le hC0]
    simpa only [Nat.mul_comm] using htotalMul
  exact hdiv.trans (Nat.le_add_right _ _)

end

end Erdos186.CFP.RandomPartition

#print axioms Erdos186.CFP.RandomPartition.exists_cutoff_sharpColorCapacity
