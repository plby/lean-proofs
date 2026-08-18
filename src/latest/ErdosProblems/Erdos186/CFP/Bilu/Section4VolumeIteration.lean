/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section9ContainerIntegration

/-!
# Bilu Section 4: the volume-decay iteration

The last paragraph of Bilu Section 4 chooses an admissible body whose
volume is less than twice the infimum of all admissible volumes.  If its
volume were above the desired uniform threshold, Lemma 4.5 would produce
a second admissible body of at most half the volume, contradicting the
choice.

The theorem below is the exact order-theoretic core of that argument.  It
is stated for an arbitrary nonempty set of nonnegative real volumes, so it
can be applied directly once Sections 9.1--9.3 have proved that their
replacement body remains admissible.
-/

namespace Erdos186.CFP.Bilu.Section4VolumeIteration

open Set

/-- The infimum argument in Bilu Section 4.  A nonempty class of
nonnegative admissible volumes which admits a factor-two improvement above
`bound` must already contain a volume at most `bound`.

This formulation deliberately asks only that the smaller volume remain in
the same class.  It therefore packages both the minimal-rank repair of
Section 9.2 and the affine-span repair of Section 9.3 into the single fact
that admissibility is preserved. -/
theorem exists_le_of_half_decay
    (volumes : Set ℝ) (hne : volumes.Nonempty)
    (hnonneg : ∀ v ∈ volumes, 0 ≤ v)
    (bound : ℝ) (hbound : 0 < bound)
    (hdecay : ∀ v ∈ volumes, bound < v →
      ∃ w ∈ volumes, w ≤ v / 2) :
    ∃ v ∈ volumes, v ≤ bound := by
  by_contra hnone
  push Not at hnone
  let m : ℝ := sInf volumes
  have hm_nonneg : 0 ≤ m := by
    exact le_csInf hne hnonneg
  have hbound_le : bound ≤ m := by
    apply le_csInf hne
    intro v hv
    exact (hnone v hv).le
  have hm_pos : 0 < m := hbound.trans_le hbound_le
  have hm_two : m < 2 * m := by linarith
  obtain ⟨v, hv, hv_two⟩ := exists_lt_of_csInf_lt hne hm_two
  obtain ⟨w, hw, hw_half⟩ := hdecay v hv (hnone v hv)
  have hhalf_lt : v / 2 < m := by linarith
  have hw_lt : w < m := hw_half.trans_lt hhalf_lt
  have hm_le_w : m ≤ w := csInf_le ⟨0, hnonneg⟩ hw
  exact (not_lt_of_ge hm_le_w) hw_lt

/-- Strict decay is equivalent to the source's more natural inequality
`2 * newVolume < oldVolume`. -/
theorem exists_le_of_two_mul_decay
    (volumes : Set ℝ) (hne : volumes.Nonempty)
    (hnonneg : ∀ v ∈ volumes, 0 ≤ v)
    (bound : ℝ) (hbound : 0 < bound)
    (hdecay : ∀ v ∈ volumes, bound < v →
      ∃ w ∈ volumes, 2 * w < v) :
    ∃ v ∈ volumes, v ≤ bound := by
  apply exists_le_of_half_decay volumes hne hnonneg bound hbound
  intro v hv hbv
  obtain ⟨w, hw, htw⟩ := hdecay v hv hbv
  exact ⟨w, hw, by linarith⟩

/-- Polynomial form of the Section 4 iteration.  This is the form obtained
after applying Proposition 7.5/Lemma 4.5: for a positive exponent, the
displayed power inequality above `bound` forces a strict factor-two volume
improvement. -/
theorem exists_le_of_pow_decay
    (q : ℕ) (hq : 0 < q)
    (volumes : Set ℝ) (hne : volumes.Nonempty)
    (hpos : ∀ v ∈ volumes, 0 < v)
    (bound : ℝ) (hbound : 0 < bound)
    (hstep : ∀ v ∈ volumes, bound < v →
      ∃ w ∈ volumes, (2 * w) ^ q ≤ bound * v ^ (q - 1)) :
    ∃ v ∈ volumes, v ≤ bound := by
  apply exists_le_of_two_mul_decay volumes hne
      (fun v hv ↦ (hpos v hv).le) bound hbound
  intro v hv hbv
  obtain ⟨w, hw, hpow⟩ := hstep v hv hbv
  refine ⟨w, hw, ?_⟩
  have hv_pos := hpos v hv
  have hmul_lt : bound * v ^ (q - 1) < v * v ^ (q - 1) :=
    mul_lt_mul_of_pos_right hbv (pow_pos hv_pos _)
  have hvpow : v * v ^ (q - 1) = v ^ q := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    simp [pow_succ, mul_comm]
  have hpow_lt : (2 * w) ^ q < v ^ q := by
    rw [← hvpow]
    exact hpow.trans_lt hmul_lt
  exact lt_of_pow_lt_pow_left₀ q hv_pos.le hpow_lt

end Erdos186.CFP.Bilu.Section4VolumeIteration

#print axioms Erdos186.CFP.Bilu.Section4VolumeIteration.exists_le_of_half_decay
#print axioms Erdos186.CFP.Bilu.Section4VolumeIteration.exists_le_of_two_mul_decay
#print axioms Erdos186.CFP.Bilu.Section4VolumeIteration.exists_le_of_pow_decay
