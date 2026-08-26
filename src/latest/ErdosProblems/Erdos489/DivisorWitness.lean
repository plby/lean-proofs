import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- A chosen divisor satisfying `p`, defaulting to zero if none exists. -/
noncomputable def divisorWitness (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ a, p a ∧ a ∣ n then Classical.choose h else 0

/-- The rank of the chosen divisor in the increasing enumeration of `p`. -/
noncomputable def divisorWitnessRank (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) : ℕ :=
  Nat.count p (divisorWitness p n)

theorem divisorWitness_spec (p : ℕ → Prop) (n : ℕ)
    (h : ∃ a, p a ∧ a ∣ n) :
    p (divisorWitness p n) ∧ divisorWitness p n ∣ n := by
  rw [divisorWitness, dif_pos h]
  exact Classical.choose_spec h

/-- Whenever a witness exists, enumerating at its count recovers it exactly. -/
theorem nth_divisorWitnessRank (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) (h : ∃ a, p a ∧ a ∣ n) :
    Nat.nth p (divisorWitnessRank p n) = divisorWitness p n := by
  exact Nat.nth_count (divisorWitness_spec p n h).1

/-- Hence the modulus at the chosen rank divides the covered integer. -/
theorem nth_divisorWitnessRank_dvd (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) (h : ∃ a, p a ∧ a ∣ n) :
    Nat.nth p (divisorWitnessRank p n) ∣ n := by
  rw [nth_divisorWitnessRank p n h]
  exact (divisorWitness_spec p n h).2

/-- Avoiding the first `R` enumerated moduli forces the chosen divisor rank to
be at least `R`. -/
theorem le_divisorWitnessRank_of_avoid_prefix
    (p : ℕ → Prop) [DecidablePred p] (n R : ℕ)
    (hcov : ∃ a, p a ∧ a ∣ n)
    (havoid : ∀ a ∈ (List.range R).map (Nat.nth p), ¬a ∣ n) :
    R ≤ divisorWitnessRank p n := by
  by_contra hnot
  have hr : divisorWitnessRank p n < R := by omega
  apply havoid (Nat.nth p (divisorWitnessRank p n))
  · exact List.mem_map.mpr ⟨divisorWitnessRank p n,
      List.mem_range.mpr hr, rfl⟩
  · exact nth_divisorWitnessRank_dvd p n hcov

end Erdos489
