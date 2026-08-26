/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite decision procedures from Lemma 4.1 of
Liam Price (GPT Pro), Large Powers Tile the Integers, 26 June 2026.
Formal author: Codex.

These procedures decide membership in the tile and its difference set. They
do not assert termination of the unbounded search for an admissible new shift.
-/

import ErdosProblems.Erdos477.BadShifts

namespace Erdos477

def powerWitnesses (m : ℤ) : Finset ℕ :=
  (Finset.range (m.natAbs + 1)).filter (fun n => (n : ℤ) ^ 6 = m)

lemma mem_powerWitnesses (m : ℤ) (n : ℕ) :
    n ∈ powerWitnesses m ↔ (n : ℤ) ^ 6 = m := by
  simp only [powerWitnesses, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rw [← h, Int.natAbs_pow]
    simpa using Nat.lt_succ_of_le (Nat.le_self_pow (by decide : (6 : ℕ) ≠ 0) n)

lemma powerWitnesses_nonempty (m : ℤ) :
    (powerWitnesses m).Nonempty ↔ m ∈ PowerValues 6 := by
  simp only [Finset.Nonempty, mem_powerWitnesses, PowerValues, Set.mem_range]

/-- A deliberately loose finite bound avoids needing an integer-root algorithm. -/
def differenceWitnesses (m : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m.natAbs + 1)).product (Finset.range (m.natAbs + 1))).filter
    (fun p => (p.1 : ℤ) ^ 6 - (p.2 : ℤ) ^ 6 = m)

lemma difference_witness_bound {m : ℤ} {u v : ℕ} (hm : m ≠ 0)
    (heq : (u : ℤ) ^ 6 - (v : ℤ) ^ 6 = m) :
    u ≤ m.natAbs ∧ v ≤ m.natAbs := by
  have hne : u ≠ v := by intro h; subst v; simp_all
  have hsep := sixth_power_separation u v hne
  rw [heq, ← Int.natCast_natAbs] at hsep
  have hnat : max u v ^ 5 ≤ m.natAbs := by exact_mod_cast hsep
  have hmax : max u v ≤ m.natAbs :=
    (Nat.le_self_pow (by decide : (5 : ℕ) ≠ 0) (max u v)).trans hnat
  exact ⟨(le_max_left u v).trans hmax, (le_max_right u v).trans hmax⟩

lemma differenceWitnesses_nonempty (m : ℤ) :
    (differenceWitnesses m).Nonempty ↔ m ∈ DifferenceSet (PowerValues 6) := by
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    have heq := (Finset.mem_filter.mp h).2
    exact ⟨(u : ℤ) ^ 6, ⟨u, rfl⟩, (v : ℤ) ^ 6, ⟨v, rfl⟩, heq.symm⟩
  · rintro ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, heq⟩
    by_cases hm : m = 0
    · rw [hm]
      exact ⟨(0, 0), by simp [differenceWitnesses]⟩
    · obtain ⟨hu, hv⟩ := difference_witness_bound hm heq.symm
      refine ⟨(u, v), Finset.mem_filter.mpr ⟨?_, heq.symm⟩⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

/-- Executable membership test; no classical decision procedure is used. -/
def isPowerValue (m : ℤ) : Bool := decide (powerWitnesses m).Nonempty

lemma isPowerValue_eq_true (m : ℤ) : isPowerValue m = true ↔ m ∈ PowerValues 6 := by
  simp only [isPowerValue, decide_eq_true_eq, powerWitnesses_nonempty]

/-- Executable difference-set membership test. -/
def isPowerDifference (m : ℤ) : Bool := decide (differenceWitnesses m).Nonempty

lemma isPowerDifference_eq_true (m : ℤ) :
    isPowerDifference m = true ↔ m ∈ DifferenceSet (PowerValues 6) := by
  simp only [isPowerDifference, decide_eq_true_eq, differenceWitnesses_nonempty]

#print axioms differenceWitnesses_nonempty
-- 'Erdos477.differenceWitnesses_nonempty' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477
