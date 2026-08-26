import Mathlib

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite counts for periodic predicates

These lemmas let later modules compare a footprint in one period with its
pullback to any common multiple, using only finite cardinalities.
-/

namespace Erdos486

/-- Repeating a predicate of period `d` through `k` complete blocks multiplies
its count by `k`. -/
theorem card_filter_range_mul_of_periodic (P : ℕ → Prop) [DecidablePred P]
    (d k : ℕ) (hP : Function.Periodic P d) :
    ((Finset.range (k * d)).filter P).card =
      k * ((Finset.range d).filter P).card := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsplit :
          Finset.Ico 0 (k * d + d) =
            Finset.Ico 0 (k * d) ∪ Finset.Ico (k * d) (k * d + d) := by
        exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_add_right _ _)).symm
      have hdisj :
          Disjoint
            ((Finset.Ico 0 (k * d)).filter P)
            ((Finset.Ico (k * d) (k * d + d)).filter P) := by
        apply Finset.disjoint_left.2
        intro n hn₁ hn₂
        simp only [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
        omega
      rw [Nat.succ_mul, Finset.range_eq_Ico, hsplit, Finset.filter_union,
        Finset.card_union_of_disjoint hdisj]
      rw [Finset.range_eq_Ico] at ih
      rw [ih, Nat.filter_Ico_card_eq_of_periodic (k * d) d P hP,
        Nat.count_eq_card_filter_range, Finset.range_eq_Ico]
      ring

/-- If `d ∣ L`, pulling a predicate on residues modulo `d` back to
`range L` preserves its normalized density exactly. -/
theorem card_filter_range_mod_of_dvd (P : ℕ → Prop) [DecidablePred P]
    {d L : ℕ} (hdiv : d ∣ L) :
    d * ((Finset.range L).filter fun n ↦ P (n % d)).card =
      L * ((Finset.range d).filter P).card := by
  obtain ⟨k, rfl⟩ := hdiv
  have hperiodic : Function.Periodic (fun n ↦ P (n % d)) d := by
    intro n
    simp
  have hcount :
      ((Finset.range (d * k)).filter fun n ↦ P (n % d)).card =
        k * ((Finset.range d).filter fun n ↦ P (n % d)).card := by
    simpa [Nat.mul_comm] using
      card_filter_range_mul_of_periodic (fun n ↦ P (n % d)) d k hperiodic
  rw [hcount]
  have hbase :
      ((Finset.range d).filter fun n ↦ P (n % d)).card =
        ((Finset.range d).filter P).card := by
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨hn, by simpa [Nat.mod_eq_of_lt hn] using hp⟩
    · rintro ⟨hn, hp⟩
      exact ⟨hn, by simpa [Nat.mod_eq_of_lt hn] using hp⟩
  rw [hbase]
  ring

end Erdos486
