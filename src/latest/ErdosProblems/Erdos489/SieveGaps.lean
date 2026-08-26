import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Positive integers avoiding every divisor satisfying `p`. -/
def divisorSifted (p : ℕ → Prop) (n : ℕ) : Prop :=
  0 < n ∧ ∀ a, p a → ¬a ∣ n

/-- No sifted integer lies strictly between consecutive members of the
increasing enumeration of an infinite sifted set. -/
theorem divisorSifted_consecutive_gap_covered
    (p : ℕ → Prop) [DecidablePred p]
    (hB : Set.Infinite {n | divisorSifted p n}) (i n : ℕ)
    (hleft : Nat.nth (divisorSifted p) i < n)
    (hright : n < Nat.nth (divisorSifted p) (i + 1)) :
    ∃ a, p a ∧ a ∣ n := by
  classical
  have hnpos : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le _) hleft
  by_contra hnone
  push_neg at hnone
  have hnB : divisorSifted p n := ⟨hnpos, hnone⟩
  have hicount : i < Nat.count (divisorSifted p) n :=
    (Nat.lt_nth_iff_count_lt hB).2 hleft
  have hindex : i + 1 ≤ Nat.count (divisorSifted p) n := by omega
  have hmono : Nat.nth (divisorSifted p) (i + 1) ≤
      Nat.nth (divisorSifted p) (Nat.count (divisorSifted p) n) :=
    (Nat.nth_strictMono hB).monotone hindex
  have hnth : Nat.nth (divisorSifted p)
      (Nat.count (divisorSifted p) n) = n := Nat.nth_count hnB
  rw [hnth] at hmono
  exact (not_lt_of_ge hmono) hright

/-- The sifted enumeration is strictly increasing and all of its consecutive
open gaps are covered by forbidden divisors. -/
theorem divisorSifted_enumeration_structure
    (p : ℕ → Prop) [DecidablePred p]
    (hB : Set.Infinite {n | divisorSifted p n}) :
    StrictMono (Nat.nth (divisorSifted p)) ∧
      ∀ i n,
        Nat.nth (divisorSifted p) i < n →
        n < Nat.nth (divisorSifted p) (i + 1) →
        ∃ a, p a ∧ a ∣ n := by
  exact ⟨Nat.nth_strictMono hB,
    divisorSifted_consecutive_gap_covered p hB⟩

end Erdos489
