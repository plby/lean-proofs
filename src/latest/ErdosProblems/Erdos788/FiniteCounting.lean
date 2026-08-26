import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary finite counting interfaces

The reconstruction and carry arguments repeatedly factor an output through a
finite description type.  The lemmas here make those cardinality steps
explicit.
-/

open scoped BigOperators

namespace Erdos788

theorem local_row_has_suffix_slack {m t tail : ℕ}
    (ht : t < m) (hblock : m - 1 ≤ tail) :
    t ≤ (m - t - 1) + tail := by
  omega

theorem sum_of_unit_costs_le_card {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℕ) (hw : ∀ i ∈ s, w i ≤ 1) :
    ∑ i ∈ s, w i ≤ s.card := by
  simpa using! Finset.sum_le_sum hw

theorem card_binary_assignments (t : ℕ) :
    Fintype.card (Fin t → Bool) = 2 ^ t := by
  simp

theorem card_binary_tables (p t : ℕ) [NeZero p] :
    Fintype.card ((Fin t → Bool) → ZMod p) = p ^ (2 ^ t) := by
  simp

theorem bertrand_interface (Q : ℕ) (hQ : Q ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ Q < q ∧ q ≤ 2 * Q :=
  Nat.exists_prime_lt_and_le_two_mul Q hQ

theorem fixed_length_digit_words_card {p : ℕ} (hp : 1 < p) (k : ℕ) :
    (List.fixedLengthDigits hp k).card = p ^ k :=
  List.card_fixedLengthDigits hp k

theorem one_bit_raw_carry {a b p : ℕ} (hp : 0 < p)
    (ha : a < p) (hb : b < p) :
    (a + b) / p ≤ 1 := by
  have hsum : a + b < 2 * p := by omega
  have hquot : (a + b) / p < 2 :=
    (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using! hsum)
  omega

theorem card_image_of_factorization {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq γ]
    (output : α → γ) (code : α → β) (decode : β → γ)
    (hfactor : ∀ x, output x = decode (code x)) :
    (Finset.univ.image output).card ≤ Fintype.card β := by
  calc
    (Finset.univ.image output).card
        ≤ (Finset.univ.image decode).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz ⊢
          obtain ⟨x, rfl⟩ := hz
          exact ⟨code x, (hfactor x).symm⟩
    _ ≤ Fintype.card β := by
      simpa using! Finset.card_image_le
        (s := (Finset.univ : Finset β)) (f := decode)

theorem carry_description_bound {α γ : Type*} [Fintype α] [DecidableEq γ]
    (k : ℕ) (output : α → γ) (carry : α → (Fin k → Bool))
    (decode : (Fin k → Bool) → γ)
    (hfactor : ∀ x, output x = decode (carry x)) :
    (Finset.univ.image output).card ≤ 2 ^ k := by
  simpa [card_binary_assignments] using!
    card_image_of_factorization output carry decode hfactor

end Erdos788
