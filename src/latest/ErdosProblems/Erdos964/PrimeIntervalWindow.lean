import ErdosProblems.Erdos964.PrimeCountingWindow

/-!
# Prime counts between two endpoints in a multiplicative window
-/

namespace Erdos964

theorem primeInterval_card_cast (a b : ℕ) (hab : a ≤ b) :
    (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) =
      (Nat.primeCounting b : ℝ) - Nat.primeCounting a := by
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  rw [primeInterval_eq_primesLE_sdiff, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

theorem exists_primeInterval_multiplicative_window_error (B : ℝ) (hB : 1 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y u v : ℝ, Y₀ ≤ Y → Y ≤ u → u ≤ v → v ≤ B * Y →
      |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime).card : ℝ) -
        (v - u) / Real.log Y| ≤ ε * (Y / Real.log Y) := by
  have hB0 : 0 < B := by linarith
  let η := ε / (2 * B)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨Y₀, hY₀, herror⟩ := exists_primeCounting_multiplicative_window_error B hB η hη
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y u v hY hYu huv hvB
  have hLY : 0 < Real.log Y := Real.log_pos (by linarith)
  have heU := herror Y u hY hYu (huv.trans hvB)
  have heV := herror Y v hY (hYu.trans huv) hvB
  rw [primeInterval_card_cast _ _ (Nat.floor_le_floor huv), sub_div, sub_sub_sub_comm]
  calc
    _ ≤ |(Nat.primeCounting ⌊v⌋₊ : ℝ) - v / Real.log Y| +
        |(Nat.primeCounting ⌊u⌋₊ : ℝ) - u / Real.log Y| := abs_sub _ _
    _ ≤ η * (v / Real.log Y) + η * (u / Real.log Y) := add_le_add heV heU
    _ = η * ((v + u) / Real.log Y) := by ring
    _ ≤ η * ((2 * B * Y) / Real.log Y) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hLY.le) hη.le
    _ = _ := by dsimp only [η]; field_simp

end Erdos964
