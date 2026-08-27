import Arxiv.Arxiv2411_18291.EmbeddingExtensions
import Arxiv.Arxiv2411_18291.ExponentialBound
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Quantitative counts of root-preserving embeddings

For an ambient set at least four times the square of the pattern size, at
least three quarters of the unrestricted assignments are injective extensions
of the prescribed root map. This makes the initial choice count in the random
greedy argument explicit, before subtracting forbidden choices.
-/

noncomputable section

namespace Arxiv2411_18291

theorem pow_sub_three_quarters {N M : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N) (m : ℕ)
    (hsize : 4 * m * M ≤ N) : (3 / 4 : ℝ) * N ^ m ≤ (N - M) ^ m := by
  obtain _ | m := m
  · norm_num
  have hN : 0 ≤ N := hM.trans hMN
  have hb := pow_add_mul_le_add_pow (a := N) (b := -M) hN (by linarith) (m + 1)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← sub_eq_add_neg] at hb
  simp only [Nat.cast_add, Nat.cast_one] at hsize
  have hp := mul_le_mul_of_nonneg_right hsize (pow_nonneg hN m)
  rw [pow_succ N m] at hb ⊢
  nlinarith

theorem descFactorial_extension_lower (n w f : ℕ) (hfw : f ≤ w) (hwn : w ≤ n) :
    ((n : ℝ) - w) ^ (w - f) ≤ ((n - f).descFactorial (w - f) : ℝ) := by
  have hb : (n - w) ^ (w - f) ≤ (n - f).descFactorial (w - f) := by
    calc
      _ ≤ (n - f + 1 - (w - f)) ^ (w - f) :=
        Nat.pow_le_pow_left (by omega) _
      _ ≤ _ := Nat.pow_sub_le_descFactorial _ _
  rw [← Nat.cast_sub hwn, ← Nat.cast_pow]
  exact_mod_cast hb

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V] {F : Finset W}

theorem card_embeddingExtension_upper (φ : F ↪ V) :
    Fintype.card (EmbeddingExtension φ) ≤
      Fintype.card V ^ (Fintype.card W - F.card) := by
  rw [card_embeddingExtension φ]
  exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/-- A uniform lower bound for every fixed injective root map. -/
theorem card_embeddingExtension_three_quarters (φ : F ↪ V)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) :
    (3 / 4 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤
      (Fintype.card (EmbeddingExtension φ) : ℝ) := by
  have hfw : F.card ≤ Fintype.card W := Finset.card_le_univ F
  have hwn : Fintype.card W ≤ Fintype.card V := by
    by_cases hw : Fintype.card W = 0
    · omega
    · have hw1 : 1 ≤ Fintype.card W := Nat.one_le_iff_ne_zero.mpr hw
      nlinarith
  have hsize : 4 * (Fintype.card W - F.card) * Fintype.card W ≤ Fintype.card V := by
    have hm := Nat.mul_le_mul_right (Fintype.card W) (Nat.sub_le (Fintype.card W) F.card)
    nlinarith
  rw [card_embeddingExtension φ]
  exact (pow_sub_three_quarters (Nat.cast_nonneg _) (by exact_mod_cast hwn)
    (Fintype.card W - F.card) (by exact_mod_cast hsize)).trans
    (descFactorial_extension_lower _ _ _ hfw hwn)

end Arxiv2411_18291
