import Arxiv.Arxiv2411_18291.AbsorberCoefficientBounds

/-! # Explicit constants for a multiplicity-reduction round -/

namespace Arxiv2411_18291

/-- The second parameter is the face rank, so the edge size is `r+1`. -/
def flatteningRoundConstant (q r : ℕ) : ℕ :=
  (7 + 4 * (q - r) + 24 * (r + 1).factorial * absorberExchangeEdges q (r + 1)) *
    (3 + 8 * (r + 1).factorial * absorberExchangeEdges q (r + 1))

theorem flatteningRoundConstant_pos (q r : ℕ) : 0 < flatteningRoundConstant q r := by
  unfold flatteningRoundConstant
  positivity

theorem flattening_round_scale_constant {q r m : ℕ} (hqr : r + 1 < q)
    (hm : m ≤ (4 * q) ^ (2 * q)) :
    3 * (3 + 8 * (r + 1).factorial * m) ≤ (4 * q) ^ (24 * q) := by
  have hq : 2 ≤ q := by omega
  have hf : (r + 1).factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have hfm : (r + 1).factorial * m ≤ (4 * q) ^ (3 * q) := by
    calc
      _ ≤ (4 * q) ^ q * (4 * q) ^ (2 * q) := Nat.mul_le_mul hf hm
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hp : 1 ≤ (4 * q) ^ (3 * q) := one_le_pow₀ (by omega)
  have hc : 33 ≤ (4 * q) ^ 2 := by nlinarith only [hq]
  calc
    _ ≤ 33 * (4 * q) ^ (3 * q) := by nlinarith only [hfm, hp]
    _ ≤ (4 * q) ^ 2 * (4 * q) ^ (3 * q) := Nat.mul_le_mul_right _ hc
    _ = (4 * q) ^ (2 + 3 * q) := by rw [pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

end Arxiv2411_18291
