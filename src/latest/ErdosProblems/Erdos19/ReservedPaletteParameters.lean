import ErdosProblems.Erdos19.CoverPaletteBudget

/-! # Exact sizes of the reserved medium palette -/

namespace Erdos19

theorem scaled_floor_le_div (n c d : ℕ) (hd : 0 < d) :
    c * (n / (c * d)) ≤ n / d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have h := Nat.mul_div_le n (c * d)
  nlinarith only [h]

theorem medium_reserved_palette_room (n s : ℕ) (hs : 0 < s) :
    2 * (n / (16 * s)) ≤ n / (4 * s) := by
  have h := scaled_floor_le_div n 4 (4 * s) (by omega)
  have heq : 4 * (4 * s) = 16 * s := by omega
  rw [heq] at h
  omega

theorem saving_reserved_palette_room (n s : ℕ) (hs : 0 < s) :
    n - n / (2 * s) + n / (4 * s) ≤ n - n / (4 * s) := by
  have h := half_saving_palette_budget n (2 * s) (by omega)
  have heq : 2 * (2 * s) = 4 * s := by omega
  simpa only [heq] using h

theorem projective_reserved_palette_room (n s h : ℕ) (hs : 0 < s)
    (hh : h ≤ n / (4 * s)) : n - n / s + h + n / (4 * s) ≤ n := by
  have hscale := scaled_floor_le_div n 4 s hs
  have hdiv := Nat.div_le_self n s
  omega

#print axioms medium_reserved_palette_room
#print axioms projective_reserved_palette_room

end Erdos19
