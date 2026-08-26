import ErdosProblems.Erdos19.DilutedLocalLemma

/-! # Integral parameter choices for the diluted coloring round -/

namespace Erdos19

theorem diluted_basic_parameters (D L : ℕ) (hL : 16 ≤ L) (hD : 2 * L ≤ D) :
    2 ≤ D / L ∧ 0 < D + 1 - D / L ∧ D + 1 - D / L ≤ D ∧
      D ≤ 2 * (D + 1 - D / L) ∧ 3 * (D / L + 1) ≤ D + 1 - D / L ∧
      D ≤ 2 * L * (D / L) := by
  have hLpos : 0 < L := by omega
  have ht : 2 ≤ D / L := (Nat.le_div_iff_mul_le hLpos).mpr hD
  have hmul : 16 * (D / L) ≤ D :=
    (Nat.mul_le_mul_right _ hL).trans (Nat.mul_div_le D L)
  have hfloor := Nat.lt_mul_div_succ D hLpos
  refine ⟨ht, by omega, by omega, by omega, by omega, ?_⟩
  nlinarith only [hfloor, Nat.mul_le_mul_left L (show D / L + 1 ≤ 2 * (D / L) by omega)]

theorem diluted_deletion_parameter_bound (h A D k t B : ℕ)
    (hA : 1024 * h ≤ A) (hB : B ≤ D ^ 2) (hk : D ≤ 2 * k)
    (hfloor : D ≤ (16 * h * A ^ 2) * (t + 1)) :
    8 * k * (2 * B * D) ≤ (t + 1) * (A * k) ^ 3 := by
  let L := 16 * h * A ^ 2
  have hA' : 64 * L ≤ A ^ 3 := by
    have hmul := Nat.mul_le_mul_right (A ^ 2) hA
    dsimp only [L]
    nlinarith only [hmul]
  have hk2 : D ^ 2 ≤ 4 * k ^ 2 := by nlinarith only [hk]
  have hstep : 16 * B * D ≤ A ^ 3 * (t + 1) * k ^ 2 := by
    calc
      16 * B * D ≤ 16 * D ^ 2 * D := by gcongr
      _ ≤ 16 * D ^ 2 * (L * (t + 1)) := Nat.mul_le_mul_left _ hfloor
      _ = (16 * L * (t + 1)) * D ^ 2 := by ring
      _ ≤ (16 * L * (t + 1)) * (4 * k ^ 2) := Nat.mul_le_mul_left _ hk2
      _ = (64 * L) * (t + 1) * k ^ 2 := by ring
      _ ≤ A ^ 3 * (t + 1) * k ^ 2 := by gcongr
  have hmul := Nat.mul_le_mul_left k hstep
  nlinarith only [hmul]

theorem diluted_mean_parameter_bound (h A D k t B : ℕ) (hh : 0 < h)
    (hk : k ≤ D) (ht : (16 * h * A ^ 2) * t ≤ D) (hB : D ^ 2 ≤ h * B) :
    6 * A ^ 2 * k * t ≤ B := by
  apply Nat.le_of_mul_le_mul_left (c := h) _ hh
  calc
    h * (6 * A ^ 2 * k * t) = (6 * h * A ^ 2 * t) * k := by ring
    _ ≤ (6 * h * A ^ 2 * t) * D := Nat.mul_le_mul_left _ hk
    _ ≤ ((16 * h * A ^ 2) * t) * D := by gcongr; norm_num
    _ ≤ D * D := Nat.mul_le_mul_right D ht
    _ ≤ h * B := by simpa only [pow_two] using hB

#print axioms diluted_basic_parameters
#print axioms diluted_deletion_parameter_bound
#print axioms diluted_mean_parameter_bound

end Erdos19
