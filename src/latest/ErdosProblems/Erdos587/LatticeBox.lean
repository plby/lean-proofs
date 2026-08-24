import ErdosProblems.Erdos587.LatticeCenter

/-! Positive integral half-widths and central-quarter containment of a lattice box. -/

namespace Erdos587

noncomputable def latticeHalfWidth (s : ℝ) : ℕ := ⌊1 / (64 * s)⌋₊

theorem latticeHalfWidth_bounds {s : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 128) :
    0 < latticeHalfWidth s ∧ (1 / 128 : ℝ) ≤ (latticeHalfWidth s : ℝ) * s ∧
      (latticeHalfWidth s : ℝ) * s ≤ 1 / 64 := by
  have hden : 0 < 64 * s := by positivity
  have hx : (2 : ℝ) ≤ 1 / (64 * s) := (le_div_iff₀ hden).mpr (by nlinarith)
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / (64 * s))
  have hfloor' := Nat.lt_floor_add_one (1 / (64 * s))
  have hcancel : (1 / (64 * s)) * s = (1 / 64 : ℝ) := by field_simp
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_⟩
  · have hhalf : (1 / (64 * s)) / 2 ≤ (latticeHalfWidth s : ℝ) := by
      dsimp only [latticeHalfWidth]
      linarith
    have hh := mul_le_mul_of_nonneg_right hhalf hs.le
    have heq : ((1 / (64 * s)) / 2) * s = (1 / 128 : ℝ) := by
      field_simp
      norm_num
    rwa [heq] at hh
  · have hh := mul_le_mul_of_nonneg_right hfloor hs.le
    rwa [hcancel] at hh

lemma central_quarter_of_three_errors {W c a b : ℝ} (_hW : 0 < W)
    (hc : |c - W / 2| ≤ W / 8) (ha : |a| ≤ W / 16) (hb : |b| ≤ W / 16) :
    c + a + b ∈ Set.Icc (W / 4) (3 * W / 4) := by
  have hc' := abs_le.mp hc
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  constructor <;> linarith [hc'.1, hc'.2, ha'.1, ha'.2, hb'.1, hb'.2]

lemma scaled_coordinate_shift_bound {W s x m : ℝ} (hW : 0 < W)
    (hx : |x| ≤ W * s) (hm : |m| * s ≤ 1 / 64) : |m * x| ≤ W / 16 := by
  rw [abs_mul]
  calc
    |m| * |x| ≤ |m| * (W * s) := mul_le_mul_of_nonneg_left hx (abs_nonneg m)
    _ = W * (|m| * s) := by ring
    _ ≤ W * (1 / 64 : ℝ) := mul_le_mul_of_nonneg_left hm hW.le
    _ ≤ W / 16 := by linarith

theorem lattice_box_mem_central_quarter {H J : ℝ} {p q z : ℤ × ℤ} {m n : ℤ}
    (hH : 0 < H) (hJ : 0 < J)
    (hcenterX : |(z.1 : ℝ) - H / 2| ≤
      H * (latticeScaledNorm H J p + latticeScaledNorm H J q) / 2)
    (hcenterY : |(z.2 : ℝ) - J / 2| ≤
      J * (latticeScaledNorm H J p + latticeScaledNorm H J q) / 2)
    (hsmall : latticeScaledNorm H J p + latticeScaledNorm H J q ≤ 1 / 4)
    (hm : |(m : ℝ)| * latticeScaledNorm H J p ≤ 1 / 64)
    (hn : |(n : ℝ)| * latticeScaledNorm H J q ≤ 1 / 64) :
    (((z + latticeCombination m n p q).1 : ℝ) ∈ Set.Icc (H / 4) (3 * H / 4)) ∧
      (((z + latticeCombination m n p q).2 : ℝ) ∈ Set.Icc (J / 4) (3 * J / 4)) := by
  have hcx : |(z.1 : ℝ) - H / 2| ≤ H / 8 := by nlinarith
  have hcy : |(z.2 : ℝ) - J / 2| ≤ J / 8 := by nlinarith
  have hpX := scaled_coordinate_shift_bound hH (abs_first_coordinate_le_scaledNorm hH p) hm
  have hqX := scaled_coordinate_shift_bound hH (abs_first_coordinate_le_scaledNorm hH q) hn
  have hpY := scaled_coordinate_shift_bound hJ (abs_second_coordinate_le_scaledNorm hJ p) hm
  have hqY := scaled_coordinate_shift_bound hJ (abs_second_coordinate_le_scaledNorm hJ q) hn
  constructor
  · have hh := central_quarter_of_three_errors hH hcx hpX hqX
    simpa only [latticeCombination, Prod.fst_add, Int.cast_add, Int.cast_mul, add_assoc] using hh
  · have hh := central_quarter_of_three_errors hJ hcy hpY hqY
    simpa only [latticeCombination, Prod.snd_add, Int.cast_add, Int.cast_mul, add_assoc] using hh

theorem latticeHalfWidth_box_mem_central_quarter {H J : ℝ} {p q z : ℤ × ℤ} {m n : ℤ}
    (hH : 0 < H) (hJ : 0 < J) (hp : p ≠ 0) (hq : q ≠ 0)
    (hcenterX : |(z.1 : ℝ) - H / 2| ≤
      H * (latticeScaledNorm H J p + latticeScaledNorm H J q) / 2)
    (hcenterY : |(z.2 : ℝ) - J / 2| ≤
      J * (latticeScaledNorm H J p + latticeScaledNorm H J q) / 2)
    (hpSmall : latticeScaledNorm H J p ≤ 1 / 128)
    (hqSmall : latticeScaledNorm H J q ≤ 1 / 128)
    (hm : |m| ≤ latticeHalfWidth (latticeScaledNorm H J p))
    (hn : |n| ≤ latticeHalfWidth (latticeScaledNorm H J q)) :
    (((z + latticeCombination m n p q).1 : ℝ) ∈ Set.Icc (H / 4) (3 * H / 4)) ∧
      (((z + latticeCombination m n p q).2 : ℝ) ∈ Set.Icc (J / 4) (3 * J / 4)) := by
  have hpPos := latticeScaledNorm_pos hH.ne' hJ.ne' hp
  have hqPos := latticeScaledNorm_pos hH.ne' hJ.ne' hq
  apply lattice_box_mem_central_quarter hH hJ hcenterX hcenterY (by linarith)
  · have hmR : |(m : ℝ)| ≤ (latticeHalfWidth (latticeScaledNorm H J p) : ℝ) := by exact_mod_cast hm
    exact (mul_le_mul_of_nonneg_right hmR hpPos.le).trans (latticeHalfWidth_bounds hpPos hpSmall).2.2
  · have hnR : |(n : ℝ)| ≤ (latticeHalfWidth (latticeScaledNorm H J q) : ℝ) := by exact_mod_cast hn
    exact (mul_le_mul_of_nonneg_right hnR hqPos.le).trans (latticeHalfWidth_bounds hqPos hqSmall).2.2

end Erdos587
