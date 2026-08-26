import ErdosProblems.Erdos633b.BoundedCounterexampleCorners

/-! Exact rational data used for the finite corner/local intersection table. -/

namespace Erdos633b

def cornerAnglePair (P Q R : ℕ) (t : ℤ × ℤ × ℤ) : ℚ × ℚ :=
  ((cornerLocalAlphaNumerator P Q R t : ℚ) / cornerLocalDeterminant P Q R t,
   (cornerLocalBetaNumerator P Q R t : ℚ) / cornerLocalDeterminant P Q R t)

def angleTablePair (v : ℕ × ℕ × ℕ) : ℚ × ℚ :=
  ((v.2.1 : ℚ) / v.1, (v.2.2 : ℚ) / v.1)

def AdmissibleCornerData (P Q R : ℕ) (t : ℤ × ℤ × ℤ) : Prop :=
  1 ≤ P ∧ 5 ≤ P + Q + R ∧ (R = 1 → Q = 0 ∧ 4 ≤ P) ∧
    cornerLocalDeterminant P Q R t ≠ 0 ∧
    (1 : ℚ) / 21 ≤ (cornerAnglePair P Q R t).1 ∧
    (cornerAnglePair P Q R t).1 < (cornerAnglePair P Q R t).2 ∧
    (cornerAnglePair P Q R t).2 <
      1 - (cornerAnglePair P Q R t).1 - (cornerAnglePair P Q R t).2 ∧
    (cornerAnglePair P Q R t).2 ≤ (2 : ℚ) / 5 ∧
    1 - (cornerAnglePair P Q R t).1 - (cornerAnglePair P Q R t).2 ≤ (2 : ℚ) / 3 ∧
    1 - (cornerAnglePair P Q R t).1 - (cornerAnglePair P Q R t).2 ≠ (1 : ℚ) / 2

instance (P Q R : ℕ) (t : ℤ × ℤ × ℤ) : Decidable (AdmissibleCornerData P Q R t) := by
  unfold AdmissibleCornerData
  infer_instance

theorem corner_pair_realizes (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (P Q R : ℕ) (hc : (P : ℝ) * α + Q * β + R * γ = Real.pi)
    (t : ℤ × ℤ × ℤ)
    (he : (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi)
    (hd : cornerLocalDeterminant P Q R t ≠ 0) :
    α = ((cornerAnglePair P Q R t).1 : ℝ) * Real.pi ∧
      β = ((cornerAnglePair P Q R t).2 : ℝ) * Real.pi := by
  have hd' : (cornerLocalDeterminant P Q R t : ℝ) ≠ 0 := by exact_mod_cast hd
  obtain ⟨ha, hb⟩ := corner_local_elimination α β γ hs P Q R hc t he
  dsimp only [cornerAnglePair]
  push_cast
  constructor
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hd').mpr
    simpa only [mul_comm] using ha
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hd').mpr
    simpa only [mul_comm] using hb

namespace Tiling

theorem admissible_corner_data_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2)
    (t : ℤ × ℤ × ℤ) (ht : t ∈ orderedNonrightRelationTriples)
    (he : (t.1 : ℝ) * d.tile.angle 0 + (t.2.1 : ℝ) * d.tile.angle 1 =
      (t.2.2 : ℝ) * Real.pi) :
    AdmissibleCornerData (d.cornerColumnCount 0) (d.cornerColumnCount 1)
      (d.cornerColumnCount 2) t := by
  obtain ⟨hα, hP, _, _, _, htotal, hR1, _⟩ :=
    d.counterexample_ordered_corner_data hn hnot h01 h12
  have hd := d.corner_local_determinant_ne_zero_unconditional hn hnot h01 h12 t ht he
  have hc := d.corner_column_angle_sum
  rw [Fin.sum_univ_three] at hc
  obtain ⟨ha, hb⟩ := corner_pair_realizes _ _ _ d.tile.angle_sum _ _ _ hc t he hd
  let x : ℚ := (cornerAnglePair (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t).1
  let y : ℚ := (cornerAnglePair (d.cornerColumnCount 0) (d.cornerColumnCount 1)
    (d.cornerColumnCount 2) t).2
  change d.tile.angle 0 = (x : ℝ) * Real.pi at ha
  change d.tile.angle 1 = (y : ℝ) * Real.pi at hb
  have hg : d.tile.angle 2 = ((1 - x - y : ℚ) : ℝ) * Real.pi := by
    push_cast
    linarith [d.tile.angle_sum]
  refine ⟨hP, htotal, hR1, hd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (1 : ℚ) / 21 ≤ x
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    nlinarith [Real.pi_pos]
  · have hr : (x : ℝ) < y := by nlinarith [Real.pi_pos]
    exact_mod_cast hr
  · have hr : (y : ℝ) < ((1 - x - y : ℚ) : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast hr
  · change y ≤ (2 : ℚ) / 5
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hh := d.middle_angle_le_two_pi_fifths_of_counterexample hn hnot h01 h12
    nlinarith [Real.pi_pos]
  · change 1 - x - y ≤ (2 : ℚ) / 3
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hh := d.tile_angle_le_two_pi_thirds_of_counterexample hn hnot 2
    nlinarith [Real.pi_pos]
  · intro hz
    have hh := d.tile_angle_ne_pi_half_of_counterexample hn hnot 2
    apply hh
    change 1 - x - y = 1 / 2 at hz
    rw [hz] at hg
    norm_num at hg
    linarith

end Tiling
end Erdos633b
