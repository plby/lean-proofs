import ErdosProblems.Erdos633b.RightDeficitVertex
import ErdosProblems.Erdos633b.RightCornerEnumeration

/-! Every strictly ordered right tile in a non-reptiling of a scalene
triangle has smaller acute angle pi/5, pi/6, pi/8, or pi/10.
The remaining metric exclusions are separate theorems. -/

namespace Erdos633b

theorem right_angle_four_values (α β : ℝ) (P Q R p q r k : ℕ)
    (hP : 4 ≤ P) (hQR : Q + R ≤ 1) (htotal : 5 ≤ P + Q + R)
    (hkp : 1 ≤ k) (hkb : k ≤ 2) (hpq : p < q) (hqb : q ≤ 7) (hrb : r ≤ 3)
    (hsum : α + β = Real.pi / 2)
    (hcorner : (P : ℝ) * α + (Q : ℝ) * β + (R : ℝ) * (Real.pi / 2) = Real.pi)
    (hlocal : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (Real.pi / 2) = (k : ℝ) * Real.pi) :
    α = Real.pi / 5 ∨ α = Real.pi / 6 ∨ α = Real.pi / 8 ∨ α = Real.pi / 10 := by
  let D := P - Q
  let A := 2 - Q - R
  have hD : (D : ℝ) = (P : ℝ) - Q := by
    dsimp only [D]
    rw [Nat.cast_sub (show Q ≤ P by omega)]
  have hA : (A : ℝ) = 2 - (Q : ℝ) - R := by
    dsimp only [A]
    rw [Nat.cast_sub (show R ≤ 2 - Q by omega), Nat.cast_sub (show Q ≤ 2 by omega)]
    norm_num
  have hangle : 2 * (D : ℝ) * α = (A : ℝ) * Real.pi := by
    rw [hD, hA]
    linear_combination 2 * hcorner - 2 * (Q : ℝ) * hsum
  have heReal : (D : ℝ) * ((q : ℝ) + r) + (A : ℝ) * p =
      2 * (D : ℝ) * k + (A : ℝ) * q := by
    apply mul_right_cancel₀ Real.pi_ne_zero
    linear_combination 2 * (D : ℝ) * hlocal - 2 * (D : ℝ) * (q : ℝ) * hsum -
      ((p : ℝ) - q) * hangle
  have he : D * (q + r) + A * p = 2 * D * k + A * q := by exact_mod_cast heReal
  have hApos : 0 < A := by dsimp only [A]; omega
  have hA2 : A ≤ 2 := by dsimp only [A]; omega
  have hD14 := right_deficit_denominator_bound A D p q r k hApos hA2 hpq hqb he
  have hP15 : P ≤ 15 := by dsimp only [D] at hD14; omega
  have hc := right_corner_parameters_exhaustive P Q R p q r k
    hP hP15 hQR htotal hkp hkb hpq hqb hrb he
  rcases hc with ⟨rfl, rfl, hPc⟩ | ⟨rfl, rfl, hPc⟩ | ⟨rfl, rfl, hPc⟩
  · rcases hPc with rfl | rfl | rfl | rfl <;> norm_num [D, A] at hangle
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · rcases hPc with rfl | rfl | rfl <;> norm_num [D, A] at hangle
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · rcases hPc with rfl | rfl <;> norm_num [D, A] at hangle
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))

namespace Tiling

theorem right_angle_four_candidates {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hright : d.tile.angle 2 = Real.pi / 2) (hαβ : d.tile.angle 0 < d.tile.angle 1)
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    d.tile.angle 0 = Real.pi / 5 ∨ d.tile.angle 0 = Real.pi / 6 ∨
      d.tile.angle 0 = Real.pi / 8 ∨ d.tile.angle 0 = Real.pi / 10 := by
  obtain ⟨hP, hQR⟩ := d.right_corner_column_alternatives hright hαβ hscalene hrep
  obtain ⟨p, q, r, k, hpq, hqb, hrb, hkp, hkb, hlocal⟩ :=
    d.exists_right_beta_excess hright hαβ hscalene hrep
  have htotal := d.five_le_corner_total_of_not_reptiling hscalene hrep
  rw [Fin.sum_univ_three] at htotal
  have hcorner := d.corner_column_angle_sum
  rw [Fin.sum_univ_three, hright] at hcorner
  apply right_angle_four_values (d.tile.angle 0) (d.tile.angle 1)
    (d.cornerColumnCount 0) (d.cornerColumnCount 1) (d.cornerColumnCount 2) p q r k
    hP hQR htotal hkp hkb hpq hqb hrb _ hcorner hlocal
  linarith [d.tile.angle_sum]

end Tiling
end Erdos633b
