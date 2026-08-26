import ErdosProblems.Erdos633b.QuarterThirdSmallOrders
import ErdosProblems.Erdos633b.CoprimeResidueLift

/-! A quarter-to-third residue gives a cosine strictly between -1/2
and zero, and this value lifts through any common angle denominator. -/

namespace Erdos633b

theorem cosine_quarter_third_bounds (D r : ℕ) (hD : 0 < D) (hr : QuarterThirdResidue D r) :
    -(1 / 2 : ℝ) < Real.cos (2 * Real.pi * r / D) ∧
      Real.cos (2 * Real.pi * r / D) < 0 := by
  obtain ⟨_, hl, hu⟩ := hr
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hu' : (3 : ℝ) * r < D := by exact_mod_cast hu
  have hθpos : 0 ≤ 2 * Real.pi * r / D := by positivity
  have hθlt : 2 * Real.pi * r / D < 2 * Real.pi / 3 := by
    rw [div_lt_iff₀ hD']
    nlinarith [Real.pi_pos]
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθpos
    (show 2 * Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hθlt
  have hval : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring,
      Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  rw [hval] at hc
  exact ⟨hc, cosine_middle_residue_neg D r hD hl (by omega)⟩

theorem cosine_eq_of_scaled_residue (N m g j D k r : ℕ)
    (hN : 0 < N) (hD : 0 < D) (hmj : m = j * g) (hND : 2 * N = D * g)
    (hrD : r < D) (he : Nat.ModEq D (k * j) r) :
    Real.cos (k * (m * (Real.pi / N))) = Real.cos (2 * Real.pi * r / D) := by
  have hrem : (k * j) % D = r := by
    change (k * j) % D = r % D at he
    rwa [Nat.mod_eq_of_lt hrD] at he
  have hkj : k * j = r + D * (k * j / D) := by
    have hh := Nat.mod_add_div (k * j) D
    rw [hrem] at hh
    exact hh.symm
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hmj' : (m : ℝ) = (j : ℝ) * g := by exact_mod_cast hmj
  have hND' : (2 : ℝ) * N = (D : ℝ) * g := by exact_mod_cast hND
  have hkj' : (k : ℝ) * j = (r : ℝ) + D * ((k * j / D : ℕ) : ℝ) := by exact_mod_cast hkj
  have hangle : (k : ℝ) * (m * (Real.pi / N)) =
      2 * Real.pi * r / D + ((k * j / D : ℕ) : ℝ) * (2 * Real.pi) := by
    apply (mul_right_cancel₀ hN')
    field_simp [hN', hD']
    linear_combination (k : ℝ) * (D : ℝ) * hmj' -
      (k : ℝ) * (j : ℝ) * hND' + 2 * (N : ℝ) * hkj'
  rw [hangle, Real.cos_add_nat_mul_two_pi]

theorem quarter_third_cosine_conjugate (N m g j D : ℕ)
    (hN : 0 < N) (hD : 6 < D) (hmj : m = j * g) (hND : 2 * N = D * g)
    (hjD : j.Coprime D) (hne : D ∉ quarterThirdExceptions) :
    ∃ k : ℕ, k.Coprime (2 * N) ∧
      -(1 / 2 : ℝ) < Real.cos (k * (m * (Real.pi / N))) ∧
      Real.cos (k * (m * (Real.pi / N))) < 0 := by
  obtain ⟨r, hr⟩ := exists_quarter_third_residue D hD hne
  have hDM : D ∣ 2 * N := ⟨g, hND⟩
  obtain ⟨k, hk, he⟩ := coprime_multiplier_residue (2 * N) D j r (by omega) hDM hjD hr.1
  refine ⟨k, hk, ?_⟩
  rw [cosine_eq_of_scaled_residue N m g j D k r hN (by omega) hmj hND
    (by have := hr.2.2; omega) he]
  exact cosine_quarter_third_bounds D r (by omega) hr

end Erdos633b
