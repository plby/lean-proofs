import Util.Bernays.CoprimeGeneratorAsymptotic

/-!
# The common area term in every coprime quadratic ideal class

The linear term is independent of the ideal class; the error is a constant
times `sqrt N + 1`. This is a count of ideals, not of distinct represented
integers.
-/

namespace Bernays

theorem area_coefficient_cancel (a m f v u n : ℝ) (hm : m ≠ 0) (hf : f ≠ 0)
    (hv : v ≠ 0) (hu : u ≠ 0) :
    a * (4 * Real.pi / ((f * m) * v)) * (m * n) =
      u * ((a * (4 * Real.pi) / (f * v * u)) * n) := by
  field_simp

theorem divide_area_error {a C K m u n : ℝ} (hu : 0 < u) (hm : 0 ≤ m)
    (hK : 0 ≤ K) (_hn : 0 ≤ n)
    (h : |u * a - u * (C * n)| ≤ K * (Real.sqrt (m * n) + 1)) :
    |a - C * n| ≤ (K * (Real.sqrt m + 1) / u) * (Real.sqrt n + 1) := by
  rw [← mul_sub, abs_mul, abs_of_pos hu] at h
  have hdiv : |a - C * n| ≤ (K * (Real.sqrt (m * n) + 1)) / u :=
    (le_div_iff₀ hu).mpr (by simpa only [mul_comm] using h)
  apply hdiv.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hu.le
  rw [mul_assoc K]
  apply mul_le_mul_of_nonneg_left _ hK
  rw [Real.sqrt_mul hm]
  nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg n]

noncomputable def idealClassAreaConstant (d b : ℤ) (F : Ideal (QuadraticAlgebra ℤ d b)) : ℝ :=
  (Nat.card (QuadraticAlgebra ℤ d b ⧸ F)ˣ : ℝ) * (4 * Real.pi) /
    ((F.cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤) *
      (Nat.card (QuadraticAlgebra ℤ d b)ˣ : ℝ))

theorem idealClassAreaConstant_pos {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF : F ≠ ⊥) :
    0 < idealClassAreaConstant d b F := by
  let := quadraticOrderIsDomain hD
  let : Finite (QuadraticAlgebra ℤ d b ⧸ F) := Ring.HasFiniteQuotients.finiteQuotient hF
  let := finite_quadraticOrder_units hD
  let := quadraticIdealLattice_discrete hD ⊤
  let := quadraticIdealLattice_full hD ⊤ top_ne_bot
  have hU : (0 : ℝ) < Nat.card (QuadraticAlgebra ℤ d b ⧸ F)ˣ := by exact_mod_cast Nat.card_pos
  have hu : (0 : ℝ) < Nat.card (QuadraticAlgebra ℤ d b)ˣ := by exact_mod_cast Nat.card_pos
  have hnorm : (0 : ℝ) < F.cardQuot := by
    exact_mod_cast (Nat.card_pos (α := QuadraticAlgebra ℤ d b ⧸ F))
  have hcov := ZLattice.covolume_pos (quadraticIdealLattice d b ⊤)
  exact div_pos (mul_pos hU (mul_pos (by norm_num) Real.pi_pos)) (mul_pos (mul_pos hnorm hcov) hu)

theorem idealClassArea_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (F : Ideal (QuadraticAlgebra ℤ d b)) (hF₀ : F ≠ ⊥) (hF₁ : F ≠ ⊤) :
    letI := quadraticOrderIsDomain hD
    ∀ C : ClassGroup (QuadraticAlgebra ℤ d b), ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      |(Nat.card (RestrictedIdealClassBall (QuadraticAlgebra ℤ d b) C N
        (fun J => IsCoprime (J : Ideal (QuadraticAlgebra ℤ d b)) F)) : ℝ) -
          idealClassAreaConstant d b F * N| ≤ K * (Real.sqrt (N : ℝ) + 1) := by
  let := quadraticOrderIsDomain hD
  intro C
  let O := QuadraticAlgebra ℤ d b
  let : Finite (O ⧸ F) := Ring.HasFiniteQuotients.finiteQuotient hF₀
  let := finite_quadraticOrder_units hD
  let := quadraticIdealLattice_discrete hD ⊤
  let := quadraticIdealLattice_full hD ⊤ top_ne_bot
  obtain ⟨I, hIC, hIF⟩ := InvertibleIdeal.exists_coprime_representative C⁻¹ F hF₀
  obtain ⟨K, hK, hbound⟩ := coprimeQuadraticBall_error hD (I : Ideal O) F I.ne_bot hF₀ hIF
  have hu : (0 : ℝ) < Nat.card Oˣ := by exact_mod_cast Nat.card_pos (α := Oˣ)
  have hnormI : (0 : ℝ) < (I : Ideal O).cardQuot := by exact_mod_cast I.cardQuot_pos
  have hnormF : (0 : ℝ) < F.cardQuot := by exact_mod_cast Nat.card_pos (α := O ⧸ F)
  have hcov := ZLattice.covolume_pos (quadraticIdealLattice d b ⊤)
  let m : ℝ := (I : Ideal O).cardQuot
  let u : ℝ := Nat.card Oˣ
  refine ⟨K * (Real.sqrt m + 1) / u, div_pos (mul_pos hK (by positivity)) hu, ?_⟩
  intro N
  have h := hbound ((I : Ideal O).cardQuot * N)
  rw [coprimeQuadraticBall_card hD I F hF₁ hIF, hIC, inv_inv, Nat.cast_mul,
    cardQuot_mul_invertible F (I : Ideal O) hF₀ I.2, Nat.cast_mul, Nat.cast_mul] at h
  have hmain :
      (Nat.card (O ⧸ F)ˣ : ℝ) *
        (4 * Real.pi / (((F.cardQuot : ℝ) * m) * ZLattice.covolume (quadraticIdealLattice d b ⊤))) *
        (m * N) = u * (idealClassAreaConstant d b F * N) := by
    exact area_coefficient_cancel _ _ _ _ _ _ hnormI.ne' hnormF.ne' hcov.ne' hu.ne'
  rw [hmain] at h
  exact divide_area_error hu hnormI.le hK.le (Nat.cast_nonneg N) h

end Bernays
