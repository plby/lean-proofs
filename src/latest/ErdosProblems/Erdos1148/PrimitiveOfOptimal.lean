import ErdosProblems.Erdos1148.QuadraticOrderBasis

/-! # Optimality forces a binary quadratic form to be primitive -/

namespace Erdos1148.DukeArithmetic

lemma primitiveIntegralForm_of_common_divisors (t : ℤ × ℤ × ℤ)
    (h : ∀ g : ℤ, g ∣ t.1 → g ∣ t.2.1 → g ∣ t.2.2 → g ∣ 1) :
    PrimitiveIntegralForm t := by
  let e : ℤ := Int.gcd t.2.1 t.2.2
  let g : ℤ := Int.gcd t.1 e
  have hga : g ∣ t.1 := Int.gcd_dvd_left _ _
  have hge : g ∣ e := Int.gcd_dvd_right _ _
  obtain ⟨u, hu⟩ := h g hga (hge.trans (Int.gcd_dvd_left _ _))
    (hge.trans (Int.gcd_dvd_right _ _))
  have he : e = t.2.1 * Int.gcdA t.2.1 t.2.2 + t.2.2 * Int.gcdB t.2.1 t.2.2 :=
    Int.gcd_eq_gcd_ab _ _
  have hg : g = t.1 * Int.gcdA t.1 e + e * Int.gcdB t.1 e := Int.gcd_eq_gcd_ab _ _
  refine ⟨u * Int.gcdA t.1 e, u * Int.gcdB t.1 e * Int.gcdA t.2.1 t.2.2,
    u * Int.gcdB t.1 e * Int.gcdB t.2.1 t.2.2, ?_⟩
  linear_combination -hu - u * hg - u * Int.gcdB t.1 e * he

noncomputable def commonDivisorMultiplier {d : ℤ} (t : ℤ × ℤ × ℤ) (g : ℤ) :
    QuadraticDiscrAlgebra d := ⟨(t.2.1 : ℚ) / (2 * g), 1 / (2 * g)⟩

lemma commonDivisorMultiplier_image_integral {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) {g : ℤ} (hg : g ≠ 0)
    (hga : g ∣ t.1) (hgb : g ∣ t.2.1) (hgc : g ∣ t.2.2) :
    integralFormFieldEmbedding ht (commonDivisorMultiplier t g) ∈ integralRationalMatrices := by
  obtain ⟨A, hA⟩ := hga
  obtain ⟨B, hB⟩ := hgb
  obtain ⟨C, hC⟩ := hgc
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hAQ : (t.1 : ℚ) = (g : ℚ) * A := by exact_mod_cast hA
  have hBQ : (t.2.1 : ℚ) = (g : ℚ) * B := by exact_mod_cast hB
  have hCQ : (t.2.2 : ℚ) = (g : ℚ) * C := by exact_mod_cast hC
  rw [mem_integralRationalMatrices_iff]
  refine ⟨!![0, -C; A, B], ?_⟩
  rw [integralFormFieldEmbedding_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map, pellFormMatrix, mapCoeffs, commonDivisorMultiplier, hAQ, hBQ, hCQ] <;>
    field_simp <;> ring

lemma commonDivisorMultiplier_mem_order_dvd_one {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) {g : ℤ} (hg : g ≠ 0)
    (hw : commonDivisorMultiplier (d := d) t g ∈ quadraticOrder d) : g ∣ 1 := by
  obtain ⟨x, y, hxy⟩ := (mem_quadraticOrder_iff_coordinates
    ((discr_monicCompanionForm t).trans ht) (primitive_monicCompanionForm t) _).mp hw
  have him := congrArg (fun w : QuadraticDiscrAlgebra d => w.im) hxy
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hy : (g : ℚ)⁻¹ = (y : ℚ) := by
    simpa [commonDivisorMultiplier, quadraticOrderGenerator] using him
  have hyQ : (g : ℚ) * y = 1 := by rw [← hy, mul_inv_cancel₀ hgQ]
  have hyZ : g * y = 1 := by exact_mod_cast hyQ
  exact ⟨y, hyZ.symm⟩

theorem primitiveIntegralForm_of_optimal {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0)
    (hopt : integralRationalMatrices.comap (integralFormFieldEmbedding ht).toRingHom =
      quadraticOrder d) : PrimitiveIntegralForm t := by
  apply primitiveIntegralForm_of_common_divisors
  intro g hga hgb hgc
  have hg : g ≠ 0 := by
    intro hg
    subst g
    exact ha (zero_dvd_iff.mp hga)
  apply commonDivisorMultiplier_mem_order_dvd_one ht hg
  rw [← hopt]
  exact commonDivisorMultiplier_image_integral ht hg hga hgb hgc

end Erdos1148.DukeArithmetic
