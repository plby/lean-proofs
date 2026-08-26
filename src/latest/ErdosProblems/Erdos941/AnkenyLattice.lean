import ErdosProblems.Erdos941.AnkenyAlgebra
import ErdosProblems.Erdos941.LatticePoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The explicit lattice for the three-square construction
-/

namespace Erdos941

open Module MeasureTheory

noncomputable section

def ankenyMatrix (a b t m : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t * a, t * b, m; Real.sqrt a, b / Real.sqrt a, 0; 0, Real.sqrt (m / a), 0]

theorem ankenyMatrix_det {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (b t : ℝ) :
    (ankenyMatrix a b t m).det = m * Real.sqrt m := by
  rw [Matrix.det_fin_three]
  simp only [ankenyMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, mul_zero, sub_zero]
  rw [Real.sqrt_div hm.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne']
  ring

def ankenyPiBasis {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (b t : ℝ) :
    Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map ((ankenyMatrix a b t m).toLinearEquiv'
    ((ankenyMatrix a b t m).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr
      (by rw [ankenyMatrix_det ha hm]; positivity))))

def ankenyBasis {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (b t : ℝ) :
    Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (ankenyPiBasis ha hm b t).map (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv

theorem ankenyPiBasis_apply {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (b t : ℝ) (i j : Fin 3) :
    ankenyPiBasis ha hm b t i j = ankenyMatrix a b t m j i := by
  change ((ankenyMatrix a b t m).mulVec ((Pi.basisFun ℝ (Fin 3)) i)) j = _
  simp [Pi.basisFun_apply, Matrix.mulVec_single]

theorem ankenyPiBasis_volume {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (b t : ℝ) :
    volume (ZSpan.fundamentalDomain (ankenyPiBasis ha hm b t)) =
      ENNReal.ofReal (m * Real.sqrt m) := by
  rw [ZSpan.volume_fundamentalDomain]
  have hmat : Matrix.of (ankenyPiBasis ha hm b t) = (ankenyMatrix a b t m).transpose := by
    ext i j
    exact ankenyPiBasis_apply ha hm b t i j
  rw [hmat, Matrix.det_transpose, ankenyMatrix_det ha hm, abs_of_pos (by positivity)]

theorem ankenyBasis_volume {a m : ℝ} (ha : 0 < a) (hm : 0 < m) (b t : ℝ) :
    volume (ZSpan.fundamentalDomain (ankenyBasis ha hm b t)) =
      ENNReal.ofReal (m * Real.sqrt m) := by
  let e := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv
  have he : MeasurePreserving e := PiLp.volume_preserving_toLp (Fin 3)
  have hpre : e ⁻¹' ZSpan.fundamentalDomain (ankenyBasis ha hm b t) =
      ZSpan.fundamentalDomain (ankenyPiBasis ha hm b t) := by
    rw [ankenyBasis, ← ZSpan.map_fundamentalDomain]
    exact Set.preimage_image_eq _ e.injective
  rw [← he.measure_preimage (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet,
    hpre, ankenyPiBasis_volume ha hm]

theorem ankenyBasis_sum_apply {a m : ℝ} (ha : 0 < a) (hm : 0 < m)
    (b t : ℝ) (c : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i, c i • ankenyBasis ha hm b t i) j =
      ∑ i, ankenyMatrix a b t m j i * c i := by
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  congr 1
  change ankenyPiBasis ha hm b t i j = _
  exact ankenyPiBasis_apply ha hm b t i j

private theorem ankeny_real_binary_identity {a b c m : ℝ} (ha : 0 < a)
    (hm : 0 < m) (hc : a * c = b ^ 2 + m) (x y : ℝ) :
    (Real.sqrt a * x + b / Real.sqrt a * y) ^ 2 + (Real.sqrt (m / a) * y) ^ 2 =
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rw [Real.sqrt_div hm.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne']
  ring_nf
  rw [Real.sq_sqrt ha.le, Real.sq_sqrt hm.le]
  have hfour : Real.sqrt a ^ 4 = a ^ 2 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, Real.sq_sqrt ha.le]
  rw [hfour]
  linear_combination -y ^ 2 * hc

theorem ankenyBasis_norm_sq {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    {b c t : ℤ} (hc : (a : ℤ) * c = b ^ 2 + m) (v : Fin 3 → ℤ) :
    ‖∑ i, (v i : ℝ) • ankenyBasis (a := (a : ℝ)) (m := (m : ℝ))
        (by exact_mod_cast ha) (by exact_mod_cast hm)
        (b : ℝ) (t : ℝ) i‖ ^ 2 =
      (ankenyQ a b c t m (v 0) (v 1) (v 2) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [ankenyBasis_sum_apply]
  simp only [Fin.sum_univ_three, ankenyMatrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zero_mul, add_zero, zero_add]
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hc' : (a : ℝ) * (c : ℝ) = (b : ℝ) ^ 2 + (m : ℝ) := by exact_mod_cast hc
  have hbin := ankeny_real_binary_identity ha' hm' hc' (v 0 : ℝ) (v 1 : ℝ)
  unfold ankenyQ ankenyR ankenyU
  push_cast
  linear_combination hbin

theorem exists_ankeny_short {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    {b c t : ℤ} (hc : (a : ℤ) * c = b ^ 2 + m) :
    ∃ x y z : ℤ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      ankenyQ a b c t m x y z < 2 * m := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨v, hv, hshort⟩ := exists_short_lattice_vector
    (ankenyBasis ha' hm' b t) hm' (ankenyBasis_volume ha' hm' b t)
  refine ⟨v 0, v 1, v 2, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hv
    fin_cases i <;> aesop
  · rw [ankenyBasis_norm_sq ha hm hc] at hshort
    exact_mod_cast hshort

/-- Given the auxiliary arithmetic parameters, the three-square construction
is unconditional: Minkowski supplies the short vector used here. -/
theorem three_squares_of_ankeny_parameters {a m : ℕ} (ha : 0 < a) (hm : 0 < m)
    (hsq : Squarefree m) {b c t : ℤ} (hc : (a : ℤ) * c = b ^ 2 + m)
    (ht : (m : ℤ) ∣ (a : ℤ) * t ^ 2 + 1) (ham : IsCoprime (m : ℤ) (a : ℤ))
    (hprime : ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ¬ p ∣ a ∧ (p ∣ m → IsSquare (-(a : ZMod p)))) :
    ∃ X Y Z : ℤ, norm3 X Y Z = m := by
  obtain ⟨x, y, z, hne, hshort⟩ := exists_ankeny_short ha hm hc (t := t)
  have hQ := ankenyQ_eq_of_short (by exact_mod_cast ha) (by exact_mod_cast hm)
    hc ht ham hne hshort
  exact ankeny_three_squares_of_Q ha hm hsq hc hprime hQ

end

end Erdos941
