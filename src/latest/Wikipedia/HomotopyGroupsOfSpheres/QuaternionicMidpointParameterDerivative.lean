import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCurveCalculus
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointTarget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Actual Bott-parameter derivatives at the midpoint -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

def angularVelocity (a b : ℝ) : ℂ := ⟨-a, -b⟩

def midpointRotationVariation (w : ℂ) (D : Matrix (Fin 3) (Fin 3) ℂ)
    (r q : Fin 3) : ℍ := (if r = q then (w : ℍ) else 0) + embed (D r q)

theorem rotation_midpoint_entry (B : Space (Fin 3)) (r q : Fin 3) :
    (rotation (Real.pi / 2) (Real.pi / 2) B).val r q = embed (B.val.val r q) := by
  rw [rotation_val, midpoint_matrix]
  rfl

theorem hasDerivAt_midpoint_coefficients (s t : ℝ → ℝ) (a b x : ℝ)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2) :
    HasDerivAt (fun y ↦ Real.cos (s y)) (-a) x ∧
      HasDerivAt (fun y ↦ Real.sin (s y) * Real.cos (t y)) (-b) x ∧
      HasDerivAt (fun y ↦ Real.sin (s y) * Real.sin (t y)) 0 x := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [hsx] using hs.cos
  · convert hs.sin.mul ht.cos using 1 <;> try rfl
    simp [hsx, htx]
  · convert hs.sin.mul ht.sin using 1 <;> try rfl
    simp [hsx, htx]

theorem hasDerivAt_rotation_entry_midpoint (s t : ℝ → ℝ) (B : ℝ → Space (Fin 3))
    (a b x : ℝ) (D : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hB : ∀ r q, HasDerivAt (fun y ↦ (B y).val.val r q) (D r q) x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2) (r q : Fin 3) :
    HasDerivAt (fun y ↦ (rotation (s y) (t y) (B y)).val r q)
      (midpointRotationVariation (angularVelocity a b) D r q) x := by
  obtain ⟨ha, hb, hc⟩ := hasDerivAt_midpoint_coefficients s t a b x hs ht hsx htx
  have hemb := hasDerivAt_embed (fun y ↦ (B y).val.val r q) (D r q) x (hB r q)
  have he := ((ha.smul_const (if r = q then (1 : ℍ) else 0)).add
    (hb.smul_const (if r = q then i else 0))).add (hc.smul hemb)
  have hf : (fun y ↦ (rotation (s y) (t y) (B y)).val r q) = fun y ↦
      Real.cos (s y) • (if r = q then (1 : ℍ) else 0) +
        (Real.sin (s y) * Real.cos (t y)) • (if r = q then i else 0) +
        (Real.sin (s y) * Real.sin (t y)) • embed ((B y).val.val r q) := by
    funext y
    rw [rotation_val, matrix_apply]
  rw [hf]
  convert he using 1 <;> try rfl
  simp only [hsx, htx, Real.sin_pi_div_two, mul_one, one_smul, zero_smul, add_zero,
    midpointRotationVariation, angularVelocity, coeComplex_mk]
  by_cases h : r = q <;> simp [h]

theorem hasDerivAt_scalarRotation_midpoint (s t : ℝ → ℝ) (a b x : ℝ)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2) :
    HasDerivAt (fun y ↦ scalarRotation (s y) (t y)) (angularVelocity a b : ℍ) x := by
  obtain ⟨ha, hb, hc⟩ := hasDerivAt_midpoint_coefficients s t a b x hs ht hsx htx
  have he := ((ha.smul_const (1 : ℍ)).add (hb.smul_const i)).add (hc.smul_const j)
  convert he using 1 <;> try rfl
  simp only [angularVelocity, coeComplex_mk, zero_smul, add_zero]

theorem normalizationVariation_formula (w : ℂ) :
    star (-((w : ℍ) * j + j * (w : ℍ))) = embed (w + star w) := by
  have he : (w : ℍ) * j + j * (w : ℍ) = embed (w + star w) := by
    rw [j_mul_coeComplex]
    change Quaternion.ofComplex w * j + Quaternion.ofComplex (star w) * j =
      Quaternion.ofComplex (w + star w) * j
    rw [map_add, add_mul]
  rw [he, star_neg, embed_star, neg_neg]

theorem hasDerivAt_referenceNormalization_midpoint (s t : ℝ → ℝ) (a b x : ℝ)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2) :
    HasDerivAt (fun y ↦ star (-(scalarRotation (s y) (t y) * scalarRotation (s y) (t y))))
      (embed (angularVelocity a b + star (angularVelocity a b))) x := by
  have hq := hasDerivAt_scalarRotation_midpoint s t a b x hs ht hsx htx
  have he := (hq.mul hq).neg.star
  convert he using 1 <;> try rfl
  rw [hsx, htx, midpoint_reference]
  exact (normalizationVariation_formula _).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
