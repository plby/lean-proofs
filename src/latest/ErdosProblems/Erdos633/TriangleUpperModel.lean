import ErdosProblems.Erdos633.UpperTriangleSector

/-!
# An isometric upper-half-plane model for every triangle

The cosine rule supplies the third squared side length. The existing
three-side congruence construction then gives an ambient isometry matching
all three labelled vertices, without any orientation assumption.
-/

namespace Erdos633

noncomputable def Triangle.upperPoint (P : Triangle) : ℂ :=
  ⟨dist P.a P.c * Real.cos P.angleA, dist P.a P.c * Real.sin P.angleA⟩

theorem Triangle.upperPoint_im_pos (P : Triangle) : 0 < P.upperPoint.im :=
  mul_pos (dist_pos.mpr P.swapBC.a_ne_b) P.sin_angleA_pos

noncomputable def Triangle.upperModel (P : Triangle) : Triangle :=
  upperTriangle (dist P.a P.b) P.upperPoint (dist_pos.mpr P.a_ne_b) P.upperPoint_im_pos

theorem Triangle.upperPoint_normSq (P : Triangle) :
    Complex.normSq P.upperPoint = dist P.a P.c ^ 2 := by
  simp only [Complex.normSq_apply, Triangle.upperPoint]
  linear_combination (dist P.a P.c) ^ 2 * Real.cos_sq_add_sin_sq P.angleA

theorem Triangle.upperModel_side_ab (P : Triangle) :
    Complex.normSq (P.b - P.a) = Complex.normSq (P.upperModel.b - P.upperModel.a) := by
  change Complex.normSq (P.b - P.a) = Complex.normSq ((dist P.a P.b : ℂ) - 0)
  rw [sub_zero, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
    ← dist_eq_norm, dist_comm P.b P.a]
  ring

theorem Triangle.upperModel_side_ac (P : Triangle) :
    Complex.normSq (P.c - P.a) = Complex.normSq (P.upperModel.c - P.upperModel.a) := by
  change Complex.normSq (P.c - P.a) = Complex.normSq (P.upperPoint - 0)
  rw [sub_zero, P.upperPoint_normSq, Complex.normSq_eq_norm_sq,
    ← dist_eq_norm, dist_comm P.c P.a]

theorem Triangle.upperModel_side_bc (P : Triangle) :
    Complex.normSq (P.c - P.b) = Complex.normSq (P.upperModel.c - P.upperModel.b) := by
  have hcos : dist P.b P.c ^ 2 = dist P.a P.b ^ 2 + dist P.a P.c ^ 2 -
      2 * dist P.a P.b * dist P.a P.c * Real.cos P.angleA := by
    simpa only [Triangle.angleA, ← pow_two, dist_comm P.b P.a, dist_comm P.c P.a] using
      EuclideanGeometry.law_cos P.b P.a P.c
  have hnorm := P.upperPoint_normSq
  simp only [Complex.normSq_apply, Triangle.upperPoint] at hnorm
  rw [Complex.normSq_eq_norm_sq, ← dist_eq_norm, dist_comm P.c P.b]
  change dist P.b P.c ^ 2 = Complex.normSq (P.upperPoint - (dist P.a P.b : ℂ))
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Triangle.upperPoint, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  linear_combination hcos - hnorm

noncomputable def Triangle.upperIsometry (P : Triangle) : ℂ ≃ᵢ ℂ :=
  P.isometryOfNormSq P.upperModel P.upperModel_side_ab P.upperModel_side_ac P.upperModel_side_bc

theorem Triangle.upperIsometry_a (P : Triangle) : P.upperIsometry P.a = 0 := by
  rw [Triangle.upperIsometry, Triangle.isometryOfNormSq_apply, P.coordinateEquiv_symm_a,
    P.upperModel.coordinateEquiv_zero]
  rfl

theorem Triangle.map_upperIsometry (P : Triangle) :
    P.mapIsometry P.upperIsometry = P.upperModel := by
  apply Triangle.ext
  · exact P.upperIsometry_a
  · change P.upperIsometry P.b = P.upperModel.b
    rw [Triangle.upperIsometry, Triangle.isometryOfNormSq_apply,
      ← P.coordinateEquiv_one, P.coordinateEquiv.symm_apply_apply,
      P.upperModel.coordinateEquiv_one]
  · change P.upperIsometry P.c = P.upperModel.c
    rw [Triangle.upperIsometry, Triangle.isometryOfNormSq_apply,
      ← P.coordinateEquiv_I, P.coordinateEquiv.symm_apply_apply,
      P.upperModel.coordinateEquiv_I]

theorem Triangle.upperModel_angleA (P : Triangle) : P.upperModel.angleA = P.angleA := by
  have h := P.cornerAngle_mapIsometry P.upperIsometry 0
  change (P.mapIsometry P.upperIsometry).angleA = P.angleA at h
  rwa [P.map_upperIsometry] at h

end Erdos633
