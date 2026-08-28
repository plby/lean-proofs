import Wikipedia.NoExoticSixSphere.RankSixLineSpinor
import Mathlib.Analysis.Complex.Circle

/-!
# Circle phases between unit representatives of a projected line

Two fixed unit vectors in the same rank-one range differ by a unique unit
complex scalar. The scalar used here is their actual Hermitian inner product.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

noncomputable def phaseSmul (z : Circle) (q : UnitSpinor) : UnitSpinor :=
  ⟨(z : ℂ) • (q : Spinor), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Circle.norm_coe,
      unitSpinor_norm, one_mul]⟩

theorem continuous_phaseSmul :
    Continuous (fun p : Circle × UnitSpinor ↦ phaseSmul p.1 p.2) :=
  (((show Continuous (fun z : Circle ↦ (z : ℂ)) from continuous_subtype_val).comp
    continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem phaseSmul_fixed (J : OrthogonalComplexStructures.Space 6)
    (q : UnitSpinor) (hq : projection J q = q) (z : Circle) :
    projection J (phaseSmul z q) = (phaseSmul z q : Spinor) := by
  change projection J ((z : ℂ) • (q : Spinor)) = (z : ℂ) • (q : Spinor)
  rw [map_smul, hq]

theorem inner_smul_unit_eq (J : OrthogonalComplexStructures.Space 6)
    (a b : UnitSpinor) (ha : projection J a = a) (hb : projection J b = b) :
    inner ℂ (b : Spinor) (a : Spinor) • (b : Spinor) = (a : Spinor) :=
  (projection_apply_eq_inner J b hb a).symm.trans ha

theorem norm_inner_unit_eq_one (J : OrthogonalComplexStructures.Space 6)
    (a b : UnitSpinor) (ha : projection J a = a) (hb : projection J b = b) :
    ‖inner ℂ (b : Spinor) (a : Spinor)‖ = 1 := by
  have h := congrArg norm (inner_smul_unit_eq J a b ha hb)
  simpa only [norm_smul, unitSpinor_norm, mul_one] using h

noncomputable def unitPhase (J : OrthogonalComplexStructures.Space 6)
    (a b : UnitSpinor) (ha : projection J a = a) (hb : projection J b = b) : Circle :=
  ⟨inner ℂ (b : Spinor) (a : Spinor), by
    change inner ℂ (b : Spinor) (a : Spinor) ∈ Metric.sphere (0 : ℂ) 1
    simpa only [Metric.mem_sphere, dist_zero_right] using
      norm_inner_unit_eq_one J a b ha hb⟩

theorem unitPhase_smul (J : OrthogonalComplexStructures.Space 6)
    (a b : UnitSpinor) (ha : projection J a = a) (hb : projection J b = b) :
    phaseSmul (unitPhase J a b ha hb) b = a :=
  Subtype.ext (inner_smul_unit_eq J a b ha hb)

variable {X : Type*} [TopologicalSpace X]

noncomputable def phaseMap (J : X → OrthogonalComplexStructures.Space 6)
    (a b : C(X, UnitSpinor)) (ha : ∀ x, projection (J x) (a x) = (a x : Spinor))
    (hb : ∀ x, projection (J x) (b x) = (b x : Spinor)) : C(X, Circle) where
  toFun x := unitPhase (J x) (a x) (b x) (ha x) (hb x)
  continuous_toFun := ((continuous_subtype_val.comp b.continuous).inner
    (continuous_subtype_val.comp a.continuous)).subtype_mk _

theorem phaseMap_smul (J : X → OrthogonalComplexStructures.Space 6)
    (a b : C(X, UnitSpinor)) (ha : ∀ x, projection (J x) (a x) = (a x : Spinor))
    (hb : ∀ x, projection (J x) (b x) = (b x : Spinor)) (x : X) :
    phaseSmul (phaseMap J a b ha hb x) (b x) = a x :=
  unitPhase_smul (J x) (a x) (b x) (ha x) (hb x)

end NoExoticSixSphere.RankSixComplexProjection
