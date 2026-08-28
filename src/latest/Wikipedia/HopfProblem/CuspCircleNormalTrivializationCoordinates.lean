import Wikipedia.HopfProblem.CuspCircleNormalTrivializationEquiv
import Wikipedia.HopfProblem.CuspCircleOrbitLocalCoordinates
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Real normal coordinates in the actual two toric charts

The explicit real fibre equivalences are assembled with the original
middle toric coordinate. They are genuine jointly real-analytic
diffeomorphisms of the full affine charts. Under the actual toric
coordinate change, the base coordinate inverts and the normal coordinate
is literally unchanged.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts ToricFan Triangle
open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

abbrev Fibre := ℂ × ℂ
abbrev Model := ℂ × Fibre

/-- The original two triangles meeting the fixed middle axis. -/
def chartTriangle : Bool → Triangle
  | false => ToricSpace.referenceTriangle
  | true => Triangle.upperNeighbour 1

/-- The exact base/normal coordinate order in the original affine three-space. -/
def coordinateSplit : CoordinateSpace 3 ≃L[ℂ] Model :=
  (show CoordinateSpace 3 ≃ₗ[ℂ] Model from
    { toFun := fun z => (z 1, (z 0, z 2))
      invFun := fun q => ![q.2.1, q.1, q.2.2]
      left_inv := by
        intro z
        ext j
        fin_cases j <;> rfl
      right_inv := by
        rintro ⟨a, z, w⟩
        rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearEquiv

@[simp] theorem coordinateSplit_apply (z : CoordinateSpace 3) :
    coordinateSplit z = (z 1, (z 0, z 2)) := rfl

@[simp] theorem coordinateSplit_symm_apply (q : Model) :
    coordinateSplit.symm q = ![q.2.1, q.1, q.2.2] := rfl

/-- The lower and upper real-linear normal coordinate changes. -/
def fibreEquiv : Bool → ℂ → Fibre ≃L[ℝ] Fibre
  | false, a => lowerEquiv a
  | true, a => upperEquiv a

theorem contDiff_fibreEquiv (b : Bool) {n : ℕ∞ω} :
    ContDiff ℝ n (fun q : Model => fibreEquiv b q.1 q.2) := by
  cases b
  · exact contDiff_lowerEquiv
  · exact contDiff_upperEquiv

theorem contDiff_fibreEquiv_symm (b : Bool) {n : ℕ∞ω} :
    ContDiff ℝ n (fun q : Model => (fibreEquiv b q.1).symm q.2) := by
  cases b
  · exact contDiff_lowerEquiv_symm
  · exact contDiff_upperEquiv_symm

/-- The joint base/fibre change is an actual global real-analytic diffeomorphism. -/
def fibreChange (b : Bool) : Diffeomorph 𝓘(ℝ, Model) 𝓘(ℝ, Model) Model Model ω where
  toFun q := (q.1, fibreEquiv b q.1 q.2)
  invFun q := (q.1, (fibreEquiv b q.1).symm q.2)
  left_inv q := Prod.ext rfl ((fibreEquiv b q.1).symm_apply_apply q.2)
  right_inv q := Prod.ext rfl ((fibreEquiv b q.1).apply_symm_apply q.2)
  contMDiff_toFun := (contDiff_fst.prodMk (contDiff_fibreEquiv b)).contMDiff
  contMDiff_invFun := (contDiff_fst.prodMk (contDiff_fibreEquiv_symm b)).contMDiff

/-- The original affine toric coordinates, in real-trivial normal form. -/
def chartCoordinates (b : Bool) :
    Diffeomorph 𝓘(ℝ, CoordinateSpace 3) 𝓘(ℝ, Model) (CoordinateSpace 3) Model ω :=
  (show Diffeomorph 𝓘(ℝ, CoordinateSpace 3) 𝓘(ℝ, Model) (CoordinateSpace 3) Model ω from
    { toEquiv := coordinateSplit.toLinearEquiv.toEquiv
      contMDiff_toFun := by
        have h : ContDiff ℝ ω (coordinateSplit : CoordinateSpace 3 → Model) :=
          (coordinateSplit.contDiff (n := ω)).restrict_scalars ℝ
        exact h.contMDiff
      contMDiff_invFun := by
        have h : ContDiff ℝ ω (coordinateSplit.symm : Model → CoordinateSpace 3) :=
          (coordinateSplit.symm.contDiff (n := ω)).restrict_scalars ℝ
        exact h.contMDiff }).trans
    (fibreChange b)

@[simp] theorem chartCoordinates_apply (b : Bool) (z : CoordinateSpace 3) :
    chartCoordinates b z = (z 1, fibreEquiv b (z 1) (z 0, z 2)) := rfl

@[simp] theorem chartCoordinates_symm_apply (b : Bool) (q : Model) :
    (chartCoordinates b).symm q =
      ![((fibreEquiv b q.1).symm q.2).1, q.1, ((fibreEquiv b q.1).symm q.2).2] := rfl

@[simp] theorem chartCoordinates_symm_middle (b : Bool) (q : Model) :
    (chartCoordinates b).symm q 1 = q.1 := rfl

/-- The zero section is literally the native middle axis, including both endpoints. -/
@[simp] theorem chartCoordinates_symm_zero (b : Bool) (a : ℂ) :
    (chartCoordinates b).symm (a, (0 : Fibre)) = ![0, a, 0] := by
  rw [chartCoordinates_symm_apply, map_zero]
  rfl

/-- Exact compatibility with the original non-linear toric chart change. -/
theorem chartCoordinates_transition (z : CoordinateSpace 3) (hz : z 1 ≠ 0) :
    chartCoordinates true
        (chartChange ToricSpace.referenceTriangle (Triangle.upperNeighbour 1) z) =
      ((z 1)⁻¹, (chartCoordinates false z).2) := by
  rw [normalTransition_apply]
  apply Prod.ext
  · rfl
  · change upperMap (z 1)⁻¹ (z 0 * z 1, z 1 * z 2) = lowerMap (z 1) (z 0, z 2)
    simpa only [mul_comm (z 0) (z 1)] using upper_lower_compatibility (z 1) hz (z 0, z 2)

/-- In the actual toric gluing, the two inverse coordinate maps agree exactly
after inverting the base and leaving the real normal vector unchanged. -/
theorem chartParameters_overlap (a : ℂ) (ha : a ≠ 0) (v : Fibre) :
    ToricSpace.inclusion (chartTriangle false) ((chartCoordinates false).symm (a, v)) =
      ToricSpace.inclusion (chartTriangle true) ((chartCoordinates true).symm (a⁻¹, v)) := by
  let z := (chartCoordinates false).symm (a, v)
  have hz : z 1 ≠ 0 := ha
  apply (ToricSpace.inclusion_eq_iff _ _ _ _).mpr
  have hs := normalTransition_source z
  refine ⟨hs.mpr hz, ?_⟩
  apply (chartCoordinates true).injective
  change chartCoordinates true
      (chartChange ToricSpace.referenceTriangle (Triangle.upperNeighbour 1) z) =
    chartCoordinates true ((chartCoordinates true).symm (a⁻¹, v))
  rw [(chartCoordinates true).apply_symm_apply, chartCoordinates_transition z hz]
  change (a⁻¹, (chartCoordinates false ((chartCoordinates false).symm (a, v))).2) = (a⁻¹, v)
  rw [(chartCoordinates false).apply_symm_apply]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
