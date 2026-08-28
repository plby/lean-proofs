import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyMap
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# A genuine collapse homotopy for the integral cusp monodromy

The compensated compact-three-torus rotation descends jointly continuously
through the original free phase-plane quotient.  A full base turn gives
the unipotent source shear, and every intermediate map still takes values
in the actual central cusp fibre.  Consequently its actual integral
singular homology map kills the image of the shear minus the identity.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb
open SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

theorem centralRotation_sourceDeck (r : ℝ) (v : Fin 2 → ℤ) (p : PhasePlane) :
    centralProject C ε hε
        (rotatingCentralPoint (C 0) r (honeycombDeckMap (C 0) v p)) =
      centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  apply (centralProject_eq_iff C ε hε _ _).mpr
  exact ⟨v, (rotatingCentralPoint_deck C v r p).symm⟩

/-- The actual central collapse after an arbitrary compensated base rotation. -/
def sourceRotation (r : ℝ) : C(SourceModel (C 0), QuotientCentralFibre C ε) where
  toFun := Quotient.lift
    (fun p : PhasePlane => centralProject C ε hε (rotatingCentralPoint (C 0) r p)) (by
      rintro p q ⟨v, hv⟩
      rw [← hv]
      exact centralRotation_sourceDeck C ε hε r v q)
  continuous_toFun := ((centralProject_continuous C ε hε).comp
    ((rotatingCentralPoint_continuous (C 0)).comp
      (continuous_const.prodMk continuous_id))).quotient_lift _

@[simp] theorem sourceRotation_projection (r : ℝ) (p : PhasePlane) :
    sourceRotation C ε hε r (sourceProjection (C 0) p) =
      centralProject C ε hε (rotatingCentralPoint (C 0) r p) := rfl

/-- Joint continuity uses the quotient topology and local compactness of
the real rotation parameter, not a choice of representatives. -/
theorem sourceRotation_continuous :
    Continuous (fun p : ℝ × SourceModel (C 0) => sourceRotation C ε hε p.1 p.2) := by
  apply (sourceProjection_isQuotientMap (C 0)).continuous_lift_prod_right
  simpa only [Function.comp_def, sourceRotation_projection] using
    (centralProject_continuous C ε hε).comp (rotatingCentralPoint_continuous (C 0))

@[simp] theorem sourceRotation_zero : sourceRotation C ε hε 0 = sourceCollapse C ε hε := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, rotatingCentralPoint_zero]
  rfl

@[simp] theorem sourceRotation_one :
    sourceRotation C ε hε 1 = (sourceCollapse C ε hε).comp (sourceShear (C 0)) := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, rotatingCentralPoint_one]
  rfl

/-- Every compensated rotation is joined to the originally prescribed
collapse by an actual continuous homotopy in the literal central fibre. -/
def sourceRotationHomotopy (r : ℝ) :
    (sourceCollapse C ε hε).Homotopy (sourceRotation C ε hε r) where
  toFun p := sourceRotation C ε hε ((p.1 : ℝ) * r) p.2
  continuous_toFun := by
    have hs : Continuous (fun p : unitInterval × SourceModel (C 0) =>
        ((p.1 : ℝ) * r, p.2)) :=
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd
    simpa only [Function.comp_def] using (sourceRotation_continuous C ε hε).comp hs
  map_zero_left q := by
    change sourceRotation C ε hε (0 * r) q = sourceCollapse C ε hε q
    rw [zero_mul, sourceRotation_zero]
  map_one_left q := by
    change sourceRotation C ε hε (1 * r) q = sourceRotation C ε hε r q
    rw [one_mul]

theorem sourceCollapse_monodromy_homotopic :
    (sourceCollapse C ε hε).Homotopic
      ((sourceCollapse C ε hε).comp (sourceShear (C 0))) := by
  rw [← sourceRotation_one]
  exact ⟨sourceRotationHomotopy C ε hε 1⟩

theorem sourceRotation_homologyMap (r : ℝ) (n : ℕ) :
    singularHomologyMap (sourceRotation C ε hε r) n =
      singularHomologyMap (sourceCollapse C ε hε) n :=
  (homotopy_homologyMap (sourceRotationHomotopy C ε hε r) n).symm

/-- The actual homology map, in every degree, is invariant under the
actual descended unipotent shear. -/
theorem sourceCollapse_homologyMap_comp_sourceShear (n : ℕ) :
    (singularHomologyMap (sourceCollapse C ε hε) n).comp
        (singularHomologyMap (sourceShear (C 0)) n) =
      singularHomologyMap (sourceCollapse C ε hε) n := by
  rw [← singularHomologyMap_comp]
  exact (homotopic_homologyMap (sourceCollapse_monodromy_homotopic C ε hε) n).symm

theorem sourceCollapse_kills_sourceShear_variation (n : ℕ)
    (a : SingularHomology (SourceModel (C 0)) n) :
    singularHomologyMap (sourceCollapse C ε hε) n
        (singularHomologyMap (sourceShear (C 0)) n a - a) = 0 := by
  rw [map_sub, ← LinearMap.comp_apply, sourceCollapse_homologyMap_comp_sourceShear, sub_self]

theorem sourceShear_variation_range_le_kernel (n : ℕ) :
    LinearMap.range (singularHomologyMap (sourceShear (C 0)) n - LinearMap.id) ≤
      LinearMap.ker (singularHomologyMap (sourceCollapse C ε hε) n) := by
  rintro a ⟨b, rfl⟩
  exact sourceCollapse_kills_sourceShear_variation C ε hε n b

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
