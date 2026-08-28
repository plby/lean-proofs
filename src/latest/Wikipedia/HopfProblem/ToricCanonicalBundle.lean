import Wikipedia.HopfProblem.CanonicalBundle
import Wikipedia.HopfProblem.ToricLogVolume

/-!
# The canonical bundle of the toric threefold

The signed chart-volume coefficients define a genuine holomorphic
canonical line bundle and a global holomorphic trivialization on the
actual glued toric space.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The existing toric atlas, equipped with its checked signed Jacobian
law. No new analytic chart structure is imposed on the space. -/
def volumeAtlas : CanonicalBundle.ConstantVolumeAtlas Space Triangle where
  chart s := (parametrization s).symm
  chart_mem_maximalAtlas s := IsManifold.subset_maximalAtlas (mem_range_self s)
  indexAt := preferredTriangle
  mem_source x := mem_chart_source (CoordinateSpace 3) x
  coefficient s := (s.rays.det : ℂ)
  coefficient_ne_zero := Triangle.signed_volume_coefficient_ne_zero
  jacobian_eq s t _z hz := parametrization_transition_det_fderiv s t hz

/-- The canonical line bundle is built from the inverse derivatives of
the toric coordinate transitions. -/
abbrev canonicalBundle := volumeAtlas.core

/-- The holomorphic nowhere-zero three-form in canonical-bundle fibres. -/
def canonicalVolume (x : Space) : canonicalBundle.Fiber x := volumeAtlas.volumeSection x

theorem canonicalVolume_ne_zero (x : Space) : canonicalVolume x ≠ 0 :=
  volumeAtlas.volumeSection_ne_zero x

theorem canonicalVolume_holomorphic :
    ContMDiff I₃ ((I₃).prod I₁) ω
      (fun x => (⟨x, canonicalVolume x⟩ : canonicalBundle.TotalSpace)) :=
  volumeAtlas.volumeSection_holomorphic

/-- In each actual toric chart, the form is its signed ordinary coordinate
volume form, including over the coordinate boundary. -/
theorem canonicalVolume_in_coordinates (s : Triangle) (x : Space) :
    volumeAtlas.inCoordinates s x (canonicalVolume x) =
      (s.rays.det : ℂ) • CanonicalBundle.volume :=
  volumeAtlas.volumeSection_inCoordinates s x

/-- The global canonical section restricts to the exact logarithmic form
displayed in Proposition 4.5(e), not just to some nonzero volume form. -/
theorem canonicalVolume_restricts_to_logarithmicVolume (s : Triangle)
    {z : CoordinateSpace 3} (hz : z ∈ torus) :
    volumeAtlas.inCoordinates s (inclusion s z) (canonicalVolume (inclusion s z)) =
      (CanonicalBundle.logarithmicVolume (torusCoordinates (inclusion s z))).compContinuousLinearMap
        (fderiv ℂ (torusCoordinates ∘ inclusion s) z) := by
  rw [canonicalVolume_in_coordinates, torusCoordinates_chart_pullback_logarithmicVolume s hz]

/-- An actual holomorphic bundle trivialization: a biholomorphism of total
spaces, covering the identity on the toric threefold. -/
def canonicalTrivialization :
    Diffeomorph ((I₃).prod I₁) ((I₃).prod I₁) canonicalBundle.TotalSpace (Space × ℂ) ω :=
  volumeAtlas.globalTrivialization

@[simp] theorem canonicalTrivialization_fst (p : canonicalBundle.TotalSpace) :
    (canonicalTrivialization p).1 = p.1 := rfl

theorem canonicalTrivialization_add (x : Space) (v w : canonicalBundle.Fiber x) :
    (canonicalTrivialization ⟨x, v + w⟩).2 =
      (canonicalTrivialization ⟨x, v⟩).2 + (canonicalTrivialization ⟨x, w⟩).2 :=
  volumeAtlas.globalTrivialization_add x v w

theorem canonicalTrivialization_smul (x : Space) (c : ℂ) (v : canonicalBundle.Fiber x) :
    (canonicalTrivialization ⟨x, c • v⟩).2 = c • (canonicalTrivialization ⟨x, v⟩).2 :=
  volumeAtlas.globalTrivialization_smul x c v

end Wikipedia.HopfProblem.ToricSpace
