import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspRegular
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspLocalAnalytic
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientLocalBiholomorph

/-!
# The actual cusp-image chart is biholomorphic

The quotient already has its independently constructed complex atlas.
On a high horodisc its projection is locally biholomorphic, since every
point there has trivial stabilizer.  Both directions of the exponential
cusp-image homeomorphism are then holomorphic by descent through actual
surjective local biholomorphisms.

The resulting ambient partial biholomorphism has exactly the previously
constructed cusp image as source and the punctured complex ball as
target.  This supplies the analytic interface for attaching the cusp.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] triangleOrbitChartedSpace

local instance : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace := triangleOrbit_isManifold

/-- The original full quotient projection, restricted to a high
horodisc and its image, is locally biholomorphic in the existing atlas. -/
theorem cuspImageProjection_isLocalDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageProjection Y) := by
  intro z
  exact isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
    (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular
      (horodisc_subset_triangleRegularLocus Y hY z.property))
    (horodisc Y) (cuspImage Y) (fun w hw => ⟨w, hw, rfl⟩) z.property

/-- The actual exponential cusp-image homeomorphism is holomorphic for
the quotient's constructed complex structure. -/
theorem cuspImageHomeomorph_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageHomeomorph Y hY) := by
  apply contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
    (cuspImageProjection_isLocalDiffeomorph Y hY) (cuspImageProjection_surjective Y)
  have he : (cuspImageHomeomorph Y hY) ∘ cuspImageProjection Y = cuspQHorodisc Y := by
    funext z
    exact cuspImageHomeomorph_mk Y hY z
  rw [he]
  exact cuspQHorodisc_holomorphic Y

/-- The inverse is holomorphic as well: its pullback by the noncritical
exponential is the original holomorphic quotient projection. -/
theorem cuspImageHomeomorph_symm_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageHomeomorph Y hY).symm := by
  apply contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
    (cuspQHorodisc_isLocalDiffeomorph Y)
    (cuspQHorodisc_surjective Y (width_pos.le.trans hY))
  have he : (cuspImageHomeomorph Y hY).symm ∘ cuspQHorodisc Y = cuspImageProjection Y := by
    funext z
    exact cuspImageHomeomorph_symm_q Y hY z
  rw [he]
  exact (cuspImageProjection_isLocalDiffeomorph Y hY).contMDiff

/-- The already constructed homeomorphism is a genuine biholomorphism;
its underlying map and inverse are unchanged. -/
def cuspImageBiholomorph (Y : ℝ) (hY : width ≤ Y) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (cuspImage Y) (puncturedCuspBall Y) ω where
  toEquiv := (cuspImageHomeomorph Y hY).toEquiv
  contMDiff_toFun := cuspImageHomeomorph_holomorphic Y hY
  contMDiff_invFun := cuspImageHomeomorph_symm_holomorphic Y hY

@[simp] theorem cuspImageBiholomorph_toHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    (cuspImageBiholomorph Y hY).toHomeomorph = cuspImageHomeomorph Y hY := by
  ext x
  rfl

@[simp] theorem cuspImageBiholomorph_apply (Y : ℝ) (hY : width ≤ Y) (x : cuspImage Y) :
    cuspImageBiholomorph Y hY x = cuspImageHomeomorph Y hY x := rfl

/-- The complex-valued cusp coordinate on the open cusp image. -/
def cuspImageCoordinate (Y : ℝ) (hY : width ≤ Y) (x : cuspImage Y) : ℂ :=
  cuspImageHomeomorph Y hY x

@[simp] theorem cuspImageCoordinate_projection (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspImageCoordinate Y hY (cuspImageProjection Y z) = cuspQ (z : ℍ) :=
  cuspImageHomeomorph_mk_coe Y hY z

theorem cuspImageCoordinate_isLocalDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageCoordinate Y hY) := by
  intro x
  exact ((cuspImageBiholomorph Y hY).isLocalDiffeomorph x).comp
    (K := 𝓘(ℂ)) (P := ℂ)
    (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (puncturedCuspBall Y)
      (cuspImageBiholomorph Y hY x))

theorem cuspImageCoordinate_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageCoordinate Y hY) :=
  (cuspImageCoordinate_isLocalDiffeomorph Y hY).contMDiff

private theorem cuspImageNonemptyForChart (Y : ℝ) : Nonempty (cuspImage Y) := by
  obtain ⟨z, hz⟩ := horodisc_nonempty Y
  exact ⟨cuspImageProjection Y ⟨z, hz⟩⟩

/-- The ambient partial biholomorphism of the full quotient defined by
the actual cusp image and its proved exponential coordinate. -/
def cuspImagePartialDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω :=
  (opensInclusionPartialDiffeomorph 𝓘(ℂ) (cuspImage Y)
    (cuspImageNonemptyForChart Y)).symm.trans
    ((cuspImageBiholomorph Y hY).toPartialDiffeomorph.trans
      (opensInclusionPartialDiffeomorph 𝓘(ℂ) (puncturedCuspBall Y)
        ((cuspImageNonemptyForChart Y).map (cuspImageHomeomorph Y hY))))

@[simp] theorem cuspImagePartialDiffeomorph_source (Y : ℝ) (hY : width ≤ Y) :
    (cuspImagePartialDiffeomorph Y hY).source = (cuspImage Y : Set TriangleOrbitSpace) := by
  simp [cuspImagePartialDiffeomorph, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem cuspImagePartialDiffeomorph_target (Y : ℝ) (hY : width ≤ Y) :
    (cuspImagePartialDiffeomorph Y hY).target = (puncturedCuspBall Y : Set ℂ) := by
  simp [cuspImagePartialDiffeomorph, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

/-- On its exact source, the ambient chart is the existing cusp-image
homeomorphism followed by the literal complex inclusion. -/
theorem cuspImagePartialDiffeomorph_apply (Y : ℝ) (hY : width ≤ Y)
    (x : TriangleOrbitSpace) (hx : x ∈ cuspImage Y) :
    cuspImagePartialDiffeomorph Y hY x = (cuspImageHomeomorph Y hY ⟨x, hx⟩ : ℂ) := by
  let e := (cuspImage Y).openPartialHomeomorphSubtypeCoe (cuspImageNonemptyForChart Y)
  have he : e.symm x = ⟨x, hx⟩ :=
    e.left_inv (mem_univ (⟨x, hx⟩ : cuspImage Y))
  change (cuspImageBiholomorph Y hY (e.symm x) : ℂ) = _
  rw [he]
  rfl

@[simp] theorem cuspImagePartialDiffeomorph_projection (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    cuspImagePartialDiffeomorph Y hY (triangleOrbitProjection (z : ℍ)) = cuspQ (z : ℍ) := by
  rw [cuspImagePartialDiffeomorph_apply Y hY _ ⟨z, z.property, rfl⟩]
  exact cuspImageHomeomorph_mk_coe Y hY z

theorem cuspImagePartialDiffeomorph_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspImagePartialDiffeomorph Y hY)
      (cuspImage Y : Set TriangleOrbitSpace) := by
  simpa only [cuspImagePartialDiffeomorph_source] using
    (cuspImagePartialDiffeomorph Y hY).contMDiffOn

theorem cuspImagePartialDiffeomorph_isLocalDiffeomorphAt (Y : ℝ) (hY : width ≤ Y)
    {x : TriangleOrbitSpace} (hx : x ∈ cuspImage Y) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspImagePartialDiffeomorph Y hY) x := by
  apply (cuspImagePartialDiffeomorph Y hY).isLocalDiffeomorphAt _ _ _
  rw [cuspImagePartialDiffeomorph_source]
  exact hx

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
