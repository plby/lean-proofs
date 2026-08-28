import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry

/-!
# The actual full-filling parametrizations into the global threefold

Restricting an original full elliptic filling to its chosen small open
piece, then applying the proved native patch inclusion, gives an analytic
partial diffeomorphism into the constructed threefold. Its source is the
literal small-filling domain and its target is the entire lifted elliptic
base patch. The original sphere coordinate agrees with the actual filling
projection on this complete source.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace Threefold.chartedSpace

/-- The literal selected open subset of the original full filling. -/
abbrev fullDomain (j : Elliptic.Kind) : TopologicalSpace.Opens (SpecialFullFilling j) :=
  pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    specialBaseCover j

/-- The actual full-filling map on its selected open source, with the
original native source atlas and the already constructed global atlas. -/
def fullParametrization (j : Elliptic.Kind) :
    PartialDiffeomorph IF IF (SpecialFullFilling j) Threefold.Space ω :=
  (opensInclusionPartialDiffeomorph IF (fullDomain j)
    (specialEllipticPiece_nonempty j)).symm.trans (nativeParametrization j)

@[simp] theorem fullParametrization_source (j : Elliptic.Kind) :
    (fullParametrization j).source = (fullDomain j : Set (SpecialFullFilling j)) := by
  simp [fullParametrization, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    opensInclusionPartialDiffeomorph, nativeParametrization_source]

@[simp] theorem fullParametrization_target (j : Elliptic.Kind) :
    (fullParametrization j).target =
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  simp [fullParametrization, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    opensInclusionPartialDiffeomorph, nativeParametrization_target]

/-- On every actual small-piece point, the full parametrization is its
original inclusion into the glued manifold. -/
@[simp] theorem fullParametrization_apply (j : Elliptic.Kind) (x : LocalSpace j) :
    fullParametrization j x.val = inclusion j x := by
  let e := opensInclusionPartialDiffeomorph IF (fullDomain j)
    (specialEllipticPiece_nonempty j)
  have he : e.symm (e x) = x := e.left_inv' (mem_univ _)
  change nativeParametrization j (e.symm (e x)) = inclusion j x
  rw [he, nativeParametrization_apply]

theorem fullParametrization_isLocalDiffeomorphAt (j : Elliptic.Kind)
    {x : SpecialFullFilling j} (hx : x ∈ (fullParametrization j).source) :
    IsLocalDiffeomorphAt IF IF ω (fullParametrization j) x :=
  (fullParametrization j).isLocalDiffeomorphAt IF IF ω hx

/-- The original sphere chart gives exactly the actual filling parameter
on the entire source of the full parametrization. -/
theorem sphereChart_projectionSphere_fullParametrization (j : Elliptic.Kind)
    (x : SpecialFullFilling j) (hx : x ∈ (fullParametrization j).source) :
    sphereChart j (Threefold.projectionSphere (fullParametrization j x)) =
      (specialFullFillingProjection j x : ℂ) := by
  have hx' : x ∈ (fullDomain j : Set (SpecialFullFilling j)) := by
    simpa only [fullParametrization_source] using hx
  let y : LocalSpace j := ⟨x, hx'⟩
  change sphereChart j (Threefold.projectionSphere (fullParametrization j y.val)) = _
  rw [fullParametrization_apply, sphereChart_projectionSphere_inclusion]
  rfl

theorem projectionSphere_fullParametrization_mem_sphereChart_source (j : Elliptic.Kind)
    (x : SpecialFullFilling j) (hx : x ∈ (fullParametrization j).source) :
    Threefold.projectionSphere (fullParametrization j x) ∈ (sphereChart j).source := by
  have hx' : x ∈ (fullDomain j : Set (SpecialFullFilling j)) := by
    simpa only [fullParametrization_source] using hx
  let y : LocalSpace j := ⟨x, hx'⟩
  change Threefold.projectionSphere (fullParametrization j y.val) ∈ _
  rw [fullParametrization_apply]
  exact projectionSphere_inclusion_mem_sphereChart_source j y

/-- Every point of the actual central fibre lies in the chosen small
domain, since the chosen radius is strictly positive. -/
theorem mem_fullParametrization_source_of_central (j : Elliptic.Kind)
    {x : SpecialFullFilling j}
    (hx : specialFullFillingProjection j x = Elliptic.discZero) :
    x ∈ (fullParametrization j).source := by
  rw [fullParametrization_source]
  change ‖(specialFullFillingProjection j x : ℂ)‖ < specialBaseCover.radius (some j)
  rw [hx, Elliptic.discZero_coe, norm_zero]
  exact specialBaseCover.radius_pos (some j)

/-- In particular, the whole actual central surface is inside the
analytic domain of the full parametrization. -/
theorem specialCentralInclusion_mem_fullParametrization_source (j : Elliptic.Kind)
    (x : SpecialCentralSurface j) :
    specialCentralInclusion j x ∈ (fullParametrization j).source := by
  apply mem_fullParametrization_source_of_central j
  exact (specialLocalData j).projection_centralFibreInclusion
    j.twist (Elliptic.mainTwist_admissible j) x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
