import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.CuspStrata

/-!
# The actual global cusp fibre

The literal fibre of the constructed sphere projection over infinity is
homeomorphic, by the actual cusp inclusion, to the central fibre of the
original toric quotient.  The chart-independent number of local branches
therefore transfers to this global fibre without identifying it with a
substitute topological model.
-/

noncomputable section

open Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

open Triangle

/-- The unchanged central fibre of the actual restricted cusp quotient. -/
def localCentralFibre : Set LocalSpace := parameter ⁻¹' {0}

/-- The literal global fibre over infinity in the normalized sphere. -/
def sphereCuspFibre : Set Threefold.Space :=
  Threefold.projectionSphere ⁻¹' {(∞ : RiemannSphere)}

@[simp] theorem mem_localCentralFibre (x : LocalSpace) :
    x ∈ localCentralFibre ↔ parameter x = 0 := Iff.rfl

@[simp] theorem mem_sphereCuspFibre (x : Threefold.Space) :
    x ∈ sphereCuspFibre ↔ Threefold.projectionSphere x = (∞ : RiemannSphere) := Iff.rfl

@[simp] theorem inclusion_mem_sphereCuspFibre_iff (x : LocalSpace) :
    inclusion x ∈ sphereCuspFibre ↔ x ∈ localCentralFibre :=
  projectionSphere_inclusion_eq_infty_iff x

/-- The cusp chart contains the whole global fibre, not only a
neighborhood of a chosen central point. -/
theorem sphereCuspFibre_eq_image : sphereCuspFibre = inclusion '' localCentralFibre := by
  ext p
  constructor
  · intro hp
    have hp' : Threefold.projection p = triangleCuspPoint := by
      apply triangleSphereUniformization.injective
      exact hp.trans triangleSphereUniformization_cusp.symm
    have hm : p ∈ range inclusion := by
      rw [inclusion_range]
      change Threefold.projection p ∈ specialBaseCover.fillingPatch none
      rw [hp']
      exact specialBaseCover.point_mem_fillingPatch none
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, (inclusion_mem_sphereCuspFibre_iff x).mp hp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (inclusion_mem_sphereCuspFibre_iff x).mpr hx

theorem exists_cusp_representative_of_projectionSphere_eq_infty
    (y : Threefold.Space) (hy : Threefold.projectionSphere y = (∞ : RiemannSphere)) :
    ∃ x : LocalSpace, parameter x = 0 ∧ inclusion x = y := by
  have hm : y ∈ inclusion '' localCentralFibre := by
    rw [← sphereCuspFibre_eq_image]
    exact hy
  exact hm

/-- The actual inclusion identifies the two literal fibres with their
inherited subspace topologies. -/
def centralFibreHomeomorph : localCentralFibre ≃ₜ sphereCuspFibre :=
  (inclusion_openEmbedding.isEmbedding.homeomorphImage localCentralFibre).trans
    (Homeomorph.setCongr sphereCuspFibre_eq_image.symm)

@[simp] theorem centralFibreHomeomorph_val (x : localCentralFibre) :
    (centralFibreHomeomorph x : Threefold.Space) = inclusion x := rfl

theorem centralFibreHomeomorph_symm_inclusion (x : sphereCuspFibre) :
    inclusion (centralFibreHomeomorph.symm x) = (x : Threefold.Space) :=
  congrArg Subtype.val (centralFibreHomeomorph.apply_symm_apply x)

theorem localCentralFibre_compact : IsCompact localCentralFibre :=
  CuspQuotient.central_fibre_compact data.correction data.radius data.radius_pos
    data.radius_lt_one data.holomorphic data.smallDrift

theorem localCentralFibre_connected : IsConnected localCentralFibre :=
  CuspQuotient.central_fibre_connected data.correction data.radius data.radius_pos

theorem sphereCuspFibre_compact : IsCompact sphereCuspFibre :=
  Threefold.projectionSphere_fibre_compact (∞ : RiemannSphere)

theorem sphereCuspFibre_connected : IsConnected sphereCuspFibre :=
  Threefold.projectionSphere_fibre_isConnected (∞ : RiemannSphere)

/-- The genuine toric branch count, transported through the fibre
homeomorphism induced by the actual open cusp inclusion. -/
def fibreBranchCount (x : sphereCuspFibre) : ℕ :=
  CuspQuotient.branchCount data.correction data.radius
    (centralFibreHomeomorph.symm x : LocalSpace)

@[simp] theorem fibreBranchCount_centralFibreHomeomorph (x : localCentralFibre) :
    fibreBranchCount (centralFibreHomeomorph x) =
      CuspQuotient.branchCount data.correction data.radius (x : LocalSpace) := by
  simp only [fibreBranchCount, Homeomorph.symm_apply_apply]

theorem fibreBranchCount_pos (x : sphereCuspFibre) : 0 < fibreBranchCount x :=
  (CuspQuotient.branchCount_pos_iff data.correction data.radius _).mpr
    (centralFibreHomeomorph.symm x).property

theorem fibreBranchCount_le_three (x : sphereCuspFibre) : fibreBranchCount x ≤ 3 :=
  CuspQuotient.branchCount_le_three data.correction data.radius _

/-- Every condition on the native number of branches transfers to its
literal image in the global cusp fibre. -/
theorem mem_image_branchCount_iff (P : ℕ → Prop) (x : sphereCuspFibre) :
    (x : Threefold.Space) ∈ inclusion ''
      {y : LocalSpace | P (CuspQuotient.branchCount data.correction data.radius y)} ↔
        P (fibreBranchCount x) := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = (centralFibreHomeomorph.symm x : LocalSpace) :=
      inclusion_injective (he.trans (centralFibreHomeomorph_symm_inclusion x).symm)
    change P (CuspQuotient.branchCount data.correction data.radius y) at hy
    change P (CuspQuotient.branchCount data.correction data.radius
      (centralFibreHomeomorph.symm x : LocalSpace))
    rwa [hyx] at hy
  · intro hx
    exact ⟨centralFibreHomeomorph.symm x, hx, centralFibreHomeomorph_symm_inclusion x⟩

theorem sphereCuspFibre_eq_image_branchCount_pos :
    sphereCuspFibre = inclusion ''
      {x : LocalSpace | 0 < CuspQuotient.branchCount data.correction data.radius x} := by
  rw [sphereCuspFibre_eq_image]
  congr 1
  ext x
  exact (CuspQuotient.branchCount_pos_iff data.correction data.radius x).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
