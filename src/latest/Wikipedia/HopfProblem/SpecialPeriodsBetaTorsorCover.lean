import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorDescent
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCover

/-!
# The actual finite-coordinate cover upstairs

The transported compact quotient cover pulls back to the literal saturations
of the regular, elliptic, and cusp sheets.  Every finite coordinate in one of
these patches has a representative in its specified sheet.  In particular,
every sufficiently large finite coordinate has an actual high-cusp lift.
-/

noncomputable section

open Set Metric Topology UpperHalfPlane TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

open MuTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

/-- The actual saturation of a common-cover patch, bundled as an open set. -/
def patchSaturation (i : Cover.Index) : Opens ℍ :=
  ⟨(Cover.patch i).saturation, (Cover.patch i).saturation_isOpen⟩

theorem patchSaturation_invariant (i : Cover.Index) (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ patchSaturation i ↔ z ∈ patchSaturation i :=
  (Cover.patch i).saturation_invariant g z

/-- The actual open domain on which two extended local sections overlap. -/
def overlapDomain (i j : Cover.Index) : Opens ℍ := patchSaturation i ⊓ patchSaturation j

theorem overlapDomain_invariant (i j : Cover.Index) (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ overlapDomain i j ↔ z ∈ overlapDomain i j :=
  (patchSaturation_invariant i g z).and (patchSaturation_invariant j g z)

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

theorem finiteProjection_mem_patch (i : Cover.Index) (z : ℍ) :
    finiteProjection π z ∈ Cover.finitePatch π i ↔ z ∈ patchSaturation i := by
  rw [Cover.finitePatch, finiteProjection_mem_pullback π hπ]
  change z ∈ triangleCompactifiedProjection ⁻¹'
    (Cover.compactPatch i : Set TriangleCompactifiedOrbitSpace) ↔ _
  rw [Cover.compactPatch_preimage_projection]
  rfl

theorem finiteProjection_preimage_patch (i : Cover.Index) :
    finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ) = patchSaturation i := by
  ext z
  exact finiteProjection_mem_patch π hπ i z

/-- Every base point in a patch has a lift in that patch's actual sheet,
not merely an arbitrary lift in its saturation. -/
theorem finitePatch_eq_image_sheet (i : Cover.Index) :
    (Cover.finitePatch π i : Set ℂ) =
      finiteProjection π '' ((Cover.patch i).sheet : Set ℍ) := by
  ext t
  constructor
  · intro ht
    obtain ⟨z, hz⟩ := finiteProjection_surjective π hπ t
    have hzs : z ∈ patchSaturation i :=
      (finiteProjection_mem_patch π hπ i z).mp (hz ▸ ht)
    obtain ⟨g, x, hx, hg⟩ := hzs
    refine ⟨x, hx, ?_⟩
    exact (finiteProjection_invariant π g x).symm.trans
      ((congrArg (finiteProjection π) hg).trans hz)
  · rintro ⟨z, hz, rfl⟩
    exact (finiteProjection_mem_patch π hπ i z).mpr ((Cover.patch i).mem_saturation z hz)

theorem finiteDescentDomain_overlap (i j : Cover.Index) :
    finiteDescentDomain π hπ (overlapDomain i j) =
      Cover.finitePatch π i ⊓ Cover.finitePatch π j := by
  ext t
  obtain ⟨z, rfl⟩ := finiteProjection_surjective π hπ t
  change finiteProjection π z ∈ finiteDescentDomain π hπ (overlapDomain i j) ↔
    finiteProjection π z ∈ Cover.finitePatch π i ∧
      finiteProjection π z ∈ Cover.finitePatch π j
  rw [finiteDescentDomain_projection π hπ _ (overlapDomain_invariant i j)]
  change z ∈ patchSaturation i ∧ z ∈ patchSaturation j ↔
    finiteProjection π z ∈ Cover.finitePatch π i ∧
      finiteProjection π z ∈ Cover.finitePatch π j
  rw [finiteProjection_mem_patch π hπ i, finiteProjection_mem_patch π hπ j]

/-- The exterior region of the actual cusp patch has representatives in
the distinguished high horodisc. -/
theorem cusp_tail_lifts {R : ℝ}
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ Cover.finitePatch π Cover.cuspIndex)
    (t : ℂ) (ht : R < ‖t‖) :
    ∃ z ∈ Triangle.horodisc Triangle.width, finiteProjection π z = t := by
  have htU : t ∈ Cover.finitePatch π Cover.cuspIndex := hRU (by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using ht.le)
  change t ∈ (Cover.finitePatch π Cover.cuspIndex : Set ℂ) at htU
  rw [finitePatch_eq_image_sheet π hπ] at htU
  exact htU

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
