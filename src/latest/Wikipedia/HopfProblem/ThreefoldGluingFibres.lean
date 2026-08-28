import Wikipedia.HopfProblem.ThreefoldGluingProper
import Mathlib.Topology.Connected.Clopen

/-!
# Literal fibres and connectedness of the actual glued projection

Each full local piece identifies its literal fibre homeomorphically with
the corresponding literal global fibre. This transfers connectedness,
not just a set-theoretic description. A proper projection with these
connected fibres has connected total space over a connected base.
-/

noncomputable section

open Set Topology TopologicalSpace

universe u

namespace Wikipedia.HopfProblem.ThreefoldGluing.Data

variable {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)

/-- The natural inclusion gives a homeomorphism of the actual fibres,
both carrying their inherited subspace topologies. -/
def fibreHomeomorph (i : D.J) (b : D.patch i) :
    (D.localProjection i ⁻¹' {b}) ≃ₜ (D.projection ⁻¹' {(b : B)}) :=
  ((D.inclusion_openEmbedding i).isEmbedding.homeomorphImage
    (D.localProjection i ⁻¹' {b})).trans
      (Homeomorph.setCongr (D.projection_fibre_eq_localImage i b).symm)

@[simp] theorem fibreHomeomorph_val (i : D.J) (b : D.patch i)
    (x : D.localProjection i ⁻¹' {b}) :
    (D.fibreHomeomorph i b x : D.Space) = D.inclusion i x := rfl

theorem fibreHomeomorph_symm_inclusion (i : D.J) (b : D.patch i)
    (x : D.projection ⁻¹' {(b : B)}) :
    D.inclusion i ((D.fibreHomeomorph i b).symm x) = x.val := by
  exact congrArg Subtype.val ((D.fibreHomeomorph i b).apply_symm_apply x)

/-- Every global fibre inherits connectedness from any local piece
whose base patch contains the point. -/
theorem projection_fibre_isConnected
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' {b}))
    (b : B) : IsConnected (D.projection ⁻¹' {b}) := by
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  rw [D.projection_fibre_eq_localImage i ⟨b, hi⟩]
  exact (hlocal i ⟨b, hi⟩).image (D.inclusion i)
    (D.inclusion_openEmbedding i).continuous.continuousOn

theorem projection_fibre_connectedSpace
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' {b}))
    (b : B) : ConnectedSpace (D.projection ⁻¹' {b}) :=
  isConnected_iff_connectedSpace.mp (D.projection_fibre_isConnected hlocal b)

/-- Connected fibres already imply surjectivity, because they are nonempty. -/
theorem projection_surjective_of_connected_fibres
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' {b})) :
    Function.Surjective D.projection := by
  intro b
  obtain ⟨x, hx⟩ := (D.projection_fibre_isConnected hlocal b).nonempty
  exact ⟨x, hx⟩

/-- A connected base and proper local projections with connected
fibres give a connected actual gluing, without a connectedness field
or an assumed global fibration theorem. -/
theorem connectedSpace [ConnectedSpace B]
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i))
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' {b})) :
    ConnectedSpace D.Space := by
  have hq : IsQuotientMap D.projection :=
    (D.projection_proper hproper).isClosedMap.isQuotientMap
      D.projection_continuous (D.projection_surjective_of_connected_fibres hlocal)
  apply connectedSpace_iff_univ.mpr
  simpa only [preimage_univ] using
    hq.isCoinducing.isConnected_preimage_of_isClosed
      (D.projection_fibre_isConnected hlocal) isClosed_univ (isConnected_univ :
        IsConnected (univ : Set B))

end Wikipedia.HopfProblem.ThreefoldGluing.Data
