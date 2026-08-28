import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Strong local contractibility through original open charts

The contractible neighborhood basis of an actual open subspace gives a
contractible neighborhood basis in the ambient space. Each basis member
is transported by the genuine homeomorphism onto its image under the open
subtype inclusion. This local criterion applies to original partial
homeomorphism covers and to native charted-space atlases.
-/

noncomputable section

open Set Topology TopologicalSpace Filter

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility

variable {M : Type*} [TopologicalSpace M]

/-- Strong local contractibility is local on original open subspaces. -/
theorem stronglyLocallyContractible_of_open_neighborhoods
    (h : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ StronglyLocallyContractibleSpace U) :
    StronglyLocallyContractibleSpace M := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro W hW
  obtain ⟨U, hxU, hU⟩ := h x
  let : StronglyLocallyContractibleSpace U := hU
  have hb : (𝓝 x).HasBasis
      (fun S : Set U => S ∈ 𝓝 (⟨x, hxU⟩ : U) ∧ ContractibleSpace S)
      (fun S => (Subtype.val : U → M) '' S) := by
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨x, hxU⟩ : U)]
    exact (contractible_basis (⟨x, hxU⟩ : U)).map Subtype.val
  obtain ⟨S, hS, hSW⟩ := hb.mem_iff.mp hW
  have hcontract : ContractibleSpace ((Subtype.val : U → M) '' S) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage S).contractibleSpace_iff.mp hS.2
  exact ⟨(Subtype.val : U → M) '' S, hb.mem_of_mem hS, hcontract, hSW⟩

/-- An original open partial homeomorphism transports strong local
contractibility from its source subspace to its target subspace. -/
theorem openPartialHomeomorph_target_stronglyLocallyContractible
    {H : Type*} [TopologicalSpace H] (e : OpenPartialHomeomorph H M)
    (hsource : StronglyLocallyContractibleSpace e.source) :
    StronglyLocallyContractibleSpace e.target := by
  let : StronglyLocallyContractibleSpace e.source := hsource
  exact e.toHomeomorphSourceTarget.symm.isOpenEmbedding.stronglyLocallyContractibleSpace

/-- A cover by original open partial homeomorphisms with strongly
locally contractible source subspaces proves the property on the target. -/
theorem stronglyLocallyContractible_of_openPartialHomeomorph_sources
    {ι : Type*} {H : ι → Type*} [∀ i, TopologicalSpace (H i)]
    (e : ∀ i, OpenPartialHomeomorph (H i) M)
    (hsource : ∀ i, StronglyLocallyContractibleSpace (e i).source)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).target) :
    StronglyLocallyContractibleSpace M := by
  apply stronglyLocallyContractible_of_open_neighborhoods
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨⟨(e i).target, (e i).open_target⟩, hi,
    openPartialHomeomorph_target_stronglyLocallyContractible (e i) (hsource i)⟩

/-- A cover by actual partial homeomorphisms from strongly locally
contractible models gives a genuine contractible neighborhood basis. -/
theorem stronglyLocallyContractible_of_openPartialHomeomorph_cover
    {ι : Type*} {H : ι → Type*} [∀ i, TopologicalSpace (H i)]
    (e : ∀ i, OpenPartialHomeomorph (H i) M)
    (hH : ∀ i, StronglyLocallyContractibleSpace (H i))
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).target) :
    StronglyLocallyContractibleSpace M := by
  apply stronglyLocallyContractible_of_openPartialHomeomorph_sources e _ hcover
  intro i
  let : StronglyLocallyContractibleSpace (H i) := hH i
  exact (e i).open_source.stronglyLocallyContractibleSpace

/-- Strong local contractibility transfers along the original native
charted-space atlas, without changing the topology or the charts. -/
theorem chartedSpace_stronglyLocallyContractibleSpace (H M : Type*)
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [StronglyLocallyContractibleSpace H] : StronglyLocallyContractibleSpace M := by
  apply stronglyLocallyContractible_of_openPartialHomeomorph_cover
    (H := fun _ : M => H) (fun x : M => (chartAt H x).symm) (fun _ => inferInstance)
  intro x
  exact ⟨x, mem_chart_source H x⟩

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalContractibility
