import Wikipedia.NoExoticSixSphere.DirectedOpenCoverChains
import Wikipedia.NoExoticSixSphere.CompactSupportNeighborhoodZero

/-!
# Genuine compact-support classes in directed open covers

The actual compact support is contained in a single cover member.
Original inverse excision gives a class there whose actual extension
is the original ambient class. This also proves vanishing on the
ambient direct limit when it holds on every member.
-/

noncomputable section

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] {ι : Type*} [Nonempty ι]
  (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)

include hdir hcover in
/-- Every actual ambient compact-support class is an original extension from a cover member. -/
theorem exists_directed_cover_representative (p : ℕ) (a : Cohomology X p) :
    ∃ (i : ι) (b : Cohomology (U i) p), inclusion (U i) (hU i) p b = a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  obtain ⟨i, hi⟩ := DirectedOpenCover.exists_compact_subset U hU hdir hcover
    (K : Set X) K.isCompact
  exact ⟨i, neighborhoodOf (U i) (hU i) K hi p b,
    inclusion_neighborhoodOf (U i) (hU i) K hi p b⟩

include hU hdir hcover in
/-- Vanishing on the members implies vanishing of the original ambient compact-support group. -/
theorem subsingleton_of_directed_cover (p : ℕ) (h : ∀ i, Subsingleton (Cohomology (U i) p)) :
    Subsingleton (Cohomology X p) := by
  have hz (a : Cohomology X p) : a = 0 := by
    obtain ⟨i, b, hb⟩ := exists_directed_cover_representative U hU hdir hcover p a
    let := h i
    exact hb.symm.trans ((congrArg (inclusion (U i) (hU i) p)
      (Subsingleton.elim b 0)).trans (inclusion (U i) (hU i) p).map_zero)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end NoExoticSixSphere.CompactSupportCohomology
