import Wikipedia.NoExoticSixSphere.CompactSupportNeighborhood

/-!
# Detecting zero after genuine compact-support enlargement

A zero direct-limit class becomes zero on a larger original compact
support. For a class excised into an open neighborhood, this enlargement
can be chosen as an actual ambient compact subset of that neighborhood.
The original inverse-excision maps retain the ambient class formula.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X : Type} [TopologicalSpace X]

/-- An actual compact-support representative is zero exactly after some support enlargement. -/
theorem of_eq_zero_iff (p : ℕ) (K : Compacts X) (a : Component X p K) :
    of X p K a = 0 ↔ ∃ (L : Compacts X) (h : K ≤ L), transition X p K L h a = 0 := by
  constructor
  · intro ha
    obtain ⟨L, hK, _, he⟩ := (of_eq_iff X p K K a 0).mp (ha.trans (of X p K).map_zero.symm)
    exact ⟨L, hK, he.trans (transition X p K L hK).map_zero⟩
  · rintro ⟨L, h, he⟩
    exact (of_transition X p h a).symm.trans
      ((congrArg (of X p L) he).trans (of X p L).map_zero)

variable [T2Space X] (U : Set X) (hU : IsOpen U)

/-- Ambient inclusion recovers the original class from its actual neighborhood restriction. -/
theorem inclusion_neighborhoodOf (K : Compacts X) (hKU : (K : Set X) ⊆ U)
    (p : ℕ) (a : Component X p K) :
    inclusion U hU p (neighborhoodOf U hU K hKU p a) = of X p K a := by
  have he := openMap_of_image (subtypeInclusion U) hU.isOpenEmbedding_subtypeVal p
    (insideCompact U K hKU) K (image_insideCompact U K hKU) (insideEquiv U hU K hKU p a)
  rw [openMap_subtype U hU p] at he
  exact he.trans (congrArg (of X p K)
    (OpenEmbeddingSupportCohomology.extension_restriction (subtypeInclusion U)
      hU.isOpenEmbedding_subtypeVal (insideCompact U K hKU : Set U)
      (insideCompact U K hKU).isCompact (K : Set X) (image_insideCompact U K hKU) p a))

/-- Zero after excision is witnessed by an ambient compact enlargement inside the neighborhood. -/
theorem neighborhoodOf_eq_zero_iff (K : Compacts X) (hKU : (K : Set X) ⊆ U)
    (p : ℕ) (a : Component X p K) :
    neighborhoodOf U hU K hKU p a = 0 ↔
      ∃ (L : Compacts X) (h : K ≤ L) (_hLU : (L : Set X) ⊆ U),
        SupportedModTwoCohomology.extend h p a = 0 := by
  constructor
  · intro ha
    obtain ⟨N, hN, he⟩ := (of_eq_zero_iff p (insideCompact U K hKU)
      (insideEquiv U hU K hKU p a)).mp ha
    let L := imageCompact U N
    have hKL : K ≤ L := by
      intro x hx
      exact ⟨⟨x, hKU hx⟩, hN hx, rfl⟩
    have hLU : (L : Set X) ⊆ U := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    refine ⟨L, hKL, hLU, ?_⟩
    let R := OpenEmbeddingSupportCohomology.restrictionEquiv (subtypeInclusion U)
      hU.isOpenEmbedding_subtypeVal (N : Set U) N.isCompact (L : Set X) rfl p
    apply R.injective
    have hs := congrArg (fun m => HomologicalComplex.homologyMap m p)
      (OpenEmbeddingSupportCohomology.restrictionMap_extend (subtypeInclusion U)
        hU.isOpenEmbedding_subtypeVal hN hKL (image_insideCompact U K hKU) rfl)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hs
    exact (congrArg (fun m => m.hom a) hs).trans (he.trans R.map_zero.symm)
  · rintro ⟨L, h, hLU, he⟩
    exact (neighborhoodOf_extend U hU h hKU hLU p a).symm.trans
      ((congrArg (neighborhoodOf U hU L hLU p) he).trans
        (neighborhoodOf U hU L hLU p).map_zero)

end NoExoticSixSphere.CompactSupportCohomology
