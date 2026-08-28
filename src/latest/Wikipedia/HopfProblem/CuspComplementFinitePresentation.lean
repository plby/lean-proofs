import Wikipedia.HopfProblem.CuspComplementFiniteCoordinates

/-!
# A finite native quotient presentation of the actual relative cusp region

The setoid is the pullback of the original twisted-lattice orbit relation,
not a replacement relation defined by the desired target. On the bounded
coordinate pieces it is exactly the finite set of original deck collisions.
The quotient has its ordinary quotient topology, and the original map is
a homeomorphism onto the literal compact cusp complement.

This is a finite overlap presentation, not a cell decomposition or a
handle-cancellation assertion.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

attribute [local instance] Threefold.space_t2Space

/-- The unchanged original lattice relation pulled back to the finite carved coordinates. -/
def coordinateRelation : Setoid carvedCoordinates :=
  Setoid.comap (fun p : carvedCoordinates => coordinateLift p.val)
    (CuspQuotient.relation (CD).correction (CD).radius)

/-- Its fibres are exactly the fibres of the original actual-complement map. -/
theorem coordinateRelation_iff (p q : carvedCoordinates) :
    coordinateRelation.r p q ↔ presentationMap p = presentationMap q := by
  constructor
  · intro h
    have hq : CuspQuotient.quotientMap (CD).correction (CD).radius (coordinateLift p.val) =
        CuspQuotient.quotientMap (CD).correction (CD).radius (coordinateLift q.val) :=
      Quotient.sound h
    apply Subtype.ext
    exact congrArg CuspGeometry.inclusion hq
  · intro h
    have hq : CuspQuotient.quotientMap (CD).correction (CD).radius (coordinateLift p.val) =
        CuspQuotient.quotientMap (CD).correction (CD).radius (coordinateLift q.val) :=
      CuspGeometry.inclusion_injective (congrArg (fun x : capComplement =>
        (x : Threefold.Space)) h)
    change (CuspQuotient.relation (CD).correction (CD).radius).r
      (coordinateLift p.val) (coordinateLift q.val)
    exact Quotient.exact hq

/-- Only the finite actual collision set is needed to identify two remaining representatives. -/
theorem coordinateRelation_iff_finiteDeck (p q : carvedCoordinates) :
    coordinateRelation.r p q ↔
      ∃ v ∈ finiteKCollision capRadius,
        ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v
          (coordinateLift q.val) = coordinateLift p.val := by
  rw [coordinateRelation_iff, Subtype.ext_iff]
  exact nativeQuotientMap_eq_iff_finiteKCollision capRadius
    (coordinateLift_mem_representatives p.val) (coordinateLift_mem_representatives q.val)

theorem coordinateRelation_decks_finite : (finiteKCollision capRadius).Finite :=
  finiteKCollision_finite capRadius_lt_cuspRadius

/-- The finite carved presentation with its genuine quotient topology. -/
abbrev FiniteModel := Quotient coordinateRelation

/-- Descent of the original coordinate map, retaining the actual relative cusp target. -/
def finiteModelMap : FiniteModel → capComplement :=
  Quotient.lift presentationMap (fun p q h => (coordinateRelation_iff p q).mp h)

@[simp] theorem finiteModelMap_mk (p : carvedCoordinates) :
    finiteModelMap (Quotient.mk coordinateRelation p) = presentationMap p := rfl

theorem finiteModelMap_continuous : Continuous finiteModelMap :=
  presentationMap_continuous.quotient_lift _

theorem finiteModelMap_injective : Function.Injective finiteModelMap := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro a b h
  exact Quotient.sound ((coordinateRelation_iff a b).mpr h)

theorem finiteModelMap_surjective : Function.Surjective finiteModelMap := by
  intro x
  obtain ⟨p, rfl⟩ := presentationMap_surjective x
  exact ⟨Quotient.mk coordinateRelation p, rfl⟩

/-- The actual compact cusp complement is exactly this finite original-overlap quotient. -/
def finiteModelHomeomorph : FiniteModel ≃ₜ capComplement :=
  let h := finiteModelMap_continuous.isClosedEmbedding finiteModelMap_injective
  h.toIsEmbedding.toHomeomorphOfSurjective finiteModelMap_surjective

@[simp] theorem finiteModelHomeomorph_mk (p : carvedCoordinates) :
    finiteModelHomeomorph (Quotient.mk coordinateRelation p) = presentationMap p := rfl

@[simp] theorem finiteModelHomeomorph_mk_coe (p : carvedCoordinates) :
    (finiteModelHomeomorph (Quotient.mk coordinateRelation p) : Threefold.Space) =
      Coordinates.toGlobal capRadius capRadius_lt_cuspRadius p.val := rfl

/-- Equality in the finite model is still the explicitly retained finite original deck relation. -/
theorem finiteModel_mk_eq_iff (p q : carvedCoordinates) :
    Quotient.mk coordinateRelation p = Quotient.mk coordinateRelation q ↔
      ∃ v ∈ finiteKCollision capRadius,
        ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v
          (coordinateLift q.val) = coordinateLift p.val :=
  Quotient.eq.trans (coordinateRelation_iff_finiteDeck p q)

/-- The outer boundary mark keeps the original cubic toric time in every finite chart. -/
theorem coordinateMap_mem_outerBoundary_iff (p : FiniteCoordinates) :
    coordinateMap p ∈ outerBoundary ↔ ‖ToricFan.Triangle.time p.2‖ = capRadius := by
  constructor
  · intro hp
    simpa only [coordinateMap_time] using outerBoundary_time hp
  · intro hp
    let q : CuspGeometry.LocalSpace :=
      CuspQuotient.quotientMap (CD).correction (CD).radius (coordinateLift p)
    refine ⟨q, ?_, rfl⟩
    have h : CuspGeometry.parameter q = ToricFan.Triangle.time p.2 :=
      ToricSpace.time_inclusion (Coordinates.triangle p.1) p.2
    exact (congrArg norm h).trans hp

/-- The inner boundary mark is exactly the remaining finite closed normal cuts. -/
theorem presentationMap_mem_innerBoundary_iff (p : carvedCoordinates) :
    (presentationMap p : Threefold.Space) ∈ frontier closedDiskNeighborhood ↔
      coordinateLift p.val ∈ ⋃ v ∈ finiteRelevantDeck capRadius,
        ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
          closedNormalLifts := by
  rw [closedDiskNeighborhood_isCompact.isClosed.frontier_eq]
  have hn : coordinateMap p.val ∉ interior closedDiskNeighborhood :=
    (mem_carvedCoordinates_iff p.val).mp p.property
  change nativeQuotientMap (coordinateLift p.val) ∉ interior closedDiskNeighborhood at hn
  have h := Set.ext_iff.mp (closedNormalCut_eq_finiteRelevantDeck capRadius)
    (coordinateLift p.val)
  have hp := coordinateLift_mem_representatives p.val
  simpa only [mem_inter_iff, mem_preimage, hp, true_and, mem_sdiff, hn, and_true,
    not_false_eq_true, presentationMap_coe, coordinateMap, Function.comp_apply] using h

end Wikipedia.HopfProblem.CuspComplement
