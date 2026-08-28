import Wikipedia.HopfProblem.CuspComplementCap
import Wikipedia.HopfProblem.CuspComplementCoordinates
import Wikipedia.HopfProblem.CuspComplementFiniteDeck

/-!
# Finitely carved native polydiscs for the actual cusp complement

The original cap is covered by exactly the 98 bounded native toric
polydiscs.  In each one the deleted interior is precisely the union of
the relevant original deck translates of the strict normal lift.  Only
finitely many deck elements occur.  The remaining coordinate domain is
compact and maps onto the actual compact cusp complement.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

attribute [local instance] Threefold.space_t2Space

/-- The literal disjoint union of the 98 closed unit-polydisc cap pieces. -/
abbrev FiniteCoordinates := Coordinates.Index × Coordinates.CoordinateCap capRadius

/-- The original toric coordinate representative, before any deck quotient. -/
def coordinateLift : FiniteCoordinates → NativeTube :=
  Coordinates.toTube capRadius capRadius_lt_cuspRadius

theorem coordinateLift_continuous : Continuous coordinateLift :=
  Coordinates.toTube_continuous capRadius capRadius_lt_cuspRadius

theorem coordinateLift_mem_representatives (p : FiniteCoordinates) :
    coordinateLift p ∈ CuspQuotient.tubeRepresentatives (CD).radius capRadius := by
  rw [← Coordinates.range_toTube capRadius capRadius_lt_cuspRadius]
  exact mem_range_self p

/-- The unchanged native coordinate map into the actual threefold. -/
def coordinateMap : FiniteCoordinates → Threefold.Space := nativeQuotientMap ∘ coordinateLift

theorem coordinateMap_continuous : Continuous coordinateMap :=
  nativeQuotientMap_continuous.comp coordinateLift_continuous

@[simp] theorem coordinateMap_native (p : FiniteCoordinates) :
    coordinateMap p = Coordinates.toGlobal capRadius capRadius_lt_cuspRadius p := rfl

@[simp] theorem coordinateMap_time (p : FiniteCoordinates) :
    CuspGeometry.cuspCoordinate (coordinateMap p) = ToricFan.Triangle.time p.2 := by
  have h : CuspGeometry.cuspCoordinate (coordinateMap p) =
      ToricSpace.time (coordinateLift p : ToricSpace.Space) :=
    CuspGeometry.cuspCoordinate_inclusion _
  exact h.trans (ToricSpace.time_inclusion (Coordinates.triangle p.1) p.2)

theorem coordinateMap_mem_cap (p : FiniteCoordinates) : coordinateMap p ∈ cap := by
  let q : CuspGeometry.LocalSpace :=
    CuspQuotient.quotientMap (CD).correction (CD).radius (coordinateLift p)
  refine ⟨q, ?_, rfl⟩
  change ‖CuspGeometry.parameter q‖ ≤ capRadius
  have h : CuspGeometry.parameter q = ToricFan.Triangle.time p.2 :=
    ToricSpace.time_inclusion (Coordinates.triangle p.1) p.2
  rw [h]
  exact p.2.property.2

/-- The finite toric cover covers the entire actual cap, including every central stratum. -/
theorem coordinateMap_range : range coordinateMap = cap := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, rfl⟩
    exact coordinateMap_mem_cap p
  · rintro x ⟨q, hq, rfl⟩
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q
    have hrep := CuspQuotient.mem_quotientRepresentatives (CD).correction (CD).radius
      (CD).radius_pos (CD).radius_lt_one (CD).holomorphic (CD).smallDrift
      capRadius_pos capRadius_lt_cuspRadius hq
    obtain ⟨y, hy, hzy⟩ := hrep
    rw [← Coordinates.range_toTube capRadius capRadius_lt_cuspRadius] at hy
    obtain ⟨p, hp⟩ := hy
    refine ⟨p, ?_⟩
    change nativeQuotientMap (coordinateLift p) = CuspGeometry.inclusion _
    change Coordinates.toTube capRadius capRadius_lt_cuspRadius p = y at hp
    change nativeQuotientMap (Coordinates.toTube capRadius capRadius_lt_cuspRadius p) = _
    rw [hp]
    exact congrArg CuspGeometry.inclusion hzy

/-- The finite family of original translates of the strict normal lift. -/
def deletedLift : Set NativeTube :=
  ⋃ v ∈ finiteRelevantDeck capRadius,
    ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
      openNormalLifts

theorem deletedLift_decks_finite : (finiteRelevantDeck capRadius).Finite :=
  finiteRelevantDeck_finite capRadius_lt_cuspRadius

/-- Exact deletion on each bounded coordinate piece, using the original quotient. -/
theorem coordinateLift_mem_deletedLift_iff (p : FiniteCoordinates) :
    coordinateLift p ∈ deletedLift ↔ coordinateMap p ∈ interior closedDiskNeighborhood := by
  have h := Set.ext_iff.mp (openNormalCut_eq_finiteRelevantDeck capRadius) (coordinateLift p)
  have hp := coordinateLift_mem_representatives p
  simpa only [mem_inter_iff, mem_preimage, hp, true_and, coordinateMap,
    Function.comp_apply, deletedLift] using h.symm

/-- The 98 native cap pieces with precisely the finite strict normal cuts removed. -/
def carvedCoordinates : Set FiniteCoordinates :=
  {p | coordinateLift p ∉ deletedLift}

theorem mem_carvedCoordinates_iff (p : FiniteCoordinates) :
    p ∈ carvedCoordinates ↔ coordinateMap p ∉ interior closedDiskNeighborhood :=
  not_congr (coordinateLift_mem_deletedLift_iff p)

theorem carvedCoordinates_isClosed : IsClosed carvedCoordinates := by
  have he : carvedCoordinates = coordinateMap ⁻¹' (interior closedDiskNeighborhood)ᶜ := by
    ext p
    exact mem_carvedCoordinates_iff p
  rw [he]
  exact isOpen_interior.isClosed_compl.preimage coordinateMap_continuous

theorem carvedCoordinates_isCompact : IsCompact carvedCoordinates :=
  carvedCoordinates_isClosed.isCompact

instance carvedCoordinates_compactSpace : CompactSpace carvedCoordinates :=
  isCompact_iff_compactSpace.mp carvedCoordinates_isCompact

/-- The map into the actual compact complement, with its inherited topology. -/
def presentationMap (p : carvedCoordinates) : capComplement :=
  ⟨coordinateMap p.val, coordinateMap_mem_cap p.val,
    (mem_carvedCoordinates_iff p.val).mp p.property⟩

@[simp] theorem presentationMap_coe (p : carvedCoordinates) :
    (presentationMap p : Threefold.Space) = coordinateMap p.val := rfl

theorem presentationMap_continuous : Continuous presentationMap :=
  (coordinateMap_continuous.comp continuous_subtype_val).subtype_mk _

/-- Every point of the actual relative cusp region has a remaining finite native representative. -/
theorem presentationMap_surjective : Function.Surjective presentationMap := by
  rintro ⟨x, hx, hn⟩
  obtain ⟨p, rfl⟩ := coordinateMap_range.symm ▸ hx
  exact ⟨⟨p, (mem_carvedCoordinates_iff p).mpr hn⟩, rfl⟩

theorem presentationMap_isQuotientMap : IsQuotientMap presentationMap :=
  presentationMap_continuous.isClosedMap.isQuotientMap
    presentationMap_continuous presentationMap_surjective

end Wikipedia.HopfProblem.CuspComplement
