import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryFrontier

/-!
# Literal toric lifts of the fixed closed normal neighborhood

The closed and strict normal disks are lifted through the original
two-chart toric parametrization into the actual cusp tube. Their images
under the original deck quotient and threefold inclusion are exactly the
already fixed closed neighborhood and its interior. Equality under that
map is precisely the unchanged correction-dependent lattice relation.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data

/-- The original toric tube used by the actual cusp filling. -/
abbrev NativeTube := ToricSpace.Tube (CuspQuotient.disc (CD).radius)

/-- The unchanged cusp quotient followed by its original threefold inclusion. -/
def nativeQuotientMap (x : NativeTube) : Threefold.Space :=
  CuspGeometry.inclusion (CuspQuotient.quotientMap (CD).correction (CD).radius x)

theorem nativeQuotientMap_continuous : Continuous nativeQuotientMap :=
  CuspGeometry.inclusion_continuous.comp
    (CuspQuotient.quotientMap_continuous (CD).correction (CD).radius)

/-- Equality in the actual threefold retains the entire original cusp deck action. -/
theorem nativeQuotientMap_eq_iff (x y : NativeTube) :
    nativeQuotientMap x = nativeQuotientMap y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v y = x := by
  let := ToricSpace.tubeAction (CD).correction (CuspQuotient.disc (CD).radius)
  constructor
  · intro h
    have hq : CuspQuotient.quotientMap (CD).correction (CD).radius x =
        CuspQuotient.quotientMap (CD).correction (CD).radius y :=
      CuspGeometry.inclusion_injective h
    have hor : x ∈ MulAction.orbit CuspQuotient.LatticeGroup y := Quotient.exact hq
    obtain ⟨g, hg⟩ := hor
    exact ⟨g.toAdd, hg⟩
  · rintro ⟨v, rfl⟩
    exact congrArg CuspGeometry.inclusion
      (CuspQuotient.quotientMap_translate (CD).correction (CD).radius v y)

/-- The literal lift of the already chosen closed normal disk product. -/
def closedNormalLift (p : ClosedNormalProduct) : NativeTube :=
  toTube (roundToSmall (closedProductIntoRound p))

@[simp] theorem closedNormalLift_coe (p : ClosedNormalProduct) :
    (closedNormalLift p : ToricSpace.Space) = fromProduct (p.1, p.2.val) := rfl

theorem closedNormalLift_continuous : Continuous closedNormalLift := by
  have hr : Continuous roundToSmall := continuous_subtype_val.subtype_mk _
  exact toTube_continuous.comp (hr.comp closedProductIntoRound_continuous)

@[simp] theorem nativeQuotientMap_closedNormalLift (p : ClosedNormalProduct) :
    nativeQuotientMap (closedNormalLift p) = closedProductMap p := rfl

theorem closedNormalLift_injective : Function.Injective closedNormalLift := by
  intro p q hpq
  exact closedProductMap_injective (congrArg nativeQuotientMap hpq)

/-- The compact, unsaturated lift in the original toric tube. -/
def closedNormalLifts : Set NativeTube := range closedNormalLift

theorem closedNormalLifts_isCompact : IsCompact closedNormalLifts :=
  isCompact_range closedNormalLift_continuous

/-- The strict normal disk inside the same unchanged compact lift. -/
def openNormalLifts : Set NativeTube :=
  closedNormalLift '' {p : ClosedNormalProduct | radiusSq p.2.val < closedRadius ^ 2}

theorem openNormalLifts_subset_closedNormalLifts : openNormalLifts ⊆ closedNormalLifts := by
  rintro _ ⟨p, _, rfl⟩
  exact mem_range_self p

/-- The closed lift maps onto the literal frozen compact normal neighborhood. -/
theorem nativeQuotientMap_image_closedNormalLifts :
    nativeQuotientMap '' closedNormalLifts = closedDiskNeighborhood := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨closedNormalLift p, mem_range_self p, rfl⟩

/-- The removed open lift maps onto the actual ambient interior, retaining its frontier. -/
theorem nativeQuotientMap_image_openNormalLifts :
    nativeQuotientMap '' openNormalLifts = interior closedDiskNeighborhood := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact (roundProductMap_mem_interior_closedDiskNeighborhood_iff
      (closedProductIntoRound p)).mpr hp
  · intro hx
    have hxN : x ∈ closedDiskNeighborhood := interior_subset hx
    obtain ⟨p, rfl⟩ := hxN
    refine ⟨closedNormalLift p, ⟨p, ?_, rfl⟩, rfl⟩
    exact (roundProductMap_mem_interior_closedDiskNeighborhood_iff
      (closedProductIntoRound p)).mp hx

end Wikipedia.HopfProblem.CuspComplement
