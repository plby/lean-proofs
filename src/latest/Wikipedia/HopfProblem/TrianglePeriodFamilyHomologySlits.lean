import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCover
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridians
import Mathlib.Topology.Homotopy.Lifting

/-!
# The actual slit cover of the regular triangle base

The proved normalized coordinate identifies the regular quotient with the
twice-punctured plane. Pulling back the actual upper and lower slit domains
gives two contractible open sets. Their overlap has the same three
contractible open components. These are subsets of the actual quotient,
not an assigned graph or a replacement base space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle

/-- Pull an actual open subset of the normalized plane back to the regular quotient. -/
def regularOpen (U : TopologicalSpace.Opens TwicePuncturedPlane) :
    TopologicalSpace.Opens TriangleRegularQuotient :=
  ⟨triangleRegularPlaneHomeomorph ⁻¹' (U : Set TwicePuncturedPlane),
    U.isOpen.preimage triangleRegularPlaneHomeomorph.continuous⟩

@[simp] theorem mem_regularOpen (U : TopologicalSpace.Opens TwicePuncturedPlane)
    (x : TriangleRegularQuotient) :
    x ∈ regularOpen U ↔ triangleRegularPlaneHomeomorph x ∈ U := Iff.rfl

/-- The restriction of the constructed coordinate homeomorphism to this actual open set. -/
def regularOpenHomeomorph (U : TopologicalSpace.Opens TwicePuncturedPlane) :
    regularOpen U ≃ₜ U :=
  triangleRegularPlaneHomeomorph.subtype (fun _ => Iff.rfl)

@[simp] theorem regularOpenHomeomorph_coe
    (U : TopologicalSpace.Opens TwicePuncturedPlane) (x : regularOpen U) :
    (regularOpenHomeomorph U x : TwicePuncturedPlane) =
      triangleRegularPlaneHomeomorph x.val := rfl

@[simp] theorem regularOpenHomeomorph_symm_coe
    (U : TopologicalSpace.Opens TwicePuncturedPlane) (x : U) :
    ((regularOpenHomeomorph U).symm x : TriangleRegularQuotient) =
      triangleRegularPlaneHomeomorph.symm x.val := rfl

theorem regularOpen_locallyPathConnectedSpace
    (U : TopologicalSpace.Opens TwicePuncturedPlane) :
    LocallyPathConnectedSpace (regularOpen U) := by
  let := twicePuncturedPlaneDomain.isOpen.locallyPathConnectedSpace
  let := U.isOpen.locallyPathConnectedSpace
  exact (regularOpenHomeomorph U).isOpenEmbedding.locallyPathConnectedSpace

/-- The upper slit, as an open subset of the actual regular quotient. -/
abbrev upperBase := regularOpen upperSlit

/-- The lower slit, as an open subset of the actual regular quotient. -/
abbrev lowerBase := regularOpen lowerSlit

/-- The three actual components of the overlap. -/
abbrev overlapBase (i : Fin 3) := regularOpen (slitOverlapStrip i)

instance upperBase_contractibleSpace : ContractibleSpace upperBase :=
  (regularOpenHomeomorph upperSlit).contractibleSpace

instance lowerBase_contractibleSpace : ContractibleSpace lowerBase :=
  (regularOpenHomeomorph lowerSlit).contractibleSpace

instance overlapBase_contractibleSpace (i : Fin 3) : ContractibleSpace (overlapBase i) :=
  (regularOpenHomeomorph (slitOverlapStrip i)).contractibleSpace

instance upperBase_locallyPathConnectedSpace : LocallyPathConnectedSpace upperBase :=
  regularOpen_locallyPathConnectedSpace upperSlit

instance lowerBase_locallyPathConnectedSpace : LocallyPathConnectedSpace lowerBase :=
  regularOpen_locallyPathConnectedSpace lowerSlit

instance overlapBase_locallyPathConnectedSpace (i : Fin 3) :
    LocallyPathConnectedSpace (overlapBase i) :=
  regularOpen_locallyPathConnectedSpace (slitOverlapStrip i)

/-- The two actual slit opens cover the whole regular quotient. -/
theorem upperBase_union_lowerBase :
    (upperBase : Set TriangleRegularQuotient) ∪ lowerBase = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_upperSlit_or_lowerSlit (triangleRegularPlaneHomeomorph x)

theorem overlapBase_subset (i : Fin 3) :
    (overlapBase i : Set TriangleRegularQuotient) ⊆
      (upperBase : Set TriangleRegularQuotient) ∩ lowerBase :=
  fun _ hx => slitOverlapStrip_subset_overlap i hx

theorem overlapBase_pairwise_disjoint :
    Pairwise fun i j : Fin 3 => Disjoint
      (overlapBase i : Set TriangleRegularQuotient) (overlapBase j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp (slitOverlapStrip_pairwise_disjoint hij) hi hj

/-- No components of the actual intersection are omitted by the three strips. -/
theorem overlapBase_iUnion :
    (⋃ i : Fin 3, (overlapBase i : Set TriangleRegularQuotient)) =
      (upperBase : Set TriangleRegularQuotient) ∩ lowerBase := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact overlapBase_subset i hi
  · intro hx
    have hh : triangleRegularPlaneHomeomorph x ∈
        ⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane) := by
      rw [slitOverlapStrip_iUnion]
      exact hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- A specified point in each actual overlap component. -/
def overlapBasePoint (i : Fin 3) : overlapBase i :=
  (regularOpenHomeomorph (slitOverlapStrip i)).symm (slitOverlapStripPoint i)

/-- The common basepoint of normalized coordinate `1/2`. -/
def slitBasepoint : TriangleRegularQuotient :=
  triangleRegularPlaneHomeomorph.symm meridianBasepoint

@[simp] theorem slitBasepoint_coordinate :
    triangleRegularPlaneHomeomorph slitBasepoint = meridianBasepoint :=
  triangleRegularPlaneHomeomorph.apply_symm_apply meridianBasepoint

theorem slitBasepoint_mem_upper : slitBasepoint ∈ upperBase := by
  rw [mem_regularOpen, slitBasepoint_coordinate]
  change (1 / 2 : ℂ) ∈ upperSlitPlane
  norm_num [upperSlitPlane]

theorem slitBasepoint_mem_lower : slitBasepoint ∈ lowerBase := by
  rw [mem_regularOpen, slitBasepoint_coordinate]
  change (1 / 2 : ℂ) ∈ lowerSlitPlane
  norm_num [lowerSlitPlane]

/-- The common basepoint as a point of the upper slit. -/
def upperBasePoint : upperBase := ⟨slitBasepoint, slitBasepoint_mem_upper⟩

/-- The same point as a point of the lower slit. -/
def lowerBasePoint : lowerBase := ⟨slitBasepoint, slitBasepoint_mem_lower⟩

/-- An actual lift of the common basepoint through the proved regular covering. -/
abbrev SlitBaseLift := triangleRegularProject ⁻¹' ({slitBasepoint} : Set TriangleRegularQuotient)

theorem slitBaseLift_nonempty : Nonempty SlitBaseLift := by
  obtain ⟨b, hb⟩ := triangleRegularProject_covering.surjective slitBasepoint
  exact ⟨⟨b, hb⟩⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
