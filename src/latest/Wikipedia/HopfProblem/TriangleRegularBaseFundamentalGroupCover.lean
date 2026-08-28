import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupHomeomorph
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoverContractions
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoverOverlap

/-!
# The actual two-open cover of the canonical twice-punctured plane

The ambient slit domains become open subsets of the literal subtype
`ℂ \ {0, 1}`.  Explicit homeomorphisms to those ambient domains transfer
their proved contractions.  The overlap is the disjoint union of three
contractible open strips, each with its specified real basepoint.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def upperSlit : TopologicalSpace.Opens TwicePuncturedPlane :=
  ⟨{z | (z : ℂ) ∈ upperSlitPlane},
    upperSlitPlane_isOpen.preimage continuous_subtype_val⟩

def lowerSlit : TopologicalSpace.Opens TwicePuncturedPlane :=
  ⟨{z | (z : ℂ) ∈ lowerSlitPlane},
    lowerSlitPlane_isOpen.preimage continuous_subtype_val⟩

@[simp] theorem mem_upperSlit (z : TwicePuncturedPlane) :
    z ∈ upperSlit ↔ (z : ℂ) ∈ upperSlitPlane := Iff.rfl

@[simp] theorem mem_lowerSlit (z : TwicePuncturedPlane) :
    z ∈ lowerSlit ↔ (z : ℂ) ∈ lowerSlitPlane := Iff.rfl

theorem mem_upperSlit_or_lowerSlit (z : TwicePuncturedPlane) :
    z ∈ upperSlit ∨ z ∈ lowerSlit := by
  have hz : (z : ℂ) ∈ ({w : ℂ | w ≠ 0 ∧ w ≠ 1}) := z.property
  rwa [← slitPlanes_union] at hz

/-- The actual two open subsets cover the entire canonical base. -/
theorem upperSlit_sup_lowerSlit : upperSlit ⊔ lowerSlit = ⊤ := by
  ext z
  change ((z : ℂ) ∈ upperSlitPlane ∨ (z : ℂ) ∈ lowerSlitPlane) ↔ True
  exact iff_true_intro (mem_upperSlit_or_lowerSlit z)

theorem upperSlit_union_lowerSlit :
    (upperSlit : Set TwicePuncturedPlane) ∪ lowerSlit = univ :=
  eq_univ_of_forall mem_upperSlit_or_lowerSlit

/-- The upper member of the cover is the actual ambient slit domain. -/
def upperSlitHomeomorph : upperSlit ≃ₜ upperSlitPlane where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, upperSlitPlane_subset_punctured z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def lowerSlitHomeomorph : lowerSlit ≃ₜ lowerSlitPlane where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, lowerSlitPlane_subset_punctured z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance upperSlit_contractibleSpace : ContractibleSpace upperSlit :=
  upperSlitHomeomorph.contractibleSpace

instance lowerSlit_contractibleSpace : ContractibleSpace lowerSlit :=
  lowerSlitHomeomorph.contractibleSpace

theorem upperSlit_simplyConnectedSpace : SimplyConnectedSpace upperSlit := inferInstance

theorem lowerSlit_simplyConnectedSpace : SimplyConnectedSpace lowerSlit := inferInstance

/-- The three actual open pieces of the cover overlap. -/
def slitOverlapStrip (i : Fin 3) : TopologicalSpace.Opens TwicePuncturedPlane :=
  ⟨{z | (z : ℂ) ∈ overlapStrip i},
    (overlapStrip_isOpen i).preimage continuous_subtype_val⟩

@[simp] theorem mem_slitOverlapStrip (i : Fin 3) (z : TwicePuncturedPlane) :
    z ∈ slitOverlapStrip i ↔ (z : ℂ) ∈ overlapStrip i := Iff.rfl

def slitOverlapStripHomeomorph (i : Fin 3) : slitOverlapStrip i ≃ₜ overlapStrip i where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, upperSlitPlane_subset_punctured
    ((overlapStrip_subset_overlap i z.property).1)⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance slitOverlapStrip_contractibleSpace (i : Fin 3) :
    ContractibleSpace (slitOverlapStrip i) :=
  (slitOverlapStripHomeomorph i).contractibleSpace

theorem slitOverlapStrip_simplyConnectedSpace (i : Fin 3) :
    SimplyConnectedSpace (slitOverlapStrip i) := inferInstance

theorem slitOverlapStrip_isPathConnected (i : Fin 3) :
    IsPathConnected (slitOverlapStrip i : Set TwicePuncturedPlane) := by
  let : ContractibleSpace (slitOverlapStrip i : Set TwicePuncturedPlane) :=
    slitOverlapStrip_contractibleSpace i
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem slitOverlapStrip_subset_overlap (i : Fin 3) :
    (slitOverlapStrip i : Set TwicePuncturedPlane) ⊆
      (upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit :=
  fun _ hz => overlapStrip_subset_overlap i hz

/-- The points of real coordinate `-1`, `1/2`, and `2`, now in the actual base. -/
def slitOverlapStripPoint (i : Fin 3) : slitOverlapStrip i :=
  (slitOverlapStripHomeomorph i).symm (overlapStripPoint i)

@[simp] theorem slitOverlapStripPoint_coe (i : Fin 3) :
    ((slitOverlapStripPoint i).val : ℂ) = overlapStripBasepoint i := rfl

theorem slitOverlapStrip_pairwise_disjoint :
    Pairwise fun i j : Fin 3 => Disjoint
      (slitOverlapStrip i : Set TwicePuncturedPlane) (slitOverlapStrip j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact Set.disjoint_left.mp (overlapStrip_pairwise_disjoint hij) hi hj

/-- The overlap consists of exactly three disjoint nonempty contractible opens. -/
theorem slitOverlapStrip_iUnion :
    (⋃ i : Fin 3, (slitOverlapStrip i : Set TwicePuncturedPlane)) =
      (upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact slitOverlapStrip_subset_overlap i hi
  · intro hz
    have hc : (z : ℂ) ∈ (⋃ i : Fin 3, overlapStrip i) := by
      rw [overlapStrip_iUnion]
      exact hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact mem_iUnion.mpr ⟨i, hi⟩

/-- Two actual base points can be joined in the overlap precisely when
they belong to the same one of its three strips. -/
theorem slitOverlap_joinedIn_iff {z w : TwicePuncturedPlane} :
    JoinedIn ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) z w ↔
      ∃ i : Fin 3, z ∈ slitOverlapStrip i ∧ w ∈ slitOverlapStrip i := by
  constructor
  · intro h
    have hc : JoinedIn (((↑) : TwicePuncturedPlane → ℂ) ''
        ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit)) (z : ℂ) (w : ℂ) :=
      h.map continuous_subtype_val
    have hs : ((↑) : TwicePuncturedPlane → ℂ) ''
        ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) ⊆
          upperSlitPlane ∩ lowerSlitPlane := by
      rintro x ⟨y, hy, rfl⟩
      exact hy
    exact overlap_joinedIn_iff.mp (hc.mono hs)
  · rintro ⟨i, hz, hw⟩
    exact ((slitOverlapStrip_isPathConnected i).joinedIn z hz w hw).mono
      (slitOverlapStrip_subset_overlap i)

theorem slitOverlapStrip_pathComponentIn (i : Fin 3) {z : TwicePuncturedPlane}
    (hz : z ∈ slitOverlapStrip i) :
    pathComponentIn ((upperSlit : Set TwicePuncturedPlane) ∩ lowerSlit) z =
      (slitOverlapStrip i : Set TwicePuncturedPlane) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, hzj, hwj⟩ := slitOverlap_joinedIn_iff.mp hw
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.mp (slitOverlapStrip_pairwise_disjoint hne) hz hzj
    exact hij ▸ hwj
  · intro hw
    exact slitOverlap_joinedIn_iff.mpr ⟨i, hz, hw⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
