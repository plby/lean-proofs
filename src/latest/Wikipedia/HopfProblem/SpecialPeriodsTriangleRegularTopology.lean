import Wikipedia.HopfProblem.CoveringManifold
import Mathlib.GroupTheory.OrderOfElement

/-!
# The free locus of a properly discontinuous action

These general topological lemmas supply the regular-domain construction for
the actual triangle action.  The free locus is defined by its stabilizers,
proved invariant and open, and equipped with the restricted free action.
The covering and Hausdorff quotient conclusions follow from the given proper
discontinuity, rather than from an assumed quotient manifold.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Wikipedia.HopfProblem.FreeActionLocus

variable (G X : Type*) [Group G] [MulAction G X]

/-- Points with trivial stabilizer for the given action. -/
def locus : Set X := {x | ∀ g : G, g • x = x → g = 1}

/-- The actual subtype of points with trivial stabilizer. -/
abbrev Space := {x : X // x ∈ locus G X}

theorem mem_locus_iff_stabilizer_eq_bot (x : X) :
    x ∈ locus G X ↔ MulAction.stabilizer G x = ⊥ := by
  constructor
  · intro hx
    apply le_antisymm _ bot_le
    intro g hg
    exact hx g hg
  · intro hx g hg
    have hmem : g ∈ (⊥ : Subgroup G) := hx ▸ hg
    exact hmem

/-- Triviality of the stabilizer is preserved by every group element. -/
theorem smul_mem_locus (g : G) {x : X} (hx : x ∈ locus G X) :
    g • x ∈ locus G X := by
  intro h hh
  have he : g⁻¹ * h * g = 1 := hx _ (by
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun y => g⁻¹ • y) hh)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left,
    inv_mul_cancel, one_mul] using congrArg (fun k : G => g * k * g⁻¹) he

theorem smul_mem_locus_iff (g : G) (x : X) :
    g • x ∈ locus G X ↔ x ∈ locus G X := by
  refine ⟨fun hx => ?_, smul_mem_locus G X g⟩
  simpa only [inv_smul_smul] using smul_mem_locus G X g⁻¹ hx

instance mulAction : MulAction G (Space G X) where
  smul g x := ⟨g • x.val, smul_mem_locus G X g x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

@[simp] theorem smul_val (g : G) (x : Space G X) : (g • x).val = g • x.val := rfl

instance isCancelSMul : IsCancelSMul G (Space G X) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  exact x.property g (congrArg Subtype.val hx)

/-- The actual orbit quotient of the free locus. -/
abbrev OrbitSpace := Quotient (MulAction.orbitRel G (Space G X))

/-- Projection to actual free-locus orbits. -/
def project : Space G X → OrbitSpace G X := Quotient.mk _

theorem project_surjective : Function.Surjective (project G X) := Quotient.mk_surjective

theorem project_eq_iff_mem_orbit (x y : Space G X) :
    project G X x = project G X y ↔ x ∈ MulAction.orbit G y := Quotient.eq''

variable [TopologicalSpace X]

instance continuousConstSMul [ContinuousConstSMul G X] :
    ContinuousConstSMul G (Space G X) where
  continuous_const_smul g :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

/-- Proper discontinuity restricts to the invariant free subtype. -/
instance properlyDiscontinuousSMul [ProperlyDiscontinuousSMul G X] :
    ProperlyDiscontinuousSMul G (Space G X) where
  finite_disjoint_inter_image {K L} hK hL := by
    apply (finite_disjoint_inter_image (Γ := G)
      (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)).subset
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact ⟨y.val, ⟨x.val, ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩, ⟨y, hy, rfl⟩⟩

/-- Under proper discontinuity, every stabilizing element has finite order. -/
theorem isOfFinOrder_of_smul_eq [ProperlyDiscontinuousSMul G X]
    (g : G) (x : X) (hg : g • x = x) : IsOfFinOrder g := by
  let := (ProperlyDiscontinuousSMul.finite_stabilizer (Γ := G) x).fintype
  exact (MulAction.stabilizer G x).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g, hg⟩ : MulAction.stabilizer G x))

variable [T2Space X] [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X]

/-- A neighbourhood with no returning nonidentity translates contains only
points with trivial stabilizer.  This proves that the free locus is open. -/
theorem isOpen_locus : IsOpen (locus G X) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hU, hdis⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  apply mem_of_superset hU
  intro y hy g hgy
  exact hx g (hdis g ⟨y, ⟨y, hy, hgy⟩, hy⟩)

/-- The open set has exactly the previously defined free points. -/
def opens : TopologicalSpace.Opens X := ⟨locus G X, isOpen_locus G X⟩

instance locallyCompactSpace : LocallyCompactSpace (Space G X) :=
  (isOpen_locus G X).locallyCompactSpace

/-- The quotient is a covering by the original restricted group action. -/
theorem quotientCovering : IsQuotientCoveringMap (project G X) G :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

instance orbitSpace_t2 : T2Space (OrbitSpace G X) := inferInstance

instance orbitSpace_secondCountable [SecondCountableTopology X] :
    SecondCountableTopology (OrbitSpace G X) :=
  ContinuousConstSMul.secondCountableTopology

end Wikipedia.HopfProblem.FreeActionLocus
