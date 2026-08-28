import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Restricting a quotient covering to an invariant subset

An invariant subset of the covering space is exactly the preimage of its
image in the quotient.  Consequently its restricted projection is still a
quotient covering, and its orbit quotient is homeomorphic to that image
with the inherited topology.  Closedness is needed only to conclude that
the image is closed; the restriction results hold for arbitrary invariant
subsets.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.InvariantSubsetQuotient

variable {M Q : Type*} {q : M → Q} {S : Set M}

/-- The projection onto the actual image, with its subspace topology. -/
def imageProject (q : M → Q) (S : Set M) (x : S) : q '' S :=
  ⟨q x, x, x.2, rfl⟩

@[simp] theorem imageProject_coe (x : S) :
    (imageProject q S x : Q) = q x := rfl

theorem imageProject_surjective : Function.Surjective (imageProject q S) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The standard restriction of an action to an invariant subset. -/
@[implicit_reducible]
def subsetAction (G : Type*) [Group G] [MulAction G M] (S : Set M)
    (hS : ∀ (g : G) (x : M), x ∈ S → g • x ∈ S) : MulAction G S where
  smul g x := ⟨g • x.1, hS g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp] theorem subsetAction_smul_coe (G : Type*) [Group G] [MulAction G M]
    (S : Set M) (hS : ∀ (g : G) (x : M), x ∈ S → g • x ∈ S)
    (g : G) (x : S) :
    letI := subsetAction G S hS
    ((g • x : S) : M) = g • (x : M) := rfl

variable [TopologicalSpace M] [TopologicalSpace Q]

theorem imageProject_continuous (hq : Continuous q) : Continuous (imageProject q S) :=
  (hq.comp continuous_subtype_val).subtype_mk _

variable {G : Type*} [Group G] [MulAction G M] [MulAction G S]
    (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M))

include hq hcompat in
theorem preimage_image_eq : q ⁻¹' (q '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hxy.symm
    have he : ((g • (⟨y, hy⟩ : S) : S) : M) = x := (hcompat g ⟨y, hy⟩).trans hg
    exact he ▸ (g • (⟨y, hy⟩ : S)).2
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- This homeomorphism changes only the proof of membership, not the point. -/
def preimageImageHomeomorph : S ≃ₜ q ⁻¹' (q '' S) :=
  Homeomorph.setCongr (preimage_image_eq hq hcompat).symm

@[simp] theorem preimageImageHomeomorph_coe (x : S) :
    (preimageImageHomeomorph hq hcompat x : M) = x := rfl

@[simp] theorem preimageImageHomeomorph_symm_coe (x : q ⁻¹' (q '' S)) :
    ((preimageImageHomeomorph hq hcompat).symm x : M) = x := rfl

include hq hcompat in
theorem imageProject_isCoveringMap : IsCoveringMap (imageProject q S) := by
  exact (hq.isCoveringMap.restrictPreimage (q '' S)).comp_homeomorph
    (preimageImageHomeomorph hq hcompat)

include hq hcompat in
theorem subtypeAction_continuousConstSMul : ContinuousConstSMul G S where
  continuous_const_smul g := by
    apply IsInducing.subtypeVal.continuous_iff.mpr
    simpa only [Function.comp_def, hcompat] using
      (hq.continuous_const_smul g).comp continuous_subtype_val

include hq hcompat in
theorem imageProject_eq_iff_mem_orbit {x y : S} :
    imageProject q S x = imageProject q S y ↔ x ∈ MulAction.orbit G y := by
  rw [Subtype.ext_iff]
  change q x = q y ↔ _
  rw [hq.apply_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext ((hcompat g y).trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (hcompat g y).symm.trans (congrArg Subtype.val hg)⟩

include hq hcompat in
theorem imageProject_isQuotientCoveringMap :
    IsQuotientCoveringMap (imageProject q S) G where
  __ := (imageProject_isCoveringMap hq hcompat).isQuotientMap imageProject_surjective
  __ := subtypeAction_continuousConstSMul hq hcompat
  apply_eq_iff_mem_orbit := imageProject_eq_iff_mem_orbit hq hcompat
  disjoint x := by
    obtain ⟨U, hU, hdisj⟩ := hq.disjoint (x : M)
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU,
      fun g hg => ?_⟩
    obtain ⟨y, ⟨z, hz, hzy⟩, hy⟩ := hg
    apply hdisj g
    refine ⟨(y : M), ⟨(z : M), hz, ?_⟩, hy⟩
    exact (hcompat g z).symm.trans (congrArg Subtype.val hzy)

include hq hcompat in
theorem imageProject_isOpenQuotientMap : IsOpenQuotientMap (imageProject q S) :=
  (imageProject_isQuotientCoveringMap hq hcompat).isOpenQuotientMap

/-- The orbit quotient and the literal image have the same underlying points. -/
def quotientEquiv : Quotient (MulAction.orbitRel G S) ≃ q '' S :=
  (Quotient.congrRight (fun _ _ => (imageProject_eq_iff_mem_orbit hq hcompat).symm)).trans
    (Setoid.quotientKerEquivOfSurjective (imageProject q S) imageProject_surjective)

@[simp] theorem quotientEquiv_mk (x : S) :
    quotientEquiv hq hcompat (Quotient.mk (MulAction.orbitRel G S) x) =
      imageProject q S x := rfl

@[simp] theorem quotientEquiv_symm_imageProject (x : S) :
    (quotientEquiv hq hcompat).symm (imageProject q S x) =
      Quotient.mk (MulAction.orbitRel G S) x := by
  rw [← quotientEquiv_mk hq hcompat x, Equiv.symm_apply_apply]

/-- The orbit quotient is homeomorphic to the image with its inherited topology. -/
def quotientHomeomorph : Quotient (MulAction.orbitRel G S) ≃ₜ q '' S where
  toEquiv := quotientEquiv hq hcompat
  continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr
    (imageProject_continuous hq.continuous)
  continuous_invFun := by
    apply (imageProject_isQuotientCoveringMap hq hcompat).toIsQuotientMap.continuous_iff.mpr
    change Continuous ((quotientEquiv hq hcompat).symm ∘ imageProject q S)
    have he : (quotientEquiv hq hcompat).symm ∘ imageProject q S =
        Quotient.mk (MulAction.orbitRel G S) := by
      funext x
      exact quotientEquiv_symm_imageProject hq hcompat x
    rw [he]
    exact continuous_quotient_mk'

@[simp] theorem quotientHomeomorph_mk (x : S) :
    quotientHomeomorph hq hcompat (Quotient.mk (MulAction.orbitRel G S) x) =
      imageProject q S x := rfl

@[simp] theorem quotientHomeomorph_mk_coe (x : S) :
    (quotientHomeomorph hq hcompat (Quotient.mk (MulAction.orbitRel G S) x) : Q) =
      q x := rfl

@[simp] theorem quotientHomeomorph_symm_imageProject (x : S) :
    (quotientHomeomorph hq hcompat).symm (imageProject q S x) =
      Quotient.mk (MulAction.orbitRel G S) x :=
  quotientEquiv_symm_imageProject hq hcompat x

include hq hcompat in
theorem orbitProject_isQuotientCoveringMap :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G S)) G := by
  have h := (imageProject_isQuotientCoveringMap hq hcompat).homeomorph_comp
    (quotientHomeomorph hq hcompat).symm
  simpa only [Function.comp_def, quotientHomeomorph_symm_imageProject] using h

include hq hcompat in
theorem isClosed_image (hS : IsClosed S) : IsClosed (q '' S) := by
  apply hq.isCoinducing.isClosed_preimage.mp
  rwa [preimage_image_eq hq hcompat]

include hq hcompat in
theorem isOpen_image (hS : IsOpen S) : IsOpen (q '' S) := by
  apply hq.isCoinducing.isOpen_preimage.mp
  rwa [preimage_image_eq hq hcompat]

end Wikipedia.HopfProblem.InvariantSubsetQuotient

namespace Wikipedia.HopfProblem.CoveringOrthant

variable {G M Q H : Type*} [Group G] [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M)

/-- A local chart on the actual quotient obtained by lifting to the covering
space and then applying a given source chart.  The model is purely topological. -/
def localChart : OpenPartialHomeomorph Q H :=
  (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).trans e

theorem self_mem_localChart_source (ha : a ∈ e.source) :
    q a ∈ (localChart hq e a).source := by
  change q a ∈ (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).source ∧
    hq.isCoveringMap.isLocalHomeomorph.localInverseAt a (q a) ∈ e.source
  exact ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source,
    by simpa only [IsLocalHomeomorph.localInverseAt_apply_self] using ha⟩

@[simp] theorem localChart_apply_project : localChart hq e a (q a) = e a := by
  simp only [localChart, OpenPartialHomeomorph.trans_apply,
    IsLocalHomeomorph.localInverseAt_apply_self]

/-- The inverse chart is the original inverse chart followed by the projection. -/
theorem localChart_symm :
    ((localChart hq e a).symm : H → Q) = q ∘ e.symm := by
  simp only [localChart, OpenPartialHomeomorph.coe_trans_symm,
    IsLocalHomeomorph.localInverseAt_symm]

@[simp] theorem localChart_symm_apply (z : H) :
    (localChart hq e a).symm z = q (e.symm z) := by
  rw [localChart_symm, Function.comp_apply]

theorem localChart_target_subset : (localChart hq e a).target ⊆ e.target :=
  fun _ hz => hz.1

/-- Any formula for a function in the source coordinates remains valid in
the corresponding quotient coordinates. -/
theorem localChart_coordinate_identity {R : Type*} (f : Q → R) (F : H → R)
    (he : ∀ x ∈ e.source, f (q x) = F (e x)) :
    ∀ z ∈ (localChart hq e a).target, f ((localChart hq e a).symm z) = F z := by
  intro z hz
  have hze := localChart_target_subset hq e a hz
  rw [localChart_symm_apply, he (e.symm z) (e.map_target hze), e.right_inv hze]

theorem localChart_coordinate_identity_on_source {R : Type*} (f : Q → R) (F : H → R)
    (he : ∀ x ∈ e.source, f (q x) = F (e x)) :
    ∀ y ∈ (localChart hq e a).source, f y = F (localChart hq e a y) := by
  intro y hy
  have h := localChart_coordinate_identity hq e a f F he
    (localChart hq e a y) ((localChart hq e a).map_source hy)
  rwa [(localChart hq e a).left_inv hy] at h

end Wikipedia.HopfProblem.CoveringOrthant
