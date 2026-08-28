import Wikipedia.HopfProblem.CuspHoneycombHexagonGluing
import Mathlib.Topology.LocallyFinite

/-!
# Gluing homeomorphisms of locally finite closed covers

The disjoint union of a locally finite closed cover is a quotient map
onto the original space. Consequently compatible cell homeomorphisms
with exactly the same point-identifications glue to a homeomorphism of
the original spaces. No replacement quotient topology is assigned to
either space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombClosedCover

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal projection from the disjoint union of a cover. -/
def projection (A : ι → Set X) (p : Σ i, A i) : X := p.2.1

theorem projection_continuous (A : ι → Set X) : Continuous (projection A) :=
  continuous_sigma_iff.mpr fun _ => continuous_subtype_val

omit [TopologicalSpace X] in
theorem projection_surjective {A : ι → Set X} (hcover : ⋃ i, A i = univ) :
    Function.Surjective (projection A) := by
  intro x
  have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ⟨⟨i, x, hi⟩, rfl⟩

/-- Local finiteness makes the original closed-cover projection closed. -/
theorem projection_isClosedMap {A : ι → Set X} (hclosed : ∀ i, IsClosed (A i))
    (hloc : LocallyFinite A) : IsClosedMap (projection A) := by
  intro S hS
  let F : ι → Set X := fun i => (Subtype.val : A i → X) ''
    ((fun x : A i => Sigma.mk i x) ⁻¹' S)
  have hFclosed (i : ι) : IsClosed (F i) :=
    (hclosed i).isClosedMap_subtype_val _ (hS.preimage continuous_sigmaMk)
  have hFsub (i : ι) : F i ⊆ A i := by
    rintro x ⟨a, _, rfl⟩
    exact a.2
  have heq : projection A '' S = ⋃ i, F i := by
    ext x
    constructor
    · rintro ⟨⟨i, a⟩, ha, rfl⟩
      exact mem_iUnion.mpr ⟨i, a, ha, rfl⟩
    · intro hx
      obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.mp hx
      exact ⟨⟨i, a⟩, ha, rfl⟩
  rw [heq]
  exact (hloc.subset hFsub).isClosed_iUnion hFclosed

theorem projection_isQuotientMap {A : ι → Set X}
    (hcover : ⋃ i, A i = univ) (hclosed : ∀ i, IsClosed (A i))
    (hloc : LocallyFinite A) : IsQuotientMap (projection A) :=
  (projection_isClosedMap hclosed hloc).isQuotientMap (projection_continuous A)
    (projection_surjective hcover)

section CommonFibres

open CuspHoneycombHexagon.CommonFibres

variable {Z : Type*} [TopologicalSpace Z] (f : Z → X) (g : Z → Y)
variable (hf : IsQuotientMap f) (hg : IsQuotientMap g)
variable (hfg : ∀ a b, f a = f b ↔ g a = g b)

/-- The common-fibre construction for arbitrary quotient maps, without
compactness assumptions on their common domain. -/
def quotientHomeomorph : X ≃ₜ Y where
  toFun := descend f g hf.surjective
  invFun := descend g f hg.surjective
  left_inv x := by
    obtain ⟨a, rfl⟩ := hf.surjective x
    rw [descend_apply f g hf.surjective (fun a b => (hfg a b).mp),
      descend_apply g f hg.surjective (fun a b => (hfg a b).mpr)]
  right_inv y := by
    obtain ⟨a, rfl⟩ := hg.surjective y
    rw [descend_apply g f hg.surjective (fun a b => (hfg a b).mpr),
      descend_apply f g hf.surjective (fun a b => (hfg a b).mp)]
  continuous_toFun := descend_continuous f g hf.surjective hf hg.continuous
    (fun a b => (hfg a b).mp)
  continuous_invFun := descend_continuous g f hg.surjective hg hf.continuous
    (fun a b => (hfg a b).mpr)

theorem quotientHomeomorph_apply (a : Z) : quotientHomeomorph f g hf hg hfg (f a) = g a :=
  descend_apply f g hf.surjective (fun a b => (hfg a b).mp) a

end CommonFibres

variable (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i)

/-- The componentwise homeomorphism of the disjoint unions. -/
def sigmaHomeomorph : (Σ i, A i) ≃ₜ (Σ i, B i) where
  toFun p := ⟨p.1, e p.1 p.2⟩
  invFun p := ⟨p.1, (e p.1).symm p.2⟩
  left_inv := by rintro ⟨i, a⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp
  continuous_toFun := continuous_sigma_iff.mpr fun i =>
    continuous_sigmaMk.comp (e i).continuous
  continuous_invFun := continuous_sigma_iff.mpr fun i =>
    continuous_sigmaMk.comp (e i).symm.continuous

variable (hAcov : ⋃ i, A i = univ) (hAcl : ∀ i, IsClosed (A i))
variable (hAloc : LocallyFinite A)
variable (hBcov : ⋃ i, B i = univ) (hBcl : ∀ i, IsClosed (B i))
variable (hBloc : LocallyFinite B)
variable (hglue : ∀ i j (x : A i) (y : A j),
  (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y))

/-- Exact cell identifications and the two original locally finite closed
covers produce a genuine global homeomorphism. -/
def homeomorph : X ≃ₜ Y :=
  quotientHomeomorph (projection A) (projection B ∘ sigmaHomeomorph A B e)
    (projection_isQuotientMap hAcov hAcl hAloc)
    ((projection_isQuotientMap hBcov hBcl hBloc).comp
      (sigmaHomeomorph A B e).isQuotientMap)
    (fun a b => hglue a.1 b.1 a.2 b.2)

/-- The global homeomorphism has exactly the prescribed map on every
closed cell, including all of its boundary points. -/
theorem homeomorph_apply (i : ι) (x : A i) :
    homeomorph A B e hAcov hAcl hAloc hBcov hBcl hBloc hglue (x : X) = (e i x : Y) :=
  quotientHomeomorph_apply _ _ _ _ _ (⟨i, x⟩ : Σ i, A i)

end Wikipedia.HopfProblem.CuspHoneycombClosedCover
