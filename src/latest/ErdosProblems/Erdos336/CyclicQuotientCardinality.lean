import Mathlib
import ErdosProblems.Erdos336.DenseCosetAddition

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G Q : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup Q] [Fintype Q] [DecidableEq Q]

noncomputable def homPreimageFinset (f : G →+ Q) (T : Finset Q) : Finset G :=
  Finset.univ.filter fun x => f x ∈ T

lemma hom_fiber_finset_eq_vadd_ker
    (f : G →+ Q) (hf : Function.Surjective f) (y : Q) :
    (Finset.univ.filter fun x => f x = y) =
      (hf y).choose +ᵥ addSubgroupFinset f.ker := by
  let a := (hf y).choose
  have ha : f a = y := (hf y).choose_spec
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_vadd_finset, mem_addSubgroupFinset]
  constructor
  · intro hx
    refine ⟨x - a, ?_, ?_⟩
    · change f (x - a) = 0
      rw [f.map_sub, hx, ha, sub_self]
    · simp only [vadd_eq_add]
      abel
  · rintro ⟨k, hk, rfl⟩
    change f (a + k) = y
    rw [f.map_add, ha, show f k = 0 from hk, add_zero]

lemma card_hom_fiber_finset_eq_card_ker
    (f : G →+ Q) (hf : Function.Surjective f) (y : Q) :
    (Finset.univ.filter fun x => f x = y).card =
      (addSubgroupFinset f.ker).card := by
  rw [hom_fiber_finset_eq_vadd_ker f hf y, Finset.card_vadd_finset]

/-- A surjective homomorphism has constant finite fibres, so the preimage of a
finite target set has cardinality target-size times kernel-size. -/
theorem card_homPreimageFinset
    (f : G →+ Q) (hf : Function.Surjective f) (T : Finset Q) :
    (homPreimageFinset f T).card = T.card * (addSubgroupFinset f.ker).card := by
  let P := homPreimageFinset f T
  have hmap : (P : Set G).MapsTo f T := by
    intro x hx
    simpa [P, homPreimageFinset] using hx
  calc
    P.card = ∑ y ∈ T, (P.filter fun x => f x = y).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ _y ∈ T, (addSubgroupFinset f.ker).card := by
      apply Finset.sum_congr rfl
      intro y hy
      have heq : P.filter (fun x => f x = y) =
          Finset.univ.filter (fun x => f x = y) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hx => hx.2
        · intro hxy
          refine ⟨?_, hxy⟩
          simpa [P, homPreimageFinset, hxy] using hy
      rw [heq, card_hom_fiber_finset_eq_card_ker f hf y]
    _ = T.card * (addSubgroupFinset f.ker).card := by
      rw [Finset.sum_const_nat]
      intro y hy
      rfl

/-- Saturation by the kernel is exactly the preimage of the finite homomorphic
image, with exact cardinality `|image|*|kernel|`. -/
theorem card_add_ker_eq_card_image_mul
    (f : G →+ Q) (hf : Function.Surjective f) (A : Finset G) :
    (A + addSubgroupFinset f.ker).card =
      (A.image f).card * (addSubgroupFinset f.ker).card := by
  have heq : A + addSubgroupFinset f.ker =
      homPreimageFinset f (A.image f) := by
    ext x
    simp only [Finset.mem_add, mem_addSubgroupFinset, homPreimageFinset,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      refine ⟨a, ha, ?_⟩
      rw [f.map_add, show f k = 0 from hk, add_zero]
    · rintro ⟨a, ha, hfa⟩
      refine ⟨a, ha, x - a, ?_, by abel⟩
      change f (x - a) = 0
      rw [f.map_sub, hfa, sub_self]
  rw [heq, card_homPreimageFinset f hf]

section CyclicQuotient

variable [IsAddCyclic G]

noncomputable def cyclicQuotientHom (K : AddSubgroup G) :
    G →+ ZMod (Nat.card (G ⧸ K)) := by
  let hcyc : IsAddCyclic (G ⧸ K) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' K)
      (QuotientAddGroup.mk'_surjective K)
  exact (zmodAddCyclicAddEquiv hcyc).symm.toAddMonoidHom.comp
    (QuotientAddGroup.mk' K)

lemma cyclicQuotientHom_surjective (K : AddSubgroup G) :
    Function.Surjective (cyclicQuotientHom K) := by
  let hcyc : IsAddCyclic (G ⧸ K) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' K)
      (QuotientAddGroup.mk'_surjective K)
  let e := zmodAddCyclicAddEquiv hcyc
  intro z
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective K (e z)
  refine ⟨x, ?_⟩
  change e.symm (QuotientAddGroup.mk' K x) = z
  rw [hx, e.symm_apply_apply]

@[simp] lemma cyclicQuotientHom_ker (K : AddSubgroup G) :
    (cyclicQuotientHom K).ker = K := by
  ext x
  change cyclicQuotientHom K x = 0 ↔ x ∈ K
  let hcyc : IsAddCyclic (G ⧸ K) :=
    isAddCyclic_of_surjective (QuotientAddGroup.mk' K)
      (QuotientAddGroup.mk'_surjective K)
  let e := zmodAddCyclicAddEquiv hcyc
  change e.symm (QuotientAddGroup.mk' K x) = 0 ↔ x ∈ K
  constructor
  · intro hx
    have := congrArg e hx
    simpa using (QuotientAddGroup.eq_zero_iff x).mp (by simpa using this)
  · intro hx
    have hq : QuotientAddGroup.mk' K x = 0 :=
      (QuotientAddGroup.eq_zero_iff x).mpr hx
    rw [hq, map_zero]

/-- Every subgroup quotient of a finite cyclic group is represented by an
explicit surjection to a `ZMod`, and saturation cardinality is image-size
times subgroup-size. -/
theorem card_add_subgroup_eq_cyclicQuotient_image_mul
    (K : AddSubgroup G) (A : Finset G) :
    (A + addSubgroupFinset K).card =
      (A.image (cyclicQuotientHom K)).card * (addSubgroupFinset K).card := by
  letI : NeZero (Nat.card (G ⧸ K)) :=
    ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  have h := card_add_ker_eq_card_image_mul (cyclicQuotientHom K)
    (cyclicQuotientHom_surjective K) A
  simpa using h

end CyclicQuotient

end Erdos336
