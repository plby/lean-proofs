import Mathlib
import ErdosProblems.Erdos336.KneserDenseCoset

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A finite pigeonhole principle inside an ambient finset. -/
lemma not_disjoint_of_card_add_gt_of_subset
    {A B U : Finset G} (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hcard : U.card < A.card + B.card) : ¬ Disjoint A B := by
  intro hdis
  have hunion : A ∪ B ⊆ U := Finset.union_subset hAU hBU
  have hle := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdis] at hle
  omega

/-- Exact additive version of the classical very-small-doubling structure
lemma: below `3/2`, a finite set is denser than `2/3` in one stabilizer
coset, its double is a full stabilizer coset, and its difference set is the
stabilizer itself. -/
theorem very_small_doubling_structure
    {A : Finset G} (hA : A.Nonempty)
    (hdbl : 2 * (A + A).card < 3 * A.card) :
    let H := (A + A).addStab
    (∃ a : G, A ⊆ a +ᵥ H) ∧
    (∃ s : G, A + A = s +ᵥ H) ∧
    2 * H.card < 3 * A.card ∧
    A - A = H := by
  let H := (A + A).addStab
  have hlt2 : (A + A).card < 2 * A.card := by omega
  obtain ⟨ha, _ha', hsum, hdense, _⟩ :=
    very_small_sum_is_one_stabilizer_coset hA hA hlt2 hdbl
  obtain ⟨a, ha⟩ := ha
  obtain ⟨s, hs⟩ := hsum
  have hdense' : 2 * H.card < 3 * A.card := by
    simpa [H] using hdense
  have hAA : (A + A).Nonempty := hA.add hA
  have hcoe : (H : Set G) =
      (AddAction.stabilizer G (↑(A + A) : Set G) : Set G) := by
    simpa [H] using (Finset.coe_addStab hAA)
  let K : AddSubgroup G := AddAction.stabilizer G (↑(A + A) : Set G)
  have hmemK {x : G} : x ∈ H ↔ x ∈ K := by
    change x ∈ (H : Set G) ↔ x ∈ (K : Set G)
    rw [hcoe]
  have hdiffsub : A - A ⊆ H := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    obtain ⟨u0, hu0, hu_eq⟩ := Finset.mem_vadd_finset.mp (ha hu)
    obtain ⟨v0, hv0, hv_eq⟩ := Finset.mem_vadd_finset.mp (ha hv)
    rw [← huv, ← hu_eq, ← hv_eq]
    apply hmemK.mpr
    have huK : u0 ∈ K := hmemK.mp hu0
    have hvK : v0 ∈ K := hmemK.mp hv0
    simpa [vadd_eq_add, add_sub_add_left_eq_sub] using K.sub_mem huK hvK
  have hHsub : H ⊆ A - A := by
    intro h hh
    let T : Finset G := h +ᵥ A
    have hTcard : T.card = A.card := by
      simpa [T] using Finset.card_vadd_finset h A
    have hAsub : A ⊆ a +ᵥ H := ha
    have hTsub : T ⊆ a +ᵥ H := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨y0, hy0, hy_eq⟩ := Finset.mem_vadd_finset.mp (ha hy)
      apply Finset.mem_vadd_finset.mpr
      refine ⟨h + y0, ?_, ?_⟩
      · apply hmemK.mpr
        exact K.add_mem (hmemK.mp hh) (hmemK.mp hy0)
      · simp only [vadd_eq_add] at hyx hy_eq ⊢
        rw [← hyx, ← hy_eq]
        abel
    have hUcard : (a +ᵥ H).card = H.card := Finset.card_vadd_finset _ _
    have hUlt : (a +ᵥ H).card < A.card + T.card := by
      rw [hUcard, hTcard]
      omega
    have hnondis : ¬ Disjoint A T :=
      not_disjoint_of_card_add_gt_of_subset hAsub hTsub hUlt
    rw [Finset.not_disjoint_iff] at hnondis
    obtain ⟨x, hxA, hxT⟩ := hnondis
    obtain ⟨y, hyA, hyx⟩ := Finset.mem_vadd_finset.mp hxT
    apply Finset.mem_sub.mpr
    refine ⟨x, hxA, y, hyA, ?_⟩
    simp only [vadd_eq_add] at hyx
    rw [← hyx]
    abel
  refine ⟨⟨a, ha⟩, ⟨s, hs⟩, hdense', ?_⟩
  exact Finset.Subset.antisymm hdiffsub hHsub

end Erdos336
