import Mathlib
import ErdosProblems.Erdos336.DenseCosetAddition

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma vadd_subgroup_finsets_disjoint_of_sub_not_mem
    (K : AddSubgroup G) {a b : G} (hab : a - b ∉ K) :
    Disjoint (a +ᵥ addSubgroupFinset K) (b +ᵥ addSubgroupFinset K) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨u, hu, hu_eq⟩ := Finset.mem_vadd_finset.mp hxa
  obtain ⟨v, hv, hv_eq⟩ := Finset.mem_vadd_finset.mp hxb
  apply hab
  have huK : u ∈ K := by simpa using hu
  have hvK : v ∈ K := by simpa using hv
  have ha : a = x - u := by
    simp only [vadd_eq_add] at hu_eq
    rw [← hu_eq]
    abel
  have hb : b = x - v := by
    simp only [vadd_eq_add] at hv_eq
    rw [← hv_eq]
    abel
  rw [ha, hb]
  convert K.sub_mem hvK huK using 1 <;> abel

lemma vadd_subgroup_finsets_eq_of_mem
    (K : AddSubgroup G) {a b : G}
    (hb : b ∈ a +ᵥ addSubgroupFinset K) :
    b +ᵥ addSubgroupFinset K = a +ᵥ addSubgroupFinset K := by
  obtain ⟨k, hk, hk_eq⟩ := Finset.mem_vadd_finset.mp hb
  have hkK : k ∈ K := by simpa using hk
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨l, hl, hl_eq⟩ := Finset.mem_vadd_finset.mp hx
    apply Finset.mem_vadd_finset.mpr
    refine ⟨k + l, ?_, ?_⟩
    · simpa using K.add_mem hkK (by simpa using hl)
    · simp only [vadd_eq_add] at hk_eq hl_eq ⊢
      rw [← hl_eq, ← hk_eq]
      abel
  · intro x hx
    obtain ⟨l, hl, hl_eq⟩ := Finset.mem_vadd_finset.mp hx
    apply Finset.mem_vadd_finset.mpr
    refine ⟨l - k, ?_, ?_⟩
    · simpa using K.sub_mem (by simpa using hl) hkK
    · simp only [vadd_eq_add] at hk_eq hl_eq ⊢
      rw [← hl_eq, ← hk_eq]
      abel

/-- If `A` misses fewer than one subgroup fibre inside its `K`-saturation,
then any two occupied fibres add to a full fibre, except possibly the self-sum
of one sparse fibre. -/
theorem fiber_sum_full_or_same_small
    (K : AddSubgroup G) (A : Finset G)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    let H := addSubgroupFinset K
    let F := fun x : G => A ∩ (x +ᵥ H)
    F a + F b = (a + b) +ᵥ H ∨
      (b ∈ a +ᵥ H ∧ F a = F b ∧ 2 * (F a).card ≤ H.card) := by
  let H := addSubgroupFinset K
  let F := fun x : G => A ∩ (x +ᵥ H)
  let E := (A + H) \ A
  let Hole := fun x : G => (x +ᵥ H) \ A
  change F a + F b = (a + b) +ᵥ H ∨
    (b ∈ a +ᵥ H ∧ F a = F b ∧ 2 * (F a).card ≤ H.card)
  have hdefectH : (A + H).card - A.card < H.card := by
    simpa [H] using hdefect
  have hzero : 0 ∈ H := by simp [H]
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hEcard : E.card = (A + H).card - A.card :=
    Finset.card_sdiff_of_subset hAsub
  have hHoleSub (x : G) (hx : x ∈ A) : Hole x ⊆ E := by
    intro y hy
    have hyU := (Finset.mem_sdiff.mp hy).1
    have hynA := (Finset.mem_sdiff.mp hy).2
    obtain ⟨k, hk, hk_eq⟩ := Finset.mem_vadd_finset.mp hyU
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_add.mpr ⟨x, hx, k, hk, hk_eq⟩, hynA⟩
  have hcard (x : G) : (F x).card + (Hole x).card = H.card := by
    dsimp [F, Hole]
    rw [Finset.inter_comm]
    simpa using Finset.card_inter_add_card_sdiff (x +ᵥ H) A
  by_cases hsame : b ∈ a +ᵥ H
  · have hcoseteq : b +ᵥ H = a +ᵥ H := by
      simpa [H] using vadd_subgroup_finsets_eq_of_mem K hsame
    have hFeq : F a = F b := by simp only [F, hcoseteq]
    by_cases hlarge : H.card < 2 * (F a).card
    · left
      rw [← hFeq]
      exact add_eq_vadd_of_coset_support_of_card_lt_add K
        (A := F a) (B := F a) (a := a) (b := b)
        (by simpa [F, H] using (Finset.inter_subset_right : F a ⊆ a +ᵥ H))
        (by
          intro x hx
          have hx' : x ∈ a +ᵥ H := Finset.inter_subset_right hx
          rw [← hcoseteq] at hx'
          simpa [H] using hx')
        (by simpa [H, two_mul] using hlarge)
    · right
      exact ⟨hsame, hFeq, by omega⟩
  · left
    have hab : a - b ∉ K := by
      intro habK
      apply hsame
      apply Finset.mem_vadd_finset.mpr
      refine ⟨b - a, ?_, by simp [vadd_eq_add]⟩
      have hneg : b - a = -(a - b) := by abel
      rw [hneg]
      simpa [H] using K.neg_mem habK
    have hdisU := vadd_subgroup_finsets_disjoint_of_sub_not_mem K hab
    have hdisHole : Disjoint (Hole a) (Hole b) :=
      hdisU.mono Finset.sdiff_subset Finset.sdiff_subset
    have hunionSub : Hole a ∪ Hole b ⊆ E :=
      Finset.union_subset (hHoleSub a ha) (hHoleSub b hb)
    have hholes : (Hole a).card + (Hole b).card ≤ E.card := by
      rw [← Finset.card_union_of_disjoint hdisHole]
      exact Finset.card_le_card hunionSub
    have hdefect' : E.card < H.card := by
      rw [hEcard]
      simpa [E] using hdefectH
    have hlarge : H.card < (F a).card + (F b).card := by
      have hca := hcard a
      have hcb := hcard b
      omega
    apply add_eq_vadd_of_coset_support_of_card_lt_add K
    · exact Finset.inter_subset_right
    · exact Finset.inter_subset_right
    · simpa [H] using hlarge

end Erdos336
