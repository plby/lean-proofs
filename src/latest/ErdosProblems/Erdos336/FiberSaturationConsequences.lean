import ErdosProblems.Erdos336.FiberSaturation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def subgroupFiber (K : AddSubgroup G) (A : Finset G) (a : G) : Finset G :=
  A ∩ (a +ᵥ addSubgroupFinset K)

noncomputable def subgroupHole (K : AddSubgroup G) (A : Finset G) (a : G) : Finset G :=
  (a +ᵥ addSubgroupFinset K) \ A

lemma card_subgroupFiber_add_card_subgroupHole
    (K : AddSubgroup G) (A : Finset G) (a : G) :
    (subgroupFiber K A a).card + (subgroupHole K A a).card =
      (addSubgroupFinset K).card := by
  unfold subgroupFiber subgroupHole
  rw [Finset.inter_comm]
  simpa using Finset.card_inter_add_card_sdiff
    (a +ᵥ addSubgroupFinset K) A

lemma subgroupHole_subset_saturation_holes
    (K : AddSubgroup G) (A : Finset G) {a : G} (ha : a ∈ A) :
    subgroupHole K A a ⊆ (A + addSubgroupFinset K) \ A := by
  intro x hx
  obtain ⟨hxU, hxnA⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨k, hk, hk_eq⟩ := Finset.mem_vadd_finset.mp hxU
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_add.mpr ⟨a, ha, k, hk, hk_eq⟩, hxnA⟩

/-- There cannot be two distinct occupied cosets whose fibres both have at
most half of a subgroup, if the total saturation defect is below one fibre. -/
theorem small_subgroup_fibers_same_coset
    (K : AddSubgroup G) (A : Finset G)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (hsmallA : 2 * (subgroupFiber K A a).card ≤ (addSubgroupFinset K).card)
    (hsmallB : 2 * (subgroupFiber K A b).card ≤ (addSubgroupFinset K).card) :
    b ∈ a +ᵥ addSubgroupFinset K := by
  by_contra hsame
  have hab : a - b ∉ K := by
    intro habK
    apply hsame
    apply Finset.mem_vadd_finset.mpr
    refine ⟨b - a, ?_, by simp [vadd_eq_add]⟩
    have hneg : b - a = -(a - b) := by abel
    rw [hneg]
    simpa using K.neg_mem habK
  have hdisU := vadd_subgroup_finsets_disjoint_of_sub_not_mem K hab
  have hdis : Disjoint (subgroupHole K A a) (subgroupHole K A b) :=
    hdisU.mono Finset.sdiff_subset Finset.sdiff_subset
  have hunion : subgroupHole K A a ∪ subgroupHole K A b ⊆
      (A + addSubgroupFinset K) \ A :=
    Finset.union_subset (subgroupHole_subset_saturation_holes K A ha)
      (subgroupHole_subset_saturation_holes K A hb)
  have hholes : (subgroupHole K A a).card + (subgroupHole K A b).card ≤
      (A + addSubgroupFinset K).card - A.card := by
    rw [← Finset.card_sdiff_of_subset]
    · rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_card hunion
    · intro x hx
      exact Finset.mem_add.mpr
        ⟨x, hx, 0, by simp, by simp⟩
  have hca := card_subgroupFiber_add_card_subgroupHole K A a
  have hcb := card_subgroupFiber_add_card_subgroupHole K A b
  omega

/-- Every point added when `2A` is subgroup-saturated lies in the doubled
coset of an occupied fibre containing at most half of the subgroup. -/
theorem missing_double_mem_small_fiber_coset
    (K : AddSubgroup G) (A : Finset G)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card)
    {z : G} (hz : z ∈ ((A + A) + addSubgroupFinset K) \ (A + A)) :
    ∃ a ∈ A, 2 * (subgroupFiber K A a).card ≤ (addSubgroupFinset K).card ∧
      z ∈ (a + a) +ᵥ addSubgroupFinset K := by
  obtain ⟨hzsat, hzn⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨w, hw, k, hk, hwk⟩ := Finset.mem_add.mp hzsat
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hw
  have hs := fiber_sum_full_or_same_small K A hdefect ha hb
  rcases hs with hfull | ⟨hbcos, hFeq, hsmall⟩
  · exfalso
    apply hzn
    apply Finset.add_subset_add Finset.inter_subset_left
      Finset.inter_subset_left
    rw [hfull]
    apply Finset.mem_vadd_finset.mpr
    refine ⟨k, hk, ?_⟩
    simp only [vadd_eq_add]
    rw [← hwk, ← hab]
  · refine ⟨a, ha, ?_, ?_⟩
    · simpa [subgroupFiber] using hsmall
    · obtain ⟨l, hl, hl_eq⟩ := Finset.mem_vadd_finset.mp hbcos
      apply Finset.mem_vadd_finset.mpr
      refine ⟨l + k, ?_, ?_⟩
      · simpa using K.add_mem (by simpa using hl) (by simpa using hk)
      · simp only [vadd_eq_add] at hl_eq hwk hab ⊢
        rw [← hwk, ← hab, ← hl_eq]
        abel

end Erdos336
