import ErdosProblems.Erdos336.FiberSaturationConsequences

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Saturating a double by `K` costs no more points than saturating the
original set, provided the original saturation has fewer than one fibre of
holes. This is the fibre-combinatorial core of Lev's saturation argument. -/
theorem double_saturation_defect_le
    (K : AddSubgroup G) (A : Finset G) (hA : A.Nonempty)
    (hdefect : (A + addSubgroupFinset K).card - A.card <
      (addSubgroupFinset K).card) :
    ((A + A) + addSubgroupFinset K).card - (A + A).card ≤
      (A + addSubgroupFinset K).card - A.card := by
  let H := addSubgroupFinset K
  let E := (A + H) \ A
  let M := ((A + A) + H) \ (A + A)
  have hzero : 0 ∈ H := by simp [H]
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have h2sub : A + A ⊆ (A + A) + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hEcard : E.card = (A + H).card - A.card :=
    Finset.card_sdiff_of_subset hAsub
  have hMcard : M.card = ((A + A) + H).card - (A + A).card :=
    Finset.card_sdiff_of_subset h2sub
  by_cases hMempty : M = ∅
  · have hMc : M.card = 0 := by simp [hMempty]
    calc
      ((A + A) + addSubgroupFinset K).card - (A + A).card = M.card := by
        simpa [H] using hMcard.symm
      _ = 0 := hMc
      _ ≤ (A + addSubgroupFinset K).card - A.card := Nat.zero_le _
  · obtain ⟨z0, hz0⟩ := Finset.nonempty_iff_ne_empty.mpr hMempty
    obtain ⟨a0, ha0, hsmall0, hz0cos⟩ :=
      missing_double_mem_small_fiber_coset K A hdefect (by simpa [M, H] using hz0)
    have hMsub : M ⊆ (a0 + a0) +ᵥ H := by
      intro z hz
      obtain ⟨a, ha, hsmall, hzcos⟩ :=
        missing_double_mem_small_fiber_coset K A hdefect (by simpa [M, H] using hz)
      have hacos : a ∈ a0 +ᵥ H := by
        exact small_subgroup_fibers_same_coset K A hdefect ha0 ha
          (by simpa [subgroupFiber, H] using hsmall0)
          (by simpa [subgroupFiber, H] using hsmall)
      obtain ⟨u, hu, hu_eq⟩ := Finset.mem_vadd_finset.mp hacos
      obtain ⟨v, hv, hv_eq⟩ := Finset.mem_vadd_finset.mp hzcos
      apply Finset.mem_vadd_finset.mpr
      refine ⟨u + u + v, ?_, ?_⟩
      · have huK : u ∈ K := by simpa [H] using hu
        have hvK : v ∈ K := by simpa [H] using hv
        simpa [H] using K.add_mem (K.add_mem huK huK) hvK
      · simp only [vadd_eq_add] at hu_eq hv_eq ⊢
        rw [← hv_eq, ← hu_eq]
        abel
    let F0 := subgroupFiber K A a0
    have ha0F : a0 ∈ F0 := by
      apply Finset.mem_inter.mpr
      refine ⟨ha0, ?_⟩
      exact Finset.mem_vadd_finset.mpr ⟨0, hzero, by simp⟩
    have hFsumSubA : F0 + F0 ⊆ A + A :=
      Finset.add_subset_add Finset.inter_subset_left Finset.inter_subset_left
    have hFsumSubCoset : F0 + F0 ⊆ (a0 + a0) +ᵥ H := by
      intro z hz
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hz
      have hxU := (Finset.mem_inter.mp hx).2
      have hyU := (Finset.mem_inter.mp hy).2
      obtain ⟨u, hu, hu_eq⟩ := Finset.mem_vadd_finset.mp hxU
      obtain ⟨v, hv, hv_eq⟩ := Finset.mem_vadd_finset.mp hyU
      apply Finset.mem_vadd_finset.mpr
      refine ⟨u + v, ?_, ?_⟩
      · simpa [H] using K.add_mem (by simpa [H] using hu) (by simpa [H] using hv)
      · simp only [vadd_eq_add] at hu_eq hv_eq ⊢
        rw [← hxy, ← hu_eq, ← hv_eq]
        abel
    have hMdiff : M ⊆ ((a0 + a0) +ᵥ H) \ (F0 + F0) := by
      intro z hz
      exact Finset.mem_sdiff.mpr
        ⟨hMsub hz, fun hzF => (Finset.mem_sdiff.mp hz).2 (hFsumSubA hzF)⟩
    have hcardM : M.card ≤ H.card - (F0 + F0).card := by
      calc
        M.card ≤ (((a0 + a0) +ᵥ H) \ (F0 + F0)).card :=
          Finset.card_le_card hMdiff
        _ = H.card - (F0 + F0).card := by
          rw [Finset.card_sdiff_of_subset hFsumSubCoset,
            Finset.card_vadd_finset]
    have hFgrowth : F0.card ≤ (F0 + F0).card :=
      Finset.card_le_card_add_left ⟨a0, ha0F⟩
    have hholeSub : subgroupHole K A a0 ⊆ E := by
      simpa [E, H] using subgroupHole_subset_saturation_holes K A ha0
    have hholeCard : H.card - F0.card = (subgroupHole K A a0).card := by
      have hc := card_subgroupFiber_add_card_subgroupHole K A a0
      simp only [F0, H] at ⊢ hc
      omega
    have hbound : H.card - F0.card ≤ E.card := by
      rw [hholeCard]
      exact Finset.card_le_card hholeSub
    calc
      ((A + A) + addSubgroupFinset K).card - (A + A).card = M.card := by
        simpa [H] using hMcard.symm
      _ ≤ H.card - (F0 + F0).card := hcardM
      _ ≤ H.card - F0.card := Nat.sub_le_sub_left hFgrowth H.card
      _ ≤ E.card := hbound
      _ = (A + addSubgroupFinset K).card - A.card := by
        simpa [H] using hEcard

end Erdos336
