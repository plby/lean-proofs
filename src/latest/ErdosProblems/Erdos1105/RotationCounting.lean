import ErdosProblems.Erdos1105.RainbowRotation

namespace Erdos1105

open SimpleGraph Finset

/-- The degree pigeonhole argument for the two crossing chords. The
missing penultimate and terminal adjacencies remove the boundary cases. -/
theorem exists_rotating_chords {n : ℕ} (G : SimpleGraph (Fin (n + 3)))
    [DecidableRel G.Adj]
    (hpenult : ¬G.Adj 0 ⟨n + 1, by omega⟩)
    (hlast : ¬G.Adj 1 (Fin.last (n + 2)))
    (hcount : n + 2 ≤
      (univ.filter (fun i : Fin (n + 3) ↦ G.Adj 0 i ∧ i.val < n + 2)).card +
      (univ.filter (fun i : Fin (n + 3) ↦ G.Adj 1 i ∧ 1 ≤ i.val)).card) :
    ∃ q : Fin (n + 3), 2 ≤ q.val ∧ q.val < n + 2 ∧ G.Adj 0 q ∧ G.Adj 1 (q + 1) := by
  classical
  let A := univ.filter (fun i : Fin (n + 3) ↦ G.Adj 0 i ∧ i.val < n + 2)
  let S := A.image (fun i ↦ i + 1)
  let T := univ.filter (fun i : Fin (n + 3) ↦ G.Adj 1 i ∧ 1 ≤ i.val)
  let U := Ico (2 : Fin (n + 3)) (Fin.last (n + 2))
  have hA (i : Fin (n + 3)) (hi : i ∈ A) : G.Adj 0 i ∧ 1 ≤ i.val ∧ i.val < n + 1 := by
    have hi' : G.Adj 0 i ∧ i.val < n + 2 := (mem_filter.mp hi).2
    have h0 : i.val ≠ 0 := by
      intro h
      have hi0 : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using h)
      exact hi'.1.ne hi0.symm
    have h1 : i.val ≠ n + 1 := by
      intro h
      have heq : i = ⟨n + 1, by omega⟩ := Fin.ext h
      exact hpenult (heq ▸ hi'.1)
    exact ⟨hi'.1, by omega, by omega⟩
  have hS : S ⊆ U := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    obtain ⟨_, hi0, hi1⟩ := hA i hi
    have hval : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
    change (i + 1) ∈ Ico (2 : Fin (n + 3)) (Fin.last (n + 2))
    rw [mem_Ico]
    change (2 : Fin (n + 3)).val ≤ (i + 1).val ∧ (i + 1).val < n + 2
    rw [hval]
    have htwo : (2 : Fin (n + 3)).val = 2 := by simp
    rw [htwo]
    omega
  have hT : T ⊆ U := by
    intro j hj
    have hj' : G.Adj 1 j ∧ 1 ≤ j.val := (mem_filter.mp hj).2
    have h1 : j.val ≠ 1 := by
      intro h
      have hj1 : j = 1 := Fin.ext (by simpa only [Fin.val_one] using h)
      exact hj'.1.ne hj1.symm
    have hend : j.val ≠ n + 2 := by
      intro h
      have heq : j = Fin.last (n + 2) := Fin.ext h
      exact hlast (heq ▸ hj'.1)
    change j ∈ Ico (2 : Fin (n + 3)) (Fin.last (n + 2))
    rw [mem_Ico]
    change (2 : Fin (n + 3)).val ≤ j.val ∧ j.val < n + 2
    have htwo : (2 : Fin (n + 3)).val = 2 := by simp
    rw [htwo]
    have := j.isLt
    omega
  have hU : U.card = n := by
    have htwo : (2 : Fin (n + 3)).val = 2 := by simp
    simp only [U, Fin.card_Ico, Fin.val_last, htwo]
    omega
  have hScard : S.card = A.card := card_image_of_injective A (fun _ _ h ↦ add_right_cancel h)
  have hunion : (S ∪ T).card ≤ n := by
    simpa only [hU] using card_le_card (union_subset hS hT)
  have hinter : 2 ≤ (S ∩ T).card := by
    have hsum := card_union_add_card_inter S T
    change n + 2 ≤ A.card + T.card at hcount
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < (S ∩ T).card)
  have hex : ∃ j ∈ S ∩ T, j ≠ (2 : Fin (n + 3)) := by
    by_cases ha2 : a = 2
    · exact ⟨b, hb, fun hb2 ↦ hab (ha2.trans hb2.symm)⟩
    · exact ⟨a, ha, ha2⟩
  obtain ⟨j, hj, hj2⟩ := hex
  obtain ⟨q, hqA, heq⟩ := mem_image.mp (mem_inter.mp hj).1
  obtain ⟨hqadj, hq1, hqend⟩ := hA q hqA
  have hq2 : 2 ≤ q.val := by
    by_contra! hq
    have hqval : q.val = 1 := by omega
    apply hj2
    rw [← heq]
    apply Fin.ext
    simp [Fin.val_add, hqval]
  refine ⟨q, hq2, by omega, hqadj, ?_⟩
  have hTj := (mem_filter.mp (mem_inter.mp hj).2).2.1
  rwa [heq]

end Erdos1105
