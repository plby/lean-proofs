import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: FiniteRealAdjacentPairsExists]
lemma FiniteRealAdjacentPairsExists
    {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (key : alpha → ℝ)
    (hinj : Function.Injective key) (hne : S.Nonempty) :
    ∃ E : Finset (alpha × alpha),
      (∀ p q, (p, q) ∈ E ↔
        p ∈ S ∧ q ∈ S ∧ key p < key q ∧
          ∀ r ∈ S, ¬(key p < key r ∧ key r < key q)) ∧
      (∀ e1 e2, e1 ∈ E → e2 ∈ E → e1 ≠ e2 →
        Disjoint (Set.Ioo (key e1.1) (key e1.2))
          (Set.Ioo (key e2.1) (key e2.2))) ∧
      (∀ e1 e2, e1 ∈ E → e2 ∈ E → e1 ≠ e2 →
        (Set.Icc (key e1.1) (key e1.2) ∩
          Set.Icc (key e2.1) (key e2.2)).Subsingleton) ∧
      E.card + 1 = S.card := by
-- BODY
  have list_char : ∀ (u : List alpha),
      u.Pairwise (fun a b ↦ key a < key b) → ∀ x y,
        (x, y) ∈ u.consecutivePairs ↔
          x ∈ u ∧ y ∈ u ∧ key x < key y ∧
            ∀ z ∈ u, ¬(key x < key z ∧ key z < key y) := by
    intro u hu
    induction u with
    | nil => simp
    | cons a u ih =>
        cases u with
        | nil => grind
        | cons b u =>
            have htail := (List.pairwise_cons.mp hu).2
            have hi := ih htail
            grind (splits := 20) [List.pairwise_cons]
  letI : LinearOrder alpha := LinearOrder.lift' key hinj
  let l : List alpha := S.sort
  let E : Finset (alpha × alpha) := l.consecutivePairs.toFinset
  have hsorted : l.Pairwise (fun a b ↦ key a < key b) := by
    have hnative : l.SortedLT := Finset.sortedLT_sort S
    refine List.Pairwise.imp (R := fun a b : alpha ↦ a < b)
      (S := fun a b ↦ key a < key b) ?_ hnative.pairwise
    intro a b hab
    change key a < key b at hab
    exact hab
  have hchar : ∀ p q,
      (p, q) ∈ l.consecutivePairs ↔
        p ∈ l ∧ q ∈ l ∧ key p < key q ∧
          ∀ r ∈ l, ¬(key p < key r ∧ key r < key q) := by
    intro p q
    exact list_char l hsorted p q
  have hmem : ∀ p q, (p, q) ∈ E ↔
      p ∈ S ∧ q ∈ S ∧ key p < key q ∧
        ∀ r ∈ S, ¬(key p < key r ∧ key r < key q) := by
    intro p q
    simp only [E, List.mem_toFinset, hchar]
    simp only [l, Finset.mem_sort]
  have hdisjoint : ∀ e1 e2, e1 ∈ E → e2 ∈ E → e1 ≠ e2 →
      Disjoint (Set.Ioo (key e1.1) (key e1.2))
        (Set.Ioo (key e2.1) (key e2.2)) := by
    intro e1 e2 he1 he2 hne12
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have h1 := (hmem e1.1 e1.2).mp he1
    have h2 := (hmem e2.1 e2.2).mp he2
    rcases lt_trichotomy (key e1.1) (key e2.1) with hlt | heq | hgt
    · exact h1.2.2.2 e2.1 h2.1 ⟨hlt, hx2.1.trans hx1.2⟩
    · have heq1 : e1.1 = e2.1 := hinj heq
      rcases lt_trichotomy (key e1.2) (key e2.2) with hlt2 | heq2 | hgt2
      · exact h2.2.2.2 e1.2 h1.2.1 ⟨heq ▸ h1.2.2.1, hlt2⟩
      · have heq2' : e1.2 = e2.2 := hinj heq2
        exact hne12 (Prod.ext heq1 heq2')
      · exact h1.2.2.2 e2.2 h2.2.1 ⟨heq ▸ h2.2.2.1, hgt2⟩
    · exact h2.2.2.2 e1.1 h1.1 ⟨hgt, hx1.1.trans hx2.2⟩
  refine ⟨E, hmem, hdisjoint, ?_, ?_⟩
  · intro e1 e2 he1 he2 hne12
    rw [Set.Icc_inter_Icc]
    exact Set.subsingleton_Icc_of_ge
      (Set.Ioo_disjoint_Ioo.mp (hdisjoint e1 e2 he1 he2 hne12))
  · have hpairs : l.consecutivePairs.Nodup := by
      have list_nodup : ∀ (u : List alpha), u.Nodup → u.consecutivePairs.Nodup := by
        intro u hu
        induction u with
        | nil => simp
        | cons a u ih =>
            cases u with
            | nil => exact .nil
            | cons b u =>
                have htail := (List.nodup_cons.mp hu).2
                have hi := ih htail
                change ((a, b) :: (b :: u).consecutivePairs).Nodup
                refine List.nodup_cons.mpr ⟨?_, hi⟩
                intro hab
                exact (List.nodup_cons.mp hu).1 (List.of_mem_zip hab).1
      exact list_nodup l (Finset.sort_nodup S (fun a b ↦ a ≤ b))
    change l.consecutivePairs.toFinset.card + 1 = S.card
    rw [List.toFinset_card_of_nodup hpairs]
    rw [List.length_zip, List.length_tail,
      Nat.min_eq_right (Nat.sub_le l.length 1)]
    rw [show l.length = S.card by exact Finset.length_sort (fun a b ↦ a ≤ b)]
    exact Nat.sub_add_cancel (Finset.card_pos.mpr hne)
