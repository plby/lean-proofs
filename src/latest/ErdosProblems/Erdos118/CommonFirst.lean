import ErdosProblems.Erdos118.LabelOverlays

/-!
Two exact response fronts with a common first ordinary position. Each new
front satisfies its own prescribed label cardinality. No blue outcome is
transported through relabelling; callers must apply both actual certificates.
-/

namespace Erdos118.CommonFirst

open LabelledExtensions Negative Negative.Exact Erdos590.Larson

private theorem head_take_succ (C : List ℕ) (k : ℕ) :
    (C.take (k + 1)).headD 0 = C.headD 0 := by
  cases C <;> rfl

private def rootTake {n : ℕ} (A : RootResponses.Setup n) (k : ℕ) (hk : k ≤ n) :
    RootResponses.Setup k :=
  LabelOverlays.rootSetup A.stem (A.stem.rootLabel.take (k + 1))
    (A.stem.label_pairwise.sublist (List.take_sublist ..))
    (fun x hx ↦ A.stem.label_before_root x ((List.take_sublist ..).subset hx)) k
    (by rw [List.length_take, A.label_length]; omega)
    (by rw [head_take_succ]; exact A.first_body)

theorem root_setups {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) :
    ∃ A : RootResponses.Setup k, ∃ B : RootResponses.Setup l,
      A.stem.ordinary = B.stem.ordinary ∧
      (A.stem.rootLabel <+: B.stem.rootLabel ∨ B.stem.rootLabel <+: A.stem.rootLabel) ∧
      (∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x) ∧
      (∀ x ∈ B.stem.decorated, x ∈ H ∧ b < x) := by
  obtain ⟨C, hC⟩ := RootResponses.setup_above (max k l) hH b
  let A := rootTake C k (le_max_left _ _)
  let B := rootTake C l (le_max_right _ _)
  have hfresh : ∀ (j : ℕ) (hj : j ≤ max k l),
      ∀ x ∈ (rootTake C j hj).stem.decorated, x ∈ H ∧ b < x := by
    intro j hj
    have hdec : (rootTake C j hj).stem.decorated =
        C.stem.rootLabel.take (j + 1) ++ C.stem.ordinary :=
      LabelOverlays.plainStem_decorated C.stem _
        (C.stem.label_pairwise.sublist (List.take_sublist ..))
        (fun x hx ↦ C.stem.label_before_root x ((List.take_sublist ..).subset hx))
    rw [hdec]
    intro x hx
    exact (List.mem_append.mp hx).elim
      (fun hx ↦ hC x (List.mem_append_left _ ((List.take_sublist ..).subset hx)))
      (fun hx ↦ hC x (C.stem.ordinary_sublist.subset hx))
  refine ⟨A, B, ?_, ?_, hfresh k _, hfresh l _⟩
  · rfl
  · change C.stem.rootLabel.take (k + 1) <+: C.stem.rootLabel.take (l + 1) ∨
      C.stem.rootLabel.take (l + 1) <+: C.stem.rootLabel.take (k + 1)
    rcases le_total k l with h | h
    · exact Or.inl (List.take_prefix_take_left (Nat.add_le_add_right h 1))
    · exact Or.inr (List.take_prefix_take_left (Nat.add_le_add_right h 1))

private def bodyTake {S : Stem} {n : ℕ} (A : BodyResponses.Setup S n)
    (T : Stem) (hT : T.done.length + 1 < T.root)
    (hbefore : ∀ x ∈ T.decorated, ∀ y ∈ BodyResponses.newWord A.position, x < y)
    (k : ℕ) (hk : k ≤ n) : BodyResponses.Setup T k where
  position :=
    { stem := T, size := A.position.size, label := A.position.label.take (k + 1)
      entries := A.position.entries, room := hT
      started := A.position.started, unfinished := A.position.unfinished
      increasing := by
        have hsub : (A.position.label.take (k + 1) ++ A.position.size :: A.position.entries).Sublist
            (BodyResponses.newWord A.position) :=
          (List.take_sublist ..).append (List.Sublist.refl _)
        exact List.pairwise_append.mpr ⟨T.increasing,
          (BodyResponses.newWord_pairwise A.position).sublist hsub,
          fun x hx y hy ↦ hbefore x hx y (hsub.subset hy)⟩ }
  stem_eq := rfl
  label_length := by
    change (A.position.label.take (k + 1)).length = k + 1
    rw [List.length_take, A.label_length]
    omega
  entries_length := by
    change A.position.entries.length = (A.position.label.take (k + 1)).headD 0
    rw [head_take_succ]
    exact A.entries_length

theorem body_setups {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ)
    (S T : Stem) (hS : S.done.length + 1 < S.root) (hT : T.done.length + 1 < T.root)
    (hST : S.ordinary = T.ordinary) :
    ∃ A : BodyResponses.Setup S k, ∃ B : BodyResponses.Setup T l,
      A.position.ordinary = B.position.ordinary ∧
      (A.position.label <+: B.position.label ∨ B.position.label <+: A.position.label) ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) ∧
      (∀ x ∈ BodyResponses.newWord B.position, x ∈ H ∧ b < x) := by
  let bound := max b (max S.decorated.sum T.decorated.sum)
  obtain ⟨C, hC⟩ := BodyResponses.setup_above S (max k l) hS hH bound
  have hbeforeS : ∀ x ∈ S.decorated, ∀ y ∈ BodyResponses.newWord C.position, x < y := by
    intro x hx y hy
    exact (nat_le_sum_of_mem hx).trans_lt
      (((le_max_left _ _).trans (le_max_right b _)).trans_lt (hC y hy).2)
  have hbeforeT : ∀ x ∈ T.decorated, ∀ y ∈ BodyResponses.newWord C.position, x < y := by
    intro x hx y hy
    exact (nat_le_sum_of_mem hx).trans_lt
      (((le_max_right _ _).trans (le_max_right b _)).trans_lt (hC y hy).2)
  let A := bodyTake C S hS hbeforeS k (le_max_left _ _)
  let B := bodyTake C T hT hbeforeT l (le_max_right _ _)
  have hfresh : ∀ (V : Stem) (hv : V.done.length + 1 < V.root)
      (hb : ∀ x ∈ V.decorated, ∀ y ∈ BodyResponses.newWord C.position, x < y)
      (j : ℕ) (hj : j ≤ max k l),
      ∀ x ∈ BodyResponses.newWord (bodyTake C V hv hb j hj).position, x ∈ H ∧ b < x := by
    intro V hv hb j hj x hx
    have hsub : (C.position.label.take (j + 1) ++ C.position.size :: C.position.entries).Sublist
        (BodyResponses.newWord C.position) :=
      (List.take_sublist ..).append (List.Sublist.refl _)
    have hf := hC x (hsub.subset hx)
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2⟩
  refine ⟨A, B, ?_, ?_, hfresh S hS hbeforeS k _, hfresh T hT hbeforeT l _⟩
  · change S.ordinary ++ C.position.size :: C.position.entries =
      T.ordinary ++ C.position.size :: C.position.entries
    rw [hST]
  · change C.position.label.take (k + 1) <+: C.position.label.take (l + 1) ∨
      C.position.label.take (l + 1) <+: C.position.label.take (k + 1)
    rcases le_total k l with h | h
    · exact Or.inl (List.take_prefix_take_left (Nat.add_le_add_right h 1))
    · exact Or.inr (List.take_prefix_take_left (Nat.add_le_add_right h 1))

end Erdos118.CommonFirst
