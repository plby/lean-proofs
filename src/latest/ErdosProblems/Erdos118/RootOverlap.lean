import ErdosProblems.Erdos118.LabelOverlays

/-!
Two actual initial root fronts of the same positive parameter, sharing the
first selected body. The fine last index is the coarse next index. Each
overlay retains the ordinary stem and is submitted separately to certificates.
-/

namespace Erdos118.RootOverlap

open LabelledExtensions LabelOverlays

private theorem root_setups_succ {L : Set ℕ} (hL : L.Infinite) (b k : ℕ) :
    ∃ A B : RootResponses.Setup (k + 1), ∃ c : ℕ, ∃ rest : List ℕ,
      A.stem.ordinary = B.stem.ordinary ∧ A.stem.rootLabel.tail = c :: rest ∧
      B.stem.rootLabel.getLastD 0 = c ∧
      (∀ x ∈ A.stem.decorated, x ∈ L ∧ b < x) ∧
      (∀ x ∈ B.stem.decorated, x ∈ L ∧ b < x) := by
  obtain ⟨M, hM⟩ := RootResponses.setup_above (2 * k + 1) hL b
  have hne : M.stem.rootLabel ≠ [] := by
    intro he
    have h := M.label_length
    simp [he] at h
  obtain ⟨f, C, hC⟩ := List.exists_cons_of_ne_nil hne
  have hClen : C.length = 2 * k + 1 := by
    have h := M.label_length
    rw [hC, List.length_cons] at h
    omega
  have hdrop : C.drop k ≠ [] := by
    intro he
    have h := congrArg List.length he
    rw [List.length_drop, hClen, List.length_nil] at h
    omega
  obtain ⟨c, rest, hrest⟩ := List.exists_cons_of_ne_nil hdrop
  let E := C.take k
  have hElen : E.length = k := by
    simp only [E, List.length_take, hClen]
    omega
  have hRlen : rest.length = k := by
    have h := congrArg List.length hrest
    rw [List.length_drop, hClen, List.length_cons] at h
    omega
  have hfull : M.stem.rootLabel = f :: (E ++ c :: rest) := by
    rw [hC, ← hrest]
    dsimp only [E]
    rw [List.take_append_drop]
  let upper := f :: c :: rest
  let lower := f :: (E ++ [c])
  have hu : upper.Sublist M.stem.rootLabel := by
    rw [hfull]
    exact (List.sublist_append_right E (c :: rest)).cons_cons f
  have hl : lower.Sublist M.stem.rootLabel := by
    rw [hfull]
    exact ((List.Sublist.refl E).append
      (List.singleton_sublist.mpr (List.mem_cons_self ..))).cons_cons f
  have hui := M.stem.label_pairwise.sublist hu
  have hli := M.stem.label_pairwise.sublist hl
  have hub : ∀ x ∈ upper, x < M.stem.root :=
    fun x hx ↦ M.stem.label_before_root x (hu.subset hx)
  have hlb : ∀ x ∈ lower, x < M.stem.root :=
    fun x hx ↦ M.stem.label_before_root x (hl.subset hx)
  have huc : upper.length = (k + 1) + 1 := by simp [upper, hRlen]
  have hlc : lower.length = (k + 1) + 1 := by simp [lower, hElen]
  have hfirst : M.stem.done.length + 1 = f := by
    simpa only [hC, List.headD_cons] using M.first_body
  let A := rootSetup M.stem upper hui hub (k + 1) huc hfirst
  let B := rootSetup M.stem lower hli hlb (k + 1) hlc hfirst
  have hordinary : ∀ x ∈ M.stem.ordinary, x ∈ L ∧ b < x :=
    fun x hx ↦ hM x (M.stem.ordinary_sublist.subset hx)
  refine ⟨A, B, c, rest, ?_, rfl, ?_, ?_, ?_⟩
  · exact (plainStem_ordinary M.stem upper hui hub).trans
      (plainStem_ordinary M.stem lower hli hlb).symm
  · change ((f :: E) ++ [c]).getLastD 0 = c
    rw [List.getLastD_eq_getLast?, List.getLast?_append]
    rfl
  · exact plainStem_supported M.stem upper hui hub
      (fun x hx ↦ hM x (List.mem_append_left _ (hu.subset hx))) hordinary
  · exact plainStem_supported M.stem lower hli hlb
      (fun x hx ↦ hM x (List.mem_append_left _ (hl.subset hx))) hordinary

theorem root_setups {L : Set ℕ} (hL : L.Infinite) (b k : ℕ) (hk : 0 < k) :
    ∃ A B : RootResponses.Setup k, ∃ c : ℕ, ∃ rest : List ℕ,
      A.stem.ordinary = B.stem.ordinary ∧ A.stem.rootLabel.tail = c :: rest ∧
      B.stem.rootLabel.getLastD 0 = c ∧
      (∀ x ∈ A.stem.decorated, x ∈ L ∧ b < x) ∧
      (∀ x ∈ B.stem.decorated, x ∈ L ∧ b < x) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact root_setups_succ hL b n

end Erdos118.RootOverlap
