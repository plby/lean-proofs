import ErdosProblems.Erdos4.FGKMTSourcePartition
import ErdosProblems.Erdos4.FGKMTLowerDegreeCovering

/-! A source is active in only its assigned round; extraction therefore uses it once. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    {m : ℕ}

noncomputable def assignedRounds (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (j : ℕ) (i : I) : FiniteLaw (Finset V) :=
  if (a i).map Fin.val = some j then μ i else FiniteLaw.dirac ∅

omit [Fintype I] [DecidableEq I] [DecidableEq V] in
theorem assignedRounds_at (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (j : Fin m) (i : I) :
    assignedRounds μ a j.val i =
      if a i = some j then μ i else FiniteLaw.dirac ∅ := by
  cases ha : a i with
  | none => simp [assignedRounds, ha]
  | some t =>
    by_cases ht : t = j
    · subst t
      simp [assignedRounds, ha]
    · have hval : t.val ≠ j.val := fun hh => ht (Fin.ext hh)
      simp [assignedRounds, ha, ht, hval]

theorem assignedRounds_prob_le (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (j : ℕ) (i : I)
    (E : Finset V → Prop) (hE : ¬ E ∅) :
    (assignedRounds μ a j i).prob E ≤ (μ i).prob E := by
  by_cases ha : (a i).map Fin.val = some j
  · simp only [assignedRounds, if_pos ha, le_refl]
  · have hzero : (FiniteLaw.dirac (∅ : Finset V)).prob E = 0 := by
      rw [FiniteLaw.prob_eq_mean, FiniteLaw.mean_dirac, if_neg hE]
    rw [assignedRounds, if_neg ha, hzero]
    exact (μ i).prob_nonneg E

theorem assignedRounds_degree (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (j : Fin m) (v : V) :
    vertexDegree (assignedRounds μ a j.val) v =
      ∑ i, if a i = some j then (μ i).prob (fun e => v ∈ e) else 0 := by
  unfold vertexDegree
  apply Finset.sum_congr rfl
  intro i _
  rw [assignedRounds_at]
  by_cases ha : a i = some j
  · simp only [if_pos ha]
  · simp only [if_neg ha]
    rw [FiniteLaw.prob_eq_mean, FiniteLaw.mean_dirac]
    simp

theorem assignedRounds_pair_le (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (j : ℕ) (v w : V) :
    pairDegree (assignedRounds μ a j) v w ≤ pairDegree μ v w := by
  apply Finset.sum_le_sum
  intro i _
  exact assignedRounds_prob_le μ a j i _ (by simp)

omit [Fintype I] [DecidableEq I] in
theorem assignedRounds_support (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (j : ℕ) (i : I) (e : Finset V)
    (he : 0 < (assignedRounds μ a j i).weight e) :
    e = ∅ ∨ (a i).map Fin.val = some j ∧ 0 < (μ i).weight e := by
  by_cases ha : (a i).map Fin.val = some j
  · exact Or.inr ⟨ha, by simpa only [assignedRounds, if_pos ha] using he⟩
  · left
    by_contra hne
    simp [assignedRounds, ha, FiniteLaw.dirac, hne] at he

def assignedChoice (a : I → Option (Fin m))
    (choice : ℕ → I → Finset V) (i : I) : Finset V :=
  match a i with
  | none => ∅
  | some j => choice j.val i

theorem assignedChoice_legal (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (choice : ℕ → I → Finset V)
    (hlegal : ∀ j < m, ∀ i, choice j i = ∅ ∨
      0 < (assignedRounds μ a j i).weight (choice j i)) (i : I) :
    assignedChoice a choice i = ∅ ∨ 0 < (μ i).weight (assignedChoice a choice i) := by
  cases ha : a i with
  | none => exact Or.inl (by simp [assignedChoice, ha])
  | some j =>
    have hh := hlegal j.val j.isLt i
    rw [assignedRounds_at, if_pos ha] at hh
    simpa only [assignedChoice, ha] using hh

theorem assignedChoice_contains (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (choice : ℕ → I → Finset V)
    (hlegal : ∀ j < m, ∀ i, choice j i = ∅ ∨
      0 < (assignedRounds μ a j i).weight (choice j i))
    (j : ℕ) (hj : j < m) (i : I) :
    choice j i ⊆ assignedChoice a choice i := by
  rcases hlegal j hj i with he | he
  · rw [he]
    exact Finset.empty_subset _
  · rcases assignedRounds_support μ a j i (choice j i) he with he | ⟨ha, _⟩
    · rw [he]
      exact Finset.empty_subset _
    · cases ht : a i with
      | none => simp [ht] at ha
      | some t =>
        have hval : t.val = j := by simpa only [ht, Option.map_some, Option.some.injEq] using ha
        simp only [assignedChoice, ht, hval]
        exact Finset.Subset.refl _

theorem assignedChoice_covers (μ : I → FiniteLaw (Finset V))
    (a : I → Option (Fin m)) (choice : ℕ → I → Finset V)
    (hlegal : ∀ j < m, ∀ i, choice j i = ∅ ∨
      0 < (assignedRounds μ a j i).weight (choice j i)) :
    coveredThrough choice m ⊆ Finset.univ.biUnion (assignedChoice a choice) := by
  intro v hv
  obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvj
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
    assignedChoice_contains μ a choice hlegal j (Finset.mem_range.mp hj) i hvi⟩

end Erdos4.FGKMT
