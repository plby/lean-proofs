import ErdosProblems.Erdos4.FGKMTProcess

/-! Every positive-mass final survivor set comes from one legal edge per source. -/

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def coveredThrough (choice : ℕ → I → Finset V) (n : ℕ) : Finset V :=
  (Finset.range n).biUnion (fun j => Finset.univ.biUnion (choice j))

theorem coveredThrough_congr (choice choice' : ℕ → I → Finset V) (n : ℕ)
    (h : ∀ j < n, choice j = choice' j) : coveredThrough choice n = coveredThrough choice' n := by
  apply Finset.biUnion_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem coveredThrough_succ (choice : ℕ → I → Finset V) (n : ℕ) :
    coveredThrough choice (n + 1) = Finset.univ.biUnion (choice n) ∪ coveredThrough choice n := by
  unfold coveredThrough
  rw [Finset.range_add_one, Finset.biUnion_insert]

theorem coveredThrough_update (choice : ℕ → I → Finset V) (n : ℕ) (new : I → Finset V) :
    coveredThrough (Function.update choice n new) n = coveredThrough choice n := by
  apply coveredThrough_congr
  intro j hj
  exact Function.update_of_ne (Nat.ne_of_lt hj) new choice

theorem complement_covered_update (choice : ℕ → I → Finset V) (n : ℕ) (new : I → Finset V) :
    (Finset.univ : Finset V) \ coveredThrough (Function.update choice n new) (n + 1) =
      afterRound (Finset.univ \ coveredThrough choice n) new := by
  rw [coveredThrough_succ, coveredThrough_update, Function.update_self]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, afterRound]
  tauto

theorem survivorProcess_legal (μ : ℕ → I → FiniteLaw (Finset V)) (t : ℕ → ℝ)
    (n : ℕ) (W : Finset V) (hW : 0 < (survivorProcess μ t n).weight W) :
    ∃ choice : ℕ → I → Finset V,
      W = Finset.univ \ coveredThrough choice n ∧
        ∀ j < n, ∀ i, choice j i = ∅ ∨ 0 < (μ j i).weight (choice j i) := by
  induction n generalizing W with
  | zero =>
    have hWeq : W = Finset.univ := by
      by_contra hne
      simp only [survivorProcess, FiniteLaw.dirac, if_neg hne] at hW
      linarith
    refine ⟨fun _ _ => ∅, ?_, ?_⟩
    · simpa [coveredThrough] using hWeq
    · intro j hj
      omega
  | succ n ih =>
    obtain ⟨Wold, new, hold, hnew, hlegal⟩ := roundLaw_support (survivorProcess μ t n)
      (μ n) (modelSequence μ n) (modelSequence_pos μ n) (t n) W hW
    obtain ⟨old, hshape, hsource⟩ := ih Wold hold
    refine ⟨Function.update old n new, ?_, ?_⟩
    · rw [complement_covered_update, ← hshape]
      exact hnew
    · intro j hj i
      by_cases heq : j = n
      · subst j
        simpa only [Function.update_self] using (hlegal i).2
      · have hjn : j < n := by omega
        rw [Function.update_of_ne heq]
        exact hsource j hjn i

end Erdos4.FGKMT
