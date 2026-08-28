import ErdosProblems.Erdos577.JointFirstRowModel

/-! Explicit cyclic candidates for every surviving four-row configuration. -/

namespace Erdos577.JointFirstRows

private def cols_0 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 1, 2, 3], by decide +kernel⟩

private def cols_1 : Fin 4 ↪ Fin 4 :=
  ⟨![0, 3, 2, 1], by decide +kernel⟩

private def cols_2 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 0, 3, 2], by decide +kernel⟩

private def cols_3 : Fin 4 ↪ Fin 4 :=
  ⟨![1, 2, 3, 0], by decide +kernel⟩

private def cols_4 : Fin 4 ↪ Fin 4 :=
  ⟨![2, 1, 0, 3], by decide +kernel⟩

private def cols_5 : Fin 4 ↪ Fin 4 :=
  ⟨![3, 0, 1, 2], by decide +kernel⟩

def directCandidate (d : Fin 4) (m : ℕ) : Fin 2 × Fin 2 × (Fin 4 ↪ Fin 4) :=
  match d.val, m with
  | 0, 55121 => (1, 0, cols_0)
  | 0, 32081 => (1, 1, cols_0)
  | 0, 60322 => (1, 0, cols_2)
  | 0, 48802 => (1, 1, cols_2)
  | 0, 54611 => (1, 1, cols_1)
  | 0, 23891 => (1, 0, cols_1)
  | 0, 60067 => (1, 1, cols_3)
  | 0, 44707 => (1, 0, cols_3)
  | 0, 55124 => (1, 0, cols_0)
  | 0, 32084 => (1, 1, cols_0)
  | 0, 55061 => (0, 0, cols_0)
  | 0, 32021 => (0, 1, cols_0)
  | 0, 54581 => (0, 1, cols_1)
  | 0, 23861 => (0, 0, cols_1)
  | 0, 55109 => (0, 0, cols_0)
  | 0, 32069 => (0, 1, cols_0)
  | 0, 54101 => (0, 0, cols_4)
  | 0, 30037 => (0, 1, cols_0)
  | 0, 54613 => (0, 1, cols_1)
  | 0, 54869 => (0, 0, cols_0)
  | 0, 22357 => (0, 0, cols_0)
  | 0, 38741 => (0, 0, cols_4)
  | 0, 51029 => (0, 0, cols_0)
  | 0, 55125 => (0, 0, cols_0)
  | 0, 31061 => (0, 1, cols_4)
  | 0, 31829 => (0, 1, cols_0)
  | 0, 15701 => (0, 1, cols_4)
  | 0, 23893 => (0, 0, cols_1)
  | 0, 27989 => (0, 1, cols_0)
  | 0, 32085 => (0, 1, cols_0)
  | 0, 54629 => (0, 1, cols_1)
  | 0, 23909 => (0, 0, cols_1)
  | 0, 30101 => (0, 1, cols_0)
  | 0, 22421 => (0, 0, cols_0)
  | 0, 30149 => (0, 1, cols_0)
  | 0, 22469 => (0, 0, cols_0)
  | 0, 54614 => (1, 1, cols_1)
  | 0, 23894 => (1, 0, cols_1)
  | 0, 47782 => (1, 1, cols_2)
  | 0, 43942 => (1, 0, cols_2)
  | 0, 60328 => (1, 0, cols_2)
  | 0, 48808 => (1, 1, cols_2)
  | 0, 30041 => (1, 1, cols_0)
  | 0, 22361 => (1, 0, cols_0)
  | 0, 60073 => (1, 1, cols_3)
  | 0, 44713 => (1, 0, cols_3)
  | 0, 60202 => (0, 0, cols_2)
  | 0, 48682 => (0, 1, cols_2)
  | 0, 59962 => (0, 1, cols_3)
  | 0, 44602 => (0, 0, cols_3)
  | 0, 47722 => (0, 1, cols_2)
  | 0, 43882 => (0, 0, cols_2)
  | 0, 60298 => (0, 0, cols_2)
  | 0, 48778 => (0, 1, cols_2)
  | 0, 60058 => (0, 1, cols_3)
  | 0, 44698 => (0, 0, cols_3)
  | 0, 58282 => (0, 0, cols_5)
  | 0, 46762 => (0, 1, cols_5)
  | 0, 59818 => (0, 0, cols_2)
  | 0, 47786 => (0, 1, cols_2)
  | 0, 60074 => (0, 1, cols_3)
  | 0, 27562 => (0, 0, cols_5)
  | 0, 43946 => (0, 0, cols_2)
  | 0, 52138 => (0, 0, cols_2)
  | 0, 60330 => (0, 0, cols_2)
  | 0, 48298 => (0, 1, cols_2)
  | 0, 16042 => (0, 1, cols_5)
  | 0, 40618 => (0, 1, cols_2)
  | 0, 44714 => (0, 0, cols_3)
  | 0, 48810 => (0, 1, cols_2)
  | 0, 47818 => (0, 1, cols_2)
  | 0, 43978 => (0, 0, cols_2)
  | 0, 30044 => (1, 1, cols_0)
  | 0, 22364 => (1, 0, cols_0)
  | 0, 47788 => (1, 1, cols_2)
  | 0, 43948 => (1, 0, cols_2)
  | 1, 55121 => (1, 0, cols_0)
  | 1, 32081 => (1, 1, cols_0)
  | 1, 54611 => (1, 1, cols_1)
  | 1, 23891 => (1, 0, cols_1)
  | 1, 55124 => (1, 0, cols_0)
  | 1, 32084 => (1, 1, cols_0)
  | 1, 55061 => (0, 0, cols_0)
  | 1, 32021 => (0, 1, cols_0)
  | 1, 54581 => (0, 1, cols_1)
  | 1, 23861 => (0, 0, cols_1)
  | 1, 55109 => (0, 0, cols_0)
  | 1, 32069 => (0, 1, cols_0)
  | 1, 54101 => (0, 0, cols_4)
  | 1, 30037 => (0, 1, cols_0)
  | 1, 54613 => (0, 1, cols_1)
  | 1, 54869 => (0, 0, cols_0)
  | 1, 22357 => (0, 0, cols_0)
  | 1, 38741 => (0, 0, cols_4)
  | 1, 51029 => (0, 0, cols_0)
  | 1, 55125 => (0, 0, cols_0)
  | 1, 31061 => (0, 1, cols_4)
  | 1, 31829 => (0, 1, cols_0)
  | 1, 15701 => (0, 1, cols_4)
  | 1, 23893 => (0, 0, cols_1)
  | 1, 27989 => (0, 1, cols_0)
  | 1, 32085 => (0, 1, cols_0)
  | 1, 54629 => (0, 1, cols_1)
  | 1, 23909 => (0, 0, cols_1)
  | 1, 30101 => (0, 1, cols_0)
  | 1, 22421 => (0, 0, cols_0)
  | 1, 30149 => (0, 1, cols_0)
  | 1, 22469 => (0, 0, cols_0)
  | 1, 54614 => (1, 1, cols_1)
  | 1, 23894 => (1, 0, cols_1)
  | 1, 30041 => (1, 1, cols_0)
  | 1, 22361 => (1, 0, cols_0)
  | 1, 30044 => (1, 1, cols_0)
  | 1, 22364 => (1, 0, cols_0)
  | 2, 60322 => (1, 0, cols_2)
  | 2, 48802 => (1, 1, cols_2)
  | 2, 60067 => (1, 1, cols_3)
  | 2, 44707 => (1, 0, cols_3)
  | 2, 47782 => (1, 1, cols_2)
  | 2, 43942 => (1, 0, cols_2)
  | 2, 60328 => (1, 0, cols_2)
  | 2, 48808 => (1, 1, cols_2)
  | 2, 60073 => (1, 1, cols_3)
  | 2, 44713 => (1, 0, cols_3)
  | 2, 60202 => (0, 0, cols_2)
  | 2, 48682 => (0, 1, cols_2)
  | 2, 59962 => (0, 1, cols_3)
  | 2, 44602 => (0, 0, cols_3)
  | 2, 47722 => (0, 1, cols_2)
  | 2, 43882 => (0, 0, cols_2)
  | 2, 60298 => (0, 0, cols_2)
  | 2, 48778 => (0, 1, cols_2)
  | 2, 60058 => (0, 1, cols_3)
  | 2, 44698 => (0, 0, cols_3)
  | 2, 58282 => (0, 0, cols_5)
  | 2, 46762 => (0, 1, cols_5)
  | 2, 59818 => (0, 0, cols_2)
  | 2, 47786 => (0, 1, cols_2)
  | 2, 60074 => (0, 1, cols_3)
  | 2, 27562 => (0, 0, cols_5)
  | 2, 43946 => (0, 0, cols_2)
  | 2, 52138 => (0, 0, cols_2)
  | 2, 60330 => (0, 0, cols_2)
  | 2, 48298 => (0, 1, cols_2)
  | 2, 16042 => (0, 1, cols_5)
  | 2, 40618 => (0, 1, cols_2)
  | 2, 44714 => (0, 0, cols_3)
  | 2, 48810 => (0, 1, cols_2)
  | 2, 47818 => (0, 1, cols_2)
  | 2, 43978 => (0, 0, cols_2)
  | 2, 47788 => (1, 1, cols_2)
  | 2, 43948 => (1, 0, cols_2)
  | _, _ => (0, 0, Function.Embedding.refl _)

def gainCandidate (d : Fin 4) (m : ℕ) : Fin 2 × (Fin 4 ↪ Fin 4) :=
  match d.val, m with
  | 0, 56625 => (1, cols_1)
  | 0, 56673 => (1, cols_2)
  | 0, 30609 => (1, cols_0)
  | 0, 30657 => (1, cols_4)
  | 0, 60978 => (1, cols_1)
  | 0, 47970 => (1, cols_2)
  | 0, 61074 => (1, cols_0)
  | 0, 48066 => (1, cols_4)
  | 0, 56595 => (0, cols_1)
  | 0, 60963 => (0, cols_1)
  | 0, 56643 => (0, cols_1)
  | 0, 61059 => (0, cols_1)
  | 0, 56628 => (1, cols_1)
  | 0, 56676 => (1, cols_2)
  | 0, 30612 => (1, cols_0)
  | 0, 30660 => (1, cols_4)
  | 0, 56598 => (0, cols_2)
  | 0, 47910 => (0, cols_2)
  | 0, 56646 => (0, cols_2)
  | 0, 48006 => (0, cols_2)
  | 0, 60984 => (1, cols_1)
  | 0, 47976 => (1, cols_2)
  | 0, 61080 => (1, cols_0)
  | 0, 48072 => (1, cols_4)
  | 0, 30489 => (0, cols_0)
  | 0, 60969 => (0, cols_0)
  | 0, 30537 => (0, cols_0)
  | 0, 61065 => (0, cols_0)
  | 0, 30492 => (0, cols_4)
  | 0, 47916 => (0, cols_4)
  | 0, 30540 => (0, cols_4)
  | 0, 48012 => (0, cols_4)
  | _, _ => (0, Function.Embedding.refl _)

def DirectAccepted (d : Fin 4) (m : ℕ) : Prop :=
  Direct d m (directCandidate d m).1 (directCandidate d m).2.1 (directCandidate d m).2.2

instance (d : Fin 4) (m : ℕ) : Decidable (DirectAccepted d m) :=
  inferInstanceAs (Decidable (Direct d m _ _ _))

def GainAccepted (d : Fin 4) (m : ℕ) : Prop :=
  Gain d m (gainCandidate d m).1 (gainCandidate d m).2

instance (d : Fin 4) (m : ℕ) : Decidable (GainAccepted d m) :=
  inferInstanceAs (Decidable (Gain d m _ _))

def covered (d : Fin 4) (m : ℕ) : Bool :=
  decide (CommonColumn d m) || decide (DirectAccepted d m) || decide (GainAccepted d m)

theorem covered_classified (d : Fin 4) (m : ℕ) (h : covered d m = true) : Classified d m := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inl (of_decide_eq_true h)
    · exact Or.inr (Or.inl ⟨(directCandidate d m).1, (directCandidate d m).2.1,
        (directCandidate d m).2.2, of_decide_eq_true h⟩)
  · exact Or.inr (Or.inr ⟨(gainCandidate d m).1, (gainCandidate d m).2, of_decide_eq_true h⟩)

end Erdos577.JointFirstRows
