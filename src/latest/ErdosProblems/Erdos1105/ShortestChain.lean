import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

theorem exists_sequence_of_reflTransGen {A : Type*} {r : A → A → Prop} {a b : A}
    (h : Relation.ReflTransGen r a b) :
    ∃ n, ∃ f : ℕ → A, f 0 = a ∧ f n = b ∧ ∀ i < n, r (f i) (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ ↦ a, rfl, rfl, by omega⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, f, hf₀, hfn, hf⟩ := ih
    let g (i : ℕ) := if i ≤ n then f i else c
    refine ⟨n + 1, g, by simpa [g] using hf₀, by simp [g], ?_⟩
    intro i hi
    by_cases hin : i < n
    · simpa only [g, if_pos (show i ≤ n by omega), if_pos (show i + 1 ≤ n by omega)] using hf i hin
    · have hi' : i = n := by omega
      subst i
      simpa only [g, if_pos le_rfl, if_neg (show ¬n + 1 ≤ n by omega), hfn] using hbc

/-- A shortest directed chain has no edge skipping any intermediate
vertex. No finiteness of the underlying type is needed. -/
theorem exists_shortest_chain {A : Type*} {r : A → A → Prop} {a b : A}
    (h : Relation.ReflTransGen r a b) :
    ∃ n, ∃ f : ℕ → A, f 0 = a ∧ f n = b ∧
      (∀ i < n, r (f i) (f (i + 1))) ∧
      ∀ i j, i + 1 < j → j ≤ n → ¬r (f i) (f j) := by
  classical
  let Q (n : ℕ) := ∃ f : ℕ → A, f 0 = a ∧ f n = b ∧ ∀ i < n, r (f i) (f (i + 1))
  have hQ : ∃ n, Q n := exists_sequence_of_reflTransGen h
  let n := Nat.find hQ
  obtain ⟨f, hf₀, hfn, hf⟩ := Nat.find_spec hQ
  refine ⟨n, f, hf₀, hfn, hf, ?_⟩
  intro i j hij hj hshort
  let d := j - i - 1
  let m := n - d
  let g (t : ℕ) := if t ≤ i then f t else f (t + d)
  have hd : 0 < d := by dsimp [d]; omega
  have hm : i < m := by dsimp [m, d]; omega
  have hmn : m < n := by dsimp [m, d]; omega
  have hnew : Q m := by
    refine ⟨g, by simpa only [g, if_pos (Nat.zero_le _)] using hf₀, ?_, ?_⟩
    · simp only [g, if_neg (not_le.mpr hm)]
      have hidx : m + d = n := by dsimp [m, d]; omega
      exact hidx ▸ hfn
    · intro t ht
      by_cases hti : t < i
      · simpa only [g, if_pos (show t ≤ i by omega), if_pos (show t + 1 ≤ i by omega)] using
          hf t (by omega)
      · by_cases heq : t = i
        · subst t
          simp only [g, if_pos le_rfl, if_neg (show ¬i + 1 ≤ i by omega)]
          have hidx : i + 1 + d = j := by dsimp [d]; omega
          rwa [hidx]
        · have hit : i < t := by omega
          simp only [g, if_neg (not_le.mpr hit), if_neg (show ¬t + 1 ≤ i by omega)]
          have hidx : t + 1 + d = t + d + 1 := by omega
          rw [hidx]
          apply hf
          dsimp [m, d] at ht ⊢
          omega
  have hmin : n ≤ m := Nat.find_min' hQ hnew
  omega

end Erdos1105

#print axioms Erdos1105.exists_shortest_chain
