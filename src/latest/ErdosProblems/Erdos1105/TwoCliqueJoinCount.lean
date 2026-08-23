import ErdosProblems.Erdos1105.BetweenCounting
import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

open SimpleGraph Finset

/-- A graph whose edges away from `C` lie inside either of two specified
sets has at most the complete-join contribution plus the two clique counts. -/
theorem two_clique_join_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B C : Finset V)
    (hshape : ∀ x y, G.Adj x y → x ∈ C ∨ y ∈ C ∨ (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)) :
    G.edgeFinset.card ≤ C.card.choose 2 + C.card * (Fintype.card V - C.card) +
      A.card.choose 2 + B.card.choose 2 := by
  classical
  let X := G.between (C : Set V) (↑(Cᶜ) : Set V)
  have hsub : G.edgeFinset ⊆ E767EGApi.edgesInside G C ∪ X.edgeFinset ∪
      E767EGApi.edgesInside G A ∪ E767EGApi.edgesInside G B := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := mem_edgeFinset.mp he
      have hinside (S : Finset V) (hx : x ∈ S) (hy : y ∈ S) :
          s(x, y) ∈ E767EGApi.edgesInside G S := by
        apply mem_filter.mpr
        refine ⟨he, ?_⟩
        intro z hz
        have hz' : z = x ∨ z = y := by simpa using hz
        rcases hz' with rfl | rfl <;> assumption
      by_cases hx : x ∈ C
      · by_cases hy : y ∈ C
        · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (hinside C hx hy)))
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _
            (mem_edgeFinset.mpr ⟨hxy, Or.inl ⟨hx, mem_compl.mpr hy⟩⟩)))
      · by_cases hy : y ∈ C
        · exact mem_union_left _ (mem_union_left _ (mem_union_right _
            (mem_edgeFinset.mpr ⟨hxy, Or.inr ⟨mem_compl.mpr hx, hy⟩⟩)))
        · rcases ((hshape x y hxy).resolve_left hx).resolve_left hy with hA | hB
          · exact mem_union_left _ (mem_union_right _ (hinside A hA.1 hA.2))
          · exact mem_union_right _ (hinside B hB.1 hB.2)
  have hcount := card_le_card hsub
  have hu₁ := card_union_le (E767EGApi.edgesInside G C) X.edgeFinset
  have hu₂ := card_union_le (E767EGApi.edgesInside G C ∪ X.edgeFinset) (E767EGApi.edgesInside G A)
  have hu₃ := card_union_le (E767EGApi.edgesInside G C ∪ X.edgeFinset ∪ E767EGApi.edgesInside G A)
    (E767EGApi.edgesInside G B)
  have hC := edgesInside_le_choose G C
  have hA := edgesInside_le_choose G A
  have hB := edgesInside_le_choose G B
  have hX : X.edgeFinset.card ≤ C.card * (Fintype.card V - C.card) := by
    rw [between_edge_count G (A := C) (B := Cᶜ) disjoint_compl_right]
    calc
      _ ≤ ∑ _ ∈ Cᶜ, C.card := sum_le_sum fun _ _ ↦ degreeWithin_le_card G C _
      _ = _ := by simp only [sum_const, smul_eq_mul, card_compl, Nat.mul_comm]
  omega

lemma two_clique_join_count_le_even_formula (n d a q : ℕ) (ha : 2 ≤ a) (had : a < d)
    (hn : 2 * d + 2 ≤ n)
    (hq : q ≤ (d + 1 - a).choose 2 + (d + 1 - a) * (n - (d + 1 - a)) +
      a.choose 2 + a.choose 2) : q ≤ pathFormula n (2 * d + 2) := by
  rw [pathFormula_even]
  apply le_trans ?_ (le_max_right _ _)
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have had' : (a : ℚ) < d := by exact_mod_cast had
  have hn' : (2 : ℚ) * d + 2 ≤ n := by exact_mod_cast hn
  have hs : ((d + 1 - a : ℕ) : ℚ) = d + 1 - a := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hns : ((n - (d + 1 - a) : ℕ) : ℚ) = n - (d + 1 - a) := by
    rw [Nat.cast_sub (by omega), hs]
  have hd₁ : ((d - 1 : ℕ) : ℚ) = d - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hnd : ((n - d + 1 : ℕ) : ℚ) = n - d + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  have hcS := Nat.cast_choose_two ℚ (d + 1 - a)
  have hcA := Nat.cast_choose_two ℚ a
  have hcD := Nat.cast_choose_two ℚ (d - 1)
  rw [hs] at hcS
  rw [hd₁] at hcD
  have hq' : (q : ℚ) ≤ ((d + 1 - a).choose 2 : ℚ) +
      (d + 1 - a : ℕ) * (n - (d + 1 - a) : ℕ) + (a.choose 2 : ℚ) + (a.choose 2 : ℚ) := by
    exact_mod_cast hq
  rw [hs, hns] at hq'
  have hm := mul_nonneg (show (0 : ℚ) ≤ a - 2 by linarith)
    (show (0 : ℚ) ≤ 2 * n - 2 * d - a - 3 by linarith)
  have h : (q : ℚ) ≤ ((d - 1).choose 2 : ℚ) +
      (d - 1 : ℕ) * (n - d + 1 : ℕ) + 2 := by
    rw [hd₁, hnd]
    nlinarith
  exact_mod_cast h

lemma two_clique_join_cone_count (n d a q : ℕ) (ha : a ≤ d) (hn : 2 * d + 2 ≤ n)
    (hq : q + n ≤ (d + 2 - a).choose 2 + (d + 2 - a) * (n + 1 - (d + 2 - a)) +
      a.choose 2 + a.choose 2) :
    q ≤ (d + 1 - a).choose 2 + (d + 1 - a) * (n - (d + 1 - a)) +
      a.choose 2 + a.choose 2 := by
  let s := d + 1 - a
  have hs : s ≤ n := by dsimp only [s]; omega
  have hds : d + 2 - a = s + 1 := by dsimp only [s]; omega
  have hc : (s + 1).choose 2 = s.choose 2 + s := by
    simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.choose_one_right, Nat.add_comm]
      using Nat.choose_succ_succ s 1
  rw [hds, hc, show n + 1 - (s + 1) = n - s by omega] at hq
  have hns := Nat.sub_add_cancel hs
  change q ≤ s.choose 2 + s * (n - s) + a.choose 2 + a.choose 2
  nlinarith

end Erdos1105

#print axioms Erdos1105.two_clique_join_edge_bound
#print axioms Erdos1105.two_clique_join_count_le_even_formula
