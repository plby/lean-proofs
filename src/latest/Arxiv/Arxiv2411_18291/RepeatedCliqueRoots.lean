import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness

/-!
# Repeated clique roots in the absorber construction

A bounded clique boundary controls every edge chosen inside each clique,
even when each clique occurs a bounded number of times. Bounded edge
multiplicity also gives a constant bound on the number of root cliques
sharing an edge with a specified root. These are the two input bounds
needed for the splitting process and its private-vertex restrictions.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {q r : ℕ}

omit [Fintype V] in
theorem repeated_clique_degree_le (D : Finset (Block V q)) (Q : I → Block V q)
    (hQ : ∀ i, Q i ∈ D) {C : ℕ}
    (hrep : ∀ P, (univ.filter fun i => Q i = P).card ≤ C) (S : Finset V) :
    familyDegree Q S ≤ C * (D.filter fun P => S ⊆ P.val).card := by
  classical
  let s := univ.filter fun i => S ⊆ (Q i).val
  let d := D.filter fun P => S ⊆ P.val
  have hmap : ∀ i ∈ s, Q i ∈ d :=
    fun i hi => mem_filter.mpr ⟨hQ i, (mem_filter.mp hi).2⟩
  have hfiber : ∀ P ∈ d, (s.filter fun i => Q i = P).card ≤ C := by
    intro P _
    apply (card_le_card (filter_subset_filter _ (subset_univ s))).trans
    exact hrep P
  calc
    _ = ∑ P ∈ d, (s.filter fun i => Q i = P).card := card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _P ∈ d, C := sum_le_sum hfiber
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]; rfl

theorem face_clique_count_le_boundary_degree (hqr : r + 1 ≤ q)
    (D : Finset (Block V q)) (S : Block V r) :
    ((D.filter fun Q => S.val ⊆ Q.val).card : ℤ) ≤
      degree (boundary (r + 1) (indicator D)) S.val := by
  rw [degree_boundary (indicator D) S.val (by rw [S.property]; omega), degree_indicator,
    S.property, Nat.add_sub_cancel_left, Nat.choose_one_right]
  have hfactor : (1 : ℤ) ≤ (q - r : ℕ) := by exact_mod_cast (show 1 ≤ q - r by omega)
  have hcard : (0 : ℤ) ≤ (D.filter fun Q => S.val ⊆ Q.val).card := Nat.cast_nonneg _
  nlinarith

theorem IsCliqueFamilyBounded.repeated_edgeFamily (hqr : r + 1 ≤ q)
    {D : Finset (Block V q)} {θ : ℝ} (hD : IsCliqueFamilyBounded r D θ)
    (Q : I → Block V q) (hQ : ∀ i, Q i ∈ D) {C : ℕ} (hC : 0 < C)
    (hrep : ∀ P, (univ.filter fun i => Q i = P).card ≤ C)
    (E : I → Block V (r + 1)) (hEQ : ∀ i, (E i).val ⊆ (Q i).val) :
    IsEdgeFamilyBounded E (C * θ) := by
  intro S
  have hsub : familyDegree E S.val ≤ familyDegree Q S.val := by
    apply card_le_card
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hi).2).trans (hEQ i)⟩
  have hcount : (familyDegree E S.val : ℝ) ≤
      (C : ℝ) * (D.filter fun P => S.val ⊆ P.val).card := by
    exact_mod_cast hsub.trans (repeated_clique_degree_le D Q hQ hrep S.val)
  have hdegree : ((D.filter fun P => S.val ⊆ P.val).card : ℝ) ≤
      ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) := by
    exact_mod_cast face_clique_count_le_boundary_degree hqr D S
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  calc
    _ ≤ _ := hcount
    _ < (C : ℝ) * (θ * Fintype.card V) :=
      mul_lt_mul_of_pos_left (hdegree.trans_lt (hD S)) hCpos
    _ = _ := (mul_assoc _ _ _).symm

def cliqueOverlapIndices (m : ℕ) (Q : I → Block V q) (P : Block V q) : Finset I :=
  univ.filter fun i => m ≤ ((Q i).val ∩ P.val).card

omit [Fintype V] in
theorem cliqueOverlapIndices_card_le [Finite V] (m : ℕ) (D : Finset (Block V q))
    (Q : I → Block V q) (hQ : ∀ i, Q i ∈ D) {C M : ℕ}
    (hrep : ∀ P, (univ.filter fun i => Q i = P).card ≤ C)
    (hmult : ∀ e : Block V m, (D.filter fun P => e.val ⊆ P.val).card ≤ M)
    (P : Block V q) : (cliqueOverlapIndices m Q P).card ≤ q.choose m * (C * M) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hsub : cliqueOverlapIndices m Q P ⊆
      (cliqueEdges m P).biUnion (fun e => univ.filter fun i => e.val ⊆ (Q i).val) := by
    intro i hi
    obtain ⟨s, hs, hsm⟩ := exists_subset_card_eq (mem_filter.mp hi).2
    exact mem_biUnion.mpr ⟨⟨s, hsm⟩,
      (mem_cliqueEdges _ _).mpr (hs.trans inter_subset_right),
      mem_filter.mpr ⟨mem_univ _, hs.trans inter_subset_left⟩⟩
  calc
    _ ≤ ∑ e ∈ cliqueEdges m P, familyDegree Q e.val :=
      (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _e ∈ cliqueEdges m P, C * M := by
      apply sum_le_sum
      intro e _
      exact (repeated_clique_degree_le D Q hQ hrep e.val).trans
        (Nat.mul_le_mul_left C (hmult e))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_cliqueEdges, Nat.cast_id]

end Arxiv2411_18291
