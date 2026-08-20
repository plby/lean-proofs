import ErdosProblems.Erdos916.Core

/-!
# The four-vertex reduction for Erdős Problem 916

For the canonical `K23Reduction` certificate from `Erdos916.Core`, this file proves that
deleting its four degree-three vertices deletes exactly eight edges.  It also records the
small-order consequences used at the bottom of the density induction.
-/

open Finset

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace K23Reduction

/-- The graph induced on the vertices outside the four-vertex reduction set. -/
def remaining (R : K23Reduction G) : SimpleGraph {v // v ∉ R.deletedFour} :=
  G.induce {v | v ∉ R.deletedFour}

noncomputable instance remainingEdgeSetFintype (R : K23Reduction G) :
    Fintype R.remaining.edgeSet :=
  Fintype.ofFinite _

/-- A wheel in the graph left after the reduction is a wheel in the ambient graph. -/
theorem wheel_of_remaining (R : K23Reduction G)
    [DecidableRel R.remaining.Adj]
    (h : HasWheelWitness R.remaining) : HasWheelWitness G := by
  have h' : HasWheelWitness (G.induce {v : V | v ∉ R.deletedFour}) := by
    apply (HasWheelWitness.decidableRel_iff R.remaining _ _).mp
    exact h
  exact HasWheelWitness.induce {v : V | v ∉ R.deletedFour} h'

private lemma card_deleteIncidenceSet_add_degree (H : SimpleGraph V) [DecidableRel H.Adj]
    (v : V) :
    #(H.deleteIncidenceSet v).edgeFinset + H.degree v = #H.edgeFinset := by
  rw [H.edgeFinset_deleteIncidenceSet_eq_sdiff v, ← H.card_incidenceFinset_eq_degree v]
  exact card_sdiff_add_card_eq_card (H.incidenceFinset_subset v)

private lemma a_zero_ne_a_one (R : K23Reduction G) : R.a 0 ≠ R.a 1 :=
  R.vertex_injective.ne (by simp)

private lemma a_ne_b (R : K23Reduction G) (i : Fin 2) (j : Fin 3) :
    R.a i ≠ R.b j :=
  R.vertex_injective.ne (by simp)

private lemma b_zero_ne_b_one (R : K23Reduction G) :
    R.b (firstTwo 0) ≠ R.b (firstTwo 1) :=
  R.vertex_injective.ne (by simp [firstTwo])

/-- Deleting the four selected vertices removes exactly eight edges. -/
theorem card_remaining_add_eight (R : K23Reduction G) :
    #R.remaining.edgeFinset + 8 = #G.edgeFinset := by
  let a₀ := R.a 0
  let a₁ := R.a 1
  let b₀ := R.b (firstTwo 0)
  let b₁ := R.b (firstTwo 1)
  let G₁ := G.deleteIncidenceSet a₀
  let G₂ := G₁.deleteIncidenceSet a₁
  let G₃ := G₂.deleteIncidenceSet b₀
  let G₄ := G₃.deleteIncidenceSet b₁
  have ha_ne : a₀ ≠ a₁ := R.a_zero_ne_a_one
  have hab₀ : G.Adj a₀ b₀ := R.adj_a_b 0 (firstTwo 0)
  have hab₁ : G.Adj a₀ b₁ := R.adj_a_b 0 (firstTwo 1)
  have ha₁b₀ : G.Adj a₁ b₀ := R.adj_a_b 1 (firstTwo 0)
  have ha₁b₁ : G.Adj a₁ b₁ := R.adj_a_b 1 (firstTwo 1)
  have ha₀b₀ : a₀ ≠ b₀ := R.a_ne_b 0 (firstTwo 0)
  have ha₀b₁ : a₀ ≠ b₁ := R.a_ne_b 0 (firstTwo 1)
  have ha₁b₀ne : a₁ ≠ b₀ := R.a_ne_b 1 (firstTwo 0)
  have ha₁b₁ne : a₁ ≠ b₁ := R.a_ne_b 1 (firstTwo 1)
  have hb_ne : b₀ ≠ b₁ := R.b_zero_ne_b_one
  have hdeg₂ : G₁.degree a₁ = 3 := by
    rw [degree_deleteIncidenceSet_of_not_adj (R.not_adj_a_a 1 0) ha_ne.symm,
      R.degree_left]
  have hdeg₃ : G₂.degree b₀ = 1 := by
    have h₁ : G₁.degree b₀ = 2 := by
      rw [degree_deleteIncidenceSet_of_adj hab₀.symm, R.degree_right]
    have hadj : G₁.Adj b₀ a₁ := by
      simp only [G₁, deleteIncidenceSet_adj]
      exact ⟨ha₁b₀.symm, ha₀b₀.symm, ha_ne.symm⟩
    rw [degree_deleteIncidenceSet_of_adj hadj, h₁]
  have hdeg₄ : G₃.degree b₁ = 1 := by
    have h₁ : G₁.degree b₁ = 2 := by
      rw [degree_deleteIncidenceSet_of_adj hab₁.symm, R.degree_right]
    have hadj : G₁.Adj b₁ a₁ := by
      simp only [G₁, deleteIncidenceSet_adj]
      exact ⟨ha₁b₁.symm, ha₀b₁.symm, ha_ne.symm⟩
    have h₂ : G₂.degree b₁ = 1 := by
      rw [degree_deleteIncidenceSet_of_adj hadj, h₁]
    have hnon : ¬G₂.Adj b₁ b₀ := by
      intro h
      simp only [G₂, G₁, deleteIncidenceSet_adj] at h
      exact R.not_adj_b_b (firstTwo 1) (firstTwo 0) h.1.1
    rw [degree_deleteIncidenceSet_of_not_adj hnon hb_ne.symm, h₂]
  have he₁ := card_deleteIncidenceSet_add_degree G a₀
  have he₂ := card_deleteIncidenceSet_add_degree G₁ a₁
  have he₃ := card_deleteIncidenceSet_add_degree G₂ b₀
  have he₄ := card_deleteIncidenceSet_add_degree G₃ b₁
  rw [R.degree_left] at he₁
  rw [hdeg₂] at he₂
  rw [hdeg₃] at he₃
  rw [hdeg₄] at he₄
  change #G₁.edgeFinset + 3 = #G.edgeFinset at he₁
  change #G₂.edgeFinset + 3 = #G₁.edgeFinset at he₂
  change #G₃.edgeFinset + 1 = #G₂.edgeFinset at he₃
  change #G₄.edgeFinset + 1 = #G₃.edgeFinset at he₄
  have hsupp : G₄.support ⊆ {v | v ∉ R.deletedFour} := by
    intro v hv hvdel
    rw [mem_support] at hv
    obtain ⟨w, hvw⟩ := hv
    simp only [G₄, G₃, G₂, G₁, deleteIncidenceSet_adj] at hvw
    rcases hvw with ⟨⟨⟨⟨-, hva₀, -⟩, hva₁, -⟩, hvb₀, -⟩, hvb₁, -⟩
    rw [R.mem_deletedFour_iff] at hvdel
    obtain ⟨i, rfl⟩ := hvdel
    rcases i with i | j
    · fin_cases i
      · exact hva₀ rfl
      · exact hva₁ rfl
    · fin_cases j
      · exact hvb₀ rfl
      · exact hvb₁ rfl
  have hind : G₄.induce {v | v ∉ R.deletedFour} = R.remaining := by
    simp only [remaining, G₄, G₃, G₂, G₁]
    rw [induce_deleteIncidenceSet_of_notMem, induce_deleteIncidenceSet_of_notMem,
      induce_deleteIncidenceSet_of_notMem, induce_deleteIncidenceSet_of_notMem]
    · simpa only [Set.mem_ofPred_eq, not_not] using R.a_mem_deletedFour 0
    · simpa only [Set.mem_ofPred_eq, not_not] using R.a_mem_deletedFour 1
    · simpa only [Set.mem_ofPred_eq, not_not] using R.b_firstTwo_mem_deletedFour 0
    · simpa only [Set.mem_ofPred_eq, not_not] using R.b_firstTwo_mem_deletedFour 1
  have hindCard :
      #(G₄.induce {v | v ∉ R.deletedFour}).edgeFinset = #R.remaining.edgeFinset := by
    calc
      #(G₄.induce {v | v ∉ R.deletedFour}).edgeFinset =
          (G₄.induce {v | v ∉ R.deletedFour}).edgeSet.ncard :=
        (Set.ncard_eq_toFinset_card' _).symm
      _ = R.remaining.edgeSet.ncard :=
        congrArg Set.ncard (congrArg SimpleGraph.edgeSet hind)
      _ = #R.remaining.edgeFinset := Set.ncard_eq_toFinset_card' _
  have hcard : #R.remaining.edgeFinset = #G₄.edgeFinset := by
    rw [← hindCard]
    exact G₄.card_edgeFinset_induce_of_support_subset hsupp
  rw [hcard]
  omega

/-- Instance-independent form of the exact eight-edge deletion. -/
theorem ncard_remaining_add_eight (R : K23Reduction G) :
    R.remaining.edgeSet.ncard + 8 = G.edgeSet.ncard := by
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  exact R.card_remaining_add_eight

/-- The remaining vertex type has exactly four fewer vertices. -/
theorem card_remaining_vertices (R : K23Reduction G) :
    Fintype.card {v // v ∉ R.deletedFour} = Fintype.card V - 4 := by
  rw [Fintype.card_subtype_compl]
  change Fintype.card V - R.deletedFour.card = Fintype.card V - 4
  rw [R.card_deletedFour]

/-- A reduction needs a sixth vertex: the third neighbor of a selected right vertex
lies outside the displayed induced `K₂,₃`. -/
theorem six_le_card (R : K23Reduction G) : 6 ≤ Fintype.card V := by
  let A : Finset V := {R.a 0, R.a 1}
  have hAcard : #A = 2 := by simp [A, R.a_zero_ne_a_one]
  have hAsub : A ⊆ G.neighborFinset (R.b (firstTwo 0)) := by
    intro x hx
    simp only [A, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simpa only [mem_neighborFinset] using (R.adj_a_b 0 (firstTwo 0)).symm
    · simpa only [mem_neighborFinset] using (R.adj_a_b 1 (firstTwo 0)).symm
  have hNcard : #(G.neighborFinset (R.b (firstTwo 0))) = 3 :=
    R.degree_right 0
  have hAss : A ⊂ G.neighborFinset (R.b (firstTwo 0)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hAsub, ?_⟩
    intro h
    have := congrArg Finset.card h
    omega
  obtain ⟨x, hxN, hxA⟩ := exists_of_ssubset hAss
  let D : Finset V := univ.map R.copy.toEmbedding
  have hDcard : #D = 5 := by simp [D]
  have hxD : x ∉ D := by
    intro hx
    change x ∈ univ.map R.copy.toEmbedding at hx
    rw [mem_map] at hx
    obtain ⟨i, -, hi⟩ := hx
    subst x
    rcases i with i | j
    · fin_cases i
      · exact hxA (by simp [A])
      · exact hxA (by simp [A])
    · apply R.not_adj_b_b (firstTwo 0) j
      simpa only [mem_neighborFinset, RelEmbedding.coe_toEmbedding] using hxN
  have hinsCard : #(insert x D) = 6 := by
    rw [card_insert_of_notMem hxD, hDcard]
  calc
    6 = #(insert x D) := hinsCard.symm
    _ ≤ #(univ : Finset V) := card_le_card (subset_univ _)
    _ = Fintype.card V := card_univ

/-- A five-vertex graph cannot carry the reduction certificate. -/
theorem card_ne_five (R : K23Reduction G) : Fintype.card V ≠ 5 := by
  intro h
  have := R.six_le_card
  omega

/-- With six vertices, only one edge can remain after the exact eight-edge deletion. -/
theorem edge_card_le_nine_of_card_eq_six (R : K23Reduction G)
    (hV : Fintype.card V = 6) : #G.edgeFinset ≤ 9 := by
  have hverts : Fintype.card {v // v ∉ R.deletedFour} = 2 := by
    rw [R.card_remaining_vertices, hV]
  have hbound := R.remaining.card_edgeFinset_le_card_choose_two
  rw [hverts] at hbound
  have hexact := R.card_remaining_add_eight
  norm_num at hbound
  omega

/-- With seven vertices, at most three edges can remain after the exact eight-edge deletion. -/
theorem edge_card_le_eleven_of_card_eq_seven (R : K23Reduction G)
    (hV : Fintype.card V = 7) : #G.edgeFinset ≤ 11 := by
  have hverts : Fintype.card {v // v ∉ R.deletedFour} = 3 := by
    rw [R.card_remaining_vertices, hV]
  have hbound := R.remaining.card_edgeFinset_le_card_choose_two
  rw [hverts] at hbound
  have hexact := R.card_remaining_add_eight
  norm_num at hbound
  omega

end K23Reduction

end Erdos916
