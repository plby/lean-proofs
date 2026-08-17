import Mathlib

/-!
# The structured Alon--Bohman--Huang family

This file isolates the inexpensive induced graphs used in the proof of
Erdős Problem 807.  There are `r` left blocks of ten vertices and `90 * r`
right vertices.  A Boolean matrix says which complete block-to-vertex stars
are present.  We use a fixed equivalence with `Fin (100 * r)`, so different
matrices give different *labelled* graphs without quotienting presentations.
-/

namespace Erdos807
namespace StructuredFamily

/-- The Boolean incidence matrix of the construction. -/
abbrev Matrix (r : ℕ) := Fin r → Fin (90 * r) → Bool

/-- A convenient typed model of the `100 * r` vertices. -/
abbrev RawVertex (r : ℕ) := (Fin r × Fin 10) ⊕ Fin (90 * r)

/-- The canonical labelling of the typed model by `Fin (100 * r)`. -/
noncomputable def vertexEquiv (r : ℕ) : RawVertex r ≃ Fin (100 * r) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (Equiv.cast (by congr 1; omega)))

/-- The `j`th vertex of block `i`. -/
noncomputable def leftVertex (r : ℕ) (i : Fin r) (j : Fin 10) : Fin (100 * r) :=
  vertexEquiv r (Sum.inl (i, j))

/-- The right vertex with index `b`. -/
noncomputable def rightVertex (r : ℕ) (b : Fin (90 * r)) : Fin (100 * r) :=
  vertexEquiv r (Sum.inr b)

/-- The ten-element left block indexed by `i`. -/
def leftBlock (r : ℕ) (i : Fin r) : Set (Fin (100 * r)) :=
  {v | ∃ j : Fin 10, (vertexEquiv r).symm v = Sum.inl (i, j)}

/-- The right vertices selected by row `i` of `M`. -/
def rightSupport (M : Matrix r) (i : Fin r) : Set (Fin (100 * r)) :=
  {v | ∃ b : Fin (90 * r), (vertexEquiv r).symm v = Sum.inr b ∧ M i b = true}

@[simp] lemma leftVertex_mem_leftBlock (i : Fin r) (j : Fin 10) :
    leftVertex r i j ∈ leftBlock r i := by
  exact ⟨j, by simp [leftVertex]⟩

@[simp] lemma rightVertex_mem_rightSupport_iff (M : Matrix r) (i : Fin r)
    (b : Fin (90 * r)) :
    rightVertex r b ∈ rightSupport M i ↔ M i b = true := by
  simp [rightVertex, rightSupport]

@[simp] lemma rightVertex_not_mem_leftBlock (i : Fin r) (b : Fin (90 * r)) :
    rightVertex r b ∉ leftBlock r i := by
  rintro ⟨a, h⟩
  simp [rightVertex] at h

@[simp] lemma leftVertex_not_mem_rightSupport (M : Matrix r) (i j : Fin r)
    (a : Fin 10) : leftVertex r i a ∉ rightSupport M j := by
  rintro ⟨b, h, -⟩
  simp [leftVertex] at h

lemma leftBlock_disjoint_rightSupport (M : Matrix r) (i j : Fin r) :
    Disjoint (leftBlock r i) (rightSupport M j) := by
  rw [Set.disjoint_left]
  rintro v ⟨a, ha⟩ ⟨b, hb, -⟩
  rw [ha] at hb
  cases hb

lemma leftBlock_eq_index {i j : Fin r} {v : Fin (100 * r)}
    (hi : v ∈ leftBlock r i) (hj : v ∈ leftBlock r j) : i = j := by
  rcases hi with ⟨a, ha⟩
  rcases hj with ⟨b, hb⟩
  rw [ha] at hb
  exact congrArg Prod.fst (Sum.inl.inj hb)

@[simp] lemma leftVertex_ne_rightVertex (i : Fin r) (a : Fin 10)
    (b : Fin (90 * r)) : leftVertex r i a ≠ rightVertex r b := by
  intro h
  have h' := (vertexEquiv r).injective h
  simp at h'

/-- The complete bipartite graph belonging to one row of the matrix. -/
def piece (M : Matrix r) (i : Fin r) : SimpleGraph (Fin (100 * r)) :=
  SimpleGraph.between (leftBlock r i) (rightSupport M i) ⊤

/-- The labelled structured graph presented by `M`. -/
def graph (M : Matrix r) : SimpleGraph (Fin (100 * r)) :=
  ⨆ i, piece M i

lemma piece_isBipartiteWith (M : Matrix r) (i : Fin r) :
    (piece M i).IsBipartiteWith (leftBlock r i) (rightSupport M i) := by
  exact SimpleGraph.between_isBipartiteWith (leftBlock_disjoint_rightSupport M i i)

lemma piece_eq_completeBipartite (M : Matrix r) (i : Fin r) :
    piece M i = SimpleGraph.between (leftBlock r i) (rightSupport M i) ⊤ := rfl

@[simp] lemma piece_adj_left_right_iff (M : Matrix r) (i j : Fin r)
    (a : Fin 10) (b : Fin (90 * r)) :
    (piece M i).Adj (leftVertex r j a) (rightVertex r b) ↔
      i = j ∧ M i b = true := by
  rw [piece, SimpleGraph.between_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact ⟨leftBlock_eq_index h.1 (leftVertex_mem_leftBlock j a),
        (rightVertex_mem_rightSupport_iff M i b).1 h.2⟩
    · exact False.elim (rightVertex_not_mem_leftBlock i b h.2)
  · rintro ⟨rfl, hb⟩
    exact ⟨(leftVertex_ne_rightVertex i a b), Or.inl
      ⟨leftVertex_mem_leftBlock i a, (rightVertex_mem_rightSupport_iff M i b).2 hb⟩⟩

@[simp] lemma graph_adj_left_right_iff (M : Matrix r) (i : Fin r)
    (a : Fin 10) (b : Fin (90 * r)) :
    (graph M).Adj (leftVertex r i a) (rightVertex r b) ↔ M i b = true := by
  rw [graph, SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨j, hj⟩
    rcases (piece_adj_left_right_iff M j i a b).1 hj with ⟨rfl, hb⟩
    exact hb
  · intro hb
    exact ⟨i, (piece_adj_left_right_iff M i i a b).2 ⟨rfl, hb⟩⟩

theorem graph_injective (r : ℕ) : Function.Injective (graph : Matrix r → _) := by
  intro M N hMN
  funext i b
  apply Bool.eq_iff_iff.mpr
  exact calc
    M i b = true ↔ (graph M).Adj (leftVertex r i (0 : Fin 10)) (rightVertex r b) :=
      (graph_adj_left_right_iff M i (0 : Fin 10) b).symm
    _ ↔ (graph N).Adj (leftVertex r i (0 : Fin 10)) (rightVertex r b) := by rw [hMN]
    _ ↔ N i b = true := graph_adj_left_right_iff N i (0 : Fin 10) b

/-- The finite set of all labelled graphs in the canonical structured family. -/
noncomputable def graphs (r : ℕ) : Finset (SimpleGraph (Fin (100 * r))) :=
  by
    classical
    exact Finset.univ.image graph

lemma card_matrix (r : ℕ) : Fintype.card (Matrix r) = 2 ^ (90 * r * r) := by
  simp only [Matrix, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← pow_mul]

/-- Exact count of the canonical family: there is no presentation multiplicity. -/
theorem card_graphs (r : ℕ) : (graphs r).card = 2 ^ (90 * r * r) := by
  classical
  rw [graphs, Finset.card_image_of_injective _ (graph_injective r), Finset.card_univ,
    card_matrix]

lemma graph_mem_graphs (M : Matrix r) : graph M ∈ graphs r := by
  classical
  simp [graphs]

/-- Different rows produce edge-disjoint complete bipartite pieces. -/
lemma piece_disjoint {M : Matrix r} {i j : Fin r} (hij : i ≠ j) :
    Disjoint (piece M i) (piece M j) := by
  rw [disjoint_iff_inf_le]
  intro u v huv
  rw [SimpleGraph.inf_adj] at huv
  simp only [piece, SimpleGraph.between_adj, SimpleGraph.top_adj, ne_eq] at huv
  rw [SimpleGraph.bot_adj]
  rcases huv with ⟨⟨-, hi⟩, ⟨-, hj⟩⟩
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact hij (leftBlock_eq_index hi.1 hj.1)
  · exact (Set.disjoint_left.mp (leftBlock_disjoint_rightSupport M i j)) hi.1 hj.1
  · exact (Set.disjoint_left.mp (leftBlock_disjoint_rightSupport M j i)) hj.1 hi.1
  · exact hij (leftBlock_eq_index hi.2 hj.2)

/-- The displayed `r` pieces have supremum exactly the structured graph. -/
lemma graph_eq_iSup_piece (M : Matrix r) : graph M = ⨆ i, piece M i := rfl

/-- A completely explicit edge partition certificate with `r` indexed parts. -/
theorem exists_biclique_edge_partition (M : Matrix r) :
    ∃ P : Fin r → SimpleGraph (Fin (100 * r)),
      (∀ i, ∃ L R : Set (Fin (100 * r)), Disjoint L R ∧
        P i = SimpleGraph.between L R ⊤) ∧
      (∀ ⦃i j⦄, i ≠ j → Disjoint (P i) (P j)) ∧
      graph M = ⨆ i, P i := by
  refine ⟨piece M, ?_, ?_, rfl⟩
  · intro i
    exact ⟨leftBlock r i, rightSupport M i, leftBlock_disjoint_rightSupport M i i, rfl⟩
  · intro i j hij
    exact piece_disjoint hij

/-- Finset form of the same certificate.  Empty or duplicate pieces may collapse,
so the family uses *at most* `r` bicliques. -/
theorem exists_biclique_finset_partition (M : Matrix r) :
    ∃ P : Finset (SimpleGraph (Fin (100 * r))),
      P.card ≤ r ∧
      (∀ H ∈ P, ∃ L R : Set (Fin (100 * r)), Disjoint L R ∧
        H = SimpleGraph.between L R ⊤) ∧
      (∀ ⦃H K⦄, H ∈ P → K ∈ P → H ≠ K → Disjoint H K) ∧
      P.sup id = graph M := by
  classical
  let P := Finset.univ.image (piece M)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · dsimp [P]
    exact (Finset.card_image_le.trans_eq (Fintype.card_fin r))
  · intro H hH
    change H ∈ Finset.univ.image (piece M) at hH
    rcases Finset.mem_image.mp hH with ⟨i, -, rfl⟩
    exact ⟨leftBlock r i, rightSupport M i, leftBlock_disjoint_rightSupport M i i, rfl⟩
  · intro H K hH hK hne
    change H ∈ Finset.univ.image (piece M) at hH
    change K ∈ Finset.univ.image (piece M) at hK
    rcases Finset.mem_image.mp hH with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hK with ⟨j, -, rfl⟩
    have hij : i ≠ j := fun h ↦ hne (congrArg (piece M) h)
    exact piece_disjoint hij
  · change (Finset.univ.image (piece M)).sup id = graph M
    rw [Finset.sup_image]
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      exact le_iSup (piece M) i
    · rw [graph]
      apply iSup_le
      intro i
      exact Finset.le_sup (by simp)

end StructuredFamily
end Erdos807
