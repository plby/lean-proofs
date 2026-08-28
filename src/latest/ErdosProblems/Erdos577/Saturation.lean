import ErdosProblems.Erdos577.Blocks

/-! Finite maximal nonfactor extensions for the Erdős–Faudree proof. -/

namespace Erdos577

open Finset

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

/-- Every complete graph of order `4*k` has the required packing. -/
theorem hasPacking_top [Fintype V] (hcard : Fintype.card V = 4 * k) :
    HasPacking (⊤ : SimpleGraph V) k := by
  classical
  let e : Fin k × Fin 4 ≃ V := Fintype.equivOfCardEq (by simp [hcard, Nat.mul_comm])
  refine ⟨{
    vertices := e.toEmbedding
    adjacent := ?_ }⟩
  intro i j
  apply (SimpleGraph.top_adj _ _).mpr
  intro he
  have hj : j = j + 1 := (Prod.mk.inj (e.injective he)).2
  fin_cases j <;> simp at hj

lemma ne_top_of_noPacking [Fintype V] (hcard : Fintype.card V = 4 * k)
    (h : ¬HasPacking G k) : G ≠ ⊤ := by
  intro hG
  apply h
  rw [hG]
  exact hasPacking_top hcard

/-- Saturated means maximal among graphs with no specified quadrilateral packing. -/
def Saturated (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬HasPacking G k ∧ ∀ H : SimpleGraph V, G < H → HasPacking H k

lemma exists_nonedge (hG : G ≠ ⊤) : ∃ u v : V, u ≠ v ∧ ¬G.Adj u v := by
  classical
  by_contra! h
  apply hG
  ext u v
  simp only [SimpleGraph.top_adj]
  exact ⟨fun hadj ↦ hadj.ne, h u v⟩

lemma Saturated.hasPacking_add_edge (h : Saturated G k) {u v : V}
    (hne : u ≠ v) (hn : ¬G.Adj u v) : HasPacking (G ⊔ SimpleGraph.edge u v) k :=
  h.2 _ (G.lt_sup_edge u v hne hn)

/-- Choose a maximal nonfactor supergraph by its actual finite edge count. -/
theorem exists_saturated_extension [Finite V] (h : ¬HasPacking G k) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Saturated H k := by
  classical
  let := Fintype.ofFinite V
  let candidates : Finset (SimpleGraph V) :=
    univ.filter fun H ↦ G ≤ H ∧ ¬HasPacking H k
  have hn : candidates.Nonempty := ⟨G, by simp [candidates, h]⟩
  obtain ⟨H, hH, hmax⟩ := candidates.exists_max_image (fun H ↦ H.edgeFinset.card) hn
  have hp : G ≤ H ∧ ¬HasPacking H k := (mem_filter.mp hH).2
  refine ⟨H, hp.1, hp.2, ?_⟩
  intro J hHJ
  by_contra hnJ
  have hJ : J ∈ candidates := mem_filter.mpr ⟨mem_univ _, hp.1.trans hHJ.le, hnJ⟩
  have hle := hmax J hJ
  have hlt : H.edgeFinset.card < J.edgeFinset.card :=
    card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).mpr hHJ)
  exact (not_lt_of_ge hle) hlt

/-- Passing to the chosen supergraph cannot lower any of the degrees. -/
lemma minimum_degree_mono [Fintype V] [DecidableRel G.Adj] {H : SimpleGraph V}
    [DecidableRel H.Adj] (hGH : G ≤ H) (d : ℕ) (h : ∀ v, d ≤ G.degree v) :
    ∀ v, d ≤ H.degree v := by
  intro v
  exact (h v).trans (G.degree_le_of_le hGH)

end Erdos577
