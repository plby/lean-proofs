/- Every selected column retains an actual intersection witness. -/
import ErdosProblems.Erdos73.RichProducts

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph SimpleGraph

variable {V I : Type*} {G : SimpleGraph V} {m n : ℕ}

theorem fullPregrill_has_grillModel_with_columns [Fintype V]
    (P : FullPregrill G m n) (hm : 0 < m) (hn : 0 < n) :
    ∃ H : SimpleGraph (Fin m × Fin n), IsGrill H ∧
      ∃ M : MinorModel H G, ∀ r j, ∃ v ∈ P.column j, v ∈ M.branchSet (r, j) := by
  cases n with
  | zero => omega
  | succ n =>
    let C := P.chooseColumnPartitions hm
    refine ⟨C.grillGraph, C.grillGraph_isGrill, C.minorModel, fun r j => ?_⟩
    exact ⟨P.first r j, P.first_mem_column r j, Finset.mem_union_left _
      (C.hull_subset j r (P.first_mem_rowHull r j))⟩

theorem grill_has_columnRich_grid_or_bipartite
    (F : SimpleGraph (Fin m × Fin n)) (hF : IsGrill F)
    (g h : ℕ) (hh : 0 < h) (hm : h ^ (2 * g) < m)
    (hn : max (2 * g) h * 2 ^ (m * m) ≤ n)
    (N : MinorModel F G) (Q : I → Finset V) (label : Fin n ↪ I)
    (hhit : ∀ r j, ∃ v ∈ Q (label j), v ∈ N.branchSet (r, j)) :
    ColumnRichGrid G Q g ∨ ColumnRichBipartite G Q h (2 * g) := by
  let b := max (2 * g) h
  have hb : 0 < b := hh.trans_le (Nat.le_max_right _ _)
  have hcard : Fintype.card (Finset (Fin m × Fin m)) * b ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_finset, Fintype.card_prod, Fintype.card_fin,
      Nat.mul_comm, b] using hn
  obtain ⟨S, hS⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (grillColumnCode F) hcard
  let J := Finset.univ.filter fun j => grillColumnCode F j = S
  have hJ : b ≤ J.card := hS
  let c : Fin b ↪o Fin n := J.orderEmbOfCardLe hJ
  have hcode (j : Fin b) : grillColumnCode F (c j) = S :=
    (Finset.mem_filter.mp (J.orderEmbOfCardLe_mem hJ j)).2
  let zero : Fin b := ⟨0, hb⟩
  let H := grillColumnGraph F (c zero)
  have hH : H.Connected := hF.2 (c zero)
  have hcolumns (j : Fin b) : H = grillColumnGraph F (c j) :=
    grillColumnGraph_eq_of_code_eq F ((hcode zero).trans (hcode j).symm)
  have hcol (j : Fin b) (r s : Fin m) (hrs : H.Adj r s) : F.Adj (r, c j) (s, c j) := by
    rw [hcolumns j] at hrs
    exact hrs
  let L := repeatedColumns_minorModel F H hF.1 c hcol
  apply product_has_columnRich_grid_or_bipartite hH g h b hh
    (by simpa only [Fintype.card_fin] using hm) (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    (L.trans N) Q (c.toEmbedding.trans label)
  intro r j
  obtain ⟨v, hvQ, hvN⟩ := hhit r (c j)
  exact ⟨v, hvQ, (MinorModel.mem_composeBranchSet L N (r, j) v).mpr
    ⟨(r, c j), column_mem_block c r j, hvN⟩⟩

theorem fullPregrill_has_columnRich_grid_or_bipartite [Fintype V]
    (P : FullPregrill G m n) (g h : ℕ) (hh : 0 < h)
    (hm : h ^ (2 * g) < m) (hn : max (2 * g) h * 2 ^ (m * m) ≤ n) :
    ColumnRichGrid G P.column g ∨ ColumnRichBipartite G P.column h (2 * g) := by
  have hmpos : 0 < m := (Nat.zero_le _).trans_lt hm
  have hnpos : 0 < n := (Nat.mul_pos (hh.trans_le (Nat.le_max_right _ _))
    (pow_pos (by omega) _)).trans_le hn
  obtain ⟨H, hH, N, hhit⟩ := fullPregrill_has_grillModel_with_columns P hmpos hnpos
  exact grill_has_columnRich_grid_or_bipartite H hH g h hh hm hn N P.column
    (Function.Embedding.refl _) hhit

theorem pregrill_has_columnRich_grid_or_bipartite [Fintype V]
    {d : ℕ} (P : Pregrill G m n d) (g h : ℕ) (hh : 0 < h)
    (hm : qualitativeGrillRows (2 * g) h ≤ m)
    (hd : 2 * qualitativeGrillRows (2 * g) h * d ≤ m)
    (hn : 2 * qualitativeGrillColumns (2 * g) h ≤ n) :
    ColumnRichGrid G P.column g ∨ ColumnRichBipartite G P.column h (2 * g) := by
  obtain ⟨F, c, hc⟩ := P.exists_fullPregrill_with_columns
    (qualitativeGrillRows (2 * g) h) (qualitativeGrillColumns (2 * g) h)
    (qualitativeGrillRows_pos _ _) hm hd hn
  rcases fullPregrill_has_columnRich_grid_or_bipartite F g h hh
      (Nat.lt_succ_self _) le_rfl with hg | hb
  · exact Or.inl (hg.reindex c.toEmbedding (fun j => (hc j).subset))
  · exact Or.inr (hb.reindex c.toEmbedding (fun j => (hc j).subset))

end
end Erdos73
