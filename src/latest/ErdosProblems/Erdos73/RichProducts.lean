/- Column-rich grid and complete bipartite models from repeated products. -/
import ErdosProblems.Erdos73.PairedGrid

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph SimpleGraph

variable {W V I : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}

/-- The product argument retains `2*g` distinct column witnesses in each
grid row, or in each left branch of the bipartite model. -/
theorem product_has_columnRich_grid_or_bipartite
    (hH : H.Connected) (g h n : ℕ) (hh : 0 < h)
    (hsize : h ^ (2 * g) < Fintype.card W) (hgn : 2 * g ≤ n) (hhn : h ≤ n)
    (N : MinorModel (H □ pathGraph n) G) (Q : I → Finset V) (c : Fin n ↪ I)
    (hhit : ∀ w j, ∃ v ∈ Q (c j), v ∈ N.branchSet (w, j)) :
    ColumnRichGrid G Q g ∨ ColumnRichBipartite G Q h (2 * g) := by
  have hbound : (h - 1 + 1) ^ (2 * g) < Fintype.card W := by
    simpa only [Nat.sub_add_cancel hh] using hsize
  let e : Fin (2 * g) ↪ I :=
    (⟨Fin.castLE hgn, Fin.castLE_injective hgn⟩ : Fin (2 * g) ↪ Fin n).trans c
  rcases exists_longPath_or_large_degree H hH (h - 1) (2 * g) hbound with
    ⟨u, v, P, hP, hlen⟩ | ⟨center, hdeg⟩
  · let row := hP.pathGraphCopy.comp (pathGraphCopyOfLE (show g ≤ P.length + 1 by omega))
    let f := boxProdCopy row (pathGraphCopyOfLE hgn)
    let L := (MinorModel.of_copy f).trans N
    let M := (pairedGridMinorModel g).trans L
    refine Or.inl ⟨M, fun r => hitsColumns_of_embedding e (fun j => ?_)⟩
    obtain ⟨x, hxQ, hxN⟩ := hhit (row r) (Fin.castLE hgn j)
    refine ⟨x, hxQ, ?_⟩
    have hxL : x ∈ L.branchSet (r, j) :=
      (MinorModel.mem_composeBranchSet (MinorModel.of_copy f) N (r, j) x).mpr
        ⟨f (r, j), Finset.mem_singleton_self _, hxN⟩
    have hj := pairedGridMinorModel_row_covers r j
    rw [gridRowSupport_eq_minorSupport] at hj ⊢
    exact mem_minorSupport_trans (pairedGridMinorModel g) L hj hxL
  · have hcard : Fintype.card (Fin h) ≤ Fintype.card (H.neighborSet center) := by
      rw [Fintype.card_fin, H.card_neighborSet_eq_degree]
      omega
    let f : Fin h ↪ H.neighborSet center :=
      Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
    let leaf : Fin h ↪ W := f.trans (Function.Embedding.subtype _)
    let column : Fin h ↪ Fin n := ⟨Fin.castLE hhn, Fin.castLE_injective hhn⟩
    have hK : (pathGraph n).Connected := by
      have : Nonempty (Fin n) := ⟨⟨0, hh.trans_le hhn⟩⟩
      exact ⟨pathGraph_preconnected n⟩
    let L := completeBipartite_minorModel_of_star_product H (pathGraph n) hK
      center leaf column (fun i => (f i).2.symm)
    refine Or.inr ⟨L.trans N, fun r => hitsColumns_of_embedding e (fun j => ?_)⟩
    obtain ⟨x, hxQ, hxN⟩ := hhit (leaf r) (Fin.castLE hgn j)
    refine ⟨x, hxQ, ?_⟩
    exact (MinorModel.mem_composeBranchSet L N (.inl r) x).mpr
      ⟨(leaf r, Fin.castLE hgn j), mem_productRow.mpr rfl, hxN⟩

end
end Erdos73
