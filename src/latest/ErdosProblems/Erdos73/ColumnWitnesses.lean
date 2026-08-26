/- Actual column-intersection witnesses, retained under minor composition. -/
import ErdosProblems.Erdos73.TangleControl
import ErdosProblems.Erdos73.ContractColumns

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

variable {U W V I J : Type*}

theorem mem_gridRowSupport {G : SimpleGraph V} {g : ℕ}
    (M : MinorModel (squareGrid g) G) (r : Fin g) (v : V) :
    v ∈ gridRowSupport M r ↔ ∃ c : Fin g, v ∈ M.branchSet (r, c) := by
  simp only [gridRowSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- The support in the host of a specified finite set of pattern vertices. -/
def minorSupport {H : SimpleGraph W} {G : SimpleGraph V}
    (M : MinorModel H G) (S : Finset W) : Finset V := S.biUnion M.branchSet

@[simp] theorem mem_minorSupport {H : SimpleGraph W} {G : SimpleGraph V}
    (M : MinorModel H G) (S : Finset W) (v : V) :
    v ∈ minorSupport M S ↔ ∃ w ∈ S, v ∈ M.branchSet w := Finset.mem_biUnion

theorem mem_minorSupport_trans {F : SimpleGraph U} {H : SimpleGraph W}
    {G : SimpleGraph V} (M : MinorModel F H) (N : MinorModel H G)
    {S : Finset U} {w : W} {v : V} (hw : w ∈ minorSupport M S)
    (hv : v ∈ N.branchSet w) : v ∈ minorSupport (M.trans N) S := by
  obtain ⟨u, huS, hwu⟩ := (mem_minorSupport M S w).mp hw
  exact (mem_minorSupport _ _ _).mpr ⟨u, huS,
    (MinorModel.mem_composeBranchSet M N u v).mpr ⟨w, hwu, hv⟩⟩

/-- At least `k` distinct labelled columns meet the specified host set. -/
def HitsColumns (Q : I → Finset V) (S : Finset V) (k : ℕ) : Prop :=
  ∃ indices : Finset I, k ≤ indices.card ∧ ∀ i ∈ indices, ∃ v ∈ Q i, v ∈ S

theorem hitsColumns_of_embedding {Q : I → Finset V} {S : Finset V} {k : ℕ}
    (e : Fin k ↪ I) (h : ∀ j, ∃ v ∈ Q (e j), v ∈ S) : HitsColumns Q S k := by
  refine ⟨Finset.univ.map e, by simp only [Finset.card_map, Finset.card_univ,
    Fintype.card_fin, le_refl], ?_⟩
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  exact h j

theorem HitsColumns.mono {Q : I → Finset V} {S T : Finset V} {k : ℕ}
    (h : HitsColumns Q S k) (hST : S ⊆ T) : HitsColumns Q T k := by
  obtain ⟨indices, hcard, hhit⟩ := h
  refine ⟨indices, hcard, fun i hi => ?_⟩
  obtain ⟨v, hvQ, hvS⟩ := hhit i hi
  exact ⟨v, hvQ, hST hvS⟩

theorem HitsColumns.reindex {Q : I → Finset V} {R : J → Finset V}
    {S : Finset V} {k : ℕ} (h : HitsColumns Q S k) (e : I ↪ J)
    (he : ∀ i, Q i ⊆ R (e i)) : HitsColumns R S k := by
  obtain ⟨indices, hcard, hhit⟩ := h
  refine ⟨indices.map e, by simpa only [Finset.card_map] using hcard, ?_⟩
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
  obtain ⟨v, hvQ, hvS⟩ := hhit i hi
  exact ⟨v, he i hvQ, hvS⟩

/-- Every chosen hit lifts in the actual union of branch sets. -/
theorem HitsColumns.trans {F : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}
    (M : MinorModel F H) (N : MinorModel H G)
    {Q : I → Finset W} {R : I → Finset V} {S : Finset U} {k : ℕ}
    (hhit : HitsColumns Q (minorSupport M S) k)
    (hlift : ∀ i w, w ∈ Q i → ∃ v ∈ R i, v ∈ N.branchSet w) :
    HitsColumns R (minorSupport (M.trans N) S) k := by
  obtain ⟨indices, hcard, hhit⟩ := hhit
  refine ⟨indices, hcard, fun i hi => ?_⟩
  obtain ⟨w, hwQ, hwS⟩ := hhit i hi
  obtain ⟨u, huS, hwu⟩ := (mem_minorSupport M S w).mp hwS
  obtain ⟨v, hvR, hvN⟩ := hlift i w hwQ
  refine ⟨v, hvR, (mem_minorSupport _ _ _).mpr ⟨u, huS, ?_⟩⟩
  exact (MinorModel.mem_composeBranchSet M N u v).mpr ⟨w, hwu, hvN⟩

theorem gridRowSupport_eq_minorSupport {G : SimpleGraph V} {g : ℕ}
    (M : MinorModel (squareGrid g) G) (r : Fin g) :
    gridRowSupport M r = minorSupport M (productRow r) := by
  ext v
  simp only [gridRowSupport, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_minorSupport, Prod.exists, mem_productRow]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨r, c, rfl, hc⟩
  · rintro ⟨s, c, hs, hc⟩
    exact ⟨c, hs ▸ hc⟩

def ColumnRichGrid (G : SimpleGraph V) (Q : I → Finset V) (g : ℕ) : Prop :=
  ∃ M : MinorModel (squareGrid g) G,
    ∀ r : Fin g, HitsColumns Q (gridRowSupport M r) (2 * g)

def ColumnRichBipartite (G : SimpleGraph V) (Q : I → Finset V) (h k : ℕ) : Prop :=
  ∃ M : MinorModel (completeBipartiteGraph (Fin h) (Fin h)) G,
    ∀ r : Fin h, HitsColumns Q (M.branchSet (.inl r)) k

theorem ColumnRichGrid.trans {H : SimpleGraph W} {G : SimpleGraph V}
    {Q : I → Finset W} {R : I → Finset V} {g : ℕ}
    (h : ColumnRichGrid H Q g) (N : MinorModel H G)
    (hlift : ∀ i w, w ∈ Q i → ∃ v ∈ R i, v ∈ N.branchSet w) :
    ColumnRichGrid G R g := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M.trans N, fun r => ?_⟩
  have hr := hM r
  rw [gridRowSupport_eq_minorSupport] at hr ⊢
  exact hr.trans M N hlift

theorem ColumnRichBipartite.trans {H : SimpleGraph W} {G : SimpleGraph V}
    {Q : I → Finset W} {R : I → Finset V} {h k : ℕ}
    (hh : ColumnRichBipartite H Q h k) (N : MinorModel H G)
    (hlift : ∀ i w, w ∈ Q i → ∃ v ∈ R i, v ∈ N.branchSet w) :
    ColumnRichBipartite G R h k := by
  obtain ⟨M, hM⟩ := hh
  refine ⟨M.trans N, fun r => ?_⟩
  have hr : HitsColumns Q (minorSupport M {Sum.inl r}) k := by
    simpa only [minorSupport, Finset.singleton_biUnion] using hM r
  simpa only [minorSupport, Finset.singleton_biUnion] using hr.trans M N hlift

theorem ColumnRichGrid.reindex {G : SimpleGraph V} {Q : I → Finset V}
    {R : J → Finset V} {g : ℕ} (h : ColumnRichGrid G Q g)
    (e : I ↪ J) (he : ∀ i, Q i ⊆ R (e i)) : ColumnRichGrid G R g := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun r => (hM r).reindex e he⟩

theorem ColumnRichBipartite.reindex {G : SimpleGraph V} {Q : I → Finset V}
    {R : J → Finset V} {h k : ℕ} (hh : ColumnRichBipartite G Q h k)
    (e : I ↪ J) (he : ∀ i, Q i ⊆ R (e i)) : ColumnRichBipartite G R h k := by
  obtain ⟨M, hM⟩ := hh
  exact ⟨M, fun r => (hM r).reindex e he⟩

/-- Every row of the parity grid copy contains a left bipartite vertex,
including the one-vertex grid. Its full branch retains the witnesses. -/
theorem ColumnRichBipartite.toGrid {G : SimpleGraph V} {Q : I → Finset V} {g : ℕ}
    (h : ColumnRichBipartite G Q (g * g + 1) (2 * g)) : ColumnRichGrid G Q g := by
  obtain ⟨M, hM⟩ := h
  let f := squareGridCopyCompleteBipartite g
  let N := (MinorModel.of_copy f).trans M
  refine ⟨N, fun r => ?_⟩
  let c : Fin g := ⟨r.val % 2, (Nat.mod_le _ _).trans_lt r.isLt⟩
  let i : Fin (g * g + 1) := (finProdFinEquiv (r, c)).castSucc
  have hp : (r.val + c.val) % 2 = 0 := by
    change (r.val + r.val % 2) % 2 = 0
    omega
  have hf : f (r, c) = Sum.inl i := by
    change (if (r.val + c.val) % 2 = 0 then Sum.inl i else Sum.inr i) = Sum.inl i
    rw [if_pos hp]
  apply (hM i).mono
  intro v hv
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_univ _, ?_⟩
  exact (MinorModel.mem_composeBranchSet (MinorModel.of_copy f) M (r, c) v).mpr
    ⟨Sum.inl i, by rw [← hf]; exact Finset.mem_singleton_self _, hv⟩

end
end Erdos73
