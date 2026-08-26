/- Consecutive equal-size blocks in a path graph. -/
import ErdosProblems.Erdos73.RootedPartition
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

theorem pathGraph_isAcyclic (n : ℕ) : (SimpleGraph.pathGraph n).IsAcyclic := by
  intro v p hp
  let S := p.support.toFinset
  have hS : S.Nonempty := ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  let w := S.max' hS
  have hw : w ∈ p.support := List.mem_toFinset.mp (Finset.max'_mem S hS)
  let c := p.rotate w hw
  have hc : c.IsCycle := hp.rotate hw
  have hmax (x : Fin n) (hx : x ∈ c.support) : x ≤ w :=
    Finset.le_max' S x (List.mem_toFinset.mpr ((p.mem_support_rotate_iff w hw).mp hx))
  have hs := hmax c.snd (c.getVert_mem_support 1)
  have ht := hmax c.penultimate (c.getVert_mem_support (c.length - 1))
  have hsa := SimpleGraph.pathGraph_adj.mp (c.adj_snd hc.not_nil)
  have hta := SimpleGraph.pathGraph_adj.mp (c.adj_penultimate hc.not_nil)
  apply hc.snd_ne_penultimate
  apply Fin.ext
  change c.snd.val ≤ w.val at hs
  change c.penultimate.val ≤ w.val at ht
  omega

theorem pathGraph_isTree (n : ℕ) (hn : 0 < n) : (SimpleGraph.pathGraph n).IsTree := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨⟨SimpleGraph.pathGraph_preconnected n⟩, pathGraph_isAcyclic n⟩

def pathBlockEmbedding {t s : ℕ} (i : Fin t) : Fin s ↪ Fin (t * s) :=
  ⟨fun j => finProdFinEquiv (i, j), fun j k h =>
    (Prod.mk.inj (finProdFinEquiv.injective h)).2⟩

def pathBlock {t s : ℕ} (i : Fin t) : Finset (Fin (t * s)) :=
  Finset.univ.map (pathBlockEmbedding (s := s) i)

theorem pathBlock_card {t s : ℕ} (i : Fin t) : (pathBlock (s := s) i).card = s := by
  simp only [pathBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem pathBlock_nonempty {t s : ℕ} (hs : 0 < s) (i : Fin t) :
    (pathBlock (s := s) i).Nonempty := by
  rw [← Finset.card_pos, pathBlock_card]
  exact hs

theorem pathBlock_disjoint {t s : ℕ} : Pairwise fun i j : Fin t =>
    Disjoint (pathBlock (s := s) i) (pathBlock (s := s) j) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hxi
  obtain ⟨b, _, hb⟩ := Finset.mem_map.mp hxj
  exact hij (Prod.mk.inj (finProdFinEquiv.injective (ha.trans hb.symm))).1

def pathBlockCopy {t s : ℕ} (i : Fin t) :
    (SimpleGraph.pathGraph s).Copy (SimpleGraph.pathGraph (t * s)) where
  toHom := {
    toFun := pathBlockEmbedding i
    map_rel' := by
      intro j k hjk
      apply SimpleGraph.pathGraph_adj.mpr
      have h := SimpleGraph.pathGraph_adj.mp hjk
      change j.val + s * i.val + 1 = k.val + s * i.val ∨
        k.val + s * i.val + 1 = j.val + s * i.val
      omega }
  injective' := (pathBlockEmbedding i).injective

theorem pathBlock_connected {t s : ℕ} (hs : 0 < s) (i : Fin t) :
    ((SimpleGraph.pathGraph (t * s)).induce (pathBlock (s := s) i : Set (Fin (t * s)))).Connected := by
  have : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have hc : ((SimpleGraph.pathGraph s).induce ((Finset.univ : Finset (Fin s)) : Set (Fin s))).Connected := by
    rw [Finset.coe_univ]
    exact ((SimpleGraph.pathGraph s).induceUnivIso.connected_iff).mpr
      ⟨SimpleGraph.pathGraph_preconnected _⟩
  exact connected_induce_map_copy (pathBlockCopy i) Finset.univ hc

end
end Erdos73
