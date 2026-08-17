import ErdosProblems.Erdos182.Foundations
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Elementary graph reductions for Erdős Problem 182

This file contains the finite reductions which do not use the deep regular-subgraph
theorems.  All statements retain the witnesses (the cut, its two sides, and the support)
needed by the later quantitative arguments.
-/

open Finset

namespace Erdos182

open SimpleGraph
open scoped symmDiff

universe u

section Support

variable {V : Type u} [Fintype V] {G H : SimpleGraph V}

/-- Restricting a finite graph to its support loses neither edges nor degrees. -/
theorem induce_support_exact [DecidableRel G.Adj] :
    #(G.induce G.support).edgeFinset = #G.edgeFinset ∧
      ∀ v : G.support, (G.induce G.support).degree v = G.degree v := by
  exact ⟨G.card_edgeFinset_induce_support, G.degree_induce_support⟩

/-- A graph with an edge has nonempty support. -/
theorem support_nonempty_of_edgeFinset_nonempty [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : G.support.Nonempty := by
  rcases hG with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ v w =>
      have hadj : G.Adj v w := by simpa using he
      exact ⟨v, w, hadj⟩

/-- Every edge of a bipartite graph has one endpoint in each of the support-trimmed
parts.  Thus unused vertices may be removed from either displayed part without changing
the bipartition. -/
theorem IsBipartiteWith.trim_support {s t : Set V}
    (hG : G.IsBipartiteWith s t) :
    G.IsBipartiteWith (s ∩ G.support) (t ∩ G.support) := by
  refine ⟨hG.disjoint.mono (Set.inter_subset_left (s := s) (t := G.support))
    (Set.inter_subset_left (s := t) (t := G.support)), ?_⟩
  intro v w hvw
  rcases hG.mem_of_adj hvw with h | h
  · exact Or.inl ⟨⟨h.1, w, hvw⟩, ⟨h.2, v, hvw.symm⟩⟩
  · exact Or.inr ⟨⟨h.1, w, hvw⟩, ⟨h.2, v, hvw.symm⟩⟩

theorem IsBipartiteWith.trim_support_union {s t : Set V}
    (hG : G.IsBipartiteWith s t) :
    (s ∩ G.support) ∪ (t ∩ G.support) = G.support := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (Set.inter_subset_right (s := s) (t := G.support))
      (Set.inter_subset_right (s := t) (t := G.support))
  · intro v hv
    rcases SimpleGraph.isBipartiteWith_support_subset hG hv with hv | hv
    · exact Or.inl ⟨hv, by assumption⟩
    · exact Or.inr ⟨hv, by assumption⟩

/-- Orient a displayed bipartition so that the first side is the larger one. -/
theorem IsBipartiteWith.orient_larger_side {s t : Set V}
    (hG : G.IsBipartiteWith s t) :
    ∃ a b : Set V, G.IsBipartiteWith a b ∧ b.ncard ≤ a.ncard ∧
      ((a = s ∧ b = t) ∨ (a = t ∧ b = s)) := by
  by_cases h : t.ncard ≤ s.ncard
  · exact ⟨s, t, hG, h, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨t, s, hG.symm, Nat.le_of_lt (Nat.lt_of_not_ge h), Or.inr ⟨rfl, rfl⟩⟩

end Support

section BipartiteCut

variable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The spanning bipartite subgraph consisting of the edges crossing a finite cut. -/
def cutAt (s : Finset V) : SimpleGraph V :=
  G.between (↑s : Set V) ↑(Finset.univ \ s)

private instance (s : Finset V) : DecidableRel (cutAt G s).Adj := by
  dsimp [cutAt]
  infer_instance

private def toggle (s : Finset V) (v : V) : Finset V :=
  if v ∈ s then s.erase v else insert v s

@[simp] private lemma mem_toggle (s : Finset V) (v w : V) :
    w ∈ toggle s v ↔ (w ∈ s ↔ w ≠ v) := by
  by_cases hv : v ∈ s <;> by_cases hw : w = v <;> simp [toggle, hv, hw]

private lemma cutAt_le (s : Finset V) : cutAt G s ≤ G :=
  SimpleGraph.between_le

private lemma cutAt_isBipartiteWith (s : Finset V) :
    (cutAt G s).IsBipartiteWith (↑s : Set V) ↑(Finset.univ \ s) := by
  apply G.between_isBipartiteWith
  rw [Finset.coe_sdiff, Finset.coe_univ]
  exact disjoint_sdiff_self_right

private lemma cutAt_toggle_delete (s : Finset V) (v : V) :
    (cutAt G s).deleteIncidenceSet v =
      (cutAt G (toggle s v)).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, cutAt, SimpleGraph.between_adj]
  constructor <;> rintro ⟨hxy, hx, hy⟩ <;> refine ⟨?_, hx, hy⟩
  · refine ⟨hxy.1, ?_⟩
    simpa [hx, hy] using hxy.2
  · refine ⟨hxy.1, ?_⟩
    simpa [hx, hy] using hxy.2

private lemma degree_cutAt_add_degree_toggle (s : Finset V) (v : V) :
    (cutAt G s).degree v + (cutAt G (toggle s v)).degree v = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← card_neighborFinset_eq_degree, ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
    simp only [cutAt, SimpleGraph.between_adj, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, true_and, mem_toggle]
    by_cases hv : v ∈ s <;> by_cases hw : w ∈ s <;> simp_all
    all_goals
      intro hadj heq
      subst w
      exact G.loopless.irrefl v hadj
  · rw [Finset.disjoint_left]
    intro w hw hw'
    rw [SimpleGraph.mem_neighborFinset] at hw hw'
    simp only [cutAt, SimpleGraph.between_adj, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, true_and, mem_toggle] at hw hw'
    by_cases hv : v ∈ s <;> by_cases hws : w ∈ s <;> simp_all

/-- Every finite graph has a bipartite subgraph containing at least half of its edges.
The witness is a genuine cut of the original vertex set. -/
theorem exists_bipartite_cut_half :
    ∃ s : Finset V,
      (cutAt G s).IsBipartiteWith (↑s : Set V) ↑(Finset.univ \ s) ∧
      cutAt G s ≤ G ∧ #G.edgeFinset ≤ 2 * #(cutAt G s).edgeFinset := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset V))
    (fun s ↦ #(cutAt G s).edgeFinset) Finset.univ_nonempty
  have hsmax (s' : Finset V) :
      #(cutAt G s').edgeFinset ≤ #(cutAt G s).edgeFinset :=
    hs s' (Finset.mem_univ s')
  have hdegree (v : V) : G.degree v ≤ 2 * (cutAt G s).degree v := by
    let H := cutAt G s
    let H' := cutAt G (toggle s v)
    have hHdeg : H.degree v ≤ #H.edgeFinset := H.degree_le_card_edgeFinset v
    have hH'deg : H'.degree v ≤ #H'.edgeFinset := H'.degree_le_card_edgeFinset v
    have hdelete : H.deleteIncidenceSet v = H'.deleteIncidenceSet v := by
      exact cutAt_toggle_delete G s v
    have hedge : #H'.edgeFinset ≤ #H.edgeFinset := hsmax (toggle s v)
    have hdecomp : #(H.deleteIncidenceSet v).edgeFinset + H.degree v = #H.edgeFinset := by
      rw [H.card_edgeFinset_deleteIncidenceSet]
      exact Nat.sub_add_cancel hHdeg
    have hdecomp' : #(H'.deleteIncidenceSet v).edgeFinset + H'.degree v = #H'.edgeFinset := by
      rw [H'.card_edgeFinset_deleteIncidenceSet]
      exact Nat.sub_add_cancel hH'deg
    have hdeg' : H'.degree v ≤ H.degree v := by
      have hc : #(H.deleteIncidenceSet v).edgeFinset =
          #(H'.deleteIncidenceSet v).edgeFinset := by
        calc
          #(H.deleteIncidenceSet v).edgeFinset =
              (H.deleteIncidenceSet v).edgeSet.ncard :=
            (Set.ncard_eq_toFinset_card' _).symm
          _ = (H'.deleteIncidenceSet v).edgeSet.ncard :=
            congrArg (fun K : SimpleGraph V ↦ K.edgeSet.ncard) hdelete
          _ = #(H'.deleteIncidenceSet v).edgeFinset :=
            Set.ncard_eq_toFinset_card' _
      omega
    have hsum : H.degree v + H'.degree v = G.degree v :=
      degree_cutAt_add_degree_toggle G s v
    simpa [H, H'] using (show G.degree v ≤ 2 * H.degree v by omega)
  refine ⟨s, cutAt_isBipartiteWith G s, cutAt_le G s, ?_⟩
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ (Finset.univ : Finset V)) ↦ hdegree v
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  rw [(cutAt G s).sum_degrees_eq_twice_card_edges] at hsum
  omega

end BipartiteCut

section MinimumDegreeCore

variable {V : Type u} [Fintype V]

private noncomputable def edgeCount (G : SimpleGraph V) : ℕ := G.edgeSet.ncard

private noncomputable def supportCount (G : SimpleGraph V) : ℕ := G.support.ncard

private noncomputable def corePotential (d : ℕ) (G : SimpleGraph V) : ℤ :=
  2 * (edgeCount G : ℤ) - (d : ℤ) * supportCount G

private noncomputable def coreScore (bound d : ℕ) (G : SimpleGraph V) : ℤ :=
  ((bound + 1 : ℕ) : ℤ) * corePotential d G + edgeCount G

private lemma edgeCount_eq_card {G : SimpleGraph V} [DecidableRel G.Adj] :
    edgeCount G = #G.edgeFinset := by
  rw [edgeCount, SimpleGraph.edgeFinset]
  exact Set.ncard_eq_toFinset_card' G.edgeSet

private lemma supportCount_eq_card {G : SimpleGraph V} :
    supportCount G = G.support.ncard := rfl

/-- The usual deletion lemma: if a nonempty graph has average degree at least `d`,
then it has a nonempty subgraph whose minimum degree is at least `d / 2` (expressed
without rounding as `d ≤ 2 * degree`).  The returned graph lives on the original
vertex type; its support is the exact nonempty vertex set of the core. -/
theorem exists_minDegree_core (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hE : G.edgeFinset.Nonempty)
    (hdense : d * G.support.ncard ≤ 2 * #G.edgeFinset) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ H.edgeFinset.Nonempty ∧
      d * H.support.ncard ≤ 2 * #H.edgeFinset ∧
      ∀ v ∈ H.support, d ≤ 2 * H.degree v := by
  classical
  let B := #G.edgeFinset
  obtain ⟨H, hHG, hmax⟩ := by
    apply Finset.exists_max_image {H : SimpleGraph V | H ≤ G} (coreScore B d)
    exact ⟨G, by simp⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHGle : H ≤ G := by simpa using hHG
  have hHedges : #H.edgeFinset ≤ B := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHGle)
  have hGscore : coreScore B d G ≤ coreScore B d H :=
    hmax G (by simpa)
  have hGpotential : 0 ≤ corePotential d G := by
    rw [corePotential, edgeCount_eq_card, supportCount_eq_card]
    have hz : ((d * G.support.ncard : ℕ) : ℤ) ≤
        ((2 * #G.edgeFinset : ℕ) : ℤ) := by exact_mod_cast hdense
    push_cast at hz
    omega
  have hHpotential : corePotential d G ≤ corePotential d H := by
    by_contra hn
    have hgap : corePotential d H + 1 ≤ corePotential d G := by omega
    have hmul := mul_le_mul_of_nonneg_left hgap (show (0 : ℤ) ≤ B + 1 by positivity)
    rw [mul_add] at hmul
    rw [coreScore, coreScore, edgeCount_eq_card, edgeCount_eq_card] at hGscore
    dsimp [B] at hGscore hHedges hmul
    exact (not_lt_of_ge hGscore) (by omega)
  have hHdense : d * H.support.ncard ≤ 2 * #H.edgeFinset := by
    have hp : 0 ≤ corePotential d H := hGpotential.trans hHpotential
    rw [corePotential, edgeCount_eq_card, supportCount_eq_card] at hp
    have hz : ((d * H.support.ncard : ℕ) : ℤ) ≤
        ((2 * #H.edgeFinset : ℕ) : ℤ) := by
      push_cast at hp
      omega
    exact_mod_cast hz
  have hHnonempty : H.edgeFinset.Nonempty := by
    by_contra hn
    have hcard : #H.edgeFinset = 0 := Finset.not_nonempty_iff_eq_empty.mp hn ▸ rfl
    have hHbot : H = ⊥ := SimpleGraph.edgeFinset_eq_empty.mp (Finset.card_eq_zero.mp hcard)
    have hscoreGpos : 0 < coreScore B d G := by
      rw [coreScore, edgeCount_eq_card]
      have hBpos : 0 < B := Finset.card_pos.mpr hE
      positivity
    have hscoreHpos : 0 < coreScore B d H := hscoreGpos.trans_le hGscore
    subst H
    simpa [coreScore, corePotential, edgeCount, supportCount] using hscoreHpos
  refine ⟨H, inferInstance, hHGle, hHnonempty, hHdense, ?_⟩
  intro v hv
  by_contra hlow
  have hlow' : 2 * H.degree v < d := Nat.lt_of_not_ge hlow
  let H' := H.deleteIncidenceSet v
  have hH'le : H' ≤ G := by
    exact (SimpleGraph.deleteIncidenceSet_le H v).trans hHGle
  have hmax' : coreScore B d H' ≤ coreScore B d H :=
    hmax H' (by simpa using hH'le)
  have hedgeDel : #H'.edgeFinset + H.degree v = #H.edgeFinset := by
    rw [H.card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel (H.degree_le_card_edgeFinset v)
  have hsuppDel : H'.support.ncard + 1 ≤ H.support.ncard := by
    have hle : H'.support.ncard ≤ (H.support \ {v}).ncard :=
      Set.ncard_le_ncard (H.support_deleteIncidenceSet_subset v) (Set.toFinite _)
    have heq : (H.support \ {v}).ncard + 1 = H.support.ncard :=
      Set.ncard_sdiff_singleton_add_one hv (Set.toFinite _)
    omega
  have hpotential : corePotential d H < corePotential d H' := by
    rw [corePotential, corePotential, edgeCount_eq_card, edgeCount_eq_card,
      supportCount_eq_card, supportCount_eq_card]
    have hedgeZ : (#H'.edgeFinset : ℤ) + H.degree v = #H.edgeFinset := by
      exact_mod_cast hedgeDel
    have hsuppZ : (H'.support.ncard : ℤ) + 1 ≤ H.support.ncard := by
      exact_mod_cast hsuppDel
    have hlowZ : 2 * (H.degree v : ℤ) < d := by exact_mod_cast hlow'
    have hmulS := mul_le_mul_of_nonneg_left hsuppZ (show (0 : ℤ) ≤ d by positivity)
    push_cast at hmulS
    nlinarith
  have hH'edges : #H'.edgeFinset ≤ B := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hH'le)
  rw [coreScore, coreScore, edgeCount_eq_card, edgeCount_eq_card] at hmax'
  have hBnonneg : (0 : ℤ) ≤ B := by positivity
  have hgap : corePotential d H + 1 ≤ corePotential d H' := by omega
  have hmul := mul_le_mul_of_nonneg_left hgap (show (0 : ℤ) ≤ B + 1 by positivity)
  rw [mul_add] at hmul
  push_cast at hmax' hmul
  exact (not_lt_of_ge hmax') (by
    have hHcast : (#H.edgeFinset : ℤ) ≤ B := by exact_mod_cast hHedges
    have hH'cast : (0 : ℤ) ≤ #H'.edgeFinset := by positivity
    omega)

/-- The support form of `exists_minDegree_core`: the induced graph on the returned
nonempty set has exactly the same edges and satisfies the rounded minimum-degree bound. -/
theorem exists_induced_minDegree_core (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hE : G.edgeFinset.Nonempty)
    (hdense : d * G.support.ncard ≤ 2 * #G.edgeFinset) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, ∃ hne : H.support.Nonempty,
      H ≤ G ∧ #(H.induce H.support).edgeFinset = #H.edgeFinset ∧
      d ≤ 2 * (H.induce H.support).minDegree := by
  obtain ⟨H, inst, hHG, hHE, -, hdeg⟩ := exists_minDegree_core G d hE hdense
  letI : DecidableRel H.Adj := inst
  have hsupp : H.support.Nonempty := support_nonempty_of_edgeFinset_nonempty hHE
  letI : Nonempty H.support := hsupp.to_subtype
  refine ⟨H, inst, hsupp, hHG, H.card_edgeFinset_induce_support, ?_⟩
  obtain ⟨v, hv⟩ := (H.induce H.support).exists_minimal_degree_vertex
  rw [hv, H.degree_induce_support]
  exact hdeg v v.property

end MinimumDegreeCore

section Trim

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Independently keep exactly `r` neighbors at every vertex in the left part of a
bipartite graph.  Because every edge has a unique left endpoint, these choices are
compatible and define a simple subgraph. -/
theorem exists_left_degree_trim [DecidableRel G.Adj]
    {s t : Set V} (hG : G.IsBipartiteWith s t) (r : ℕ)
    (hr : ∀ v ∈ s, r ≤ G.degree v) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧ H.IsBipartiteWith s t ∧
      ∀ v ∈ s, H.degree v = r := by
  classical
  have hex : ∀ (v : V) (hv : v ∈ s),
      ∃ N : Finset V, N ⊆ G.neighborFinset v ∧ #N = r := by
    intro v hv
    exact Finset.exists_subset_card_eq (hr v hv)
  choose N hNG hNcard using hex
  let N' : V → Finset V := fun v ↦ if hv : v ∈ s then N v hv else ∅
  let H : SimpleGraph V :=
    { Adj := fun v w ↦ G.Adj v w ∧
        ((v ∈ s ∧ w ∈ N' v) ∨ (w ∈ s ∧ v ∈ N' w))
      symm := ⟨fun v w hvw ↦ ⟨G.symm.symm v w hvw.1, hvw.2.symm⟩⟩
      loopless := ⟨fun v hv ↦ G.loopless.irrefl v hv.1⟩ }
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hle : H ≤ G := fun _ _ h ↦ h.1
  have hbip : H.IsBipartiteWith s t := by
    refine ⟨hG.disjoint, ?_⟩
    intro v w hvw
    exact hG.mem_of_adj (hle hvw)
  refine ⟨H, inferInstance, hle, hbip, ?_⟩
  intro v hv
  have hNv : N' v = N v hv := by simp [N', hv]
  have hneighbor : H.neighborFinset v = N' v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    constructor
    · intro hw
      have hwG : G.Adj v w := hw.1
      rcases hw.2 with hw | hw
      · exact hw.2
      · have hwt : w ∈ t := hG.mem_of_mem_adj hv hwG
        exact (Set.disjoint_left.1 hG.disjoint hw.1 hwt).elim
    · intro hw
      have hwN : w ∈ N v hv := by simpa [hNv] using hw
      have hwG : G.Adj v w := by simpa using hNG v hv hwN
      exact ⟨hwG, Or.inl ⟨hv, hw⟩⟩
  rw [← card_neighborFinset_eq_degree, hneighbor, hNv, hNcard]

end Trim

end Erdos182
