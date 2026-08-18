/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SparseDegree
import ErdosProblems.Erdos570.SparseColoring

/-!
# Deleting a prescribed set of leaves

For a connected graph of order at least three, distinct leaves determine
distinct incident edges.  Deleting any set of leaves therefore removes at
least that many edges, and the remaining induced graph stays connected.
These facts let the sparse Ramsey argument delete a quantitatively chosen
set of leaves while retaining control of the cyclomatic excess.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- The induced code obtained by deleting the vertices in `L`. -/
def deleteLeavesCode (H : GraphCode) (L : Finset (Fin H.vertexCount)) :
    GraphCode :=
  inducedCode H (Finset.univ \ L)

@[simp] theorem deleteLeavesCode_vertexCount (H : GraphCode)
    (L : Finset (Fin H.vertexCount)) :
    (deleteLeavesCode H L).vertexCount = H.vertexCount - L.card := by
  rw [deleteLeavesCode, inducedCode_vertexCount,
    Finset.card_sdiff_of_subset (Finset.subset_univ L)]
  simp

theorem deleteLeavesCode_isContained (H : GraphCode)
    (L : Finset (Fin H.vertexCount)) :
    IsContained (deleteLeavesCode H L) H :=
  inducedCode_isContained H (Finset.univ \ L)

/-- Two leaves in a connected graph with at least three vertices cannot be
adjacent: otherwise their two-vertex component would be the whole graph. -/
theorem not_adj_of_leaves_of_connected
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    {v w : Fin H.vertexCount}
    (hv : H.graph.degree v = 1) (hw : H.graph.degree w = 1) :
    ¬ H.graph.Adj v w := by
  intro hvw
  have hvwne : v ≠ w := hvw.ne
  let S : Set (Fin H.vertexCount) := ({v} : Set (Fin H.vertexCount))ᶜ
  let wS : S := ⟨w, by simp [S, hvwne.symm]⟩
  have hdel : (H.graph.induce S).Connected := by
    simpa [S] using hconn.induce_compl_singleton_of_degree_eq_one hv
  have hexists : ∃ z : Fin H.vertexCount, z ≠ v ∧ z ≠ w := by
    by_contra h
    have huniv : (Finset.univ : Finset (Fin H.vertexCount)) ⊆ {v, w} := by
      intro z _
      by_cases hzv : z = v
      · simp [hzv]
      · have hzw : z = w := by
          by_contra hzw
          exact h ⟨z, hzv, hzw⟩
        simp [hzw]
    have hcard := Finset.card_le_card huniv
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have hpCard : ({v, w} : Finset (Fin H.vertexCount)).card ≤ 2 :=
      Finset.card_insert_le v {w}
    omega
  obtain ⟨z, hzv, hzw⟩ := hexists
  let zS : S := ⟨z, by simp [S, hzv]⟩
  have hwSzS : wS ≠ zS := by
    intro h
    exact hzw (congrArg Subtype.val h).symm
  haveI : Nontrivial S := ⟨⟨wS, zS, hwSzS⟩⟩
  have hpos : 0 < (H.graph.induce S).degree wS :=
    hdel.preconnected.degree_pos_of_nontrivial wS
  have hzero : (H.graph.induce S).degree wS = 0 := by
    by_contra hne
    have hpos' : 0 < (H.graph.induce S).degree wS := Nat.pos_of_ne_zero hne
    have hnotIso := ((H.graph.induce S).degree_pos wS).mp hpos'
    obtain ⟨y, hadj⟩ :=
      (H.graph.induce S).exists_adj_iff_not_isIsolated.mpr hnotIso
    have hwy : H.graph.Adj w y.1 := hadj
    obtain ⟨u, hwu, hunique⟩ :=
      (H.graph.degree_eq_one_iff_existsUnique_adj).mp hw
    have huv : u = v := (hunique v hvw.symm).symm
    have hyu : y.1 = u := hunique y.1 hwy
    have hyv : y.1 = v := hyu.trans huv
    exact y.2 (by simpa [S, hyv])
  omega

/-- Choose the unique edge incident with a leaf. -/
def leafEdge (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) (hv : H.graph.degree v = 1) : Sym2 (Fin H.vertexCount) :=
  s(v, Classical.choose
    ((H.graph.degree_eq_one_iff_existsUnique_adj).mp hv))

theorem leafEdge_mem_edgeFinset
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) (hv : H.graph.degree v = 1) :
    leafEdge H v hv ∈ H.graph.edgeFinset := by
  unfold leafEdge
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact Classical.choose_spec
    ((H.graph.degree_eq_one_iff_existsUnique_adj).mp hv) |>.1

theorem leafEdge_injective
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1) :
    Function.Injective (fun v : L ↦ leafEdge H v.1 (hL v.1 v.2)) := by
  intro v w heq
  apply Subtype.ext
  change s(v.1, _) = s(w.1, _) at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with hsame | hswap
  · exact hsame.1
  · exfalso
    have hvw : H.graph.Adj v.1 w.1 := by
      have hadj := Classical.choose_spec
        ((H.graph.degree_eq_one_iff_existsUnique_adj).mp (hL v.1 v.2)) |>.1
      simpa only [hswap.2] using hadj
    exact not_adj_of_leaves_of_connected H hconn hn
      (hL v.1 v.2) (hL w.1 w.2) hvw

/-- Deleting `d` leaves removes at least `d` edges. -/
theorem deleteLeavesCode_edgeCount_add_card_le
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1) :
    (deleteLeavesCode H L).edgeCount + L.card ≤ H.edgeCount := by
  classical
  let S : Finset (Fin H.vertexCount) := Finset.univ \ L
  let kept : Finset (Sym2 (Fin H.vertexCount)) :=
    H.graph.edgeFinset.filter fun e ↦ e.toFinset ⊆ S
  have hkeptCard : kept.card = (deleteLeavesCode H L).edgeCount := by
    rw [GraphCode.edgeCount_eq_card_edgeFinset]
    have hfilter := H.graph.card_filter_edgeFinset_toFinset_subset S
    have hiso := (inducedCodeIso H S).card_edgeFinset_eq
    have hcode : deleteLeavesCode H L = inducedCode H S := rfl
    rw [hcode]
    exact hfilter.trans hiso
  let removed : Finset (Sym2 (Fin H.vertexCount)) :=
    H.graph.edgeFinset \ kept
  have hsplit : kept.card + removed.card = H.edgeCount := by
    have hsub : kept ⊆ H.graph.edgeFinset := by
      intro e he
      exact (Finset.mem_filter.mp he).1
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    rw [GraphCode.edgeCount_eq_card_edgeFinset]
    simpa [removed, add_comm] using hcard
  let f : L → removed := fun v ↦
    ⟨leafEdge H v.1 (hL v.1 v.2), by
      apply Finset.mem_sdiff.mpr
      refine ⟨leafEdge_mem_edgeFinset H v.1 (hL v.1 v.2), ?_⟩
      intro hkeep
      have hsubset := (Finset.mem_filter.mp hkeep).2
      have hvS : v.1 ∈ S := hsubset (by
        exact Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
      exact (Finset.mem_sdiff.mp hvS).2 v.2⟩
  have hfinj : Function.Injective f := by
    intro v w h
    apply leafEdge_injective H hconn hn L hL
    exact congrArg Subtype.val h
  have hcard : L.card ≤ removed.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfinj
  rw [← hkeptCard]
  omega

/-- Removing leaves preserves preconnectedness; a cardinal lower bound makes
the remaining induced graph genuinely connected. -/
theorem deleteLeavesCode_connected
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1)
    (hcard : L.card < H.vertexCount) :
    (deleteLeavesCode H L).graph.Connected := by
  classical
  let S : Finset (Fin H.vertexCount) := Finset.univ \ L
  have hpre : (H.graph.induce (S : Set _)).Preconnected := by
    apply hconn.preconnected.induce_of_degree_eq_one
    intro v hvS
    have hvL : v ∈ L := by
      by_contra hvL
      exact hvS (by simp [S, hvL])
    have hdeg := hL v hvL
    obtain ⟨u, _hu, hunique⟩ :=
      (H.graph.degree_eq_one_iff_existsUnique_adj).mp hdeg
    intro a ha b hb
    exact (hunique a ha).trans (hunique b hb).symm
  have hScard : S.card = H.vertexCount - L.card := by
    dsimp only [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ L)]
    simp
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty S := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hindConn : (H.graph.induce (S : Set _)).Connected := ⟨hpre⟩
  exact (inducedCodeIso H S).connected_iff.mp hindConn

theorem deleteLeavesCode_noIsolated
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1)
    (hremain : 2 ≤ H.vertexCount - L.card) :
    NoIsolated (deleteLeavesCode H L) := by
  have hQconn := deleteLeavesCode_connected H hconn L hL (by omega)
  intro v
  letI : Nontrivial (Fin (deleteLeavesCode H L).vertexCount) := by
    let a : Fin (deleteLeavesCode H L).vertexCount := ⟨0, by
      simpa using (show 0 < H.vertexCount - L.card by omega)⟩
    let b : Fin (deleteLeavesCode H L).vertexCount := ⟨1, by
      have : 1 < H.vertexCount - L.card := by omega
      simpa using this⟩
    exact ⟨⟨a, b, by
      intro hab
      have hv := congrArg Fin.val hab
      simp [a, b] at hv⟩⟩
  exact hQconn.preconnected.not_isIsolated v

/-- The cyclomatic excess cannot increase when a set of leaves is deleted. -/
theorem deleteLeavesCode_sparseExcess_le
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected) (hn : 3 ≤ H.vertexCount)
    (L : Finset (Fin H.vertexCount))
    (hL : ∀ v ∈ L, H.graph.degree v = 1) :
    sparseExcess (deleteLeavesCode H L) ≤ sparseExcess H := by
  have hedge := deleteLeavesCode_edgeCount_add_card_le H hconn hn L hL
  simp only [sparseExcess, deleteLeavesCode_vertexCount]
  omega

end Erdos570
