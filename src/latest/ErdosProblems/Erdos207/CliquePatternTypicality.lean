/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternExtensions
import ErdosProblems.Erdos207.PatternTypicalityArithmetic

/-! # Iteration typicality gives proper clique-extension estimates with exact loss -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem properPattern_error_of_full_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) (target error : ℝ)
    (hfull : |((iterationExtensionVertices A Q U).card : ℝ) - target| ≤ error) :
    |((properPatternExtensions A Q U).card : ℝ) - target| ≤
      error + (graphSupportFinset Q).card := by
  obtain ⟨hlo, hhi⟩ := properPatternExtensions_card_comparison A Q U
  have hloR : ((properPatternExtensions A Q U).card : ℝ) ≤
      (iterationExtensionVertices A Q U).card := by exact_mod_cast hlo
  have hhiR : ((iterationExtensionVertices A Q U).card : ℝ) ≤
      (properPatternExtensions A Q U).card + (graphSupportFinset Q).card := by exact_mod_cast hhi
  have hs : (0 : ℝ) ≤ (graphSupportFinset Q).card := by positivity
  have hb := abs_le.mp hfull
  apply abs_le.mpr
  constructor <;> linarith

theorem properPatternExtensions_univ_eq_of_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V)
    (hQ : (graphEdges Q).Nonempty) (hA : ∀ T ∈ A, T.1 ⊆ U) :
    properPatternExtensions A Q univ = properPatternExtensions A Q U := by
  ext v
  simp only [mem_properPatternExtensions_iff, mem_iterationExtensionVertices_iff,
    mem_univ, true_and]
  constructor
  · rintro ⟨hext, hvQ⟩
    obtain ⟨e, he⟩ := hQ
    obtain ⟨T, hTA, hvT, _⟩ := hext e he
    exact ⟨⟨hA T hTA hvT, hext⟩, hvQ⟩
  · exact fun h ↦ ⟨h.1.2, h.2⟩

theorem cliquePattern_edges_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (hS : 2 ≤ S.card) :
    (graphEdges (cliquePattern S)).Nonempty := by
  apply card_pos.mp
  rw [cliquePattern_edge_card]
  exact Nat.choose_pos hS

theorem cliquePattern_subset_supported_graph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S U : Finset V) (hS : 2 ≤ S.card)
    (hSG : cliquePattern S ≤ G) (hG : GraphSupportedOn G (U : Set V)) : S ⊆ U := by
  intro v hv
  have hsupport : v ∈ graphSupportFinset (cliquePattern S) := by
    simpa only [cliquePattern_support S hS] using hv
  obtain ⟨w, hvw⟩ := mem_graphSupportFinset_iff.mp hsupport
  exact (hG (hSG hvw)).1

theorem triple_supported_of_graph_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (T : TripleOn V)
    (hG : GraphSupportedOn G (U : Set V)) (hT : tripleEdgeFinset T ⊆ graphEdges G) :
    T.1 ⊆ U := by
  intro v hv
  have hnonempty : (T.1.erase v).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hv, T.2]
    decide
  obtain ⟨w, hw⟩ := hnonempty
  have hvw : v ≠ w := (mem_erase.mp hw).1.symm
  have he := hT (mk_mem_tripleEdgeFinset_iff.mpr ⟨hv, (mem_erase.mp hw).2, hvw⟩)
  exact (hG (mem_graphEdges_iff.mp he)).1

theorem cliquePattern_edge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ graphEdges G) :
    cliquePattern e.toFinset ≤ G := by
  apply (cliquePattern_le_iff G e.toFinset).mpr
  have hc := Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he))
  rw [← hc, powersetCard_self]
  exact singleton_subset_iff.mpr ((mem_graphPairFamily_toFinset_iff G e).mpr he)

theorem IsIterationTypical.clique_proper_extension_error
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} (htyp : IsIterationTypical W k G A p eta xi h)
    (i : Fin ell) (hki : k.val ≤ i.val) (iStar : Fin (ell + 1))
    (hstar : iStar = i.castSucc ∨ iStar = i.succ)
    (S : Finset V) (hS : 2 ≤ S.card) (hSh : S.card ≤ h)
    (hSU : S ⊆ W.U i.castSucc) (hSG : cliquePattern S ≤ G) :
    let target : ℝ := (p : ℝ) ^ S.card * (eta : ℝ) ^ (S.card.choose 2) * (W.U iStar).card
    |((properPatternExtensions A (cliquePattern S) (W.U iStar)).card : ℝ) - target| ≤
      (xi : ℝ) * target + S.card := by
  have hsupport : GraphSupportedOn (cliquePattern S) (W.U i.castSucc : Set V) :=
    fun {_ _} huv ↦ ⟨hSU huv.2.1, hSU huv.2.2⟩
  have hfull := htyp.2 i hki iStar hstar (cliquePattern S) hSG hsupport
    (by simpa only [cliquePattern_support S hS] using hSh)
  rw [withinMultiplicativeError_iff_abs] at hfull
  simp only [cliquePattern_support S hS, cliquePattern_edge_card, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_natCast] at hfull
  have hproper := properPattern_error_of_full_error A (cliquePattern S) (W.U iStar)
    _ _ hfull
  simpa only [cliquePattern_support S hS] using hproper

end

end Erdos207
