/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkFanGeometry

/-! # The KSSS link maximum-extension estimate with its actual source weights -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem sourceLink_weight_ratio_ge_one
    (p r a n u : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hu : 0 < u) (ha : 1 ≤ a) (hun : u ≤ n) :
    1 ≤ a * n / (r * p ^ 2 * u) := by
  apply (le_div_iff₀ (by positivity : 0 < r * p ^ 2 * u)).mpr
  rw [one_mul]
  have hrp : r * p ^ 2 ≤ 1 :=
    (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hp1)).trans hr1
  exact (mul_le_of_le_one_left zero_le hrp).trans
    (hun.trans (le_mul_of_one_le_left zero_le ha))

theorem Vortex.ambient_inverse_le_triple_weight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (hn : 0 < W.terminalSize) (T : TripleOn V) :
    (Fintype.card V : ℝ≥0)⁻¹ ≤ vortexTripleWeight W 1 T := by
  have hpos : 0 < (W.U (W.level T)).card := hn.trans_le
    (card_le_card (W.antitone (W.level T) (Fin.last ell) (Fin.le_last _)))
  have hpos' : (0 : ℝ≥0) < (W.U (W.level T)).card := by exact_mod_cast hpos
  have hle : ((W.U (W.level T)).card : ℝ≥0) ≤ Fintype.card V := by exact_mod_cast card_le_univ (W.U (W.level T))
  simpa only [one_div, vortexTripleWeight] using one_div_le_one_div_of_le hpos' hle

theorem SourceVortexWellSpread.sourceLink_canonical_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j q : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (U : Finset V) (e : Sym2 V) (A : TripleSystemOn V)
    (hoff : ¬ e.IsDiag) (hcross : IsCrossingEdge U e) (hjq : j ≤ q) (hy : 1 ≤ y)
    (p r a : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hu : 0 < U.card)
    (hlevel : ∀ T ∈ A, W.level T = Fin.last ell)
    (hinner : ∀ T ∈ A, (T.1 ∩ U).card = 2)
    (hblock : r * a ≤ p * U.card / W.terminalSize) (hpa : p * a ≤ 1)
    (hw : 1 ≤ a * W.terminalSize / (r * p ^ 2 * U.card))
    (hscale : z * (a * W.terminalSize / (r * p ^ 2 * U.card)) ^ (q + 1) / W.terminalSize ≤ y) :
    HasExtensionBound (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
      (sourceLinkMixedWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
        (vortexTripleWeight W p) (fun _ ↦ a / (r * p ^ 2 * U.card))
        (sourceLinkCanonicalEdgeWeight U p r))
      ((4 : ℝ≥0) ^ (j - 2) * ((1 + (ell + 1) ^ 2 : ℕ) * (j ^ ell : ℕ)) * y) := by
  have hn' : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast h.terminal_nonempty
  have hu' : (0 : ℝ≥0) < U.card := by exact_mod_cast hu
  have hspokes : ∀ T ∈ A, (tripleCrossingEdges U T).card = 2 :=
    fun T hT ↦ card_tripleCrossingEdges_of_two_inner_vertices U T (hinner T hT)
  apply h.sourceLink_hasExtensionBound hoff hjq hy _ _ _ _ p
    (a * W.terminalSize / (r * p ^ 2 * U.card)) (a / U.card) hp1 hw
  · exact W.ambient_inverse_le_triple_weight h.terminal_nonempty
  · intro T
    simp only [vortexTripleWeight]
    exact le_of_eq (by ring)
  · intro T hT
    rw [vortexTripleWeight, hlevel T hT]
    change a / (r * p ^ 2 * (U.card : ℝ≥0)) ≤
      (a * W.terminalSize / (r * p ^ 2 * U.card)) * (1 / W.terminalSize)
    apply le_of_eq
    field_simp
  · intro T hT
    rw [sourceLinkCanonicalEdgeWeight_triangle U p r T (hspokes T hT)]
    have hb := sourceLinkCanonicalWeight_block_le p r a W.terminalSize U.card hp hp1 hr hn' hu' hblock
    rw [vortexTripleWeight, hlevel T hT]
    exact hb.trans_eq (by change p / (W.terminalSize : ℝ≥0) = p * (1 / W.terminalSize); ring)
  · exact sourceLinkCanonicalEdgeWeight_le_one U p r hp1 hr1
  · intro T hT
    have hm := mem_inter.mp hT
    have heT := (mem_filter.mp hm.1).2.1
    rw [sourceLinkCanonicalEdgeWeight_root_triangle U p r T (hspokes T hm.2) heT hcross]
    exact le_of_eq (sourceLinkCanonicalWeight_root_block p r a U.card hp hr hu')
  · have hcard : ((sourceTerminalEdgeFan W e ∩ A).card : ℝ≥0) ≤ U.card := by
      exact_mod_cast card_sourceLink_inner_fan_le W U e A hoff hcross hinner
    calc
      _ ≤ (U.card : ℝ≥0) * (a / U.card) * p := by gcongr
      _ = p * a := by field_simp
      _ ≤ _ := hpa
  · exact hscale

end

end Erdos207
