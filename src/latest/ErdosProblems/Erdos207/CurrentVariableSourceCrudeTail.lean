/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CurrentVertexSourceCrudeTail
import ErdosProblems.Erdos207.VariableSourceCrudeTail

/-! # The local conditional process inherits source tails at its own random horizon -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsGraphStronglyWellDistributed.current_variable_source_crude_failure_le_sum
    {D V I : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype I]
    {ell q s : ℕ} {P : FiniteLaw D} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : D → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsGraphStronglyWellDistributed P W k G initial later p C b)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (horizon floor : D → ℕ) (J : D → ForbiddenFamilyOn (W.U k))
    (active : D → ℕ → GreedyStateOn (W.U k) → Prop) (S₀ : D → GreedyStateOn (W.U k))
    (delta : ℝ≥0) (hdelta : delta ≤ 1) (hfloor : ∀ d, 0 < floor d)
    (hratio : ∀ d, (horizon d : ℝ≥0) * (floor d : ℝ≥0)⁻¹ ≤ delta)
    (hactive : ∀ d i S, active d i S → floor d ≤ S.available.card)
    (hInv : ∀ d, GreedyInvariant (J d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (F : I → ForbiddenFamilyOn V) (order : I → ℕ) (y z : I → ℝ≥0)
    (hF : ∀ i, SourceVortexWellSpread (W.prefix k) (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (hprior : P.SupportedOn (fun d ↦
      Disjoint (mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U k)) (S₀ d).available) (initial d ∪ later d) ∧
      ∀ B ∈ mapForbiddenFamily (Function.Embedding.subtype (fun v ↦ v ∈ W.U k)) (J d),
        B ⊆ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U k)) (S₀ d).available ∧
        ∃ i E, E ∈ F i ∧ B ⊆ E ∧ E \ B ⊆ initial d ∪ later d))
    (K : CrudeThresholds) (hK : ∀ i : CrudeStatisticIndex V q, 0 < crudeThreshold K i) :
    (P.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (J d) (active d) (S₀ d))).probability
      (fun u ↦ ¬ CrudeStateBounds (J u.1) u.2 q K) ≤
      ∑ i : CrudeStatisticIndex V q,
        sourceCrudeTailBound (W.prefix k) order z s (2 + delta * (W.prefix k).terminalSize)
          ((4 * C) ^ (s * (2 * q))) (((4 * C) ^ (s * (2 * q))) * b) K i := by
  classical
  let e : (W.U k) ↪ V := Function.Embedding.subtype (fun v ↦ v ∈ W.U k)
  let J' := fun d ↦ mapForbiddenFamily e (J d)
  let S₀' := fun d ↦ mapGreedyState e (S₀ d)
  let active' := fun d i (S : GreedyStateOn V) ↦
    S = mapGreedyState e (restrictGreedyStateTo (W.U k) S) ∧ active d i (restrictGreedyStateTo (W.U k) S)
  have hactiveMap : ∀ d i S, active' d i (mapGreedyState e S) ↔ active d i S := by
    intro d i S
    change (mapGreedyState e S = mapGreedyState e (restrictGreedyStateTo (W.U k) (mapGreedyState e S)) ∧
      active d i (restrictGreedyStateTo (W.U k) (mapGreedyState e S))) ↔ active d i S
    simp only [e, restrictGreedyStateTo_map, true_and]
  have hfloor' : ∀ d i S, active' d i S → floor d ≤ S.available.card := by
    intro d i S hs
    have hc := hactive d i (restrictGreedyStateTo (W.U k) S) hs.2
    rw [hs.1]
    exact (card_mapTripleSystem e (restrictGreedyStateTo (W.U k) S).available).symm ▸ hc
  have hInv' : ∀ d, GreedyInvariant (J' d) (S₀' d) :=
    fun d ↦ (greedyInvariant_map_iff e (J d) (S₀ d)).2 (hInv d)
  have hchosen' : ∀ d, (S₀' d).chosen = ∅ := by
    intro d
    change mapTripleSystem e (S₀ d).chosen = ∅
    rw [hchosen d]
    rfl
  have hgeometry' : ∀ d T, T ∈ (S₀' d).available → T.1 ⊆ W.U k := by
    intro d T hT
    obtain ⟨U, _, rfl⟩ := mem_map.mp hT
    exact mapTriple_subtype_supported (W.U k) U
  have hbound := hstrong.variable_source_crude_failure_le_sum (q := q) (s := s) hp hC hnonempty
    horizon floor J' active' S₀' delta hdelta hfloor hratio hfloor' hInv' hchosen' hgeometry'
    F order y z hF horder hidentical hprior K hK
  refine le_trans ?_ hbound
  rw [FiniteLaw.probability_jointBind, FiniteLaw.probability_jointBind]
  apply sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ zero_le
  rw [← stoppedGreedyStateLaw_map e (horizon d) (J d) (active d) (active' d) (hactiveMap d) (S₀ d),
    FiniteLaw.probability_map]
  apply FiniteLaw.probability_mono
  intro S hbad hgood
  exact hbad (CrudeStateBounds.of_map e (J d) S K hgood)

end

end Erdos207
