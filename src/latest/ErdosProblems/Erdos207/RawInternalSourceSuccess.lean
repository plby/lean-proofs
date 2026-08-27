/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawInternalLeftSuccess

/-! # Internal-cover failure bounded by the actual source left moments -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.rawInternal_failure_probability_le
    {Ω V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} (i : Fin ell)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V) (Γ : SimpleGraph V) (A P0 : Ω → TripleSystemOn V)
    (bits : Ω → Sym2 V → Bool) (threshold d leftCap : ℕ) (hthreshold : 0 < threshold)
    (initial : Ω → TripleSystemOn V) (later : Ω × InternalEdgeGreedyStateOn V → TripleSystemOn V)
    {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed
      (L.jointBind (rawResidualInternalKernel W i (orders.biUnion F) G A P0 bits threshold))
      W i.castSucc Γ (fun z ↦ initial z.1) later
      (fun z ↦ reserveEdges (G z.1) (W.U i.succ) (bits z.1)) p r C b)
    (hdis : (L.jointBind (rawResidualInternalKernel W i (orders.biUnion F) G A P0 bits threshold)).SupportedOn
      fun z ↦ Disjoint (initial z.1) (later z))
    (hclass : (L.jointBind (rawResidualInternalKernel W i (orders.biUnion F) G A P0 bits threshold)).SupportedOn
      fun z ↦ z.2.chosen = initial z.1 ∪ later z)
    (Good : Ω → Prop) (priorError epsilon : ℝ≥0) (error y z : ℕ → ℝ≥0) (s : ℕ → ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hepsilon : 0 < epsilon) (hU : (W.U i.succ).Nonempty)
    (hcap : epsilon*p^2*r^2*(W.U i.succ).card ≤ leftCap)
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix i.castSucc) j (F j) (y j) (z j))
    (hscale : ∀ j ∈ orders, z j ≤ y j*r^2*p^3*(W.U i.succ).card)
    (hscalar : ∀ j ∈ orders,
      sourceLeftFailureBound i.val j (s j) (Fintype.card V) p r C b (y j)
        (epsilon/(orders.card+1 : ℝ≥0)) (W.U i.succ).card ≤ error j)
    (hpacking0 : ∀ ω, Good ω → IsPackingOn (P0 ω))
    (havoid0 : ∀ ω, Good ω → AvoidsForbidden (P0 ω) (orders.biUnion F))
    (hbase : ∀ ω, Good ω → G ω ≤ Γ)
    (hlevel : ∀ ω, Good ω → ∀ T ∈ A ω, (W.prefix i.castSucc).level T = Fin.last i.val)
    (hinitial : ∀ ω, Good ω → ∀ T ∈ A ω, ¬ CompletesForbidden (orders.biUnion F) (initial ω) T)
    (hinitialPair : ∀ ω, Good ω → ∀ T ∈ A ω, TriangleAvoidsGraph (coveredGraph (P0 ω)) T)
    (hincidence : ∀ ω, Good ω → ∀ v : V,
      (scheduledEdgesAt (preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω)) v).card ≤ d)
    (hsupply : ∀ ω, Good ω → ∀ e ∈ preliminaryResidualInternalEdges (G ω) (W.U i.succ) (P0 ω),
      4*d+leftCap+threshold ≤ (activeReserveWedgeVertices (G ω) (W.U i.succ)
        (residualInternalExtensionSet W i (A ω) e) e.out.1 e.out.2 (bits ω)).card)
    (hprior : L.probability (fun ω ↦ ¬ Good ω) ≤ priorError) :
    (L.jointBind (rawResidualInternalKernel W i (orders.biUnion F) G A P0 bits threshold)).probability
      (fun z ↦ z.2.failed = true) ≤ priorError+(Fintype.card V : ℝ≥0)^2*∑ j ∈ orders, error j := by
  apply L.rawResidualInternal_failure_probability_le W i (orders.biUnion F) G Γ A P0 bits
    threshold d leftCap hthreshold initial later Good priorError _ hclass hpacking0 havoid0 hbase
    hlevel hinitial hinitialPair hincidence hsupply hprior
  apply le_trans _ (hstrong.sourceLeftCaps_probability_le hdis orders F y z (W.U i.succ) s
    epsilon error hp hp1 hr hr1 hC hepsilon hU hsource hscale hscalar)
  apply FiniteLaw.probability_mono
  intro ω hbad hgood
  exact hbad (hgood.mono_cutoff hcap)

theorem IsResidualReserveStronglyWellDistributed.condition_rawInternal_success
    {Ω V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {i : Fin ell} {k : Fin (ell+1)} {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V} {Γ : SimpleGraph V} {A P0 : Ω → TripleSystemOn V}
    {bits : Ω → Sym2 V → Bool} {threshold : ℕ}
    {initial later : Ω × InternalEdgeGreedyStateOn V → TripleSystemOn V}
    {reserve : Ω × InternalEdgeGreedyStateOn V → Finset (Sym2 V)} {p r C b error : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed
      (L.jointBind (rawResidualInternalKernel W i F G A P0 bits threshold)) W k Γ initial later reserve p r C b)
    (hthreshold : 0 < threshold)
    (hfailure : (L.jointBind (rawResidualInternalKernel W i F G A P0 bits threshold)).probability
      (fun z ↦ z.2.failed = true) ≤ error) (herror : error < 1) :
    let joint := L.jointBind (rawResidualInternalKernel W i F G A P0 bits threshold)
    let Success := fun z : Ω × InternalEdgeGreedyStateOn V ↦ z.2.failed = false
    ∃ hpos : 0 < joint.probability Success,
      1-error ≤ joint.probability Success ∧
      IsResidualReserveStronglyWellDistributed (joint.conditionOn Success hpos) W k Γ initial later reserve
        p r (C/(1-error)) b ∧
      (joint.conditionOn Success hpos).SupportedOn fun z ↦
        RawResidualInternalStructure W i F G A P0 bits threshold z.1 z.2 ∧
        z.2.failed = false ∧ GreedyReachable F (P0 z.1) z.2.chosen ∧
        z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
        (z.2.chosen \ P0 z.1).card ≤ (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
        ∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ), (coveredGraph z.2.chosen).Adj e.out.1 e.out.2 := by
  dsimp only
  let K := rawResidualInternalKernel W i F G A P0 bits threshold
  let joint := L.jointBind K
  let Success := fun z : Ω × InternalEdgeGreedyStateOn V ↦ z.2.failed = false
  have hnot : joint.probability (fun z ↦ ¬ Success z) ≤ error := by
    simpa only [Success, Bool.not_eq_false] using hfailure
  have hlower : 1-error ≤ joint.probability Success := by
    rw [joint.probability_not Success] at hnot
    exact tsub_le_iff_tsub_le.mp hnot
  have hden : 0 < 1-error := tsub_pos_iff_lt.mpr herror
  have hpos : 0 < joint.probability Success := hden.trans_le hlower
  refine ⟨hpos, hlower, ?_, ?_⟩
  · apply (hstrong.conditionOn Success hpos).mono _ le_rfl
    exact div_le_div_of_nonneg_left zero_le hden hlower
  · have hstruct : joint.SupportedOn fun z ↦ RawResidualInternalStructure W i F G A P0 bits threshold z.1 z.2 := by
      intro z hz
      exact rawResidualInternalKernel_supported_structure W i F G A P0 bits threshold hthreshold z.1 z.2
        ((L.jointBind_mass_pos_iff K z.1 z.2).mp hz).2
    have hstruct' := hstruct.conditionOn hpos
    have hsuccess := joint.conditionOn_supported Success hpos
    intro z hz
    have hs := hstruct' z hz
    have hf := hsuccess z hz
    exact ⟨hs, hf, hs.complete_internalCover hf⟩

end

end Erdos207
