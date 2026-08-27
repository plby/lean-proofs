/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveStrongWellDistributed
import ErdosProblems.Erdos207.FiniteJointConditioning

/-!
# A reserve-aware master law conditioned on dependent good fibers

This is the law-level form needed by the cover-down iteration.  The ambient
graph, and hence the good reserve event, may depend on the old master state.
A uniform conditional failure estimate below `epsilon < 1` permits
conditioning the joint old-state/reserve law.  All prescribed reserve-edge
factors survive, with the explicit reciprocal loss `1 / (1 - epsilon)` in
the multiplicative constant.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Sample reserve edges conditionally at every old state, then condition
the joint law on a state-dependent good-reserve event. -/
theorem IsStronglyWellDistributed.jointBind_conditionedReserveEdges
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p C b r epsilon : ℝ≥0}
    (hstrong : IsStronglyWellDistributed L W k initial later p C b)
    (hC : 1 ≤ C) (hr : r ≤ 1)
    (Good : Omega → (Sym2 V → Bool) → Prop)
    (hbad : ∀ omega,
      (reserveEdgeLaw (G omega) U r hr).probability
        (fun bits ↦ ¬ Good omega bits) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let K : Omega → FiniteLaw (Sym2 V → Bool) :=
      fun omega ↦ reserveEdgeLaw (G omega) U r hr
    let J := L.jointBind K
    let P : Omega × (Sym2 V → Bool) → Prop :=
      fun z ↦ Good z.1 z.2
    ∃ hpos : 0 < J.probability P,
      IsReserveStronglyWellDistributed (J.conditionOn P hpos) W k
        (fun z ↦ initial z.1) (fun z ↦ later z.1)
        (fun z ↦ reserveEdges (G z.1) U z.2)
        p r (C / (1 - epsilon)) b ∧
      (J.conditionOn P hpos).SupportedOn P ∧
      1 - epsilon ≤ J.probability P := by
  dsimp only
  let K : Omega → FiniteLaw (Sym2 V → Bool) :=
    fun omega ↦ reserveEdgeLaw (G omega) U r hr
  let J := L.jointBind K
  let P : Omega × (Sym2 V → Bool) → Prop :=
    fun z ↦ Good z.1 z.2
  have hlower : 1 - epsilon ≤ J.probability P := by
    exact L.one_sub_le_jointBind_probability K Good epsilon hbad
  have hpos : 0 < J.probability P := by
    exact (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hpos, ?_, FiniteLaw.conditionOn_supported J P hpos, hlower⟩
  have hreserve : IsReserveStronglyWellDistributed J W k
      (fun z ↦ initial z.1) (fun z ↦ later z.1)
      (fun z ↦ reserveEdges (G z.1) U z.2) p r C b := by
    exact hstrong.jointBind_reserveEdges hC hr
  have hconditioned := hreserve.conditionOn P hpos
  apply hconditioned.mono_factor
  dsimp only [J, P] at hlower hpos ⊢
  gcongr
  exact tsub_pos_iff_lt.mpr hepsilon

end

end Erdos207
