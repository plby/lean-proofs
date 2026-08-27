/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpInternalEdgeSupportedKernel

/-!
# Conditioning an existing reserve-aware law before the internal cover

The preliminary phase may be run after the reserve has already been sampled.
Its output is therefore an existing reserve-aware law, rather than a law to
which the reserve kernel still has to be bound.  This file conditions that
law directly on internal-kernel readiness and then applies the sharp internal
cover update.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Condition an existing reserve-aware law on the supported internal-cover
readiness event.  A uniform failure bound gives both positivity and the
explicit reciprocal loss used in the next multiplicative constant. -/
theorem IsReserveStronglyWellDistributed.conditionInternalOuterEdgeKernel
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {k next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A P0 initial later : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b epsilon p' C' b' : ℝ≥0}
    (hreserve : IsReserveStronglyWellDistributed law W k initial later reserve
      p reserveDensity C b)
    (i : Fin ell) (a D horizon : ℕ) (hD : 0 < D)
    (hbad : law.probability (fun omega ↦
      ¬ InternalOuterKernelReady W i F (G omega) (A omega) (P0 omega)
        (bits omega) a D) ≤ epsilon)
    (hepsilon : epsilon < 1)
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card ≤ horizon)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkn : k ≤ next) (hCC' : C / (1 - epsilon) ≤ C')
    (hC' : 1 ≤ C') (hpp' : p ≤ p')
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let Ready : Omega → Prop := fun omega ↦
      InternalOuterKernelReady W i F (G omega) (A omega) (P0 omega)
        (bits omega) a D
    ∃ hpos : 0 < law.probability Ready,
      let Lc := law.conditionOn Ready hpos
      let K : Omega → FiniteLaw (InternalEdgeGreedyStateOn V) :=
        supportedInternalOuterEdgeKernel W i F G A P0 bits a D
      let added : Omega → InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        supportedInternalOuterEdgeAdded P0
      IsReserveStronglyWellDistributed (Lc.jointBind K) W next
          (jointInitial initial) (jointLater later added)
          (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' ∧
        (Lc.jointBind K).SupportedOn (fun z ↦
          GreedyReachable F (P0 z.1) z.2.chosen ∧
          z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
          (z.2.chosen \ P0 z.1).card ≤
            (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
          ∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ),
            (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) ∧
        1 - epsilon ≤ law.probability Ready := by
  dsimp only
  let Ready : Omega → Prop := fun omega ↦
    InternalOuterKernelReady W i F (G omega) (A omega) (P0 omega)
      (bits omega) a D
  have hlower : 1 - epsilon ≤ law.probability Ready := by
    rw [law.probability_not Ready] at hbad
    calc
      1 - epsilon ≤ 1 - (1 - law.probability Ready) :=
        tsub_le_tsub_left hbad 1
      _ = law.probability Ready :=
        tsub_tsub_cancel_of_le (law.probability_le_one Ready)
  have hpos : 0 < law.probability Ready :=
    (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hpos, ?_⟩
  let Lc := law.conditionOn Ready hpos
  let K : Omega → FiniteLaw (InternalEdgeGreedyStateOn V) :=
    supportedInternalOuterEdgeKernel W i F G A P0 bits a D
  let added : Omega → InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    supportedInternalOuterEdgeAdded P0
  have hconditioned : IsReserveStronglyWellDistributed Lc W k
      initial later reserve p reserveDensity
        (C / law.probability Ready) b := by
    exact hreserve.conditionOn Ready hpos
  have hfactorBound : C / law.probability Ready ≤ C' := by
    calc
      C / law.probability Ready ≤ C / (1 - epsilon) := by
        exact div_le_div_of_nonneg_left zero_le
          (tsub_pos_iff_lt.mpr hepsilon) hlower
      _ ≤ C' := hCC'
  have hupdate :=
    hconditioned.jointBind_supportedInternalOuterEdgeKernel_sharp
      i a D horizon hD (law.conditionOn_supported Ready hpos)
      horizonBound hnonempty hkn hfactorBound hC' hpp' hfactor hbb' hnew
  exact ⟨by simpa only [Lc, K, added] using hupdate.1,
    by simpa only [Lc, K, added] using hupdate.2, hlower⟩

end

end Erdos207
