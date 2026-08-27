/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteConditioning
import ErdosProblems.Erdos207.MasterIterationData

/-!
# Conditioning the input to the KSSS master iteration

This is the exact finite version of the reduction immediately following
Proposition 10.6: condition on IG2--IG4, whose probability is at least
`1-ξ`.  Parity remains supported, IG2--IG4 then hold throughout the support,
and the strong-distribution constant is multiplied by the reciprocal of the
conditioning probability.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- The pointwise-good event used to condition one master stage. -/
def masterPointwiseGoodEvent
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V)
    (A I D : Ω → TripleSystemOn V)
    (p eta ξ : ℝ≥0) (h : ℕ) (ω : Ω) : Prop :=
  IsMasterStagePointwiseGood W k F (G ω) (A ω) (I ω) (D ω)
    p eta ξ h

/-- Conditioned input law and its proof of positive normalizing mass. -/
def conditionedMasterLaw
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1))
    (F : ForbiddenFamilyOn V)
    (G : Ω → SimpleGraph V)
    (A I D : Ω → TripleSystemOn V)
    (p eta ξ C b : ℝ≥0) (h : ℕ)
    (hξ : ξ < 1)
    (hgood : IsMasterIterationGood L W k F G A I D p eta ξ C b h) :
    FiniteLaw Ω :=
  L.conditionOn (masterPointwiseGoodEvent W k F G A I D p eta ξ h)
    ((tsub_pos_iff_lt.mpr hξ).trans_le hgood.2.2)

/-- After conditioning, every supported outcome satisfies IG2--IG4 and all
remaining iteration-good clauses persist with the exact reciprocal loss. -/
theorem IsMasterIterationGood.conditionPointwise
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Ω → SimpleGraph V}
    {A I D : Ω → TripleSystemOn V}
    {p eta ξ C b : ℝ≥0} {h : ℕ}
    (hgood : IsMasterIterationGood L W k F G A I D p eta ξ C b h)
    (hξ : ξ < 1) :
    IsMasterIterationGood
      (conditionedMasterLaw L W k F G A I D p eta ξ C b h hξ hgood)
      W k F G A I D p eta ξ
      (C / L.probability
        (masterPointwiseGoodEvent W k F G A I D p eta ξ h)) b h := by
  let Good := masterPointwiseGoodEvent W k F G A I D p eta ξ h
  have hpos : 0 < L.probability Good :=
    (tsub_pos_iff_lt.mpr hξ).trans_le hgood.2.2
  let Lc := L.conditionOn Good hpos
  have hsupport : Lc.SupportedOn Good := L.conditionOn_supported Good hpos
  have heven : HasEvenStageGraphs Lc G :=
    hgood.1.conditionOn hpos
  have hstrong : IsStronglyWellDistributed Lc W k I D p
      (C / L.probability Good) b :=
    hgood.2.1.conditionOn Good hpos
  have hprob : 1 - ξ ≤ Lc.probability Good := by
    rw [Lc.probability_eq_one_of_supported Good hsupport]
    exact tsub_le_self
  simpa only [conditionedMasterLaw, Good, Lc] using
    (show IsMasterIterationGood Lc W k F G A I D p eta ξ
      (C / L.probability Good) b h from ⟨heven, hstrong, hprob⟩)

end

end Erdos207
