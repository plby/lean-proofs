/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryDegreeCoverGeometry
import ErdosProblems.Erdos207.SourceReserveGoodProbability

/-! # Averaging the preliminary degree event without discarding bad prior inputs -/

namespace Erdos207

open scoped NNReal

noncomputable section

def sourcePreliminaryDegreeFailure (N n d s : ℕ) (rate C error : ℝ≥0) : ℝ≥0 :=
  (N : ℝ≥0) * ((2 * (n : ℝ≥0) * rate / (d + 1)) ^ s + (2 * (n : ℝ≥0) * C / (d + 1)) ^ s * error)

theorem IsGraphMixedProductBound.protected_preliminary_degree_failure_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V}
    {current U : Finset V} {reserve : Finset (Sym2 V)} {survival point C error rate J : ℝ≥0}
    (h : IsGraphMixedProductBound L selected (reserveProtectedOuterGraph G U reserve) survival point C error)
    (hsupp : GraphSupportedOn G (current : Set V)) (hRate : C * survival ≤ rate) (hC : C ≤ J)
    (s d : ℕ) (hs : 2 * s ≤ d + 1) :
    L.probability (fun omega ↦ ¬ PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph G U reserve) U (selected omega) d) ≤
        sourcePreliminaryDegreeFailure (Fintype.card V) current.card d s rate J error := by
  have hsupp' : GraphSupportedOn (reserveProtectedOuterGraph G U reserve) (current : Set V) := by
    intro v w hAdj
    exact hsupp (reserveProtectedOuterGraph_le G U reserve hAdj)
  apply (h.preliminary_degree_failure_le current U hsupp' s d hs).trans
  unfold sourcePreliminaryDegreeFailure
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply add_le_add
  · have hm := mul_le_mul_of_nonneg_left hRate (show 0 ≤ 2 * (current.card : ℝ≥0) from zero_le)
    have hm' : 2 * (current.card : ℝ≥0) * C * survival ≤ 2 * (current.card : ℝ≥0) * rate := by
      simpa only [mul_assoc] using hm
    exact pow_le_pow_left' (div_le_div_of_nonneg_right hm' zero_le) s
  · gcongr

theorem FiniteLaw.jointProtectedPreliminary_degree_failure_le
    {Ω Ξ V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ξ] [DecidableEq Ξ]
    [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (G : Ω → SimpleGraph V) (current U : Finset V)
    (reserve : Ω → Finset (Sym2 V)) (selected : Ω → Ξ → TripleSystemOn V)
    (survival point C : Ω → ℝ≥0) (rate J error priorError : ℝ≥0)
    (Prior : Ω → Prop) (s d : ℕ) (hs : 2 * s ≤ d + 1)
    (hprior : L.probability (fun omega ↦ ¬ Prior omega) ≤ priorError)
    (hmixed : ∀ omega, 0 < L.mass omega → Prior omega →
      IsGraphMixedProductBound (K omega) (selected omega)
        (reserveProtectedOuterGraph (G omega) U (reserve omega)) (survival omega) (point omega) (C omega) error)
    (hsupp : ∀ omega, 0 < L.mass omega → Prior omega → GraphSupportedOn (G omega) (current : Set V))
    (hRate : ∀ omega, 0 < L.mass omega → Prior omega → C omega * survival omega ≤ rate)
    (hC : ∀ omega, 0 < L.mass omega → Prior omega → C omega ≤ J) :
    (L.jointBind K).probability (fun z ↦ ¬ (Prior z.1 ∧
      PreliminaryResidualDegreeGood (reserveProtectedOuterGraph (G z.1) U (reserve z.1)) U (selected z.1 z.2) d)) ≤
        priorError + sourcePreliminaryDegreeFailure (Fintype.card V) current.card d s rate J error := by
  apply L.jointBind_not_good_pair_le K Prior
    (fun omega sample ↦ PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph (G omega) U (reserve omega)) U (selected omega sample) d)
    priorError _ hprior
  intro omega hmass hg
  exact (hmixed omega hmass hg).protected_preliminary_degree_failure_le (hsupp omega hmass hg)
    (hRate omega hmass hg) (hC omega hmass hg) s d hs

end

end Erdos207
