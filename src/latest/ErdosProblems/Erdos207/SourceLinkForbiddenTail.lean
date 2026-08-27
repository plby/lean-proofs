/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkSampledForbiddenCount
import ErdosProblems.Erdos207.SourceLinkCanonicalMomentProbability

/-! # Source marked moments bound actual sampled forbidden degrees -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.sourceLinkForbiddenSamples_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (U : Finset V) (e : Sym2 V) (A : TripleSystemOn V)
    (I D historical Q : Ω → TripleSystemOn V) (reserve : Ω → Finset (Sym2 V))
    (hgeom : L.SupportedOn fun x ↦ Q x ⊆ A ∧
      (∀ T ∈ Q x, W.level T = Fin.last ell) ∧
      (∀ T ∈ Q x, ¬ CompletesForbidden F (I x ∪ historical x) T) ∧
      (∀ T ∈ D x \ historical x, W.level T = Fin.last ell) ∧
      (Q x).biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U (I x) (D x) (reserve x))
    (s cap : ℕ) (M : ℝ≥0)
    (hmoment : L.expectation (fun x ↦ selectedCount
      (fun c : sourceLinkMarkings W F e A ↦ c.1.coordinates e)
      (sourceLinkRealizedCoordinates G U (I x) (D x) (Q x) (reserve x)) ^ s) ≤ M) :
    L.probability (fun x ↦ cap < (sourceLinkForbiddenSamples F (I x) (D x) (Q x) e).card) ≤
      M / (cap + 1 : ℝ≥0) ^ s := by
  let X := fun x ↦ selectedCount (fun c : sourceLinkMarkings W F e A ↦ c.1.coordinates e)
    (sourceLinkRealizedCoordinates G U (I x) (D x) (Q x) (reserve x))
  have hpos : (0 : ℝ≥0) < (cap + 1 : ℝ≥0) ^ s := pow_pos (by positivity) s
  calc
    _ ≤ L.probability (fun x ↦ (cap + 1 : ℝ≥0) ^ s ≤ X x ^ s) := by
      apply L.probability_mono_of_supported hgeom
      intro x hx hlarge
      have hc := sourceLinkForbiddenSamples_card_le_selectedCount (e := e) G U (reserve x)
        hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
      have hnat : cap + 1 ≤ (sourceLinkForbiddenSamples F (I x) (D x) (Q x) e).card := by omega
      have hreal : (cap + 1 : ℝ≥0) ≤ ((sourceLinkForbiddenSamples F (I x) (D x) (Q x) e).card : ℝ≥0) := by
        exact_mod_cast hnat
      exact pow_le_pow_left' (hreal.trans hc) s
    _ ≤ L.expectation (fun x ↦ X x ^ s) / (cap + 1 : ℝ≥0) ^ s :=
      L.probability_le_expectation_div _ hpos
    _ ≤ M / (cap + 1 : ℝ≥0) ^ s := div_le_div_of_nonneg_right hmoment zero_le

theorem IsResidualReserveStronglyWellDistributed.sourceLink_canonical_forbidden_tail
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell j q s : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hstruct : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix k) j F y z)
    (U : Finset V) (e : Sym2 V) (A : TripleSystemOn V)
    (hoff : ¬ e.IsDiag) (hcross : IsCrossingEdge U e) (hjq : j ≤ q) (hy : 1 ≤ y)
    (a : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hu : 0 < U.card)
    (hlevel : ∀ T ∈ A, (W.prefix k).level T = Fin.last k.val)
    (hinner : ∀ T ∈ A, (T.1 ∩ U).card = 2)
    (hblock : r * a ≤ p * U.card / (W.prefix k).terminalSize) (hpa : p * a ≤ 1)
    (hw : 1 ≤ a * (W.prefix k).terminalSize / (r * p ^ 2 * U.card))
    (hscale : z * (a * (W.prefix k).terminalSize / (r * p ^ 2 * U.card)) ^ (q + 1) /
      (W.prefix k).terminalSize ≤ y)
    (candidate : Ω → Ξ → TripleSystemOn V) (J delta : ℝ≥0)
    (hsigma : a / (r * p ^ 2 * U.card) ≤ 1) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hcandidate : ∀ ω, 0 < L.mass ω → ∀ Q,
      (K ω).probability (fun ξ ↦ Q ⊆ candidate ω ξ) ≤
        (a / (r * p ^ 2 * U.card)) ^ Q.card + J ^ Q.card * delta)
    (historical : Ω → TripleSystemOn V)
    (hgeom : (L.jointBind K).SupportedOn fun x ↦ candidate x.1 x.2 ⊆ A ∧
      (∀ T ∈ candidate x.1 x.2, ¬ CompletesForbidden F (initial x.1 ∪ historical x.1) T) ∧
      (∀ T ∈ later x.1 \ historical x.1, (W.prefix k).level T = Fin.last k.val) ∧
      (candidate x.1 x.2).biUnion tripleEdgeFinset ⊆
        sourceLinkRetainedEdges G U (initial x.1) (later x.1) (reserve x.1))
    (cap : ℕ) :
    let d := 4 * (j - 2)
    let κ : ℝ≥0 := (4 : ℝ≥0) ^ (j - 2) * ((1 + (k.val + 1) ^ 2 : ℕ) * (j ^ k.val : ℕ)) * y
    (L.jointBind K).probability (fun x ↦ cap <
      (sourceLinkForbiddenSamples F (initial x.1) (later x.1) (candidate x.1 x.2) e).card) ≤
      ((max (C ^ 2) J) ^ (s * d) *
        (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ s +
          (b + delta) * ((4 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s)) /
        (cap + 1 : ℝ≥0) ^ s := by
  dsimp only
  refine (L.jointBind K).sourceLinkForbiddenSamples_tail (W.prefix k) F G U e A
    (fun x ↦ initial x.1) (fun x ↦ later x.1) (fun x ↦ historical x.1)
    (fun x ↦ candidate x.1 x.2) (fun x ↦ reserve x.1) ?_ s cap _ ?_
  · intro x hx
    have hg := hgeom x hx
    exact ⟨hg.1, fun T hT ↦ hlevel T (hg.1 hT), hg.2⟩
  · exact hstrong.sourceLink_canonical_moment_le hstruct hsource U e A hoff hcross hjq hy a
      hp hp1 hr hr1 hu hlevel hinner hblock hpa hw hscale candidate J delta hsigma hC hJ hcandidate

end

end Erdos207
