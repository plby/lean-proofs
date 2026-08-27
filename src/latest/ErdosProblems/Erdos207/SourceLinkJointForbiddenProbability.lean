/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkJointGeometry
import ErdosProblems.Erdos207.SourceLinkForbiddenTail
import ErdosProblems.Erdos207.SampledLinkForbiddenGoodTail
import ErdosProblems.Erdos207.BoundedPatternIndex

/-! # The source moment and pinned-edge/order unions for the actual joint reservoir law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.not_sampledLinkForbiddenOrdersGood_le_on_support
    {Ω O V J : Type*} [Fintype Ω] [DecidableEq V] [DecidableEq J]
    (L : FiniteLaw Ω) (K : Ω → O → BipartiteLink V) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (I D Q : Ω → TripleSystemOn V) (cap : J → ℕ) (pins : Finset (Sym2 V)) (error : J → Sym2 V → ℝ≥0)
    (hpins : L.SupportedOn fun x ↦
      (∀ o (a : ↥(K x o).left), s((K x o).center,(K x o).leftEmbedding a) ∈ pins) ∧
      (∀ o (b : ↥(K x o).right), s((K x o).center,(K x o).rightEmbedding b) ∈ pins))
    (htail : ∀ j ∈ orders, ∀ e ∈ pins,
      L.probability (fun x ↦ cap j < (sourceLinkForbiddenSamples (F j) (I x) (D x) (Q x) e).card) ≤ error j e) :
    L.probability (fun x ↦ ¬ IsSampledLinkForbiddenGood (K x) (orders.biUnion F) (I x) (D x) (Q x)
      (∑ j ∈ orders, cap j)) ≤ ∑ e ∈ pins, ∑ j ∈ orders, error j e := by
  calc
    _ ≤ L.probability (fun x ↦ ∃ e ∈ pins, (∑ j ∈ orders, cap j) <
        (sourceLinkForbiddenSamples (orders.biUnion F) (I x) (D x) (Q x) e).card) := by
      apply L.probability_mono_of_supported hpins
      intro x hx hbad
      by_contra hn
      push Not at hn
      apply hbad
      intro o
      exact ⟨fun a ↦ hn _ (hx.1 o a), fun b ↦ hn _ (hx.2 o b)⟩
    _ ≤ ∑ e ∈ pins, L.probability (fun x ↦ (∑ j ∈ orders, cap j) <
        (sourceLinkForbiddenSamples (orders.biUnion F) (I x) (D x) (Q x) e).card) :=
      L.probability_exists_le pins _
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      exact L.sourceLinkForbiddenOrders_probability_le orders F I D Q e cap (fun j ↦ error j e)
        (fun j hj ↦ htail j hj e he)

def sourceLinkFailureBound (k j s N cap : ℕ) (C b y : ℝ≥0) : ℝ≥0 :=
  let d := 4*(j-2)
  let kappa : ℝ≥0 := (4 : ℝ≥0)^(j-2)*((1+(k+1)^2 : ℕ)*(j^k : ℕ))*y
  (C^2)^(s*d)*(((boundedIntersectionMomentCoefficient d s : ℝ≥0)*kappa)^s+
    b*((4 : ℝ≥0)^(j-2)*(N+1 : ℝ≥0)^(3*j))^s)/(cap+1 : ℝ≥0)^s

theorem IsResidualReserveStronglyWellDistributed.rawLinkJoint_forbidden_probability_le
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell q : ℕ}
    {L : FiniteLaw Ω} {kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V)}
    {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V}
    {initial later historical available : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k Gamma initial later reserve p r C b)
    (hdis : L.SupportedOn fun omega ↦ Disjoint (initial omega) (later omega))
    (U : Finset V) (center : Ω → O ↪ V) (links : Ω → O → BipartiteLink V)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V) (y z error : ℕ → ℝ≥0) (s cap : ℕ → ℕ)
    (a : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hu : 0 < U.card) (hC : 1 ≤ C)
    (hblock : r*a ≤ p*U.card/(W.prefix k).terminalSize) (hpa : p*a ≤ 1)
    (hw : 1 ≤ a*(W.prefix k).terminalSize/(r*p^2*U.card))
    (hsigma : a/(r*p^2*U.card) ≤ 1)
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix k) j (F j) (y j) (z j))
    (hjq : ∀ j ∈ orders, j ≤ q) (hy : ∀ j ∈ orders, 1 ≤ y j)
    (hscale : ∀ j ∈ orders,
      z j*(a*(W.prefix k).terminalSize/(r*p^2*U.card))^(q+1)/(W.prefix k).terminalSize ≤ y j)
    (hscalar : ∀ j ∈ orders, sourceLinkFailureBound k.val j (s j) (Fintype.card V) (cap j) C b (y j) ≤ error j)
    (hstruct : ∀ omega, 0 < L.mass omega → (kernel omega).SupportedOn
      (IsSampledLinkJointOutcome (orders.biUnion F) (available omega) (initial omega ∪ later omega) (links omega)))
    (hpoint : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
      (kernel omega).probability (fun result ↦ Q ⊆ result.1) ≤ (a/(r*p^2*U.card))^Q.card)
    (hgeometry : L.SupportedOn fun omega ↦ RawLinkSourceGeometry W k Gamma U (initial omega) (later omega)
      (historical omega) (available omega) (reserve omega) (center omega) (links omega) orders F) :
    (L.jointBind kernel).probability (fun result ↦
      ¬ IsSampledLinkForbiddenGood (links result.1) (orders.biUnion F) (initial result.1) (later result.1)
        result.2.1 (∑ j ∈ orders, cap j)) ≤ (Fintype.card V : ℝ≥0)^2*∑ j ∈ orders, error j := by
  let Ambient := sourceLinkAmbientCandidates (W.U k) U
  let J := L.jointBind kernel
  have hpoint' : ∀ omega, 0 < L.mass omega → ∀ Q,
      (kernel omega).probability (fun result ↦ Q ⊆ result.1) ≤
        (a/(r*p^2*U.card))^Q.card+(1 : ℝ≥0)^Q.card*0 := by
    intro omega hmass Q
    simpa only [mul_zero, add_zero] using hpoint omega hmass Q
  have htail : ∀ j ∈ orders, ∀ e ∈ crossingEdges Gamma U,
      J.probability (fun result ↦ cap j <
        (sourceLinkForbiddenSamples (F j) (initial result.1) (later result.1) result.2.1 e).card) ≤ error j := by
    intro j hj e he
    have heG := (mem_crossingEdges_iff.mp he).1
    have hb := hstrong.sourceLink_canonical_forbidden_tail
      (Ξ := TripleSystemOn V × TripleSystemOn V) (K := kernel) (q := q) (s := s j)
      hdis (hsource j hj) U e Ambient
      (Gamma.not_isDiag_of_mem_edgeSet heG) (mem_crossingEdges_iff.mp he).2 (hjq j hj) (hy j hj)
      a hp hp1 hr hr1 hu (sourceLinkAmbientCandidates_terminal W k U)
      (fun T hT ↦ (mem_sourceLinkAmbientCandidates_iff.mp hT).2) hblock hpa hw (hscale j hj)
      (fun _ result ↦ result.1) 1 0 hsigma hC le_rfl hpoint' historical (rawLinkSource_joint_geometry hgeometry hstruct hj) (cap j)
    have hC2 : (1 : ℝ≥0) ≤ C^2 := one_le_pow₀ hC
    have hb' : J.probability (fun result ↦ cap j <
        (sourceLinkForbiddenSamples (F j) (initial result.1) (later result.1) result.2.1 e).card) ≤
        sourceLinkFailureBound k.val j (s j) (Fintype.card V) (cap j) C b (y j) := by
      simpa only [sourceLinkFailureBound, max_eq_left hC2, add_zero] using hb
    exact hb'.trans (hscalar j hj)
  have hb := J.not_sampledLinkForbiddenOrdersGood_le_on_support (fun result ↦ links result.1) orders F
    (fun result ↦ initial result.1) (fun result ↦ later result.1) (fun result ↦ result.2.1) cap
    (crossingEdges Gamma U) (fun j _ ↦ error j) (rawLinkSource_joint_pins kernel hgeometry) htail
  apply hb.trans
  simp only [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast (card_le_univ (crossingEdges Gamma U)).trans (card_sym2_le_square V)

end

end Erdos207
