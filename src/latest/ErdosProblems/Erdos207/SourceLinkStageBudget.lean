/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAbsorberLinkCompression
import ErdosProblems.Erdos207.SourceReserveMatchingPreparation
import ErdosProblems.Erdos207.SourcePrefixCoefficients
import ErdosProblems.Erdos207.SourceMasterConstants

/-! # Explicit numeric inputs finish the actual prepared link stage -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure SourceLinkStageBudget
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q h : ℕ) (W : Vortex V ell) (i : Fin ell) (bank : TripleSystemOn V)
    (p r C beta eta xi xi' : ℝ≥0) where
  a : ℝ≥0
  referenceTolerance : ℝ≥0
  epsilon : ℝ≥0
  d : ℕ
  degreeError : ℝ≥0
  futureDegreeError : ℝ≥0
  priorError : ℝ≥0
  Delta : ℕ
  collisionCap : ℕ
  degree : ℕ
  overlap : ℕ
  collisionMoment : ℕ
  scale : ℕ
  c : ℕ
  overlapMoment : ℕ
  degreeMoment : ℕ
  linkMoment : ℕ → ℕ
  cap : ℕ → ℕ
  quasiMoment : ℕ → ℕ
  linkError : ℕ → ℝ≥0
  quasiError : ℕ → ℝ≥0
  reference_small : referenceTolerance ≤ 1/524288
  degree_loss : (2*d : ℝ≥0) ≤ referenceTolerance*r*p^3*eta^2*(W.U i.succ).card
  reference_large : (18*(65537+4*scale) : ℕ) ≤ r*p^2*eta*(W.U i.succ).card
  hall_upper : (c : ℝ≥0) ≤ r*p^2*eta*(W.U i.succ).card/40
  degree_lower : 2*r*p^2*eta*(W.U i.succ).card ≤ degree
  cap_budget : collisionCap+∑ j ∈ Icc 4 q, cap j ≤ Delta
  collision_moment : 2*collisionMoment ≤ collisionCap+1
  hall_budget : (Delta+scale : ℝ≥0) ≤ (a/(r*p^2*(W.U i.succ).card))*c/2
  hall_small : 2*(Fintype.card V+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^scale ≤ 1/2
  overlap_moment : 2*overlapMoment ≤ overlap+1
  prior_bound : degreeError+(Fintype.card V : ℝ≥0)^2*
    ((2*((W.U i.castSucc).card : ℝ≥0)*C^2*r^2/(overlap+1))^overlapMoment+
      (2*((W.U i.castSucc).card : ℝ≥0)*C^2/(overlap+1))^overlapMoment*beta) ≤ priorError
  block : r*a ≤ p*(W.U i.succ).card/(W.prefix i.castSucc).terminalSize
  pa : p*a ≤ 1
  marked_ge_one : 1 ≤ a*(W.prefix i.castSucc).terminalSize/(r*p^2*(W.U i.succ).card)
  sampling_le_one : a/(r*p^2*(W.U i.succ).card) ≤ 1
  point_charge : (a/(r*p^2*(W.U i.succ).card))*p^3*r^2 ≤ p/(W.U i.castSucc).card
  marked_scale : ∀ j ∈ Icc 4 q,
    sourcePrefixZ q bank i.val j*(a*(W.prefix i.castSucc).terminalSize/(r*p^2*(W.U i.succ).card))^(q+1)/
      (W.prefix i.castSucc).terminalSize ≤ sourcePrefixY q i.val
  link_scalar : ∀ j ∈ Icc 4 q,
    sourceLinkFailureBound i.val j (linkMoment j) (Fintype.card V) (cap j) C beta
      (sourcePrefixY q i.val) ≤ linkError j
  epsilon_pos : 0 < epsilon
  xi_mono : xi ≤ xi'
  loss : (1+h+h^2 : ℕ)*epsilon ≤ xi'-xi
  pattern_support : ∀ a ∈ futureLevelPairs i.succ,
    (h : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card
  degree_size : ∀ a ∈ futureLevelPairs i.succ,
    (2*degreeMoment : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card
  degree_scalar : (2*(overlap+1 : ℝ≥0)*(a/(r*p^2*(W.U i.succ).card))/
    (epsilon*p^h*eta^(h^2)))^degreeMoment ≤ futureDegreeError
  future_scale : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q,
    sourcePrefixZ q bank a.1.val j ≤ sourcePrefixY q a.1.val*p^(h+1)*(W.U a.2).card
  quasi_scalar : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q,
    sourceQuasiUniformFailureBound a.1.val j (quasiMoment j) h (Fintype.card V)
      p (2*max (C^5) 1) beta (sourcePrefixY q a.1.val) (epsilon/((Icc 4 q).card+1 : ℝ≥0)) eta
        (W.U a.2).card ≤ quasiError j
  coverage_half : priorError+
    rawLinkGeometricFailure (Fintype.card {x : V // x ∉ W.U i.succ}) (Fintype.card V)
      degree overlap collisionCap collisionMoment scale (a/(r*p^2*(W.U i.succ).card))+
    (Fintype.card V : ℝ≥0)^2*∑ j ∈ Icc 4 q, linkError j ≤ 1/2
  future_budget : (priorError+(ell*(ell+1) : ℕ)*Fintype.card V*futureDegreeError)+
    (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(Fintype.card V+1 : ℝ≥0)^(2*h^2))*h^2*
      ∑ j ∈ Icc 4 q, quasiError j ≤ xi'/2

theorem SourceLinkStageBudget.finish
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell q h : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell} {i : Fin ell}
    {Gamma : SimpleGraph V} {bank ambient : TripleSystemOn V} {G : Omega → SimpleGraph V}
    {I D P Q R A : Omega → TripleSystemOn V} {reserve : Omega → Finset (Sym2 V)}
    {bits : Omega → Sym2 V → Bool} {p r C beta eta xi xi' : ℝ≥0}
    (B : SourceLinkStageBudget q h W i bank p r C beta eta xi xi')
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hC : 1 ≤ C) (hh : 1 ≤ h)
    (hnonempty : ∀ j, (W.U j).Nonempty) (hsource : HasAbsorberSourcePrefixBounds q bank W)
    (hstrong : IsResidualReserveStronglyWellDistributed L W i.castSucc Gamma I
      (fun omega ↦ D omega ∪ R omega) reserve p r C beta)
    (Kold : Omega → {x : V // x ∉ W.U i.succ} → BipartiteLink V)
    (hstate : L.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) (W.U i.succ) (A omega) (I omega) (D omega) (R omega) (Kold omega) ∧
      (∀ o, (Kold omega o).left ⊆ W.U i.succ) ∧
      (∀ o, (Kold omega o).right ⊆ W.U i.succ) ∧
      (∀ o, (Kold omega o).SpokesIn (reserve omega)))
    (heven : HasEvenStageGraphs L G)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W i.castSucc
      (absorberErdosForbiddenConfigurationsOn q bank) G A I D p eta xi h))
    (hbase : L.SupportedOn fun omega ↦ IsPackingOn (I omega ∪ (D omega ∪ R omega)) ∧
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) (absorberSourceFamily q bank))
    (hmeet : L.SupportedOn fun omega ↦ TrianglesMeetAtMostOne (W.U i.succ) (R omega))
    (hGbase : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hGsupp : L.SupportedOn fun omega ↦ GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (havailable : L.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : L.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : L.SupportedOn fun omega ↦ CoversOriginalGraph Gamma (G omega) (I omega) (D omega))
    (hprotected : L.SupportedOn fun omega ↦ P omega ⊆
      reserveProtectedAvailable (reserveEdges (G omega) (W.U i.succ) (bits omega)) (A omega))
    (hR : L.SupportedOn fun omega ↦ R omega = P omega ∪ Q omega)
    (hdis : L.SupportedOn fun omega ↦ Disjoint (P omega) (Q omega))
    (huse : L.SupportedOn fun omega ↦ NewTrianglesUseScheduledOuterEdges (W.U i.succ)
      (preliminaryResidualInternalEdges (G omega) (W.U i.succ) (P omega)) (P omega) (R omega))
    (hreference : L.SupportedOn fun omega ↦ ReserveLinkReferenceGood (G omega) (A omega)
      (W.U i.castSucc) (W.U i.succ) (reserveEdges (G omega) (W.U i.succ) (bits omega))
      ((r : ℝ)*p*(W.U i.succ).card) ((p : ℝ)*eta) B.referenceTolerance)
    (hdegreeFailure : L.probability (fun omega ↦ ¬ PreliminaryResidualDegreeGood
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) (W.U i.succ) (P omega) B.d) ≤ B.degreeError) :
    ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W i.succ (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta xi' (4*max (C^5) 1) beta h := by
  have hrhoNN : p*eta ≤ 1 := by simpa only [mul_one] using mul_le_mul hp1 heta1 zero_le zero_le
  have hrho : (p : ℝ)*eta ≤ 1 := by exact_mod_cast hrhoNN
  have hreferenceSmall : (B.referenceTolerance : ℝ) ≤ 1/524288 := by exact_mod_cast B.reference_small
  have hloss : (2*B.d : ℕ) ≤ (B.referenceTolerance : ℝ)*((p : ℝ)*eta)^2*((r : ℝ)*p*(W.U i.succ).card) := by
    have hh : (2*B.d : ℝ≥0) ≤ B.referenceTolerance*(p*eta)^2*(r*p*(W.U i.succ).card) := by
      calc
        _ ≤ _ := B.degree_loss
        _ = _ := by ring
    exact_mod_cast hh
  have hlarge : (18*(65537+4*B.scale) : ℕ) ≤ ((p : ℝ)*eta)*((r : ℝ)*p*(W.U i.succ).card) := by
    have hh : (18*(65537+4*B.scale) : ℕ) ≤ (p*eta)*(r*p*(W.U i.succ).card) := by
      calc
        _ ≤ _ := B.reference_large
        _ = _ := by ring
    exact_mod_cast hh
  have hc : (B.c : ℝ) ≤ (((p : ℝ)*eta)*((r : ℝ)*p*(W.U i.succ).card))/40 := by
    have hh : (B.c : ℝ≥0) ≤ ((p*eta)*(r*p*(W.U i.succ).card))/40 := by
      calc
        _ ≤ _ := B.hall_upper
        _ = _ := by ring
    exact_mod_cast hh
  have hdegree : 2*((p : ℝ)*eta)*((r : ℝ)*p*(W.U i.succ).card) ≤ B.degree := by
    have hh : 2*(p*eta)*(r*p*(W.U i.succ).card) ≤ (B.degree : ℝ≥0) := by
      calc
        _ = 2*r*p^2*eta*(W.U i.succ).card := by ring
        _ ≤ _ := B.degree_lower
    exact_mod_cast hh
  obtain ⟨links, hlinks, hmatching, hprior⟩ := hstrong.exists_source_reserve_matching_preparation
    (W.U i.castSucc) (W.U i.succ) (absorberSourceFamily q bank) Kold
    (fun omega hm ↦ (hstate omega hm).1) (fun omega hm ↦ (hstate omega hm).2.1)
    (fun omega hm ↦ (hstate omega hm).2.2.1) (fun omega hm ↦ (hstate omega hm).2.2.2)
    hGsupp (fun omega hm ↦ (hold omega hm).2.2.2.2.2.1)
    (fun omega hm ↦ (hold omega hm).2.2.2.2.1) hmeet
    (fun omega hm ↦ (hbase omega hm).1) (fun omega hm ↦ (hbase omega hm).2)
    hprotected hR hdis huse ((r : ℝ)*p*(W.U i.succ).card) ((p : ℝ)*eta)
    B.referenceTolerance hreference (by positivity) (by positivity) hrho
    (by positivity) hreferenceSmall B.d B.degreeError hloss hdegreeFailure
    (B.a/(r*p^2*(W.U i.succ).card)) B.Delta B.collisionCap (∑ j ∈ Icc 4 q, B.cap j)
    B.degree B.overlap B.collisionMoment B.scale B.c B.overlapMoment hlarge hc hdegree
    B.cap_budget B.collision_moment B.hall_budget B.hall_small B.overlap_moment
  have hcoverage : B.priorError+
      rawLinkGeometricFailure (Fintype.card {x : V // x ∉ W.U i.succ}) (Fintype.card V)
        B.degree B.overlap B.collisionCap B.collisionMoment B.scale (B.a/(r*p^2*(W.U i.succ).card))+
      (Fintype.card V : ℝ≥0)^2*∑ j ∈ Icc 4 q, B.linkError j < 1 :=
    B.coverage_half.trans_lt (by norm_num)
  have hhalf : (1/2 : ℝ≥0) ≤ 1-(B.priorError+
      rawLinkGeometricFailure (Fintype.card {x : V // x ∉ W.U i.succ}) (Fintype.card V)
        B.degree B.overlap B.collisionCap B.collisionMoment B.scale (B.a/(r*p^2*(W.U i.succ).card))+
      (Fintype.card V : ℝ≥0)^2*∑ j ∈ Icc 4 q, B.linkError j) := by
    calc
      (1/2 : ℝ≥0) = 1-1/2 := by
        apply NNReal.coe_injective
        rw [NNReal.coe_sub (by norm_num : (1/2 : ℝ≥0) ≤ 1)]
        norm_num
      _ ≤ _ := tsub_le_tsub_left B.coverage_half (1 : ℝ≥0)
  have hfuture := B.future_budget.trans (show xi'/2 ≤ xi'*(1-(B.priorError+
      rawLinkGeometricFailure (Fintype.card {x : V // x ∉ W.U i.succ}) (Fintype.card V)
        B.degree B.overlap B.collisionCap B.collisionMoment B.scale (B.a/(r*p^2*(W.U i.succ).card))+
      (Fintype.card V : ℝ≥0)^2*∑ j ∈ Icc 4 q, B.linkError j)) from
      by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hhalf (zero_le (a := xi')))
  obtain ⟨law, hlaw⟩ := hstrong.exists_source_absorber_compressed_link_transition i links
    (fun _ ↦ sourcePrefixY q i.val) (sourcePrefixZ q bank i.val) B.linkError B.linkMoment B.cap
    (fun a _ ↦ sourcePrefixY q a.val) (fun a ↦ sourcePrefixZ q bank a.val) B.quasiMoment B.quasiError
    _ B.priorError B.futureDegreeError B.a 1 B.Delta B.collisionCap B.degree B.overlap
    B.collisionMoment B.scale B.c B.degreeMoment hp hp1 hr hr1 heta heta1 hC le_rfl B.epsilon_pos
    hh B.xi_mono hnonempty B.block B.pa B.marked_ge_one B.sampling_le_one
    (by simpa only [one_mul] using B.point_charge)
    (fun j hj ↦ hsource.at_stage i.castSucc j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2)
    (fun _ _ ↦ one_le_sourcePrefixY q i.val) B.marked_scale B.link_scalar hbase
    (hprior.trans B.prior_bound) hmatching heven hold hlinks hmeet hGbase hGsupp havailable hselected hcover
    B.loss B.pattern_support B.degree_size B.degree_scalar
    (fun a _ j hj ↦ hsource.at_stage a.1.castSucc j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2)
    B.future_scale (by simpa only [mul_one] using B.quasi_scalar) hcoverage hfuture
  refine ⟨law, hlaw.mono_constants ?_ le_rfl⟩
  have hcst := conditioning_constant_le_double (2*max (C^5) 1) _ B.coverage_half
  simpa only [mul_one, show (2 : ℝ≥0)*(2*max (C^5) 1) = 4*max (C^5) 1 by ring] using hcst

end

end Erdos207
