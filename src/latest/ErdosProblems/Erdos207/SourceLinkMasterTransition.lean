/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawLinkJointSourceSuccess
import ErdosProblems.Erdos207.ResidualRawLinkJointUpdate
import ErdosProblems.Erdos207.RawLinkCapsMasterUpdate
import ErdosProblems.Erdos207.FutureQuasiSourceProbability

/-! # One actual source-controlled joint link law supplies the master transition -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.exists_source_link_master_transition
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell q h : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    {Gamma : SimpleGraph V} {G : Omega → SimpleGraph V}
    {I D R A : Omega → TripleSystemOn V} {reserve : Omega → Finset (Sym2 V)}
    {p r C beta eta xi xi' epsilon : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W i.castSucc Gamma I
      (fun omega ↦ D omega ∪ R omega) reserve p r C beta)
    (links : Omega → {x : V // x ∉ W.U i.succ} → BipartiteLink V)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (y z linkError : ℕ → ℝ≥0) (linkMoment cap : ℕ → ℕ)
    (futureY futureZ : Fin ell → ℕ → ℝ≥0) (quasiMoment : ℕ → ℕ) (quasiError : ℕ → ℝ≥0)
    (Good : Omega → Prop) (priorError degreeError : ℝ≥0)
    (a factor : ℝ≥0) (Delta collisionCap degree overlap collisionMoment t c degreeMoment : ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hC : 1 ≤ C) (hfactor : 1 ≤ factor)
    (hepsilon : 0 < epsilon) (hh : 1 ≤ h) (hxi : xi ≤ xi')
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hblock : r*a ≤ p*(W.U i.succ).card/(W.prefix i.castSucc).terminalSize)
    (hpa : p*a ≤ 1) (hw : 1 ≤ a*(W.prefix i.castSucc).terminalSize/(r*p^2*(W.U i.succ).card))
    (hsigma : a/(r*p^2*(W.U i.succ).card) ≤ 1)
    (hnew : (a/(r*p^2*(W.U i.succ).card))*p^3*r^2 ≤ factor*(p/(W.U i.castSucc).card))
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix i.castSucc) j (F j) (y j) (z j))
    (hjq : ∀ j ∈ orders, j ≤ q) (hy : ∀ j ∈ orders, 1 ≤ y j)
    (hscale : ∀ j ∈ orders, z j*(a*(W.prefix i.castSucc).terminalSize/(r*p^2*(W.U i.succ).card))^(q+1)/
      (W.prefix i.castSucc).terminalSize ≤ y j)
    (hscalar : ∀ j ∈ orders,
      sourceLinkFailureBound i.val j (linkMoment j) (Fintype.card V) (cap j) C beta (y j) ≤ linkError j)
    (hdis : L.SupportedOn fun omega ↦ Disjoint (I omega) (D omega ∪ R omega))
    (hgeometry : L.SupportedOn fun omega ↦ RawLinkSourceGeometry W i.castSucc Gamma (W.U i.succ)
      (I omega) (D omega ∪ R omega) (D omega) (A omega) (reserve omega)
      (outsideVertexEmbedding (W.U i.succ)) (links omega) orders F)
    (hbase : L.SupportedOn fun omega ↦ IsPackingOn (I omega ∪ (D omega ∪ R omega)) ∧
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) (orders.biUnion F))
    (hprior : L.probability (fun omega ↦ ¬ Good omega) ≤ priorError)
    (hmatching : ∀ omega, 0 < L.mass omega → Good omega →
      RawLinkMatchingGeometry (W.U i.succ) (outsideVertexEmbedding (W.U i.succ)) (links omega)
        (orders.biUnion F) (A omega) (I omega) (D omega ∪ R omega)
        (a/(r*p^2*(W.U i.succ).card)) Delta collisionCap (∑ j ∈ orders, cap j)
        degree overlap collisionMoment t (Fintype.card V) c)
    (heven : HasEvenStageGraphs L G)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W i.castSucc (orders.biUnion F) G A I D p eta xi h))
    (hstate : L.SupportedOn fun omega ↦ IsIntermediateLinkState (G omega) (W.U i.succ)
      (A omega) (I omega) (D omega) (R omega) (links omega))
    (hmeet : L.SupportedOn fun omega ↦ TrianglesMeetAtMostOne (W.U i.succ) (R omega))
    (hGbase : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hloss : (1+h+h^2 : ℕ)*epsilon ≤ xi'-xi)
    (hsupport : ∀ a ∈ futureLevelPairs i.succ,
      (h : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card)
    (hdegreeSize : ∀ a ∈ futureLevelPairs i.succ,
      (2*degreeMoment : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card)
    (hdegreeScalar : (2*(overlap+1 : ℝ≥0)*(a/(r*p^2*(W.U i.succ).card))/
      (epsilon*p^h*eta^(h^2)))^degreeMoment ≤ degreeError)
    (hfutureSource : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ orders,
      SourceVortexWellSpread (W.prefix a.1.castSucc) j (F j) (futureY a.1 j) (futureZ a.1 j))
    (hfutureScale : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ orders,
      futureZ a.1 j ≤ futureY a.1 j*p^(h+1)*(W.U a.2).card)
    (hquasiScalar : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ orders,
      sourceQuasiUniformFailureBound a.1.val j (quasiMoment j) h (Fintype.card V)
        p (2*max (C^5*factor) 1) beta (futureY a.1 j) (epsilon/(orders.card+1 : ℝ≥0)) eta
          (W.U a.2).card ≤ quasiError j) :
    let coverageError := priorError +
      rawLinkGeometricFailure (Fintype.card {x : V // x ∉ W.U i.succ}) (Fintype.card V)
        degree overlap collisionCap collisionMoment t (a/(r*p^2*(W.U i.succ).card)) +
      (Fintype.card V : ℝ≥0)^2*∑ j ∈ orders, linkError j
    coverageError < 1 →
    (priorError+(ell*(ell+1) : ℕ)*Fintype.card V*degreeError) +
      (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(Fintype.card V+1 : ℝ≥0)^(2*h^2))*h^2*
        ∑ j ∈ orders, quasiError j ≤ xi'*(1-coverageError) →
    ∃ kernel : Omega → FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      let joint := L.jointBind kernel
      let Success := fun z : Omega × (TripleSystemOn V × TripleSystemOn V) ↦
        ∀ o, CoversBipartiteLink (links z.1 o) z.2.2
      ∃ hpos : 0 < joint.probability Success,
        1-coverageError ≤ joint.probability Success ∧
        IsResidualMasterIterationGood (joint.conditionOn Success hpos) W i.succ Gamma (orders.biUnion F)
          (fun z ↦ updatedStageGraph (G z.1) (W.U i.succ) (R z.1 ∪ z.2.2))
          (fun z ↦ updatedStageAvailable (orders.biUnion F) (W.U i.succ)
            (A z.1) (I z.1) (D z.1) (R z.1 ∪ z.2.2))
          (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ (R z.1 ∪ z.2.2))
          p eta xi' ((2*max (C^5*factor) 1)/(1-coverageError)) beta h ∧
        (joint.conditionOn Success hpos).SupportedOn fun z ↦
          IsMasterCoverStep (orders.biUnion F) (G z.1) (W.U i.succ)
            (A z.1) (I z.1) (D z.1) (R z.1 ∪ z.2.2) := by
  dsimp only
  intro hcoverageError hfutureBudget
  obtain ⟨kernel, hstruct, hpoint, _hselectedPoint, hcover⟩ :=
    hstrong.exists_rawLinkJoint_source_success hdis (W.U i.succ)
      (fun _ ↦ outsideVertexEmbedding (W.U i.succ)) links orders F y z linkError linkMoment cap
      a hp hp1 hr hr1 (card_pos.mpr (hnonempty i.succ)) hC hblock hpa hw hsigma hsource hjq hy hscale
      hscalar hgeometry hbase Good priorError hprior Delta collisionCap degree overlap collisionMoment
      t (Fintype.card V) c hmatching
  let joint := L.jointBind kernel
  have hnext : i.castSucc ≤ i.succ := by exact Fin.le_iff_val_le_val.mpr (by simp)
  have hupdated := hstrong.jointBind_rawLinkJoint_numeric (kernel := kernel) (next := i.succ)
    (W.U i.succ) (fun _ ↦ outsideVertexEmbedding (W.U i.succ)) links orders F
    (a/(r*p^2*(W.U i.succ).card)) factor hC hfactor hsigma hnext hnonempty hnew
    hgeometry hstruct (fun omega _ ↦ hpoint omega)
  have hCnew : (1 : ℝ≥0) ≤ 2*max (C^5*factor) 1 := by
    calc
      _ ≤ max (C^5*factor) 1 := le_max_right _ _
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : ℝ≥0) ≤ 2 by norm_num) (show 0 ≤ max (C^5*factor) 1 from zero_le)
  have hstructJoint : joint.SupportedOn fun z ↦ IsSampledLinkJointOutcome (orders.biUnion F)
      (A z.1) (I z.1 ∪ (D z.1 ∪ R z.1)) (links z.1) z.2 := by
    intro sample hm
    have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp hm
    exact hstruct sample.1 hmasses.1 sample.2 hmasses.2
  have hdisJoint : joint.SupportedOn fun z ↦ Disjoint (I z.1) ((D z.1 ∪ R z.1) ∪ z.2.2) := by
    intro sample hm
    have hmasses := (L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp hm
    exact disjoint_union_right.mpr ⟨hdis sample.1 hmasses.1,
      (hstructJoint sample hm).selected_safe.2.1.mono_left subset_union_left⟩
  have hquasi := hupdated.futureQuasiCaps_probability_le hdisJoint hnonempty orders F futureY futureZ
    quasiMoment epsilon eta quasiError hp hp1 hCnew hepsilon heta heta1 hfutureSource hfutureScale hquasiScalar
  have hdegree := L.rawLinkJoint_futureDegree_failure_le kernel W i.succ hnonempty (orders.biUnion F)
    links A (fun omega ↦ I omega ∪ (D omega ∪ R omega)) R G Good
    (a/(r*p^2*(W.U i.succ).card)) p eta epsilon degreeError priorError overlap degreeMoment h
    hp heta hepsilon hprior hstruct (fun omega _ ↦ hpoint omega)
    (fun omega hm _ ↦ hmeet omega hm)
    (fun omega hm hg o ↦ (hgeometry omega hm).center_eq o ▸ (hgeometry omega hm).center_outside o)
    (fun omega hm hg ↦ (hmatching omega hm hg).overlap_bound) hdegreeSize hdegreeScalar
  have liftSupport {P : Omega → Prop} (hP : L.SupportedOn P) :
      joint.SupportedOn (fun z ↦ P z.1) := by
    intro sample hm
    exact hP sample.1 ((L.jointBind_mass_pos_iff kernel sample.1 sample.2).mp hm).1
  have hquasi' : joint.probability (fun sample ↦ ¬ FutureQuasiCaps W i.succ (orders.biUnion F)
      Gamma (I sample.1) (D sample.1 ∪ (R sample.1 ∪ sample.2.2)) p eta epsilon h) ≤
      (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(Fintype.card V+1 : ℝ≥0)^(2*h^2))*h^2*
        ∑ j ∈ orders, quasiError j := by
    simpa only [union_assoc] using hquasi
  obtain ⟨hpos, hprob, hmaster⟩ := residualMasterIterationGood_of_rawLink_joint_caps
    hupdated (liftSupport heven) (liftSupport hold) (liftSupport hstate) hstructJoint
    hcover hcoverageError (liftSupport hGbase) hnext hxi hp1 heta1 hh hloss hsupport
    hdegree hquasi' hfutureBudget
  refine ⟨kernel, hpos, hprob, hmaster, ?_⟩
  have hstructConditioned := hstructJoint.conditionOn hpos
  have hstateConditioned := (liftSupport hstate).conditionOn hpos
  have hcovered := joint.conditionOn_supported _ hpos
  intro sample hm
  exact (hstructConditioned sample hm).masterCoverStep (hstateConditioned sample hm) (hcovered sample hm)

end

end Erdos207
