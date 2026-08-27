/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMasterTransition
import ErdosProblems.Erdos207.SupportedReserveMatchingLinks
import ErdosProblems.Erdos207.AbsorberSourceFamilyTransfer
import ErdosProblems.Erdos207.ResidualUpdatedCompression
import ErdosProblems.Erdos207.ConditionedCompressedReserveStage

/-! # The actual successful link law restores and compresses the full absorber invariant -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.exists_source_absorber_compressed_link_transition
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V]
    {ell q h : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    {Gamma : SimpleGraph V} {bank ambient : TripleSystemOn V} {G : Omega → SimpleGraph V}
    {I D R A : Omega → TripleSystemOn V} {reserve : Omega → Finset (Sym2 V)}
    {p r C beta eta xi xi' epsilon : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W i.castSucc Gamma I
      (fun omega ↦ D omega ∪ R omega) reserve p r C beta)
    (links : Omega → {x : V // x ∉ W.U i.succ} → BipartiteLink V)
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
    (hsource : ∀ j ∈ Icc 4 q, SourceVortexWellSpread (W.prefix i.castSucc) j
      (absorberInducedConfigurationsOn q j bank) (y j) (z j))
    (hy : ∀ j ∈ Icc 4 q, 1 ≤ y j)
    (hscale : ∀ j ∈ Icc 4 q, z j*(a*(W.prefix i.castSucc).terminalSize/(r*p^2*(W.U i.succ).card))^(q+1)/
      (W.prefix i.castSucc).terminalSize ≤ y j)
    (hscalar : ∀ j ∈ Icc 4 q,
      sourceLinkFailureBound i.val j (linkMoment j) (Fintype.card V) (cap j) C beta (y j) ≤ linkError j)
    (hbase : L.SupportedOn fun omega ↦ IsPackingOn (I omega ∪ (D omega ∪ R omega)) ∧
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) (absorberSourceFamily q bank))
    (hprior : L.probability (fun omega ↦ ¬ Good omega) ≤ priorError)
    (hmatching : ∀ omega, 0 < L.mass omega → Good omega →
      RawLinkMatchingGeometry (W.U i.succ) (outsideVertexEmbedding (W.U i.succ)) (links omega)
        (absorberSourceFamily q bank) (A omega) (I omega) (D omega ∪ R omega)
        (a/(r*p^2*(W.U i.succ).card)) Delta collisionCap (∑ j ∈ Icc 4 q, cap j)
        degree overlap collisionMoment t (Fintype.card V) c)
    (heven : HasEvenStageGraphs L G)
    (hold : L.SupportedOn (masterPointwiseGoodEvent W i.castSucc
      (absorberErdosForbiddenConfigurationsOn q bank) G A I D p eta xi h))
    (hstate : L.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) (W.U i.succ) (A omega) (I omega) (D omega) (R omega) (links omega) ∧
      (∀ o, (links omega o).left ⊆ W.U i.succ) ∧
      (∀ o, (links omega o).right ⊆ W.U i.succ) ∧
      (∀ o, (links omega o).SpokesIn (reserve omega)))
    (hmeet : L.SupportedOn fun omega ↦ TrianglesMeetAtMostOne (W.U i.succ) (R omega))
    (hGbase : L.SupportedOn fun omega ↦ G omega ≤ Gamma)
    (hGsupp : L.SupportedOn fun omega ↦ GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (havailable : L.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : L.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : L.SupportedOn fun omega ↦ CoversOriginalGraph Gamma (G omega) (I omega) (D omega))
    (hloss : (1+h+h^2 : ℕ)*epsilon ≤ xi'-xi)
    (hsupport : ∀ a ∈ futureLevelPairs i.succ,
      (h : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card)
    (hdegreeSize : ∀ a ∈ futureLevelPairs i.succ,
      (2*degreeMoment : ℝ≥0) ≤ epsilon*p^h*eta^(h^2)*(W.U a.2).card)
    (hdegreeScalar : (2*(overlap+1 : ℝ≥0)*(a/(r*p^2*(W.U i.succ).card))/
      (epsilon*p^h*eta^(h^2)))^degreeMoment ≤ degreeError)
    (hfutureSource : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q,
      SourceVortexWellSpread (W.prefix a.1.castSucc) j
        (absorberInducedConfigurationsOn q j bank) (futureY a.1 j) (futureZ a.1 j))
    (hfutureScale : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q,
      futureZ a.1 j ≤ futureY a.1 j*p^(h+1)*(W.U a.2).card)
    (hquasiScalar : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q,
      sourceQuasiUniformFailureBound a.1.val j (quasiMoment j) h (Fintype.card V)
        p (2*max (C^5*factor) 1) beta (futureY a.1 j) (epsilon/((Icc 4 q).card+1 : ℝ≥0)) eta
          (W.U a.2).card ≤ quasiError j) :
    let coverageError := priorError +
      rawLinkGeometricFailure (Fintype.card {x : V // x ∉ W.U i.succ}) (Fintype.card V)
        degree overlap collisionCap collisionMoment t (a/(r*p^2*(W.U i.succ).card)) +
      (Fintype.card V : ℝ≥0)^2*∑ j ∈ Icc 4 q, linkError j
    coverageError < 1 →
    (priorError+(ell*(ell+1) : ℕ)*Fintype.card V*degreeError) +
      (ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(Fintype.card V+1 : ℝ≥0)^(2*h^2))*h^2*
        ∑ j ∈ Icc 4 q, quasiError j ≤ xi'*(1-coverageError) →
    ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W i.succ (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta xi' ((2*max (C^5*factor) 1)/(1-coverageError)) beta h := by
  dsimp only
  intro hcoverageError hfutureBudget
  have holdSource : L.SupportedOn (masterPointwiseGoodEvent W i.castSucc
      (absorberSourceFamily q bank) G A I D p eta xi h) :=
    fun omega hm ↦ (hold omega hm).to_absorberSource
  have htri : L.SupportedOn fun omega ↦ ConsistsOfTriangles (G omega) (A omega) :=
    fun omega hm ↦ (hold omega hm).2.2.2.2.2.1
  have hinitial : L.SupportedOn fun omega ↦ ∀ T ∈ A omega,
      ¬ CompletesForbidden (absorberSourceFamily q bank) (I omega ∪ D omega) T :=
    fun omega hm ↦ (holdSource omega hm).2.2.2.2.2.2
  have hgeometry := supported_rawLinkSourceGeometry_of_intermediate L W i.castSucc Gamma
    (W.U i.succ) G I D R A reserve links hstate hGbase hGsupp htri (Icc 4 q)
    (fun j ↦ absorberInducedConfigurationsOn q j bank) hinitial
  have hdis : L.SupportedOn fun omega ↦ Disjoint (I omega) (D omega ∪ R omega) :=
    fun omega hm ↦ (hstate omega hm).1.2.2
  obtain ⟨kernel, hpos, hlower, hmaster, hstep⟩ :=
    hstrong.exists_source_link_master_transition i links (Icc 4 q)
      (fun j ↦ absorberInducedConfigurationsOn q j bank) y z linkError linkMoment cap
      futureY futureZ quasiMoment quasiError Good priorError degreeError a factor
      Delta collisionCap degree overlap collisionMoment t c degreeMoment hp hp1 hr hr1 heta heta1
      hC hfactor hepsilon hh hxi hnonempty hblock hpa hw hsigma hnew hsource
      (fun j hj ↦ (mem_Icc.mp hj).2) hy hscale hscalar hdis hgeometry hbase hprior hmatching
      heven holdSource (fun omega hm ↦ (hstate omega hm).1) hmeet hGbase hloss hsupport hdegreeSize
      hdegreeScalar hfutureSource hfutureScale hquasiScalar hcoverageError hfutureBudget
  have holdJoint := hold.jointBind_fst (kernel := kernel)
  have holdGood := holdJoint.conditionOn hpos
  obtain ⟨hfull, hfullStep⟩ := hmaster.restore_updated_absorber holdGood hstep
  exact ⟨_, hfull.compress_updated hfullStep
    ((havailable.jointBind_fst (kernel := kernel)).conditionOn hpos)
    ((hselected.jointBind_fst (kernel := kernel)).conditionOn hpos)
    ((hcover.jointBind_fst (kernel := kernel)).conditionOn hpos)
    ((hGbase.jointBind_fst (kernel := kernel)).conditionOn hpos)⟩

end

end Erdos207
