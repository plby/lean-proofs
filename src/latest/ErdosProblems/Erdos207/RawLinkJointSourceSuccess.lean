/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawLinkMatchingGeometry
import ErdosProblems.Erdos207.RawSampledLinkJointKernel
import ErdosProblems.Erdos207.SourceLinkJointForbiddenProbability

/-! # The actual raw simultaneous-link kernel succeeds by the source joint marked moments -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.exists_rawLinkJoint_source_success
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V] {ell q : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V}
    {initial later historical available : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k Gamma initial later reserve p r C b)
    (hdis : L.SupportedOn fun omega ↦ Disjoint (initial omega) (later omega))
    (U : Finset V) (center : Ω → O ↪ V) (links : Ω → O → BipartiteLink V)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V) (y z error : ℕ → ℝ≥0) (moment cap : ℕ → ℕ)
    (a : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hu : 0 < U.card) (hC : 1 ≤ C)
    (hblock : r*a ≤ p*U.card/(W.prefix k).terminalSize) (hpa : p*a ≤ 1)
    (hw : 1 ≤ a*(W.prefix k).terminalSize/(r*p^2*U.card)) (hsigma : a/(r*p^2*U.card) ≤ 1)
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix k) j (F j) (y j) (z j))
    (hjq : ∀ j ∈ orders, j ≤ q) (hy : ∀ j ∈ orders, 1 ≤ y j)
    (hscale : ∀ j ∈ orders,
      z j*(a*(W.prefix k).terminalSize/(r*p^2*U.card))^(q+1)/(W.prefix k).terminalSize ≤ y j)
    (hscalar : ∀ j ∈ orders, sourceLinkFailureBound k.val j (moment j) (Fintype.card V) (cap j) C b (y j) ≤ error j)
    (hgeometry : L.SupportedOn fun omega ↦ RawLinkSourceGeometry W k Gamma U (initial omega) (later omega)
      (historical omega) (available omega) (reserve omega) (center omega) (links omega) orders F)
    (hbase : L.SupportedOn fun omega ↦ IsPackingOn (initial omega ∪ later omega) ∧
      AvoidsForbidden (initial omega ∪ later omega) (orders.biUnion F))
    (Good : Ω → Prop) (priorError : ℝ≥0) (hprior : L.probability (fun omega ↦ ¬ Good omega) ≤ priorError)
    (Delta collisionCap degree overlap s t N c : ℕ)
    (hmatching : ∀ omega, 0 < L.mass omega → Good omega →
      RawLinkMatchingGeometry U (center omega) (links omega) (orders.biUnion F) (available omega)
        (initial omega) (later omega) (a/(r*p^2*U.card)) Delta collisionCap (∑ j ∈ orders, cap j)
          degree overlap s t N c) :
    ∃ kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      (∀ omega, 0 < L.mass omega → (kernel omega).SupportedOn
        (IsSampledLinkJointOutcome (orders.biUnion F) (available omega)
          (initial omega ∪ later omega) (links omega))) ∧
      (∀ omega, ∀ Q : TripleSystemOn V,
        (kernel omega).probability (fun result ↦ Q ⊆ result.1) ≤ (a/(r*p^2*U.card))^Q.card) ∧
      (∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
        (kernel omega).probability (fun result ↦ Q ⊆ result.2) ≤ (a/(r*p^2*U.card))^Q.card) ∧
      (L.jointBind kernel).probability (fun result ↦ ¬ ∀ o, CoversBipartiteLink (links result.1 o) result.2.2) ≤
        priorError+rawLinkGeometricFailure (Fintype.card O) N degree overlap collisionCap s t (a/(r*p^2*U.card))+
          (Fintype.card V : ℝ≥0)^2*∑ j ∈ orders, error j := by
  obtain ⟨kernel, hstruct, hpoint, hfail⟩ := exists_rawSampledLinkJointKernel L (orders.biUnion F)
    available initial later links Good (a/(r*p^2*U.card))
    (rawLinkGeometricFailure (Fintype.card O) N degree overlap collisionCap s t (a/(r*p^2*U.card)))
    (∑ j ∈ orders, cap j) hbase (fun omega hmass hgood ↦ (hmatching omega hmass hgood).exists_joint_law hsigma)
  have hforbidden := hstrong.rawLinkJoint_forbidden_probability_le (kernel := kernel) (q := q) hdis
    U center links orders F y z error moment cap a hp hp1 hr hr1 hu hC hblock hpa hw hsigma
    hsource hjq hy hscale hscalar hstruct (fun omega _ ↦ hpoint omega) hgeometry
  refine ⟨kernel, hstruct, hpoint, ?_, hfail priorError _ hprior hforbidden⟩
  intro omega hmass Q
  exact (kernel omega).sampledLinkJoint_selected_probability_le (hstruct omega hmass)
    (a/(r*p^2*U.card)) (hpoint omega) Q

end

end Erdos207
