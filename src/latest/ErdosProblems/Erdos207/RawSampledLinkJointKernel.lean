/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawSampledLinkJointLaw
import ErdosProblems.Erdos207.FiniteJointAdditiveFailure

/-! # Totalizing the varying-link joint sampler and retaining its actual failure probability -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem isSampledLinkJointOutcome_empty
    {O V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A P : TripleSystemOn V) (K : O → BipartiteLink V)
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F) :
    IsSampledLinkJointOutcome F A P K (∅,∅) := by
  refine ⟨empty_subset _, empty_subset _, ?_, ?_, ?_, ?_⟩
  · simp only [forall_mem_empty_iff]
  · exact ⟨empty_subset _, disjoint_empty_right _, by simpa only [union_empty] using hpacking,
      by simpa only [union_empty] using havoid⟩
  · exact fun T hT ↦ (notMem_empty T hT).elim
  · exact fun T hT ↦ (notMem_empty T hT).elim

theorem pure_empty_linkJoint_inclusion
    {V : Type*} [Fintype V] [DecidableEq V] (sigma : ℝ≥0) (Q : TripleSystemOn V) :
    (FiniteLaw.pure ((∅ : TripleSystemOn V), (∅ : TripleSystemOn V))).probability
      (fun result ↦ Q ⊆ result.1) ≤ sigma^Q.card := by
  rw [FiniteLaw.probability_pure]
  by_cases hQ : Q = ∅
  · subst Q
    simp
  · have hnot : ¬ Q ⊆ (∅ : TripleSystemOn V) := by simpa only [subset_empty] using hQ
    simp only [hnot, if_false]
    exact zero_le

theorem exists_rawSampledLinkJointKernel
    {Ω O V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (F : ForbiddenFamilyOn V) (A I D : Ω → TripleSystemOn V)
    (links : Ω → O → BipartiteLink V) (Good : Ω → Prop) (sigma conditionalError : ℝ≥0) (forbiddenCap : ℕ)
    (hbase : L.SupportedOn fun omega ↦ IsPackingOn (I omega ∪ D omega) ∧ AvoidsForbidden (I omega ∪ D omega) F)
    (hready : ∀ omega, 0 < L.mass omega → Good omega →
      ∃ law : FiniteLaw (TripleSystemOn V × TripleSystemOn V),
        law.SupportedOn (IsSampledLinkJointOutcome F (A omega) (I omega ∪ D omega) (links omega)) ∧
        (∀ Q : TripleSystemOn V, law.probability (fun result ↦ Q ⊆ result.1) ≤ sigma^Q.card) ∧
        law.probability (fun result ↦ ¬ ∀ o, CoversBipartiteLink (links omega o) result.2) ≤ conditionalError+
          law.probability (fun result ↦ ¬ IsSampledLinkForbiddenGood (links omega) F (I omega) (D omega) result.1 forbiddenCap)) :
    ∃ kernel : Ω → FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      (∀ omega, 0 < L.mass omega → (kernel omega).SupportedOn
        (IsSampledLinkJointOutcome F (A omega) (I omega ∪ D omega) (links omega))) ∧
      (∀ omega, ∀ Q : TripleSystemOn V,
        (kernel omega).probability (fun result ↦ Q ⊆ result.1) ≤ sigma^Q.card) ∧
      ∀ priorError obstructionError : ℝ≥0,
        L.probability (fun omega ↦ ¬ Good omega) ≤ priorError →
        (L.jointBind kernel).probability (fun result ↦
          ¬ IsSampledLinkForbiddenGood (links result.1) F (I result.1) (D result.1) result.2.1 forbiddenCap) ≤ obstructionError →
        (L.jointBind kernel).probability (fun result ↦ ¬ ∀ o, CoversBipartiteLink (links result.1 o) result.2.2) ≤
          priorError+conditionalError+obstructionError := by
  have hchoice : ∀ omega, ∃ law : FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      (0 < L.mass omega → law.SupportedOn
        (IsSampledLinkJointOutcome F (A omega) (I omega ∪ D omega) (links omega))) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun result ↦ Q ⊆ result.1) ≤ sigma^Q.card) ∧
      (0 < L.mass omega → Good omega →
        law.probability (fun result ↦ ¬ ∀ o, CoversBipartiteLink (links omega o) result.2) ≤ conditionalError+
          law.probability (fun result ↦ ¬ IsSampledLinkForbiddenGood (links omega) F (I omega) (D omega) result.1 forbiddenCap)) := by
    intro omega
    by_cases hreadyOmega : 0 < L.mass omega ∧ Good omega
    · obtain ⟨law, hstruct, hpoint, hfail⟩ := hready omega hreadyOmega.1 hreadyOmega.2
      exact ⟨law, fun _ ↦ hstruct, hpoint, fun _ _ ↦ hfail⟩
    · refine ⟨FiniteLaw.pure (∅,∅), ?_, pure_empty_linkJoint_inclusion sigma, ?_⟩
      · intro hmass
        exact FiniteLaw.supportedOn_pure _ (isSampledLinkJointOutcome_empty F (A omega) (I omega ∪ D omega)
          (links omega) (hbase omega hmass).1 (hbase omega hmass).2)
      · intro hmass hgood
        exact (hreadyOmega ⟨hmass, hgood⟩).elim
  choose kernel hstruct hpoint hfail using hchoice
  refine ⟨kernel, hstruct, hpoint, ?_⟩
  intro priorError obstructionError hprior hobstruction
  exact L.jointBind_failure_le_of_conditional_add kernel Good
    (fun omega result ↦ ¬ ∀ o, CoversBipartiteLink (links omega o) result.2)
    (fun omega result ↦ ¬ IsSampledLinkForbiddenGood (links omega) F (I omega) (D omega) result.1 forbiddenCap)
    priorError conditionalError obstructionError hprior hfail hobstruction

end

end Erdos207
