/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomCoverStage
import ErdosProblems.Erdos207.RelativeRootedThreatMoment
import ErdosProblems.Erdos207.VertexStarWeight

/-!
# Moments for the random internal-edge stage

The B4 estimate applies to triangles selected after the initial packing.
This file converts it to a joint-inclusion estimate for `chosen \ P0` and
then applies the finite weight-system lemma to every new vertex star.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- B4 as a joint-inclusion estimate for the genuinely new part of the
terminal family.  Unlike the raw B4 statement, this version needs no
disjointness premise: if `Q` meets `P0`, the event is impossible. -/
theorem internalEdgeGreedyProcess_probability_subset_newChosen_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 Q : TripleSystemOn V) (s : Nat)
    (hQcard : Q.card <= s) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => Q ⊆ z.chosen \ P0) <=
      (s.factorial : NNReal) *
        setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  by_cases hdisjoint : Disjoint Q P0
  · calc
      L.probability (fun z => Q ⊆ z.chosen \ P0) <=
          L.probability (fun z => Q ⊆ z.chosen) := by
        apply L.probability_mono
        intro z hz T hT
        exact (mem_sdiff.mp (hz hT)).1
      _ <= (Q.card.factorial : NNReal) *
          ((D : NNReal)⁻¹ ^ Q.card) :=
        internalEdgeGreedyProcess_probability_subset_chosen_le
          F G U omega S edges hne hnodup hu hv hSU D hD P0 Q hdisjoint
      _ <= (s.factorial : NNReal) * ((D : NNReal)⁻¹ ^ Q.card) := by
        gcongr
      _ = (s.factorial : NNReal) *
          setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := by
        simp [setWeight]
  · have himpossible : ∀ z : InternalEdgeGreedyStateOn V,
        ¬ Q ⊆ z.chosen \ P0 := by
      intro z hsub
      apply hdisjoint
      rw [Finset.disjoint_left]
      intro T hTQ hTP0
      exact (mem_sdiff.mp (hsub hTQ)).2 hTP0
    calc
      L.probability (fun z => Q ⊆ z.chosen \ P0) <=
          L.probability (fun _ => False) := by
        apply L.probability_mono
        intro z hz
        exact himpossible z hz
      _ = 0 := L.probability_false
      _ <= (s.factorial : NNReal) *
          setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := bot_le

/-- Exact extension budget for one vertex star under reciprocal threshold
weight. -/
def internalEdgeVertexStarBudget
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : Nat) (v : V) : NNReal :=
  (∑ T : universeTriplesThrough v, (D : NNReal)⁻¹) + 1

/-- Moment bound for the new triangles through one vertex in the terminal
internal-edge law. -/
theorem internalEdgeGreedyProcess_newVertexStar_momentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (s : Nat) (v : V) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).expectation
        (fun z => ((triplesThrough (z.chosen \ P0) v).card : NNReal) ^ s) <=
      (s.factorial : NNReal) *
        (((2 : NNReal) ^ s * internalEdgeVertexStarBudget D v) ^ s) := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  have hmoment := configurationMomentBound L
    (fun T : universeTriplesThrough v => ({T.1} : TripleSystemOn V))
    (fun z : InternalEdgeGreedyStateOn V => z.chosen \ P0)
    (fun _ : TripleOn V => (D : NNReal)⁻¹)
    (s.factorial : NNReal) (internalEdgeVertexStarBudget D v)
    (d := 1) (s := s)
    (by intro T; simp)
    (singletonVertexStar_hasExtensionBound_pointWeight v
      (fun _ : TripleOn V => (D : NNReal)⁻¹))
    (by
      intro Q hQcard
      have hQcard' : Q.card <= s := by omega
      exact internalEdgeGreedyProcess_probability_subset_newChosen_le
        F G U omega S edges hne hnodup hu hv hSU D hD P0 Q s hQcard')
  simpa only [L, selectedCount_singletonVertexStar,
    internalEdgeVertexStarBudget, Nat.mul_one] using hmoment

/-- Markov upper tail for a new vertex star. -/
theorem internalEdgeGreedyProcess_probability_newVertexStar_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (s : Nat) (v : V) (a : NNReal) (ha : 0 < a) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => a <= (triplesThrough (z.chosen \ P0) v).card) <=
      ((s.factorial : NNReal) *
        (((2 : NNReal) ^ s * internalEdgeVertexStarBudget D v) ^ s)) /
          a ^ s := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  have hmono : L.probability
      (fun z => a <= (triplesThrough (z.chosen \ P0) v).card) <=
      L.probability (fun z =>
        a ^ s <= ((triplesThrough (z.chosen \ P0) v).card : NNReal) ^ s) := by
    apply L.probability_mono
    intro z hz
    exact pow_le_pow_left' hz s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div
    (fun z => ((triplesThrough (z.chosen \ P0) v).card : NNReal) ^ s)
    (pow_pos ha s)
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right (pow_pos ha s)).2
  exact internalEdgeGreedyProcess_newVertexStar_momentBound
    F G U omega S edges hne hnodup hu hv hSU D hD P0 s v

/-- B4 controls rooted configurations whose remainders may use both the
initial packing and triangles inserted by the internal-edge stage.  The only
combinatorial input is the relative-remainder extension budget. -/
theorem internalEdgeGreedyProcess_rootedActive_momentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (u v : V) (k s : Nat)
    (hfamily : ∀ C ∈ F, C.card <= k) (kappa : NNReal)
    (hkappa : HasExtensionBound
      (fun z : RootedThreatWitness V F u v =>
        relativeRootedThreatRemainder P0 z)
      (fun _ : TripleOn V => (D : NNReal)⁻¹) kappa) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).expectation
        (fun z => ((rootedActiveForbiddenConfigurations
          F z.chosen u v).card : NNReal) ^ s) <=
      ((s * (k - 1)).factorial : NNReal) *
        (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s) := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  calc
    L.expectation (fun z => ((rootedActiveForbiddenConfigurations
        F z.chosen u v).card : NNReal) ^ s) <=
        L.expectation (fun z => ((rootedActiveForbiddenConfigurations
          F (P0 ∪ (z.chosen \ P0)) u v).card : NNReal) ^ s) := by
      apply L.expectation_mono
      intro z
      apply pow_le_pow_left'
      exact_mod_cast rootedActiveForbiddenConfigurations_card_mono
        (P := z.chosen) (P' := P0 ∪ (z.chosen \ P0)) (by
          intro T hT
          by_cases hTP0 : T ∈ P0
          · exact mem_union_left _ hTP0
          · exact mem_union_right _ (mem_sdiff.mpr ⟨hT, hTP0⟩))
    _ <= ((s * (k - 1)).factorial : NNReal) *
        (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s) := by
      apply relativeRootedActiveMomentBound L
        (fun z => z.chosen \ P0) F P0 u v
        (fun _ : TripleOn V => (D : NNReal)⁻¹)
        ((s * (k - 1)).factorial : NNReal) kappa hfamily hkappa
      intro Q hQcard
      exact internalEdgeGreedyProcess_probability_subset_newChosen_le
        F G U omega S edges hne hnodup hu hv hSU D hD P0 Q
          (s * (k - 1)) hQcard

/-- Markov upper tail for the actual rooted-active count after the random
internal-edge stage. -/
theorem internalEdgeGreedyProcess_probability_rootedActive_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (u v : V) (k s : Nat)
    (hfamily : ∀ C ∈ F, C.card <= k) (kappa a : NNReal)
    (ha : 0 < a)
    (hkappa : HasExtensionBound
      (fun z : RootedThreatWitness V F u v =>
        relativeRootedThreatRemainder P0 z)
      (fun _ : TripleOn V => (D : NNReal)⁻¹) kappa) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => a <= (rootedActiveForbiddenConfigurations
          F z.chosen u v).card) <=
      (((s * (k - 1)).factorial : NNReal) *
        (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s)) / a ^ s := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  have hmono : L.probability (fun z =>
      a <= (rootedActiveForbiddenConfigurations F z.chosen u v).card) <=
      L.probability (fun z =>
        a ^ s <= ((rootedActiveForbiddenConfigurations
          F z.chosen u v).card : NNReal) ^ s) := by
    apply L.probability_mono
    intro z hz
    exact pow_le_pow_left' hz s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div
    (fun z => ((rootedActiveForbiddenConfigurations
      F z.chosen u v).card : NNReal) ^ s) (pow_pos ha s)
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right (pow_pos ha s)).2
  exact internalEdgeGreedyProcess_rootedActive_momentBound
    F G U omega S edges hne hnodup hu hv hSU D hD P0
      u v k s hfamily kappa hkappa

/-- Fully finite specialization using only the cardinality of the forbidden
family.  Sharper KSSS applications replace this crude extension budget by the
well-spread bound, but no abstract extension premise remains here. -/
theorem internalEdgeGreedyProcess_probability_rootedActive_ge_le_crude
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (u v : V) (k s : Nat) (hfamily : ∀ C ∈ F, C.card <= k)
    (a : NNReal) (ha : 0 < a) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => a <= (rootedActiveForbiddenConfigurations
          F z.chosen u v).card) <=
      (((s * (k - 1)).factorial : NNReal) *
        (((2 : NNReal) ^ (s * (k - 1)) * (F.card * k : NNReal)) ^ s)) /
          a ^ s := by
  apply internalEdgeGreedyProcess_probability_rootedActive_ge_le
    F G U omega S edges hne hnodup hu hv hSU D hD P0
      u v k s hfamily (F.card * k : NNReal) a ha
  apply relativeRootedThreatRemainder_hasExtensionBound_crude
    F P0 u v (fun _ : TripleOn V => (D : NNReal)⁻¹) k hfamily
  intro T
  apply (inv_le_one₀ (by exact_mod_cast hD)).2
  exact_mod_cast hD

end

end Erdos207
