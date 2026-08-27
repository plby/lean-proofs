/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexRootedThreatFourWeight
import ErdosProblems.Erdos207.VortexRootedThreatMoment
import ErdosProblems.Erdos207.VortexVertexStarMoment
import ErdosProblems.Erdos207.RootedThreatWellSpread

/-!
# Full terminal moments for one cyclic vortex law

This file recombines indexed rooted threats with the order-four complement,
then takes a single union bound over all vertex stars and all ordered pairs.
Thus the selected outcome has exactly the three deterministic controls used
by the terminal cover-down failure split.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Ambient-size-free coefficient inside the full rooted extension budget. -/
def fullRootedThreatVortexCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q : ℕ) (B : TripleSystemOn V)
    (c : ℝ≥0) : ℝ≥0 :=
  indexedRootedThreatVortexUniformCoefficient W q B +
    (1 + 3 * ((ell + 1 : ℕ) * c))

/-- Indexed and order-four rooted witnesses together have the required
uniform vortex extension bound. -/
theorem rootedThreatRemainder_hasExtensionBound_vortex
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : RootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v ↦
        rootedThreatRemainder z)
      (vortexTripleWeight W c)
      ((Fintype.card V : ℝ≥0) *
      fullRootedThreatVortexCoefficient W q B c) := by
  intro A
  rw [extensionWeight_rootedThreat_eq_indexed_add_four]
  calc
    extensionWeight
        (fun z : IndexedRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (vortexTripleWeight W c) A +
      extensionWeight
        (fun z : FourRootedThreatWitness V q B u v ↦
          rootedThreatRemainder z.1)
        (vortexTripleWeight W c) A ≤
      (Fintype.card V : ℝ≥0) *
          indexedRootedThreatVortexUniformCoefficient W q B +
        (Fintype.card V : ℝ≥0) *
          (1 + 3 * ((ell + 1 : ℕ) * c)) :=
      add_le_add
        (indexedRootedThreatRemainder_hasExtensionBound_vortex
          W B c hc houter hterminal huv A)
        (fourRootedThreatRemainder_hasExtensionBound_vortex
          W B c huv A)
    _ = (Fintype.card V : ℝ≥0) *
        fullRootedThreatVortexCoefficient W q B c := by
      unfold fullRootedThreatVortexCoefficient
      ring

/-- Sharpened form of the full rooted bound.  The apparent order-four
summand in the older estimate is zero because no order-four packing can be
an Erdős configuration. -/
theorem rootedThreatRemainder_hasExtensionBound_vortex_noFour
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : RootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v ↦
        rootedThreatRemainder z)
      (vortexTripleWeight W c)
      ((Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexUniformCoefficient W q B) := by
  intro A
  rw [extensionWeight_rootedThreat_eq_indexed_add_four]
  have hindexed := indexedRootedThreatRemainder_hasExtensionBound_vortex
    (q := q) W B c hc houter hterminal huv A
  have hfour := fourRootedThreatRemainder_hasExtensionBound_zero
    (q := q) B (vortexTripleWeight W c) (u := u) (v := v) A
  simpa only [add_zero] using add_le_add hindexed hfour

/-- The no-order-four rooted extension bound for vortex multipliers at least
one. -/
theorem rootedThreatRemainder_hasExtensionBound_vortex_noFour_of_one_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hc : 1 ≤ c)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : RootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v ↦
        rootedThreatRemainder z)
      (vortexTripleWeight W c)
      ((Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexLargeCoefficient W q B c 0) := by
  intro A
  rw [extensionWeight_rootedThreat_eq_indexed_add_four]
  have hindexed :=
    indexedRootedThreatRemainder_hasExtensionBound_vortex_of_one_le
      (q := q) W B c hc houter hterminal huv A
  have hfour := fourRootedThreatRemainder_hasExtensionBound_zero
    (q := q) B (vortexTripleWeight W c) (u := u) (v := v) A
  simpa only [add_zero] using add_le_add hindexed hfour

/-- Factorial joint-inclusion constant at the largest union of `s` rooted
remainders. -/
def fullRootedMomentJointConstant (q s : ℕ) : ℕ :=
  (s * (q - 1)).factorial

/-- Moment bound for the actual rooted active forbidden-configuration count,
including both indexed and order-four configurations. -/
theorem cyclicVortexGreedy_fullRootedActiveMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q s : ℕ} (W : Vortex V ell) (B A : TripleSystemOn V)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hratio : ∀ k : Fin (ell + 1),
      (vortexPackingSaturationFuel V : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤
        c / (W.U k).card)
    {u v : V} (huv : u ≠ v) :
    (scheduledStoppedVortexGreedyProcessLaw
      (absorberErdosForbiddenConfigurationsOn q B) W
      (vortexCyclicSchedule ell) D
      (vortexPackingSaturationFuel V * (ell + 1))
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).expectation
        (fun S ↦ ((rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S.chosen u v).card : ℝ≥0) ^ s) ≤
      (fullRootedMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ (s * (q - 1)) *
          ((Fintype.card V : ℝ≥0) *
            fullRootedThreatVortexCoefficient W q B c)) ^ s) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let cycles := vortexPackingSaturationFuel V
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D (cycles * (ell + 1)) S₀
  apply rootedActiveMomentBound L (fun S ↦ S.chosen) F u v
    (vortexTripleWeight W c)
    (fullRootedMomentJointConstant q s : ℝ≥0)
    ((Fintype.card V : ℝ≥0) *
      fullRootedThreatVortexCoefficient W q B c)
  · intro C hCF
    exact card_le_cutoff_of_mem_absorberErdosForbidden hCF
  · exact rootedThreatRemainder_hasExtensionBound_vortex
      W B c hc houter hterminal huv
  · intro T hTcard
    have hjoint :=
      cyclicVortexGreedy_probability_subset_chosen_le_vortexWeight
        F W D hD cycles c hratio S₀ T (by
          simp [S₀, absorberGreedyInitialState])
    apply hjoint.trans
    gcongr
    exact_mod_cast Nat.factorial_le hTcard

/-- Markov upper tail for the full rooted active count at one ordered pair. -/
theorem cyclicVortexGreedy_probability_fullRootedActive_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q s : ℕ} (W : Vortex V ell) (B A : TripleSystemOn V)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (c a : ℝ≥0) (hc : c ≤ 1) (ha : 0 < a)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hratio : ∀ k : Fin (ell + 1),
      (vortexPackingSaturationFuel V : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤
        c / (W.U k).card)
    (e : DistinctPair V) :
    (scheduledStoppedVortexGreedyProcessLaw
      (absorberErdosForbiddenConfigurationsOn q B) W
      (vortexCyclicSchedule ell) D
      (vortexPackingSaturationFuel V * (ell + 1))
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)).probability
        (fun S ↦ a ≤ (rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S.chosen e.1.1 e.1.2).card) ≤
      ((fullRootedMomentJointConstant q s : ℝ≥0) *
        (((2 : ℝ≥0) ^ (s * (q - 1)) *
          ((Fintype.card V : ℝ≥0) *
            fullRootedThreatVortexCoefficient W q B c)) ^ s)) / a ^ s := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D
    (vortexPackingSaturationFuel V * (ell + 1)) S₀
  let X : GreedyStateOn V → ℝ≥0 := fun S ↦
    ((rootedActiveForbiddenConfigurations F
      S.chosen e.1.1 e.1.2).card : ℝ≥0) ^ s
  have hmono : L.probability (fun S ↦ a ≤
      (rootedActiveForbiddenConfigurations F
        S.chosen e.1.1 e.1.2).card) ≤
      L.probability (fun S ↦ a ^ s ≤ X S) := by
    apply L.probability_mono
    intro S hS
    exact pow_le_pow_left' hS s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div X (pow_pos ha s)
  refine hmarkov.trans ?_
  apply (div_le_div_iff_of_pos_right (pow_pos ha s)).2
  exact cyclicVortexGreedy_fullRootedActiveMomentBound
    W B A D hD c hc houter hterminal hratio e.2

/-- One outcome of the common cyclic law simultaneously has the structural
saturation certificate, every vertex-star cutoff, and every full rooted
active cutoff. -/
theorem exists_cyclicVortexGreedy_terminalControls
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q s : ℕ} (W : Vortex V ell) (B A : TripleSystemOn V)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (c aStar aRoot : ℝ≥0) (hc : c ≤ 1)
    (haStar : 0 < aStar) (haRoot : 0 < aRoot)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hratio : ∀ k : Fin (ell + 1),
      (vortexPackingSaturationFuel V : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤
        c / (W.U k).card)
    (hsmall :
      (∑ v : V,
        ((s.factorial : ℝ≥0) *
          (((2 : ℝ≥0) ^ s *
            vortexVertexStarExtensionBudget W c v) ^ s)) / aStar ^ s) +
      (Fintype.card (DistinctPair V) : ℝ≥0) *
        (((fullRootedMomentJointConstant q s : ℝ≥0) *
          (((2 : ℝ≥0) ^ (s * (q - 1)) *
            ((Fintype.card V : ℝ≥0) *
              fullRootedThreatVortexCoefficient W q B c)) ^ s)) /
            aRoot ^ s) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
        (absorberErdosForbiddenConfigurationsOn q B) A S ∧
      S.available.card ≤ ∑ k, D k ∧
      S.available ⊆
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A).available ∧
      (∀ v : V,
        ((triplesThrough S.chosen v).card : ℝ≥0) < aStar) ∧
      (∀ e : DistinctPair V,
        ((rootedActiveForbiddenConfigurations
          (absorberErdosForbiddenConfigurationsOn q B)
          S.chosen e.1.1 e.1.2).card : ℝ≥0) < aRoot) := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D
    (vortexPackingSaturationFuel V * (ell + 1)) S₀
  let Good : GreedyStateOn V → Prop := fun S ↦
    AbsorberGreedyInvariant F A S ∧
      S.available.card ≤ ∑ k, D k ∧ S.available ⊆ S₀.available
  have hS₀ : AbsorberGreedyInvariant F A S₀ := by
    exact absorberGreedyInitialState_invariant F A fun C hC ↦
      absorberErdosForbidden_nonempty hC
  have hsupport : L.SupportedOn Good := by
    exact cyclicVortexGreedy_supported_globalBound hD hS₀
  let starEps : V → ℝ≥0 := fun v ↦
    ((s.factorial : ℝ≥0) *
      (((2 : ℝ≥0) ^ s * vortexVertexStarExtensionBudget W c v) ^ s)) /
        aStar ^ s
  let rootEps : ℝ≥0 :=
    ((fullRootedMomentJointConstant q s : ℝ≥0) *
      (((2 : ℝ≥0) ^ (s * (q - 1)) *
        ((Fintype.card V : ℝ≥0) *
          fullRootedThreatVortexCoefficient W q B c)) ^ s)) / aRoot ^ s
  let bad : Option (Sum V (DistinctPair V)) → GreedyStateOn V → Prop
    | none, S => ¬ Good S
    | some (Sum.inl v), S => aStar ≤ (triplesThrough S.chosen v).card
    | some (Sum.inr e), S => aRoot ≤
        (rootedActiveForbiddenConfigurations F
          S.chosen e.1.1 e.1.2).card
  have hstruct : L.probability (bad none) = 0 := by
    change L.probability (fun S ↦ ¬ Good S) = 0
    rw [L.probability_not, L.probability_eq_one_of_supported Good hsupport]
    simp
  have hstar : ∀ v : V,
      L.probability (bad (some (Sum.inl v))) ≤ starEps v := by
    intro v
    exact cyclicVortexGreedy_probability_vertexStar_ge_le
      W B A D hD c aStar haStar hratio v
  have hroot : ∀ e : DistinctPair V,
      L.probability (bad (some (Sum.inr e))) ≤ rootEps := by
    intro e
    exact cyclicVortexGreedy_probability_fullRootedActive_ge_le
      W B A D hD c aRoot hc haRoot houter hterminal hratio e
  have hsum : ∑ i : Option (Sum V (DistinctPair V)),
      L.probability (bad i) < 1 := by
    rw [Fintype.sum_option, hstruct, zero_add, Fintype.sum_sum_type]
    calc
      (∑ v : V, L.probability (bad (some (Sum.inl v)))) +
          ∑ e : DistinctPair V,
            L.probability (bad (some (Sum.inr e))) ≤
        (∑ v : V, starEps v) +
          ∑ _e : DistinctPair V, rootEps := by
        apply add_le_add
        · exact sum_le_sum fun v hv ↦ hstar v
        · exact sum_le_sum fun e he ↦ hroot e
      _ = (∑ v : V, starEps v) +
          (Fintype.card (DistinctPair V) : ℝ≥0) * rootEps := by simp
      _ < 1 := by simpa only [starEps, rootEps] using hsmall
  obtain ⟨S, hS⟩ := L.exists_avoiding_of_sum_probability_lt_one
    (univ : Finset (Option (Sum V (DistinctPair V)))) bad
      (by simpa using hsum)
  have hGood : Good S := not_not.mp (hS none (mem_univ none))
  refine ⟨S, hGood.1, hGood.2.1, hGood.2.2, ?_, ?_⟩
  · intro v
    exact lt_of_not_ge (hS (some (Sum.inl v)) (mem_univ _))
  · intro e
    exact lt_of_not_ge (hS (some (Sum.inr e)) (mem_univ _))

end

end Erdos207
