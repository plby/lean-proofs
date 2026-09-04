/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedKernelJointInclusion
import ErdosProblems.Erdos207.VortexWeight
import ErdosProblems.Erdos207.GreedyOneStepProbability
import ErdosProblems.Erdos207.GreedyDeletionStatistics
import ErdosProblems.Erdos207.AvailablePairDegreeTrajectory

/-!
# A constrained greedy kernel restricted to one vortex level

At one cover-down stage only triangles whose deepest vortex level is `k`
are sampled.  This restriction is what turns a reciprocal availability bound
into the level-dependent weight `c / |U_k|`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def vortexLevelAvailable
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (S : GreedyStateOn V) :
    TripleSystemOn V :=
  S.available.filter fun T ↦ W.level T = k

@[simp]
lemma mem_vortexLevelAvailable_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {S : GreedyStateOn V}
    {T : TripleOn V} :
    T ∈ vortexLevelAvailable W k S ↔ T ∈ S.available ∧ W.level T = k := by
  simp [vortexLevelAvailable]

/-- Uniformly choose a currently legal triangle at level `k`, or stay put
when that level has no legal triangle. -/
def vortexLevelGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) := by
  classical
  exact if h : (vortexLevelAvailable W k S).Nonempty then
    letI : Nonempty (vortexLevelAvailable W k S) :=
      ⟨⟨h.choose, h.choose_spec⟩⟩
    FiniteLaw.map
      (fun T : vortexLevelAvailable W k S ↦ greedyStep F S T.1)
      (FiniteLaw.uniform : FiniteLaw (vortexLevelAvailable W k S))
  else FiniteLaw.pure S

/-- Stop the level-restricted kernel below a prescribed level-availability
threshold. -/
def stoppedVortexLevelGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) :=
  if D ≤ (vortexLevelAvailable W k S).card then
    vortexLevelGreedyKernel F W k S
  else FiniteLaw.pure S

/-- Law of a fixed-level threshold-stopped phase. -/
def stoppedVortexLevelGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D fuel : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.iterateKernel (stoppedVortexLevelGreedyKernel F W k D)
    fuel (FiniteLaw.pure S)

/-- A uniform horizon long enough that the exact-progress alternative cannot
persist on the finite triangle ground set. -/
def vortexLevelSaturationFuel (V : Type*) [Fintype V] [DecidableEq V] : ℕ :=
  Fintype.card (TripleOn V) + 1

/-- A quadratic saturation horizon obtained from the packing edge budget. -/
def vortexPackingSaturationFuel (V : Type*) [Fintype V] : ℕ :=
  Fintype.card V * (Fintype.card V - 1) + 1

/-- With a nonempty level-available set, the unrestricted level kernel is
supported on genuine greedy steps using a triangle at that level. -/
theorem vortexLevelGreedyKernel_supported_step_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (S : GreedyStateOn V) (hA : (vortexLevelAvailable W k S).Nonempty) :
    (vortexLevelGreedyKernel F W k S).SupportedOn
      (fun S' ↦ ∃ T ∈ vortexLevelAvailable W k S,
        S' = greedyStep F S T) := by
  classical
  unfold vortexLevelGreedyKernel
  simp only [hA, dite_true]
  let : Nonempty (vortexLevelAvailable W k S) :=
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  exact (FiniteLaw.uniform_supported
    (fun _ : vortexLevelAvailable W k S ↦ True) (fun _ ↦ trivial)).map
      (fun T ↦ greedyStep F S T.1) fun T _ ↦ ⟨T.1, T.2, rfl⟩

theorem vortexLevelGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1)) :
    IsMonotoneSingleInsertionKernel (vortexLevelGreedyKernel F W k)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold vortexLevelGreedyKernel
  split_ifs with hnonempty
  · let : Nonempty (vortexLevelAvailable W k S) :=
      ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    let next : vortexLevelAvailable W k S → GreedyStateOn V :=
      fun T ↦ greedyStep F S T.1
    have hu : FiniteLaw.SupportedOn
        (fun _ : vortexLevelAvailable W k S ↦ True)
        (FiniteLaw.uniform : FiniteLaw (vortexLevelAvailable W k S)) :=
      FiniteLaw.uniform_supported _ fun _ ↦ trivial
    refine hu.map next ?_
    intro T _hT
    constructor
    · exact subset_insert T.1 S.chosen
    · by_cases hmem : T.1 ∈ S.chosen
      · simp [next, greedyStep, hmem]
      · simp [next, greedyStep, hmem]
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

theorem stoppedVortexLevelGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D : ℕ) :
    IsMonotoneSingleInsertionKernel
      (stoppedVortexLevelGreedyKernel F W k D)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold stoppedVortexLevelGreedyKernel
  split_ifs with hactive
  · exact vortexLevelGreedyKernel_monotone_singleInsertion F W k S
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

theorem vortexLevelGreedyKernel_probability_new_triangle
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (S : GreedyStateOn V) (T : TripleOn V) (hTnot : T ∉ S.chosen) :
    (vortexLevelGreedyKernel F W k S).probability
        (fun S' ↦ T ∈ S'.chosen) =
      if T ∈ vortexLevelAvailable W k S then
        ((vortexLevelAvailable W k S).card : ℝ≥0)⁻¹ else 0 := by
  classical
  by_cases hnonempty : (vortexLevelAvailable W k S).Nonempty
  · let : Nonempty (vortexLevelAvailable W k S) :=
      ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    let next : vortexLevelAvailable W k S → GreedyStateOn V :=
      fun U ↦ greedyStep F S U.1
    simp only [vortexLevelGreedyKernel, hnonempty, dite_true]
    change (FiniteLaw.map next
      (FiniteLaw.uniform : FiniteLaw (vortexLevelAvailable W k S))).probability
        (fun S' ↦ T ∈ S'.chosen) = _
    rw [FiniteLaw.probability_map]
    by_cases hT : T ∈ vortexLevelAvailable W k S
    · simp only [if_pos hT]
      let T0 : vortexLevelAvailable W k S := ⟨T, hT⟩
      have hunique : ∀ U : vortexLevelAvailable W k S,
          T ∈ (next U).chosen ↔ U = T0 := by
        intro U
        simp only [next, greedyStep, mem_insert]
        constructor
        · intro h
          rcases h with hTU | hTC
          · apply Subtype.ext
            exact hTU.symm
          · exact (hTnot hTC).elim
        · intro h
          subst U
          exact Or.inl rfl
      simpa only [Fintype.card_coe] using
        (@FiniteLaw.uniform_probability_unique
          (vortexLevelAvailable W k S) _ inferInstance
          (fun U ↦ T ∈ (next U).chosen) T0 hunique)
    · simp only [if_neg hT]
      have hfalse :
          (fun U : vortexLevelAvailable W k S ↦ T ∈ (next U).chosen) =
            (fun _ ↦ False) := by
        funext U
        apply propext
        constructor
        · intro h
          simp only [next, greedyStep, mem_insert] at h
          rcases h with hTU | hTC
          · exact hT (hTU ▸ U.2)
          · exact hTnot hTC
        · exact False.elim
      rw [hfalse, FiniteLaw.probability_false]
  · have hempty : vortexLevelAvailable W k S = ∅ :=
      not_nonempty_iff_eq_empty.mp hnonempty
    have hT : T ∉ vortexLevelAvailable W k S := by simp [hempty]
    simp [vortexLevelGreedyKernel, hnonempty, hT, hTnot]

/-- The point hazard is zero off level `k` and at most `D⁻¹` on level `k`. -/
theorem stoppedVortexLevelGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D : ℕ) (hD : 0 < D) (S : GreedyStateOn V) (T : TripleOn V)
    (hTnot : T ∉ S.chosen) :
    (stoppedVortexLevelGreedyKernel F W k D S).probability
        (fun S' ↦ T ∈ S'.chosen) ≤
      if W.level T = k then (D : ℝ≥0)⁻¹ else 0 := by
  classical
  unfold stoppedVortexLevelGreedyKernel
  split_ifs with hactive hlevel
  · rw [vortexLevelGreedyKernel_probability_new_triangle F W k S T hTnot]
    split_ifs with hTavailable
    · simpa only [one_div] using
        (one_div_le_one_div_of_le (by exact_mod_cast hD)
          (by exact_mod_cast hactive :
            (D : ℝ≥0) ≤ (vortexLevelAvailable W k S).card))
    · exact bot_le
  · rw [vortexLevelGreedyKernel_probability_new_triangle F W k S T hTnot]
    rw [if_neg]
    intro hmem
    exact hlevel (mem_vortexLevelAvailable_iff.mp hmem).2
  · rw [FiniteLaw.probability_pure]
    simp [hTnot]
  · rw [FiniteLaw.probability_pure]
    simp [hTnot]

theorem stoppedVortexLevelGreedyKernel_supported_absorberInvariant
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {k : Fin (ell + 1)} {D : ℕ} {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant F A S) :
    (stoppedVortexLevelGreedyKernel F W k D S).SupportedOn
      (AbsorberGreedyInvariant F A) := by
  classical
  unfold stoppedVortexLevelGreedyKernel
  split_ifs with hactive
  · unfold vortexLevelGreedyKernel
    split_ifs with hnonempty
    · let : Nonempty (vortexLevelAvailable W k S) :=
        ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
      exact (FiniteLaw.uniform_supported
        (fun _ : vortexLevelAvailable W k S ↦ True) (fun _ ↦ trivial)).map
          (fun T ↦ greedyStep F S T.1) fun T _ ↦
            hS.step (mem_vortexLevelAvailable_iff.mp T.2).1
    · exact FiniteLaw.supportedOn_pure _ hS
  · exact FiniteLaw.supportedOn_pure _ hS

/-- A stopped level transition can only delete globally available
triangles. -/
theorem stoppedVortexLevelGreedyKernel_supported_available_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D : ℕ) (S : GreedyStateOn V) :
    (stoppedVortexLevelGreedyKernel F W k D S).SupportedOn
      (fun S' ↦ S'.available ⊆ S.available) := by
  classical
  unfold stoppedVortexLevelGreedyKernel
  split_ifs with hactive
  · unfold vortexLevelGreedyKernel
    split_ifs with hnonempty
    · let : Nonempty (vortexLevelAvailable W k S) :=
        ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
      exact (FiniteLaw.uniform_supported
        (fun _ : vortexLevelAvailable W k S ↦ True) (fun _ ↦ trivial)).map
          (fun T ↦ greedyStep F S T.1) fun T _ ↦
            greedyStep_available_subset F S T.1
    · exact FiniteLaw.supportedOn_pure _ Subset.rfl
  · exact FiniteLaw.supportedOn_pure _ Subset.rfl

/-- Availability remains a subset of its value at the start of an entire
fixed-level phase. -/
theorem stoppedVortexLevelGreedyProcessLaw_supported_available_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D : ℕ) (S₀ : GreedyStateOn V) :
    ∀ fuel,
      (stoppedVortexLevelGreedyProcessLaw F W k D fuel S₀).SupportedOn
        (fun S ↦ S.available ⊆ S₀.available) := by
  intro fuel
  induction fuel with
  | zero => exact FiniteLaw.supportedOn_pure _ Subset.rfl
  | succ fuel ih =>
      rw [stoppedVortexLevelGreedyProcessLaw,
        FiniteLaw.iterateKernel_succ_right]
      have ih' := ih
      unfold stoppedVortexLevelGreedyProcessLaw at ih'
      exact ih'.bind _ fun S hS S' hmass ↦
        (stoppedVortexLevelGreedyKernel_supported_available_subset
          F W k D S S' hmass).trans hS

/-- A supported fixed-level phase either reaches the level threshold or
performs exactly one legal insertion at every scheduled step.  In both cases
the full absorber invariant is retained. -/
theorem stoppedVortexLevelGreedyProcessLaw_supported_progress
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {k : Fin (ell + 1)} {D : ℕ} {S₀ : GreedyStateOn V}
    (hS₀ : AbsorberGreedyInvariant F A S₀) (hD : 0 < D) :
    ∀ fuel,
      (stoppedVortexLevelGreedyProcessLaw F W k D fuel S₀).SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          ((vortexLevelAvailable W k S).card < D ∨
            S.chosen.card = S₀.chosen.card + fuel)) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _
        ⟨hS₀, Or.inr (by omega)⟩
  | succ fuel ih =>
      rw [stoppedVortexLevelGreedyProcessLaw,
        FiniteLaw.iterateKernel_succ_right]
      have ih' := ih
      unfold stoppedVortexLevelGreedyProcessLaw at ih'
      refine ih'.bind (stoppedVortexLevelGreedyKernel F W k D) ?_
      intro S hS
      unfold stoppedVortexLevelGreedyKernel
      split_ifs with hactive
      · have hnonempty : (vortexLevelAvailable W k S).Nonempty := by
          rw [← card_pos]
          exact hD.trans_le hactive
        have hsteps := vortexLevelGreedyKernel_supported_step_of_nonempty
          F W k S hnonempty
        intro S' hmass
        obtain ⟨T, hT, rfl⟩ := hsteps S' hmass
        have hTavailable : T ∈ S.available :=
          (mem_vortexLevelAvailable_iff.mp hT).1
        have hTnot : T ∉ S.chosen := (hS.1.1.2.2 T hTavailable).1
        have hcardS : S.chosen.card = S₀.chosen.card + fuel := by
          rcases hS.2 with hsmall | hcard
          · omega
          · exact hcard
        refine ⟨hS.1.step hTavailable, Or.inr ?_⟩
        simp only [greedyStep]
        rw [card_insert_of_notMem hTnot, hcardS]
        omega
      · exact FiniteLaw.supportedOn_pure _
          ⟨hS.1, Or.inl (by omega)⟩

/-- Running for the finite saturation horizon forces the selected level
below its stopping threshold on every positive-mass outcome. -/
theorem stoppedVortexLevelGreedyProcessLaw_supported_belowThreshold
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {k : Fin (ell + 1)} {D : ℕ} {S₀ : GreedyStateOn V}
    (hS₀ : AbsorberGreedyInvariant F A S₀) (hD : 0 < D) :
    (stoppedVortexLevelGreedyProcessLaw F W k D
      (vortexLevelSaturationFuel V) S₀).SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          (vortexLevelAvailable W k S).card < D) := by
  have hprogress := stoppedVortexLevelGreedyProcessLaw_supported_progress
    (W := W) (k := k) hS₀ hD (vortexLevelSaturationFuel V)
  intro S hmass
  have hS := hprogress S hmass
  refine ⟨hS.1, ?_⟩
  rcases hS.2 with hsmall | hcard
  · exact hsmall
  · have hbound : S.chosen.card ≤ Fintype.card (TripleOn V) := by
      have hsub := card_le_card (subset_univ S.chosen)
      simpa only [card_univ] using hsub
    unfold vortexLevelSaturationFuel at hcard
    omega

/-- The packing invariant reduces the saturation horizon from the number of
all triples to a quadratic number of steps. -/
theorem stoppedVortexLevelGreedyProcessLaw_supported_belowThreshold_packing
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {k : Fin (ell + 1)} {D : ℕ} {S₀ : GreedyStateOn V}
    (hS₀ : AbsorberGreedyInvariant F A S₀) (hD : 0 < D) :
    (stoppedVortexLevelGreedyProcessLaw F W k D
      (vortexPackingSaturationFuel V) S₀).SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          (vortexLevelAvailable W k S).card < D) := by
  have hprogress := stoppedVortexLevelGreedyProcessLaw_supported_progress
    (W := W) (k := k) hS₀ hD (vortexPackingSaturationFuel V)
  intro S hmass
  have hS := hprogress S hmass
  refine ⟨hS.1, ?_⟩
  rcases hS.2 with hsmall | hcard
  · exact hsmall
  · have hpackingBound := hS.1.1.1.six_mul_card_le
    unfold vortexPackingSaturationFuel at hcard
    omega

/-- Joint inclusion for a fixed-level stopped phase, expressed directly in
the vortex triangle weight. -/
theorem stoppedVortexLevelGreedy_probability_subset_chosen_le_vortexWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell) (k : Fin (ell + 1))
    (D fuel : ℕ) (hD : 0 < D) (c : ℝ≥0)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      c / (W.U k).card)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) :
    (FiniteLaw.iterateKernel
        (stoppedVortexLevelGreedyKernel F W k D) fuel
        (FiniteLaw.pure S)).probability (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) * setWeight (vortexTripleWeight W c) U := by
  let pi : TripleOn V → ℝ≥0 := fun T ↦
    if W.level T = k then (D : ℝ≥0)⁻¹ else 0
  have hjoint := iterateKernel_probability_subset_le_pointWeight
    (stoppedVortexLevelGreedyKernel F W k D)
    (fun S : GreedyStateOn V ↦ S.chosen) pi
    (stoppedVortexLevelGreedyKernel_monotone_singleInsertion F W k D)
    (fun S T hT ↦
      stoppedVortexLevelGreedyKernel_probability_new_triangle_le
        F W k D hD S T hT)
    S U hdisjoint fuel
  apply hjoint.trans
  have hpoint : ∀ T : TripleOn V,
      (fuel : ℝ≥0) * pi T ≤ vortexTripleWeight W c T := by
    intro T
    by_cases hlevel : W.level T = k
    · simp only [pi, hlevel, if_true, vortexTripleWeight]
      simpa only [hlevel] using hratio
    · simp [pi, hlevel, vortexTripleWeight]
  have hweight : (fuel : ℝ≥0) ^ U.card * setWeight pi U =
      setWeight (fun T ↦ (fuel : ℝ≥0) * pi T) U := by
    unfold setWeight
    rw [← prod_const]
    simp only [card_attach, prod_mul_distrib]
  rw [mul_assoc, hweight]
  gcongr
  unfold setWeight
  apply prod_le_prod
  · intro T hTU
    exact bot_le
  · intro T hTU
    exact hpoint T

end

end Erdos207
