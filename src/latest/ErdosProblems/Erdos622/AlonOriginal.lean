/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.LinearArboricity
import ErdosProblems.Erdos622.PippengerSchedule
import ErdosProblems.Erdos76.FiniteBernoulliLocality
import ErdosProblems.Erdos76.PippengerSpencerInnerSurvival
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The quantitative endpoint of Alon's linear-arboricity argument

Alon's 1988 proof first establishes the explicit estimate

`la(G) ≤ d / 2 + 6000 * d * log (log d) / log d + c`

for regular graphs of degree `d`; the extension from regular graphs to graphs
of maximum degree `d` is made by embedding the latter in a regular graph.
The high-girth extraction and induction producing that estimate are separate
combinatorial inputs.  This file verifies the analytic endpoint of the
argument and the exact averaging consequence used by Draganić--Keevash--
Müyesser: a decomposition into at most `(1+epsilon)*D/2` linear forests
contains one forest with at least `2*e(G)/((1+epsilon)*D)` edges.

Primary source: N. Alon, *The linear arboricity of graphs*, Israel J. Math.
62 (1988), 311--325, Theorem 3.1 and Proposition 3.3.
-/

open Filter Finset
open scoped Topology

namespace Erdos622
namespace LinearArboricity

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The relative (degree-normalized) error in Alon's explicit 1988 bound. -/
def alonRelativeError (x : ℝ) : ℝ :=
  6000 * (Real.log (Real.log x) / Real.log x)

/-- Alon's relative error tends to zero.  This is the analytic passage from
Proposition 3.3 of the paper to its asymptotic Theorem 3.1. -/
theorem tendsto_alonRelativeError :
    Tendsto alonRelativeError atTop (𝓝 0) := by
  have hloglog :
      (fun x : ℝ ↦ Real.log (Real.log x)) =o[atTop] Real.log := by
    refine (Real.isLittleO_log_id_atTop.comp_tendsto
      Real.tendsto_log_atTop).congr' ?_ ?_
    · exact Eventually.of_forall fun _ ↦ rfl
    · exact Eventually.of_forall fun _ ↦ rfl
  change Tendsto
    (fun x : ℝ ↦ 6000 * (Real.log (Real.log x) / Real.log x)) atTop (𝓝 0)
  simpa only [mul_zero] using
    hloglog.tendsto_div_nhds_zero.const_mul 6000

/-- The same convergence along natural degree parameters. -/
theorem tendsto_alonRelativeError_nat :
    Tendsto (fun d : ℕ ↦ alonRelativeError d) atTop (𝓝 0) :=
  tendsto_alonRelativeError.comp tendsto_natCast_atTop_atTop

/-- A constant additive term, divided by the degree, tends to zero. -/
theorem tendsto_const_div_natCast (c : ℝ) :
    Tendsto (fun d : ℕ ↦ c / (d : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_natCast_atTop_atTop.inv_tendsto_atTop.const_mul c
  convert h using 1 <;> simp [div_eq_mul_inv]

/-- The normalized error occurring in Proposition 3.3 tends to zero. -/
theorem tendsto_alonTotalRelativeError (c : ℝ) :
    Tendsto (fun d : ℕ ↦ alonRelativeError d + c / (d : ℝ))
      atTop (𝓝 0) :=
  by
    simpa only [zero_add] using
      tendsto_alonRelativeError_nat.add (tendsto_const_div_natCast c)

/-- Eventual epsilon form of the normalized error estimate. -/
theorem eventually_alonTotalRelativeError_lt (c : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ d : ℕ in atTop,
      alonRelativeError d + c / (d : ℝ) < epsilon :=
  (tendsto_alonTotalRelativeError c).eventually_lt_const hepsilon

/-- The explicit error term in Proposition 3.3 is eventually absorbed by
the multiplicative `(1+epsilon)` formulation used in the DKM paper. -/
theorem eventually_alonExplicitBound_le (c : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ d : ℕ in atTop,
      (d : ℝ) / 2 + (d : ℝ) * alonRelativeError d + c ≤
        (1 + epsilon) * (d : ℝ) / 2 := by
  filter_upwards
    [eventually_alonTotalRelativeError_lt c (half_pos hepsilon),
      eventually_gt_atTop 0] with d herror hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcdiv : (d : ℝ) * (c / (d : ℝ)) = c := by
    field_simp
  have hscaled :
      (d : ℝ) * (alonRelativeError d + c / (d : ℝ)) <
        (d : ℝ) * (epsilon / 2) :=
    mul_lt_mul_of_pos_left herror hdR
  rw [mul_add, hcdiv] at hscaled
  nlinarith

/-! ## The finite local-lemma engine used in the random extraction -/

/-- A convenient, completely finite Bernoulli-product form of the symmetric
local lemma.  Alon's random high-girth extraction has precisely this shape:
each bad event is supported on a finite set of edge coordinates and the
dependency graph contains every overlap of supports. -/
theorem exists_avoiding_bernoulli_localEvents
    {E I : Type*} [Fintype E] [DecidableEq E]
    [Fintype I] [DecidableEq I]
    (prob : E → ℝ) (hprob0 : ∀ e, 0 ≤ prob e)
    (hprob1 : ∀ e, prob e ≤ 1)
    (support : I → Finset E) (bad : I → Finset E → Prop)
    (dependency : I → Finset I)
    {bound x : ℝ} {dependencyDegree : ℕ}
    (hbound0 : 0 ≤ bound) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hparameter : bound ≤ x * (1 - x) ^ dependencyDegree)
    (hdegree : ∀ i, (dependency i).card ≤ dependencyDegree)
    (hlocal : ∀ i,
      Erdos76.FiniteNibble.EventDependsOn (support i) (bad i))
    (hoverlap :
      Erdos76.FiniteNibble.ContainsSupportOverlaps support dependency)
    (hmarginal : ∀ i,
      Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset E ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
        (bad i) ≤ bound) :
    ∃ S : Finset E, ∀ i, ¬ bad i S := by
  let mass : Finset E → ℝ := fun S ↦
    Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S
  refine Erdos76.FiniteLocalLemma.exists_avoiding_all
    mass ?_ ?_ bad dependency hbound0 hx0 hx1 hparameter hdegree ?_
  · intro S
    exact Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun e _ ↦ hprob0 e) (fun e _ ↦ hprob1 e)
  · simpa [mass] using
      Erdos76.FiniteNibble.sum_bernoulliMass
        (Finset.univ : Finset E) prob
  · exact Erdos76.FiniteNibble.hasLocalBound_of_eventDependsOn
      prob hprob0 hprob1 support bad dependency hlocal hoverlap hmarginal

/-- Containing a fixed coordinate set is an event supported on that set. -/
lemma eventDependsOn_superset {E : Type*} [Fintype E] [DecidableEq E]
    (R : Finset E) :
    Erdos76.FiniteNibble.EventDependsOn R (fun S : Finset E ↦ R ⊆ S) := by
  intro S T hST
  unfold Erdos76.FiniteNibble.AgreesOn at hST
  constructor
  · intro hRS e heR
    have he : e ∈ S ∩ R := Finset.mem_inter.mpr ⟨hRS heR, heR⟩
    rw [hST] at he
    exact (Finset.mem_inter.mp he).1
  · intro hRT e heR
    have he : e ∈ T ∩ R := Finset.mem_inter.mpr ⟨hRT heR, heR⟩
    rw [← hST] at he
    exact (Finset.mem_inter.mp he).1

/-- Exact Bernoulli mass of the event that all coordinates in `R` occur. -/
lemma bernoulli_eventMass_superset
    {E : Type*} [Fintype E] [DecidableEq E]
    (prob : E → ℝ) (R : Finset E) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset E ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
        (fun S ↦ R ⊆ S) =
      ∏ e ∈ R, prob e := by
  rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass
    (eventDependsOn_superset R)]
  unfold Erdos76.FiniteNibble.restrictedEventMass
  let full : Erdos76.FiniteNibble.Subsets R := ⟨R, Subset.rfl⟩
  rw [Fintype.sum_eq_single full]
  · simp [full, Erdos76.FiniteNibble.bernoulliMass]
  · intro S hS
    have hne : S.1 ≠ R := by
      intro heq
      apply hS
      exact Subtype.ext heq
    have hnot : ¬R ⊆ S.1 := by
      intro hsub
      exact hne (Subset.antisymm S.2 hsub)
    simp [hnot]

/-- Avoiding a fixed coordinate set is also supported on that set. -/
lemma eventDependsOn_disjoint {E : Type*} [Fintype E] [DecidableEq E]
    (R : Finset E) :
    Erdos76.FiniteNibble.EventDependsOn R
      (fun S : Finset E ↦ Disjoint S R) := by
  intro S T hST
  unfold Erdos76.FiniteNibble.AgreesOn at hST
  change Disjoint S R ↔ Disjoint T R
  rw [Finset.disjoint_iff_inter_eq_empty,
    Finset.disjoint_iff_inter_eq_empty, hST]

/-- Exact Bernoulli mass of selecting no coordinate from `R`. -/
lemma bernoulli_eventMass_disjoint
    {E : Type*} [Fintype E] [DecidableEq E]
    (prob : E → ℝ) (R : Finset E) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset E ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
        (fun S ↦ Disjoint S R) =
      ∏ e ∈ R, (1 - prob e) := by
  rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass
    (eventDependsOn_disjoint R)]
  unfold Erdos76.FiniteNibble.restrictedEventMass
  let empty : Erdos76.FiniteNibble.Subsets R := ⟨∅, empty_subset R⟩
  rw [Fintype.sum_eq_single empty]
  · simp [empty, Erdos76.FiniteNibble.bernoulliMass]
  · intro S hS
    have hne : S.1 ≠ ∅ := by
      intro heq
      apply hS
      exact Subtype.ext heq
    have hnot : ¬Disjoint S.1 R := by
      intro hdisj
      have : S.1 = ∅ := by
        rw [← Finset.subset_empty]
        intro e heS
        exact False.elim
          ((Finset.disjoint_left.mp hdisj) heS (S.2 heS))
      exact hne this
    simp [hnot]

namespace AsymmetricLocalLemma

variable {Omega I : Type*} [Fintype Omega] [Fintype I] [DecidableEq I]

/-- Event-dependent local conditional bounds. -/
def HasIndexedLocalBound (mass : Omega → ℝ) (bad : I → Omega → Prop)
    (dependency : I → Finset I) (bound : I → ℝ) : Prop :=
  ∀ (i : I) (S : Finset I), i ∉ S → Disjoint S (dependency i) →
    Erdos76.FiniteLocalLemma.eventMass mass
        (fun omega ↦ bad i omega ∧
          Erdos76.FiniteLocalLemma.Avoid bad S omega) ≤
      bound i * Erdos76.FiniteLocalLemma.eventMass mass
        (Erdos76.FiniteLocalLemma.Avoid bad S)

/-- Exact independence outside the dependency neighbourhood, together with
event-wise marginal estimates, supplies the indexed conditional bounds. -/
lemma hasIndexedLocalBound_of_independentOutside
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    (bound : I → ℝ)
    (hindep : Erdos76.FiniteLocalLemma.IndependentOutside mass bad dependency)
    (hmarginal : ∀ i,
      Erdos76.FiniteLocalLemma.eventMass mass (bad i) ≤ bound i) :
    HasIndexedLocalBound mass bad dependency bound := by
  intro i S hiS hdisj
  rw [hindep i S hiS hdisj]
  exact mul_le_mul_of_nonneg_right (hmarginal i)
    (Erdos76.FiniteLocalLemma.eventMass_nonneg mass hmass
      (Erdos76.FiniteLocalLemma.Avoid bad S))

private theorem conditional_event_le
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    (bound weight : I → ℝ)
    (hweight0 : ∀ i, 0 ≤ weight i) (hweight1 : ∀ i, weight i < 1)
    (hparameter : ∀ i,
      bound i ≤ weight i * ∏ j ∈ dependency i, (1 - weight j))
    (hlocal : HasIndexedLocalBound mass bad dependency bound)
    (S : Finset I) (i : I) (hiS : i ∉ S) :
    Erdos76.FiniteLocalLemma.eventMass mass
        (fun omega ↦ bad i omega ∧
          Erdos76.FiniteLocalLemma.Avoid bad S omega) ≤
      weight i * Erdos76.FiniteLocalLemma.eventMass mass
        (Erdos76.FiniteLocalLemma.Avoid bad S) := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S i with
  | h n ih =>
      let T := S \ dependency i
      let R := S ∩ dependency i
      have hTS : T ⊆ S := sdiff_subset
      have hRS : R ⊆ S := inter_subset_left
      have hRdep : R ⊆ dependency i := inter_subset_right
      have hTR : T ∪ R = S := by
        ext j
        simp [T, R]
        tauto
      have hiT : i ∉ T := fun hi ↦ hiS (hTS hi)
      have hTdisj : Disjoint T (dependency i) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext j
        simp [T]
      have hnum_mono :
          Erdos76.FiniteLocalLemma.eventMass mass
              (fun omega ↦ bad i omega ∧
                Erdos76.FiniteLocalLemma.Avoid bad S omega) ≤
            Erdos76.FiniteLocalLemma.eventMass mass
              (fun omega ↦ bad i omega ∧
                Erdos76.FiniteLocalLemma.Avoid bad T omega) := by
        apply Erdos76.FiniteLocalLemma.eventMass_mono mass hmass
        intro omega homega
        exact ⟨homega.1,
          Erdos76.FiniteLocalLemma.avoid_anti hTS homega.2⟩
      have hnum_local :
          Erdos76.FiniteLocalLemma.eventMass mass
              (fun omega ↦ bad i omega ∧
                Erdos76.FiniteLocalLemma.Avoid bad T omega) ≤
            bound i * Erdos76.FiniteLocalLemma.eventMass mass
              (Erdos76.FiniteLocalLemma.Avoid bad T) :=
        hlocal i T hiT hTdisj
      have hfactor0 : ∀ j, 0 ≤ 1 - weight j :=
        fun j ↦ sub_nonneg.mpr (hweight1 j).le
      have hfactor1 : ∀ j, 1 - weight j ≤ 1 := by
        intro j
        linarith [hweight0 j]
      have hprodDepR :
          (∏ j ∈ dependency i, (1 - weight j)) ≤
            ∏ j ∈ R, (1 - weight j) :=
        Finset.prod_le_prod_of_subset_of_le_one hRdep
          (fun j _ ↦ hfactor0 j) (fun j _ _ ↦ hfactor1 j)
      have hlower_aux : ∀ U : Finset I, U ⊆ R →
          (∏ j ∈ U, (1 - weight j)) *
              Erdos76.FiniteLocalLemma.eventMass mass
                (Erdos76.FiniteLocalLemma.Avoid bad T) ≤
            Erdos76.FiniteLocalLemma.eventMass mass
              (Erdos76.FiniteLocalLemma.Avoid bad (T ∪ U)) := by
        intro U
        induction U using Finset.induction_on with
        | empty =>
            intro _
            simp
        | @insert j U hj ihU =>
            intro hsub
            have hjR : j ∈ R := hsub (mem_insert_self j U)
            have hUR : U ⊆ R := fun a ha ↦ hsub (mem_insert_of_mem ha)
            have hjS : j ∈ S := hRS hjR
            have hjdep : j ∈ dependency i := hRdep hjR
            have hjT : j ∉ T := by simp [T, hjdep]
            have hjTU : j ∉ T ∪ U := by simp [hjT, hj]
            have hTUS : T ∪ U ⊆ S := by
              intro a ha
              rcases mem_union.mp ha with haT | haU
              · exact hTS haT
              · exact hRS (hUR haU)
            have hcard_lt : (T ∪ U).card < n := by
              rw [← hcard]
              exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr
                ⟨hTUS, by
                  intro heq
                  have : j ∈ T ∪ U := heq.symm ▸ hjS
                  exact hjTU this⟩)
            have hcond := ih (T ∪ U).card hcard_lt
              (T ∪ U) j hjTU rfl
            have hstep :
                (1 - weight j) *
                    Erdos76.FiniteLocalLemma.eventMass mass
                      (Erdos76.FiniteLocalLemma.Avoid bad (T ∪ U)) ≤
                  Erdos76.FiniteLocalLemma.eventMass mass
                    (Erdos76.FiniteLocalLemma.Avoid bad
                      (insert j (T ∪ U))) := by
              have hid :=
                Erdos76.FiniteLocalLemma.eventMass_avoid_insert_add
                  mass bad j (T ∪ U)
              linarith
            calc
              (∏ a ∈ insert j U, (1 - weight a)) *
                    Erdos76.FiniteLocalLemma.eventMass mass
                      (Erdos76.FiniteLocalLemma.Avoid bad T) =
                  (1 - weight j) *
                    ((∏ a ∈ U, (1 - weight a)) *
                      Erdos76.FiniteLocalLemma.eventMass mass
                        (Erdos76.FiniteLocalLemma.Avoid bad T)) := by
                rw [prod_insert hj]
                ring
              _ ≤ (1 - weight j) *
                    Erdos76.FiniteLocalLemma.eventMass mass
                      (Erdos76.FiniteLocalLemma.Avoid bad (T ∪ U)) :=
                mul_le_mul_of_nonneg_left (ihU hUR) (hfactor0 j)
              _ ≤ Erdos76.FiniteLocalLemma.eventMass mass
                    (Erdos76.FiniteLocalLemma.Avoid bad
                      (insert j (T ∪ U))) := hstep
              _ = Erdos76.FiniteLocalLemma.eventMass mass
                    (Erdos76.FiniteLocalLemma.Avoid bad
                      (T ∪ insert j U)) := by
                congr 2
                ext a
                simp
      have hlower :
          (∏ j ∈ R, (1 - weight j)) *
              Erdos76.FiniteLocalLemma.eventMass mass
                (Erdos76.FiniteLocalLemma.Avoid bad T) ≤
            Erdos76.FiniteLocalLemma.eventMass mass
              (Erdos76.FiniteLocalLemma.Avoid bad S) := by
        simpa only [hTR] using hlower_aux R Subset.rfl
      have hmassT :
          0 ≤ Erdos76.FiniteLocalLemma.eventMass mass
            (Erdos76.FiniteLocalLemma.Avoid bad T) :=
        Erdos76.FiniteLocalLemma.eventMass_nonneg mass hmass _
      calc
        Erdos76.FiniteLocalLemma.eventMass mass
            (fun omega ↦ bad i omega ∧
              Erdos76.FiniteLocalLemma.Avoid bad S omega) ≤
          bound i * Erdos76.FiniteLocalLemma.eventMass mass
            (Erdos76.FiniteLocalLemma.Avoid bad T) :=
          hnum_mono.trans hnum_local
        _ ≤ (weight i * ∏ j ∈ dependency i, (1 - weight j)) *
              Erdos76.FiniteLocalLemma.eventMass mass
                (Erdos76.FiniteLocalLemma.Avoid bad T) :=
          mul_le_mul_of_nonneg_right (hparameter i) hmassT
        _ ≤ (weight i * ∏ j ∈ R, (1 - weight j)) *
              Erdos76.FiniteLocalLemma.eventMass mass
                (Erdos76.FiniteLocalLemma.Avoid bad T) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprodDepR (hweight0 i)) hmassT
        _ = weight i *
              ((∏ j ∈ R, (1 - weight j)) *
                Erdos76.FiniteLocalLemma.eventMass mass
                  (Erdos76.FiniteLocalLemma.Avoid bad T)) := by ring
        _ ≤ weight i * Erdos76.FiniteLocalLemma.eventMass mass
              (Erdos76.FiniteLocalLemma.Avoid bad S) :=
          mul_le_mul_of_nonneg_left hlower (hweight0 i)

/-- Finite asymmetric local lemma in the event-dependent product form used
in Alon's proof. -/
theorem exists_avoiding_all
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_total : ∑ omega, mass omega = 1)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    (bound weight : I → ℝ)
    (hweight0 : ∀ i, 0 ≤ weight i) (hweight1 : ∀ i, weight i < 1)
    (hparameter : ∀ i,
      bound i ≤ weight i * ∏ j ∈ dependency i, (1 - weight j))
    (hlocal : HasIndexedLocalBound mass bad dependency bound) :
    ∃ omega, ∀ i, ¬ bad i omega := by
  have hcond : ∀ (S : Finset I) (i : I), i ∉ S →
      Erdos76.FiniteLocalLemma.eventMass mass
          (fun omega ↦ bad i omega ∧
            Erdos76.FiniteLocalLemma.Avoid bad S omega) ≤
        weight i * Erdos76.FiniteLocalLemma.eventMass mass
          (Erdos76.FiniteLocalLemma.Avoid bad S) :=
    conditional_event_le mass hmass bad dependency bound weight
      hweight0 hweight1 hparameter hlocal
  have hAvoidLower : ∀ S : Finset I,
      (∏ i ∈ S, (1 - weight i)) ≤
        Erdos76.FiniteLocalLemma.eventMass mass
          (Erdos76.FiniteLocalLemma.Avoid bad S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa [Erdos76.FiniteLocalLemma.eventMass,
          Erdos76.FiniteLocalLemma.Avoid] using hmass_total.ge
    | @insert i S hiS ihS =>
        have hstep :
            (1 - weight i) *
                Erdos76.FiniteLocalLemma.eventMass mass
                  (Erdos76.FiniteLocalLemma.Avoid bad S) ≤
              Erdos76.FiniteLocalLemma.eventMass mass
                (Erdos76.FiniteLocalLemma.Avoid bad (insert i S)) := by
          have hc := hcond S i hiS
          have hid := Erdos76.FiniteLocalLemma.eventMass_avoid_insert_add
            mass bad i S
          linarith
        calc
          (∏ j ∈ insert i S, (1 - weight j)) =
              (1 - weight i) * ∏ j ∈ S, (1 - weight j) := by
            rw [prod_insert hiS]
          _ ≤ (1 - weight i) *
                Erdos76.FiniteLocalLemma.eventMass mass
                  (Erdos76.FiniteLocalLemma.Avoid bad S) :=
            mul_le_mul_of_nonneg_left ihS
              (sub_nonneg.mpr (hweight1 i).le)
          _ ≤ Erdos76.FiniteLocalLemma.eventMass mass
                (Erdos76.FiniteLocalLemma.Avoid bad (insert i S)) := hstep
  by_contra hnone
  push Not at hnone
  have hzero :
      Erdos76.FiniteLocalLemma.eventMass mass
        (Erdos76.FiniteLocalLemma.Avoid bad (univ : Finset I)) = 0 := by
    unfold Erdos76.FiniteLocalLemma.eventMass
    apply sum_eq_zero
    intro omega _
    have hnot :
        ¬ Erdos76.FiniteLocalLemma.Avoid bad (univ : Finset I) omega := by
      intro hAvoid
      obtain ⟨i, hi⟩ := hnone omega
      exact hAvoid i (mem_univ i) hi
    simp [hnot]
  have hpos : 0 < ∏ i ∈ (univ : Finset I), (1 - weight i) :=
    Finset.prod_pos fun i _ ↦ sub_pos.mpr (hweight1 i)
  have := hAvoidLower (univ : Finset I)
  rw [hzero] at this
  linarith

end AsymmetricLocalLemma

namespace IndependentTransversal

universe v

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- Vertex-selection probability in Alon's independent-transversal proof. -/
def vertexProbability (d : ℕ) : ℝ := 1 / (25 * (d : ℝ))

/-- Local-lemma weight assigned to a bad edge event. -/
def edgeWeight (d : ℕ) : ℝ := 1 / (100 * (d : ℝ) ^ 2)

/-- One part of a function-coded vertex partition. -/
def partFiber {r : ℕ} (part : V → Fin r) (i : Fin r) : Finset V :=
  Finset.univ.filter fun v ↦ part v = i

@[simp] lemma mem_partFiber {r : ℕ} (part : V → Fin r) (i : Fin r) (v : V) :
    v ∈ partFiber part i ↔ part v = i := by
  simp [partFiber]

/-- Bad-event indices: one for every partition class and one for every graph
edge. -/
abbrev EventIndex (r : ℕ) (G : SimpleGraph V) := Fin r ⊕ G.edgeSet

/-- Coordinate support of an empty-part or selected-edge event. -/
def eventSupport {r : ℕ} (G : SimpleGraph V) (part : V → Fin r) :
    EventIndex r G → Finset V
  | Sum.inl i => partFiber part i
  | Sum.inr e => e.1.toFinset

/-- The two families of bad events in Alon's proof. -/
def badEvent {r : ℕ} (G : SimpleGraph V) (part : V → Fin r) :
    EventIndex r G → Finset V → Prop
  | Sum.inl i, S => Disjoint S (partFiber part i)
  | Sum.inr e, S => e.1.toFinset ⊆ S

/-- Edges meeting a vertex set, represented through the rank-two
hypergraph associated with `G`. -/
def meetingEdges (G : SimpleGraph V) (A : Finset V) : Finset G.edgeSet :=
  (Erdos622.PippengerSchedule.graphHypergraph G).edgesMeeting A

/-- The explicit dependency neighbourhood from Proposition 2.4. -/
def dependency {r : ℕ} (G : SimpleGraph V) (part : V → Fin r) :
    EventIndex r G → Finset (EventIndex r G)
  | Sum.inl i =>
      (meetingEdges G (partFiber part i)).map Function.Embedding.inr
  | Sum.inr e =>
      (e.1.toFinset.image part).map Function.Embedding.inl ∪
        ((meetingEdges G e.1.toFinset).erase e).map Function.Embedding.inr

/-- Local-lemma weights for the two event families. -/
def eventWeight {r : ℕ} (G : SimpleGraph V) (d : ℕ) :
    EventIndex r G → ℝ
  | Sum.inl _ => 1 / 2
  | Sum.inr _ => edgeWeight d

/-- Marginal upper bounds for the two event families. -/
def eventBound {r : ℕ} (G : SimpleGraph V) (part : V → Fin r) (d : ℕ) :
    EventIndex r G → ℝ
  | Sum.inl i => (1 - vertexProbability d) ^ (partFiber part i).card
  | Sum.inr _ => vertexProbability d ^ 2

lemma prod_dependency_inl {r : ℕ} (G : SimpleGraph V)
    (part : V → Fin r) (d : ℕ) (i : Fin r) :
    (∏ j ∈ dependency G part (Sum.inl i), (1 - eventWeight G d j)) =
      (1 - edgeWeight d) ^ (meetingEdges G (partFiber part i)).card := by
  simp [dependency, eventWeight]

lemma prod_dependency_inr {r : ℕ} (G : SimpleGraph V)
    (part : V → Fin r) (d : ℕ) (e : G.edgeSet) :
    (∏ j ∈ dependency G part (Sum.inr e), (1 - eventWeight G d j)) =
      (1 / 2 : ℝ) ^ (e.1.toFinset.image part).card *
        (1 - edgeWeight d) ^ ((meetingEdges G e.1.toFinset).erase e).card := by
  have hdisj : Disjoint
      ((e.1.toFinset.image part).map Function.Embedding.inl)
      (((meetingEdges G e.1.toFinset).erase e).map
        Function.Embedding.inr) := by
    rw [Finset.disjoint_left]
    intro z hzLeft hzRight
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp hzLeft
    obtain ⟨b, _hb, hab⟩ := Finset.mem_map.mp hzRight
    exact Sum.inr_ne_inl hab
  have hleft :
      (∏ j ∈ (e.1.toFinset.image part).map Function.Embedding.inl,
        (1 - eventWeight G d j)) =
        (1 / 2 : ℝ) ^ (e.1.toFinset.image part).card := by
    rw [Finset.prod_map]
    simp [eventWeight]
    rw [show (1 - (2 : ℝ)⁻¹) = 2⁻¹ by norm_num, inv_pow]
  have hright :
      (∏ j ∈ ((meetingEdges G e.1.toFinset).erase e).map
          (Function.Embedding.inr : G.edgeSet ↪ EventIndex r G),
        (1 - eventWeight G d j)) =
        (1 - edgeWeight d) ^
          ((meetingEdges G e.1.toFinset).erase e).card := by
    rw [Finset.prod_map]
    simp [eventWeight]
  change
    (∏ j ∈ (e.1.toFinset.image part).map Function.Embedding.inl ∪
        ((meetingEdges G e.1.toFinset).erase e).map
          (Function.Embedding.inr : G.edgeSet ↪ EventIndex r G),
      (1 - eventWeight G d j)) = _
  rw [prod_union hdisj, hleft, hright]

lemma meetingEdges_card_le {G : SimpleGraph V} {d : ℕ}
    (hdegree : ∀ v, G.degree v ≤ d) (A : Finset V) :
    (meetingEdges G A).card ≤ A.card * d := by
  apply Erdos76.FiniteHypergraph.edgesMeeting_card_le_mul_degree
  intro v _hv
  simpa [meetingEdges, Erdos622.PippengerSchedule.graphHypergraph_edgeDegree]
    using hdegree v

lemma eventWeight_nonneg {r : ℕ} (G : SimpleGraph V) {d : ℕ} (hd : 0 < d)
    (i : EventIndex r G) : 0 ≤ eventWeight G d i := by
  cases i with
  | inl i => norm_num [eventWeight]
  | inr e =>
      rw [eventWeight, edgeWeight]
      positivity

lemma eventWeight_lt_one {r : ℕ} (G : SimpleGraph V) {d : ℕ} (hd : 0 < d)
    (i : EventIndex r G) : eventWeight G d i < 1 := by
  cases i with
  | inl i => norm_num [eventWeight]
  | inr e =>
      rw [eventWeight, edgeWeight]
      have hdd : 1 * 1 ≤ d * d := Nat.mul_le_mul hd hd
      have hdenNat : 1 < 100 * (d * d) := by omega
      apply (div_lt_one (by positivity)).2
      simpa [pow_two] using (show (1 : ℝ) < 100 * ((d : ℝ) * d) by
        exact_mod_cast hdenNat)

/-- Each bad event only depends on the advertised vertex coordinates. -/
lemma badEvent_dependsOn {r : ℕ} (G : SimpleGraph V) (part : V → Fin r)
    (i : EventIndex r G) :
    Erdos76.FiniteNibble.EventDependsOn (eventSupport G part i)
      (badEvent G part i) := by
  cases i with
  | inl i =>
      exact eventDependsOn_disjoint (partFiber part i)
  | inr e =>
      exact eventDependsOn_superset e.1.toFinset

/-- The explicit dependency neighbourhood contains every overlap of event
supports. -/
lemma dependency_contains_overlaps {r : ℕ} (G : SimpleGraph V)
    (part : V → Fin r) :
    Erdos76.FiniteNibble.ContainsSupportOverlaps
      (eventSupport G part) (dependency G part) := by
  intro i j hij hoverlap
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          exfalso
          obtain ⟨v, hvi, hvj⟩ := not_disjoint_iff.mp hoverlap
          have hi : part v = i := (mem_partFiber part i v).mp hvi
          have hj : part v = j := (mem_partFiber part j v).mp hvj
          apply hij
          simp only [Sum.inl.injEq]
          exact hi.symm.trans hj
      | inr e =>
          simp only [dependency, Finset.mem_map]
          refine ⟨e, ?_, rfl⟩
          rw [meetingEdges, Erdos76.FiniteHypergraph.mem_edgesMeeting]
          exact fun hdisj ↦ hoverlap hdisj.symm
  | inr e =>
      cases j with
      | inl j =>
          simp only [dependency, mem_union, Finset.mem_map]
          left
          obtain ⟨v, hve, hvj⟩ := not_disjoint_iff.mp hoverlap
          refine ⟨j, ?_, rfl⟩
          exact mem_image.mpr
            ⟨v, hve, (mem_partFiber part j v).mp hvj⟩
      | inr f =>
          simp only [dependency, mem_union, Finset.mem_map]
          right
          refine ⟨f, ?_, rfl⟩
          apply mem_erase.mpr
          constructor
          · intro hef
            apply hij
            simp only [Sum.inr.injEq]
            exact hef.symm
          · rw [meetingEdges, Erdos76.FiniteHypergraph.mem_edgesMeeting]
            exact fun hdisj ↦ hoverlap hdisj.symm

/-- Exact marginal masses of both kinds of bad event. -/
lemma badEvent_marginal {r : ℕ} (G : SimpleGraph V) (part : V → Fin r)
    (d : ℕ) (i : EventIndex r G) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset V ↦ Erdos76.FiniteNibble.bernoulliMass
          Finset.univ (fun _ ↦ vertexProbability d) S)
        (badEvent G part i) =
      match i with
      | Sum.inl a => (1 - vertexProbability d) ^ (partFiber part a).card
      | Sum.inr _ => vertexProbability d ^ 2 := by
  cases i with
  | inl i =>
      rw [show badEvent G part (Sum.inl i) =
          (fun S ↦ Disjoint S (partFiber part i)) by rfl,
        bernoulli_eventMass_disjoint]
      simp
  | inr e =>
      rw [show badEvent G part (Sum.inr e) =
          (fun S ↦ e.1.toFinset ⊆ S) by rfl,
        bernoulli_eventMass_superset]
      rw [prod_const, Sym2.card_toFinset_of_not_isDiag e.1
        (G.not_isDiag_of_mem_edgeSet e.2)]

/-- The numerical inequality for an empty-part bad event in Proposition 2.4
of Alon's paper. -/
lemma emptyPart_parameter {d : ℕ} (hd : 0 < d) :
    (1 - vertexProbability d) ^ (25 * d) ≤
      (1 / 2 : ℝ) * (1 - edgeWeight d) ^ (25 * d * d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (1 : ℝ) ≤ (25 * d : ℕ) := by
    exact_mod_cast (show 1 ≤ 25 * d by omega)
  have hupp :
      (1 - vertexProbability d) ^ (25 * d) ≤ Real.exp (-1) := by
    simpa [vertexProbability, Nat.cast_mul] using
      (Real.one_sub_div_pow_le_exp_neg (n := 25 * d) (t := 1) hn)
  have hq0 : 0 ≤ edgeWeight d := by
    rw [edgeWeight]
    positivity
  have hq1 : edgeWeight d ≤ 1 := by
    rw [edgeWeight]
    have hden : (1 : ℝ) ≤ 100 * (d : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd]
    exact (div_le_one (by positivity)).2 hden
  have hbern := one_add_mul_le_pow
    (a := -edgeWeight d) (by linarith : (-2 : ℝ) ≤ -edgeWeight d)
    (25 * d * d)
  have hlinear :
      (3 / 4 : ℝ) =
        1 + ((25 * d * d : ℕ) : ℝ) * (-edgeWeight d) := by
    rw [edgeWeight]
    push_cast
    field_simp
    ring
  have hlow :
      (3 / 4 : ℝ) ≤ (1 - edgeWeight d) ^ (25 * d * d) := by
    rw [hlinear]
    simpa [sub_eq_add_neg] using hbern
  calc
    (1 - vertexProbability d) ^ (25 * d) ≤ Real.exp (-1) := hupp
    _ ≤ 3 / 8 := (Real.exp_neg_one_lt_d9.trans (by norm_num)).le
    _ = (1 / 2 : ℝ) * (3 / 4) := by norm_num
    _ ≤ (1 / 2 : ℝ) * (1 - edgeWeight d) ^ (25 * d * d) :=
      mul_le_mul_of_nonneg_left hlow (by norm_num)

/-- The numerical inequality for a selected-edge bad event in Proposition
2.4 of Alon's paper. -/
lemma selectedEdge_parameter {d : ℕ} (hd : 0 < d) :
    vertexProbability d ^ 2 ≤
      edgeWeight d * (1 / 2 : ℝ) ^ 2 *
        (1 - edgeWeight d) ^ (2 * d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ edgeWeight d := by
    rw [edgeWeight]
    positivity
  have hq1 : edgeWeight d ≤ 1 := by
    rw [edgeWeight]
    have hden : (1 : ℝ) ≤ 100 * (d : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd]
    exact (div_le_one (by positivity)).2 hden
  have hbern := one_add_mul_le_pow
    (a := -edgeWeight d) (by linarith : (-2 : ℝ) ≤ -edgeWeight d)
    (2 * d)
  have hlinear :
      1 - (1 : ℝ) / (50 * d) =
        1 + ((2 * d : ℕ) : ℝ) * (-edgeWeight d) := by
    rw [edgeWeight]
    push_cast
    field_simp
    ring
  have hpow :
      1 - (1 : ℝ) / (50 * d) ≤
        (1 - edgeWeight d) ^ (2 * d) := by
    rw [hlinear]
    simpa [sub_eq_add_neg] using hbern
  have hrough :
      (16 / 25 : ℝ) ≤ 1 - (1 : ℝ) / (50 * d) := by
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hinv : (1 : ℝ) / (50 * d) ≤ 1 / 50 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 50 * d)
        (by norm_num : (0 : ℝ) < 50)).2
      nlinarith
    nlinarith
  have hpow' : (16 / 25 : ℝ) ≤
      (1 - edgeWeight d) ^ (2 * d) := hrough.trans hpow
  have hcoef : 0 ≤ edgeWeight d * (1 / 2 : ℝ) ^ 2 := by
    exact mul_nonneg hq0 (sq_nonneg _)
  calc
    vertexProbability d ^ 2 =
        edgeWeight d * (1 / 2 : ℝ) ^ 2 * (16 / 25 : ℝ) := by
      rw [vertexProbability, edgeWeight]
      field_simp
      ring
    _ ≤ edgeWeight d * (1 / 2 : ℝ) ^ 2 *
          (1 - edgeWeight d) ^ (2 * d) :=
      mul_le_mul_of_nonneg_left hpow' hcoef

/-- The two numerical estimates above verify every asymmetric-local-lemma
parameter inequality for Alon's bad events. -/
lemma event_parameter {r : ℕ} (G : SimpleGraph V) (part : V → Fin r)
    {d : ℕ} (hd : 0 < d) (hdegree : ∀ v, G.degree v ≤ d)
    (hcard : ∀ i, (partFiber part i).card = 25 * d)
    (i : EventIndex r G) :
    eventBound G part d i ≤ eventWeight G d i *
      ∏ j ∈ dependency G part i, (1 - eventWeight G d j) := by
  have hq0 : 0 ≤ edgeWeight d := by
    rw [edgeWeight]
    positivity
  have hq1 : edgeWeight d ≤ 1 := by
    rw [edgeWeight]
    have hden : (1 : ℝ) ≤ 100 * (d : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd]
    exact (div_le_one (by positivity)).2 hden
  have hb0 : 0 ≤ 1 - edgeWeight d := sub_nonneg.mpr hq1
  have hb1 : 1 - edgeWeight d ≤ 1 := by linarith [hq0]
  cases i with
  | inl a =>
      rw [eventBound, eventWeight, prod_dependency_inl, hcard a]
      have hmeet : (meetingEdges G (partFiber part a)).card ≤ 25 * d * d := by
        simpa [hcard a, Nat.mul_assoc] using
          meetingEdges_card_le (G := G) hdegree (partFiber part a)
      have hpow :
          (1 - edgeWeight d) ^ (25 * d * d) ≤
            (1 - edgeWeight d) ^
              (meetingEdges G (partFiber part a)).card :=
        pow_le_pow_of_le_one hb0 hb1 hmeet
      exact (emptyPart_parameter hd).trans
        (mul_le_mul_of_nonneg_left hpow (by norm_num))
  | inr e =>
      rw [eventBound, eventWeight, prod_dependency_inr]
      have hpartCard : (e.1.toFinset.image part).card ≤ 2 := by
        exact (card_image_le.trans_eq
          (Sym2.card_toFinset_of_not_isDiag e.1
            (G.not_isDiag_of_mem_edgeSet e.2)))
      have hedgeCard :
          ((meetingEdges G e.1.toFinset).erase e).card ≤ 2 * d := by
        calc
          ((meetingEdges G e.1.toFinset).erase e).card ≤
              (meetingEdges G e.1.toFinset).card := card_erase_le
          _ ≤ e.1.toFinset.card * d :=
            meetingEdges_card_le (G := G) hdegree e.1.toFinset
          _ = 2 * d := congrArg (fun n ↦ n * d)
            (Sym2.card_toFinset_of_not_isDiag e.1
              (G.not_isDiag_of_mem_edgeSet e.2))
      have hhalfPow :
          (1 / 2 : ℝ) ^ 2 ≤
            (1 / 2 : ℝ) ^ (e.1.toFinset.image part).card :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hpartCard
      have hedgePow :
          (1 - edgeWeight d) ^ (2 * d) ≤
            (1 - edgeWeight d) ^
              ((meetingEdges G e.1.toFinset).erase e).card :=
        pow_le_pow_of_le_one hb0 hb1 hedgeCard
      have hprod :
          (1 / 2 : ℝ) ^ 2 * (1 - edgeWeight d) ^ (2 * d) ≤
            (1 / 2 : ℝ) ^ (e.1.toFinset.image part).card *
              (1 - edgeWeight d) ^
                ((meetingEdges G e.1.toFinset).erase e).card :=
        mul_le_mul hhalfPow hedgePow (by positivity) (by positivity)
      exact (selectedEdge_parameter hd).trans
        (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod hq0)

/-- Alon's Proposition 2.4 in the equal-size form: a graph of maximum degree
`d` whose vertex partition has classes of size `25 d` has an independent
transversal.  The original at-least-size form follows by trimming each class;
this exact form is the probabilistic core used in the large-girth argument. -/
theorem exists_independent_transversal_exact {r d : ℕ} (hd : 0 < d)
    (G : SimpleGraph V) (part : V → Fin r)
    (hdegree : ∀ v, G.degree v ≤ d)
    (hcard : ∀ i, (partFiber part i).card = 25 * d) :
    ∃ W : Finset V,
      (∀ i : Fin r, ∃ v, v ∈ W ∧ part v = i) ∧
      ∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v := by
  let p : V → ℝ := fun _ ↦ vertexProbability d
  let mass : Finset V → ℝ := fun W ↦
    Erdos76.FiniteNibble.bernoulliMass Finset.univ p W
  have hp0 : ∀ v, 0 ≤ p v := by
    intro v
    simp only [p, vertexProbability]
    positivity
  have hp1 : ∀ v, p v ≤ 1 := by
    intro v
    simp only [p, vertexProbability]
    have hden : (1 : ℝ) ≤ 25 * (d : ℝ) := by
      exact_mod_cast (show 1 ≤ 25 * d by omega)
    exact (div_le_one (by positivity)).2 hden
  have hmass0 : ∀ W, 0 ≤ mass W := by
    intro W
    exact Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ W)
      (fun v _ ↦ hp0 v) (fun v _ ↦ hp1 v)
  have hmassTotal : ∑ W, mass W = 1 := by
    simpa [mass] using
      (Erdos76.FiniteNibble.sum_bernoulliMass
        (Finset.univ : Finset V) p)
  have hindep : Erdos76.FiniteLocalLemma.IndependentOutside mass
      (badEvent G part) (dependency G part) := by
    simpa [mass, p] using
      (Erdos76.FiniteNibble.independentOutside_of_eventDependsOn
        (fun _ : V ↦ vertexProbability d) (eventSupport G part)
        (badEvent G part) (dependency G part)
        (badEvent_dependsOn G part)
        (dependency_contains_overlaps G part))
  have hmarginal : ∀ i,
      Erdos76.FiniteLocalLemma.eventMass mass (badEvent G part i) ≤
        eventBound G part d i := by
    intro i
    cases i with
    | inl a =>
        simpa [mass, p, eventBound] using
          (badEvent_marginal G part d (Sum.inl a)).le
    | inr e =>
        simpa [mass, p, eventBound] using
          (badEvent_marginal G part d (Sum.inr e)).le
  have hlocal : AsymmetricLocalLemma.HasIndexedLocalBound mass
      (badEvent G part) (dependency G part) (eventBound G part d) :=
    AsymmetricLocalLemma.hasIndexedLocalBound_of_independentOutside
      mass hmass0 (badEvent G part) (dependency G part)
      (eventBound G part d) hindep hmarginal
  obtain ⟨W, hW⟩ := AsymmetricLocalLemma.exists_avoiding_all
    mass hmass0 hmassTotal (badEvent G part) (dependency G part)
      (eventBound G part d) (eventWeight G d)
      (eventWeight_nonneg G hd) (eventWeight_lt_one G hd)
      (event_parameter G part hd hdegree hcard) hlocal
  refine ⟨W, ?_, ?_⟩
  · intro i
    have hnot : ¬ Disjoint W (partFiber part i) := hW (Sum.inl i)
    obtain ⟨v, hvW, hvpart⟩ := not_disjoint_iff.mp hnot
    exact ⟨v, hvW, (mem_partFiber part i v).mp hvpart⟩
  · intro u huW v hvW huv
    let e : G.edgeSet := ⟨s(u, v), huv⟩
    have hbad : badEvent G part (Sum.inr e) W := by
      change e.1.toFinset ⊆ W
      simpa [e, Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using
        And.intro huW hvW
    exact hW (Sum.inr e) hbad

/-- Alon's Proposition 2.4 exactly as published: classes may be larger than
`25 d`.  Trim every class, apply the exact-size result to the induced graph,
and map its transversal back to the original vertex type. -/
theorem exists_independent_transversal {r d : ℕ} (hd : 0 < d)
    (G : SimpleGraph V) (part : V → Fin r)
    (hdegree : ∀ v, G.degree v ≤ d)
    (hcard : ∀ i, 25 * d ≤ (partFiber part i).card) :
    ∃ W : Finset V,
      (∀ i : Fin r, ∃ v, v ∈ W ∧ part v = i) ∧
      ∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v := by
  classical
  choose A hAsub hAcard using fun i ↦
    Finset.exists_subset_card_eq (hcard i)
  let S : Set V := {v | v ∈ A (part v)}
  let part' : S → Fin r := fun v ↦ part v.1
  have hfiber : ∀ i, (partFiber part' i).card = 25 * d := by
    intro i
    have hmap :
        (partFiber part' i).map (Function.Embedding.subtype S) = A i := by
      ext v
      constructor
      · intro hv
        obtain ⟨x, hxpart, hxv⟩ := Finset.mem_map.mp hv
        subst v
        have hxpart' : part x.1 = i := by
          simpa [part'] using (mem_partFiber part' i x).mp hxpart
        change x.1 ∈ A i
        have hxA : x.1 ∈ A (part x.1) := x.2
        simpa [hxpart'] using hxA
      · intro hv
        have hvpart : part v = i :=
          (mem_partFiber part i v).mp (hAsub i hv)
        let x : S := ⟨v, by simpa [S, hvpart] using hv⟩
        apply Finset.mem_map.mpr
        refine ⟨x, ?_, rfl⟩
        exact (mem_partFiber part' i x).mpr (by simpa [part', x] using hvpart)
    calc
      (partFiber part' i).card =
          ((partFiber part' i).map (Function.Embedding.subtype S)).card :=
        (Finset.card_map _).symm
      _ = (A i).card := congrArg Finset.card hmap
      _ = 25 * d := hAcard i
  have hdegree' : ∀ v : S, (G.induce S).degree v ≤ d := by
    intro v
    have hsubset :
        ((G.induce S).neighborFinset v).map
            (Function.Embedding.subtype S) ⊆ G.neighborFinset v.1 := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hw
      rw [SimpleGraph.mem_neighborFinset]
      change G.Adj v.1 a.1
      rw [SimpleGraph.mem_neighborFinset] at ha
      exact ha
    calc
      (G.induce S).degree v = ((G.induce S).neighborFinset v).card :=
        ((G.induce S).card_neighborFinset_eq_degree v).symm
      _ = (((G.induce S).neighborFinset v).map
            (Function.Embedding.subtype S)).card :=
        (Finset.card_map _).symm
      _ ≤ (G.neighborFinset v.1).card := Finset.card_le_card hsubset
      _ = G.degree v.1 := G.card_neighborFinset_eq_degree v.1
      _ ≤ d := hdegree v.1
  obtain ⟨W, hpartW, hindW⟩ :=
    exists_independent_transversal_exact hd (G.induce S) part'
      hdegree' hfiber
  let W' : Finset V := W.map (Function.Embedding.subtype S)
  refine ⟨W', ?_, ?_⟩
  · intro i
    obtain ⟨v, hvW, hvpart⟩ := hpartW i
    refine ⟨v.1, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨v, hvW, rfl⟩
    · simpa [part'] using hvpart
  · intro u huW v hvW huv
    obtain ⟨u', hu'W, hu'⟩ := Finset.mem_map.mp huW
    obtain ⟨v', hv'W, hv'⟩ := Finset.mem_map.mp hvW
    subst u
    subst v
    exact hindW u' hu'W v' hv'W huv

end IndependentTransversal

variable {V : Type u} [Fintype V]

/-- The one-large-forest conclusion extracted from a linear-forest
decomposition.  This is the only consequence of linear arboricity used in
the induced-edge part of the almost-bipartite argument. -/
theorem Decomposition.exists_linearForest_edgeDensity
    [DecidableEq V] {G : SimpleGraph V} {k D : ℕ}
    (d : Decomposition G k) (hk : 0 < k) (hD : 0 < D)
    {epsilon : ℝ} (hepsilon : -1 < epsilon)
    (hkBound : (k : ℝ) ≤ (1 + epsilon) * (D : ℝ) / 2) :
    ∃ F : SimpleGraph V,
      F ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest F ∧
      2 * (Fintype.card G.edgeSet : ℝ) /
          ((1 + epsilon) * (D : ℝ)) ≤
        (Fintype.card F.edgeSet : ℝ) := by
  obtain ⟨F, hFG, hlinear, haverage⟩ := d.exists_large_linearForest hk
  refine ⟨F, hFG, hlinear, ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hscale : 0 < (1 + epsilon) * (D : ℝ) :=
    mul_pos (by linarith) hDR
  have hcount : 0 ≤ (Fintype.card G.edgeSet : ℝ) := by positivity
  have hkScale : (k : ℝ) ≤ ((1 + epsilon) * (D : ℝ)) / 2 := by
    simpa [mul_assoc] using hkBound
  have hrecip :
      2 / ((1 + epsilon) * (D : ℝ)) ≤ 1 / (k : ℝ) := by
    rw [div_le_div_iff₀ hscale hkR]
    nlinarith
  calc
    2 * (Fintype.card G.edgeSet : ℝ) /
          ((1 + epsilon) * (D : ℝ)) =
        (Fintype.card G.edgeSet : ℝ) *
          (2 / ((1 + epsilon) * (D : ℝ))) := by ring
    _ ≤ (Fintype.card G.edgeSet : ℝ) * (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip hcount
    _ = (Fintype.card G.edgeSet : ℝ) / (k : ℝ) := by ring
    _ ≤ (Fintype.card F.edgeSet : ℝ) := haverage

/-- The weakest uniform asymptotic linear-arboricity consequence needed by
the Erdős 622 proof: eventually, every graph of maximum degree at most `D`
contains one linear forest of the stated density. -/
def AsymptoticLargeLinearForest : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ D₀ : ℕ,
      ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) (D : ℕ),
        D₀ ≤ D →
        (∀ v, G.degree v ≤ D) →
        ∃ F : SimpleGraph V,
          F ≤ G ∧ Erdos622.SimpleGraph.IsLinearForest F ∧
          2 * (Fintype.card G.edgeSet : ℝ) /
              ((1 + epsilon) * (D : ℝ)) ≤
            (Fintype.card F.edgeSet : ℝ)

/-- Alon's decomposition theorem implies exactly the large-forest interface
used by DKM.  The threshold is enlarged to make the degree positive, which
is needed only to divide by it. -/
theorem asymptoticLargeLinearForest_of_asymptoticLinearArboricity
    (hAlon : AsymptoticLinearArboricity.{u}) :
    AsymptoticLargeLinearForest.{u} := by
  intro epsilon hepsilon
  obtain ⟨D₀, hD₀⟩ := hAlon epsilon hepsilon
  refine ⟨max D₀ 1, ?_⟩
  intro W _ _ G D hD hdegree
  have hD₀D : D₀ ≤ D := (le_max_left D₀ 1).trans hD
  have hDpos : 0 < D := (le_max_right D₀ 1).trans hD
  obtain ⟨k, hk, hkBound, hd⟩ := hD₀ W G D hD₀D hdegree
  let d : Decomposition G k := Classical.choice hd
  exact d.exists_linearForest_edgeDensity hk hDpos (by linarith) hkBound

end

end LinearArboricity
end Erdos622
