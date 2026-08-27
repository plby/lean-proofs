import ErdosProblems.Erdos745.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The parameterized Erdős--Rényi model for Problem 745

Clipping makes the measure defined at every natural index.  The theorem
`eventually_edgeProbability_eq` proves that the edge probability is exactly
`lam / n` at all sufficiently large indices for every nonnegative fixed `lam`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology unitInterval

namespace Erdos745

/-- The edge probability `lam/n`, clipped only at inadmissible early indices. -/
noncomputable def edgeProbability (lam : ℝ) (n : ℕ) : unitInterval :=
  ⟨max 0 (min 1 (lam / n)), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩

theorem coe_edgeProbability {lam : ℝ} {n : ℕ}
    (hlam : 0 ≤ lam) (hn : 0 < n) (hlamn : lam ≤ n) :
    (edgeProbability lam n : ℝ) = lam / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change max 0 (min 1 (lam / n)) = lam / n
  rw [min_eq_right ((div_le_one hnR).mpr hlamn),
    max_eq_right (div_nonneg hlam hnR.le)]

theorem eventually_edgeProbability_eq {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ᶠ n : ℕ in atTop, (edgeProbability lam n : ℝ) = lam / n := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop lam),
    eventually_gt_atTop (0 : ℕ)] with n hlamn hn
  exact coe_edgeProbability hlam hn hlamn

@[simp] theorem edgeProbability_one (n : ℕ) :
    edgeProbability 1 n = criticalEdgeProbability n := by
  by_cases hn : n = 0
  · subst n
    apply Subtype.ext
    simp [edgeProbability]
  · apply Subtype.ext
    rw [coe_edgeProbability zero_le_one (Nat.pos_of_ne_zero hn)
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)),
      coe_criticalEdgeProbability hn]

/-- The exact independent-edge random graph with fixed density parameter `lam`. -/
noncomputable def randomGraph (lam : ℝ) (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (Fin n) (edgeProbability lam n)

instance (lam : ℝ) (n : ℕ) : IsProbabilityMeasure (randomGraph lam n) := by
  unfold randomGraph
  infer_instance

@[simp] theorem randomGraph_one (n : ℕ) :
    randomGraph 1 n = criticalRandomGraph n := by
  simp [randomGraph, criticalRandomGraph]

/-- Real probability of a graph event at density parameter `lam`. -/
noncomputable def probability (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (randomGraph lam n).real {G | P G}

@[simp] theorem probability_one (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    probability 1 n P = criticalProbability n P := by
  simp [probability, criticalProbability]

@[simp] theorem probability_true (lam : ℝ) (n : ℕ) :
    probability lam n (fun _ ↦ True) = 1 := by
  simp [probability, measureReal_def]

@[simp] theorem probability_false (lam : ℝ) (n : ℕ) :
    probability lam n (fun _ ↦ False) = 0 := by
  simp [probability]

theorem probability_nonneg (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : 0 ≤ probability lam n P :=
  measureReal_nonneg

theorem probability_le_one (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : probability lam n P ≤ 1 :=
  measureReal_le_one

theorem probability_mono {lam : ℝ} {n : ℕ}
    {P Q : SimpleGraph (Fin n) → Prop} (h : ∀ G, P G → Q G) :
    probability lam n P ≤ probability lam n Q := by
  apply measureReal_mono (h₂ := by finiteness)
  intro G hG
  exact h G hG

theorem probability_not (lam : ℝ) (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) :
    probability lam n (fun G ↦ ¬ P G) = 1 - probability lam n P := by
  change (randomGraph lam n).real ({G | P G}ᶜ) = _
  rw [measureReal_compl (measurableSet_graphEvent _)]
  simp [probability]

theorem probability_inter_ge (lam : ℝ) (n : ℕ)
    (P Q : SimpleGraph (Fin n) → Prop) :
    probability lam n P + probability lam n Q - 1 ≤
      probability lam n (fun G ↦ P G ∧ Q G) := by
  have hadd := measureReal_union_add_inter (μ := randomGraph lam n)
    (s := {G | P G}) (t := {G | Q G}) (measurableSet_graphEvent _)
  have hle : (randomGraph lam n).real ({G | P G} ∪ {G | Q G}) ≤ 1 :=
    measureReal_le_one
  change (randomGraph lam n).real {G | P G} +
      (randomGraph lam n).real {G | Q G} - 1 ≤
    (randomGraph lam n).real ({G | P G} ∩ {G | Q G})
  linarith

theorem randomGraph_real_singleton {lam : ℝ} {n : ℕ}
    (hlam : 0 ≤ lam) (hn : 0 < n) (hlamn : lam ≤ n)
    (G : SimpleGraph (Fin n)) :
    (randomGraph lam n).real {G} =
      (lam / n) ^ G.edgeSet.ncard *
        (1 - lam / n) ^ (n.choose 2 - G.edgeSet.ncard) := by
  rw [measureReal_def, randomGraph, SimpleGraph.binomialRandom_singleton,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow]
  simp [coe_edgeProbability hlam hn hlamn]

/-- High probability in the model with fixed parameter `lam`. -/
def WithHighProbabilityAt (lam : ℝ)
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n ↦ probability lam n (P n)) atTop (𝓝 1)

@[simp] theorem withHighProbabilityAt_one
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) :
    WithHighProbabilityAt 1 P ↔ WithHighProbability P := by
  simp [WithHighProbabilityAt, WithHighProbability]

/-- The exponential decay rate in the KSS component formula. -/
noncomputable def logarithmicDecay (lam : ℝ) : ℝ := lam - 1 - Real.log lam

theorem logarithmicDecay_pos {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    0 < logarithmicDecay lam := by
  have hlog := Real.log_lt_sub_one_of_pos hlam hne
  dsimp [logarithmicDecay]
  linarith

@[simp] theorem logarithmicDecay_one : logarithmicDecay 1 = 0 := by
  simp [logarithmicDecay]

/-- The leading constant in the KSS logarithmic asymptotic. -/
noncomputable def logarithmicConstant (lam : ℝ) : ℝ := (logarithmicDecay lam)⁻¹

theorem logarithmicConstant_pos_of_ne_one {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    0 < logarithmicConstant lam :=
  inv_pos.mpr (logarithmicDecay_pos hlam hne)

theorem logarithmicConstant_pos {lam : ℝ} (hlam : 1 < lam) :
    0 < logarithmicConstant lam :=
  inv_pos.mpr (logarithmicDecay_pos (zero_lt_one.trans hlam) (ne_of_gt hlam))

/-- The sharp logarithmic upper bound asserted in the corrected problem. -/
def KSSLogarithmicStatement : Prop :=
  ∀ lam : ℝ, 1 < lam → ∀ A : ℝ, logarithmicConstant lam < A →
    WithHighProbabilityAt lam
      (fun n G ↦ secondOrder n G ≤ A * Real.log (n : ℝ))

/-- The full first-order KSS law: `L₂/log n` converges in probability to
`(lam - 1 - log lam)⁻¹`. -/
def KSSLogarithmicAsymptotic : Prop :=
  ∀ lam : ℝ, 1 < lam → ∀ ε : ℝ, 0 < ε →
    WithHighProbabilityAt lam (fun n G ↦
      |secondOrder n G / Real.log (n : ℝ) - logarithmicConstant lam| < ε)

end Erdos745
