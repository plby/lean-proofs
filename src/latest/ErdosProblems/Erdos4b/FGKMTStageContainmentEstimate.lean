/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTStageProductEstimate
import ErdosProblems.Erdos4b.FGKMTStageAvoidance

/-! # Actual one-stage containment with an explicit relative error -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def nextSurvival (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (v : α) : ℝ :=
  P v * Real.exp (-F.degree v / P v)

theorem nextSurvival_pos (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    {v : α} (hP : 0 < P v) : 0 < F.nextSurvival P v :=
  mul_pos hP (Real.exp_pos _)

theorem nextSurvival_le (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    {v : α} (hP : 0 ≤ P v) : F.nextSurvival P v ≤ P v := by
  have hexp : Real.exp (-F.degree v / P v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (F.degree_nonneg v)) hP)
  exact (mul_le_mul_of_nonneg_left hexp hP).trans_eq (mul_one _)

theorem survivalProduct_nextSurvival (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (e : Finset α) :
    survivalProduct (F.nextSurvival P) e =
      survivalProduct P e * Real.exp (-F.testSetTarget P e) := by
  simp only [survivalProduct, nextSurvival, Finset.prod_mul_distrib,
    ← Real.exp_sum, neg_div, Finset.sum_neg_distrib, testSetTarget]

theorem testSetTarget_le_card_mul (F : FiniteEdgeFamily I Ω α) {P : α → ℝ}
    (e : Finset α) {D : ℝ} (hP : ∀ v ∈ e, 0 < P v)
    (hdegree : ∀ v ∈ e, F.degree v ≤ D * P v) :
    F.testSetTarget P e ≤ (e.card : ℝ) * D := by
  calc
    _ ≤ ∑ _v ∈ e, D := Finset.sum_le_sum fun v hv =>
      (div_le_iff₀ (hP v hv)).mpr (hdegree v hv)
    _ = _ := by simp

variable {Ξ : Type*} [Fintype Ξ]

def stageNormalizerTailBound (F : FiniteEdgeFamily I Ω α) (κ b η τ : ℝ) : ℝ :=
  (3 * η + (1 + η) * (1 / κ ^ F.rank) * ((F.rank : ℝ) * b)) / τ ^ 2

theorem badNormalizerMass_from_containment (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ b η τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hb : 0 ≤ b) (hη : 0 ≤ η) (hτ : 0 < τ)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A) (i : I) :
    F.badNormalizerMass P ρ W τ i ≤ F.stageNormalizerTailBound κ b η τ := by
  apply F.badNormalizerMass_le hκ0 hκ1 hP ρ W hρ hρsum i hb hη hτ (hcap i)
  · intro w
    exact hcor (F.edge i w) (F.edge_subset i w) ((F.edge_card_le i w).trans (by omega))
  · intro w z
    have hcard := (Finset.card_union_le (F.edge i w) (F.edge i z)).trans
      (Nat.add_le_add (F.edge_card_le i w) (F.edge_card_le i z))
    have h := (abs_le.mp (hcor (F.edge i w ∪ F.edge i z)
      (Finset.union_subset (F.edge_subset i w) (F.edge_subset i z)) (by omega))).2
    linarith

variable [DecidableEq I]

def transitionContainmentMass (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (τ : ℝ) (e : Finset α) : ℝ :=
  ∑ s, ∑ ξ : I → Option Ω,
    if e ⊆ F.reweightedRemaining (W s) ξ then F.transitionMass P W τ ρ s ξ else 0

theorem transitionContainmentMass_eq_conditioned (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (ρ : Ξ → ℝ) (W : Ξ → Finset α) (τ : ℝ)
    (hP : ∀ v ∈ F.vertices, 0 < P v) (hτ : τ < 1) (e : Finset α)
    (hq : 0 < containmentMass ρ W e) :
    F.transitionContainmentMass P ρ W τ e = containmentMass ρ W e *
      ∑ s, conditionedStateMass ρ W e s * finiteMissProduct
        (fun i => (F.reweightedFamily P (W s) τ hP hτ).hitMass i e) := by
  rw [transitionContainmentMass, F.transition_containment_eq_product P ρ W τ hP hτ e,
    conditionedState_expectation]
  unfold finiteMissProduct
  field_simp

theorem transitionContainmentMass_relative_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η τ β t u b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2)
    (ht : 0 < t) (hu : 0 < u) (hbad : ∀ i, F.badNormalizerMass P ρ W τ i ≤ β)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A)
    (hcap : ∀ i, ∀ v ∈ e, F.vertexMass i v ≤ b)
    (hhit : F.testSetHitBound e κ b ≤ 1 / 2)
    (hsmall : 2 * F.testSetSquareBound e κ b + F.testSetMeanError e κ δ (t + u) ≤ 1) :
    |F.transitionContainmentMass P ρ W τ e - survivalProduct (F.nextSurvival P) e| ≤
      (η + (1 + η) * Real.exp (F.testSetTarget P e) *
        F.stageAvoidanceError P ρ W e κ δ η τ β t u b) *
          survivalProduct (F.nextSurvival P) e := by
  have he := hcor e heV (Nat.le_add_right _ _)
  have hpos : ∀ a ∈ F.vertices, 0 < P a := fun a ha => hκ0.trans_le (hP0 a ha)
  have hq := containmentMass_pos_of_relative_error (fun a ha => hpos a (heV ha))
    (lt_of_le_of_lt hη (by norm_num)) he
  have hmean := F.reweighted_miss_product_conditioned_error hκ0 hκ1 hP0 hP1 ρ W hρ hρsum
    e heV hδ hcodeg hη0 hη hτ0 hτ ht hu hbad hcor hcap hhit hsmall
  rw [F.transitionContainmentMass_eq_conditioned P ρ W τ hpos
    (hτ.trans_lt (by norm_num)) e hq, F.survivalProduct_nextSurvival]
  exact relative_mass_times_mean_error hq.le ((abs_nonneg _).trans hmean) he hmean

theorem transitionContainmentMass_error_from_containment (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η τ t u b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (ht : 0 < t) (hu : 0 < u) (hb : 0 ≤ b)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hhit : F.testSetHitBound e κ b ≤ 1 / 2)
    (hsmall : 2 * F.testSetSquareBound e κ b + F.testSetMeanError e κ δ (t + u) ≤ 1) :
    |F.transitionContainmentMass P ρ W τ e - survivalProduct (F.nextSurvival P) e| ≤
      (η + (1 + η) * Real.exp (F.testSetTarget P e) *
        F.stageAvoidanceError P ρ W e κ δ η τ (F.stageNormalizerTailBound κ b η τ) t u b) *
          survivalProduct (F.nextSurvival P) e := by
  have hbad := F.badNormalizerMass_from_containment hκ0 hκ1 hP0 ρ W hρ hρsum hb hη0 hτ0
    hcap (fun A hAV hA => hcor A hAV (by omega))
  exact F.transitionContainmentMass_relative_error hκ0 hκ1 hP0 hP1 ρ W hρ hρsum
    e heV hδ hcodeg hη0 hη hτ0.le hτ ht hu hbad hcor
    (fun i v hv => hcap i v (heV hv)) hhit hsmall

end

end Erdos4b.FGKMT.FiniteEdgeFamily
