/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTStageContainmentEstimate

/-! # Scalar envelopes for the actual one-stage error -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def stageFirstEnvelope (F : FiniteEdgeFamily I Ω α) (e : Finset α) (κ δ : ℝ) : ℝ :=
  (1 / κ) * (1 / κ ^ F.rank) * ((e.card : ℝ) * δ)

def stageSecondEnvelope (F : FiniteEdgeFamily I Ω α) (e : Finset α) (κ δ D : ℝ) : ℝ :=
  (1 / κ ^ 2) * (1 / κ ^ (2 * F.rank)) * ((2 * (e.card : ℝ) + F.rank) * δ * D)

def stageVarianceEnvelope (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    (κ δ η D : ℝ) : ℝ :=
  4 * η * D ^ 2 + (1 + 4 * η) * F.stageSecondEnvelope e κ δ D +
    2 * D * (4 * η * (D + F.stageFirstEnvelope e κ δ) + F.stageFirstEnvelope e κ δ)

def stageTailEnvelope (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    (κ δ η τ β t u D : ℝ) : ℝ :=
  (e.card : ℝ) * (F.stageVarianceEnvelope e κ δ η D / t ^ 2 +
    2 * (β + 2 * τ) * (1 / κ ^ F.rank) * (1 / κ ^ e.card) * D / u)

theorem vertexFirstError_le_envelope (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (e : Finset α) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (v : α) (hP : κ ≤ P v) :
    0 ≤ F.vertexFirstError P e κ δ v ∧
      F.vertexFirstError P e κ δ v ≤ F.stageFirstEnvelope e κ δ := by
  have hp := hκ.trans_le hP
  constructor
  · unfold vertexFirstError
    positivity
  · unfold vertexFirstError stageFirstEnvelope
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hκ hP) (by positivity))
      (by positivity)

theorem vertexSecondError_le_envelope (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (e : Finset α) {κ δ D : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hD : 0 ≤ D) (v : α) (hP0 : κ ≤ P v) (hP1 : P v ≤ 1)
    (hdegree : F.degree v ≤ D * P v) :
    0 ≤ F.vertexSecondError P e κ δ v ∧
      F.vertexSecondError P e κ δ v ≤ F.stageSecondEnvelope e κ δ D := by
  have hp := hκ.trans_le hP0
  have hd0 := F.degree_nonneg v
  have hd : F.degree v ≤ D := hdegree.trans (by nlinarith)
  constructor
  · unfold vertexSecondError
    positivity
  · unfold vertexSecondError stageSecondEnvelope
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (one_div_le_one_div_of_le (pow_pos hκ 2) (pow_le_pow_left₀ hκ.le hP0 2))
        (by positivity)
    · exact mul_le_mul_of_nonneg_left hd (by positivity)
    · positivity
    · positivity

theorem vertexVarianceError_le_envelope (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (e : Finset α) {κ δ η D : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hD : 0 ≤ D) (v : α) (hP0 : κ ≤ P v) (hP1 : P v ≤ 1)
    (hdegree : F.degree v ≤ D * P v) :
    F.vertexVarianceError P e κ δ η v ≤ F.stageVarianceEnvelope e κ δ η D := by
  have hp := hκ.trans_le hP0
  have hs0 : 0 ≤ F.degree v / P v := div_nonneg (F.degree_nonneg v) hp.le
  have hs : F.degree v / P v ≤ D := (div_le_iff₀ hp).mpr hdegree
  have hL1 := F.vertexFirstError_le_envelope e hκ hδ v hP0
  have hL2 := F.vertexSecondError_le_envelope e hκ hδ hD v hP0 hP1 hdegree
  have hE0 : 0 ≤ F.vertexMeanError P e κ δ η v := by
    unfold vertexMeanError
    exact add_nonneg (mul_nonneg (by positivity) (add_nonneg hs0 hL1.1)) hL1.1
  have hE : F.vertexMeanError P e κ δ η v ≤
      4 * η * (D + F.stageFirstEnvelope e κ δ) + F.stageFirstEnvelope e κ δ := by
    exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hs hL1.2) (by positivity)) hL1.2
  unfold vertexVarianceError stageVarianceEnvelope
  apply add_le_add
  · exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hs 2) (by positivity))
      (mul_le_mul_of_nonneg_left hL2.2 (by positivity))
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hE hE0 (by positivity)

theorem testSetSquareBound_sqrt (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    (κ δ : ℝ) (hI : 0 < Fintype.card I) :
    F.testSetSquareBound e κ (δ / Real.sqrt (Fintype.card I)) =
      4 * (1 / κ ^ (2 * F.rank)) * (e.card : ℝ) ^ 2 * δ ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  have hsq := Real.sq_sqrt hn.le
  have hroot : Real.sqrt (Fintype.card I) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  unfold testSetSquareBound testSetHitBound
  rw [show 2 * F.rank = F.rank * 2 by omega, pow_mul]
  field_simp
  rw [hsq]
  ring

variable {Ξ : Type*} [Fintype Ξ]

theorem containmentMass_ge_half_pow {P : α → ℝ} {ρ : Ξ → ℝ}
    {W : Ξ → Finset α} (e : Finset α) {κ η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ e, κ ≤ P v) (hη : η ≤ 1 / 2)
    (hcor : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e) :
    κ ^ e.card / 2 ≤ containmentMass ρ W e := by
  have hprod := survivalProduct_ge_pow hκ0.le hκ1 hP (Nat.le_refl e.card)
  have hpos := (survivalProduct_pos (fun v hv => hκ0.trans_le (hP v hv))).le
  have hsmall := mul_le_mul_of_nonneg_right hη hpos
  linarith [(abs_le.mp hcor).1]

theorem testSetTailBudget_le_envelope (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α)
    {κ δ η τ β t u D : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ : 0 ≤ τ) (hβ : 0 ≤ β)
    (hu : 0 < u) (hD : 0 ≤ D) (hP0 : ∀ v ∈ e, κ ≤ P v)
    (hP1 : ∀ v ∈ e, P v ≤ 1) (hdegree : ∀ v ∈ e, F.degree v ≤ D * P v)
    (hcor : |containmentMass ρ W e - survivalProduct P e| ≤ η * survivalProduct P e) :
    F.testSetTailBudget P ρ W e κ δ η τ β t u ≤
      F.stageTailEnvelope e κ δ η τ β t u D := by
  have hq := containmentMass_ge_half_pow e hκ0 hκ1 hP0 hη hcor
  have hqpos : 0 < containmentMass ρ W e :=
    (by positivity : 0 < κ ^ e.card / 2).trans_le hq
  have hqu : 0 < κ ^ e.card / 2 * u := mul_pos (by positivity) hu
  calc
    _ ≤ ∑ _v ∈ e, (F.stageVarianceEnvelope e κ δ η D / t ^ 2 +
        2 * (β + 2 * τ) * (1 / κ ^ F.rank) * (1 / κ ^ e.card) * D / u) := by
      apply Finset.sum_le_sum
      intro v hv
      apply add_le_add
      · exact div_le_div_of_nonneg_right
          (F.vertexVarianceError_le_envelope e hκ0 hδ hη0 hD v
            (hP0 v hv) (hP1 v hv) (hdegree v hv)) (sq_nonneg t)
      · have hd : F.degree v ≤ D := (hdegree v hv).trans (by nlinarith [hP1 v hv])
        calc
          _ ≤ ((β + 2 * τ) * ((1 / κ ^ F.rank) * D)) / (containmentMass ρ W e * u) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity))
              (mul_nonneg (by positivity) hu.le)
          _ ≤ ((β + 2 * τ) * ((1 / κ ^ F.rank) * D)) / (κ ^ e.card / 2 * u) :=
            div_le_div_of_nonneg_left (by positivity) hqu (mul_le_mul_of_nonneg_right hq hu.le)
          _ = _ := by field_simp
    _ = _ := by simp only [stageTailEnvelope, Finset.sum_const, nsmul_eq_mul]

def stageErrorEnvelope (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    (κ δ η τ β t u b D : ℝ) : ℝ :=
  4 * F.testSetSquareBound e κ b + 2 * F.testSetMeanError e κ δ (t + u) +
    F.stageTailEnvelope e κ δ η τ β t u D

theorem stageErrorEnvelope_nonneg (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    {κ δ η τ β t u b D : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hτ : 0 ≤ τ) (hβ : 0 ≤ β) (ht : 0 ≤ t) (hu : 0 ≤ u) (hD : 0 ≤ D) :
    0 ≤ F.stageErrorEnvelope e κ δ η τ β t u b D := by
  unfold stageErrorEnvelope stageTailEnvelope stageVarianceEnvelope
    stageFirstEnvelope stageSecondEnvelope testSetMeanError testSetSquareBound
  positivity

variable [DecidableEq I]

theorem transitionContainmentMass_scalar_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η τ t u b D : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (ht : 0 < t) (hu : 0 < u) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hdegree : ∀ v ∈ e, F.degree v ≤ D * P v)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ b)
    (hhit : F.testSetHitBound e κ b ≤ 1 / 2)
    (hsmall : 2 * F.testSetSquareBound e κ b + F.testSetMeanError e κ δ (t + u) ≤ 1) :
    |F.transitionContainmentMass P ρ W τ e - survivalProduct (F.nextSurvival P) e| ≤
      (η + (1 + η) * Real.exp ((e.card : ℝ) * D) *
        F.stageErrorEnvelope e κ δ η τ (F.stageNormalizerTailBound κ b η τ) t u b D) *
          survivalProduct (F.nextSurvival P) e := by
  let β := F.stageNormalizerTailBound κ b η τ
  have hβ : 0 ≤ β := by dsimp [β, stageNormalizerTailBound]; positivity
  have hfirst := F.transitionContainmentMass_error_from_containment hκ0 hκ1 hP0 hP1
    ρ W hρ hρsum e heV hδ hcodeg hη0 hη hτ0 hτ ht hu hb hcor hcap hhit hsmall
  have hE : F.stageAvoidanceError P ρ W e κ δ η τ β t u b ≤
      F.stageErrorEnvelope e κ δ η τ β t u b D :=
    add_le_add le_rfl (F.testSetTailBudget_le_envelope ρ W e hκ0 hκ1 hδ hη0 hη hτ0.le hβ
      hu hD (fun v hv => hP0 v (heV hv)) (fun v hv => hP1 v (heV hv)) hdegree
      (hcor e heV (Nat.le_add_right _ _)))
  have htarget := F.testSetTarget_le_card_mul e
    (fun v hv => hκ0.trans_le (hP0 v (heV hv))) hdegree
  have hE0 := F.stageErrorEnvelope_nonneg e hκ0 hδ hη0 hτ0.le hβ ht.le hu.le hD (b := b)
  have hprod : 0 ≤ survivalProduct (F.nextSurvival P) e :=
    (survivalProduct_pos (fun v hv => F.nextSurvival_pos
      (hκ0.trans_le (hP0 v (heV hv))))).le
  refine hfirst.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl ?_) hprod)
  calc
    _ ≤ (1 + η) * Real.exp (F.testSetTarget P e) *
        F.stageErrorEnvelope e κ δ η τ β t u b D :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htarget) (by positivity)) hE0

end

end Erdos4b.FGKMT.FiniteEdgeFamily
