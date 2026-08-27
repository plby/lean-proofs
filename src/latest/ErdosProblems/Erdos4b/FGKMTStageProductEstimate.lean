/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTestSetTail
import ErdosProblems.Erdos4b.FGKMTMissProductEstimate

/-! # Explicit one-stage conditional avoidance error -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def testSetHitBound (F : FiniteEdgeFamily I Ω α) (e : Finset α) (κ b : ℝ) : ℝ :=
  2 * (1 / κ ^ F.rank) * (e.card : ℝ) * b

def testSetSquareBound (F : FiniteEdgeFamily I Ω α) (e : Finset α) (κ b : ℝ) : ℝ :=
  (Fintype.card I : ℝ) * F.testSetHitBound e κ b ^ 2

theorem testSetSquareBound_nonneg (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) (κ b : ℝ) : 0 ≤ F.testSetSquareBound e κ b := by
  unfold testSetSquareBound
  positivity

theorem reweighted_hit_square_sum_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (e : Finset α)
    (hcap : ∀ i, ∀ v ∈ e, F.vertexMass i v ≤ b) :
    let G := F.reweightedFamily P W τ (fun v hv => hκ0.trans_le (hP v hv))
      (hτ.trans_lt (by norm_num))
    (∑ i, G.hitMass i e ^ 2) ≤ F.testSetSquareBound e κ b := by
  intro G
  calc
    _ ≤ ∑ _i : I, F.testSetHitBound e κ b ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact pow_le_pow_left₀ (G.hitMass_nonneg i e)
        (F.reweightedFamily_hitMass_le_card hκ0 hκ1 hP W hτ0 hτ i e (hcap i)) 2
    _ = _ := by simp only [testSetSquareBound, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]

theorem reweighted_miss_product_good_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ δ a b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (e : Finset α) (heV : e ⊆ F.vertices)
    (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hcodeg : ∀ v ∈ e, ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ)
    (hcap : ∀ i, ∀ v ∈ e, F.vertexMass i v ≤ b)
    (hhit : F.testSetHitBound e κ b ≤ 1 / 2)
    (hsmall : 2 * F.testSetSquareBound e κ b + F.testSetMeanError e κ δ a ≤ 1)
    (hgood : ¬(F.testBadVertices P W τ e a).Nonempty) :
    let G := F.reweightedFamily P W τ (fun v hv => hκ0.trans_le (hP v hv))
      (hτ.trans_lt (by norm_num))
    |finiteMissProduct (fun i => G.hitMass i e) - Real.exp (-F.testSetTarget P e)| ≤
      4 * F.testSetSquareBound e κ b + 2 * F.testSetMeanError e κ δ a := by
  intro G
  have hh (i : I) : G.hitMass i e ≤ 1 / 2 :=
    (F.reweightedFamily_hitMass_le_card hκ0 hκ1 hP W hτ0 hτ i e (hcap i)).trans hhit
  have hsq := F.reweighted_hit_square_sum_le hκ0 hκ1 hP W hτ0 hτ e hcap
  have hmean := F.reweighted_hit_sum_error_of_good hκ0 hκ1 hP W hτ0 hτ e hδ hcodeg hgood
  have h := finiteMissProduct_target_error (fun i => G.hitMass_nonneg i e) hh
    (F.testSetTarget_nonneg e (fun v hv => (hκ0.trans_le (hP v (heV hv))).le))
    (F.testSetMeanError_nonneg e hκ0 hδ ha) hmean (by linarith)
  exact h.trans (by linarith)

variable {Ξ : Type*} [Fintype Ξ]

def stageAvoidanceError (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α) (κ δ η τ β t u b : ℝ) : ℝ :=
  4 * F.testSetSquareBound e κ b + 2 * F.testSetMeanError e κ δ (t + u) +
    F.testSetTailBudget P ρ W e κ δ η τ β t u

theorem reweighted_miss_product_conditioned_error (F : FiniteEdgeFamily I Ω α)
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
    let G (s : Ξ) := F.reweightedFamily P (W s) τ
      (fun v hv => hκ0.trans_le (hP0 v hv)) (hτ.trans_lt (by norm_num))
    |(∑ s, conditionedStateMass ρ W e s * finiteMissProduct (fun i => (G s).hitMass i e)) -
      Real.exp (-F.testSetTarget P e)| ≤ F.stageAvoidanceError P ρ W e κ δ η τ β t u b := by
  intro G
  have hq := containmentMass_pos_of_relative_error
    (fun v hv => hκ0.trans_le (hP0 v (heV hv))) (lt_of_le_of_lt hη (by norm_num))
    (hcor e heV (Nat.le_add_right _ _))
  have htarget := F.testSetTarget_nonneg e
    (fun v hv => (hκ0.trans_le (hP0 v (heV hv))).le)
  have hh (s : Ξ) (i : I) : (G s).hitMass i e ≤ 1 / 2 :=
    (F.reweightedFamily_hitMass_le_card hκ0 hκ1 hP0 (W s) hτ0 hτ i e (hcap i)).trans hhit
  have hgood := fun s => F.reweighted_miss_product_good_error
    hκ0 hκ1 hP0 (W s) hτ0 hτ e heV hδ (add_nonneg ht.le hu.le)
    (fun v hv a ha hne => hcodeg v hv a (heV ha) hne) hcap hhit hsmall
  have herr := finite_good_bad_mean_error (conditionedStateMass ρ W e)
    (fun s => finiteMissProduct (fun i => (G s).hitMass i e))
    (conditionedStateMass_nonneg hρ hq) (conditionedStateMass_sum_one hq)
    (fun s => (F.testBadVertices P (W s) τ e (t + u)).Nonempty)
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
    (add_nonneg (mul_nonneg (by norm_num) (F.testSetSquareBound_nonneg e κ b))
      (mul_nonneg (by norm_num) (F.testSetMeanError_nonneg e hκ0 hδ (add_nonneg ht.le hu.le))))
    (fun s => (finiteMissProduct_pos (hh s)).le)
    (fun s => finiteMissProduct_le_one (fun i => (G s).hitMass_nonneg i e) (hh s)) hgood
  have htail := F.testBadVertices_conditioned_tail hκ0 hκ1 hP0 hP1 ρ W hρ hρsum
    e heV hδ hcodeg hη0 hη hτ0 hτ ht hu hbad hcor
  exact herr.trans (add_le_add le_rfl htail)

end

end Erdos4b.FGKMT.FiniteEdgeFamily
