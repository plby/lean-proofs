/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteGoodBad
import ErdosProblems.Erdos4b.FGKMTReweightedVertexTail
import ErdosProblems.Erdos4b.FGKMTReweightedHitBounds

/-! # Simultaneous vertex control and test-set hit-sum approximation -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def testSetTarget (F : FiniteEdgeFamily I Ω α) (P : α → ℝ) (e : Finset α) : ℝ :=
  ∑ v ∈ e, F.degree v / P v

def testSetMeanError (F : FiniteEdgeFamily I Ω α) (e : Finset α) (κ δ a : ℝ) : ℝ :=
  (e.card : ℝ) * a + 2 * (1 / κ ^ F.rank) * (e.card : ℝ) ^ 2 * δ

def testBadVertices (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Finset α) (τ : ℝ) (e : Finset α) (a : ℝ) : Finset α :=
  e.filter fun v => a ≤ |F.reweightedVertexDegree P W τ v - F.degree v / P v|

theorem testSetTarget_nonneg (F : FiniteEdgeFamily I Ω α) {P : α → ℝ} (e : Finset α)
    (hP : ∀ v ∈ e, 0 ≤ P v) : 0 ≤ F.testSetTarget P e :=
  Finset.sum_nonneg fun v hv => div_nonneg (F.degree_nonneg v) (hP v hv)

theorem testSetMeanError_nonneg (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    {κ δ a : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) (ha : 0 ≤ a) :
    0 ≤ F.testSetMeanError e κ δ a := by unfold testSetMeanError; positivity

theorem testBadVertices_empty (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Finset α) (τ a : ℝ) : F.testBadVertices P W τ ∅ a = ∅ := by
  simp only [testBadVertices, Finset.filter_empty]

theorem reweighted_hit_sum_error_of_good (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ δ a : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (e : Finset α) (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ)
    (hgood : ¬(F.testBadVertices P W τ e a).Nonempty) :
    let G := F.reweightedFamily P W τ (fun v hv => hκ0.trans_le (hP v hv))
      (hτ.trans_lt (by norm_num))
    |(∑ i, G.hitMass i e) - F.testSetTarget P e| ≤ F.testSetMeanError e κ δ a := by
  intro G
  have hvertex (v : α) (hv : v ∈ e) : |G.degree v - F.degree v / P v| ≤ a := by
    rw [← F.reweightedVertexDegree_eq_degree]
    apply le_of_lt (lt_of_not_ge ?_)
    intro hbad
    exact hgood ⟨v, Finset.mem_filter.mpr ⟨hv, hbad⟩⟩
  have hsum : |(∑ v ∈ e, G.degree v) - F.testSetTarget P e| ≤ (e.card : ℝ) * a := by
    rw [testSetTarget, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ v ∈ e, |G.degree v - F.degree v / P v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ e, a := Finset.sum_le_sum hvertex
      _ = _ := by simp
  have hhit := F.reweightedFamily_sum_hitMass_error hκ0 hκ1 hP W hτ0 hτ e hδ hcodeg
  have htri := abs_sub_le (∑ i, G.hitMass i e) (∑ v ∈ e, G.degree v) (F.testSetTarget P e)
  exact htri.trans (by dsimp [testSetMeanError]; linarith)

variable {Ξ : Type*} [Fintype Ξ]

def testSetTailBudget (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (e : Finset α) (κ δ η τ β t u : ℝ) : ℝ :=
  ∑ v ∈ e, (F.vertexVarianceError P e κ δ η v / t ^ 2 +
    ((β + 2 * τ) * ((1 / κ ^ F.rank) * F.degree v)) / (containmentMass ρ W e * u))

theorem testBadVertices_mass_le (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (ρ : Ξ → ℝ) (W : Ξ → Finset α) (τ : ℝ) (e : Finset α) (a : ℝ)
    (hρ : ∀ s, 0 ≤ ρ s) (hq : 0 < containmentMass ρ W e) :
    (∑ s, if (F.testBadVertices P (W s) τ e a).Nonempty
      then conditionedStateMass ρ W e s else 0) ≤
      ∑ v ∈ e, ∑ s,
        if a ≤ |F.reweightedVertexDegree P (W s) τ v - F.degree v / P v|
          then conditionedStateMass ρ W e s else 0 := by
  simp only [testBadVertices, Finset.filter_nonempty_iff]
  exact finite_event_union_mass_le (conditionedStateMass ρ W e)
    (conditionedStateMass_nonneg hρ hq) e
    (fun v s => a ≤ |F.reweightedVertexDegree P (W s) τ v - F.degree v / P v|)

theorem testBadVertices_conditioned_tail (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η τ β t u : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2)
    (ht : 0 < t) (hu : 0 < u) (hbad : ∀ i, F.badNormalizerMass P ρ W τ i ≤ β)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A) :
    (∑ s, if (F.testBadVertices P (W s) τ e (t + u)).Nonempty
      then conditionedStateMass ρ W e s else 0) ≤
      F.testSetTailBudget P ρ W e κ δ η τ β t u := by
  have he := hcor e heV (Nat.le_add_right _ _)
  have hq := containmentMass_pos_of_relative_error
    (fun a ha => hκ0.trans_le (hP0 a (heV ha))) (lt_of_le_of_lt hη (by norm_num)) he
  refine (F.testBadVertices_mass_le P ρ W τ e (t + u) hρ hq).trans ?_
  apply Finset.sum_le_sum
  intro v hv
  exact F.reweightedVertexDegree_conditioned_tail hκ0 hκ1 hP0 hP1 ρ W hρ hρsum
    e heV v hv hδ (hcodeg v hv) hη0 hη hτ0 hτ ht hu hbad hcor

end

end Erdos4b.FGKMT.FiniteEdgeFamily
