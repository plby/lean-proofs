import ErdosProblems.Erdos1148.ReturningGaussWidth
import ErdosProblems.Erdos1148.GaussBoxVectorCandidates

/-! # Returning-vector classes inside a bounded Gauss coordinate box -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def BoundedGaussParameters :=
  {p : ℝ × ℝ × ℝ // |p.1| ≤ 1 ∧ |p.2.1| ≤ 1 ∧ 1 / 2 ≤ p.2.2 ∧ p.2.2 ≤ 2}

noncomputable def gaussParameterFrame (g : SL(2, ℝ)) (p : BoundedGaussParameters) : SL(2, ℝ) :=
  g * unstableHorocycle p.val.1 * upperTriangularFrame p.val.2.1 p.val.2.2
    (by have := p.property.2.2.1; linarith)

def GaussVectorReturns (g : SL(2, ℝ)) (S c : ℝ) (q : ℤ × ℤ) (p : BoundedGaussParameters) : Prop :=
  c ≤ modularVectorLengthSq (gaussParameterFrame g p) q.1 q.2 ∧
    modularVectorLengthSq (gaussParameterFrame g p) q.1 q.2 ≤ 1 ∧
      modularVectorLengthSq ((gaussParameterFrame g p) * diagonalFlow S) q.1 q.2 ≤ 1

def ReturningGaussParameters (g : SL(2, ℝ)) (S c : ℝ) : Set BoundedGaussParameters :=
  {p | ∃ q : ℤ × ℤ, GaussVectorReturns g S c q p}

theorem returningGauss_parameter_diameter (g : SL(2, ℝ)) {S c : ℝ} (hc : 0 < c)
    (hsmall : 96 * Real.exp (-S) ≤ c) (q : ℤ × ℤ) {p p' : BoundedGaussParameters}
    (hp : GaussVectorReturns g S c q p) (hp' : GaussVectorReturns g S c q p') :
    |p.val.1 - p'.val.1| ≤ (16 / Real.sqrt c) * Real.exp (-(S / 2)) := by
  exact returning_gauss_width_le g p.val.1 p'.val.1 p.val.2.1 p'.val.2.1 p.val.2.2 p'.val.2.2 S c
    p.property.2.1 p.property.2.2.1 p.property.2.2.2 p'.property.2.2.1 hc q.1 q.2
    hp.1 hp.2.2 hp'.2.2 hsmall

theorem exists_uniform_returningGauss_candidates {A : ℝ} (hA : 0 ≤ A) :
    ∃ V : Finset (ℤ × ℤ), ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ (S c : ℝ) (p : BoundedGaussParameters) (q : ℤ × ℤ),
        GaussVectorReturns g S c q p → q ∈ V := by
  obtain ⟨V, hV⟩ := exists_gaussBox_vector_candidates hA
  refine ⟨V, ?_⟩
  intro g hg S c p q hp
  exact hV g hg p.val.1 p.val.2.1 p.val.2.2 p.property.1 p.property.2.1
    p.property.2.2.1 p.property.2.2.2 q.1 q.2 hp.2.1

end Erdos1148.DukeArithmetic
