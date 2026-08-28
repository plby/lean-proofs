import Wikipedia.HopfProblem.ToricTwists
import Wikipedia.HopfProblem.CuspPuncturedDeck

/-!
# Negation and the actual corrected cusp periods

Negating the fibre coordinate negates both integral period vectors while
leaving the logarithmic base coordinate unchanged. The parameter-dependent
exponential correction is inverted, for every matrix function `C`.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspNegation

open ToricSpace CuspUniformization

theorem cuspVector_neg (v : Fin 2 → ℤ) : cuspVector (-v) = -cuspVector v := by
  ext i
  fin_cases i <;> simp [cuspVector]

theorem exponentialMultiplier_neg (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) :
    exponentialMultiplier C (-v) t = (exponentialMultiplier C v t)⁻¹ := by
  have he : (fun i => ((-v) i : ℂ)) = -(fun i => (v i : ℂ)) := by
    ext i
    simp
  ext j
  change Complex.exp (2 * Real.pi * Complex.I *
      ((C t) *ᵥ (fun i => ((-v) i : ℂ))) j) =
    (Complex.exp (2 * Real.pi * Complex.I *
      ((C t) *ᵥ (fun i => (v i : ℂ))) j))⁻¹
  rw [he, Matrix.mulVec_neg]
  simp only [Pi.neg_apply, mul_neg, Complex.exp_neg]

def logNeg (p : ℂ × ComplexPlane₂) : ℂ × ComplexPlane₂ := (p.1, -p.2)

theorem logNeg_involutive : Function.Involutive logNeg := by
  intro p
  simp only [logNeg, neg_neg]

def negateDeck (g : LogDeck) : LogDeck := ⟨g.k, -g.m, -g.n⟩

theorem logNeg_deck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (p : ℂ × ComplexPlane₂) :
    logNeg (logDeckTransform C g p) = logDeckTransform C (negateDeck g) (logNeg p) := by
  apply Prod.ext
  · rfl
  · have hm : (fun i => ((-g.m) i : ℂ)) = -(fun i => (g.m i : ℂ)) := by
      ext i
      simp
    have hn : (fun i => ((-g.n) i : ℂ)) = -(fun i => (g.n i : ℂ)) := by
      ext i
      simp
    change -(p.2 + (fun i => (g.m i : ℂ)) +
      logarithmicPeriod C p.1 *ᵥ (fun i => (g.n i : ℂ))) =
      -p.2 + (fun i => ((-g.m) i : ℂ)) +
        logarithmicPeriod C p.1 *ᵥ (fun i => ((-g.n) i : ℂ))
    rw [hm, hn, Matrix.mulVec_neg]
    abel

end Wikipedia.HopfProblem.CuspNegation
