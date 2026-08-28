import Wikipedia.HopfProblem.DegreeCollapseSupportedPhaseClock
import Wikipedia.HopfProblem.DegreeCollapseSuspensionVectorField

/-!
# The actual autonomous field of a transverse phase clock

Swap the time and transverse coordinates and conjugate complete vertical
translation by the actual clock diffeomorphism. The resulting smooth
autonomous field has zero transverse component and strictly positive time
component. Its complete integral curves are constructed explicitly.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

open FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def phaseConjugatingDiffeomorph
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) :
    Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
  ((ContinuousLinearEquiv.prodComm ℝ E ℝ).toDiffeomorph.trans D).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ E).toDiffeomorph

theorem phaseConjugatingDiffeomorph_apply
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) (p : E × ℝ) :
    phaseConjugatingDiffeomorph D p = ((D (p.2, p.1)).2, (D (p.2, p.1)).1) := rfl

/-- The exact new flow retains the transverse coordinate for all real times. -/
theorem phaseClockFlow_base
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hbase : ∀ p, (D p).2 = p.2) (p : E × ℝ) (t : ℝ) :
    (suspensionFlow (phaseConjugatingDiffeomorph D) t p).1 = p.1 := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have hh := congrArg (fun w : E × ℝ => w.1) (Q.apply_symm_apply p)
  change (D (z.2, z.1)).2 = p.1 at hh
  rw [hbase] at hh
  change (D (z.2 + t, z.1)).2 = p.1
  rw [hbase]
  exact hh

/-- The actual autonomous phase-clock field has zero transverse component. -/
theorem phaseClockField_base_zero
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hbase : ∀ p, (D p).2 = p.2) (p : E × ℝ) :
    (suspensionField (phaseConjugatingDiffeomorph D) p).1 = 0 := by
  have hd : HasDerivAt (fun t => (suspensionFlow (phaseConjugatingDiffeomorph D) t p).1)
      (suspensionField (phaseConjugatingDiffeomorph D) p).1 0 :=
    (hasDerivAt_suspensionFlow_zero (phaseConjugatingDiffeomorph D) p).fst
  have heq : (fun t => (suspensionFlow (phaseConjugatingDiffeomorph D) t p).1) =
      (fun _ => p.1) := funext (phaseClockFlow_base D hbase p)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 p.1)

/-- The time component of the new field is the actual positive clock derivative. -/
theorem phaseClockField_time_derivative
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞) (p : E × ℝ) :
    (suspensionField (phaseConjugatingDiffeomorph D) p).2 =
      fderiv ℝ (fun q => (D q).1)
        ((phaseConjugatingDiffeomorph D).symm p).swap (1, 0) := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have hd : HasDerivAt (fun t => (suspensionFlow Q t p).2) (suspensionField Q p).2 0 :=
    (hasDerivAt_suspensionFlow_zero Q p).snd
  have hD : ContDiff ℝ ∞ (fun q : ℝ × E => (D q).1) := D.contMDiff.contDiff.fst
  have hc : HasDerivAt (fun t : ℝ => (z.2 + t, z.1)) ((1 : ℝ), (0 : E)) 0 :=
    ((hasDerivAt_id 0).const_add z.2).prodMk (hasDerivAt_const 0 z.1)
  have hi := (hD.differentiable (by simp) (z.2 + 0, z.1)).hasFDerivAt.comp_hasDerivAt 0 hc
  simp only [add_zero] at hi
  change HasDerivAt (fun t => (D (z.2 + t, z.1)).1) (suspensionField Q p).2 0 at hd
  exact hd.unique hi

theorem phaseClockField_time_positive
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (hpos : ∀ q, 1 / 2 < fderiv ℝ (fun p => (D p).1) q (1, 0)) (p : E × ℝ) :
    1 / 2 < (suspensionField (phaseConjugatingDiffeomorph D) p).2 := by
  rw [phaseClockField_time_derivative]
  exact hpos _

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
