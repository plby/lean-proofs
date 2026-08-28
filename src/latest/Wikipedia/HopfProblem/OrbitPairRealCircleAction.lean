import Wikipedia.HopfProblem.OrbitPairFreeLocus

/-!
# The original circle action and character in smooth real time

These definitions retain the original complex flow and the original
normalized exponential. Only the time parameter and differentiability
field are restricted to the real numbers; the threefold atlas is unchanged.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization
open VerticalAction.Exponential

attribute [local instance] Threefold.chartedSpace

local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

def realCircleAction (t : ℝ) (x : Threefold.Space) : Threefold.Space :=
  VerticalAction.flow (t : ℂ) x

@[simp] theorem realCircleAction_eq (t : ℝ) (x : Threefold.Space) :
    realCircleAction t x = Homology.DeltaSweep.actionMap ((t : AddCircle (1 : ℝ)), x) :=
  (Homology.DeltaSweep.actionMap_real t x).symm

theorem realCircleAction_add (s t : ℝ) (x : Threefold.Space) :
    realCircleAction (s + t) x = realCircleAction s (realCircleAction t x) := by
  simp only [realCircleAction, Complex.ofReal_add, VerticalAction.flow_add]

theorem realCircleAction_periodic (t : ℝ) (x : Threefold.Space) :
    realCircleAction (t + 1) x = realCircleAction t x := by
  rw [realCircleAction_add]
  change VerticalAction.flow (t : ℂ) (VerticalAction.flow (1 : ℂ) x) =
    VerticalAction.flow (t : ℂ) x
  rw [← Int.cast_one, VerticalAction.flow_int_cast]

theorem realCircleAction_smooth :
    ContMDiff ((𝓘(ℝ)).prod IX) IX ∞
      (fun p : ℝ × Threefold.Space => realCircleAction p.1 p.2) := by
  have hr : ContMDiff ((IX).prod 𝓘(ℝ, ℂ)) IX ∞
      (fun p : Threefold.Space × ℂ => VerticalAction.flow p.2 p.1) := by
    intro p
    have hc := (VerticalAction.jointFlow_holomorphic.of_le
      (show (∞ : ℕ∞ω) ≤ ω by simp)) p
    obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp hc
    exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  exact hr.comp (contMDiff_snd.prodMk (Complex.ofRealCLM.contDiff.contMDiff.comp contMDiff_fst))

/-- The original unit complex character, without rescaling the period. -/
def realCircleCharacter (t : ℝ) : ℂ := normalizedExponential (t : ℂ)

@[simp] theorem realCircleCharacter_eq (t : ℝ) :
    realCircleCharacter t = (Homology.DeltaSweep.circleParameter
      (t : AddCircle (1 : ℝ)) : ℂ) := rfl

theorem realCircleCharacter_unit (t : ℝ) : ‖realCircleCharacter t‖ = 1 :=
  VerticalAction.FixedCoordinates.CircleOrbit.normalizedExponential_real_norm t

theorem realCircleCharacter_ne_zero (t : ℝ) : realCircleCharacter t ≠ 0 :=
  (normalizedExponential (t : ℂ)).ne_zero

theorem realCircleCharacter_add (s t : ℝ) :
    realCircleCharacter (s + t) = realCircleCharacter s * realCircleCharacter t := by
  simp only [realCircleCharacter, Complex.ofReal_add, normalizedExponential_add, Units.val_mul]

theorem realCircleCharacter_periodic (t : ℝ) :
    realCircleCharacter (t + 1) = realCircleCharacter t := by
  rw [realCircleCharacter_add]
  have h : realCircleCharacter 1 = 1 := by
    change (normalizedExponential (1 : ℂ) : ℂ) = 1
    simpa only [Int.cast_one, Units.val_one] using
      congrArg (fun u : ℂˣ => (u : ℂ)) (normalizedExponential_int (1 : ℤ))
  rw [h, mul_one]

theorem realCircleCharacter_smooth : ContDiff ℝ ∞ realCircleCharacter :=
  ((CuspUniformization.exponential_holomorphic.of_le (by simp)).restrict_scalars ℝ).comp
    Complex.ofRealCLM.contDiff

end Wikipedia.HopfProblem.OrbitPair
