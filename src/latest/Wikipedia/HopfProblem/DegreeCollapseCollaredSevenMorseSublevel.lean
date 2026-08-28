import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenExcellentMorse
import Wikipedia.HopfProblem.DegreeCollapseRegularMorseSublevelCells
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseIndexNegation

/-!
# The literal collared half is an actual regular excellent Morse sublevel

Negating the constructed excellent time turns its nonnegative half into
the regular zero sublevel of a genuine excellent Morse function on the
unchanged closed ambient manifold. The identification is the identity on
ambient points. The original half therefore has a finite homotopy cell
construction in dimensions at most seven. Its original smooth atlas and
boundary framing remain the already constructed ones; no disk is inferred.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

variable (P : S.ExcellentMorsePresentation)

def sublevelFunction : C(S.Space, ℝ) := -P.function

theorem sublevelFunction_smooth : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ P.sublevelFunction :=
  P.smooth.neg

theorem sublevelFunction_morse : IsMorse (Vector 7) P.sublevelFunction :=
  MorseCancellation.isMorse_neg P.morse

theorem sublevelFunction_distinct :
    InjOn P.sublevelFunction (criticalPoints (Vector 7) P.sublevelFunction) := by
  change InjOn (fun p ↦ -P.function p) (criticalPoints (Vector 7) (fun p ↦ -P.function p))
  rw [criticalPoints_neg]
  intro p hp q hq he
  exact P.distinct hp hq (neg_injective he)

theorem sublevelFunction_regular : ∀ p, P.sublevelFunction p = 0 →
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) P.sublevelFunction p) := by
  intro p hp
  have hp' : P.function p = 0 := neg_eq_zero.mp hp
  change Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (-(P.function : S.Space → ℝ)) p)
  rw [mfderiv_neg]
  exact neg_surjective.comp (P.regular p hp')

def halfSublevelHomeomorph : S.Half ≃ₜ {p : S.Space // P.sublevelFunction p ≤ 0} where
  toFun p := ⟨p.val, neg_nonpos.mpr ((P.nonnegative_iff p.val).mpr p.property)⟩
  invFun p := ⟨p.val, (P.nonnegative_iff p.val).mp (neg_nonpos.mp p.property)⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

theorem halfSublevelHomeomorph_point (p : S.Half) :
    (P.halfSublevelHomeomorph p).val = p.val := rfl

include P in
theorem built_half : FiniteCells.Built 7 S.Half := by
  have hb := MorseCells.built_regular_sublevel P.sublevelFunction_smooth P.sublevelFunction_morse
    P.sublevelFunction_distinct 0 (by
      intro p hp hz
      exact RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular p hz hp)
  have hd : Module.finrank ℝ (Vector 7) = 7 := by simp
  rw [hd] at hb
  exact FiniteCells.Built.equiv P.halfSublevelHomeomorph.symm.toHomotopyEquiv hb

end ExcellentMorsePresentation

theorem half_finiteCells (S : CollaredSevenState B) : FiniteCells.Built 7 S.Half :=
  S.excellentMorsePresentation.built_half

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
