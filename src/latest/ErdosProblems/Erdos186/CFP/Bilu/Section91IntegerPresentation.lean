/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section90IntegerInitialization
import ErdosProblems.Erdos186.CFP.Bilu.Section91InitialCoordinates
import ErdosProblems.Erdos186.CFP.Bilu.Section92ShortKernel

/-!
# The Section 9.1 presentation as an integer-valued map

For the original source set `A ⊂ ℤ`, Section 9 starts in dimension one
with `Section90IntegerInitialization.integerSet A`.  Evaluating the unique
coordinate turns the standard-coordinate Section 9.1 presentation into an
additive map to `ℤ`.  Every element of `A` has a literal lift, and the map
is therefore ready for the short primitive-kernel construction.
-/

namespace Erdos186.CFP.Bilu.Section91IntegerPresentation

open Proposition75Data Section9NormalizedReplacement
open Section90IntegerInitialization Section91InitialCoordinates
open Section91InitialCoordinates.InitialPresentation
open Section91InitialPresentation.InitialPresentation
open Section92ShortKernel

noncomputable section

/-- Evaluation of a one-dimensional integral point at its unique
coordinate. -/
def singletonValue : Mahler.IntegralPoint 1 →+ ℤ where
  toFun z := z 0
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem singletonValue_singletonPoint (x : ℤ) :
    singletonValue (singletonPoint x) = x := rfl

variable {r : ℕ} {B : Set (EuclideanSpace ℝ (Fin 1))}
  {a : Fin r → EuclideanSpace ℝ (Fin 1)}
  {D : GeometricData B a}
  {A : Finset ℤ} {coverConstant sigma : ℕ}
  {constant scale : ENNReal}

namespace InitialPresentation

variable (N : CoveredNormalizedReplacement (D := D)
  (K := integerSet A) (coverConstant := coverConstant)
  constant scale sigma)

/-- The standard-coordinate Section 9.1 presentation, evaluated in its
unique target coordinate. -/
noncomputable def integerPresentationMap :
    Mahler.IntegralPoint (initialRank N) →+ ℤ :=
  singletonValue.comp (coordinatePresentationMap N)

@[simp] theorem integerPresentationMap_apply
    (q : Mahler.IntegralPoint (initialRank N)) :
    integerPresentationMap N q = coordinatePresentationMap N q 0 :=
  rfl

/-- Every original integer has a lift through the standard-coordinate
presentation. -/
theorem exists_integerLift (x : ℤ) (hx : x ∈ A) :
    ∃ q : Mahler.IntegralPoint (initialRank N),
      integerPresentationMap N q = x := by
  have hxK : singletonPoint x ∈ integerSet A :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨q, hq⟩ := exists_coordinateLift N (singletonPoint x) hxK
  refine ⟨q, ?_⟩
  rw [integerPresentationMap_apply, hq]
  rfl

/-- The image of the integer-valued presentation contains `A`. -/
theorem subset_range_integerPresentationMap :
    (A : Set ℤ) ⊆ Set.range (integerPresentationMap N) := by
  intro x hx
  exact exists_integerLift N x hx

/-- Failure of bounded injectivity for the actual integer-valued Section
9.1 map produces the complete primitive quotient step of Section 9.2. -/
theorem exists_primitiveKernelStep_of_not_injOn
    (p : Seminorm ℝ (Fin (initialRank N) → ℝ)) (T : ℝ)
    (hbad : ¬ Set.InjOn (integerPresentationMap N)
      {z : Mahler.IntegralPoint (initialRank N) |
        p (Mahler.integralEmbed z) ≤ T}) :
    Nonempty (PrimitiveKernelStep p (integerPresentationMap N) T) :=
  exists_primitiveKernelStep_of_not_injOn_ball p
    (integerPresentationMap N) T hbad

/-- The standard source rank has the Section 9.1 bound required for all
subsequent rank-decreasing quotient steps. -/
theorem integerPresentationRank_le :
    initialRank N ≤ (1 + r - 1) + sigma * coverConstant :=
  coordinateRank_le N

end InitialPresentation

end

end Erdos186.CFP.Bilu.Section91IntegerPresentation

#print axioms Erdos186.CFP.Bilu.Section91IntegerPresentation.InitialPresentation.exists_integerLift
#print axioms Erdos186.CFP.Bilu.Section91IntegerPresentation.InitialPresentation.subset_range_integerPresentationMap
#print axioms Erdos186.CFP.Bilu.Section91IntegerPresentation.InitialPresentation.exists_primitiveKernelStep_of_not_injOn
