import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homotopy.Basic

/-!
# Contractions from actual real lifts of circle maps

A continuous real lift contracts a circle-valued map by multiplying the
lift by `1 - t`. For a map to a product, the same homotopy leaves the
second coordinate fixed. These are explicit continuous homotopies with
their endpoint identities proved from the lift equation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]

/-- Scale a continuous real lift to zero in the actual additive circle. -/
def circleLiftContraction (f : C(S, AddCircle (1 : ℝ))) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = f s) :
    f.Homotopy (ContinuousMap.const S 0) where
  toFun p := (((1 - (p.1 : ℝ)) * l p.2 : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (l.continuous.comp continuous_snd))
  map_zero_left s := by simpa using hlift s
  map_one_left s := by simp

/-- The contraction is the displayed lift-scaling formula, at every time and point. -/
@[simp] theorem circleLiftContraction_apply (f : C(S, AddCircle (1 : ℝ))) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = f s) (t : unitInterval) (s : S) :
    circleLiftContraction f l hlift (t, s) =
      (((1 - (t : ℝ)) * l s : ℝ) : AddCircle (1 : ℝ)) := rfl

/-- Contract only the lifted circle coordinate of a product-valued map. -/
def circleProductLiftContraction (f : C(S, AddCircle (1 : ℝ) × X)) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = (f s).1) :
    f.Homotopy
      ⟨fun s => (0, (f s).2), continuous_const.prodMk f.continuous.snd⟩ where
  toFun p := ((((1 - (p.1 : ℝ)) * l p.2 : ℝ) : AddCircle (1 : ℝ)), (f p.2).2)
  continuous_toFun := ((AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (l.continuous.comp continuous_snd))).prodMk (f.continuous.snd.comp continuous_snd)
  map_zero_left s := by
    apply Prod.ext
    · simpa using hlift s
    · rfl
  map_one_left s := by simp

/-- Exact product formula for the genuine contraction homotopy. -/
@[simp] theorem circleProductLiftContraction_apply
    (f : C(S, AddCircle (1 : ℝ) × X)) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = (f s).1)
    (t : unitInterval) (s : S) :
    circleProductLiftContraction f l hlift (t, s) =
      ((((1 - (t : ℝ)) * l s : ℝ) : AddCircle (1 : ℝ)), (f s).2) := rfl

/-- The second coordinate remains fixed throughout the product contraction. -/
@[simp] theorem circleProductLiftContraction_snd
    (f : C(S, AddCircle (1 : ℝ) × X)) (l : C(S, ℝ))
    (hlift : ∀ s, (l s : AddCircle (1 : ℝ)) = (f s).1)
    (t : unitInterval) (s : S) :
    (circleProductLiftContraction f l hlift (t, s)).2 = (f s).2 := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology
