import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductDefinition
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginProduct

/-!
# The actual positive-circle sweep on singular homology

A continuous circle-parametrized self-map gives a degree-one homology
operation by first crossing with the original positive quotient loop and
then applying its actual singular-homology map. Naturality follows from
the proved chain-level cross-product naturality and equality of the actual
continuous maps. For translations in a topological additive group, this
is exactly the Pontryagin product with the image of that positive loop.

The circle is `AddCircle (1 : ℝ)` throughout and is always the first
cross-product factor. No homology vanishing or action law is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

local notation "Circle" => CircleTopology.Circle

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The sweep is the actual induced map after the actual cross product
with the positively oriented circle, with that circle placed first. -/
def sweep (a : C(Circle × X, X)) (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] SingularHomology X (n + 1) :=
  (singularHomologyMap a (n + 1)).comp (positiveCircleCross X n)

@[simp] theorem sweep_apply (a : C(Circle × X, X)) (n : ℕ)
    (v : SingularHomology X n) :
    sweep a n v = singularHomologyMap a (n + 1) (positiveCircleCross X n v) := rfl

/-- Naturality of the positive-circle factor, proved directly from
the actual bilinear singular-homology cross-product naturality. -/
theorem positiveCircleCross_natural (f : C(X, Y)) (n : ℕ)
    (v : SingularHomology X n) :
    singularHomologyMap ((ContinuousMap.id Circle).prodMap f) (n + 1)
        (positiveCircleCross X n v) =
      positiveCircleCross Y n (singularHomologyMap f n v) := by
  have h := crossProductHomology_natural (ContinuousMap.id Circle) f n
    (loopHomologyClass CirclePaths.positiveLoop) v
  change singularHomologyMap ((ContinuousMap.id Circle).prodMap f) (n + 1)
      (positiveCircleCross X n v) =
    crossProductHomology Circle Y n
      (singularHomologyMap (ContinuousMap.id Circle) 1
        (loopHomologyClass CirclePaths.positiveLoop))
      (singularHomologyMap f n v) at h
  simpa only [positiveCircleCross, singularHomologyMap_id, LinearMap.id_apply] using h

/-- An equality of the actual equivariant continuous-map square gives
naturality of the sweep on the actual singular homology groups. -/
theorem sweep_natural (aX : C(Circle × X, X)) (aY : C(Circle × Y, Y))
    (f : C(X, Y))
    (h : aY.comp ((ContinuousMap.id Circle).prodMap f) = f.comp aX)
    (n : ℕ) (v : SingularHomology X n) :
    sweep aY n (singularHomologyMap f n v) =
      singularHomologyMap f (n + 1) (sweep aX n v) := by
  calc
    _ = singularHomologyMap aY (n + 1)
        (singularHomologyMap ((ContinuousMap.id Circle).prodMap f) (n + 1)
          (positiveCircleCross X n v)) := by
      rw [sweep_apply, positiveCircleCross_natural]
    _ = singularHomologyMap (aY.comp ((ContinuousMap.id Circle).prodMap f)) (n + 1)
        (positiveCircleCross X n v) := by
      rw [singularHomologyMap_comp, LinearMap.comp_apply]
    _ = singularHomologyMap (f.comp aX) (n + 1) (positiveCircleCross X n v) := by rw [h]
    _ = _ := by rw [singularHomologyMap_comp, LinearMap.comp_apply, sweep_apply]

/-- The same naturality identity as equality of integral linear maps. -/
theorem sweep_natural_linearMap (aX : C(Circle × X, X)) (aY : C(Circle × Y, Y))
    (f : C(X, Y))
    (h : aY.comp ((ContinuousMap.id Circle).prodMap f) = f.comp aX) (n : ℕ) :
    (sweep aY n).comp (singularHomologyMap f n) =
      (singularHomologyMap f (n + 1)).comp (sweep aX n) := by
  apply LinearMap.ext
  intro v
  exact sweep_natural aX aY f h n v

/-- Pointwise equivariance supplies the literal map equality required
by sweep naturality. -/
theorem sweep_natural_of_equivariant (aX : C(Circle × X, X)) (aY : C(Circle × Y, Y))
    (f : C(X, Y)) (h : ∀ t x, aY (t, f x) = f (aX (t, x)))
    (n : ℕ) (v : SingularHomology X n) :
    sweep aY n (singularHomologyMap f n v) =
      singularHomologyMap f (n + 1) (sweep aX n v) := by
  apply sweep_natural aX aY f ?_ n v
  apply ContinuousMap.ext
  intro p
  exact h p.1 p.2

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- The literal translation family determined by a continuous map
from the actual additive circle to a topological additive group. -/
def additionSweepMap (b : C(Circle, G)) : C(Circle × G, G) :=
  (PeriodTorusHigherHomologyPontryagin.additionMap G).comp
    (b.prodMap (ContinuousMap.id G))

@[simp] theorem additionSweepMap_apply (b : C(Circle, G)) (t : Circle) (x : G) :
    additionSweepMap b (t, x) = b t + x := rfl

/-- Sweeping by addition is exactly the genuine Pontryagin product,
with the positive circle image as its degree-one left factor. -/
theorem sweep_addition (b : C(Circle, G)) (n : ℕ) (v : SingularHomology G n) :
    sweep (additionSweepMap b) n v =
      PeriodTorusHigherHomologyPontryagin.product G n
        (singularHomologyMap b 1 (loopHomologyClass CirclePaths.positiveLoop)) v := by
  have h := crossProductHomology_natural b (ContinuousMap.id G) n
    (loopHomologyClass CirclePaths.positiveLoop) v
  change singularHomologyMap (b.prodMap (ContinuousMap.id G)) (n + 1)
      (positiveCircleCross G n v) =
    crossProductHomology G G n
      (singularHomologyMap b 1 (loopHomologyClass CirclePaths.positiveLoop))
      (singularHomologyMap (ContinuousMap.id G) n v) at h
  rw [singularHomologyMap_id, LinearMap.id_apply] at h
  rw [sweep_apply, additionSweepMap, singularHomologyMap_comp, LinearMap.comp_apply,
    h, PeriodTorusHigherHomologyPontryagin.product_apply]

/-- Any actual continuous map with the translation formula has the
same genuine Pontryagin sweep, without changing its definition. -/
theorem sweep_eq_product_of_addition (a : C(Circle × G, G)) (b : C(Circle, G))
    (h : ∀ t x, a (t, x) = b t + x) (n : ℕ) (v : SingularHomology G n) :
    sweep a n v = PeriodTorusHigherHomologyPontryagin.product G n
      (singularHomologyMap b 1 (loopHomologyClass CirclePaths.positiveLoop)) v := by
  have ha : a = additionSweepMap b := by
    apply ContinuousMap.ext
    intro p
    exact h p.1 p.2
  rw [ha]
  exact sweep_addition b n v

/-- An actual equivariant map from a translation family carries its
Pontryagin product to the sweep in the target space. -/
theorem sweep_equivariant_addition_of_comp_eq (a : C(Circle × X, X))
    (b : C(Circle, G)) (i : C(G, X))
    (h : a.comp ((ContinuousMap.id Circle).prodMap i) = i.comp (additionSweepMap b))
    (n : ℕ) (v : SingularHomology G n) :
    sweep a n (singularHomologyMap i n v) = singularHomologyMap i (n + 1)
      (PeriodTorusHigherHomologyPontryagin.product G n
        (singularHomologyMap b 1 (loopHomologyClass CirclePaths.positiveLoop)) v) := by
  rw [sweep_natural (additionSweepMap b) a i h, sweep_addition]

/-- The pointwise translation-intertwining formula alone gives the
exact sweep of every image class, with the circle-first positive sign. -/
theorem sweep_equivariant_addition (a : C(Circle × X, X)) (b : C(Circle, G))
    (i : C(G, X)) (h : ∀ t y, a (t, i y) = i (b t + y))
    (n : ℕ) (v : SingularHomology G n) :
    sweep a n (singularHomologyMap i n v) = singularHomologyMap i (n + 1)
      (PeriodTorusHigherHomologyPontryagin.product G n
        (singularHomologyMap b 1 (loopHomologyClass CirclePaths.positiveLoop)) v) := by
  apply sweep_equivariant_addition_of_comp_eq a b i ?_ n v
  apply ContinuousMap.ext
  intro p
  exact h p.1 p.2

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
