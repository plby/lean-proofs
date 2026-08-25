/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-
Released under the Apache License 2.0.
This interface and its supporting region lemmas adapt the Jordan curve
formalization already included in this repository.
-/

/-
Informal proof: Ryuji Maehara, "The Jordan curve theorem via the Brouwer
fixed point theorem", American Mathematical Monthly 91 (1984), 641–643.
Original formalization: rkirov/jordan_pick, commit
b141748187099368d1b564de5fc6601026255378, vendored in
Wikipedia.JordanCurveTheorem.Core.
-/

import Wikipedia.JordanCurveTheorem.Regions

/-!
# The Jordan curve theorem

A continuous injective map from the unit circle into the plane has exactly
two complementary connected components. Both are open and path connected;
one is bounded, the other unbounded, and each has the original curve as its
frontier.

The geometric proof is Maehara's reduction to the two-dimensional Brouwer
fixed point theorem. The imported development proves Brouwer from covering
space theory and the no-retraction theorem, so no fixed point or separation
principle is assumed.

* `jordan_curve` gives the exact number of connected components.
* `jordan_curve_theorem` gives both regions and their boundary properties.
* `jordan_curve_circle` uses Mathlib's complex unit circle `Circle` instead
  of the unit sphere in `EuclideanSpace ℝ (Fin 2)`.

The canonical regions and their component lemmas are in `Regions.lean`.
-/

namespace JordanCurveTheorem

open Set Metric Function Bornology

/-- **Jordan curve theorem, component count.** The only hypotheses on the
parametrization are continuity and injectivity. -/
theorem jordan_curve (r : UnitCircle → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set Plane)) = 2 :=
  JordanCurve.jordan_curve r hcont hinj

/-- **Jordan curve theorem, complementary regions.** The complement is the
disjoint union of two nonempty open connected regions, exactly one of which
is bounded. Their frontiers are both the curve. -/
theorem jordan_curve_theorem (r : UnitCircle → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ U V : Set Plane,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range r)ᶜ ∧
      IsBounded U ∧ ¬ IsBounded V ∧
      frontier U = range r ∧ frontier V = range r := by
  refine ⟨inside (range r), outside (range r), ?_⟩
  exact ⟨isOpen_inside hcont, isOpen_outside hcont,
    (isPathConnected_inside hcont hinj).isConnected,
    (isPathConnected_outside hcont).isConnected,
    disjoint_inside_outside (range r), inside_union_outside (range r),
    isBounded_inside hcont hinj, not_isBounded_outside hcont,
    frontier_inside hcont hinj, frontier_outside hcont hinj⟩

/-- The same component count for Mathlib's unit circle in the complex plane. -/
theorem jordan_curve_circle (r : Circle → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set Plane)) = 2 := by
  let e := JordanCurve.Arcs.spherePlaneHomeoCircle
  have hrange : range (r ∘ e) = range r :=
    e.surjective.range_comp r
  rw [← hrange]
  exact jordan_curve (r ∘ e) (hcont.comp e.continuous) (hinj.comp e.injective)

end JordanCurveTheorem

#print axioms JordanCurveTheorem.jordan_curve
-- 'JordanCurveTheorem.jordan_curve' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms JordanCurveTheorem.jordan_curve_theorem
-- 'JordanCurveTheorem.jordan_curve_theorem' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms JordanCurveTheorem.jordan_curve_circle
-- 'JordanCurveTheorem.jordan_curve_circle' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
