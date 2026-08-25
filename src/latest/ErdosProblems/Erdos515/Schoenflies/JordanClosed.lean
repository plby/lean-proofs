/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import ErdosProblems.Erdos515.Schoenflies.SquareCycle
import ErdosProblems.Erdos515.Schoenflies.PolyArcRealize
import Wikipedia.JordanCurveTheorem

/-!
# Part I, with nothing assumed

The end of Part I. Everything below is already proved elsewhere; this module supplies the last
arguments and states the four headline theorems with no hypotheses at all, so that a consumer —
and the axiom audit — sees them in the form the blueprint states them.

Two hypotheses were carried, deliberately, across three waves of parallel work, under the
standing rule that a missing result is named rather than `sorry`-ed:

* `Schoenflies.SquaresTwoConnected`, in `Schoenflies/ArcComplement.lean` — a subdivided
  axis-parallel square boundary is 2-connected. Discharged by
  `Schoenflies.squaresTwoConnected` in `Schoenflies/SquareCycle.lean`.
* `Schoenflies.IsPolyArcCarrier`, in `Schoenflies/ArcCollars.lean` — every simple polygonal arc
  is the carrier of a `PolyArc`. Discharged by
  `Schoenflies.isPolyArcCarrier_of_isPolygonal` in `Schoenflies/PolyArcRealize.lean`, the arc
  analogue of the realization theorem that `Schoenflies/Realization.lean` proves for closed
  curves.

Discharging the first makes `thm:arc-complement`, and with it `lem:accessible-dense` and
`thm:jordan`. Supplying the second removes the collar hypothesis from
`lem:crosscut-at-most-two`, and with `thm:jordan` that finishes `thm:general-crosscut`.

## Blueprint

* `Schoenflies.arc_complement` — **`thm:arc-complement`**: the complement of a simple arc in
  the plane is connected.
* `Schoenflies.jordan_curve_theorem` — **`thm:jordan`**: a Jordan curve separates the plane
  into exactly two regions, one bounded and one unbounded, each with the curve as its boundary.
  Stated as `IsSeparating C`, the same predicate `thm:polygonal-jordan` uses, so that every
  consumer written against the polygonal case applies verbatim.
* `Schoenflies.crosscut_theorem`, `Schoenflies.crosscut_theorem_three_regions` —
  **`thm:general-crosscut`**.
-/

open Set

namespace Schoenflies

/-- **`thm:arc-complement`.** If `A` is a simple arc in the plane, then `ℝ² ∖ A` is connected. -/
theorem arc_complement {A : Set Plane} (hA : IsArc A) : IsConnected Aᶜ :=
  isConnected_compl_arc hA squaresTwoConnected

/-- **`thm:arc-complement`, the polygonal form.** Two distinct points off a simple arc are
joined, off the arc, by a simple polygonal arc. -/
theorem arc_complement_poly {A : Set Plane} (hA : IsArc A) {u w : Plane}
    (huw : u ≠ w) (hu : u ∉ A) (hw : w ∉ A) :
    ∃ P : Set Plane, IsPolygonal P ∧ IsArcBetween P u w ∧ P ⊆ Aᶜ :=
  exists_simple_poly_compl_arc hA squaresTwoConnected huw hu hw

/-- **`thm:jordan`, the Jordan curve theorem.** The complement of a Jordan curve has exactly two
regions, one bounded and one unbounded, and both have the curve as their boundary.

`IsSeparating` packages all of that, and is the same predicate the polygonal case
(`Schoenflies.ClosedPolygon.polygonal_jordan`) is stated through — so `Schoenflies.inside`,
`Schoenflies.outside` and the whole region API of `Schoenflies/CrosscutCells.lean` apply to a
general Jordan curve with nothing to transport. -/
theorem jordan_curve_theorem {C : Set Plane} (hC : IsJordanCurve C) : IsSeparating C :=
  by
    obtain ⟨f, hf, hrange⟩ := hC
    let g : AddCircle (1 : ℝ) → Plane := AddCircle.liftIco 1 0 f
    have hg_cont : Continuous g :=
      AddCircle.liftIco_zero_continuous hf.closes hf.continuousOn
    have hg_inj : Function.Injective g := by
      intro x y hxy
      apply (AddCircle.equivIco (1 : ℝ) 0).injective
      apply Subtype.ext
      exact hf.injOn
        (by simpa using (AddCircle.equivIco (1 : ℝ) 0 x).property)
        (by simpa using (AddCircle.equivIco (1 : ℝ) 0 y).property)
        hxy
    have hg_range : Set.range g = C := by
      rw [← hrange]
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        refine ⟨(AddCircle.equivIco (1 : ℝ) 0 z : ℝ), ?_, rfl⟩
        have hz := (AddCircle.equivIco (1 : ℝ) 0 z).property
        exact ⟨hz.1, le_of_lt (by simpa using hz.2)⟩
      · rintro ⟨t, ht, rfl⟩
        by_cases ht_one : t = 1
        · subst t
          refine ⟨0, ?_⟩
          calc
            g 0 = f 0 := by
              exact AddCircle.liftIco_zero_coe_apply (by norm_num)
            _ = f 1 := hf.closes
        · have ht_lt : t < 1 := lt_of_le_of_ne ht.2 ht_one
          exact ⟨(t : AddCircle (1 : ℝ)),
            AddCircle.liftIco_zero_coe_apply ⟨ht.1, ht_lt⟩⟩
    let r : JordanCurveTheorem.UnitCircle → Plane :=
      g ∘ JordanCurve.Brouwer.acToSphere.symm
    have hr_cont : Continuous r :=
      hg_cont.comp JordanCurve.Brouwer.acToSphere.symm.continuous
    have hr_inj : Function.Injective r :=
      hg_inj.comp JordanCurve.Brouwer.acToSphere.symm.injective
    have hr_range : Set.range r = C := by
      exact (JordanCurve.Brouwer.acToSphere.symm.surjective.range_comp g).trans hg_range
    refine ⟨⟨f, hf, hrange⟩, ?_, ?_, ?_, ?_⟩
    · simpa [JordanCurveTheorem.inside, Schoenflies.inside, hr_range] using
        (JordanCurveTheorem.isPathConnected_inside hr_cont hr_inj).isConnected
    · simpa [JordanCurveTheorem.outside, Schoenflies.outside, hr_range] using
        (JordanCurveTheorem.isPathConnected_outside hr_cont).isConnected
    · simpa [JordanCurveTheorem.inside, Schoenflies.inside, hr_range] using
        JordanCurveTheorem.frontier_inside hr_cont hr_inj
    · simpa [JordanCurveTheorem.outside, Schoenflies.outside, hr_range] using
        JordanCurveTheorem.frontier_outside hr_cont hr_inj

/-- **`thm:general-crosscut`, first sentence.** A polygonal crosscut of a Jordan domain cuts it
into exactly two components, the interiors of the two curves the crosscut makes with the two
arcs of `C`. The two sides are labelled by which arc of `C` their closure meets. -/
theorem crosscut_theorem {C P A₁ A₂ : Set Plane} {p q : Plane}
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  general_crosscut' (fun _ hS => jordan_curve_theorem hS) h hcut

end Schoenflies
