import ErdosProblems.Erdos1002.ContinuedFractionCylinderCounting
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The deterministic oscillatory cylinder sum

This file closes the purely deterministic counting step in the marked-Poisson
argument.  A prefix tuple has one entry in each of `d` finite time boxes.
Each deepest continued-fraction cylinder has terminal denominator at most
`R`.  Thus there are at most `L ^ d` prefix tuples and at most
`2 * (R + 1) ^ 2` deepest cylinders.  Combining these *proved* cardinality
bounds with the exact endpoint evaluation of the oscillatory integral gives
the nested absolute-sum estimate used in the early case and in the
late-prefix argument.

The statement permits an arbitrary retained subfamily of deepest cylinders
for each prefix tuple.  This covers all value-window and denominator-window
filters: on a fixed cylinder their intersection is either empty or one
interval, whose endpoints are the functions `left` and `right` below.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-! ## One interval on every fixed cylinder -/

/-- Intersection of a closed cylinder interval with finitely many affine
closed value windows. -/
def affineWindowIntersection {r : ℕ}
    (cylinderLeft cylinderRight : ℝ)
    (windowLower windowUpper slope intercept : Fin r → ℝ) : Set ℝ :=
  Set.Icc cylinderLeft cylinderRight ∩
    ⋂ i, (fun x ↦ slope i * x + intercept i) ⁻¹'
      Set.Icc (windowLower i) (windowUpper i)

/-- On a fixed continued-fraction cylinder all value coordinates are affine,
so imposing finitely many interval constraints leaves either no points or
one closed interval.  This proves the geometric assertion used when the
cylinder integral is replaced by an interval integral. -/
theorem affineWindowIntersection_eq_empty_or_Icc
    {r : ℕ} (cylinderLeft cylinderRight : ℝ)
    (windowLower windowUpper slope intercept : Fin r → ℝ) :
    affineWindowIntersection cylinderLeft cylinderRight
        windowLower windowUpper slope intercept = ∅ ∨
      ∃ left right : ℝ, left ≤ right ∧
        affineWindowIntersection cylinderLeft cylinderRight
          windowLower windowUpper slope intercept = Set.Icc left right := by
  classical
  let S : Set ℝ := affineWindowIntersection cylinderLeft cylinderRight
    windowLower windowUpper slope intercept
  by_cases hS : S = ∅
  · exact Or.inl hS
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    have hpre (i : Fin r) : Set.OrdConnected
        ((fun x : ℝ ↦ slope i * x + intercept i) ⁻¹'
          Set.Icc (windowLower i) (windowUpper i)) := by
      by_cases hslope : 0 ≤ slope i
      · apply Set.ordConnected_Icc.preimage_mono
        intro x y hxy
        simpa [add_comm] using!
          add_le_add_right (mul_le_mul_of_nonneg_left hxy hslope)
            (intercept i)
      · apply Set.ordConnected_Icc.preimage_anti
        intro x y hxy
        have hslope' : slope i ≤ 0 := le_of_not_ge hslope
        simpa [add_comm] using!
          add_le_add_right (mul_le_mul_of_nonpos_left hxy hslope')
            (intercept i)
    have hord : S.OrdConnected := by
      dsimp [S, affineWindowIntersection]
      exact Set.ordConnected_Icc.inter
        (Set.ordConnected_iInter hpre)
    have hclosed : IsClosed S := by
      dsimp [S, affineWindowIntersection]
      apply isClosed_Icc.inter
      apply isClosed_iInter
      intro i
      exact isClosed_Icc.preimage
        ((continuous_const.mul continuous_id).add continuous_const)
    have hsubset : S ⊆ Set.Icc cylinderLeft cylinderRight := by
      intro x hx
      exact hx.1
    have hcompact : IsCompact S :=
      isCompact_Icc.of_isClosed_subset hclosed hsubset
    have hconnected : IsConnected S := ⟨hSne, hord.isPreconnected⟩
    have heq : S = Set.Icc (sInf S) (sSup S) :=
      eq_Icc_of_connected_compact hconnected hcompact
    refine Or.inr ⟨sInf S, sSup S, ?_, heq⟩
    exact Set.nonempty_Icc.mp (heq ▸ hSne)

/-- Choices of one integer index from each of a finite collection of time
boxes. -/
abbrev OscillatoryPrefixTuple {d : ℕ} (boxes : Fin d → Finset ℕ) :=
  ∀ j, ↑(boxes j)

/-- The number of prefix tuples is the product of the sizes of the time
boxes. -/
theorem card_oscillatoryPrefixTuple {d : ℕ}
    (boxes : Fin d → Finset ℕ) :
    Fintype.card (OscillatoryPrefixTuple boxes) =
      ∏ j, (boxes j).card := by
  simp [OscillatoryPrefixTuple, Fintype.card_pi]

/-- If all `d` boxes have at most `L` elements, there are at most `L ^ d`
prefix tuples. -/
theorem card_oscillatoryPrefixTuple_le_pow {d L : ℕ}
    (boxes : Fin d → Finset ℕ)
    (hboxes : ∀ j, (boxes j).card ≤ L) :
    Fintype.card (OscillatoryPrefixTuple boxes) ≤ L ^ d := by
  rw [card_oscillatoryPrefixTuple]
  calc
    ∏ j, (boxes j).card ≤ ∏ _j : Fin d, L := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun j _ ↦ hboxes j)
    _ = L ^ d := by simp

/--
Full deterministic cylinder-sum estimate.

For every prefix tuple `u`, `cells u` is the retained finite family of
deepest cylinders.  On a retained cylinder `w`, `left u w` and `right u w`
are the two endpoints left after intersecting all affine value constraints,
and `D u w` is the cylinderwise-constant integer frequency before the
outer factor `N`.  The conclusion keeps the absolute value *outside* the
cylinder sum, as in the manuscript.  No cardinality estimate is assumed:
both the tuple count and the denominator-bounded cylinder count are proved
inside the argument.
-/
theorem sum_norm_sum_intervalIntegral_oscillatory_cylinders_le
    {d L R N : ℕ} (hN : 0 < N)
    (boxes : Fin d → Finset ℕ)
    (hboxes : ∀ j, (boxes j).card ≤ L)
    (cells : OscillatoryPrefixTuple boxes →
      Finset (BoundedPositiveTerminalWord R))
    (left right D : OscillatoryPrefixTuple boxes →
      BoundedPositiveTerminalWord R → ℝ)
    {denominatorFloor : ℝ} (hfloor : 0 < denominatorFloor)
    (hD : ∀ u w, w ∈ cells u → denominatorFloor ≤ |D u w|) :
    (∑ u : OscillatoryPrefixTuple boxes,
      ‖∑ w ∈ cells u,
        ∫ x : ℝ in left u w..right u w,
          oscillatoryPhase ((N : ℝ) * D u w) x‖) ≤
      ((2 * L ^ d * (R + 1) ^ 2 : ℕ) : ℝ) /
        (Real.pi * (N : ℝ) * denominatorFloor) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfrequencyFloor : 0 < (N : ℝ) * denominatorFloor :=
    mul_pos hNR hfloor
  let cylinderBound : ℝ :=
    ((2 * (R + 1) ^ 2 : ℕ) : ℝ) /
      (Real.pi * ((N : ℝ) * denominatorFloor))
  have hOne (u : OscillatoryPrefixTuple boxes) :
      ‖∑ w ∈ cells u,
        ∫ x : ℝ in left u w..right u w,
          oscillatoryPhase ((N : ℝ) * D u w) x‖ ≤ cylinderBound := by
    calc
      ‖∑ w ∈ cells u,
          ∫ x : ℝ in left u w..right u w,
            oscillatoryPhase ((N : ℝ) * D u w) x‖ ≤
          ∑ w ∈ cells u,
            ‖∫ x : ℝ in left u w..right u w,
              oscillatoryPhase ((N : ℝ) * D u w) x‖ :=
        norm_sum_le _ _
      _ ≤ cylinderBound := by
        exact sum_norm_intervalIntegral_cfCylinders_le
          (cells u) (left u) (right u)
          (fun w ↦ (N : ℝ) * D u w) hfrequencyFloor (by
            intro w hw
            rw [abs_mul, abs_of_pos hNR]
            exact mul_le_mul_of_nonneg_left (hD u w hw) hNR.le)
  have hcardNat :
      Fintype.card (OscillatoryPrefixTuple boxes) ≤ L ^ d :=
    card_oscillatoryPrefixTuple_le_pow boxes hboxes
  have hcardReal :
      (Fintype.card (OscillatoryPrefixTuple boxes) : ℝ) ≤
        (L ^ d : ℕ) := by
    exact_mod_cast hcardNat
  have hcylinderBound : 0 ≤ cylinderBound := by
    dsimp [cylinderBound]
    positivity
  calc
    (∑ u : OscillatoryPrefixTuple boxes,
      ‖∑ w ∈ cells u,
        ∫ x : ℝ in left u w..right u w,
          oscillatoryPhase ((N : ℝ) * D u w) x‖) ≤
        ∑ _u : OscillatoryPrefixTuple boxes, cylinderBound := by
      exact Finset.sum_le_sum fun u _hu ↦ hOne u
    _ = (Fintype.card (OscillatoryPrefixTuple boxes) : ℝ) *
        cylinderBound := by
      simp
    _ ≤ (L ^ d : ℕ) * cylinderBound :=
      mul_le_mul_of_nonneg_right hcardReal hcylinderBound
    _ = ((2 * L ^ d * (R + 1) ^ 2 : ℕ) : ℝ) /
        (Real.pi * (N : ℝ) * denominatorFloor) := by
      dsimp [cylinderBound]
      push_cast
      ring

end

end Erdos1002
