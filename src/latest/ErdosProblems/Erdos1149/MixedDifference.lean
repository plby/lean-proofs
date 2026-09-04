/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Circle

/-!
# Mixed finite differences

This file supplies the real-variable calculus used at the leaves of a
controlled Weyl-differencing tree.  An arbitrary ordered translate pair is
written as a signed positive forward difference.  Iterating this identity
turns an entire mixed history into one sign, one harmless base translation,
and a list of nonnegative forward steps.  The resulting positive differences
are then estimated by repeated applications of the mean-value theorem.
-/

namespace Erdos1149

open scoped ComplexConjugate

namespace MixedDifference

/-! ## Positive forward differences -/

/-- A real forward difference with real displacement `h`. -/
def realPositiveDifference (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  f (x + h) - f x

/-- Iterated real forward differences.  The head of the list is the
outermost difference, matching controlled-correlation histories. -/
def iteratedRealPositiveDifference (f : ℝ → ℝ) :
    List ℝ → ℝ → ℝ
  | [], x => f x
  | h :: hs, x =>
      realPositiveDifference (iteratedRealPositiveDifference f hs) h x

@[simp] theorem iteratedRealPositiveDifference_nil
    (f : ℝ → ℝ) (x : ℝ) :
    iteratedRealPositiveDifference f [] x = f x := rfl

@[simp] theorem iteratedRealPositiveDifference_cons
    (f : ℝ → ℝ) (h : ℝ) (hs : List ℝ) (x : ℝ) :
    iteratedRealPositiveDifference f (h :: hs) x =
      iteratedRealPositiveDifference f hs (x + h) -
        iteratedRealPositiveDifference f hs x := rfl

/-- Differentiation commutes with every finite forward-difference history. -/
theorem hasDerivAt_iteratedRealPositiveDifference
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hs : List ℝ) (x : ℝ) :
    HasDerivAt (iteratedRealPositiveDifference f hs)
      (iteratedRealPositiveDifference f' hs x) x := by
  induction hs generalizing x with
  | nil => exact hf x
  | cons h hs ih =>
      simp only [iteratedRealPositiveDifference_cons]
      have hderiv := (ih (x + h)).comp_add_const x h |>.sub (ih x)
      exact hderiv.congr_of_eventuallyEq (by
        filter_upwards [] with y
        rfl)

/-- Repeated mean-value bounds for an iterated positive difference. -/
theorem iteratedRealPositiveDifference_bounds
    (F : ℕ → ℝ → ℝ) (hs : List ℝ) (L U x : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hsmooth : ∀ j < hs.length, ∀ y,
      HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y, L ≤ F hs.length y ∧ F hs.length y ≤ U) :
    L * hs.prod ≤ iteratedRealPositiveDifference (F 0) hs x ∧
      iteratedRealPositiveDifference (F 0) hs x ≤ U * hs.prod := by
  induction hs generalizing F L U x with
  | nil =>
      simpa only [iteratedRealPositiveDifference_nil, List.prod_nil,
        mul_one, List.length_nil] using hfinal x
  | cons h hs ih =>
      have hh : 0 ≤ h := hsteps h (by simp)
      have htail : ∀ t ∈ hs, 0 ≤ t := by
        intro t ht
        exact hsteps t (by simp [ht])
      let G : ℕ → ℝ → ℝ := fun j ↦ F (j + 1)
      have hsmoothTail : ∀ j < hs.length, ∀ y,
          HasDerivAt (G j) (G (j + 1) y) y := by
        intro j hj y
        simpa only [G, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hsmooth (j + 1) (by simp only [List.length_cons]; omega) y
      have hfinalTail : ∀ y,
          L ≤ G hs.length y ∧ G hs.length y ≤ U := by
        intro y
        simpa only [G, List.length_cons, Nat.add_comm] using hfinal y
      have hderivBounds (y : ℝ) :
          L * hs.prod ≤ iteratedRealPositiveDifference (F 1) hs y ∧
            iteratedRealPositiveDifference (F 1) hs y ≤ U * hs.prod := by
        simpa only [G] using
          ih G L U y htail hsmoothTail hfinalTail
      let g : ℝ → ℝ := iteratedRealPositiveDifference (F 0) hs
      let g' : ℝ → ℝ := iteratedRealPositiveDifference (F 1) hs
      have hgderiv (y : ℝ) : HasDerivAt g (g' y) y := by
        apply hasDerivAt_iteratedRealPositiveDifference
        intro z
        simpa only [g, g'] using hsmooth 0 (by simp) z
      have hgd : Differentiable ℝ g := fun y ↦ (hgderiv y).differentiableAt
      have hderivEq (y : ℝ) : deriv g y = g' y := (hgderiv y).deriv
      have hxy : x ≤ x + h := by linarith
      have hlower :
          (L * hs.prod) * ((x + h) - x) ≤ g (x + h) - g x := by
        apply mul_sub_le_image_sub_of_le_deriv hgd
        · intro y
          rw [hderivEq]
          exact (hderivBounds y).1
        · exact hxy
      have hupper :
          g (x + h) - g x ≤ (U * hs.prod) * ((x + h) - x) := by
        apply image_sub_le_mul_sub_of_deriv_le hgd
        · intro y
          rw [hderivEq]
          exact (hderivBounds y).2
        · exact hxy
      simpa only [iteratedRealPositiveDifference_cons, g, List.prod_cons] using
        And.intro (by nlinarith) (by nlinarith)

/-! ### Localized calculus on a translation window -/

/-- A forward-difference history only asks for the derivative of the
underlying function between its base point and its total translation. -/
theorem hasDerivAt_iteratedRealPositiveDifference_of_mem_Icc
    {f f' : ℝ → ℝ} {A B x : ℝ} (hs : List ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hf : ∀ y ∈ Set.Icc A B, HasDerivAt f (f' y) y)
    (hxA : A ≤ x) (hxB : x + hs.sum ≤ B) :
    HasDerivAt (iteratedRealPositiveDifference f hs)
      (iteratedRealPositiveDifference f' hs x) x := by
  induction hs generalizing x with
  | nil =>
      apply hf x
      constructor
      · exact hxA
      · simpa using hxB
  | cons h hs ih =>
      have hh : 0 ≤ h := hsteps h (by simp)
      have htail : ∀ t ∈ hs, 0 ≤ t := by
        intro t ht
        exact hsteps t (by simp [ht])
      have hxTail : x + hs.sum ≤ B := by
        have htotal : x + h + hs.sum ≤ B := by
          simpa only [List.sum_cons, add_assoc] using hxB
        linarith
      have hxhA : A ≤ x + h := hxA.trans (by linarith)
      have hxhB : x + h + hs.sum ≤ B := by
        simpa only [List.sum_cons, add_assoc] using hxB
      simp only [iteratedRealPositiveDifference_cons]
      have hderiv :=
        (ih (x := x + h) htail hxhA hxhB).comp_add_const x h |>.sub
          (ih (x := x) htail hxA hxTail)
      exact hderiv.congr_of_eventuallyEq (by
        filter_upwards [] with y
        rfl)

/-- Localized repeated mean-value bounds.  All derivatives and the final
derivative estimate are required only on a containing interval `[A,B]`;
`x + hs.sum ≤ B` is the complete translation-budget condition. -/
theorem iteratedRealPositiveDifference_bounds_on_Icc
    (F : ℕ → ℝ → ℝ) (hs : List ℝ)
    (A B L U x : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hxA : A ≤ x) (hxB : x + hs.sum ≤ B)
    (hsmooth : ∀ j < hs.length, ∀ y ∈ Set.Icc A B,
      HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y ∈ Set.Icc A B,
      L ≤ F hs.length y ∧ F hs.length y ≤ U) :
    L * hs.prod ≤ iteratedRealPositiveDifference (F 0) hs x ∧
      iteratedRealPositiveDifference (F 0) hs x ≤ U * hs.prod := by
  induction hs generalizing F x with
  | nil =>
      have hx : x ∈ Set.Icc A B := ⟨hxA, by simpa using hxB⟩
      simpa only [iteratedRealPositiveDifference_nil, List.prod_nil,
        mul_one, List.length_nil] using hfinal x hx
  | cons h hs ih =>
      have hh : 0 ≤ h := hsteps h (by simp)
      have htail : ∀ t ∈ hs, 0 ≤ t := by
        intro t ht
        exact hsteps t (by simp [ht])
      by_cases hh0 : h = 0
      · subst h
        simp
      have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
      let G : ℕ → ℝ → ℝ := fun j ↦ F (j + 1)
      have hsmoothTail : ∀ j < hs.length, ∀ y ∈ Set.Icc A B,
          HasDerivAt (G j) (G (j + 1) y) y := by
        intro j hj y hy
        simpa only [G, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hsmooth (j + 1) (by simp only [List.length_cons]; omega) y hy
      have hfinalTail : ∀ y ∈ Set.Icc A B,
          L ≤ G hs.length y ∧ G hs.length y ≤ U := by
        intro y hy
        simpa only [G, List.length_cons, Nat.add_comm] using hfinal y hy
      have hderivBounds (y : ℝ) (hy : y ∈ Set.Icc x (x + h)) :
          L * hs.prod ≤ iteratedRealPositiveDifference (F 1) hs y ∧
            iteratedRealPositiveDifference (F 1) hs y ≤ U * hs.prod := by
        have hyA : A ≤ y := hxA.trans hy.1
        have hyB : y + hs.sum ≤ B := by
          have hbudget : x + h + hs.sum ≤ B := by
            simpa only [List.sum_cons, add_assoc] using hxB
          linarith [hy.2]
        simpa only [G] using
          ih G y htail hyA hyB hsmoothTail hfinalTail
      let g : ℝ → ℝ := iteratedRealPositiveDifference (F 0) hs
      let g' : ℝ → ℝ := iteratedRealPositiveDifference (F 1) hs
      have hgderiv (y : ℝ) (hy : y ∈ Set.Icc x (x + h)) :
          HasDerivAt g (g' y) y := by
        have hyA : A ≤ y := hxA.trans hy.1
        have hyB : y + hs.sum ≤ B := by
          have hbudget : x + h + hs.sum ≤ B := by
            simpa only [List.sum_cons, add_assoc] using hxB
          linarith [hy.2]
        apply hasDerivAt_iteratedRealPositiveDifference_of_mem_Icc hs htail
        · intro z hz
          simpa only [g, g'] using hsmooth 0 (by simp) z hz
        · exact hyA
        · exact hyB
      have hgcont : ContinuousOn g (Set.Icc x (x + h)) := by
        intro y hy
        exact (hgderiv y hy).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hcSlope⟩ := exists_hasDerivAt_eq_slope g g'
        (by linarith) hgcont (fun y hy ↦ hgderiv y ⟨hy.1.le, hy.2.le⟩)
      have hcBounds := hderivBounds c ⟨hc.1.le, hc.2.le⟩
      have hslope : g' c * h = g (x + h) - g x := by
        rw [hcSlope, show x + h - x = h by ring]
        exact div_mul_cancel₀ _ hh0
      simp only [iteratedRealPositiveDifference_cons, List.prod_cons]
      constructor <;> nlinarith

/-- Localized bounds for a unit increment.  The interval budget includes
both the history translations and the additional unit displacement. -/
theorem iteratedRealPositiveDifference_unitIncrement_bounds_on_Icc
    (F : ℕ → ℝ → ℝ) (hs : List ℝ)
    (A B L U x : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hxA : A ≤ x) (hxB : x + 1 + hs.sum ≤ B)
    (hsmooth : ∀ j < hs.length + 1, ∀ y ∈ Set.Icc A B,
      HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y ∈ Set.Icc A B,
      L ≤ F (hs.length + 1) y ∧ F (hs.length + 1) y ≤ U) :
    L * hs.prod ≤
        iteratedRealPositiveDifference (F 0) hs (x + 1) -
          iteratedRealPositiveDifference (F 0) hs x ∧
      iteratedRealPositiveDifference (F 0) hs (x + 1) -
          iteratedRealPositiveDifference (F 0) hs x ≤ U * hs.prod := by
  have hsteps' : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    simp only [List.mem_cons] at hh
    rcases hh with rfl | hh
    · norm_num
    · exact hsteps h hh
  have h := iteratedRealPositiveDifference_bounds_on_Icc F
    ((1 : ℝ) :: hs) A B L U x hsteps' hxA (by simpa [add_assoc] using hxB)
    (by simpa using hsmooth) (by simpa using hfinal)
  simpa only [iteratedRealPositiveDifference_cons, List.prod_cons, one_mul]
    using h

/-- Localized monotonicity of a forward difference.  The observed interval
`[C,D]`, enlarged by the total translation of `hs`, must lie in the smooth
window `[A,B]`. -/
theorem monotoneOn_iteratedRealPositiveDifference_of_deriv_nonneg_on_Icc
    {f f' : ℝ → ℝ} (hs : List ℝ) (A B C D : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hCA : A ≤ C) (hDB : D + hs.sum ≤ B)
    (hf : ∀ y ∈ Set.Icc A B, HasDerivAt f (f' y) y)
    (hnonneg : ∀ y ∈ Set.Icc C D,
      0 ≤ iteratedRealPositiveDifference f' hs y) :
    MonotoneOn (iteratedRealPositiveDifference f hs) (Set.Icc C D) := by
  have hd (y : ℝ) (hy : y ∈ Set.Icc C D) :
      HasDerivAt (iteratedRealPositiveDifference f hs)
        (iteratedRealPositiveDifference f' hs y) y := by
    apply hasDerivAt_iteratedRealPositiveDifference_of_mem_Icc hs hsteps hf
    · exact hCA.trans hy.1
    · linarith [hy.2]
  apply monotoneOn_of_deriv_nonneg (convex_Icc C D)
  · intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy
    exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hdy := hd y (interior_subset hy)
    rw [hdy.deriv]
    exact hnonneg y (interior_subset hy)

/-- Localized antitonicity of a forward difference. -/
theorem antitoneOn_iteratedRealPositiveDifference_of_deriv_nonpos_on_Icc
    {f f' : ℝ → ℝ} (hs : List ℝ) (A B C D : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hCA : A ≤ C) (hDB : D + hs.sum ≤ B)
    (hf : ∀ y ∈ Set.Icc A B, HasDerivAt f (f' y) y)
    (hnonpos : ∀ y ∈ Set.Icc C D,
      iteratedRealPositiveDifference f' hs y ≤ 0) :
    AntitoneOn (iteratedRealPositiveDifference f hs) (Set.Icc C D) := by
  have hd (y : ℝ) (hy : y ∈ Set.Icc C D) :
      HasDerivAt (iteratedRealPositiveDifference f hs)
        (iteratedRealPositiveDifference f' hs y) y := by
    apply hasDerivAt_iteratedRealPositiveDifference_of_mem_Icc hs hsteps hf
    · exact hCA.trans hy.1
    · linarith [hy.2]
  apply antitoneOn_of_deriv_nonpos (convex_Icc C D)
  · intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy
    exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hdy := hd y (interior_subset hy)
    rw [hdy.deriv]
    exact hnonpos y (interior_subset hy)

/-- If the next iterated derivative is nonnegative, the consecutive
increments of a positive-difference phase are monotone on `[C,D]`. -/
theorem monotoneOn_unitIncrement_of_nextDifference_nonneg_on_Icc
    {f f' : ℝ → ℝ} (hs : List ℝ) (A B C D : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hCA : A ≤ C) (hDB : D + 1 + hs.sum ≤ B)
    (hf : ∀ y ∈ Set.Icc A B, HasDerivAt f (f' y) y)
    (hnonneg : ∀ y ∈ Set.Icc C D,
      0 ≤ iteratedRealPositiveDifference f' ((1 : ℝ) :: hs) y) :
    MonotoneOn
      (fun y ↦ iteratedRealPositiveDifference f hs (y + 1) -
        iteratedRealPositiveDifference f hs y) (Set.Icc C D) := by
  have hsteps' : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    rcases (List.mem_cons.mp hh) with rfl | hh
    · norm_num
    · exact hsteps h hh
  have hm :=
    monotoneOn_iteratedRealPositiveDifference_of_deriv_nonneg_on_Icc
      ((1 : ℝ) :: hs) A B C D hsteps' hCA (by simpa [add_assoc] using hDB)
        hf hnonneg
  intro x hx y hy hxy
  simpa only [iteratedRealPositiveDifference_cons] using hm hx hy hxy

/-- If the next iterated derivative is nonpositive, the consecutive
increments are antitone on `[C,D]`. -/
theorem antitoneOn_unitIncrement_of_nextDifference_nonpos_on_Icc
    {f f' : ℝ → ℝ} (hs : List ℝ) (A B C D : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hCA : A ≤ C) (hDB : D + 1 + hs.sum ≤ B)
    (hf : ∀ y ∈ Set.Icc A B, HasDerivAt f (f' y) y)
    (hnonpos : ∀ y ∈ Set.Icc C D,
      iteratedRealPositiveDifference f' ((1 : ℝ) :: hs) y ≤ 0) :
    AntitoneOn
      (fun y ↦ iteratedRealPositiveDifference f hs (y + 1) -
        iteratedRealPositiveDifference f hs y) (Set.Icc C D) := by
  have hsteps' : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    rcases (List.mem_cons.mp hh) with rfl | hh
    · norm_num
    · exact hsteps h hh
  have hm :=
    antitoneOn_iteratedRealPositiveDifference_of_deriv_nonpos_on_Icc
      ((1 : ℝ) :: hs) A B C D hsteps' hCA (by simpa [add_assoc] using hDB)
        hf hnonpos
  intro x hx y hy hxy
  simpa only [iteratedRealPositiveDifference_cons] using hm hx hy hxy

/-- A fixed nonnegative sign for the derivative of order `hs.length + 2`
implies monotonicity of the unit increments after the history `hs`.  This
packages the second localized MVT application used before Kusmin--Landau. -/
theorem monotoneOn_unitIncrement_of_finalDerivative_nonneg_on_Icc
    (F : ℕ → ℝ → ℝ) (hs : List ℝ)
    (A B C D L U : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hCA : A ≤ C) (hDB : D + 1 + hs.sum ≤ B) (hL : 0 ≤ L)
    (hsmooth : ∀ j < hs.length + 2, ∀ y ∈ Set.Icc A B,
      HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y ∈ Set.Icc A B,
      L ≤ F (hs.length + 2) y ∧ F (hs.length + 2) y ≤ U) :
    MonotoneOn
      (fun y ↦ iteratedRealPositiveDifference (F 0) hs (y + 1) -
        iteratedRealPositiveDifference (F 0) hs y) (Set.Icc C D) := by
  have hsteps' : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · norm_num
    · exact hsteps h hh
  let G : ℕ → ℝ → ℝ := fun j ↦ F (j + 1)
  have hnonneg (y : ℝ) (hy : y ∈ Set.Icc C D) :
      0 ≤ iteratedRealPositiveDifference (F 1) ((1 : ℝ) :: hs) y := by
    have hyA : A ≤ y := hCA.trans hy.1
    have hyB : y + ((1 : ℝ) :: hs).sum ≤ B := by
      simp only [List.sum_cons]
      linarith [hy.2]
    have hb := iteratedRealPositiveDifference_bounds_on_Icc G
      ((1 : ℝ) :: hs) A B L U y hsteps' hyA hyB
        (by
          intro j hj z hz
          rw [List.length_cons] at hj
          simpa only [G, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hsmooth (j + 1) (by omega) z hz)
        (by
          intro z hz
          simpa only [G, List.length_cons, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hfinal z hz)
    have hp : 0 ≤ ((1 : ℝ) :: hs).prod := List.prod_nonneg hsteps'
    simpa only [G] using (mul_nonneg hL hp).trans hb.1
  apply monotoneOn_unitIncrement_of_nextDifference_nonneg_on_Icc
    hs A B C D hsteps hCA hDB
  · intro y hy
    exact hsmooth 0 (by omega) y hy
  · exact hnonneg

/-- The fixed nonpositive-sign counterpart of the preceding theorem. -/
theorem antitoneOn_unitIncrement_of_finalDerivative_nonpos_on_Icc
    (F : ℕ → ℝ → ℝ) (hs : List ℝ)
    (A B C D L U : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hCA : A ≤ C) (hDB : D + 1 + hs.sum ≤ B) (hU : U ≤ 0)
    (hsmooth : ∀ j < hs.length + 2, ∀ y ∈ Set.Icc A B,
      HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y ∈ Set.Icc A B,
      L ≤ F (hs.length + 2) y ∧ F (hs.length + 2) y ≤ U) :
    AntitoneOn
      (fun y ↦ iteratedRealPositiveDifference (F 0) hs (y + 1) -
        iteratedRealPositiveDifference (F 0) hs y) (Set.Icc C D) := by
  have hsteps' : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · norm_num
    · exact hsteps h hh
  let G : ℕ → ℝ → ℝ := fun j ↦ F (j + 1)
  have hnonpos (y : ℝ) (hy : y ∈ Set.Icc C D) :
      iteratedRealPositiveDifference (F 1) ((1 : ℝ) :: hs) y ≤ 0 := by
    have hyA : A ≤ y := hCA.trans hy.1
    have hyB : y + ((1 : ℝ) :: hs).sum ≤ B := by
      simp only [List.sum_cons]
      linarith [hy.2]
    have hb := iteratedRealPositiveDifference_bounds_on_Icc G
      ((1 : ℝ) :: hs) A B L U y hsteps' hyA hyB
        (by
          intro j hj z hz
          rw [List.length_cons] at hj
          simpa only [G, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hsmooth (j + 1) (by omega) z hz)
        (by
          intro z hz
          simpa only [G, List.length_cons, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hfinal z hz)
    have hp : 0 ≤ ((1 : ℝ) :: hs).prod := List.prod_nonneg hsteps'
    have hUp : U * ((1 : ℝ) :: hs).prod ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hU hp
    simpa only [G] using hb.2.trans hUp
  apply antitoneOn_unitIncrement_of_nextDifference_nonpos_on_Icc
    hs A B C D hsteps hCA hDB
  · intro y hy
    exact hsmooth 0 (by omega) y hy
  · exact hnonpos

/-! ## Normalizing ordered translate pairs -/

/-- Difference of two real translates. -/
def realPairDifference (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  f (x + a) - f (x + b)

/-- Iterated translate-pair differences, with the head outermost. -/
def iteratedRealPairDifference (f : ℝ → ℝ) :
    List (ℝ × ℝ) → ℝ → ℝ
  | [], x => f x
  | (a, b) :: hs, x =>
      realPairDifference (iteratedRealPairDifference f hs) a b x

@[simp] theorem iteratedRealPairDifference_nil (f : ℝ → ℝ) (x : ℝ) :
    iteratedRealPairDifference f [] x = f x := rfl

@[simp] theorem iteratedRealPairDifference_cons
    (f : ℝ → ℝ) (a b : ℝ) (hs : List (ℝ × ℝ)) (x : ℝ) :
    iteratedRealPairDifference f ((a, b) :: hs) x =
      iteratedRealPairDifference f hs (x + a) -
        iteratedRealPairDifference f hs (x + b) := rfl

/-- Orientation of an ordered pair: `1` for a forward-oriented pair and
`-1` for a backward-oriented pair. -/
noncomputable def pairOrientation (a b : ℝ) : ℝ :=
  if b ≤ a then 1 else -1

/-- The nonnegative length of an ordered translate pair. -/
def pairStep (a b : ℝ) : ℝ := |a - b|

/-- The common base translation in the positive-difference normal form. -/
def pairBase (a b : ℝ) : ℝ := min a b

@[simp] theorem abs_pairOrientation (a b : ℝ) :
    |pairOrientation a b| = 1 := by
  by_cases h : b ≤ a
  · simp [pairOrientation, h]
  · simp [pairOrientation, h]

theorem pairOrientation_ne_zero (a b : ℝ) : pairOrientation a b ≠ 0 := by
  intro h
  have := congrArg abs h
  simp at this

@[simp] theorem pairStep_nonneg (a b : ℝ) : 0 ≤ pairStep a b :=
  abs_nonneg _

/-- Exact signed-positive normalization of one ordered pair. -/
theorem realPairDifference_eq_orientation_mul
    (f : ℝ → ℝ) (a b x : ℝ) :
    realPairDifference f a b x =
      pairOrientation a b *
        realPositiveDifference f (pairStep a b) (x + pairBase a b) := by
  by_cases h : b ≤ a
  · rw [show pairOrientation a b = 1 by simp [pairOrientation, h]]
    simp only [realPairDifference, pairStep, pairBase, min_eq_right h,
      one_mul, realPositiveDifference]
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    congr 1
    ring_nf
  · have hab : a ≤ b := le_of_not_ge h
    rw [show pairOrientation a b = -1 by simp [pairOrientation, h]]
    simp only [realPairDifference, pairStep, pairBase, min_eq_left hab,
      neg_mul, realPositiveDifference]
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring_nf

/-- Product of the orientation signs in a mixed history. -/
noncomputable def historyOrientation (hs : List (ℝ × ℝ)) : ℝ :=
  (hs.map fun ab ↦ pairOrientation ab.1 ab.2).prod

/-- Positive step lengths in a mixed history. -/
def historySteps (hs : List (ℝ × ℝ)) : List ℝ :=
  hs.map fun ab ↦ pairStep ab.1 ab.2

/-- Total base translation in a mixed history. -/
def historyBase (hs : List (ℝ × ℝ)) : ℝ :=
  (hs.map fun ab ↦ pairBase ab.1 ab.2).sum

@[simp] theorem length_historySteps (hs : List (ℝ × ℝ)) :
    (historySteps hs).length = hs.length := by
  simp [historySteps]

@[simp] theorem historyOrientation_nil : historyOrientation [] = 1 := rfl
@[simp] theorem historySteps_nil : historySteps [] = [] := rfl
@[simp] theorem historyBase_nil : historyBase [] = 0 := rfl

@[simp] theorem historyOrientation_cons (a b : ℝ) (hs : List (ℝ × ℝ)) :
    historyOrientation ((a, b) :: hs) =
      pairOrientation a b * historyOrientation hs := by
  simp [historyOrientation]

@[simp] theorem historySteps_cons (a b : ℝ) (hs : List (ℝ × ℝ)) :
    historySteps ((a, b) :: hs) = pairStep a b :: historySteps hs := rfl

@[simp] theorem historyBase_cons (a b : ℝ) (hs : List (ℝ × ℝ)) :
    historyBase ((a, b) :: hs) = pairBase a b + historyBase hs := by
  simp [historyBase]

theorem historySteps_nonneg (hs : List (ℝ × ℝ)) :
    ∀ h ∈ historySteps hs, 0 ≤ h := by
  intro h hh
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hh
  exact pairStep_nonneg ab.1 ab.2

@[simp] theorem abs_historyOrientation (hs : List (ℝ × ℝ)) :
    |historyOrientation hs| = 1 := by
  induction hs with
  | nil => simp
  | cons ab hs ih =>
      rcases ab with ⟨a, b⟩
      rw [historyOrientation_cons, abs_mul, abs_pairOrientation, ih, one_mul]

theorem historyOrientation_ne_zero (hs : List (ℝ × ℝ)) :
    historyOrientation hs ≠ 0 := by
  intro h
  have := congrArg abs h
  simp at this

theorem historyOrientation_eq_one_or_neg_one (hs : List (ℝ × ℝ)) :
    historyOrientation hs = 1 ∨ historyOrientation hs = -1 := by
  exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (abs_historyOrientation hs)

/-- Exact normal form for a full mixed history. -/
theorem iteratedRealPairDifference_eq_normalForm
    (f : ℝ → ℝ) (hs : List (ℝ × ℝ)) (x : ℝ) :
    iteratedRealPairDifference f hs x =
      historyOrientation hs *
        iteratedRealPositiveDifference f (historySteps hs) (x + historyBase hs) := by
  induction hs generalizing x with
  | nil => simp
  | cons ab hs ih =>
      rcases ab with ⟨a, b⟩
      let g : ℝ → ℝ :=
        fun y ↦ iteratedRealPositiveDifference f (historySteps hs) y
      calc
        iteratedRealPairDifference f ((a, b) :: hs) x =
            historyOrientation hs * realPairDifference g a b
              (x + historyBase hs) := by
          rw [iteratedRealPairDifference_cons, ih, ih]
          simp only [realPairDifference, g]
          ring_nf
        _ = historyOrientation hs * pairOrientation a b *
              realPositiveDifference g (pairStep a b)
                (x + historyBase hs + pairBase a b) := by
          rw [realPairDifference_eq_orientation_mul]
          ring
        _ = historyOrientation ((a, b) :: hs) *
              iteratedRealPositiveDifference f
                (historySteps ((a, b) :: hs))
                (x + historyBase ((a, b) :: hs)) := by
          rw [historyOrientation_cons, historySteps_cons, historyBase_cons,
            iteratedRealPositiveDifference_cons]
          simp only [realPositiveDifference, g]
          congr 1 <;> ring_nf

/-! ## Natural histories and sampled smooth functions -/

/-- A controlled history entry `(d,k,l)` represents translations `k*d` and
`l*d`. -/
abbrev NatPairHistory := List (ℕ × ℕ × ℕ)

/-- Explicit positive step contributed by `(d,k,l)`. -/
def natPairStep (h : ℕ × ℕ × ℕ) : ℝ :=
  (h.1 : ℝ) * |(h.2.1 : ℝ) - h.2.2|

/-- Explicit base translation contributed by `(d,k,l)`. -/
def natPairBase (h : ℕ × ℕ × ℕ) : ℝ :=
  (h.1 : ℝ) * (min h.2.1 h.2.2 : ℕ)

def natHistorySteps (hs : NatPairHistory) : List ℝ := hs.map natPairStep

def natHistoryBase (hs : NatPairHistory) : ℝ := (hs.map natPairBase).sum

/-- Cast a controlled natural history to its two real translations. -/
def realHistory (hs : NatPairHistory) : List (ℝ × ℝ) :=
  hs.map fun h ↦ (((h.2.1 * h.1 : ℕ) : ℝ), ((h.2.2 * h.1 : ℕ) : ℝ))

@[simp] theorem length_realHistory (hs : NatPairHistory) :
    (realHistory hs).length = hs.length := by
  simp [realHistory]

theorem pairStep_nat_translations (d k l : ℕ) :
    pairStep ((k * d : ℕ) : ℝ) ((l * d : ℕ) : ℝ) =
      (d : ℝ) * |(k : ℝ) - l| := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  simp only [pairStep]
  push_cast
  calc
    |(k : ℝ) * d - (l : ℝ) * d| = |((k : ℝ) - l) * d| := by ring_nf
    _ = |(k : ℝ) - l| * |(d : ℝ)| := abs_mul _ _
    _ = (d : ℝ) * |(k : ℝ) - l| := by rw [abs_of_nonneg hd0]; ring

theorem pairBase_nat_translations (d k l : ℕ) :
    pairBase ((k * d : ℕ) : ℝ) ((l * d : ℕ) : ℝ) =
      (d : ℝ) * (min k l : ℕ) := by
  unfold pairBase
  by_cases hkl : k ≤ l
  · have hmulNat : k * d ≤ l * d := Nat.mul_le_mul_right d hkl
    have hmul : ((k * d : ℕ) : ℝ) ≤ (l * d : ℕ) := by
      exact_mod_cast hmulNat
    rw [min_eq_left hmul, min_eq_left hkl]
    push_cast
    ring
  · have hlk : l ≤ k := le_of_not_ge hkl
    have hmulNat : l * d ≤ k * d := Nat.mul_le_mul_right d hlk
    have hmul : ((l * d : ℕ) : ℝ) ≤ (k * d : ℕ) := by
      exact_mod_cast hmulNat
    rw [min_eq_right hmul, min_eq_right hlk]
    push_cast
    ring

theorem pairOrientation_nat_translations_of_pos
    (d k l : ℕ) (hd : 0 < d) :
    pairOrientation ((k * d : ℕ) : ℝ) ((l * d : ℕ) : ℝ) =
      if l ≤ k then 1 else -1 := by
  unfold pairOrientation
  by_cases hlk : l ≤ k
  · have hmulNat : l * d ≤ k * d := Nat.mul_le_mul_right d hlk
    have hmul : ((l * d : ℕ) : ℝ) ≤ (k * d : ℕ) := by
      exact_mod_cast hmulNat
    rw [if_pos hmul, if_pos hlk]
  · have hkl : k < l := lt_of_not_ge hlk
    have hmulNat : k * d < l * d := Nat.mul_lt_mul_of_pos_right hkl hd
    have hnot : ¬ ((l * d : ℕ) : ℝ) ≤ (k * d : ℕ) := by
      exact_mod_cast (Nat.not_le_of_lt hmulNat)
    rw [if_neg hnot, if_neg hlk]

theorem pairStep_nat_translations_pos
    (d k l : ℕ) (hd : 0 < d) (hkl : k ≠ l) :
    0 < pairStep ((k * d : ℕ) : ℝ) ((l * d : ℕ) : ℝ) := by
  rw [pairStep_nat_translations]
  exact mul_pos (by exact_mod_cast hd)
    (abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hkl)))

@[simp] theorem historySteps_realHistory (hs : NatPairHistory) :
    historySteps (realHistory hs) = natHistorySteps hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
      rcases h with ⟨d, k, l⟩
      simp only [realHistory, List.map_cons, historySteps_cons,
        natHistorySteps, List.map_cons]
      change pairStep ((k * d : ℕ) : ℝ) ((l * d : ℕ) : ℝ) ::
          historySteps (realHistory hs) =
        natPairStep (d, k, l) :: natHistorySteps hs
      rw [ih]
      congr 1
      exact pairStep_nat_translations d k l

@[simp] theorem historyBase_realHistory (hs : NatPairHistory) :
    historyBase (realHistory hs) = natHistoryBase hs := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
      rcases h with ⟨d, k, l⟩
      simp only [realHistory, List.map_cons, historyBase_cons,
        natHistoryBase, List.map_cons, List.sum_cons]
      change pairBase ((k * d : ℕ) : ℝ) ((l * d : ℕ) : ℝ) +
          historyBase (realHistory hs) =
        natPairBase (d, k, l) + natHistoryBase hs
      rw [ih, pairBase_nat_translations]
      unfold natPairBase
      push_cast
      rfl

/-- Pair differences of an arbitrary real-valued natural sequence. -/
def iteratedNatPairDifference (u : ℕ → ℝ) :
    NatPairHistory → ℕ → ℝ
  | [], x => u x
  | (d, k, l) :: hs, x =>
      iteratedNatPairDifference u hs (x + k * d) -
        iteratedNatPairDifference u hs (x + l * d)

@[simp] theorem iteratedNatPairDifference_nil (u : ℕ → ℝ) (x : ℕ) :
    iteratedNatPairDifference u [] x = u x := rfl

@[simp] theorem iteratedNatPairDifference_cons
    (u : ℕ → ℝ) (d k l : ℕ) (hs : NatPairHistory) (x : ℕ) :
    iteratedNatPairDifference u ((d, k, l) :: hs) x =
      iteratedNatPairDifference u hs (x + k * d) -
        iteratedNatPairDifference u hs (x + l * d) := rfl

/-- Sampling a smooth real function commutes exactly with the history cast. -/
theorem iteratedNatPairDifference_sample
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) :
    iteratedNatPairDifference (fun n ↦ f n) hs x =
      iteratedRealPairDifference f (realHistory hs) x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      rcases h with ⟨d, k, l⟩
      simp only [iteratedNatPairDifference_cons, realHistory, List.map_cons,
        iteratedRealPairDifference_cons, ih]
      push_cast
      rfl

/-- Sampled controlled histories have the same signed-positive normal form. -/
theorem iteratedNatPairDifference_eq_normalForm
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) :
    iteratedNatPairDifference (fun n ↦ f n) hs x =
      historyOrientation (realHistory hs) *
        iteratedRealPositiveDifference f (historySteps (realHistory hs))
          ((x : ℝ) + historyBase (realHistory hs)) := by
  rw [iteratedNatPairDifference_sample,
    iteratedRealPairDifference_eq_normalForm]

/-- The unit increment of a sampled mixed history is its orientation sign
times the unit increment of the normalized positive difference. -/
theorem iteratedNatPairDifference_unitIncrement_eq_normalForm
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) :
    iteratedNatPairDifference (fun n ↦ f n) hs (x + 1) -
        iteratedNatPairDifference (fun n ↦ f n) hs x =
      historyOrientation (realHistory hs) *
        (iteratedRealPositiveDifference f (historySteps (realHistory hs))
            ((x : ℝ) + historyBase (realHistory hs) + 1) -
          iteratedRealPositiveDifference f (historySteps (realHistory hs))
            ((x : ℝ) + historyBase (realHistory hs))) := by
  rw [iteratedNatPairDifference_eq_normalForm,
    iteratedNatPairDifference_eq_normalForm]
  push_cast
  ring_nf

/-- The unit increment before applying the history orientation. -/
def normalizedNatUnitIncrement
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) : ℝ :=
  iteratedRealPositiveDifference f (historySteps (realHistory hs))
      ((x : ℝ) + historyBase (realHistory hs) + 1) -
    iteratedRealPositiveDifference f (historySteps (realHistory hs))
      ((x : ℝ) + historyBase (realHistory hs))

/-- The actual unit increment of a sampled controlled history. -/
def mixedNatUnitIncrement
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) : ℝ :=
  iteratedNatPairDifference (fun n ↦ f n) hs (x + 1) -
    iteratedNatPairDifference (fun n ↦ f n) hs x

theorem mixedNatUnitIncrement_eq_orientation_mul
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) :
    mixedNatUnitIncrement f hs x =
      historyOrientation (realHistory hs) * normalizedNatUnitIncrement f hs x := by
  exact iteratedNatPairDifference_unitIncrement_eq_normalForm f hs x

/-- Orientation transfers a positive two-sided bound to either the positive
or the negative Kusmin--Landau branch. -/
theorem mixedNatUnitIncrement_signed_bounds
    (f : ℝ → ℝ) (hs : NatPairHistory) (x : ℕ) (lo hi : ℝ)
    (hbound : lo ≤ normalizedNatUnitIncrement f hs x ∧
      normalizedNatUnitIncrement f hs x ≤ hi) :
    (historyOrientation (realHistory hs) = 1 ∧
        lo ≤ mixedNatUnitIncrement f hs x ∧
        mixedNatUnitIncrement f hs x ≤ hi) ∨
      (historyOrientation (realHistory hs) = -1 ∧
        -hi ≤ mixedNatUnitIncrement f hs x ∧
        mixedNatUnitIncrement f hs x ≤ -lo) := by
  rcases historyOrientation_eq_one_or_neg_one (realHistory hs) with hsgn | hsgn
  · left
    refine ⟨hsgn, ?_⟩
    rw [mixedNatUnitIncrement_eq_orientation_mul, hsgn, one_mul]
    exact hbound
  · right
    refine ⟨hsgn, ?_⟩
    rw [mixedNatUnitIncrement_eq_orientation_mul, hsgn, neg_one_mul]
    constructor <;> linarith [hbound.1, hbound.2]

/-- If normalized increments are monotone, orientation `1` preserves that
direction while orientation `-1` reverses it. -/
theorem mixedNatUnitIncrement_monotonicity_of_normalized_monotone
    (f : ℝ → ℝ) (hs : NatPairHistory) (S : Set ℕ)
    (hmono : MonotoneOn (normalizedNatUnitIncrement f hs) S) :
    (historyOrientation (realHistory hs) = 1 ∧
        MonotoneOn (mixedNatUnitIncrement f hs) S) ∨
      (historyOrientation (realHistory hs) = -1 ∧
        AntitoneOn (mixedNatUnitIncrement f hs) S) := by
  rcases historyOrientation_eq_one_or_neg_one (realHistory hs) with hsgn | hsgn
  · left
    refine ⟨hsgn, ?_⟩
    intro x hx y hy hxy
    rw [mixedNatUnitIncrement_eq_orientation_mul,
      mixedNatUnitIncrement_eq_orientation_mul, hsgn, one_mul, one_mul]
    exact hmono hx hy hxy
  · right
    refine ⟨hsgn, ?_⟩
    intro x hx y hy hxy
    rw [mixedNatUnitIncrement_eq_orientation_mul,
      mixedNatUnitIncrement_eq_orientation_mul, hsgn, neg_one_mul, neg_one_mul]
    exact neg_le_neg (hmono hx hy hxy)

/-- If normalized increments are antitone, orientation `1` preserves that
direction while orientation `-1` reverses it. -/
theorem mixedNatUnitIncrement_monotonicity_of_normalized_antitone
    (f : ℝ → ℝ) (hs : NatPairHistory) (S : Set ℕ)
    (hmono : AntitoneOn (normalizedNatUnitIncrement f hs) S) :
    (historyOrientation (realHistory hs) = 1 ∧
        AntitoneOn (mixedNatUnitIncrement f hs) S) ∨
      (historyOrientation (realHistory hs) = -1 ∧
        MonotoneOn (mixedNatUnitIncrement f hs) S) := by
  rcases historyOrientation_eq_one_or_neg_one (realHistory hs) with hsgn | hsgn
  · left
    refine ⟨hsgn, ?_⟩
    intro x hx y hy hxy
    rw [mixedNatUnitIncrement_eq_orientation_mul,
      mixedNatUnitIncrement_eq_orientation_mul, hsgn, one_mul, one_mul]
    exact hmono hx hy hxy
  · right
    refine ⟨hsgn, ?_⟩
    intro x hx y hy hxy
    rw [mixedNatUnitIncrement_eq_orientation_mul,
      mixedNatUnitIncrement_eq_orientation_mul, hsgn, neg_one_mul, neg_one_mul]
    exact neg_le_neg (hmono hx hy hxy)

/-- Local derivative bounds give two-sided absolute bounds for the unit
increment of a normalized controlled history.  The assumption `0 ≤ L`
selects the fixed-sign branch before the harmless orientation sign is
discarded by the absolute value. -/
theorem abs_iteratedNatPairDifference_unitIncrement_bounds_on_Icc
    (F : ℕ → ℝ → ℝ) (hs : NatPairHistory) (x : ℕ)
    (A B L U : ℝ) (hL : 0 ≤ L)
    (hxA : A ≤ (x : ℝ) + historyBase (realHistory hs))
    (hxB : (x : ℝ) + historyBase (realHistory hs) + 1 +
      (historySteps (realHistory hs)).sum ≤ B)
    (hsmooth : ∀ j < (historySteps (realHistory hs)).length + 1,
      ∀ y ∈ Set.Icc A B, HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y ∈ Set.Icc A B,
      L ≤ F ((historySteps (realHistory hs)).length + 1) y ∧
        F ((historySteps (realHistory hs)).length + 1) y ≤ U) :
    L * (historySteps (realHistory hs)).prod ≤
        |iteratedNatPairDifference (fun n ↦ F 0 n) hs (x + 1) -
          iteratedNatPairDifference (fun n ↦ F 0 n) hs x| ∧
      |iteratedNatPairDifference (fun n ↦ F 0 n) hs (x + 1) -
          iteratedNatPairDifference (fun n ↦ F 0 n) hs x| ≤
        U * (historySteps (realHistory hs)).prod := by
  let steps := historySteps (realHistory hs)
  let base := historyBase (realHistory hs)
  let inc := iteratedRealPositiveDifference (F 0) steps
      ((x : ℝ) + base + 1) -
    iteratedRealPositiveDifference (F 0) steps ((x : ℝ) + base)
  have hb := iteratedRealPositiveDifference_unitIncrement_bounds_on_Icc
    F steps A B L U ((x : ℝ) + base)
      (historySteps_nonneg (realHistory hs)) hxA (by simpa [steps, base] using hxB)
      (by simpa [steps] using hsmooth) (by simpa [steps] using hfinal)
  have hprod : 0 ≤ steps.prod :=
    List.prod_nonneg (by simpa [steps] using historySteps_nonneg (realHistory hs))
  have hinc : 0 ≤ inc := by
    dsimp only [inc]
    exact (mul_nonneg hL hprod).trans hb.1
  rw [iteratedNatPairDifference_unitIncrement_eq_normalForm]
  rw [abs_mul, abs_historyOrientation, one_mul, abs_of_nonneg hinc]
  exact hb

/-! ## Monotonicity and unit increments -/

/-- A nonnegative derivative makes an iterated positive difference monotone. -/
theorem monotone_iteratedRealPositiveDifference
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hs : List ℝ)
    (hnonneg : ∀ x, 0 ≤ iteratedRealPositiveDifference f' hs x) :
    Monotone (iteratedRealPositiveDifference f hs) := by
  have hd (x : ℝ) : HasDerivAt (iteratedRealPositiveDifference f hs)
      (iteratedRealPositiveDifference f' hs x) x :=
    hasDerivAt_iteratedRealPositiveDifference hf hs x
  apply monotone_of_deriv_nonneg
  · exact fun x ↦ (hd x).differentiableAt
  · intro x
    rw [(hd x).deriv]
    exact hnonneg x

/-- A nonpositive derivative makes an iterated positive difference antitone. -/
theorem antitone_iteratedRealPositiveDifference
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hs : List ℝ)
    (hnonpos : ∀ x, iteratedRealPositiveDifference f' hs x ≤ 0) :
    Antitone (iteratedRealPositiveDifference f hs) := by
  have hd (x : ℝ) : HasDerivAt (iteratedRealPositiveDifference f hs)
      (iteratedRealPositiveDifference f' hs x) x :=
    hasDerivAt_iteratedRealPositiveDifference hf hs x
  apply antitone_of_deriv_nonpos
  · exact fun x ↦ (hd x).differentiableAt
  · intro x
    rw [(hd x).deriv]
    exact hnonpos x

/-- The consecutive increment of an iterated positive difference is the
same difference with one extra unit step. -/
theorem iteratedRealPositiveDifference_unitIncrement
    (f : ℝ → ℝ) (hs : List ℝ) (x : ℝ) :
    iteratedRealPositiveDifference f hs (x + 1) -
        iteratedRealPositiveDifference f hs x =
      iteratedRealPositiveDifference f (1 :: hs) x := rfl

/-- Bounds for the unit increment, obtained from one additional derivative. -/
theorem iteratedRealPositiveDifference_unitIncrement_bounds
    (F : ℕ → ℝ → ℝ) (hs : List ℝ) (L U x : ℝ)
    (hsteps : ∀ h ∈ hs, 0 ≤ h)
    (hsmooth : ∀ j < hs.length + 1, ∀ y,
      HasDerivAt (F j) (F (j + 1) y) y)
    (hfinal : ∀ y, L ≤ F (hs.length + 1) y ∧
      F (hs.length + 1) y ≤ U) :
    L * hs.prod ≤
        iteratedRealPositiveDifference (F 0) hs (x + 1) -
          iteratedRealPositiveDifference (F 0) hs x ∧
      iteratedRealPositiveDifference (F 0) hs (x + 1) -
          iteratedRealPositiveDifference (F 0) hs x ≤ U * hs.prod := by
  have hsteps' : ∀ h ∈ (1 : ℝ) :: hs, 0 ≤ h := by
    intro h hh
    simp only [List.mem_cons] at hh
    rcases hh with rfl | hh
    · norm_num
    · exact hsteps h hh
  have h := iteratedRealPositiveDifference_bounds F ((1 : ℝ) :: hs)
    L U x hsteps' (by simpa using hsmooth) (by simpa using hfinal)
  simpa only [iteratedRealPositiveDifference_cons, List.prod_cons, one_mul]
    using h

/-! ## Fourier phases -/

/-- The standard real Fourier phase. -/
noncomputable def phase (x : ℝ) : ℂ := Real.fourierChar x

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Circle.norm_coe _

theorem phase_sub (x y : ℝ) :
    phase (x - y) = phase x * starRingEnd ℂ (phase y) := by
  have hadd (u v : ℝ) : phase (u + v) = phase u * phase v := by
    change ((Real.fourierChar (u + v) : Circle) : ℂ) =
      ((Real.fourierChar u : Circle) : ℂ) * Real.fourierChar v
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  have hneg (u : ℝ) : phase (-u) = starRingEnd ℂ (phase u) := by
    change ((Real.fourierChar (-u) : Circle) : ℂ) =
      starRingEnd ℂ ((Real.fourierChar u : Circle) : ℂ)
    rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rw [sub_eq_add_neg, hadd, hneg]

/-- Iterated complex pair correlation for real translate histories. -/
noncomputable def iteratedPhasePairCorrelation (f : ℝ → ℝ) :
    List (ℝ × ℝ) → ℝ → ℂ
  | [], x => phase (f x)
  | (a, b) :: hs, x =>
      iteratedPhasePairCorrelation f hs (x + a) *
        starRingEnd ℂ (iteratedPhasePairCorrelation f hs (x + b))

/-- Phase correlations are exactly phases of the corresponding real mixed
differences. -/
theorem iteratedPhasePairCorrelation_eq_phase
    (f : ℝ → ℝ) (hs : List (ℝ × ℝ)) (x : ℝ) :
    iteratedPhasePairCorrelation f hs x =
      phase (iteratedRealPairDifference f hs x) := by
  induction hs generalizing x with
  | nil => rfl
  | cons ab hs ih =>
      rcases ab with ⟨a, b⟩
      simp only [iteratedPhasePairCorrelation, iteratedRealPairDifference,
        realPairDifference, ih]
      rw [phase_sub]

/-- Every iterated phase correlation still has unit norm. -/
@[simp] theorem norm_iteratedPhasePairCorrelation
    (f : ℝ → ℝ) (hs : List (ℝ × ℝ)) (x : ℝ) :
    ‖iteratedPhasePairCorrelation f hs x‖ = 1 := by
  rw [iteratedPhasePairCorrelation_eq_phase, norm_phase]

end MixedDifference

end Erdos1149
