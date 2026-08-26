/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# First question of Erdős #501 — Hechler's counterexample under `CH`

Under `CH` there is a family `(A x)_{x ∈ ℝ}` of bounded (indeed countable, hence
null) sets with no infinite independent set (S. H. Hechler, *Directed graphs
over topological spaces: some set theoretical aspects*, Israel J. Math. 11
(1972) 231–248).

Construction.  `CH` gives `#ℝ = ℵ₁`, hence a bijection `e : ℝ ≃ ω₁` (as
`(ℵ₁).ord.ToType`); every initial segment `{y | e y < e x}` is countable.  Put

  `A x = {y | e y < e x ∧ |y| ≤ |x| + 1}`.

If `X` were infinite and independent, then for the `e`-least element `m` of any
nonempty `Y ⊆ X` and every other `y ∈ Y` independence forces `|y| + 1 < |m|`
(since `m ∉ A y` and `e m < e y`).  Removing minima repeatedly gives, for every
`n`, an infinite `Y ⊆ X` with `|y| + n ≤ |m₀|` on `Y` (`m₀` the least element of
`X`), which is absurd for `n > |m₀|`.

This is the file `Hechler501FC_master.lean` of the 2026‑08‑16/17 session,
re-derived here at the unified pin; the delivered version may replace it.
The statement is the right-hand side of `formal-conjectures`'
`erdos_501.variants.hechler_CH`.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Analysis.Real.Cardinality

open MeasureTheory Set
open scoped Cardinal

universe u

namespace Erdos501

/-- Hechler (1972): under `CH` there is a family of bounded null sets
`A : ℝ → Set ℝ` with no infinite independent set. -/
theorem hechler_of_CH (hCH : (ℵ₁ : Cardinal.{u}) = 𝔠) :
    ∃ (A : ℝ → Set ℝ),
      (∀ x, Bornology.IsBounded (A x)) ∧
      (∀ x, volume.toOuterMeasure (A x) < 1) ∧
      ¬ ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y) := by
  -- `CH` in universe `0`, and `#ℝ = ℵ₁`.
  have hCH0 : (ℵ₁ : Cardinal.{0}) = 𝔠 := by
    have h : (ℵ₁ : Cardinal.{u}) = Cardinal.lift.{u} (𝔠 : Cardinal.{0}) := by
      rw [Cardinal.lift_continuum]; exact hCH
    exact Cardinal.aleph_one_eq_lift.mp h
  have hR : #ℝ = #((ℵ₁ : Cardinal.{0}).ord.ToType) := by
    rw [Cardinal.mk_real, Cardinal.mk_ord_toType, hCH0]
  -- A well-ordering of `ℝ` of type `ω₁`.
  obtain ⟨e⟩ : Nonempty (ℝ ≃ (ℵ₁ : Cardinal.{0}).ord.ToType) := Cardinal.eq.mp hR
  -- Initial segments of `ω₁` are countable.
  have hIio : ∀ i : (ℵ₁ : Cardinal.{0}).ord.ToType, (Iio i).Countable := by
    intro i
    have h := Cardinal.mk_Iio_lt i (by rw [Cardinal.mk_ord_toType, Ordinal.type_toType])
    rw [Cardinal.mk_ord_toType] at h
    exact Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp h)
  -- The family.
  set A : ℝ → Set ℝ := fun x => {y | e y < e x ∧ |y| ≤ |x| + 1} with hA
  refine ⟨A, ?_, ?_, ?_⟩
  · -- bounded
    intro x
    refine (Metric.isBounded_Icc (-(|x| + 1)) (|x| + 1)).subset ?_
    intro y hy
    exact abs_le.mp hy.2
  · -- countable, hence null; in particular outer measure `< 1`
    intro x
    have hc : (A x).Countable :=
      ((hIio (e x)).preimage e.injective).mono (fun y hy => hy.1)
    show volume (A x) < 1
    rw [hc.measure_zero volume]
    exact zero_lt_one
  · -- no infinite independent set
    rintro ⟨X, hXinf, hXind⟩
    have wf : WellFounded (fun a b : ℝ => e a < e b) := InvImage.wf e wellFounded_lt
    -- The `e`-least element of a nonempty `Y ⊆ X` dominates the rest by more than `1`.
    have key : ∀ Y : Set ℝ, Y ⊆ X → ∀ hY : Y.Nonempty,
        ∀ y ∈ Y, y ≠ wf.min Y hY → |y| + 1 < |wf.min Y hY| := by
      intro Y hYX hY y hy hne
      have hmin : wf.min Y hY ∈ Y := wf.min_mem Y hY
      have h1 : ¬ e y < e (wf.min Y hY) := wf.not_lt_min Y hy
      have h2 : e (wf.min Y hY) < e y :=
        lt_of_le_of_ne (not_lt.mp h1) (fun h => hne (e.injective h).symm)
      have h3 : wf.min Y hY ∉ A y := hXind (hYX hmin) (hYX hy) hne.symm
      simp only [hA, mem_ofPred_eq, not_and, not_le] at h3
      exact h3 h2
    -- Iterate: for every `n` there is an infinite `Y ⊆ X` with `|y| + n ≤ |m|` on `Y`.
    set m := wf.min X hXinf.nonempty with hm
    have claim : ∀ n : ℕ, ∃ Y : Set ℝ, Y ⊆ X ∧ Y.Infinite ∧ ∀ y ∈ Y, |y| + n ≤ |m| := by
      intro n
      induction n with
      | zero =>
        refine ⟨X, subset_rfl, hXinf, fun y hy => ?_⟩
        by_cases hym : y = m
        · subst hym; simp
        · have := key X subset_rfl hXinf.nonempty y hy hym
          push_cast
          linarith
      | succ n ih =>
        obtain ⟨Y, hYX, hYinf, hY⟩ := ih
        have hYne : Y.Nonempty := hYinf.nonempty
        refine ⟨Y \ {wf.min Y hYne}, fun y hy => hYX hy.1,
          hYinf.sdiff (finite_singleton _), fun y hy => ?_⟩
        have hne : y ≠ wf.min Y hYne := fun h => hy.2 (h ▸ mem_singleton _)
        have h1 := key Y hYX hYne y hy.1 hne
        have h2 := hY _ (wf.min_mem Y hYne)
        push_cast
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt |m|
    obtain ⟨Y, -, hYinf, hY⟩ := claim n
    obtain ⟨y, hy⟩ := hYinf.nonempty
    have := hY y hy
    linarith [abs_nonneg y]

end Erdos501
