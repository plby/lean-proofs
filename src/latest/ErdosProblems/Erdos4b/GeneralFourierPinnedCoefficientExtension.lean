/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientFace

/-!
# Source support on the reduced pinned coefficient

Extending a reduced tuple by `1` at the pin recovers the literal source
coefficient. Its checked coordinate support therefore also applies to
the weighted reduced coefficient used by the totient graph kernel.
-/

namespace Erdos4b

noncomputable section

def extendPinnedDivisorTuple {K : ℕ} (h : Fin K) (d : PinnedShiftIndex h → ℕ) : Fin K → ℕ :=
  fun i ↦ if hi : i = h then 1 else d ⟨i, hi⟩

@[simp] theorem extendPinnedDivisorTuple_at_pin {K : ℕ} (h : Fin K)
    (d : PinnedShiftIndex h → ℕ) : extendPinnedDivisorTuple h d h = 1 := by
  simp [extendPinnedDivisorTuple]

@[simp] theorem extendPinnedDivisorTuple_at_other {K : ℕ} (h : Fin K)
    (d : PinnedShiftIndex h → ℕ) (i : PinnedShiftIndex h) :
    extendPinnedDivisorTuple h d i.val = d i := by
  simp only [extendPinnedDivisorTuple, dif_neg i.property]
  rfl

theorem sourceAnalyticSelbergCoefficient_extend_eq_pinned
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (LD LE : ℝ) (d e : PinnedShiftIndex h → ℕ) :
    (sourceAnalyticSelbergCoefficient S F G LD LE
      (extendPinnedDivisorTuple h d) (extendPinnedDivisorTuple h e) : ℂ) =
      pinnedSourceSelbergCoefficient S F G h LD LE d e := by
  rw [sourceAnalyticSelbergCoefficient_eq_pinnedFace S F G h LD LE _ _
    (extendPinnedDivisorTuple_at_pin h d) (extendPinnedDivisorTuple_at_pin h e)]
  simp only [extendPinnedDivisorTuple_at_other]

theorem sourceAnalyticSelbergCoefficient_extend_ne_zero
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (LD LE : ℝ) (d e : PinnedShiftIndex h → ℕ)
    (hne : pinnedSourceSelbergCoefficient S F G h LD LE d e ≠ 0) :
    sourceAnalyticSelbergCoefficient S F G LD LE
      (extendPinnedDivisorTuple h d) (extendPinnedDivisorTuple h e) ≠ 0 := by
  intro hz
  apply hne
  rw [← sourceAnalyticSelbergCoefficient_extend_eq_pinned S F G h LD LE d e, hz,
    Complex.ofReal_zero]

theorem pinnedSourceSelbergCoefficient_nonzero_support
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) {LD : ℝ} (hLD : 0 < LD) {Y p₀ : ℕ} (hY : 1 < Y) (hp₀ : 0 < p₀)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀)
    (d e : PinnedShiftIndex h → ℕ)
    (hne : pinnedSourceSelbergCoefficient S F G h LD (Real.log Y) d e ≠ 0) :
    ∀ i, Squarefree (d i) ∧ Squarefree (e i) ∧ d i < p₀ ∧ e i ≤ Y := by
  have hfull := sourceAnalyticSelbergCoefficient_extend_ne_zero S F G h LD (Real.log Y) d e hne
  have hsq := sourceAnalyticSelbergCoefficient_nonzero_squarefree S F G LD (Real.log Y) _ _ hfull
  have hfirst := sourceAnalyticSelbergCoefficient_first_coordinate_lt
    S F G hLD hFsupport hp₀ hD _ _ hfull
  have hcomp := sourceAnalyticSelbergCoefficient_companion_coordinate_le
    S F G LD hY hGsupport _ _ hfull
  intro i
  have hout : Squarefree (extendPinnedDivisorTuple h d i.val) ∧
      Squarefree (extendPinnedDivisorTuple h e i.val) ∧
      extendPinnedDivisorTuple h d i.val < p₀ ∧ extendPinnedDivisorTuple h e i.val ≤ Y :=
    ⟨(hsq i.val).1, (hsq i.val).2, hfirst i.val, hcomp i.val⟩
  simpa only [extendPinnedDivisorTuple_at_other] using hout

end

end Erdos4b
