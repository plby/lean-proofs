/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLocalInverse
import Mathlib.Logic.Embedding.Basic

/-!
# Local composition after removing a pinned coordinate

The inclusion `e` identifies the available coordinates. The inverse
parameter is `v-1`, while the original coefficient parameter is `v`.
The local formula is exact, including the negative moved-prime entry.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {ι κ : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq κ]

open scoped Classical in
def localPinnedCoeffKernel (v : ℝ) (e : ι ↪ κ) (r : Option ι) (s : Option κ) : ℝ :=
  match r, s with
  | none, none => 1
  | none, some j => if ∃ i, e i = j then -(1 / (v - 1)) else 1
  | some i, _ => if s = some (e i) then v / (v - 1) else 0

theorem localPinnedCoeffKernel_eq_contraction {v : ℝ} (hv : v - 1 ≠ 0)
    (e : ι ↪ κ) (r : Option ι) (s : Option κ) :
    (∑ d, localInverseCoeff (v - 1) r d * localDivisorCoeff v (d.map e) s) =
      localPinnedCoeffKernel v e r s := by
  classical
  rw [sum_localInverseCoeff_mul]
  cases r with
  | none =>
    cases s with
    | none => simp [localDivisorCoeff, localPinnedCoeffKernel]
    | some j =>
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        simp [localDivisorCoeff, localPinnedCoeffKernel, e.injective.eq_iff]
        field_simp [hv]
        ring
      · have hne : ∀ i, j ≠ e i := fun i hi => hj ⟨i, hi.symm⟩
        simp [localDivisorCoeff, localPinnedCoeffKernel, hj, hne]
  | some i =>
    cases s with
    | none => simp [localDivisorCoeff, localPinnedCoeffKernel]
    | some j =>
      by_cases hij : j = e i <;> simp [localDivisorCoeff, localPinnedCoeffKernel, hij]

def localPinnedProfileKernel [Fintype κ] (v : ℝ) (e : ι ↪ κ)
    (r : Option ι) (s : Option κ) : ℝ :=
  localRowWeight (v - 1) r * localPinnedCoeffKernel v e r s / localRowWeight v s

omit [DecidableEq ι] in
theorem localPinnedProfileKernel_none_none [Fintype κ] (v : ℝ) (e : ι ↪ κ) :
    localPinnedProfileKernel v e none none = 1 := by
  simp [localPinnedProfileKernel, localRowWeight, localPinnedCoeffKernel]

omit [DecidableEq ι] in
theorem localPinnedProfileKernel_none_image [Fintype κ] (v : ℝ) (e : ι ↪ κ) (i : ι) :
    localPinnedProfileKernel v e none (some (e i)) =
      -(1 / ((v - 1) * (v - Fintype.card κ))) := by
  simp [localPinnedProfileKernel, localRowWeight, localPinnedCoeffKernel]
  ring

omit [DecidableEq ι] in
theorem localPinnedProfileKernel_none_missing [Fintype κ] (v : ℝ) (e : ι ↪ κ)
    (j : κ) (hj : ∀ i, e i ≠ j) :
    localPinnedProfileKernel v e none (some j) = 1 / (v - Fintype.card κ) := by
  simp [localPinnedProfileKernel, localRowWeight, localPinnedCoeffKernel, hj]

omit [DecidableEq ι] in
theorem localPinnedProfileKernel_some [Fintype κ]
    (hcard : Fintype.card κ = Fintype.card ι + 1) {v : ℝ}
    (hv : v - Fintype.card κ ≠ 0) (e : ι ↪ κ) (i : ι) (s : Option κ) :
    localPinnedProfileKernel v e (some i) s =
      if s = some (e i) then v / (v - 1) else 0 := by
  classical
  have hrow : v - 1 - Fintype.card ι = v - Fintype.card κ := by
    rw [hcard, Nat.cast_add, Nat.cast_one]
    ring
  by_cases hs : s = some (e i)
  · subst s
    simp only [localPinnedProfileKernel, localPinnedCoeffKernel, localRowWeight,
      if_true, hrow]
    exact mul_div_cancel_left₀ _ hv
  · simp [localPinnedProfileKernel, localPinnedCoeffKernel, hs]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.localPinnedCoeffKernel_eq_contraction
#print axioms Erdos4b.FGKMT.localPinnedProfileKernel_some
