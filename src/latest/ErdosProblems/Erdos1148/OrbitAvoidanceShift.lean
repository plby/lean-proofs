import ErdosProblems.Erdos1148.ErgodicAvoidance

/-! # Restricting avoidance to a later block, and full measure when the target is null -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter

lemma finiteOrbitAvoidance_shift_block {X : Type*} {f : X → X} {U : Set X}
    {n k j : ℕ} (hj : j < k) {x : X} (hx : x ∈ finiteOrbitAvoidance f U (k * n)) :
    f^[j * n] x ∈ finiteOrbitAvoidance f U n := by
  intro m hm
  have hmn : m + j * n < k * n := by
    calc
      m + j * n < n + j * n := Nat.add_lt_add_right hm _
      _ = (j + 1) * n := by ring
      _ ≤ k * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
  simpa only [Function.iterate_add_apply] using hx (m + j * n) hmn

theorem ae_infiniteOrbitAvoidance_of_null {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ) {U : Set X} (hU : μ U = 0) :
    ∀ᵐ x ∂μ, x ∈ infiniteOrbitAvoidance f U := by
  have hae : ∀ᵐ x ∂μ, x ∉ U := by
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hU
  exact ae_all_iff.mpr (fun n => (hf.iterate n).quasiMeasurePreserving.ae hae)

theorem ae_finiteOrbitAvoidance_of_null {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → X} (hf : MeasurePreserving f μ μ) {U : Set X} (hU : μ U = 0) (n : ℕ) :
    ∀ᵐ x ∂μ, x ∈ finiteOrbitAvoidance f U n :=
  (ae_infiniteOrbitAvoidance_of_null hf hU).mono fun _ hx k _ => hx k

end Erdos1148.DukeArithmetic
