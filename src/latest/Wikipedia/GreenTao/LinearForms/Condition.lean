import Wikipedia.SzemeredisTheorem.LinearForms.Basic

/-!
# Elementary properties of the linear-forms condition

This file records the normalization and positivity facts that every later
transference estimate uses.  The deep input—that the W-tricked Selberg
majorant satisfies this condition—is isolated in the sieve layer.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Select no factors from the CFZ system. -/
def emptyLinearFormsExponent (k : ℕ) : LinearFormsExponent k :=
  fun _ _ => false

@[simp]
theorem linearFormsProduct_empty (k N : ℕ) (ν : ZMod N → ℝ)
    (x : CubePoint k N) :
    linearFormsProduct k N ν (emptyLinearFormsExponent k) x = 1 := by
  simp [linearFormsProduct, emptyLinearFormsExponent]

theorem linearFormsProduct_nonneg {k N : ℕ}
    {ν : ZMod N → ℝ} (hν : ∀ y, 0 ≤ ν y)
    (e : LinearFormsExponent k) (x : CubePoint k N) :
    0 ≤ linearFormsProduct k N ν e x := by
  apply Finset.prod_nonneg
  intro j
  simp only [Finset.mem_univ, forall_const]
  apply Finset.prod_nonneg
  intro ω
  simp only [Finset.mem_univ, forall_const]
  split
  · exact hν _
  · exact zero_le_one

theorem mean_linearFormsProduct_nonneg {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} (hν : ∀ y, 0 ≤ ν y)
    (e : LinearFormsExponent k) :
    0 ≤ mean (linearFormsProduct k N ν e) :=
  mean_nonneg (linearFormsProduct_nonneg hν e)

/-- Testing the empty subproduct forces the error tolerance to be
nonnegative. -/
theorem HasLinearFormsCondition.error_nonneg {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η) :
    0 ≤ η := by
  have he := h (emptyLinearFormsExponent k)
  have hproduct :
      linearFormsProduct k N ν (emptyLinearFormsExponent k) =
        fun _ => 1 := by
    funext x
    exact linearFormsProduct_empty k N ν x
  rw [hproduct] at he
  simpa using he

/-- The constant-one majorant satisfies the condition with every
nonnegative error tolerance. -/
theorem hasLinearFormsCondition_one {k N : ℕ} [NeZero N]
    {η : ℝ} (hη : 0 ≤ η) :
    HasLinearFormsCondition k N (fun _ => 1) η := by
  intro e
  have hproduct :
      linearFormsProduct k N (fun _ => 1) e = fun _ => 1 := by
    funext x
    simp [linearFormsProduct]
  rw [hproduct]
  simpa using hη

/-- At zero tolerance, the quantitative condition says exactly that every
subproduct average is one. -/
theorem hasLinearFormsCondition_zero_iff {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} :
    HasLinearFormsCondition k N ν 0 ↔
      ∀ e : LinearFormsExponent k,
        mean (linearFormsProduct k N ν e) = 1 := by
  constructor
  · intro h e
    have habs : |mean (linearFormsProduct k N ν e) - 1| = 0 :=
      le_antisymm (h e) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h e
    rw [h e, sub_self, abs_zero]

end Wikipedia.SzemeredisTheorem
