import Wikipedia.SzemeredisTheorem.LinearForms.Basic

/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A nondependent index for the CFZ family: a deleted coordinate together
with a vertex of the remaining Boolean cube. -/
abbrev CFZFormIndex (k : ℕ) :=
  Σ j : Fin k, DeletedCube k j

/-- The doubled variables used by the CFZ forms. -/
abbrev CFZVariable (k : ℕ) :=
  Fin k × Bool

/-- The integer coefficient of a doubled variable in a CFZ form. -/
def cfzCoefficient {k : ℕ} (q : CFZFormIndex k)
    (v : CFZVariable k) : ℤ :=
  if h : v.1 ≠ q.1 then
    if v.2 = q.2 ⟨v.1, h⟩ then
      (v.1 : ℤ) - (q.1 : ℤ)
    else
      0
  else
    0

/-- Evaluate the integer coefficient vector in `ZMod N` on a doubled
variable vector. -/
noncomputable def cfzCoefficientEval (k N : ℕ)
    (q : CFZFormIndex k) (x : CubePoint k N) : ZMod N :=
  ∑ v : CFZVariable k,
    (cfzCoefficient q v : ZMod N) * x v.1 v.2

@[simp]
theorem cfzCoefficient_deleted {k : ℕ} (q : CFZFormIndex k) (b : Bool) :
    cfzCoefficient q (q.1, b) = 0 := by
  simp [cfzCoefficient]

@[simp]
theorem cfzCoefficient_selected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) =
      (i.1 : ℤ) - (q.1 : ℤ) := by
  simp [cfzCoefficient, i.2]

theorem cfzCoefficient_unselected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) (b : Bool)
    (hb : b ≠ q.2 i) :
    cfzCoefficient q (i.1, b) = 0 := by
  simp [cfzCoefficient, i.2, hb]

/-- The coefficient-vector presentation evaluates to the original
`apLinearForm`. -/
theorem cfzCoefficientEval_eq_apLinearForm (k N : ℕ)
    (q : CFZFormIndex k) (x : CubePoint k N) :
    cfzCoefficientEval k N q x =
      apLinearForm k N q.1 q.2 x := by
  rcases q with ⟨j, ω⟩
  classical
  rw [cfzCoefficientEval, Fintype.sum_prod_type]
  let g : Fin k → ZMod N := fun i =>
    ∑ b : Bool,
      (cfzCoefficient ⟨j, ω⟩ (i, b) : ZMod N) * x i b
  change (∑ i, g i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin k => i ≠ j) g]
  have hnot : (∑ i : {i : Fin k // ¬ i ≠ j}, g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.1 = j := not_ne_iff.mp i.2
    simp [g, cfzCoefficient, hi]
  rw [hnot, add_zero]
  apply Fintype.sum_congr
  intro i
  cases hω : ω i <;>
    simp [g, cfzCoefficient, i.2, hω]

theorem cfzCoefficient_selected_ne_zero {k : ℕ}
    (q : CFZFormIndex k) (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) ≠ 0 := by
  rw [cfzCoefficient_selected]
  apply sub_ne_zero.mpr
  intro h
  apply i.2
  apply Fin.ext
  exact_mod_cast h

/-- For `k ≥ 2`, every CFZ form has a nonzero integer coefficient. -/
theorem exists_cfzCoefficient_ne_zero {k : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    ∃ v : CFZVariable k, cfzCoefficient q v ≠ 0 := by
  have hcard : 1 < Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ :=
    Fintype.exists_ne_of_one_lt_card hcard q.1
  let i' : {i : Fin k // i ≠ q.1} := ⟨i, hi⟩
  exact ⟨(i, q.2 i'), cfzCoefficient_selected_ne_zero q i'⟩

/-- Equivalently, the coefficient vector of every CFZ form is nonzero. -/
theorem cfzCoefficient_ne_zero {k : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    cfzCoefficient q ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_cfzCoefficient_ne_zero hk q
  intro hzero
  exact hv (congrFun hzero v)

/-- Distinct CFZ forms have a doubled variable which occurs in the second
form but not in the first. -/
theorem exists_cfzCoefficient_support_separating {k : ℕ}
    (q r : CFZFormIndex k) (hqr : q ≠ r) :
    ∃ v : CFZVariable k,
      cfzCoefficient q v = 0 ∧ cfzCoefficient r v ≠ 0 := by
  rcases q with ⟨j, ω⟩
  rcases r with ⟨j', ω'⟩
  by_cases hj : j = j'
  · subst j'
    have hω : ω ≠ ω' := by
      intro h
      subst ω'
      exact hqr rfl
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hω
    refine ⟨(i.1, ω' i), ?_, cfzCoefficient_selected_ne_zero ⟨j, ω'⟩ i⟩
    exact cfzCoefficient_unselected ⟨j, ω⟩ i (ω' i) (Ne.symm hi)
  · let i : {i : Fin k // i ≠ j'} := ⟨j, hj⟩
    refine ⟨(j, ω' i), cfzCoefficient_deleted ⟨j, ω⟩ (ω' i), ?_⟩
    exact cfzCoefficient_selected_ne_zero ⟨j', ω'⟩ i

/-- Two integer coefficient vectors are proportional when all their
two-by-two minors vanish.  For nonzero vectors this is equivalent to
proportionality over `ℚ`, while avoiding a choice of orientation or ratio. -/
def IntCoefficientProportional {ι : Type*}
    (c₁ c₂ : ι → ℤ) : Prop :=
  ∀ v w, c₁ v * c₂ w = c₁ w * c₂ v

/-- At the weakest bound ensuring that every individual form is nonzero, the
CFZ coefficient vectors are pairwise non-proportional. -/
theorem cfzCoefficients_pairwise_not_proportional {k : ℕ} (hk : 2 ≤ k) :
    Pairwise fun q r : CFZFormIndex k =>
      ¬ IntCoefficientProportional
        (cfzCoefficient q) (cfzCoefficient r) := by
  intro q r hqr hproportional
  obtain ⟨v, hqv, hrv⟩ :=
    exists_cfzCoefficient_support_separating q r hqr
  obtain ⟨w, hqw⟩ := exists_cfzCoefficient_ne_zero hk q
  have hminor := hproportional v w
  have hright :
      cfzCoefficient q w * cfzCoefficient r v ≠ 0 :=
    mul_ne_zero hqw hrv
  apply hright
  simpa [hqv] using hminor.symm

end Wikipedia.SzemeredisTheorem
