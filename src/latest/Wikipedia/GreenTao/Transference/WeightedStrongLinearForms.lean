import Wikipedia.GreenTao.Transference.FaceMoments

/-!
# Weighted endpoint of the strong linear-forms argument

The CFZ densification proof applies Cauchy--Schwarz repeatedly to a
centered factor on one simplex face.  At the final doubled stage, every
remaining relatively bounded factor has been replaced by either its
majorant or by one.  The resulting expression is

* the product of all centered copies of the selected face; times
* an arbitrary Boolean-selected subproduct of the other CFZ forms.

This file proves the exact quantitative linear-forms estimate for that
endpoint.  The still-missing recursive Cauchy--Schwarz bridge belongs in
the same module after this algebraic target.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Replace the selector on one CFZ face while retaining every selector on
the other faces. -/
def overwriteFaceExponent
    {k : ℕ} (j : Fin k)
    (face : BooleanCube (DeletedCube k j))
    (other : LinearFormsExponent k) :
    LinearFormsExponent k :=
  fun i ω =>
    if h : i = j then face (h ▸ ω) else other i ω

@[simp]
theorem overwriteFaceExponent_same
    {k : ℕ} (j : Fin k)
    (face : BooleanCube (DeletedCube k j))
    (other : LinearFormsExponent k)
    (ω : DeletedCube k j) :
    overwriteFaceExponent j face other j ω = face ω := by
  simp [overwriteFaceExponent]

theorem overwriteFaceExponent_other
    {k : ℕ} (j i : Fin k) (hij : i ≠ j)
    (face : BooleanCube (DeletedCube k j))
    (other : LinearFormsExponent k)
    (ω : DeletedCube k i) :
    overwriteFaceExponent j face other i ω =
      other i ω := by
  simp [overwriteFaceExponent, hij]

/-- If the retained selector is false on the distinguished face, its
product times a selected product on that face is the product selected by
the overwritten exponent. -/
theorem faceSelectedProduct_mul_linearFormsProduct_eq_overwrite
    {k N : ℕ}
    (ν : ZMod N → ℝ) (j : Fin k)
    (face : BooleanCube (DeletedCube k j))
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false)
    (x : CubePoint k N) :
    cubeSelectedProduct
          (fun ω => faceFactorFamily k N ν j ω x) face *
        linearFormsProduct k N ν other x =
      linearFormsProduct k N ν
        (overwriteFaceExponent j face other) x := by
  rw [faceSelectedProduct_eq_linearFormsProduct]
  unfold linearFormsProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ω _hω
  by_cases hij : i = j
  · subst i
    simp [faceLinearFormsExponent, overwriteFaceExponent,
      hother]
  · simp [faceLinearFormsExponent, overwriteFaceExponent, hij]

/-- Pointwise expansion of the weighted centered-face endpoint into
ordinary CFZ subproducts. -/
theorem faceCenteredProduct_mul_linearFormsProduct_eq_sum
    {k N : ℕ}
    (ν : ZMod N → ℝ) (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false)
    (x : CubePoint k N) :
    faceCenteredProduct k N ν j x *
        linearFormsProduct k N ν other x =
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          linearFormsProduct k N ν
            (overwriteFaceExponent j face other) x := by
  rw [faceCenteredProduct]
  change
    centeredProduct
          (fun ω : DeletedCube k j =>
            faceFactorFamily k N ν j ω x) *
        linearFormsProduct k N ν other x =
      _
  rw [centeredProduct_eq_sum_sign_mul_selected,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro face _hface
  rw [mul_assoc]
  apply congrArg (fun z : ℝ => cubeSign face * z)
  exact
    faceSelectedProduct_mul_linearFormsProduct_eq_overwrite
      ν j face other hother x

/-- Averaged form of the exact endpoint expansion. -/
theorem mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
    {k N : ℕ} [NeZero N]
    (ν : ZMod N → ℝ) (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false) :
    mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x) =
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          mean (linearFormsProduct k N ν
            (overwriteFaceExponent j face other)) := by
  calc
    mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x) =
        mean (fun x =>
          ∑ face : BooleanCube (DeletedCube k j),
            cubeSign face *
              linearFormsProduct k N ν
                (overwriteFaceExponent j face other) x) := by
      apply congrArg mean
      funext x
      exact
        faceCenteredProduct_mul_linearFormsProduct_eq_sum
          ν j other hother x
    _ =
        ∑ face : BooleanCube (DeletedCube k j),
          mean (fun x =>
            cubeSign face *
              linearFormsProduct k N ν
                (overwriteFaceExponent j face other) x) :=
      mean_fintype_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro face _hface
      exact mean_smul (cubeSign face) _

/-- Quantitative weighted strong-linear-forms endpoint.

An arbitrary fixed subproduct of all other CFZ faces may accompany the
centered cube on `j`; the same `2^(2^(k-1))` inclusion--exclusion loss as
for the unweighted centered face suffices. -/
theorem HasLinearFormsCondition.abs_mean_faceCenteredProduct_mul_le
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false) :
    |mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x)| ≤
      (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η := by
  rw [mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
    ν j other hother]
  have hsign :
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face = 0 :=
    sum_cubeSign_eq_zero
  rw [sum_mul_eq_sum_mul_sub_one_of_sum_eq_zero
    (fun face : BooleanCube (DeletedCube k j) =>
      cubeSign face)
    (fun face =>
      mean (linearFormsProduct k N ν
        (overwriteFaceExponent j face other)))
    hsign]
  calc
    |∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          (mean (linearFormsProduct k N ν
            (overwriteFaceExponent j face other)) - 1)| ≤
        ∑ face : BooleanCube (DeletedCube k j),
          |cubeSign face *
            (mean (linearFormsProduct k N ν
              (overwriteFaceExponent j face other)) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _face : BooleanCube (DeletedCube k j), η := by
      apply Finset.sum_le_sum
      intro face _hface
      simpa [abs_mul] using
        hLF (overwriteFaceExponent j face other)
    _ =
        (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η := by
      simp [BooleanCube, Fintype.card_bool]

end Wikipedia.SzemeredisTheorem
