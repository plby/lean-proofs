import ErdosProblems.Erdos1148.BasicLemmaArithmetic

/-!
# Changes of variables for binary quadratic forms

This supplies the integral and real special-linear actions used to define the
form orbits in the Duke–ELMV argument. Coefficients use the same triple
convention as the Erdős 1148 reduction.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def evalForm {R : Type*} [CommRing R] (t : R × R × R) (x y : R) : R :=
  t.1 * x ^ 2 + t.2.1 * x * y + t.2.2 * y ^ 2

lemma eq_of_evalForm_eq {R : Type*} [CommRing R] {t u : R × R × R}
    (h : ∀ x y, evalForm t x y = evalForm u x y) : t = u := by
  have ha : t.1 = u.1 := by simpa only [evalForm, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_one, mul_zero, add_zero] using h 1 0
  have hc : t.2.2 = u.2.2 := by simpa only [evalForm, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_one, mul_zero, zero_add] using h 0 1
  have hb : t.2.1 = u.2.1 := by
    have hsum := h 1 1
    simp only [evalForm, one_pow, mul_one] at hsum
    linear_combination hsum - ha - hc
  exact Prod.ext ha (Prod.ext hb hc)

/-- Coefficients after substitution by a two-by-two matrix. -/
def transform {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (t : R × R × R) : R × R × R :=
  (t.1 * M 0 0 ^ 2 + t.2.1 * M 0 0 * M 1 0 + t.2.2 * M 1 0 ^ 2,
    2 * t.1 * M 0 0 * M 0 1 + t.2.1 * (M 0 0 * M 1 1 + M 0 1 * M 1 0) +
      2 * t.2.2 * M 1 0 * M 1 1,
    t.1 * M 0 1 ^ 2 + t.2.1 * M 0 1 * M 1 1 + t.2.2 * M 1 1 ^ 2)

lemma evalForm_transform {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) (x y : R) :
    evalForm (transform M t) x y =
      evalForm t (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) := by
  dsimp [evalForm, transform]
  ring

lemma transform_one {R : Type*} [CommRing R] (t : R × R × R) :
    transform 1 t = t := by
  apply eq_of_evalForm_eq
  intro x y
  simp [evalForm_transform]

lemma transform_mul {R : Type*} [CommRing R]
    (M N : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) :
    transform (M * N) t = transform N (transform M t) := by
  apply eq_of_evalForm_eq
  intro x y
  simp only [evalForm_transform, Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> ring

lemma discr_transform {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) :
    discr (transform M t) = M.det ^ 2 * discr t := by
  dsimp [discr, transform]
  rw [Matrix.det_fin_two]
  ring

def formAction {R : Type*} [CommRing R] (g : SL(2, R)) (t : R × R × R) : R × R × R :=
  transform (g⁻¹ : SL(2, R)) t

lemma formAction_one {R : Type*} [CommRing R] (t : R × R × R) :
    formAction 1 t = t := by
  simp only [formAction, inv_one, Matrix.SpecialLinearGroup.coe_one, transform_one]

lemma formAction_mul {R : Type*} [CommRing R] (g h : SL(2, R)) (t : R × R × R) :
    formAction (g * h) t = formAction g (formAction h t) := by
  simp only [formAction, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, transform_mul]

lemma discr_formAction {R : Type*} [CommRing R] (g : SL(2, R)) (t : R × R × R) :
    discr (formAction g t) = discr t := by
  rw [formAction, discr_transform, Matrix.SpecialLinearGroup.det_coe, one_pow, one_mul]

lemma formAction_injective {R : Type*} [CommRing R] (g : SL(2, R)) :
    Function.Injective (formAction g) := by
  intro t u h
  have heq := congrArg (formAction g⁻¹) h
  simpa only [← formAction_mul, inv_mul_cancel, formAction_one] using heq

def transformLinear {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (R × R × R) →ₗ[R] (R × R × R) where
  toFun := transform M
  map_add' t u := by ext <;> dsimp [transform] <;> ring
  map_smul' s t := by ext <;> dsimp [transform] <;> ring

def formActionEquiv {R : Type*} [CommRing R] (g : SL(2, R)) :
    (R × R × R) ≃ₗ[R] (R × R × R) :=
  { transformLinear (g⁻¹ : SL(2, R)) with
    invFun := formAction g⁻¹
    left_inv := fun t => by
      change formAction g⁻¹ (formAction g t) = t
      rw [← formAction_mul, inv_mul_cancel, formAction_one]
    right_inv := fun t => by
      change formAction g (formAction g⁻¹ t) = t
      rw [← formAction_mul, mul_inv_cancel, formAction_one] }

lemma formAction_sub {R : Type*} [CommRing R] (g : SL(2, R)) (t u : R × R × R) :
    formAction g (t - u) = formAction g t - formAction g u :=
  (formActionEquiv g).map_sub t u

lemma pairing_formAction {R : Type*} [CommRing R] (g : SL(2, R)) (t u : R × R × R) :
    pairing (formAction g t) (formAction g u) = pairing t u := by
  have h := discr_formAction g (t - u)
  rw [formAction_sub, discr_sub, discr_sub, discr_formAction, discr_formAction] at h
  linear_combination -h

/-- Ordered pairs with fixed individual discriminants and fixed mixed coefficient. -/
abbrev FormPair (R : Type*) [CommRing R] (d ℓ : R) :=
  {p : (R × R × R) × (R × R × R) //
    discr p.1 = d ∧ discr p.2 = d ∧ pairing p.1 p.2 = ℓ}

def pairAction {R : Type*} [CommRing R] {d ℓ : R}
    (g : SL(2, R)) (p : FormPair R d ℓ) : FormPair R d ℓ :=
  ⟨(formAction g p.1.1, formAction g p.1.2), by
    simpa only [discr_formAction, pairing_formAction] using p.2⟩

instance formPairMulAction {R : Type*} [CommRing R] {d ℓ : R} :
    MulAction SL(2, R) (FormPair R d ℓ) where
  smul := pairAction
  one_smul p := by
    apply Subtype.ext
    exact Prod.ext (formAction_one _) (formAction_one _)
  mul_smul g h p := by
    apply Subtype.ext
    exact Prod.ext (formAction_mul g h _) (formAction_mul g h _)

/-- The integral diagonal orbits counted in the basic lemma. -/
abbrev IntegralPairOrbits (d ℓ : ℤ) :=
  Quotient (MulAction.orbitRel SL(2, ℤ) (FormPair ℤ d ℓ))

end Erdos1148.DukeArithmetic
