import Wikipedia.SzemeredisTheorem.Transference.APCut
import Wikipedia.SzemeredisTheorem.Transference.APSimplexCut
import Wikipedia.GreenTao.Transference.BoxNorm
import Wikipedia.GreenTao.Transference.StrongLinearForms

/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Reindex a deleted Boolean cube by the canonical `Fin n` enumeration of
the coordinates other than `j`. -/
noncomputable def deletedCubeEquiv
    {n : ℕ} (j : Fin (n + 1)) :
    (Fin n → Bool) ≃ DeletedCube (n + 1) j :=
  Equiv.arrowCongr (finSuccAboveEquiv j) (Equiv.refl Bool)

@[simp]
theorem deletedCubeEquiv_apply_succAbove
    {n : ℕ} (j : Fin (n + 1))
    (ω : Fin n → Bool) (t : Fin n) :
    deletedCubeEquiv j ω (finSuccAboveEquiv j t) = ω t := by
  simp [deletedCubeEquiv]

/-- Extend a Boolean selector on the forms belonging to the face `j` by
`false` on every other face. -/
def faceLinearFormsExponent {k : ℕ} (j : Fin k)
    (e : BooleanCube (DeletedCube k j)) :
    LinearFormsExponent k :=
  fun j' ω =>
    if h : j' = j then e (h ▸ ω) else false

@[simp]
theorem faceLinearFormsExponent_same
    {k : ℕ} (j : Fin k)
    (e : BooleanCube (DeletedCube k j))
    (ω : DeletedCube k j) :
    faceLinearFormsExponent j e j ω = e ω := by
  simp [faceLinearFormsExponent]

/-- The family of majorant factors on one fixed CFZ face. -/
def faceFactorFamily (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) :
    DeletedCube k j → CubePoint k N → ℝ :=
  fun ω x => ν (apLinearForm k N j ω x)

/-- Selecting a subproduct of one face agrees with selecting the
corresponding subproduct of the full CFZ system. -/
theorem faceSelectedProduct_eq_linearFormsProduct
    (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) (e : BooleanCube (DeletedCube k j))
    (x : CubePoint k N) :
    cubeSelectedProduct
        (fun ω => faceFactorFamily k N ν j ω x) e =
      linearFormsProduct k N ν
        (faceLinearFormsExponent j e) x := by
  rw [linearFormsProduct, Fintype.prod_eq_single j]
  · simp [cubeSelectedProduct, faceFactorFamily,
      faceLinearFormsExponent]
  · intro j' hj'
    apply Fintype.prod_eq_one
    intro ω
    simp [faceLinearFormsExponent, hj']

/-- The full linear-forms condition restricts to the Boolean subproduct
condition on any one face. -/
theorem HasLinearFormsCondition.hasFaceBooleanSubproductCondition
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η)
    (j : Fin k) :
    HasBooleanSubproductCondition
      (faceFactorFamily k N ν j) η := by
  intro e
  have hfun :
      (fun x => cubeSelectedProduct
        (fun ω => faceFactorFamily k N ν j ω x) e) =
      linearFormsProduct k N ν
        (faceLinearFormsExponent j e) := by
    funext x
    exact faceSelectedProduct_eq_linearFormsProduct
      k N ν j e x
  rw [hfun]
  exact h (faceLinearFormsExponent j e)

/-- The centered product over all forms on one face. -/
def faceCenteredProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) (x : CubePoint k N) : ℝ :=
  ∏ ω : DeletedCube k j,
    (ν (apLinearForm k N j ω x) - 1)

/-- A quantitative linear-forms condition bounds the centered moment on
each individual face. -/
theorem HasLinearFormsCondition.abs_mean_faceCenteredProduct_le
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η)
    (j : Fin k) :
    |mean (faceCenteredProduct k N ν j)| ≤
      (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η := by
  change
    |mean (fun x =>
      centeredProduct
        (fun ω => faceFactorFamily k N ν j ω x))| ≤ _
  exact abs_mean_centeredProduct_le_two_pow
    (h.hasFaceBooleanSubproductCondition j)

/-- After inserting the irrelevant coordinate `j` and canonically
reindexing the deleted cube, a face form is the expected weighted coordinate
sum. -/
theorem apLinearForm_insertNth_deletedCubeEquiv
    (n N : ℕ) (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → Bool → ZMod N)
    (ω : Fin n → Bool) :
    apLinearForm (n + 1) N j (deletedCubeEquiv j ω)
        (Fin.insertNth j a y) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t (ω t)) := by
  unfold apLinearForm
  symm
  exact Fintype.sum_equiv (finSuccAboveEquiv j)
    (fun t : Fin n =>
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * y t (ω t)))
    (fun i : {i : Fin (n + 1) // i ≠ j} =>
      ((((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) *
        ((Fin.insertNth j a y :
          Fin (n + 1) → Bool → ZMod N) i.1)
          (deletedCubeEquiv j ω i)))
    (fun t => by simp)

/-- The centered product on a fixed face, after deleting the irrelevant
coordinate, is a weighted cube-vertex product on `Fin n`. -/
theorem faceCenteredProduct_insertNth
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → Bool → ZMod N) :
    faceCenteredProduct (n + 1) N ν j
        (Fin.insertNth j a y) =
      ∏ ω : Fin n → Bool,
        (ν (∑ t : Fin n,
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t (ω t))) - 1) := by
  unfold faceCenteredProduct
  apply Fintype.prod_equiv (deletedCubeEquiv j).symm
  intro ω
  have hform :
      apLinearForm (n + 1) N j ω
          (Fin.insertNth j a y) =
        ∑ t : Fin n,
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) *
              y t ((deletedCubeEquiv j).symm ω t)) := by
    simpa using
      apLinearForm_insertNth_deletedCubeEquiv
        n N j a y ((deletedCubeEquiv j).symm ω)
  rw [hform]

/-- Averaging a face centered product discards its irrelevant coordinate and
leaves the weighted cube-vertex average. -/
theorem mean_faceCenteredProduct_eq_weightedCube
    (n N : ℕ) [NeZero N] (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    mean (faceCenteredProduct (n + 1) N ν j) =
      mean (fun y : Fin n → Bool → ZMod N =>
        ∏ ω : Fin n → Bool,
          (ν (∑ t : Fin n,
            ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
              ZMod N) * y t (ω t))) - 1)) := by
  calc
    mean (faceCenteredProduct (n + 1) N ν j) =
        mean₂ (fun a : Bool → ZMod N =>
          fun y : Fin n → Bool → ZMod N =>
            faceCenteredProduct (n + 1) N ν j
              (Fin.insertNth j a y)) :=
      mean_insertNth n j _
    _ = mean (fun _a : Bool → ZMod N =>
          mean (fun y : Fin n → Bool → ZMod N =>
            ∏ ω : Fin n → Bool,
              (ν (∑ t : Fin n,
                ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
                  ZMod N) * y t (ω t))) - 1))) := by
      unfold mean₂
      apply congrArg mean
      funext a
      apply congrArg mean
      funext y
      exact faceCenteredProduct_insertNth n N ν j a y
    _ = mean (fun y : Fin n → Bool → ZMod N =>
          ∏ ω : Fin n → Bool,
            (ν (∑ t : Fin n,
              ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
                ZMod N) * y t (ω t))) - 1)) := by
      apply mean_const

/-- Apply one additive automorphism to both endpoints in every
coordinate. -/
def endpointScalingEquiv
    {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : Fin n → G ≃+ G) :
    (Fin n → Bool → G) ≃ (Fin n → Bool → G) where
  toFun x i b := e i (x i b)
  invFun x i b := (e i).symm (x i b)
  left_inv x := by
    funext i b
    exact (e i).symm_apply_apply (x i b)
  right_inv x := by
    funext i b
    exact (e i).apply_symm_apply (x i b)

@[simp]
theorem endpointScalingEquiv_apply
    {G : Type*} [AddCommGroup G] {n : ℕ}
    (e : Fin n → G ≃+ G)
    (x : Fin n → Bool → G) (i : Fin n) (b : Bool) :
    endpointScalingEquiv e x i b = e i (x i b) :=
  rfl

/-- Coordinatewise additive automorphisms transport a weighted cube mean to
the ordinary coordinate-sum cube mean. -/
theorem mean_weightedCube_eq_cubeFunctionMean
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (e : Fin n → G ≃+ G) (h : G → ℝ) :
    mean (fun x : Fin n → Bool → G =>
      ∏ ω : Fin n → Bool,
        h (∑ i, e i (x i (ω i)))) =
      cubeFunctionMean n
        (fun y : Fin n → G => h (∑ i, y i)) := by
  unfold cubeFunctionMean mean
  apply Fintype.expect_equiv (endpointScalingEquiv e)
  intro x
  apply Finset.prod_congr rfl
  intro ω _
  congr 1

/-- Under the AP factorial coprimality hypothesis, the centered face moment
is exactly the ordinary box moment of the centered majorant composed with
coordinate sum. -/
theorem mean_faceCenteredProduct_eq_boxMoment
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial n))
    (ν : ZMod N → ℝ) (j : Fin (n + 1)) :
    mean (faceCenteredProduct (n + 1) N ν j) =
      boxMoment n (fun y : Fin n → ZMod N =>
        ν (∑ i, y i) - 1) := by
  calc
    mean (faceCenteredProduct (n + 1) N ν j) =
        mean (fun y : Fin n → Bool → ZMod N =>
          ∏ ω : Fin n → Bool,
            (ν (∑ t : Fin n,
              ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
                ZMod N) * y t (ω t))) - 1)) :=
      mean_faceCenteredProduct_eq_weightedCube n N ν j
    _ = cubeFunctionMean n
          (fun y : Fin n → ZMod N =>
            ν (∑ i, y i) - 1) := by
      simpa using
        mean_weightedCube_eq_cubeFunctionMean n
          (fun t => apFaceScalingEquiv hN j t)
          (fun z => ν z - 1)
    _ = cubeMean n
          (fun y : Fin n → ZMod N =>
            ν (∑ i, y i) - 1) :=
      cubeFunctionMean_eq_cubeMean _ _
    _ = boxMoment n
          (fun y : Fin n → ZMod N =>
            ν (∑ i, y i) - 1) :=
      (boxMoment_eq_cubeMean _ _).symm

/-- A deleted `n`-dimensional Boolean cube has `2 ^ n` vertices. -/
theorem card_deletedCube
    {n : ℕ} (j : Fin (n + 1)) :
    Fintype.card (DeletedCube (n + 1) j) = 2 ^ n := by
  calc
    Fintype.card (DeletedCube (n + 1) j) =
        Fintype.card (Fin n → Bool) :=
      Fintype.card_congr (deletedCubeEquiv j).symm
    _ = 2 ^ n := by
      simp [Fintype.card_bool]

/-- The linear-forms condition supplies the box-moment estimate required by
generalized von Neumann. -/
theorem HasLinearFormsCondition.abs_boxMoment_centeredSum_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition (n + 1) N ν η)
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) :
    |boxMoment n (fun y : Fin n → ZMod N =>
      ν (∑ i, y i) - 1)| ≤
        (2 : ℝ) ^ (2 ^ n) * η := by
  have hface := h.abs_mean_faceCenteredProduct_le j
  rw [mean_faceCenteredProduct_eq_boxMoment n N hN ν j,
    card_deletedCube] at hface
  exact hface

/-- Powered cut-correlation estimate obtained by composing generalized von
Neumann with the fixed-face linear-forms bound. -/
theorem HasLinearFormsCondition.abs_cutCorrelation_pow_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition (n + 2) N ν η)
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (u : CutTestFamily (ZMod N) (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
        (2 ^ (n + 1)) ≤
      (2 : ℝ) ^ (2 ^ (n + 1)) * η := by
  let j : Fin (n + 2) := 0
  have hvn :=
    abs_cutCorrelation_pow_le_boxMoment
      n ν (fun _ => 1) u hu
  have hbox :=
    h.abs_boxMoment_centeredSum_le hN j
  calc
    |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
          (2 ^ (n + 1)) ≤
        boxMoment (n + 1)
          (fun x : Fin (n + 1) → ZMod N =>
            ν (∑ i, x i) - (fun _ => (1 : ℝ)) (∑ i, x i)) :=
      hvn
    _ = boxMoment (n + 1)
          (fun x : Fin (n + 1) → ZMod N =>
            ν (∑ i, x i) - 1) := by
      rfl
    _ ≤ |boxMoment (n + 1)
          (fun x : Fin (n + 1) → ZMod N =>
            ν (∑ i, x i) - 1)| :=
      le_abs_self _
    _ ≤ (2 : ℝ) ^ (2 ^ (n + 1)) * η :=
      hbox

/-- Quantitative strong linear-forms conclusion in cut-discrepancy form.
The displayed power comparison is the explicit parameter conversion from
the linear-forms error to the requested cut error. -/
theorem HasLinearFormsCondition.cutDiscrepancyLe_one
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (h : HasLinearFormsCondition (n + 2) N ν η)
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (hε : 0 ≤ ε)
    (hηε :
      (2 : ℝ) ^ (2 ^ (n + 1)) * η ≤
        ε ^ (2 ^ (n + 1))) :
    CutDiscrepancyLe (n + 1) ν (fun _ => 1) ε := by
  intro u hu0 hu1
  have hu : IsAbsBoundedCutTest u :=
    (show IsBoundedCutTest u from ⟨hu0, hu1⟩).isAbsBounded
  have hpow :
      |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
          (2 ^ (n + 1)) ≤
        ε ^ (2 ^ (n + 1)) :=
    (h.abs_cutCorrelation_pow_le hN u hu).trans hηε
  exact le_of_pow_le_pow_left₀
    (pow_ne_zero _ two_ne_zero) hε hpow

end Wikipedia.SzemeredisTheorem
