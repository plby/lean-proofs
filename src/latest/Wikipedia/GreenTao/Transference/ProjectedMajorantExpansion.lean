import Wikipedia.GreenTao.Transference.FaceMoments
import Wikipedia.GreenTao.Transference.ProjectedMajorantMoments

/-!
# The AP-simplex projected majorant

Fix a colour `j` of the canonical `(n + 1)`-colour arithmetic-progression
simplex.  A point of the distinguished `j`-edge is written canonically as
`y : Fin n → ZMod N`.  Inserting `a : ZMod N` at coordinate `j` produces a
full simplex point.  The projected majorant is

```
ν'_j(y) = 𝔼 a, ∏ t, ν(L_{j.succAbove t}(insertNth j a y)),
```

the conditional average of all incident majorant edges other than colour
`j`.

Its square uses two independent values of the eliminated coordinate while
sharing `y`.  These are exactly the one-copy and two-copy subproducts of the
CFZ linear-forms system which choose respectively the `false` vertex and the
`false`/`true` vertices at coordinate `j`, keeping every other doubled
coordinate at `false`.  The unused `true` copies of the coordinates in `y`
are removed by an explicit finite coordinate equivalence below.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projection geometry -/

/-- The Boolean vertex used for colour `i` in the projected-majorant
expansion.  It chooses `b` at the eliminated coordinate `j` and the canonical
`false` copy at every other coordinate. -/
def apProjectionVertex
    {k : ℕ} (j i : Fin k) (b : Bool) :
    DeletedCube k i :=
  fun q => if q.1 = j then b else false

/-- The full one-copy simplex tuple selected from a doubled CFZ point:
start with all `false` coordinates and replace coordinate `j` by its `b`
copy. -/
def apProjectionTuple
    {k N : ℕ} (j : Fin k) (b : Bool)
    (x : CubePoint k N) :
    Fin k → ZMod N :=
  Function.update (fun i => x i false) j (x j b)

/-- A selected CFZ form is exactly the corresponding AP-simplex form on
the full tuple chosen by `apProjectionTuple`. -/
theorem apLinearForm_projectionVertex
    {k N : ℕ} (j i : Fin k)
    (b : Bool) (x : CubePoint k N) :
    apLinearForm k N i (apProjectionVertex j i b) x =
      apSimplexForm k N i
        (deleteCoordinate (apProjectionTuple j b x) i) := by
  unfold apLinearForm apSimplexForm
  apply Fintype.sum_congr
  intro q
  apply congrArg (fun z : ZMod N =>
    ((((q.1 : ℤ) - (i : ℤ) : ℤ) : ZMod N) * z))
  change
    x q.1 (if q.1 = j then b else false) =
      Function.update (fun r => x r false) j (x j b) q.1
  by_cases hq : q.1 = j
  · simp [hq]
  · simp [hq]

/-- In canonical deleted-face coordinates, `apProjectionTuple` is
literally insertion of the eliminated coordinate. -/
theorem apProjectionTuple_eq_insertNth
    {n N : ℕ} (j : Fin (n + 1)) (b : Bool)
    (x : CubePoint (n + 1) N) :
    apProjectionTuple j b x =
      Fin.insertNth j (x j b)
        (fun t => x (j.succAbove t) false) := by
  apply (Fin.eq_insertNth_iff).2
  constructor
  · simp [apProjectionTuple]
  · funext t
    rw [Fin.removeNth_apply]
    simp [apProjectionTuple]

/-- The two selected vertices are distinct whenever the colour is not the
eliminated colour. -/
theorem apProjectionVertex_false_ne_true
    {k : ℕ} (j i : Fin k) (hij : i ≠ j) :
    apProjectionVertex j i false ≠
      apProjectionVertex j i true := by
  intro h
  let q : {q : Fin k // q ≠ i} := ⟨j, Ne.symm hij⟩
  have hq := congrFun h q
  simp [apProjectionVertex, q] at hq

/-- Product of all AP-simplex majorant edges incident to the eliminated
coordinate, except the distinguished colour itself. -/
def apIncidentMajorantProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) : ℝ :=
  ∏ t : Fin n,
    ν (apSimplexForm (n + 1) N (j.succAbove t)
      (deleteCoordinate (Fin.insertNth j a y)
        (j.succAbove t)))

/-- The standard one-step AP-simplex projected majorant. -/
noncomputable def apProjectedMajorant
    (n N : ℕ) [NeZero N] (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  fun y => mean (fun a =>
    apIncidentMajorantProduct n N ν j a y)

/-- The corresponding product written directly with the existing
`faceFactorFamily` API. -/
def apProjectionFaceProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) (b : Bool)
    (x : CubePoint (n + 1) N) : ℝ :=
  ∏ t : Fin n,
    faceFactorFamily (n + 1) N ν (j.succAbove t)
      (apProjectionVertex j (j.succAbove t) b) x

/-- The explicit face product is the incident-edge product after selecting
one copy of the eliminated coordinate. -/
theorem apProjectionFaceProduct_eq_incidentMajorantProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) (b : Bool)
    (x : CubePoint (n + 1) N) :
    apProjectionFaceProduct n N ν j b x =
      apIncidentMajorantProduct n N ν j (x j b)
        (fun t => x (j.succAbove t) false) := by
  unfold apProjectionFaceProduct apIncidentMajorantProduct
  apply Fintype.prod_congr
  intro t
  rw [faceFactorFamily,
    apLinearForm_projectionVertex
      j (j.succAbove t),
    apProjectionTuple_eq_insertNth]

/-- Nonnegativity of the base majorant gives nonnegativity of every
incident-edge product. -/
theorem apIncidentMajorantProduct_nonneg
    {n N : ℕ} {ν : ZMod N → ℝ}
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) :
    0 ≤ apIncidentMajorantProduct n N ν j a y := by
  exact Finset.prod_nonneg fun t _ => hν _

/-- Nonnegativity descends through the conditional average defining the
projection. -/
theorem apProjectedMajorant_nonneg
    {n N : ℕ} [NeZero N] {ν : ZMod N → ℝ}
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (n + 1)) (y : Fin n → ZMod N) :
    0 ≤ apProjectedMajorant n N ν j y :=
  mean_nonneg fun a =>
    apIncidentMajorantProduct_nonneg hν j a y

/-! ## One-copy and two-copy selectors -/

/-- Select one projected copy: for each colour other than `j`, choose the
CFZ form using the `false` copy at coordinate `j`. -/
noncomputable def apProjectedOneCopyExponent
    (n : ℕ) (j : Fin (n + 1)) :
    LinearFormsExponent (n + 1) :=
  fun i ω =>
    if i = j then false
    else if ω = apProjectionVertex j i false then true else false

/-- Select two projected copies: for each colour other than `j`, choose both
CFZ forms obtained by using `false` and `true` at coordinate `j`. -/
noncomputable def apProjectedTwoCopyExponent
    (n : ℕ) (j : Fin (n + 1)) :
    LinearFormsExponent (n + 1) :=
  fun i ω =>
    if i = j then false
    else if
      ω = apProjectionVertex j i false ∨
        ω = apProjectionVertex j i true
    then true
    else false

/-- The one-copy selector evaluates to the explicit product of the selected
face factors. -/
theorem linearFormsProduct_oneCopy_eq_faceProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apProjectedOneCopyExponent n j) x =
      apProjectionFaceProduct n N ν j false x := by
  classical
  unfold apProjectionFaceProduct
  rw [linearFormsProduct, Fin.prod_univ_succAbove _ j]
  have hself :
      (∏ ω : DeletedCube (n + 1) j,
        if apProjectedOneCopyExponent n j j ω then
          ν (apLinearForm (n + 1) N j ω x)
        else 1) = 1 := by
    apply Fintype.prod_eq_one
    intro ω
    simp [apProjectedOneCopyExponent]
  rw [hself, one_mul]
  apply Fintype.prod_congr
  intro t
  let v :=
    apProjectionVertex j (j.succAbove t) false
  rw [Fintype.prod_eq_single v]
  · simp [apProjectedOneCopyExponent, v,
      faceFactorFamily, Fin.succAbove_ne]
  · intro ω hω
    simp [apProjectedOneCopyExponent, v,
      Fin.succAbove_ne, hω]

/-- The two-copy selector evaluates to the product of the two explicit face
products sharing all non-eliminated `false` coordinates. -/
theorem linearFormsProduct_twoCopy_eq_faceProducts
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apProjectedTwoCopyExponent n j) x =
      apProjectionFaceProduct n N ν j false x *
        apProjectionFaceProduct n N ν j true x := by
  classical
  unfold apProjectionFaceProduct
  rw [linearFormsProduct, Fin.prod_univ_succAbove _ j]
  have hself :
      (∏ ω : DeletedCube (n + 1) j,
        if apProjectedTwoCopyExponent n j j ω then
          ν (apLinearForm (n + 1) N j ω x)
        else 1) = 1 := by
    apply Fintype.prod_eq_one
    intro ω
    simp [apProjectedTwoCopyExponent]
  rw [hself, one_mul]
  calc
    (∏ t : Fin n,
        ∏ ω : DeletedCube (n + 1) (j.succAbove t),
          if apProjectedTwoCopyExponent n j
              (j.succAbove t) ω then
            ν (apLinearForm (n + 1) N
              (j.succAbove t) ω x)
          else 1) =
        ∏ t : Fin n,
          (ν (apLinearForm (n + 1) N
              (j.succAbove t)
              (apProjectionVertex j
                (j.succAbove t) false) x) *
            ν (apLinearForm (n + 1) N
              (j.succAbove t)
              (apProjectionVertex j
                (j.succAbove t) true) x)) := by
      apply Fintype.prod_congr
      intro t
      let v₀ :=
        apProjectionVertex j (j.succAbove t) false
      let v₁ :=
        apProjectionVertex j (j.succAbove t) true
      have hprod :
          (∏ ω : DeletedCube (n + 1) (j.succAbove t),
            if apProjectedTwoCopyExponent n j
                (j.succAbove t) ω then
              ν (apLinearForm (n + 1) N
                (j.succAbove t) ω x)
            else 1) =
          (if apProjectedTwoCopyExponent n j
              (j.succAbove t) v₀ then
            ν (apLinearForm (n + 1) N
              (j.succAbove t) v₀ x)
          else 1) *
          (if apProjectedTwoCopyExponent n j
              (j.succAbove t) v₁ then
            ν (apLinearForm (n + 1) N
              (j.succAbove t) v₁ x)
          else 1) := by
        apply Finset.prod_eq_mul
          (s := Finset.univ) v₀ v₁
        · exact apProjectionVertex_false_ne_true
            j (j.succAbove t) (Fin.succAbove_ne j t)
        · intro ω _ hω
          simp [apProjectedTwoCopyExponent, v₀, v₁,
            Fin.succAbove_ne, hω.1, hω.2]
        · simp
        · simp
      simpa [apProjectedTwoCopyExponent, v₀, v₁,
        Fin.succAbove_ne] using hprod
    _ =
        (∏ t : Fin n,
          ν (apLinearForm (n + 1) N
            (j.succAbove t)
            (apProjectionVertex j
              (j.succAbove t) false) x)) *
        ∏ t : Fin n,
          ν (apLinearForm (n + 1) N
            (j.succAbove t)
            (apProjectionVertex j
              (j.succAbove t) true) x) :=
      Finset.prod_mul_distrib

/-- One-copy pointwise expansion in the canonical inserted-coordinate
presentation of the AP simplex. -/
theorem linearFormsProduct_oneCopy_eq_incidentMajorantProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apProjectedOneCopyExponent n j) x =
      apIncidentMajorantProduct n N ν j
        (x j false)
        (fun t => x (j.succAbove t) false) := by
  rw [linearFormsProduct_oneCopy_eq_faceProduct,
    apProjectionFaceProduct_eq_incidentMajorantProduct]

/-- Two-copy pointwise expansion.  Only coordinate `j` is doubled in the
incident products; the remaining coordinates use the same `false` copy. -/
theorem linearFormsProduct_twoCopy_eq_incidentMajorantProducts
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apProjectedTwoCopyExponent n j) x =
      apIncidentMajorantProduct n N ν j
          (x j false)
          (fun t => x (j.succAbove t) false) *
        apIncidentMajorantProduct n N ν j
          (x j true)
          (fun t => x (j.succAbove t) false) := by
  rw [linearFormsProduct_twoCopy_eq_faceProducts,
    apProjectionFaceProduct_eq_incidentMajorantProduct,
    apProjectionFaceProduct_eq_incidentMajorantProduct]

/-! ## The finite coordinate equivalence -/

/-- Split a doubled CFZ point into:

* the shared `false` tuple on coordinates other than `j`;
* the `false` and `true` values at `j`;
* the unused `true` tuple on coordinates other than `j`.

This is the coordinate equivalence behind both projected moment identities.
-/
def apProjectionCubeEquiv
    (n N : ℕ) (j : Fin (n + 1)) :
    CubePoint (n + 1) N ≃
      (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
        (Fin n → ZMod N)) where
  toFun x :=
    (((fun t => x (j.succAbove t) false),
      (x j false, x j true)),
      fun t => x (j.succAbove t) true)
  invFun p i b :=
    match b with
    | false =>
        (Fin.insertNth j p.1.2.1 p.1.1 :
          Fin (n + 1) → ZMod N) i
    | true =>
        (Fin.insertNth j p.1.2.2 p.2 :
          Fin (n + 1) → ZMod N) i
  left_inv x := by
    funext i b
    cases b with
    | false =>
        change
          (Fin.insertNth j (x j false)
              (fun t => x (j.succAbove t) false) :
                Fin (n + 1) → ZMod N) i =
            x i false
        have htuple :
            Fin.insertNth j (x j false)
                (fun t => x (j.succAbove t) false) =
              fun q => x q false := by
          apply (Fin.insertNth_eq_iff).2
          exact ⟨rfl, rfl⟩
        exact congrFun htuple i
    | true =>
        change
          (Fin.insertNth j (x j true)
              (fun t => x (j.succAbove t) true) :
                Fin (n + 1) → ZMod N) i =
            x i true
        have htuple :
            Fin.insertNth j (x j true)
                (fun t => x (j.succAbove t) true) =
              fun q => x q true := by
          apply (Fin.insertNth_eq_iff).2
          exact ⟨rfl, rfl⟩
        exact congrFun htuple i
  right_inv p := by
    rcases p with ⟨⟨y, ⟨a₀, a₁⟩⟩, y₁⟩
    apply Prod.ext
    · apply Prod.ext
      · funext t
        simp
      · apply Prod.ext <;> simp
    · funext t
      simp

/-! ## Exact projected moment identities -/

/-- The one-copy projected moment is exactly the CFZ subproduct selected by
`apProjectedOneCopyExponent`.  All discarded coordinates are uniform finite
fibers, so no cardinality factor appears. -/
theorem mean_apProjectedMajorant_eq_oneCopyLinearFormsProduct
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (j : Fin (n + 1)) :
    mean (apProjectedMajorant n N ν j) =
      mean (linearFormsProduct (n + 1) N ν
        (apProjectedOneCopyExponent n j)) := by
  change
    mean (fun y : Fin n → ZMod N =>
      mean (fun a : ZMod N =>
        apIncidentMajorantProduct n N ν j a y)) = _
  calc
    mean (fun y : Fin n → ZMod N =>
        mean (fun a : ZMod N =>
          apIncidentMajorantProduct n N ν j a y)) =
        mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N =>
            apIncidentMajorantProduct n N ν j a y) :=
      rfl
    _ = mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N × ZMod N =>
            apIncidentMajorantProduct n N ν j a.1 y) := by
      unfold mean₂
      apply congrArg mean
      funext y
      exact
        (mean_prod_fst
          (fun a : ZMod N =>
            apIncidentMajorantProduct n N ν j a y)).symm
    _ = mean (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
        apIncidentMajorantProduct n N ν j q.2.1 q.1) :=
      (mean_prod_type _).symm
    _ = mean (fun p :
          (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
            (Fin n → ZMod N)) =>
        apIncidentMajorantProduct n N ν j
          p.1.2.1 p.1.1) :=
      (mean_prod_fst
        (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
          apIncidentMajorantProduct n N ν j
            q.2.1 q.1)).symm
    _ = mean (linearFormsProduct (n + 1) N ν
          (apProjectedOneCopyExponent n j)) := by
      symm
      apply mean_equiv (apProjectionCubeEquiv n N j)
      intro x
      simpa [apProjectionCubeEquiv] using
        linearFormsProduct_oneCopy_eq_incidentMajorantProduct
          n N ν j x

/-- The second projected moment is exactly the two-copy CFZ subproduct.
The two eliminated coordinates are independent, while the edge coordinates
are shared; the final `true` edge tuple in `apProjectionCubeEquiv` is unused.
-/
theorem mean_apProjectedMajorant_sq_eq_twoCopyLinearFormsProduct
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (j : Fin (n + 1)) :
    mean (fun y => apProjectedMajorant n N ν j y ^ 2) =
      mean (linearFormsProduct (n + 1) N ν
        (apProjectedTwoCopyExponent n j)) := by
  change
    mean (fun y : Fin n → ZMod N =>
      mean (fun a : ZMod N =>
        apIncidentMajorantProduct n N ν j a y) ^ 2) = _
  calc
    mean (fun y : Fin n → ZMod N =>
        mean (fun a : ZMod N =>
          apIncidentMajorantProduct n N ν j a y) ^ 2) =
        mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N × ZMod N =>
            apIncidentMajorantProduct n N ν j a.1 y *
              apIncidentMajorantProduct n N ν j a.2 y) :=
      mean_inner_sq_eq_mean₂_pair _
    _ = mean (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
        apIncidentMajorantProduct n N ν j q.2.1 q.1 *
          apIncidentMajorantProduct n N ν j q.2.2 q.1) :=
      (mean_prod_type _).symm
    _ = mean (fun p :
          (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
            (Fin n → ZMod N)) =>
        apIncidentMajorantProduct n N ν j
            p.1.2.1 p.1.1 *
          apIncidentMajorantProduct n N ν j
            p.1.2.2 p.1.1) :=
      (mean_prod_fst
        (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
          apIncidentMajorantProduct n N ν j q.2.1 q.1 *
            apIncidentMajorantProduct n N ν j
              q.2.2 q.1)).symm
    _ = mean (linearFormsProduct (n + 1) N ν
          (apProjectedTwoCopyExponent n j)) := by
      symm
      apply mean_equiv (apProjectionCubeEquiv n N j)
      intro x
      simpa [apProjectionCubeEquiv] using
        linearFormsProduct_twoCopy_eq_incidentMajorantProducts
          n N ν j x

/-! ## Linear forms imply projected-majorant moments -/

/-- The canonical AP linear-forms condition supplies the projected
majorant moment package with no error loss.

Pointwise nonnegativity is stated separately because a collection of
averaged linear-forms estimates does not imply it; sieve majorants provide
this hypothesis independently. -/
theorem HasLinearFormsCondition.hasProjectedMajorantMoments_apProjection
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (j : Fin (n + 1)) :
    HasProjectedMajorantMoments
      (apProjectedMajorant n N ν j) η := by
  refine
    { error_nonneg := h.error_nonneg
      nonneg := apProjectedMajorant_nonneg hν j
      firstMoment_close := ?_
      secondMoment_close := ?_ }
  · rw [mean_apProjectedMajorant_eq_oneCopyLinearFormsProduct]
    exact h (apProjectedOneCopyExponent n j)
  · rw [mean_apProjectedMajorant_sq_eq_twoCopyLinearFormsProduct]
    exact h (apProjectedTwoCopyExponent n j)

end Wikipedia.SzemeredisTheorem
