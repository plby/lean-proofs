import Wikipedia.GreenTao.Transference.RelativeSimplexIteration

/-!
# Mixed projected moments for recursive relative densification

After one colour has been densified, its majorant is the constant function
one.  At the next stage the projected majorant is therefore not the product
of a common `ν` on every incident colour: it is a mixed product, with `ν`
only on the colours which remain sparse and `1` on the colours already
densified.

This file closes that moment gap.  A Boolean mask records the remaining
sparse colours.  We expand the first and second moments of the corresponding
projected majorant as explicit subproducts of the original CFZ linear-forms
system.  Consequently one unchanged `HasLinearFormsCondition` supplies the
moment package for every recursive mask, and hence supplies the next
heterogeneous full-to-projected state transition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Majorants with previously densified colours set to one -/

/-- The heterogeneous face-majorant family which uses `ν` on active
colours and the constant function one on colours already densified. -/
def apMaskedFaceMajorant
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool) :
    (i : Fin k) → ZMod N → ℝ :=
  fun i z => if active i then ν z else 1

@[simp]
theorem apMaskedFaceMajorant_of_active
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool)
    (i : Fin k) (z : ZMod N)
    (hi : active i = true) :
    apMaskedFaceMajorant ν active i z = ν z := by
  simp [apMaskedFaceMajorant, hi]

@[simp]
theorem apMaskedFaceMajorant_of_inactive
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool)
    (i : Fin k) (z : ZMod N)
    (hi : active i = false) :
    apMaskedFaceMajorant ν active i z = 1 := by
  simp [apMaskedFaceMajorant, hi]

/-- Product of the still-active incident majorants after inserting the
eliminated coordinate.  Inactive colours contribute literal factors `1`. -/
def apMaskedIncidentMajorantProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) : ℝ :=
  apHeterogeneousIncidentProduct n N
    (apMaskedFaceMajorant ν active) j a y

/-- Conditional projection of the mixed incident majorant product. -/
noncomputable def apMaskedProjectedMajorant
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  apHeterogeneousProjectedWeight n N
    (apMaskedFaceMajorant ν active) j

theorem apMaskedProjectedMajorant_nonneg
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) :
    0 ≤ apMaskedProjectedMajorant n N ν active j y := by
  unfold apMaskedProjectedMajorant
  exact mean_nonneg fun a =>
    Finset.prod_nonneg fun t _ => by
      cases hactive : active (j.succAbove t) <;>
        simp [apMaskedFaceMajorant, hactive, hν]

/-! ## Masked CFZ selectors -/

/-- Select one projected copy on every active incident colour and no form
on an inactive colour. -/
noncomputable def apMaskedProjectedOneCopyExponent
    (n : ℕ) (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    LinearFormsExponent (n + 1) :=
  fun i ω =>
    if i = j then false
    else if active i then
      if ω = apProjectionVertex j i false then true else false
    else false

/-- Select two projected copies on every active incident colour and no form
on an inactive colour. -/
noncomputable def apMaskedProjectedTwoCopyExponent
    (n : ℕ) (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    LinearFormsExponent (n + 1) :=
  fun i ω =>
    if i = j then false
    else if active i then
      if
        ω = apProjectionVertex j i false ∨
          ω = apProjectionVertex j i true
      then true
      else false
    else false

/-- The masked one-copy CFZ subproduct is exactly the active incident
majorant product. -/
theorem linearFormsProduct_maskedOneCopy_eq_incidentMajorantProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apMaskedProjectedOneCopyExponent n active j) x =
      apMaskedIncidentMajorantProduct n N ν active j
        (x j false)
        (fun t => x (j.succAbove t) false) := by
  classical
  unfold apMaskedIncidentMajorantProduct
  unfold apHeterogeneousIncidentProduct
  rw [linearFormsProduct, Fin.prod_univ_succAbove _ j]
  have hself :
      (∏ ω : DeletedCube (n + 1) j,
        if apMaskedProjectedOneCopyExponent n active j j ω then
          ν (apLinearForm (n + 1) N j ω x)
        else 1) = 1 := by
    apply Fintype.prod_eq_one
    intro ω
    simp [apMaskedProjectedOneCopyExponent]
  rw [hself, one_mul]
  apply Fintype.prod_congr
  intro t
  cases hactive : active (j.succAbove t) with
  | false =>
      simp [apMaskedProjectedOneCopyExponent,
        apMaskedFaceMajorant, hactive, Fin.succAbove_ne]
  | true =>
      let v :=
        apProjectionVertex j (j.succAbove t) false
      rw [Fintype.prod_eq_single v]
      · have hform :=
          congrArg ν
            (apLinearForm_projectionVertex
              j (j.succAbove t) false x)
        simpa [apMaskedProjectedOneCopyExponent,
          apMaskedFaceMajorant, hactive, v, Fin.succAbove_ne,
          apProjectionTuple_eq_insertNth] using hform
      · intro ω hω
        simp [apMaskedProjectedOneCopyExponent,
          hactive, v, Fin.succAbove_ne, hω]

/-- The masked two-copy CFZ subproduct is exactly the product of two active
incident majorant products sharing all non-eliminated coordinates. -/
theorem linearFormsProduct_maskedTwoCopy_eq_incidentMajorantProducts
    (n N : ℕ) (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (x : CubePoint (n + 1) N) :
    linearFormsProduct (n + 1) N ν
        (apMaskedProjectedTwoCopyExponent n active j) x =
      apMaskedIncidentMajorantProduct n N ν active j
          (x j false)
          (fun t => x (j.succAbove t) false) *
        apMaskedIncidentMajorantProduct n N ν active j
          (x j true)
          (fun t => x (j.succAbove t) false) := by
  classical
  unfold apMaskedIncidentMajorantProduct
  unfold apHeterogeneousIncidentProduct
  rw [linearFormsProduct, Fin.prod_univ_succAbove _ j]
  have hself :
      (∏ ω : DeletedCube (n + 1) j,
        if apMaskedProjectedTwoCopyExponent n active j j ω then
          ν (apLinearForm (n + 1) N j ω x)
        else 1) = 1 := by
    apply Fintype.prod_eq_one
    intro ω
    simp [apMaskedProjectedTwoCopyExponent]
  rw [hself, one_mul]
  calc
    (∏ t : Fin n,
        ∏ ω : DeletedCube (n + 1) (j.succAbove t),
          if apMaskedProjectedTwoCopyExponent n active j
              (j.succAbove t) ω then
            ν (apLinearForm (n + 1) N
              (j.succAbove t) ω x)
          else 1) =
        ∏ t : Fin n,
          (if active (j.succAbove t) then
            ν (apLinearForm (n + 1) N
              (j.succAbove t)
              (apProjectionVertex j
                (j.succAbove t) false) x)
          else 1) *
          (if active (j.succAbove t) then
            ν (apLinearForm (n + 1) N
              (j.succAbove t)
              (apProjectionVertex j
                (j.succAbove t) true) x)
          else 1) := by
      apply Fintype.prod_congr
      intro t
      cases hactive : active (j.succAbove t) with
      | false =>
          simp [apMaskedProjectedTwoCopyExponent,
            hactive, Fin.succAbove_ne]
      | true =>
          let v₀ :=
            apProjectionVertex j (j.succAbove t) false
          let v₁ :=
            apProjectionVertex j (j.succAbove t) true
          have hprod :
              (∏ ω : DeletedCube (n + 1) (j.succAbove t),
                if apMaskedProjectedTwoCopyExponent n active j
                    (j.succAbove t) ω then
                  ν (apLinearForm (n + 1) N
                    (j.succAbove t) ω x)
                else 1) =
              (if apMaskedProjectedTwoCopyExponent n active j
                  (j.succAbove t) v₀ then
                ν (apLinearForm (n + 1) N
                  (j.succAbove t) v₀ x)
              else 1) *
              (if apMaskedProjectedTwoCopyExponent n active j
                  (j.succAbove t) v₁ then
                ν (apLinearForm (n + 1) N
                  (j.succAbove t) v₁ x)
              else 1) := by
            apply Finset.prod_eq_mul
              (s := Finset.univ) v₀ v₁
            · exact apProjectionVertex_false_ne_true
                j (j.succAbove t) (Fin.succAbove_ne j t)
            · intro ω _ hω
              simp [apMaskedProjectedTwoCopyExponent,
                hactive, v₀, v₁, Fin.succAbove_ne,
                hω.1, hω.2]
            · simp
            · simp
          simpa [apMaskedProjectedTwoCopyExponent,
            hactive, v₀, v₁, Fin.succAbove_ne] using hprod
    _ =
        (∏ t : Fin n,
          if active (j.succAbove t) then
            ν (apLinearForm (n + 1) N
              (j.succAbove t)
              (apProjectionVertex j
                (j.succAbove t) false) x)
          else 1) *
        ∏ t : Fin n,
          if active (j.succAbove t) then
            ν (apLinearForm (n + 1) N
              (j.succAbove t)
              (apProjectionVertex j
                (j.succAbove t) true) x)
          else 1 :=
      Finset.prod_mul_distrib
    _ =
        (∏ t : Fin n,
          apMaskedFaceMajorant ν active
            (j.succAbove t)
            (apSimplexForm (n + 1) N (j.succAbove t)
              (deleteCoordinate
                (Fin.insertNth j (x j false)
                  (fun q => x (j.succAbove q) false))
                (j.succAbove t)))) *
        ∏ t : Fin n,
          apMaskedFaceMajorant ν active
            (j.succAbove t)
            (apSimplexForm (n + 1) N (j.succAbove t)
              (deleteCoordinate
                (Fin.insertNth j (x j true)
                  (fun q => x (j.succAbove q) false))
                (j.succAbove t))) := by
      apply congrArg₂ (· * ·)
      · apply Fintype.prod_congr
        intro t
        cases hactive : active (j.succAbove t) with
        | false =>
            simp [apMaskedFaceMajorant, hactive]
        | true =>
            have hform :=
              congrArg ν
                (apLinearForm_projectionVertex
                  j (j.succAbove t) false x)
            simpa [apMaskedFaceMajorant, hactive,
              apProjectionTuple_eq_insertNth] using hform
      · apply Fintype.prod_congr
        intro t
        cases hactive : active (j.succAbove t) with
        | false =>
            simp [apMaskedFaceMajorant, hactive]
        | true =>
            have hform :=
              congrArg ν
                (apLinearForm_projectionVertex
                  j (j.succAbove t) true x)
            simpa [apMaskedFaceMajorant, hactive,
              apProjectionTuple_eq_insertNth] using hform

/-! ## Exact mixed projected moments -/

/-- The first moment of a mixed projected majorant is an explicit
one-copy subproduct of the original CFZ system. -/
theorem mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    mean (apMaskedProjectedMajorant n N ν active j) =
      mean (linearFormsProduct (n + 1) N ν
        (apMaskedProjectedOneCopyExponent n active j)) := by
  change
    mean (fun y : Fin n → ZMod N =>
      mean (fun a : ZMod N =>
        apMaskedIncidentMajorantProduct n N ν active j a y)) = _
  calc
    mean (fun y : Fin n → ZMod N =>
        mean (fun a : ZMod N =>
          apMaskedIncidentMajorantProduct n N ν active j a y)) =
        mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a y) :=
      rfl
    _ = mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N × ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a.1 y) := by
      unfold mean₂
      apply congrArg mean
      funext y
      exact
        (mean_prod_fst
          (fun a : ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a y)).symm
    _ = mean (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
        apMaskedIncidentMajorantProduct n N ν active j q.2.1 q.1) :=
      (mean_prod_type _).symm
    _ = mean (fun p :
          (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
            (Fin n → ZMod N)) =>
        apMaskedIncidentMajorantProduct n N ν active j
          p.1.2.1 p.1.1) :=
      (mean_prod_fst
        (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
          apMaskedIncidentMajorantProduct n N ν active j
            q.2.1 q.1)).symm
    _ = mean (linearFormsProduct (n + 1) N ν
          (apMaskedProjectedOneCopyExponent n active j)) := by
      symm
      apply mean_equiv (apProjectionCubeEquiv n N j)
      intro x
      simpa [apProjectionCubeEquiv] using
        linearFormsProduct_maskedOneCopy_eq_incidentMajorantProduct
          n N ν active j x

/-- The second moment of a mixed projected majorant is the corresponding
two-copy CFZ subproduct. -/
theorem mean_apMaskedProjectedMajorant_sq_eq_twoCopyLinearFormsProduct
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    mean (fun y =>
      apMaskedProjectedMajorant n N ν active j y ^ 2) =
      mean (linearFormsProduct (n + 1) N ν
        (apMaskedProjectedTwoCopyExponent n active j)) := by
  change
    mean (fun y : Fin n → ZMod N =>
      mean (fun a : ZMod N =>
        apMaskedIncidentMajorantProduct n N ν active j a y) ^ 2) = _
  calc
    mean (fun y : Fin n → ZMod N =>
        mean (fun a : ZMod N =>
          apMaskedIncidentMajorantProduct n N ν active j a y) ^ 2) =
        mean₂ (fun y : Fin n → ZMod N =>
          fun a : ZMod N × ZMod N =>
            apMaskedIncidentMajorantProduct n N ν active j a.1 y *
              apMaskedIncidentMajorantProduct n N ν active j a.2 y) :=
      mean_inner_sq_eq_mean₂_pair _
    _ = mean (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
        apMaskedIncidentMajorantProduct n N ν active j q.2.1 q.1 *
          apMaskedIncidentMajorantProduct n N ν active j q.2.2 q.1) :=
      (mean_prod_type _).symm
    _ = mean (fun p :
          (((Fin n → ZMod N) × (ZMod N × ZMod N)) ×
            (Fin n → ZMod N)) =>
        apMaskedIncidentMajorantProduct n N ν active j
            p.1.2.1 p.1.1 *
          apMaskedIncidentMajorantProduct n N ν active j
            p.1.2.2 p.1.1) :=
      (mean_prod_fst
        (fun q :
          (Fin n → ZMod N) × (ZMod N × ZMod N) =>
          apMaskedIncidentMajorantProduct n N ν active j q.2.1 q.1 *
            apMaskedIncidentMajorantProduct n N ν active j
              q.2.2 q.1)).symm
    _ = mean (linearFormsProduct (n + 1) N ν
          (apMaskedProjectedTwoCopyExponent n active j)) := by
      symm
      apply mean_equiv (apProjectionCubeEquiv n N j)
      intro x
      simpa [apProjectionCubeEquiv] using
        linearFormsProduct_maskedTwoCopy_eq_incidentMajorantProducts
          n N ν active j x

/-! ## The recursive moment and state-transition certificates -/

/-- One common CFZ linear-forms condition supplies projected moments for
every choice of active sparse colours.  Inactive colours contribute one and
therefore simply disappear from the selected CFZ subproduct. -/
theorem HasLinearFormsCondition.hasProjectedMajorantMoments_apMaskedProjection
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    HasProjectedMajorantMoments
      (apMaskedProjectedMajorant n N ν active j) η := by
  refine
    { error_nonneg := hLF.error_nonneg
      nonneg := apMaskedProjectedMajorant_nonneg hν active j
      firstMoment_close := ?_
      secondMoment_close := ?_ }
  · rw [mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct]
    exact hLF (apMaskedProjectedOneCopyExponent n active j)
  · rw [mean_apMaskedProjectedMajorant_sq_eq_twoCopyLinearFormsProduct]
    exact hLF (apMaskedProjectedTwoCopyExponent n active j)

/-- Recursive heterogeneous densification step after any set of earlier
colours has had its majorant replaced by one.  This is a concrete transition
between the canonical full and projected states from
`RelativeSimplexIteration`; no additional moment hypothesis is exposed. -/
theorem HasLinearFormsCondition.apMaskedRelativeSimplexStateTransition
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    {g : APFaceWeightFamily n N}
    (j : Fin (n + 1))
    (hj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) j) :
    RelativeDensificationCountLoss
      (apRelativeSimplexFullState g
        (apMaskedFaceMajorant ν active) j)
      (apRelativeSimplexProjectedState g
        (apMaskedFaceMajorant ν active) j)
      (Real.sqrt (3 * η)) := by
  have hMoments :
      HasProjectedMajorantMoments
        (apHeterogeneousProjectedWeight n N
          (apMaskedFaceMajorant ν active) j) η := by
    exact hLF.hasProjectedMajorantMoments_apMaskedProjection
      hν active j
  exact hMoments.apRelativeSimplexStateTransition hj hrest

end Wikipedia.SzemeredisTheorem
