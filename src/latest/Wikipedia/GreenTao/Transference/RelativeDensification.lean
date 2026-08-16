import Wikipedia.GreenTao.Transference.ProjectedMajorantExpansion

/-!
# One relative AP-simplex densification step

Fix a colour `j` in the canonical `(n + 1)`-colour AP simplex.  Put a
unit-bounded weight `f` on the distinguished edge and a relatively bounded
weight `g ≤ ν` on every other edge.  Averaging the non-distinguished edge
product over the missing coordinate gives `apProjectedEdgeWeight g`; it is
dominated by the projected majorant built from `ν`.

The linear-forms condition gives first and second moments for that projected
majorant.  Hence replacing `apProjectedEdgeWeight g` by its pointwise
truncation at one costs at most `√(3 * η)` both in normalized mean and in the
multilinear AP-simplex pairing against the distinguished bounded edge.

This is one exact transference step, not a full relative counting theorem.
The remaining iteration must arrange that the distinguished factor is
already unit-bounded at each step and identify the resulting surrogate
pairings with the next lower-complexity counting problem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projecting a relatively bounded edge weight -/

/-- The projected product of all non-distinguished `g`-edges.  This is the
same finite conditional average as `apProjectedMajorant`, but the name
records its role as the function to be truncated. -/
noncomputable def apProjectedEdgeWeight
    (n N : ℕ) [NeZero N] (g : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  apProjectedMajorant n N g j

/-- The bounded surrogate used in one densification step. -/
noncomputable def apProjectedBoundedSurrogate
    (n N : ℕ) [NeZero N] (g : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  truncateAtOne (apProjectedEdgeWeight n N g j)

@[simp]
theorem apProjectedBoundedSurrogate_apply
    (n N : ℕ) [NeZero N] (g : ZMod N → ℝ)
    (j : Fin (n + 1)) (y : Fin n → ZMod N) :
    apProjectedBoundedSurrogate n N g j y =
      min (apProjectedEdgeWeight n N g j y) 1 :=
  rfl

/-- Pointwise domination is preserved by the product of incident edges. -/
theorem apIncidentMajorantProduct_mono
    {n N : ℕ} {f g : ZMod N → ℝ}
    (hf0 : ∀ z, 0 ≤ f z)
    (hfg : ∀ z, f z ≤ g z)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) :
    apIncidentMajorantProduct n N f j a y ≤
      apIncidentMajorantProduct n N g j a y := by
  unfold apIncidentMajorantProduct
  exact Finset.prod_le_prod
    (fun t _ => hf0 _)
    (fun t _ => hfg _)

/-- Conditional averaging preserves domination of the projected edge
weights. -/
theorem apProjectedEdgeWeight_mono
    {n N : ℕ} [NeZero N]
    {f g : ZMod N → ℝ}
    (hf0 : ∀ z, 0 ≤ f z)
    (hfg : ∀ z, f z ≤ g z)
    (j : Fin (n + 1)) (y : Fin n → ZMod N) :
    apProjectedEdgeWeight n N f j y ≤
      apProjectedEdgeWeight n N g j y := by
  unfold apProjectedEdgeWeight apProjectedMajorant
  exact mean_mono fun a =>
    apIncidentMajorantProduct_mono hf0 hfg j a y

/-- A nonnegative base edge weight has a nonnegative projection. -/
theorem apProjectedEdgeWeight_nonneg
    {n N : ℕ} [NeZero N]
    {g : ZMod N → ℝ}
    (hg0 : ∀ z, 0 ≤ g z)
    (j : Fin (n + 1)) (y : Fin n → ZMod N) :
    0 ≤ apProjectedEdgeWeight n N g j y :=
  apProjectedMajorant_nonneg hg0 j y

/-- The projected majorant moments give the complete pointwise range and
`L¹` loss specification for the bounded surrogate. -/
theorem HasLinearFormsCondition.apProjectedBoundedSurrogate_spec
    {n N : ℕ} [NeZero N]
    {ν g : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgν : ∀ z, g z ≤ ν z)
    (j : Fin (n + 1)) :
    (∀ y,
      0 ≤ apProjectedBoundedSurrogate n N g j y ∧
        apProjectedBoundedSurrogate n N g j y ≤ 1) ∧
      mean (fun y =>
        |apProjectedEdgeWeight n N g j y -
          apProjectedBoundedSurrogate n N g j y|) ≤
        Real.sqrt (3 * η) := by
  have hν0 : ∀ z, 0 ≤ ν z :=
    fun z => (hg0 z).trans (hgν z)
  have hmoments :=
    hLF.hasProjectedMajorantMoments_apProjection hν0 j
  have hdom :
      ∀ y, apProjectedEdgeWeight n N g j y ≤
        apProjectedMajorant n N ν j y :=
    apProjectedEdgeWeight_mono hg0 hgν j
  simpa [apProjectedBoundedSurrogate,
    apProjectedEdgeWeight] using
    hmoments.truncateAtOne_spec
      (apProjectedEdgeWeight_nonneg hg0 j) hdom

/-- In particular, the absolute difference of normalized means has the same
square-root bound. -/
theorem HasLinearFormsCondition.abs_mean_apProjectedEdgeWeight_sub_surrogate_le
    {n N : ℕ} [NeZero N]
    {ν g : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgν : ∀ z, g z ≤ ν z)
    (j : Fin (n + 1)) :
    |mean (apProjectedEdgeWeight n N g j) -
        mean (apProjectedBoundedSurrogate n N g j)| ≤
      Real.sqrt (3 * η) := by
  rw [← mean_sub]
  exact
    (Finset.abs_expect_le Finset.univ _).trans
      (hLF.apProjectedBoundedSurrogate_spec hg0 hgν j).2

/-! ## Exact AP-simplex pairing -/

/-- The distinguished AP edge written in canonical deleted-face
coordinates. -/
noncomputable def apDistinguishedFaceWeight
    (n N : ℕ) (f : ZMod N → ℝ)
    (j : Fin (n + 1))
    (y : Fin n → ZMod N) : ℝ :=
  f (apSimplexForm (n + 1) N j
    (finTupleToDeletedVector j y))

/-- The AP-simplex system with `f` on colour `j` and `g` on every other
colour.  This is the multilinear configuration for one densification step.
-/
def apOneColorMixedSimplexSystem
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) where
  edgeWeight i x :=
    if i = j then
      f (apSimplexForm (n + 1) N i x)
    else
      g (apSimplexForm (n + 1) N i x)

@[simp]
theorem apOneColorMixedSimplexSystem_edge_self
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) j) :
    (apOneColorMixedSimplexSystem n N f g j).edgeWeight j x =
      f (apSimplexForm (n + 1) N j x) := by
  simp [apOneColorMixedSimplexSystem]

theorem apOneColorMixedSimplexSystem_edge_other
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j i : Fin (n + 1)) (hij : i ≠ j)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) i) :
    (apOneColorMixedSimplexSystem n N f g j).edgeWeight i x =
      g (apSimplexForm (n + 1) N i x) := by
  simp [apOneColorMixedSimplexSystem, hij]

/-- After inserting the missing coordinate, the mixed simplex weight is
exactly the distinguished face factor times the incident-edge product. -/
theorem apOneColorMixedSimplexWeight_insertNth
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) :
    (apOneColorMixedSimplexSystem n N f g j).simplexWeight
        (Fin.insertNth j a y) =
      apIncidentMajorantProduct n N g j a y *
        apDistinguishedFaceWeight n N f j y := by
  rw [WeightedSimplexSystem.simplexWeight,
    Fin.prod_univ_succAbove _ j,
    apOneColorMixedSimplexSystem_edge_self]
  have hdelete :
      deleteCoordinate (Fin.insertNth j a y) j =
        finTupleToDeletedVector j y := by
    simpa using
      deleteCoordinate_eq_finTupleToDeletedVector
        j (Fin.insertNth j a y)
  rw [hdelete]
  have htail :
      (∏ t : Fin n,
        (apOneColorMixedSimplexSystem n N f g j).edgeWeight
          (j.succAbove t)
          (deleteCoordinate (Fin.insertNth j a y)
            (j.succAbove t))) =
        apIncidentMajorantProduct n N g j a y := by
    unfold apIncidentMajorantProduct
    apply Fintype.prod_congr
    intro t
    exact apOneColorMixedSimplexSystem_edge_other
      n N f g j (j.succAbove t)
      (Fin.succAbove_ne j t) _
  rw [htail, apDistinguishedFaceWeight, mul_comm]

/-- The normalized mixed simplex count is exactly the pairing of the
distinguished face weight with the projected non-distinguished edge weight.
-/
theorem apOneColorMixedSimplexCount_eq_projectedPairing
    (n N : ℕ) [NeZero N]
    (f g : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    (apOneColorMixedSimplexSystem n N f g j).simplexCount =
      mean (fun y =>
        apProjectedEdgeWeight n N g j y *
          apDistinguishedFaceWeight n N f j y) := by
  rw [WeightedSimplexSystem.simplexCount,
    mean_insertNth n j, mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext y
  calc
    mean (fun a : ZMod N =>
        (apOneColorMixedSimplexSystem n N f g j).simplexWeight
          (Fin.insertNth j a y)) =
        mean (fun a : ZMod N =>
          apIncidentMajorantProduct n N g j a y *
            apDistinguishedFaceWeight n N f j y) := by
      apply congrArg mean
      funext a
      exact apOneColorMixedSimplexWeight_insertNth
        n N f g j a y
    _ = mean (fun a : ZMod N =>
          apDistinguishedFaceWeight n N f j y *
            apIncidentMajorantProduct n N g j a y) := by
      apply congrArg mean
      funext a
      ring
    _ = apDistinguishedFaceWeight n N f j y *
        mean (fun a : ZMod N =>
          apIncidentMajorantProduct n N g j a y) :=
      mean_smul _ _
    _ = apProjectedEdgeWeight n N g j y *
        apDistinguishedFaceWeight n N f j y := by
      rw [mul_comm]
      rfl

/-- The count-like pairing after replacing the projected edge product by
its bounded surrogate. -/
noncomputable def apOneColorDensifiedPairing
    (n N : ℕ) [NeZero N]
    (f g : ZMod N → ℝ)
    (j : Fin (n + 1)) : ℝ :=
  mean (fun y =>
    apProjectedBoundedSurrogate n N g j y *
      apDistinguishedFaceWeight n N f j y)

/-- One exact relative densification estimate.  If the distinguished edge
`f` is already `[0,1]`-valued and all remaining edges satisfy
`0 ≤ g ≤ ν`, replacing their projection by its bounded surrogate changes
the AP-simplex multilinear count by at most `√(3 * η)`. -/
theorem HasLinearFormsCondition.abs_apOneColorMixedSimplexCount_sub_densifiedPairing_le
    {n N : ℕ} [NeZero N]
    {ν f g : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hf0 : ∀ z, 0 ≤ f z)
    (hf1 : ∀ z, f z ≤ 1)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgν : ∀ z, g z ≤ ν z)
    (j : Fin (n + 1)) :
    |(apOneColorMixedSimplexSystem n N f g j).simplexCount -
        apOneColorDensifiedPairing n N f g j| ≤
      Real.sqrt (3 * η) := by
  rw [apOneColorMixedSimplexCount_eq_projectedPairing]
  have hν0 : ∀ z, 0 ≤ ν z :=
    fun z => (hg0 z).trans (hgν z)
  have hmoments :=
    hLF.hasProjectedMajorantMoments_apProjection hν0 j
  have hdom :
      ∀ y, apProjectedEdgeWeight n N g j y ≤
        apProjectedMajorant n N ν j y :=
    apProjectedEdgeWeight_mono hg0 hgν j
  have hface :
      ∀ y, |apDistinguishedFaceWeight n N f j y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg]
    · exact hf1 _
    · exact hf0 _
  simpa [apOneColorDensifiedPairing,
    apProjectedBoundedSurrogate] using
    hmoments.abs_mean_mul_sub_truncateAtOne_mul_le_sqrt
      hdom hface

/-- Packaged form of one AP-simplex relative densification step: the
surrogate is pointwise `[0,1]`, its `L¹` replacement loss is explicit, and
the corresponding one-colour multilinear count loss has the same bound. -/
theorem HasLinearFormsCondition.apRelativeDensificationStep
    {n N : ℕ} [NeZero N]
    {ν f g : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hf0 : ∀ z, 0 ≤ f z)
    (hf1 : ∀ z, f z ≤ 1)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgν : ∀ z, g z ≤ ν z)
    (j : Fin (n + 1)) :
    ((∀ y,
        0 ≤ apProjectedBoundedSurrogate n N g j y ∧
          apProjectedBoundedSurrogate n N g j y ≤ 1) ∧
      mean (fun y =>
        |apProjectedEdgeWeight n N g j y -
          apProjectedBoundedSurrogate n N g j y|) ≤
        Real.sqrt (3 * η)) ∧
      |(apOneColorMixedSimplexSystem n N f g j).simplexCount -
          apOneColorDensifiedPairing n N f g j| ≤
        Real.sqrt (3 * η) := by
  exact
    ⟨hLF.apProjectedBoundedSurrogate_spec hg0 hgν j,
      hLF.abs_apOneColorMixedSimplexCount_sub_densifiedPairing_le
        hf0 hf1 hg0 hgν j⟩

/-!
## Remaining interface for iteration

The theorem above closes the analytic truncation step.  A full relative
simplex counting theorem still needs an iteration invariant which represents
`apOneColorDensifiedPairing` as the next lower-complexity multilinear system,
keeps the factor paired against the next truncation unit-bounded, and sums
the resulting `√(3 * η)` losses over the chosen colour order.  None of those
identifications follows merely from `0 ≤ g ≤ ν`, so it is intentionally not
asserted here.
-/

end Wikipedia.SzemeredisTheorem
