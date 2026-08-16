import Wikipedia.GreenTao.Transference.RelativeSimplexComparison
import Wikipedia.GreenTao.Transference.ConvolutionClosure

/-!
# Closure of projected face-cut discrepancy

A recursive relative-simplex comparison has two logically separate closure
steps.

* Truncating a projected incident product at one is stable against every
  lower-face cut test.  The loss is exactly the square-root moment loss from
  each side.
* If all simplex edges are already bounded, edgewise face-cut discrepancy is
  stable under projection.  The proof inserts the requested lower-face cut
  product into the distinguished edge and applies the bounded simplex
  comparison theorem.

For a genuinely sparse system the second statement cannot be applied:
the other edge weights occurring in the telescope need not be bounded by
one.  The theorem
`HasProjectedMajorantMoments.faceCutDiscrepancyLe_projectedPairing_of_raw`
therefore isolates the precise remaining hypothesis, namely face-cut
discrepancy of the *untruncated* projected pairings.  This is the residual
which an iterated sparse densification argument must propagate.

The first section also records the exact finite-product consequence of the
generalized-convolution mixture API.  It identifies the one-variable
nonlinear closure already available from dense-model duality; no extra
analytic hypothesis is introduced here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Multiplicative closure of generalized-convolution tests -/

/-- A single cut-discrepancy estimate controls pairing with every finite
product of bounded generalized convolutions, with no loss depending on the
number of factors. -/
theorem CutDiscrepancyLe.abs_finitePairing_prod_generalizedConvolution_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r m : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut :
      CutDiscrepancyLe (r + 1) ν (fun _ => 1) ε)
    (u : Fin m → CutTestFamily G (r + 1))
    (hu : ∀ a, IsBoundedCutTest (u a)) :
    |finitePairing (ν - fun _ => 1)
        (fun z =>
          ∏ a, generalizedConvolution (r + 1) (u a) z)| ≤ ε := by
  obtain ⟨q, hq⟩ :=
    ConvolutionMixture.exists_eq_prod_generalizedConvolution
      r m u hu
  have hpair :=
    hcut.abs_finitePairing_convolutionMixture_le q
  rw [hq] at hpair
  exact hpair

/-! ## Nonlinear truncation closure -/

/-- Multiplying by an absolutely unit-bounded factor and a bounded cut
product remains absolutely bounded by one. -/
theorem abs_mul_cutTestProduct_le_one
    {G : Type*} {r : ℕ}
    {a : (Fin r → G) → ℝ}
    (ha : ∀ x, |a x| ≤ 1)
    {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u)
    (x : Fin r → G) :
    |a x * cutTestProduct u x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (cutTestProduct_nonneg hu x)]
  calc
    |a x| * cutTestProduct u x ≤
        1 * cutTestProduct u x :=
      mul_le_mul_of_nonneg_right
        (ha x) (cutTestProduct_nonneg hu x)
    _ = cutTestProduct u x := one_mul _
    _ ≤ 1 := cutTestProduct_le_one hu x

/-- Truncating two nonnegative projected weights preserves their face-cut
comparison.  Each side pays only its own projected-majorant moment loss.

The hypothesis before truncation is deliberately stated on the explicit
products `F * a` and `K * b`: this is the exact residual produced after the
analytic truncation estimates have been discharged. -/
theorem HasProjectedMajorantMoments.faceCutDiscrepancyLe_truncate_mul
    {G : Type*} [Fintype G] [Nonempty G] {r : ℕ}
    {F K ν μ a b : (Fin r → G) → ℝ}
    {η θ ε : ℝ}
    (hFmom : HasProjectedMajorantMoments ν η)
    (hKmom : HasProjectedMajorantMoments μ θ)
    (hFν : ∀ x, F x ≤ ν x)
    (hKμ : ∀ x, K x ≤ μ x)
    (ha : ∀ x, |a x| ≤ 1)
    (hb : ∀ x, |b x| ≤ 1)
    (hraw :
      FaceCutDiscrepancyLe
        (fun x => F x * a x)
        (fun x => K x * b x) ε) :
    FaceCutDiscrepancyLe
      (fun x => truncateAtOne F x * a x)
      (fun x => truncateAtOne K x * b x)
      (Real.sqrt (3 * η) + ε + Real.sqrt (3 * θ)) := by
  intro u hu
  let U : (Fin r → G) → ℝ :=
    fun x => cutTestProduct u x
  let qF : (Fin r → G) → ℝ :=
    fun x => a x * U x
  let qK : (Fin r → G) → ℝ :=
    fun x => b x * U x
  have hqF : ∀ x, |qF x| ≤ 1 := by
    intro x
    exact abs_mul_cutTestProduct_le_one ha hu x
  have hqK : ∀ x, |qK x| ≤ 1 := by
    intro x
    exact abs_mul_cutTestProduct_le_one hb hu x
  have hleftRaw :=
    hFmom.abs_mean_mul_sub_truncateAtOne_mul_le_sqrt
      hFν hqF
  have hleft :
      |mean (fun x =>
          truncateAtOne F x * a x * U x) -
        mean (fun x => F x * a x * U x)| ≤
          Real.sqrt (3 * η) := by
    rw [abs_sub_comm]
    simpa [qF, U, mul_assoc] using hleftRaw
  have hright :
      |mean (fun x => K x * b x * U x) -
        mean (fun x =>
          truncateAtOne K x * b x * U x)| ≤
          Real.sqrt (3 * θ) := by
    have hrightRaw :=
      hKmom.abs_mean_mul_sub_truncateAtOne_mul_le_sqrt
        hKμ hqK
    simpa [qK, U, mul_assoc] using hrightRaw
  have hmiddle :
      |mean (fun x => F x * a x * U x) -
        mean (fun x => K x * b x * U x)| ≤ ε := by
    have h := hraw u hu
    rw [show
        faceCutDifferenceCorrelation
            (fun x => F x * a x)
            (fun x => K x * b x) u =
          mean (fun x => F x * a x * U x) -
            mean (fun x => K x * b x * U x) by
      unfold faceCutDifferenceCorrelation
      rw [← mean_sub]
      apply congrArg mean
      funext x
      simp only [U]
      ring] at h
    exact h
  rw [show
      faceCutDifferenceCorrelation
          (fun x => truncateAtOne F x * a x)
          (fun x => truncateAtOne K x * b x) u =
        mean (fun x => truncateAtOne F x * a x * U x) -
          mean (fun x =>
            truncateAtOne K x * b x * U x) by
    unfold faceCutDifferenceCorrelation
    rw [← mean_sub]
    apply congrArg mean
    funext x
    simp only [U]
    ring]
  calc
    |mean (fun x => truncateAtOne F x * a x * U x) -
        mean (fun x => truncateAtOne K x * b x * U x)| =
        |(mean (fun x => truncateAtOne F x * a x * U x) -
            mean (fun x => F x * a x * U x)) +
          (mean (fun x => F x * a x * U x) -
            mean (fun x => K x * b x * U x)) +
          (mean (fun x => K x * b x * U x) -
            mean (fun x =>
              truncateAtOne K x * b x * U x))| := by
      congr 1
      ring
    _ ≤
        |mean (fun x => truncateAtOne F x * a x * U x) -
            mean (fun x => F x * a x * U x)| +
          |mean (fun x => F x * a x * U x) -
            mean (fun x => K x * b x * U x)| +
          |mean (fun x => K x * b x * U x) -
            mean (fun x =>
              truncateAtOne K x * b x * U x)| := by
      calc
        |(mean (fun x => truncateAtOne F x * a x * U x) -
              mean (fun x => F x * a x * U x)) +
            (mean (fun x => F x * a x * U x) -
              mean (fun x => K x * b x * U x)) +
            (mean (fun x => K x * b x * U x) -
              mean (fun x =>
                truncateAtOne K x * b x * U x))| ≤
            |(mean (fun x => truncateAtOne F x * a x * U x) -
              mean (fun x => F x * a x * U x)) +
              (mean (fun x => F x * a x * U x) -
                mean (fun x => K x * b x * U x))| +
            |mean (fun x => K x * b x * U x) -
              mean (fun x =>
                truncateAtOne K x * b x * U x)| :=
          abs_add_le _ _
        _ ≤
            (|mean (fun x => truncateAtOne F x * a x * U x) -
                mean (fun x => F x * a x * U x)| +
              |mean (fun x => F x * a x * U x) -
                mean (fun x => K x * b x * U x)|) +
            |mean (fun x => K x * b x * U x) -
              mean (fun x =>
                truncateAtOne K x * b x * U x)| :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (abs_add_le
                (mean (fun x =>
                    truncateAtOne F x * a x * U x) -
                  mean (fun x => F x * a x * U x))
                (mean (fun x => F x * a x * U x) -
                  mean (fun x => K x * b x * U x)))
                |mean (fun x => K x * b x * U x) -
                  mean (fun x =>
                    truncateAtOne K x * b x * U x)|
    _ ≤ Real.sqrt (3 * η) + ε + Real.sqrt (3 * θ) :=
      add_le_add (add_le_add hleft hmiddle) hright

/-! ## The exact raw projected residual -/

/-- The pairing edge before truncating the incident projection. -/
noncomputable def generalSimplexUntruncatedPairingEdge
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y =>
    generalSimplexProjectedWeight H j y *
      generalSimplexDistinguishedWeight H j y

/-- Projected-majorant moments reduce projected face-cut closure to the
untruncated projected pairing, with the two explicit truncation losses. -/
theorem HasProjectedMajorantMoments.faceCutDiscrepancyLe_projectedPairing_of_raw
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H K Hmajorant Kmajorant : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j l : Fin (n + 1)}
    {η θ ε : ℝ}
    (hHmom :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight Hmajorant j) η)
    (hKmom :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight Kmajorant l) θ)
    (hHj : ∀ x,
      0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1)
    (hKl : ∀ x,
      0 ≤ K.edgeWeight l x ∧ K.edgeWeight l x ≤ 1)
    (hHrest :
      GeneralSimplexUntouchedBounds H Hmajorant j)
    (hKrest :
      GeneralSimplexUntouchedBounds K Kmajorant l)
    (hraw :
      FaceCutDiscrepancyLe
        (generalSimplexUntruncatedPairingEdge H j)
        (generalSimplexUntruncatedPairingEdge K l) ε) :
    FaceCutDiscrepancyLe
      (generalProjectedPairingEdge H j)
      (generalProjectedPairingEdge K l)
      (Real.sqrt (3 * η) + ε + Real.sqrt (3 * θ)) := by
  have hHa :
      ∀ y, |generalSimplexDistinguishedWeight H j y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg
      (generalSimplexDistinguishedWeight_mem_unitInterval hHj y).1]
    exact
      (generalSimplexDistinguishedWeight_mem_unitInterval hHj y).2
  have hKa :
      ∀ y, |generalSimplexDistinguishedWeight K l y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg
      (generalSimplexDistinguishedWeight_mem_unitInterval hKl y).1]
    exact
      (generalSimplexDistinguishedWeight_mem_unitInterval hKl y).2
  change
    FaceCutDiscrepancyLe
      (fun y =>
        truncateAtOne (generalSimplexProjectedWeight H j) y *
          generalSimplexDistinguishedWeight H j y)
      (fun y =>
        truncateAtOne (generalSimplexProjectedWeight K l) y *
          generalSimplexDistinguishedWeight K l y)
      (Real.sqrt (3 * η) + ε + Real.sqrt (3 * θ))
  exact
    hHmom.faceCutDiscrepancyLe_truncate_mul
      hKmom
      (generalSimplexProjectedWeight_mono hHrest)
      (generalSimplexProjectedWeight_mono hKrest)
      hHa hKa hraw

/-! ## Bounded algebraic closure under projection -/

/-- Insert one lower-face cut product into the distinguished edge of a
weighted simplex. -/
noncomputable def faceCutWeightedSimplexSystem
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (u : CutTestFamily G n) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G) where
  edgeWeight i x :=
    H.edgeWeight i x *
      if i = j then
        cutTestProduct u (deletedFaceTuple i x)
      else 1

@[simp]
theorem faceCutWeightedSimplexSystem_edge_selected
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (u : CutTestFamily G n)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) j) :
    (faceCutWeightedSimplexSystem H j u).edgeWeight j x =
      H.edgeWeight j x *
        cutTestProduct u (deletedFaceTuple j x) := by
  simp [faceCutWeightedSimplexSystem]

@[simp]
theorem faceCutWeightedSimplexSystem_edge_other
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j i : Fin (n + 1))
    (u : CutTestFamily G n)
    (hij : i ≠ j)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) i) :
    (faceCutWeightedSimplexSystem H j u).edgeWeight i x =
      H.edgeWeight i x := by
  simp [faceCutWeightedSimplexSystem, hij]

theorem faceCutWeightedSimplexSystem_unitInterval
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1))
    {u : CutTestFamily G n}
    (hu : IsBoundedCutTest u) :
    EdgeWeightsInUnitInterval
      (faceCutWeightedSimplexSystem H j u) := by
  intro i x
  by_cases hij : i = j
  · subst i
    rw [faceCutWeightedSimplexSystem_edge_selected]
    constructor
    · exact mul_nonneg (hH j x).1
        (cutTestProduct_nonneg hu _)
    · exact mul_le_one₀ (hH j x).2
        (cutTestProduct_nonneg hu _)
        (cutTestProduct_le_one hu _)
  · simpa [faceCutWeightedSimplexSystem_edge_other H j i u hij]
      using hH i x

@[simp]
theorem generalSimplexIncidentProduct_faceCutWeighted
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (u : CutTestFamily G n)
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct
        (faceCutWeightedSimplexSystem H j u) j a y =
      generalSimplexIncidentProduct H j a y := by
  unfold generalSimplexIncidentProduct
  apply Fintype.prod_congr
  intro t
  simp [faceCutWeightedSimplexSystem,
    Fin.succAbove_ne]

@[simp]
theorem generalSimplexProjectedWeight_faceCutWeighted
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (u : CutTestFamily G n) :
    generalSimplexProjectedWeight
        (faceCutWeightedSimplexSystem H j u) j =
      generalSimplexProjectedWeight H j := by
  funext y
  unfold generalSimplexProjectedWeight
  apply congrArg mean
  funext a
  exact generalSimplexIncidentProduct_faceCutWeighted
    H j u a y

@[simp]
theorem generalSimplexDistinguishedWeight_faceCutWeighted
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (u : CutTestFamily G n)
    (y : Fin n → G) :
    generalSimplexDistinguishedWeight
        (faceCutWeightedSimplexSystem H j u) j y =
      generalSimplexDistinguishedWeight H j y *
        cutTestProduct u y := by
  unfold generalSimplexDistinguishedWeight
  rw [faceCutWeightedSimplexSystem_edge_selected]
  rw [deletedFaceTuple_finTupleToDeletedVector]

/-- The cut-weighted simplex count is exactly the raw projected pairing
against the chosen lower-face cut product. -/
theorem faceCutWeightedSimplexCount_eq
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (u : CutTestFamily G n) :
    (faceCutWeightedSimplexSystem H j u).simplexCount =
      mean (fun y =>
        generalSimplexUntruncatedPairingEdge H j y *
          cutTestProduct u y) := by
  rw [generalSimplexCount_eq_projectedPairing,
    generalSimplexProjectedWeight_faceCutWeighted]
  apply congrArg mean
  funext y
  rw [generalSimplexDistinguishedWeight_faceCutWeighted]
  simp only [generalSimplexUntruncatedPairingEdge]
  ring

/-- Edgewise face-cut discrepancy is preserved after inserting the same
bounded cut product into one distinguished edge. -/
theorem EdgeFaceCutDiscrepancyLe.faceCutWeighted
    {G : Type*} [Fintype G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (j : Fin (n + 1))
    {u : CutTestFamily G n}
    (hu : IsBoundedCutTest u) :
    EdgeFaceCutDiscrepancyLe
      (faceCutWeightedSimplexSystem H j u)
      (faceCutWeightedSimplexSystem K j u) ε := by
  intro i
  by_cases hij : i = j
  · subst i
    intro v hv
    let uv : CutTestFamily G n :=
      fun t y => u t y * v t y
    have huv : IsBoundedCutTest uv :=
      hu.mul hv
    have hbase := hcut j uv huv
    rw [show
        faceCutDifferenceCorrelation
            (canonicalEdgeFunction
              (faceCutWeightedSimplexSystem H j u) j)
            (canonicalEdgeFunction
              (faceCutWeightedSimplexSystem K j u) j) v =
          faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j) uv by
      unfold faceCutDifferenceCorrelation
      apply congrArg mean
      funext y
      change
        ((faceCutWeightedSimplexSystem H j u).edgeWeight j
              (finTupleToDeletedVector j y) -
            (faceCutWeightedSimplexSystem K j u).edgeWeight j
              (finTupleToDeletedVector j y)) *
            cutTestProduct v y =
          (H.edgeWeight j (finTupleToDeletedVector j y) -
            K.edgeWeight j (finTupleToDeletedVector j y)) *
            cutTestProduct uv y
      rw [faceCutWeightedSimplexSystem_edge_selected,
        faceCutWeightedSimplexSystem_edge_selected,
        deletedFaceTuple_finTupleToDeletedVector]
      change
        ((H.edgeWeight j (finTupleToDeletedVector j y) *
              cutTestProduct u y) -
            (K.edgeWeight j (finTupleToDeletedVector j y) *
              cutTestProduct u y)) *
            cutTestProduct v y =
          (H.edgeWeight j (finTupleToDeletedVector j y) -
            K.edgeWeight j (finTupleToDeletedVector j y)) *
            cutTestProduct uv y
      rw [show
          cutTestProduct uv y =
            cutTestProduct u y * cutTestProduct v y by
        exact cutTestProduct_mul u v y]
      ring]
    exact hbase
  · have hHcanonical :
        canonicalEdgeFunction
            (faceCutWeightedSimplexSystem H j u) i =
          canonicalEdgeFunction H i := by
      funext y
      simp [canonicalEdgeFunction,
        faceCutWeightedSimplexSystem_edge_other H j i u hij]
    have hKcanonical :
        canonicalEdgeFunction
            (faceCutWeightedSimplexSystem K j u) i =
          canonicalEdgeFunction K i := by
      funext y
      simp [canonicalEdgeFunction,
        faceCutWeightedSimplexSystem_edge_other K j i u hij]
    rw [hHcanonical, hKcanonical]
    exact hcut i

/-- Raw projected pairings of two fully bounded systems inherit the
edgewise discrepancy, with the usual one-error-per-colour loss. -/
theorem EdgeFaceCutDiscrepancyLe.faceCutDiscrepancyLe_untruncatedPairing
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) :
    FaceCutDiscrepancyLe
      (generalSimplexUntruncatedPairingEdge H j)
      (generalSimplexUntruncatedPairingEdge K j)
      (((n + 1 : ℕ) : ℝ) * ε) := by
  intro u hu
  rw [show
      faceCutDifferenceCorrelation
          (generalSimplexUntruncatedPairingEdge H j)
          (generalSimplexUntruncatedPairingEdge K j) u =
        (faceCutWeightedSimplexSystem H j u).simplexCount -
          (faceCutWeightedSimplexSystem K j u).simplexCount by
    rw [faceCutWeightedSimplexCount_eq,
      faceCutWeightedSimplexCount_eq]
    unfold faceCutDifferenceCorrelation
    rw [← mean_sub]
    apply congrArg mean
    funext y
    ring]
  exact simplexCount_abs_sub_le_of_edgeFaceCutDiscrepancy
    (faceCutWeightedSimplexSystem H j u)
    (faceCutWeightedSimplexSystem K j u)
    (faceCutWeightedSimplexSystem_unitInterval hH j hu)
    (faceCutWeightedSimplexSystem_unitInterval hK j hu)
    (hcut.faceCutWeighted j hu)

/-- A bounded simplex projection never exceeds one, so its truncation is
identically the original projection. -/
theorem generalSimplexProjectedSurrogate_eq_of_unitInterval
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    generalSimplexProjectedSurrogate H j =
      generalSimplexProjectedWeight H j := by
  funext y
  unfold generalSimplexProjectedSurrogate truncateAtOne
  rw [min_eq_left]
  calc
    generalSimplexProjectedWeight H j y ≤
        generalSimplexProjectedWeight
          (oneWeightedSimplexSystem G n) j y :=
      generalSimplexProjectedWeight_mono
        (hH.generalSimplexUntouchedBounds_one j) y
    _ = 1 := by
      exact congrFun
        (generalSimplexProjectedWeight_one
          (G := G) (n := n) j) y

/-- In the fully bounded case the actual truncated projected-pairing edges
therefore inherit edgewise face-cut discrepancy with loss `(n+1) ε`. -/
theorem EdgeFaceCutDiscrepancyLe.faceCutDiscrepancyLe_projectedPairing
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) :
    FaceCutDiscrepancyLe
      (generalProjectedPairingEdge H j)
      (generalProjectedPairingEdge K j)
      (((n + 1 : ℕ) : ℝ) * ε) := by
  change
    FaceCutDiscrepancyLe
      (fun y =>
        generalSimplexProjectedSurrogate H j y *
          generalSimplexDistinguishedWeight H j y)
      (fun y =>
        generalSimplexProjectedSurrogate K j y *
          generalSimplexDistinguishedWeight K j y)
      (((n + 1 : ℕ) : ℝ) * ε)
  rw [generalSimplexProjectedSurrogate_eq_of_unitInterval hH j,
    generalSimplexProjectedSurrogate_eq_of_unitInterval hK j]
  exact hcut.faceCutDiscrepancyLe_untruncatedPairing hH hK j

/-! ## AP specialization and active-mask transition -/

/-- Remove one chosen colour from the set of still-sparse faces. -/
def deactivateFace
    {k : ℕ} (active : Fin k → Bool) (j : Fin k) :
    Fin k → Bool :=
  fun i => if i = j then false else active i

@[simp]
theorem deactivateFace_selected
    {k : ℕ} (active : Fin k → Bool) (j : Fin k) :
    deactivateFace active j j = false := by
  simp [deactivateFace]

@[simp]
theorem deactivateFace_other
    {k : ℕ} (active : Fin k → Bool)
    (j i : Fin k) (hij : i ≠ j) :
    deactivateFace active j i = active i := by
  simp [deactivateFace, hij]

/-- Deactivating the face being projected does not alter the incident
projected majorant, because that face is omitted from the incident product. -/
@[simp]
theorem apMaskedProjectedMajorant_deactivateFace
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    apMaskedProjectedMajorant n N ν
        (deactivateFace active j) j =
      apMaskedProjectedMajorant n N ν active j := by
  funext y
  unfold apMaskedProjectedMajorant
  unfold apHeterogeneousProjectedWeight
  apply congrArg mean
  funext a
  unfold apHeterogeneousIncidentProduct
  apply Fintype.prod_congr
  intro t
  simp [apMaskedFaceMajorant, deactivateFace,
    Fin.succAbove_ne]

/-- Edgewise ordinary AP cut discrepancy gives the heterogeneous direct
face-cut hypothesis colour by colour. -/
theorem edgeFaceCutDiscrepancyLe_apHeterogeneous_of_cutDiscrepancy
    {n N : ℕ} [NeZero N]
    {g h : APFaceWeightFamily n N}
    {ε : ℝ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (hcut : ∀ i, CutDiscrepancyLe n (g i) (h i) ε) :
    EdgeFaceCutDiscrepancyLe
      (apHeterogeneousSimplexSystem n N g)
      (apHeterogeneousSimplexSystem n N h) ε := by
  intro i
  have hi :=
    (hcut i).faceCutDiscrepancyLe_apCanonicalEdge hN i
  change
    FaceCutDiscrepancyLe
      (fun y =>
        g i (apSimplexForm (n + 1) N i
          (finTupleToDeletedVector i y)))
      (fun y =>
        h i (apSimplexForm (n + 1) N i
          (finTupleToDeletedVector i y))) ε
  change
    FaceCutDiscrepancyLe
      (fun y =>
        g i (apSimplexForm (n + 1) N i
          (finTupleToDeletedVector i y)))
      (fun y =>
        h i (apSimplexForm (n + 1) N i
          (finTupleToDeletedVector i y))) ε at hi
  exact hi

/-- Fully bounded AP face families inherit projected whole-face
discrepancy directly from the original edgewise `CutDiscrepancyLe`.
This is the closed algebraic step available once the active mask is empty. -/
theorem apProjectedPairingEdge_faceCutDiscrepancyLe_of_edgewiseCut
    {n N : ℕ} [NeZero N]
    {g h : APFaceWeightFamily n N}
    {ε : ℝ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (hg : ∀ i z, 0 ≤ g i z ∧ g i z ≤ 1)
    (hh : ∀ i z, 0 ≤ h i z ∧ h i z ≤ 1)
    (hcut : ∀ i, CutDiscrepancyLe n (g i) (h i) ε)
    (j : Fin (n + 1)) :
    FaceCutDiscrepancyLe
      (apProjectedPairingEdge n N g j)
      (apProjectedPairingEdge n N h j)
      (((n + 1 : ℕ) : ℝ) * ε) := by
  have hG :
      EdgeWeightsInUnitInterval
        (apHeterogeneousSimplexSystem n N g) :=
    fun i x => hg i _
  have hH :
      EdgeWeightsInUnitInterval
        (apHeterogeneousSimplexSystem n N h) :=
    fun i x => hh i _
  have hfaces :=
    edgeFaceCutDiscrepancyLe_apHeterogeneous_of_cutDiscrepancy
      hN hcut
  change
    FaceCutDiscrepancyLe
      (generalProjectedPairingEdge
        (apHeterogeneousSimplexSystem n N g) j)
      (generalProjectedPairingEdge
        (apHeterogeneousSimplexSystem n N h) j)
      (((n + 1 : ℕ) : ℝ) * ε)
  exact hfaces.faceCutDiscrepancyLe_projectedPairing
    hG hH j

/-- AP notation for the exact untruncated projected residual. -/
noncomputable def apUntruncatedProjectedPairingEdge
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  fun y =>
    apHeterogeneousProjectedWeight n N g j y *
      apHeterogeneousDistinguishedFaceWeight n N g j y

/-- The nonlinear sparse closure currently supported by the moment API.
The two masks may differ, so this statement applies immediately after a
face has been deactivated.  All truncation losses are discharged; the only
remaining hypothesis is face-cut discrepancy of the explicit untruncated
projected pairings. -/
theorem HasLinearFormsCondition.apProjectedPairingEdge_faceCutDiscrepancyLe_of_raw
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (activeG activeH : Fin (n + 1) → Bool)
    {g h : APFaceWeightFamily n N}
    (j l : Fin (n + 1))
    (hgj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hhl : ∀ z, 0 ≤ h l z ∧ h l z ≤ 1)
    (hgrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν activeG) j)
    (hhrest :
      APUntouchedFaceBounds h
        (apMaskedFaceMajorant ν activeH) l)
    (hraw :
      FaceCutDiscrepancyLe
        (apUntruncatedProjectedPairingEdge n N g j)
        (apUntruncatedProjectedPairingEdge n N h l) ε) :
    FaceCutDiscrepancyLe
      (apProjectedPairingEdge n N g j)
      (apProjectedPairingEdge n N h l)
      (Real.sqrt (3 * η) + ε + Real.sqrt (3 * η)) := by
  let Gsystem :=
    apHeterogeneousSimplexSystem n N g
  let Hsystem :=
    apHeterogeneousSimplexSystem n N h
  let Gmajorant :=
    apHeterogeneousSimplexSystem n N
      (apMaskedFaceMajorant ν activeG)
  let Hmajorant :=
    apHeterogeneousSimplexSystem n N
      (apMaskedFaceMajorant ν activeH)
  have hGmoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight Gmajorant j) η := by
    change
      HasProjectedMajorantMoments
        (apMaskedProjectedMajorant
          n N ν activeG j) η
    exact hLF.hasProjectedMajorantMoments_apMaskedProjection
      hν activeG j
  have hHmoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight Hmajorant l) η := by
    change
      HasProjectedMajorantMoments
        (apMaskedProjectedMajorant
          n N ν activeH l) η
    exact hLF.hasProjectedMajorantMoments_apMaskedProjection
      hν activeH l
  have hGj :
      ∀ x, 0 ≤ Gsystem.edgeWeight j x ∧
        Gsystem.edgeWeight j x ≤ 1 :=
    fun x => hgj _
  have hHl :
      ∀ x, 0 ≤ Hsystem.edgeWeight l x ∧
        Hsystem.edgeWeight l x ≤ 1 :=
    fun x => hhl _
  have hGrest :
      GeneralSimplexUntouchedBounds
        Gsystem Gmajorant j := by
    intro t x
    exact hgrest t _
  have hHrest :
      GeneralSimplexUntouchedBounds
        Hsystem Hmajorant l := by
    intro t x
    exact hhrest t _
  have hrawGeneral :
      FaceCutDiscrepancyLe
        (generalSimplexUntruncatedPairingEdge Gsystem j)
        (generalSimplexUntruncatedPairingEdge Hsystem l) ε := by
    exact hraw
  have hclosed :=
    hGmoments.faceCutDiscrepancyLe_projectedPairing_of_raw
      hHmoments hGj hHl hGrest hHrest hrawGeneral
  exact hclosed

/-- Explicit one-mask-update version of the nonlinear closure theorem. -/
theorem HasLinearFormsCondition.apProjectedPairingEdge_faceCutDiscrepancyLe_after_deactivate
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (n + 1) → Bool)
    {g h : APFaceWeightFamily n N}
    (j : Fin (n + 1))
    (hgj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hhj : ∀ z, 0 ≤ h j z ∧ h j z ≤ 1)
    (hgrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν active) j)
    (hhrest :
      APUntouchedFaceBounds h
        (apMaskedFaceMajorant ν
          (deactivateFace active j)) j)
    (hraw :
      FaceCutDiscrepancyLe
        (apUntruncatedProjectedPairingEdge n N g j)
        (apUntruncatedProjectedPairingEdge n N h j) ε) :
    FaceCutDiscrepancyLe
      (apProjectedPairingEdge n N g j)
      (apProjectedPairingEdge n N h j)
      (Real.sqrt (3 * η) + ε + Real.sqrt (3 * η)) :=
  hLF.apProjectedPairingEdge_faceCutDiscrepancyLe_of_raw
    hν active (deactivateFace active j)
    j j hgj hhj hgrest hhrest hraw

/-- Feed the nonlinear closure result into the exact re-embedded endpoint
comparison from `RelativeSimplexComparison`. -/
theorem HasLinearFormsCondition.apProjectedPairingSimplexCount_abs_sub_le_of_raw
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (activeG activeH : Fin (n + 1) → Bool)
    {g h : APFaceWeightFamily n N}
    (j l embeddedAt : Fin (n + 1))
    (hgj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hhl : ∀ z, 0 ≤ h l z ∧ h l z ≤ 1)
    (hgrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν activeG) j)
    (hhrest :
      APUntouchedFaceBounds h
        (apMaskedFaceMajorant ν activeH) l)
    (hraw :
      FaceCutDiscrepancyLe
        (apUntruncatedProjectedPairingEdge n N g j)
        (apUntruncatedProjectedPairingEdge n N h l) ε) :
    |(apProjectedPairingSimplexSystem
          n N g j embeddedAt).simplexCount -
        (apProjectedPairingSimplexSystem
          n N h l embeddedAt).simplexCount| ≤
      Real.sqrt (3 * η) + ε + Real.sqrt (3 * η) := by
  exact
    apProjectedPairingSimplexCount_abs_sub_le_of_faceCutDiscrepancy
      g h j l embeddedAt
      (hLF.apProjectedPairingEdge_faceCutDiscrepancyLe_of_raw
        hν activeG activeH j l hgj hhl hgrest hhrest hraw)

end Wikipedia.SzemeredisTheorem
