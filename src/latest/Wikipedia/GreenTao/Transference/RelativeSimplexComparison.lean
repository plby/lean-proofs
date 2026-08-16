import Wikipedia.SzemeredisTheorem.Hypergraph.WeakCounting
import Wikipedia.GreenTao.Transference.GeneralRelativeSimplexStep

/-!
# Cut-discrepancy comparison of bounded relative simplex states

For an arbitrary simplex edge, the natural discrepancy is tested directly
on its deleted-face coordinates against products of functions omitting one
face coordinate.  This is the same cut-test family used by
`FaceRegularityState.IsFaceCutRegular`, but here it compares two arbitrary
edge functions rather than a function and its conditional expectation.

The existing `simplexMixedCutTest` reconstructs the product of all
non-distinguished factors in an edge-by-edge telescoping term.  Consequently
face-cut discrepancy controls each mixed correlation whenever both simplex
systems are fully bounded.  Summing the correlations gives an actual
weighted-simplex comparison theorem with loss one `ε` per colour.

The final section specializes this comparison to the arbitrary whole-face
functions produced by recursive projection and re-embedding.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Direct face-cut discrepancy -/

/-- Correlation of a difference of arbitrary deleted-face functions with a
product of lower-face tests. -/
noncomputable def faceCutDifferenceCorrelation
    {G : Type*} [Fintype G] {r : ℕ}
    (f g : (Fin r → G) → ℝ)
    (u : CutTestFamily G r) : ℝ :=
  mean fun x =>
    (f x - g x) * cutTestProduct u x

/-- Two arbitrary functions on an `r`-coordinate face are `ε`-close in
face-cut discrepancy. -/
def FaceCutDiscrepancyLe
    {G : Type*} [Fintype G] {r : ℕ}
    (f g : (Fin r → G) → ℝ)
    (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |faceCutDifferenceCorrelation f g u| ≤ ε

theorem FaceCutDiscrepancyLe.apply
    {G : Type*} [Fintype G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε : ℝ}
    (h : FaceCutDiscrepancyLe f g ε)
    (u : CutTestFamily G r)
    (hu : IsBoundedCutTest u) :
    |faceCutDifferenceCorrelation f g u| ≤ ε :=
  h u hu

theorem FaceCutDiscrepancyLe.refl
    {G : Type*} [Fintype G] {r : ℕ}
    (f : (Fin r → G) → ℝ) :
    FaceCutDiscrepancyLe f f 0 := by
  intro u hu
  simp [faceCutDifferenceCorrelation]

theorem FaceCutDiscrepancyLe.mono
    {G : Type*} [Fintype G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε ε' : ℝ}
    (h : FaceCutDiscrepancyLe f g ε)
    (hε : ε ≤ ε') :
    FaceCutDiscrepancyLe f g ε' :=
  fun u hu => (h u hu).trans hε

theorem FaceCutDiscrepancyLe.symm
    {G : Type*} [Fintype G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε : ℝ}
    (h : FaceCutDiscrepancyLe f g ε) :
    FaceCutDiscrepancyLe g f ε := by
  intro u hu
  have hneg :
      faceCutDifferenceCorrelation g f u =
        -faceCutDifferenceCorrelation f g u := by
    unfold faceCutDifferenceCorrelation
    calc
      mean (fun x =>
          (g x - f x) * cutTestProduct u x) =
          mean (fun x =>
            (-1 : ℝ) *
              ((f x - g x) * cutTestProduct u x)) := by
        apply congrArg mean
        funext x
        ring
      _ = (-1 : ℝ) *
          mean (fun x =>
            (f x - g x) * cutTestProduct u x) :=
        mean_smul _ _
      _ = -faceCutDifferenceCorrelation f g u := by
        simp [faceCutDifferenceCorrelation]
  rw [hneg, abs_neg]
  exact h u hu

/-- The constant-one lower-face tests show that face-cut discrepancy
controls the difference of normalized means. -/
theorem FaceCutDiscrepancyLe.abs_mean_sub_le
    {G : Type*} [Fintype G] [Nonempty G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε : ℝ}
    (h : FaceCutDiscrepancyLe f g ε) :
    |mean f - mean g| ≤ ε := by
  have hone :=
    h (fun _ : Fin r =>
      fun _ : Fin (r - 1) → G => (1 : ℝ))
      isBoundedCutTest_one
  simpa [faceCutDifferenceCorrelation, cutTestProduct,
    ← mean_sub] using hone

theorem FaceCutDiscrepancyLe.epsilon_nonneg
    {G : Type*} [Fintype G] [Nonempty G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε : ℝ}
    (h : FaceCutDiscrepancyLe f g ε) :
    0 ≤ ε :=
  (abs_nonneg (mean f - mean g)).trans h.abs_mean_sub_le

/-! ## Edgewise discrepancy for arbitrary weighted simplices -/

/-- Every corresponding pair of canonical simplex edge functions is close
in face-cut discrepancy. -/
def EdgeFaceCutDiscrepancyLe
    {G : Type*} [Fintype G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (ε : ℝ) : Prop :=
  ∀ j,
    FaceCutDiscrepancyLe
      (canonicalEdgeFunction H j)
      (canonicalEdgeFunction K j) ε

/-- Fixing the distinguished simplex coordinate turns its mixed
telescoping term into the direct face residual paired with the reconstructed
bounded cut product. -/
theorem mixedSimplexTerm_insertNth_eq_faceCutDifference
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    mixedSimplexTerm H K j (Fin.insertNth j a y) =
      (canonicalEdgeFunction H j y -
        canonicalEdgeFunction K j y) *
      cutTestProduct (simplexMixedCutTest H K j a) y := by
  have hHj :
      H.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        canonicalEdgeFunction H j y := by
    simp [canonicalEdgeFunction,
      deleteCoordinate_eq_finTupleToDeletedVector]
  have hKj :
      K.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        canonicalEdgeFunction K j y := by
    simp [canonicalEdgeFunction,
      deleteCoordinate_eq_finTupleToDeletedVector]
  unfold mixedSimplexTerm
  rw [hHj, hKj]
  rw [show
      cutTestProduct (simplexMixedCutTest H K j a) y =
        (∏ i ∈ (Finset.univ :
            Finset (Fin (n + 1))) with i < j,
          H.edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i)) *
        ∏ i ∈ (Finset.univ :
            Finset (Fin (n + 1))) with j < i,
          K.edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i) by
      exact prod_simplexMixedCutTest_eraseCoordinate
        H K j a y]
  ring

/-- A generic mixed simplex correlation is an average, over the omitted
vertex, of direct face-cut correlations. -/
theorem mixedSimplexCorrelation_eq_mean_faceCutDifference
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    mixedSimplexCorrelation H K j =
      mean (fun a : G =>
        faceCutDifferenceCorrelation
          (canonicalEdgeFunction H j)
          (canonicalEdgeFunction K j)
          (simplexMixedCutTest H K j a)) := by
  unfold mixedSimplexCorrelation
  rw [mean_insertNth n j]
  unfold mean₂ faceCutDifferenceCorrelation
  apply congrArg mean
  funext a
  apply congrArg mean
  funext y
  exact mixedSimplexTerm_insertNth_eq_faceCutDifference
    H K j a y

/-- Face-cut discrepancy of the distinguished edge controls its mixed
telescoping correlation when every other factor is bounded. -/
theorem abs_mixedSimplexCorrelation_le_of_faceCutDiscrepancy
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1))
    {ε : ℝ}
    (hcut :
      FaceCutDiscrepancyLe
        (canonicalEdgeFunction H j)
        (canonicalEdgeFunction K j) ε) :
    |mixedSimplexCorrelation H K j| ≤ ε := by
  rw [mixedSimplexCorrelation_eq_mean_faceCutDifference]
  calc
    |mean (fun a : G =>
        faceCutDifferenceCorrelation
          (canonicalEdgeFunction H j)
          (canonicalEdgeFunction K j)
          (simplexMixedCutTest H K j a))| ≤
        mean (fun a : G =>
          |faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexMixedCutTest H K j a)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : G => ε) := by
      apply mean_mono
      intro a
      exact hcut
        (simplexMixedCutTest H K j a)
        (simplexMixedCutTest_bounded H K hH hK j a)
    _ = ε := mean_const _

/-- Uniform edgewise face-cut discrepancy controls every mixed
correlation. -/
theorem EdgeFaceCutDiscrepancyLe.mixedSimplexCorrelationLe
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε) :
    MixedSimplexCorrelationLe H K ε := by
  intro j
  exact abs_mixedSimplexCorrelation_le_of_faceCutDiscrepancy
    H K hH hK j (hcut j)

/-- Terminal fully bounded relative-simplex comparison in face-cut
discrepancy.  No sup-distance hypothesis is used. -/
theorem simplexCount_abs_sub_le_of_edgeFaceCutDiscrepancy
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε) :
    |H.simplexCount - K.simplexCount| ≤
      ((n + 1 : ℕ) : ℝ) * ε :=
  simplexCount_abs_sub_le_of_mixedCorrelation H K
    (hcut.mixedSimplexCorrelationLe H K hH hK)

/-! ## Bridge from the existing AP cut discrepancy -/

/-- On an AP edge, direct face-cut correlation is the existing transported
linear cut correlation with the canonical coefficient automorphisms. -/
theorem faceCutDifferenceCorrelation_apCanonicalEdge_eq_linearCutCorrelation
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial n))
    (f g : ZMod N → ℝ)
    (j : Fin (n + 1))
    (u : CutTestFamily (ZMod N) n) :
    faceCutDifferenceCorrelation
        (canonicalEdgeFunction
          (apSimplexSystem (n + 1) N f) j)
        (canonicalEdgeFunction
          (apSimplexSystem (n + 1) N g) j) u =
      linearCutCorrelation n
        (apFaceScalingEquiv hN j) f g u := by
  unfold faceCutDifferenceCorrelation linearCutCorrelation
  apply congrArg mean
  funext y
  change
    (f (apSimplexForm (n + 1) N j
        (finTupleToDeletedVector j y)) -
      g (apSimplexForm (n + 1) N j
        (finTupleToDeletedVector j y))) *
        cutTestProduct u y =
      (f (∑ i, apFaceScalingEquiv hN j i (y i)) -
        g (∑ i, apFaceScalingEquiv hN j i (y i))) *
        cutTestProduct u y
  rw [apSimplexForm_finTupleToDeletedVector]
  simp only [apFaceScalingEquiv_apply]

/-- Existing cut discrepancy supplies direct face-cut discrepancy on every
canonical AP simplex edge. -/
theorem CutDiscrepancyLe.faceCutDiscrepancyLe_apCanonicalEdge
    {n N : ℕ} [NeZero N]
    {f g : ZMod N → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe n f g ε)
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) :
    FaceCutDiscrepancyLe
      (canonicalEdgeFunction
        (apSimplexSystem (n + 1) N f) j)
      (canonicalEdgeFunction
        (apSimplexSystem (n + 1) N g) j) ε := by
  intro u hu
  rw [faceCutDifferenceCorrelation_apCanonicalEdge_eq_linearCutCorrelation
    n N hN f g j u]
  exact hcut.abs_linearCutCorrelation_le
    (apFaceScalingEquiv hN j) u hu

/-- Existing cut discrepancy therefore supplies the complete edgewise
face-cut hypothesis for the two AP simplex systems. -/
theorem CutDiscrepancyLe.edgeFaceCutDiscrepancyLe_apSimplexSystem
    {n N : ℕ} [NeZero N]
    {f g : ZMod N → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe n f g ε)
    (hN : Nat.Coprime N (Nat.factorial n)) :
    EdgeFaceCutDiscrepancyLe
      (apSimplexSystem (n + 1) N f)
      (apSimplexSystem (n + 1) N g) ε :=
  fun j =>
    hcut.faceCutDiscrepancyLe_apCanonicalEdge hN j

/-- AP specialization of the generic terminal comparison, stated directly
with the established `CutDiscrepancyLe` API. -/
theorem apSimplexCount_abs_sub_le_of_cutDiscrepancy
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial n))
    (f g : ZMod N → ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1)
    (hg : ∀ z, 0 ≤ g z ∧ g z ≤ 1)
    {ε : ℝ}
    (hcut : CutDiscrepancyLe n f g ε) :
    |(apSimplexSystem (n + 1) N f).simplexCount -
        (apSimplexSystem (n + 1) N g).simplexCount| ≤
      ((n + 1 : ℕ) : ℝ) * ε := by
  have hF :
      EdgeWeightsInUnitInterval
        (apSimplexSystem (n + 1) N f) :=
    fun _ x => hf (apSimplexForm (n + 1) N _ x)
  have hG :
      EdgeWeightsInUnitInterval
        (apSimplexSystem (n + 1) N g) :=
    fun _ x => hg (apSimplexForm (n + 1) N _ x)
  exact simplexCount_abs_sub_le_of_edgeFaceCutDiscrepancy
    (apSimplexSystem (n + 1) N f)
    (apSimplexSystem (n + 1) N g)
    hF hG
    (hcut.edgeFaceCutDiscrepancyLe_apSimplexSystem hN)

/-! ## Projected endpoint comparisons -/

/-- The whole-face weight carried by a generic projected state. -/
noncomputable def generalProjectedPairingEdge
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y =>
    generalSimplexProjectedSurrogate H j y *
      generalSimplexDistinguishedWeight H j y

@[simp]
theorem mean_generalProjectedPairingEdge
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    mean (generalProjectedPairingEdge H j) =
      generalSimplexDensifiedPairing H j :=
  rfl

/-- Face-cut control of two generic projected whole-face weights gives a
terminal comparison of their densified pairings. -/
theorem generalSimplexDensifiedPairing_abs_sub_le_of_faceCutDiscrepancy
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j l : Fin (n + 1))
    {ε : ℝ}
    (hcut :
      FaceCutDiscrepancyLe
        (generalProjectedPairingEdge H j)
        (generalProjectedPairingEdge K l) ε) :
    |generalSimplexDensifiedPairing H j -
        generalSimplexDensifiedPairing K l| ≤ ε := by
  simpa using hcut.abs_mean_sub_le

/-- A two-sided relative comparison step.  Densify each sparse system once,
compare the resulting bounded whole-face functions in face-cut discrepancy,
and add the two explicit truncation losses. -/
theorem HasProjectedMajorantMoments.generalSimplexCount_abs_sub_le_via_projectedFaceCut
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H K Hmajorant Kmajorant : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j l : Fin (n + 1)}
    {η θ ε : ℝ}
    (hHmoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight Hmajorant j) η)
    (hKmoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight Kmajorant l) θ)
    (hHj : ∀ x,
      0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1)
    (hKj : ∀ x,
      0 ≤ K.edgeWeight l x ∧ K.edgeWeight l x ≤ 1)
    (hHrest :
      GeneralSimplexUntouchedBounds H Hmajorant j)
    (hKrest :
      GeneralSimplexUntouchedBounds K Kmajorant l)
    (hcut :
      FaceCutDiscrepancyLe
        (generalProjectedPairingEdge H j)
        (generalProjectedPairingEdge K l) ε) :
    |H.simplexCount - K.simplexCount| ≤
      Real.sqrt (3 * η) + ε + Real.sqrt (3 * θ) := by
  have hleft :
      |H.simplexCount -
          generalSimplexDensifiedPairing H j| ≤
        Real.sqrt (3 * η) :=
    hHmoments.abs_generalSimplexCount_sub_densifiedPairing_le
      hHj hHrest
  have hmiddle :
      |generalSimplexDensifiedPairing H j -
          generalSimplexDensifiedPairing K l| ≤ ε :=
    generalSimplexDensifiedPairing_abs_sub_le_of_faceCutDiscrepancy
      H K j l hcut
  have hright :
      |generalSimplexDensifiedPairing K l -
          K.simplexCount| ≤ Real.sqrt (3 * θ) := by
    rw [abs_sub_comm]
    exact
      hKmoments.abs_generalSimplexCount_sub_densifiedPairing_le
        hKj hKrest
  calc
    |H.simplexCount - K.simplexCount| =
        |(H.simplexCount -
            generalSimplexDensifiedPairing H j) +
          (generalSimplexDensifiedPairing H j -
            generalSimplexDensifiedPairing K l) +
          (generalSimplexDensifiedPairing K l -
            K.simplexCount)| := by
      congr 1
      ring
    _ ≤
        |H.simplexCount -
            generalSimplexDensifiedPairing H j| +
          |generalSimplexDensifiedPairing H j -
            generalSimplexDensifiedPairing K l| +
          |generalSimplexDensifiedPairing K l -
            K.simplexCount| := by
      exact
        (abs_add_le
          ((H.simplexCount -
              generalSimplexDensifiedPairing H j) +
            (generalSimplexDensifiedPairing H j -
              generalSimplexDensifiedPairing K l))
          (generalSimplexDensifiedPairing K l -
            K.simplexCount)).trans <| by
          gcongr
          exact abs_add_le _ _
    _ ≤ Real.sqrt (3 * η) + ε + Real.sqrt (3 * θ) :=
      add_le_add (add_le_add hleft hmiddle) hright

/-- AP specialization of the two-sided relative comparison.  The common
linear-forms condition supplies both masked projected-moment packages; the
only remaining comparison hypothesis is face-cut discrepancy of the two
bounded projected whole-face weights. -/
theorem HasLinearFormsCondition.apHeterogeneousSimplexCount_abs_sub_le_via_projectedFaceCut
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (g h : APFaceWeightFamily n N)
    (activeG activeH : Fin (n + 1) → Bool)
    (j l : Fin (n + 1))
    (hgj : ∀ z, 0 ≤ g j z ∧ g j z ≤ 1)
    (hhl : ∀ z, 0 ≤ h l z ∧ h l z ≤ 1)
    (hgrest :
      APUntouchedFaceBounds g
        (apMaskedFaceMajorant ν activeG) j)
    (hhrest :
      APUntouchedFaceBounds h
        (apMaskedFaceMajorant ν activeH) l)
    (hcut :
      FaceCutDiscrepancyLe
        (apProjectedPairingEdge n N g j)
        (apProjectedPairingEdge n N h l) ε) :
    |(apHeterogeneousSimplexSystem n N g).simplexCount -
        (apHeterogeneousSimplexSystem n N h).simplexCount| ≤
      Real.sqrt (3 * η) + ε + Real.sqrt (3 * η) := by
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
    fun x => hgj (apSimplexForm (n + 1) N j x)
  have hHl :
      ∀ x, 0 ≤ Hsystem.edgeWeight l x ∧
        Hsystem.edgeWeight l x ≤ 1 :=
    fun x => hhl (apSimplexForm (n + 1) N l x)
  have hGrest :
      GeneralSimplexUntouchedBounds
        Gsystem Gmajorant j := by
    intro t x
    exact hgrest t
      (apSimplexForm (n + 1) N (j.succAbove t) x)
  have hHrest :
      GeneralSimplexUntouchedBounds
        Hsystem Hmajorant l := by
    intro t x
    exact hhrest t
      (apSimplexForm (n + 1) N (l.succAbove t) x)
  have hprojectedCut :
      FaceCutDiscrepancyLe
        (generalProjectedPairingEdge Gsystem j)
        (generalProjectedPairingEdge Hsystem l) ε := by
    exact hcut
  exact
    hGmoments.generalSimplexCount_abs_sub_le_via_projectedFaceCut
      hHmoments hGj hHl hGrest hHrest hprojectedCut

/-- Exact terminal comparison for the AP projected-pairing edges from
`RecursiveRelativeCount`. -/
theorem apHeterogeneousDensifiedPairing_abs_sub_le_of_faceCutDiscrepancy
    {n N : ℕ} [NeZero N]
    (g h : APFaceWeightFamily n N)
    (j l : Fin (n + 1))
    {ε : ℝ}
    (hcut :
      FaceCutDiscrepancyLe
        (apProjectedPairingEdge n N g j)
        (apProjectedPairingEdge n N h l) ε) :
    |apHeterogeneousDensifiedPairing n N g j -
        apHeterogeneousDensifiedPairing n N h l| ≤ ε := by
  change
    |mean (apProjectedPairingEdge n N g j) -
      mean (apProjectedPairingEdge n N h l)| ≤ ε
  exact hcut.abs_mean_sub_le

/-- Re-embedding the two projected edges at a common selectable colour
preserves the same terminal face-cut comparison. -/
theorem apProjectedPairingSimplexCount_abs_sub_le_of_faceCutDiscrepancy
    {n N : ℕ} [NeZero N]
    (g h : APFaceWeightFamily n N)
    (j l embeddedAt : Fin (n + 1))
    {ε : ℝ}
    (hcut :
      FaceCutDiscrepancyLe
        (apProjectedPairingEdge n N g j)
        (apProjectedPairingEdge n N h l) ε) :
    |(apProjectedPairingSimplexSystem
          n N g j embeddedAt).simplexCount -
        (apProjectedPairingSimplexSystem
          n N h l embeddedAt).simplexCount| ≤ ε := by
  rw [apProjectedPairingSimplexCount_eq,
    apProjectedPairingSimplexCount_eq]
  exact
    apHeterogeneousDensifiedPairing_abs_sub_le_of_faceCutDiscrepancy
      g h j l hcut

end Wikipedia.SzemeredisTheorem
