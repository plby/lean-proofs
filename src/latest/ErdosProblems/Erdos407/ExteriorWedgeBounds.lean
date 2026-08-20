/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.ExteriorEndpoint
import ErdosProblems.Erdos407.AdelicSuccessiveMinima
import ErdosProblems.Erdos407.AdelicMinimaUpper
import ErdosProblems.Erdos407.WeightedEvertseBasis

/-!
# The omitted-wedge saving in GLR Lemma 5.3

This file isolates the concrete combinatorics and determinant estimate used
at the exterior-power endpoint of the rational three-place Subspace Theorem.
For a split index `k`, the distinguished exterior coordinate is the tail
`{k, ..., n - 1}`.  Every other subset of the same cardinality contains an
index before `k`.  Evertse's pairwise-minimum basis estimate therefore saves
the adjacent-minimum ratio in the distinguished exterior row.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

namespace ExteriorWedgeBounds

open ExteriorEndpoint

/-! ## The smallest adjacent successive-minimum ratio -/

/-- The ratio across one adjacent pair in an ordered list of positive
successive minima.  The ambient list has length `m + 1`, while gaps are
indexed by `Fin m`. -/
noncomputable def adjacentRatio {m : ℕ} (μ : Fin (m + 1) → ℝ)
    (i : Fin m) : ℝ :=
  μ i.castSucc / μ i.succ

/-- A gap at which the adjacent ratio is smallest.  This is the gap used in
GLR §5.3 (equivalently, it is where the multiplicative jump is largest). -/
noncomputable def minAdjacentRatioIndex {m : ℕ} (hm : 0 < m)
    (μ : Fin (m + 1) → ℝ) : Fin m :=
  Classical.choose
    (Finset.exists_min_image Finset.univ (adjacentRatio μ)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩)

theorem minAdjacentRatioIndex_minimal {m : ℕ} (hm : 0 < m)
    (μ : Fin (m + 1) → ℝ) (i : Fin m) :
    adjacentRatio μ (minAdjacentRatioIndex hm μ) ≤ adjacentRatio μ i := by
  exact (Classical.choose_spec
    (Finset.exists_min_image Finset.univ (adjacentRatio μ)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

/-- The split point immediately after the selected gap. -/
noncomputable def selectedSplitIndex {m : ℕ} (hm : 0 < m)
    (μ : Fin (m + 1) → ℝ) : Fin (m + 1) :=
  (minAdjacentRatioIndex hm μ).succ

theorem selectedSplitIndex_pos {m : ℕ} (hm : 0 < m)
    (μ : Fin (m + 1) → ℝ) :
    0 < (selectedSplitIndex hm μ).val := by
  simp [selectedSplitIndex]

/-- The lower endpoint of a gap, in an ambient list of arbitrary length
`n ≥ 2`. -/
def gapLowerIndex {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by omega⟩

/-- The upper endpoint of a gap, hence the corresponding tail split. -/
def gapUpperIndex {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by omega⟩

@[simp] theorem gapLowerIndex_val {n : ℕ} (i : Fin (n - 1)) :
    (gapLowerIndex i).val = i.val := rfl

@[simp] theorem gapUpperIndex_val {n : ℕ} (i : Fin (n - 1)) :
    (gapUpperIndex i).val = i.val + 1 := rfl

noncomputable def ambientAdjacentRatio {n : ℕ} (lam : Fin n → ℝ)
    (i : Fin (n - 1)) : ℝ :=
  lam (gapLowerIndex i) / lam (gapUpperIndex i)

/-- A minimum adjacent ratio for an `n`-tuple, using only `2 ≤ n`. -/
noncomputable def ambientMinRatioIndex {n : ℕ} (hn : 2 ≤ n)
    (lam : Fin n → ℝ) : Fin (n - 1) :=
  Classical.choose
    (Finset.exists_min_image Finset.univ (ambientAdjacentRatio lam)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)

theorem ambientMinRatioIndex_minimal {n : ℕ} (hn : 2 ≤ n)
    (lam : Fin n → ℝ) (i : Fin (n - 1)) :
    ambientAdjacentRatio lam (ambientMinRatioIndex hn lam) ≤
      ambientAdjacentRatio lam i := by
  exact (Classical.choose_spec
    (Finset.exists_min_image Finset.univ (ambientAdjacentRatio lam)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

noncomputable def ambientSelectedSplit {n : ℕ} (hn : 2 ≤ n)
    (lam : Fin n → ℝ) : Fin n :=
  gapUpperIndex (ambientMinRatioIndex hn lam)

theorem ambientSelectedSplit_pos {n : ℕ} (hn : 2 ≤ n)
    (lam : Fin n → ℝ) :
    0 < (ambientSelectedSplit hn lam).val := by
  simp [ambientSelectedSplit]

/-- The exact ordered-minima interface needed by the exterior endpoint.
`AdelicMinima.AdaptedBasisCertificate` instantiates it by projection, while
the exterior argument remains independent of how the minima were built. -/
structure OrderedMinimaData (n : ℕ) where
  lambda : Fin n → ℝ
  point : Fin n → Fin n → ℚ
  lambda_pos : ∀ j, 0 < lambda j
  lambda_mono : Monotone lambda
  independent : LinearIndependent ℚ point
  sIntegral : ∀ j, AdelicMinkowski.InZOneSix (point j)

/-- Forget the rank-boundary fields of the concrete adelic certificate and
retain exactly the data consumed by the exterior argument. -/
def OrderedMinimaData.ofAdaptedBasisCertificate {n : ℕ}
    {L : AdelicMinima.LocalForms n} {Q : ℕ}
    {c : HeightBoxes.LocalConstants n}
    (B : AdelicMinima.AdaptedBasisCertificate L Q c) : OrderedMinimaData n :=
  { lambda := B.lambda
    point := B.point
    lambda_pos := B.lambda_pos
    lambda_mono := B.lambda_mono
    independent := B.independent
    sIntegral := B.sIntegral }

/-- The minimum factor is active only at the Archimedean place. -/
def certificatePlaceScale {n : ℕ} (B : OrderedMinimaData n)
    (place : Place23) (j : Fin n) : ℝ :=
  if place = Place23.infinite then B.lambda j else 1

theorem certificatePlaceScale_pos {n : ℕ} (B : OrderedMinimaData n)
    (place : Place23) (j : Fin n) :
    0 < certificatePlaceScale B place j := by
  by_cases h : place = Place23.infinite
  · simp [certificatePlaceScale, h, B.lambda_pos j]
  · simp [certificatePlaceScale, h]

theorem certificatePlaceScale_monotone {n : ℕ} (B : OrderedMinimaData n)
    (place : Place23) : Monotone (certificatePlaceScale B place) := by
  by_cases h : place = Place23.infinite
  · subst place
    change Monotone B.lambda
    exact B.lambda_mono
  · intro i j hij
    simp [certificatePlaceScale, h]

/-- Output interface of the weighted Evertse lemma.  The construction in
`WeightedEvertseBasis` supplies this data, including its genuine triangular
`Z[1/6]` change of basis; the exterior estimates consume only the displayed
pairwise bound and its integrity fields. -/
structure WeightedEvertseData {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (B : OrderedMinimaData n) (ρ : Place23 → Fin n → ℝ) where
  change : Matrix (Fin n) (Fin n) ℚ
  change_lower : EvertseBasis.IsUnitLowerTriangular change
  change_sIntegral : ∀ i j,
    AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ change i j)
  vector : Fin n → Fin n → ℚ
  vector_eq : vector = EvertseBasis.transformBasis change B.point
  permutation : Place23 → Equiv.Perm (Fin n)
  coefficient : Place23 → ℝ
  coefficient_pos : ∀ place, 0 < coefficient place
  coefficient_nonneg : ∀ place, 0 ≤ coefficient place
  independent : LinearIndependent ℚ vector
  sIntegral : ∀ j, AdelicMinkowski.InZOneSix (vector j)
  pairwise : ∀ place i j,
    HeightBoxes.realPlaceNorm place
        (permutedLocalForms L permutation place i (vector j)) ≤
      coefficient place * ρ place (permutation place i) *
        min (certificatePlaceScale B place i)
          (certificatePlaceScale B place j)

/-- One fixed choice of the outer Evertse constant.  Crucially this depends
only on the fixed local forms, not on `Q`, the exponent array, the row radii,
or the successive-minimum certificate. -/
noncomputable def weightedEvertseConstant {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L) : ℝ :=
  Classical.choose (WeightedEvertseBasis.exists_weightedEvertseBasis L hL)

theorem one_le_weightedEvertseConstant {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L) :
    1 ≤ weightedEvertseConstant L hL :=
  (Classical.choose_spec
    (WeightedEvertseBasis.exists_weightedEvertseBasis L hL)).1

/-- The fixed placewise loss attached to `L`; this is the coefficient used
by every weighted Evertse basis subsequently constructed for these forms. -/
noncomputable def fixedWeightedEvertseCoefficient {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L) :
    Place23 → ℝ :=
  fun place ↦ WeightedEvertseBasis.rowApproxFactor place *
    (if place = Place23.infinite then weightedEvertseConstant L hL else 1)

/-- The constructive weighted Evertse lemma produces the exact endpoint
package from an ordered-minima basis and its row radii, and exposes that its
coefficient is the fixed function depending only on `L`. -/
theorem exists_weightedEvertseData_fixedCoefficient {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (B : OrderedMinimaData n)
    (ρ : Place23 → Fin n → ℝ)
    (hρ : ∀ place i, 0 < ρ place i)
    (hlocal : ∀ place i j,
      HeightBoxes.realPlaceNorm place (L place i (B.point j)) ≤
        ρ place i * certificatePlaceScale B place j) :
    ∃ E : WeightedEvertseData L B ρ,
      E.coefficient = fixedWeightedEvertseCoefficient L hL := by
  let C := weightedEvertseConstant L hL
  have hC : 1 ≤ C := one_le_weightedEvertseConstant L hL
  have hE := (Classical.choose_spec
    (WeightedEvertseBasis.exists_weightedEvertseBasis L hL)).2
  obtain ⟨A, hAlower, hAS, hvLI, hvS, π, hpair⟩ :=
    hE B.point ρ (certificatePlaceScale B) B.independent B.sIntegral hρ
      (certificatePlaceScale_pos B) (certificatePlaceScale_monotone B) hlocal
  let coeff : Place23 → ℝ := fun place ↦
    WeightedEvertseBasis.rowApproxFactor place *
      (if place = Place23.infinite then C else 1)
  refine ⟨{
    change := A
    change_lower := hAlower
    change_sIntegral := hAS
    vector := EvertseBasis.transformBasis A B.point
    vector_eq := rfl
    permutation := π
    coefficient := coeff
    coefficient_pos := ?_
    coefficient_nonneg := ?_
    independent := hvLI
    sIntegral := hvS
    pairwise := ?_ }, ?_⟩
  · intro place
    exact mul_pos
      (zero_lt_one.trans_le (WeightedEvertseBasis.one_le_rowApproxFactor place))
      (by split_ifs <;> linarith)
  · intro place
    exact mul_nonneg
      (zero_le_one.trans (WeightedEvertseBasis.one_le_rowApproxFactor place))
      (by split_ifs <;> linarith)
  · intro place i j
    exact hpair place i j
  · rfl

/-- Compatibility wrapper when only nonemptiness is needed. -/
theorem nonempty_weightedEvertseData {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (B : OrderedMinimaData n)
    (ρ : Place23 → Fin n → ℝ)
    (hρ : ∀ place i, 0 < ρ place i)
    (hlocal : ∀ place i j,
      HeightBoxes.realPlaceNorm place (L place i (B.point j)) ≤
        ρ place i * certificatePlaceScale B place j) :
    Nonempty (WeightedEvertseData L B ρ) := by
  obtain ⟨E, _⟩ := exists_weightedEvertseData_fixedCoefficient
    L hL B ρ hρ hlocal
  exact ⟨E⟩

/-- Direct specialization to the constructed three-place adapted-basis
certificate, retaining the fixed-coefficient identity. -/
theorem exists_weightedEvertseData_fixedCoefficient_of_adaptedBasisCertificate
    {n : ℕ} (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B : AdelicMinima.AdaptedBasisCertificate L Q c) :
    ∃ E : WeightedEvertseData L
        (OrderedMinimaData.ofAdaptedBasisCertificate B)
        (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
      E.coefficient = fixedWeightedEvertseCoefficient L hL := by
  apply exists_weightedEvertseData_fixedCoefficient L hL
    (OrderedMinimaData.ofAdaptedBasisCertificate B)
  · intro place i
    exact AdelicMinima.exponentRadius_pos_of_one_le hQ c place i
  · intro place i j
    simpa [OrderedMinimaData.ofAdaptedBasisCertificate,
      certificatePlaceScale, AdelicMinima.placeScale, mul_comm] using
      B.local_bound j place i

/-- Compatibility form of the adapted-certificate constructor. -/
theorem nonempty_weightedEvertseData_of_adaptedBasisCertificate
    {n : ℕ} (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B : AdelicMinima.AdaptedBasisCertificate L Q c) :
    Nonempty (WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate B)
      (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i)) := by
  obtain ⟨E, _⟩ :=
    exists_weightedEvertseData_fixedCoefficient_of_adaptedBasisCertificate
      L hL hQ c B
  exact ⟨E⟩

/-- Unconditional joint construction of the genuine upper-product adapted
certificate and its fixed-coefficient weighted Evertse basis. -/
theorem exists_upperCertificate_fixedWeightedEvertseData
    {n : ℕ} (hn : 0 < n) (L : AdelicMinima.LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : HeightBoxes.LocalConstants n) :
    ∃ A : AdelicMinimaUpper.UpperAdaptedBasisCertificate
        L Q c (AdelicMinimaUpper.upperConstant L),
      ∃ E : WeightedEvertseData L
          (OrderedMinimaData.ofAdaptedBasisCertificate
            A.toAdaptedBasisCertificate)
          (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
        E.coefficient = fixedWeightedEvertseCoefficient L hL := by
  obtain ⟨A⟩ := AdelicMinimaUpper.exists_upperAdaptedBasisCertificate
    hn L hL hQ c
  obtain ⟨E, hcoeff⟩ :=
    exists_weightedEvertseData_fixedCoefficient_of_adaptedBasisCertificate
      L hL hQ c A.toAdaptedBasisCertificate
  exact ⟨A, E, hcoeff⟩

/-- The selected gap extracted directly from ordered successive-minima
data. -/
noncomputable def certificateGapIndex {n : ℕ} (hn : 2 ≤ n)
    (B : OrderedMinimaData n) : Fin (n - 1) :=
  ambientMinRatioIndex hn B.lambda

noncomputable def certificateSplitIndex {n : ℕ}
    (hn : 2 ≤ n) (B : OrderedMinimaData n) : Fin n :=
  gapUpperIndex (certificateGapIndex hn B)

theorem certificateGapIndex_minimal {n : ℕ}
    (hn : 2 ≤ n) (B : OrderedMinimaData n) (i : Fin (n - 1)) :
    ambientAdjacentRatio B.lambda (certificateGapIndex hn B) ≤
      ambientAdjacentRatio B.lambda i :=
  ambientMinRatioIndex_minimal hn B.lambda i

theorem certificateSplitIndex_pos {n : ℕ}
    (hn : 2 ≤ n) (B : OrderedMinimaData n) :
    0 < (certificateSplitIndex hn B).val := by
  simp [certificateSplitIndex]

/-! ## The distinguished tail coordinate -/

/-- The predecessor of a nonzero split index, kept in the same ambient
`Fin n` type. -/
def splitPredecessor {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val) : Fin n :=
  ⟨κ.val - 1, by omega⟩

@[simp] theorem splitPredecessor_val {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) :
    (splitPredecessor κ hκ).val = κ.val - 1 := rfl

theorem splitPredecessor_lt {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) :
    splitPredecessor κ hκ < κ := by
  change κ.val - 1 < κ.val
  omega

theorem le_splitPredecessor_of_lt {n : ℕ} {κ i : Fin n}
    (hκ : 0 < κ.val) (hi : i < κ) :
    i ≤ splitPredecessor κ hκ := by
  change i.val ≤ κ.val - 1
  omega

/-- The distinguished `q = n-k` exterior coordinate is the terminal
interval `{k, ..., n-1}`. -/
noncomputable def tailExteriorIndex {n : ℕ} (κ : Fin n) :
    Set.powersetCard (Fin n) (n - κ.val) :=
  ⟨Finset.Ici κ, by simp⟩

@[simp] theorem mem_tailExteriorIndex {n : ℕ} (κ i : Fin n) :
    i ∈ (tailExteriorIndex κ : Finset (Fin n)) ↔ κ ≤ i := by
  simp [tailExteriorIndex]

/-- Every row index in the distinguished tail is at least the split. -/
theorem tailExteriorIndex_enum_ge {n : ℕ} (κ : Fin n)
    (a : Fin (n - κ.val)) :
    κ ≤ Set.powersetCard.ofFinEmbEquiv.symm (tailExteriorIndex κ) a := by
  apply (mem_tailExteriorIndex κ _).mp
  exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    (tailExteriorIndex κ) _).mp ⟨a, rfl⟩

/-- Any exterior coordinate different from the tail contains a column
strictly before the split. -/
theorem exists_enum_lt_of_ne_tail {n : ℕ} (κ : Fin n)
    (J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    ∃ b : Fin (n - κ.val),
      Set.powersetCard.ofFinEmbEquiv.symm J b < κ := by
  obtain ⟨i, hiJ, hitail⟩ :=
    (Set.powersetCard.exists_mem_notMem_iff_ne J
      (tailExteriorIndex κ)).mp hJ
  have hirange : i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm J) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J i).mpr hiJ
  obtain ⟨b, rfl⟩ := hirange
  refine ⟨b, lt_of_not_ge ?_⟩
  intro hge
  exact hitail ((mem_tailExteriorIndex κ _).mpr hge)

/-- Monotonicity converts tail membership into the lower row scale. -/
theorem tail_scale_le {n : ℕ} (κ : Fin n) (μ : Fin n → ℝ)
    (hμ : Monotone μ) (a : Fin (n - κ.val)) :
    μ κ ≤ μ (Set.powersetCard.ofFinEmbEquiv.symm
      (tailExteriorIndex κ) a) :=
  hμ (tailExteriorIndex_enum_ge κ a)

/-- Monotonicity converts the early column in every omitted coordinate into
the upper scale immediately before the split. -/
theorem exists_omitted_column_scale_le {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) (μ : Fin n → ℝ) (hμ : Monotone μ)
    (J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    ∃ b : Fin (n - κ.val),
      μ (Set.powersetCard.ofFinEmbEquiv.symm J b) ≤
        μ (splitPredecessor κ hκ) := by
  obtain ⟨b, hb⟩ := exists_enum_lt_of_ne_tail κ J hJ
  exact ⟨b, hμ (le_splitPredecessor_of_lt hκ hb)⟩

/-! ## Recovering the original prefix subspace -/

/-- The vectors complementary to the tail are exactly the first `k` basis
vectors.  This identifies the original subspace recovered from the omitted
exterior hyperplane. -/
theorem prefixSpan_eq_basisComplementSubspace {n : ℕ}
    (v : Fin n → Fin n → ℚ) (κ : Fin n) :
    Submodule.span ℚ
        (Set.range (fun i : Fin κ.val ↦
          v (Fin.castLE (Nat.le_of_lt κ.isLt) i))) =
      basisComplementSubspace v (tailExteriorIndex κ) := by
  rw [basisComplementSubspace]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    let j : {j : Fin n // j ∉ (tailExteriorIndex κ).1} :=
      ⟨Fin.castLE (Nat.le_of_lt κ.isLt) i, by
        rw [mem_tailExteriorIndex]
        exact not_le.mpr (by
          change i.val < κ.val
          exact i.isLt)⟩
    exact ⟨j, rfl⟩
  · rintro ⟨i, rfl⟩
    have hi : i.1 < κ := by
      exact lt_of_not_ge (by
        intro hge
        exact i.2 ((mem_tailExteriorIndex κ i.1).mpr hge))
    let j : Fin κ.val := ⟨i.1.val, hi⟩
    refine ⟨j, ?_⟩
    exact congrArg v (Fin.ext (by rfl))

/-- Any smaller initial span is contained in the complement recovered from
the tail coordinate. -/
theorem initialSpan_le_basisComplementSubspace {n r : ℕ}
    (v : Fin n → Fin n → ℚ) (κ : Fin n) (hr : r ≤ κ.val) :
    Submodule.span ℚ
        (Set.range (fun i : Fin r ↦
          v (Fin.castLE (hr.trans (Nat.le_of_lt κ.isLt)) i))) ≤
      basisComplementSubspace v (tailExteriorIndex κ) := by
  rw [← prefixSpan_eq_basisComplementSubspace v κ]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  let j : Fin κ.val := Fin.castLE hr i
  refine ⟨j, ?_⟩
  exact congrArg v (Fin.ext (by rfl))

/-- A lower-triangular change sends its first `r` rows into the span of the
first `r` original vectors. -/
theorem transformPrefixSpan_le {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → Fin n → ℚ)
    (hr : r ≤ n) (hA : A.IsLowerTriangular) :
    Submodule.span ℚ (Set.range (fun i : Fin r ↦
        EvertseBasis.transformBasis A x (Fin.castLE hr i))) ≤
      Submodule.span ℚ (Set.range (fun i : Fin r ↦ x (Fin.castLE hr i))) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (∑ j, A (Fin.castLE hr i) j • x j) ∈ _
  apply Submodule.sum_mem
  intro j _
  by_cases hij : Fin.castLE hr i < j
  · have hz : A (Fin.castLE hr i) j = 0 := hA hij
    simpa [hz] using (Submodule.zero_mem
      (Submodule.span ℚ (Set.range (fun i : Fin r ↦ x (Fin.castLE hr i)))))
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    have hjr : j.val < r := by
      have hji : j ≤ Fin.castLE hr i := le_of_not_gt hij
      exact lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hji) i.isLt
    let k : Fin r := ⟨j.val, hjr⟩
    refine ⟨k, ?_⟩
    exact congrArg x (Fin.ext (by rfl))

/-- For linearly independent bases, the preceding inclusion is equality. -/
theorem transformPrefixSpan_eq {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → Fin n → ℚ)
    (hr : r ≤ n) (hA : EvertseBasis.IsUnitLowerTriangular A)
    (hx : LinearIndependent ℚ x) :
    Submodule.span ℚ (Set.range (fun i : Fin r ↦
        EvertseBasis.transformBasis A x (Fin.castLE hr i))) =
      Submodule.span ℚ (Set.range (fun i : Fin r ↦ x (Fin.castLE hr i))) := by
  apply Submodule.eq_of_le_of_finrank_eq (transformPrefixSpan_le A x hr hA.1)
  rw [finrank_span_eq_card, finrank_span_eq_card]
  · exact hx.comp (Fin.castLE hr) (Fin.castLE_injective hr)
  · exact (ExteriorEndpoint.evertseTransform_linearIndependent hA hx).comp
      (Fin.castLE hr) (Fin.castLE_injective hr)

/-- Any original prefix below the selected split lies in the complementary
subspace recovered from the omitted exterior hyperplane of the transformed
basis. -/
theorem orderedCertificate_initialSpan_le_recoveredComplement
    {n r : ℕ} (hn : 2 ≤ n) (B : OrderedMinimaData n)
    {L : Place23 → Fin n → RatLinearForm n}
    {ρ : Place23 → Fin n → ℝ} (E : WeightedEvertseData L B ρ)
    (hr : r ≤ (certificateSplitIndex hn B).val) :
    Submodule.span ℚ (Set.range (fun i : Fin r ↦
        B.point (Fin.castLE
          (hr.trans (Nat.le_of_lt (certificateSplitIndex hn B).isLt)) i))) ≤
      basisComplementSubspace E.vector
        (tailExteriorIndex (certificateSplitIndex hn B)) := by
  rw [E.vector_eq]
  rw [← transformPrefixSpan_eq E.change B.point
    (hr.trans (Nat.le_of_lt (certificateSplitIndex hn B).isLt))
    E.change_lower B.independent]
  exact initialSpan_le_basisComplementSubspace
    (EvertseBasis.transformBasis E.change B.point)
    (certificateSplitIndex hn B) hr

/-- If the scale-one rank lies below the selected split, the actual
approximation span is contained in the original subspace recovered from the
exterior hyperplane. -/
theorem adaptedApproximationSpan_le_recoveredComplement
    {n : ℕ} (hn : 2 ≤ n)
    (L : AdelicMinima.LocalForms n) {Q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) ρ)
    (hrank : B₀.rank ≤ (certificateSplitIndex hn
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀)).val) :
    Erdos407.RankDrop.realSApproximationSpan L Q c ≤
      basisComplementSubspace E.vector
        (tailExteriorIndex (certificateSplitIndex hn
          (OrderedMinimaData.ofAdaptedBasisCertificate B₀))) := by
  let B := OrderedMinimaData.ofAdaptedBasisCertificate B₀
  have hrank' : B₀.rank ≤ n := B₀.rank_le
  have hsplit : B₀.rank ≤ n :=
    hrank.trans (Nat.le_of_lt (certificateSplitIndex hn B).isLt)
  have hfun :
      (fun i : Fin B₀.rank ↦
        B.point (Fin.castLE hsplit i)) =
        B₀.point ∘ Fin.castLE hrank' := by
    funext i
    apply congrArg B₀.point
    apply Fin.ext
    rfl
  rw [← B₀.prefix_span, ← hfun]
  exact orderedCertificate_initialSpan_le_recoveredComplement hn B E hrank

/-! ## The concrete omitted-wedge determinant estimate -/

/-- The adjacent ratio saved by the distinguished exterior coordinate. -/
noncomputable def distinguishedRatio {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) (μ : Fin n → ℝ) : ℝ :=
  μ (splitPredecessor κ hκ) / μ κ

theorem splitPredecessor_gapUpperIndex {n : ℕ} (i : Fin (n - 1)) :
    splitPredecessor (gapUpperIndex i) (by simp) = gapLowerIndex i := by
  apply Fin.ext
  simp [splitPredecessor]

theorem distinguishedRatio_certificateSplit {n : ℕ}
    (hn : 2 ≤ n) (B : OrderedMinimaData n) :
    distinguishedRatio (certificateSplitIndex hn B)
        (certificateSplitIndex_pos hn B) B.lambda =
      ambientAdjacentRatio B.lambda (certificateGapIndex hn B) := by
  unfold distinguishedRatio ambientAdjacentRatio certificateSplitIndex
  rw [splitPredecessor_gapUpperIndex]

theorem distinguishedRatio_certificatePlaceScale_infinite {n : ℕ}
    (hn : 2 ≤ n) (B : OrderedMinimaData n) :
    distinguishedRatio (certificateSplitIndex hn B)
        (certificateSplitIndex_pos hn B)
        (certificatePlaceScale B Place23.infinite) =
      ambientAdjacentRatio B.lambda (certificateGapIndex hn B) := by
  change distinguishedRatio (certificateSplitIndex hn B)
      (certificateSplitIndex_pos hn B) B.lambda = _
  exact distinguishedRatio_certificateSplit hn B

theorem distinguishedRatio_certificatePlaceScale_finite {n : ℕ}
    (hn : 2 ≤ n) (B : OrderedMinimaData n) (place : Place23)
    (hplace : place ≠ Place23.infinite) :
    distinguishedRatio (certificateSplitIndex hn B)
        (certificateSplitIndex_pos hn B) (certificatePlaceScale B place) = 1 := by
  rw [distinguishedRatio]
  simp [certificatePlaceScale, hplace]

theorem distinguishedRatio_nonneg {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) :
    0 ≤ distinguishedRatio κ hκ μ := by
  exact div_nonneg (hμ _).le (hμ _).le

theorem distinguishedRatio_le_one {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (hmono : Monotone μ) :
    distinguishedRatio κ hκ μ ≤ 1 := by
  rw [distinguishedRatio, div_le_one (hμ κ)]
  exact hmono (splitPredecessor_lt κ hκ).le

/-! ### The rank-tail gap

The global minimum gap need not lie after the scale-one rank.  For recovery
one instead minimizes over the `n - R` gaps whose split indices are
`R, ..., n - 1`.  The first numerator is then `lambda_(R-1) ≤ 1`, while the
last denominator is the final successive minimum. -/

theorem prod_adjacentRatio {m : ℕ} (μ : Fin (m + 1) → ℝ)
    (hμ : ∀ i, μ i ≠ 0) :
    (∏ i : Fin m, adjacentRatio μ i) = μ 0 / μ (Fin.last m) := by
  induction m with
  | zero =>
      simp [hμ]
  | succ m ih =>
      rw [Fin.prod_univ_succ]
      change μ 0 / μ 1 *
          (∏ i, adjacentRatio (fun j => μ j.succ) i) = _
      rw [ih (fun i => μ i.succ) (fun i => hμ i.succ)]
      have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
        apply Fin.ext
        simp
      rw [hlast]
      have hone : (1 : Fin (m + 1 + 1)) = Fin.succ 0 := by
        apply Fin.ext
        simp
      rw [hone]
      field_simp [hμ]

theorem minAdjacentRatio_pow_le_prod {m : ℕ} (hm : 0 < m)
    (μ : Fin (m + 1) → ℝ) (hμ : ∀ i, 0 < μ i) :
    (adjacentRatio μ (minAdjacentRatioIndex hm μ)) ^ m ≤
      ∏ i : Fin m, adjacentRatio μ i := by
  calc
    (adjacentRatio μ (minAdjacentRatioIndex hm μ)) ^ m =
        ∏ _i : Fin m, adjacentRatio μ (minAdjacentRatioIndex hm μ) := by
      simp
    _ ≤ ∏ i : Fin m, adjacentRatio μ i := by
      apply Finset.prod_le_prod
      · intro i _
        exact (div_pos (hμ _) (hμ _)).le
      · intro i _
        exact minAdjacentRatioIndex_minimal hm μ i

/-- The ordered segment `lambda_(R-1), ..., lambda_(n-1)` containing exactly
the gaps whose split lies at or after rank `R`. -/
def rankTailMinima {n R : ℕ} (hRpos : 0 < R) (hRlt : R < n)
    (lam : Fin n → ℝ) : Fin (n - R + 1) → ℝ :=
  fun i => lam ⟨R - 1 + i.val, by omega⟩

/-- Convert a gap in the rank-tail segment to its ambient split index. -/
def rankTailSplit {n R : ℕ} (hRlt : R < n)
    (i : Fin (n - R)) : Fin n :=
  ⟨R + i.val, by omega⟩

noncomputable def rankTailMinRatioIndex {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ) :
    Fin (n - R) :=
  minAdjacentRatioIndex (Nat.sub_pos_of_lt hRlt)
    (rankTailMinima hRpos hRlt lam)

/-- The recovery-compatible split: the smallest ratio among all gaps from
the scale-one boundary through the final minimum. -/
noncomputable def rankTailSelectedSplit {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ) : Fin n :=
  rankTailSplit hRlt (rankTailMinRatioIndex hRpos hRlt lam)

theorem rankTailSelectedSplit_ge {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ) :
    R ≤ (rankTailSelectedSplit hRpos hRlt lam).val := by
  simp [rankTailSelectedSplit, rankTailSplit]

theorem rankTailSelectedSplit_pos {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ) :
    0 < (rankTailSelectedSplit hRpos hRlt lam).val :=
  hRpos.trans_le (rankTailSelectedSplit_ge hRpos hRlt lam)

theorem rankTailRatio_eq_distinguished {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ)
    (i : Fin (n - R)) :
    adjacentRatio (rankTailMinima hRpos hRlt lam) i =
      distinguishedRatio (rankTailSplit hRlt i)
        (by simp [rankTailSplit]; omega) lam := by
  unfold adjacentRatio rankTailMinima distinguishedRatio
  congr 2 <;> apply Fin.ext <;>
    simp [rankTailSplit, splitPredecessor] <;> omega

@[simp] theorem rankTailMinima_zero {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ) :
    rankTailMinima hRpos hRlt lam 0 = lam ⟨R - 1, by omega⟩ :=
  rfl

@[simp] theorem rankTailMinima_last {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n) (lam : Fin n → ℝ) :
    rankTailMinima hRpos hRlt lam (Fin.last (n - R)) =
      lam ⟨n - 1, by omega⟩ := by
  unfold rankTailMinima
  congr 1
  apply Fin.ext
  simp
  omega

/-- Multiplicative pigeonhole on the recovery-compatible tail.  If the last
minimum is at least `Q^a`, one selected adjacent ratio saves
`Q^(-a/(n-R))`. -/
theorem rankTailSelectedRatio_le_rpow {n R : ℕ}
    (hRpos : 0 < R) (hRlt : R < n)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    {Q a : ℝ} (hQ : 1 < Q)
    (hpre : lam ⟨R - 1, by omega⟩ ≤ 1)
    (hlast : Q ^ a ≤ lam ⟨n - 1, by omega⟩) :
    distinguishedRatio (rankTailSelectedSplit hRpos hRlt lam)
        (rankTailSelectedSplit_pos hRpos hRlt lam) lam ≤
      Q ^ (-a / (n - R : ℕ)) := by
  let μ := rankTailMinima hRpos hRlt lam
  let m := n - R
  have hm : 0 < m := Nat.sub_pos_of_lt hRlt
  let i₀ := minAdjacentRatioIndex hm μ
  have hratio :
      distinguishedRatio (rankTailSelectedSplit hRpos hRlt lam)
          (rankTailSelectedSplit_pos hRpos hRlt lam) lam =
        adjacentRatio μ i₀ := by
    symm
    exact rankTailRatio_eq_distinguished hRpos hRlt lam i₀
  rw [hratio]
  have hpow : (adjacentRatio μ i₀) ^ m ≤
      lam ⟨R - 1, by omega⟩ / lam ⟨n - 1, by omega⟩ := by
    calc
      (adjacentRatio μ i₀) ^ m ≤ ∏ i : Fin m, adjacentRatio μ i :=
        minAdjacentRatio_pow_le_prod hm μ (fun _ => hlam _)
      _ = μ 0 / μ (Fin.last m) :=
        prod_adjacentRatio μ (fun _ => (hlam _).ne')
      _ = lam ⟨R - 1, by omega⟩ / lam ⟨n - 1, by omega⟩ := by
        dsimp only [μ, m]
        rw [rankTailMinima_zero, rankTailMinima_last]
  have hquot : lam ⟨R - 1, by omega⟩ / lam ⟨n - 1, by omega⟩ ≤
      Q ^ (-a) := by
    calc
      lam ⟨R - 1, by omega⟩ / lam ⟨n - 1, by omega⟩ ≤
          1 / Q ^ a :=
        div_le_div₀ zero_le_one hpre
          (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) a) hlast
      _ = Q ^ (-a) := by
        rw [Real.rpow_neg (zero_lt_one.trans hQ).le]
        exact one_div _
  apply (pow_le_pow_iff_left₀
    (div_pos (hlam _) (hlam _)).le
    (Real.rpow_nonneg (zero_lt_one.trans hQ).le _) hm.ne').mp
  calc
    (adjacentRatio μ i₀) ^ m ≤ Q ^ (-a) := hpow.trans hquot
    _ = (Q ^ (-a / (m : ℝ))) ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hQ).le]
      congr 1
      field_simp
    _ = (Q ^ (-a / (n - R : ℕ))) ^ m := by rfl

/-- Adapted-certificate form of the tail-gap estimate.  The numerator bound
is supplied by the scale-one boundary field of the certificate. -/
theorem adaptedRankTailSelectedRatio_le_rpow
    {n : ℕ} (L : AdelicMinima.LocalForms n) {Q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {base a : ℝ} (hbase : 1 < base)
    (hlast : base ^ a ≤ B₀.lambda ⟨n - 1, by omega⟩) :
    distinguishedRatio
        (rankTailSelectedSplit hRpos hRlt B₀.lambda)
        (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda) B₀.lambda ≤
      base ^ (-a / (n - B₀.rank : ℕ)) := by
  apply rankTailSelectedRatio_le_rpow hRpos hRlt B₀.lambda B₀.lambda_pos
    hbase
  · exact B₀.low_le_one ⟨B₀.rank - 1, by omega⟩ (by simp; omega)
  · exact hlast

/-- Because the rank-tail split is at or after `rank`, the complementary
subspace recovered from its omitted exterior coordinate contains the whole
scale-one approximation span. -/
theorem adaptedRankTailApproximationSpan_le_recoveredComplement
    {n : ℕ}
    (L : AdelicMinima.LocalForms n) {Q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) ρ) :
    Erdos407.RankDrop.realSApproximationSpan L Q c ≤
      basisComplementSubspace E.vector
        (tailExteriorIndex
          (rankTailSelectedSplit hRpos hRlt B₀.lambda)) := by
  let B := OrderedMinimaData.ofAdaptedBasisCertificate B₀
  let κ := rankTailSelectedSplit hRpos hRlt B₀.lambda
  have hrank : B₀.rank ≤ κ.val :=
    rankTailSelectedSplit_ge hRpos hRlt B₀.lambda
  have hfun :
      (fun i : Fin B₀.rank ↦ B.point (Fin.castLE B₀.rank_le i)) =
        B₀.point ∘ Fin.castLE B₀.rank_le := by
    rfl
  rw [← B₀.prefix_span, ← hfun, E.vector_eq,
    ← transformPrefixSpan_eq E.change B.point B₀.rank_le
      E.change_lower B.independent]
  exact initialSpan_le_basisComplementSubspace
    (EvertseBasis.transformBasis E.change B.point) κ hrank

/-- For every omitted basis wedge, evaluation in the distinguished tail
row saves the precise adjacent-minimum ratio.  The local forms have already
been reindexed by Evertse's place-dependent permutation. -/
theorem realPlaceNorm_tailExteriorLocalForm_apply_omitted_le
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ : Fin n → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hμ : ∀ i, 0 < μ i) (hmono : Monotone μ)
    (hentry : ∀ i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A * min (μ i) (μ j))
    (J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val) place
          (exteriorIndexEquivFin n (n - κ.val) (tailExteriorIndex κ))
          (finExteriorBasisWedge v J)) ≤
      (Nat.factorial (n - κ.val) : ℝ) *
        distinguishedRatio κ hκ μ *
          ∏ a : Fin (n - κ.val),
            A * μ (Set.powersetCard.ofFinEmbEquiv.symm
              (tailExteriorIndex κ) a) := by
  apply realPlaceNorm_exteriorLocalForms_apply_le_with_saving
    (permutedLocalForms L π) (permutedLocalForms_nonsingular hL π)
    place (tailExteriorIndex κ) J v μ A (μ κ)
      (μ (splitPredecessor κ hκ)) hA (hμ κ)
      (hμ (splitPredecessor κ hκ)).le
  · intro a
    rw [exteriorIndexOfSet_enum]
    exact tail_scale_le κ μ hmono a
  · rw [exteriorIndexOfSet_enum]
    exact exists_omitted_column_scale_le κ hκ μ hmono J hJ
  · intro i j
    rw [exteriorIndexOfSet_enum]
    exact hentry _ _

/-- The ordinary row-product estimate for any exterior row. -/
theorem realPlaceNorm_exteriorLocalForm_apply_omitted_le
    {n : ℕ} (κ : Fin n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ : Fin n → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hμ : ∀ i, 0 < μ i)
    (hentry : ∀ i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A * min (μ i) (μ j))
    (I J : Set.powersetCard (Fin n) (n - κ.val)) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val) place
          (exteriorIndexEquivFin n (n - κ.val) I)
          (finExteriorBasisWedge v J)) ≤
      (Nat.factorial (n - κ.val) : ℝ) *
        ∏ a : Fin (n - κ.val),
          A * μ (Set.powersetCard.ofFinEmbEquiv.symm I a) := by
  rw [finExteriorBasisWedge_eq_finWedgeCoordinates]
  apply realPlaceNorm_exteriorLocalForms_apply_le
    (permutedLocalForms L π) (permutedLocalForms_nonsingular hL π)
    place I (fun b ↦ v (Set.powersetCard.ofFinEmbEquiv.symm J b))
    (fun a ↦ A * μ (Set.powersetCard.ofFinEmbEquiv.symm I a))
  · intro a
    exact mul_nonneg hA (hμ _).le
  · intro a b
    rw [exteriorIndexOfSet_enum]
    exact (hentry _ _).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hA)

/-- The row radius used for an omitted wedge.  Exactly one exterior row,
the distinguished tail, carries the adjacent-minimum saving. -/
noncomputable def omittedWedgeRowRadius {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) (μ : Fin n → ℝ) (A : ℝ)
    (I : Set.powersetCard (Fin n) (n - κ.val)) : ℝ :=
  (Nat.factorial (n - κ.val) : ℝ) *
    (if I = tailExteriorIndex κ then distinguishedRatio κ hκ μ else 1) *
      ∏ a : Fin (n - κ.val),
        A * μ (Set.powersetCard.ofFinEmbEquiv.symm I a)

/-- Uniform local bound, combining the saved tail row with all ordinary
rows. -/
theorem realPlaceNorm_exteriorLocalForm_apply_omitted_le_rowRadius
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ : Fin n → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hμ : ∀ i, 0 < μ i) (hmono : Monotone μ)
    (hentry : ∀ i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A * min (μ i) (μ j))
    (I J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val) place
          (exteriorIndexEquivFin n (n - κ.val) I)
          (finExteriorBasisWedge v J)) ≤
      omittedWedgeRowRadius κ hκ μ A I := by
  by_cases hI : I = tailExteriorIndex κ
  · subst I
    simpa [omittedWedgeRowRadius] using
      realPlaceNorm_tailExteriorLocalForm_apply_omitted_le
        κ hκ L hL place π v μ A hA hμ hmono hentry J hJ
  · simpa [omittedWedgeRowRadius, hI] using
      realPlaceNorm_exteriorLocalForm_apply_omitted_le
        κ L hL place π v μ A hA hμ hentry I J

/-! ### The row-weighted form used by the successive-minima certificate -/

/-- Evertse's estimate with a row weight `ρ_i`.  A low selected column still
saves `upper/lower`, because the row weight is common to the base and saved
entry in every Leibniz term. -/
theorem realPlaceNorm_exteriorLocalForms_apply_le_with_weighted_saving
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (I J : Set.powersetCard (Fin n) q)
    (v : Fin n → Fin n → ℚ) (μ ρ : Fin n → ℝ)
    (A lower upper : ℝ) (hA : 0 ≤ A) (hρ : ∀ i, 0 ≤ ρ i)
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hrows : ∀ a : Fin q, lower ≤
      μ ((exteriorIndexOfSet I).enum a))
    (hlowColumn : ∃ b : Fin q,
      μ ((exteriorIndexOfSet J).enum b) ≤ upper)
    (hentry : ∀ a b : Fin q,
      HeightBoxes.realPlaceNorm place
          (L place ((exteriorIndexOfSet I).enum a)
            (v ((exteriorIndexOfSet J).enum b))) ≤
        A * ρ ((exteriorIndexOfSet I).enum a) *
          min (μ ((exteriorIndexOfSet I).enum a))
            (μ ((exteriorIndexOfSet J).enum b))) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms L hL q place (exteriorIndexEquivFin n q I)
          (finExteriorBasisWedge v J)) ≤
      (Nat.factorial q : ℝ) * (upper / lower) *
        ∏ a, A * ρ ((exteriorIndexOfSet I).enum a) *
          μ ((exteriorIndexOfSet I).enum a) := by
  rw [finExteriorBasisWedge_eq_finWedgeCoordinates,
    exteriorLocalForms_apply_wedgeCoordinates]
  let M : Matrix (Fin q) (Fin q) ℚ := fun a b ↦
    L place ((exteriorIndexOfSet I).enum a)
      (v ((exteriorIndexOfSet J).enum b))
  let r : Fin q → ℝ := fun a ↦
    A * ρ ((exteriorIndexOfSet I).enum a) *
      μ ((exteriorIndexOfSet I).enum a)
  have hmuRows : ∀ a, 0 ≤ μ ((exteriorIndexOfSet I).enum a) := by
    intro a
    exact hlower.le.trans (hrows a)
  have hr : ∀ a, 0 ≤ r a := fun a ↦
    mul_nonneg (mul_nonneg hA (hρ _)) (hmuRows a)
  have hratio : 0 ≤ upper / lower := div_nonneg hupper hlower.le
  apply real_placeNorm_det_le_rowProduct_with_saving place M r
    (upper / lower) hr hratio
  · intro a b
    exact (hentry a b).trans <| by
      dsimp only [r]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _)
        (mul_nonneg hA (hρ _))
  · intro σ
    obtain ⟨b, hb⟩ := hlowColumn
    let a : Fin q := σ.symm b
    refine ⟨a, ?_⟩
    have hcol : σ a = b := by simp [a]
    have hfirst : HeightBoxes.realPlaceNorm place (M a (σ a)) ≤
        A * ρ ((exteriorIndexOfSet I).enum a) * upper := by
      calc
        HeightBoxes.realPlaceNorm place (M a (σ a)) ≤
            A * ρ ((exteriorIndexOfSet I).enum a) *
              min (μ ((exteriorIndexOfSet I).enum a))
                (μ ((exteriorIndexOfSet J).enum (σ a))) := hentry a (σ a)
        _ ≤ A * ρ ((exteriorIndexOfSet I).enum a) *
              μ ((exteriorIndexOfSet J).enum (σ a)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _)
            (mul_nonneg hA (hρ _))
        _ ≤ A * ρ ((exteriorIndexOfSet I).enum a) * upper := by
          rw [hcol]
          exact mul_le_mul_of_nonneg_left hb (mul_nonneg hA (hρ _))
    have hratioRow : upper ≤
        (upper / lower) * μ ((exteriorIndexOfSet I).enum a) := by
      have hmul := mul_le_mul_of_nonneg_left (hrows a) hratio
      calc
        upper = (upper / lower) * lower := by field_simp
        _ ≤ (upper / lower) * μ ((exteriorIndexOfSet I).enum a) := hmul
    calc
      HeightBoxes.realPlaceNorm place (M a (σ a)) ≤
          A * ρ ((exteriorIndexOfSet I).enum a) * upper := hfirst
      _ ≤ A * ρ ((exteriorIndexOfSet I).enum a) *
          ((upper / lower) * μ ((exteriorIndexOfSet I).enum a)) :=
        mul_le_mul_of_nonneg_left hratioRow (mul_nonneg hA (hρ _))
      _ = (upper / lower) * r a := by simp only [r]; ring

/-- Weighted specialization of the saved tail-coordinate estimate. -/
theorem realPlaceNorm_tailExteriorLocalForm_apply_omitted_le_weighted
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ ρ : Fin n → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hρ : ∀ i, 0 ≤ ρ i)
    (hμ : ∀ i, 0 < μ i) (hmono : Monotone μ)
    (hentry : ∀ i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A * ρ i * min (μ i) (μ j))
    (J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val) place
          (exteriorIndexEquivFin n (n - κ.val) (tailExteriorIndex κ))
          (finExteriorBasisWedge v J)) ≤
      (Nat.factorial (n - κ.val) : ℝ) *
        distinguishedRatio κ hκ μ *
          ∏ a : Fin (n - κ.val),
            A * ρ (Set.powersetCard.ofFinEmbEquiv.symm
              (tailExteriorIndex κ) a) *
              μ (Set.powersetCard.ofFinEmbEquiv.symm
                (tailExteriorIndex κ) a) := by
  apply realPlaceNorm_exteriorLocalForms_apply_le_with_weighted_saving
    (permutedLocalForms L π) (permutedLocalForms_nonsingular hL π)
    place (tailExteriorIndex κ) J v μ ρ A (μ κ)
      (μ (splitPredecessor κ hκ)) hA hρ (hμ κ)
      (hμ (splitPredecessor κ hκ)).le
  · intro a
    rw [exteriorIndexOfSet_enum]
    exact tail_scale_le κ μ hmono a
  · rw [exteriorIndexOfSet_enum]
    exact exists_omitted_column_scale_le κ hκ μ hmono J hJ
  · intro a b
    rw [exteriorIndexOfSet_enum]
    exact hentry _ _

/-- Weighted ordinary row-product estimate. -/
theorem realPlaceNorm_exteriorLocalForm_apply_omitted_le_weighted
    {n : ℕ} (κ : Fin n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ ρ : Fin n → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hρ : ∀ i, 0 ≤ ρ i) (hμ : ∀ i, 0 < μ i)
    (hentry : ∀ i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A * ρ i * min (μ i) (μ j))
    (I J : Set.powersetCard (Fin n) (n - κ.val)) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val) place
          (exteriorIndexEquivFin n (n - κ.val) I)
          (finExteriorBasisWedge v J)) ≤
      (Nat.factorial (n - κ.val) : ℝ) *
        ∏ a : Fin (n - κ.val),
          A * ρ (Set.powersetCard.ofFinEmbEquiv.symm I a) *
            μ (Set.powersetCard.ofFinEmbEquiv.symm I a) := by
  rw [finExteriorBasisWedge_eq_finWedgeCoordinates]
  apply realPlaceNorm_exteriorLocalForms_apply_le
    (permutedLocalForms L π) (permutedLocalForms_nonsingular hL π)
    place I (fun b ↦ v (Set.powersetCard.ofFinEmbEquiv.symm J b))
    (fun a ↦ A * ρ (Set.powersetCard.ofFinEmbEquiv.symm I a) *
      μ (Set.powersetCard.ofFinEmbEquiv.symm I a))
  · intro a
    exact mul_nonneg (mul_nonneg hA (hρ _)) (hμ _).le
  · intro a b
    rw [exteriorIndexOfSet_enum]
    exact (hentry _ _).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _)
        (mul_nonneg hA (hρ _)))

/-- Explicit row radius in the weighted application. -/
noncomputable def weightedOmittedWedgeRowRadius {n : ℕ} (κ : Fin n)
    (hκ : 0 < κ.val) (μ ρ : Fin n → ℝ) (A : ℝ)
    (I : Set.powersetCard (Fin n) (n - κ.val)) : ℝ :=
  (Nat.factorial (n - κ.val) : ℝ) *
    (if I = tailExteriorIndex κ then distinguishedRatio κ hκ μ else 1) *
      ∏ a : Fin (n - κ.val),
        A * ρ (Set.powersetCard.ofFinEmbEquiv.symm I a) *
          μ (Set.powersetCard.ofFinEmbEquiv.symm I a)

theorem realPlaceNorm_exteriorLocalForm_apply_omitted_le_weightedRowRadius
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ ρ : Fin n → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hρ : ∀ i, 0 ≤ ρ i)
    (hμ : ∀ i, 0 < μ i) (hmono : Monotone μ)
    (hentry : ∀ i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A * ρ i * min (μ i) (μ j))
    (I J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val) place
          (exteriorIndexEquivFin n (n - κ.val) I)
          (finExteriorBasisWedge v J)) ≤
      weightedOmittedWedgeRowRadius κ hκ μ ρ A I := by
  by_cases hI : I = tailExteriorIndex κ
  · subst I
    simpa [weightedOmittedWedgeRowRadius] using
      realPlaceNorm_tailExteriorLocalForm_apply_omitted_le_weighted
        κ hκ L hL place π v μ ρ A hA hρ hμ hmono hentry J hJ
  · simpa [weightedOmittedWedgeRowRadius, hI] using
      realPlaceNorm_exteriorLocalForm_apply_omitted_le_weighted
        κ L hL place π v μ ρ A hA hρ hμ hentry I J

/-! ## Packaging all omitted wedges into one exterior box -/

/-- If the chosen logarithmic box dominates the explicit determinant row
radii, every basis wedge other than the tail lies in that box. -/
theorem omittedWedge_mem_approximationBox
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (μ : Place23 → Fin n → ℝ)
    (A : Place23 → ℝ)
    (hA : ∀ place, 0 ≤ A place)
    (hμ : ∀ place i, 0 < μ place i)
    (hmono : ∀ place, Monotone (μ place))
    (hentry : ∀ place i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A place * min (μ place i) (μ place j))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose (n - κ.val)))
    (hradius : ∀ place I,
      omittedWedgeRowRadius κ hκ (μ place) (A place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n (n - κ.val) I))
    (J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    HeightBoxes.InApproximationBox
      (exteriorLocalForms (permutedLocalForms L π)
        (permutedLocalForms_nonsingular hL π) (n - κ.val))
      (Q : ℝ) c (finExteriorBasisWedge v J) := by
  intro place i
  let I := (exteriorIndexEquivFin n (n - κ.val)).symm i
  have hi : i = exteriorIndexEquivFin n (n - κ.val) I := by simp [I]
  rw [hi]
  exact (realPlaceNorm_exteriorLocalForm_apply_omitted_le_rowRadius
    κ hκ L hL place π v (μ place) (A place) (hA place)
      (hμ place) (hmono place) (hentry place) I J hJ).trans
    (hradius place I)

/-- Weighted box package matching the normalized Evertse-basis API: `ρ`
contains the original logarithmic row radii, while `μ` contains only the
ordered successive-minimum scales. -/
theorem omittedWedge_mem_approximationBox_weighted
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ)
    (μ ρ : Place23 → Fin n → ℝ) (A : Place23 → ℝ)
    (hA : ∀ place, 0 ≤ A place)
    (hρ : ∀ place i, 0 ≤ ρ place i)
    (hμ : ∀ place i, 0 < μ place i)
    (hmono : ∀ place, Monotone (μ place))
    (hentry : ∀ place i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A place * ρ place i * min (μ place i) (μ place j))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose (n - κ.val)))
    (hradius : ∀ place I,
      weightedOmittedWedgeRowRadius κ hκ (μ place) (ρ place) (A place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n (n - κ.val) I))
    (J : Set.powersetCard (Fin n) (n - κ.val))
    (hJ : J ≠ tailExteriorIndex κ) :
    HeightBoxes.InApproximationBox
      (exteriorLocalForms (permutedLocalForms L π)
        (permutedLocalForms_nonsingular hL π) (n - κ.val))
      (Q : ℝ) c (finExteriorBasisWedge v J) := by
  intro place i
  let I := (exteriorIndexEquivFin n (n - κ.val)).symm i
  have hi : i = exteriorIndexEquivFin n (n - κ.val) I := by simp [I]
  rw [hi]
  exact (realPlaceNorm_exteriorLocalForm_apply_omitted_le_weightedRowRadius
    κ hκ L hL place π v (μ place) (ρ place) (A place)
      (hA place) (hρ place) (hμ place) (hmono place)
      (hentry place) I J hJ).trans (hradius place I)

/-- The weighted omitted wedges are the required `D-1` S-integral domain
witnesses. -/
theorem omittedWedges_mem_realSIntegralApproximationDomain_weighted
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (μ ρ : Place23 → Fin n → ℝ) (A : Place23 → ℝ)
    (hA : ∀ place, 0 ≤ A place)
    (hρ : ∀ place i, 0 ≤ ρ place i)
    (hμ : ∀ place i, 0 < μ place i)
    (hmono : ∀ place, Monotone (μ place))
    (hentry : ∀ place i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A place * ρ place i * min (μ place i) (μ place j))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose (n - κ.val)))
    (hradius : ∀ place I,
      weightedOmittedWedgeRowRadius κ hκ (μ place) (ρ place) (A place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n (n - κ.val) I)) :
    ∀ J : OmittedExteriorIndex (tailExteriorIndex κ),
      finExteriorBasisWedge v J.1 ∈
        Erdos407.RankDrop.realSIntegralApproximationDomain
          (exteriorLocalForms (permutedLocalForms L π)
            (permutedLocalForms_nonsingular hL π) (n - κ.val)) Q c := by
  intro J
  exact finExteriorBasisWedge_mem_realSIntegralApproximationDomain
    (permutedLocalForms L π) (permutedLocalForms_nonsingular hL π)
    v hvS Q c J.1
      (omittedWedge_mem_approximationBox_weighted κ hκ L hL π v μ ρ A
        hA hρ hμ hmono hentry Q c hradius J.1 J.2)

theorem realSApproximationRank_ge_pred_of_omittedWedges_weighted
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (hv : LinearIndependent ℚ v)
    (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (μ ρ : Place23 → Fin n → ℝ) (A : Place23 → ℝ)
    (hA : ∀ place, 0 ≤ A place)
    (hρ : ∀ place i, 0 ≤ ρ place i)
    (hμ : ∀ place i, 0 < μ place i)
    (hmono : ∀ place, Monotone (μ place))
    (hentry : ∀ place i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A place * ρ place i * min (μ place i) (μ place j))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose (n - κ.val)))
    (hradius : ∀ place I,
      weightedOmittedWedgeRowRadius κ hκ (μ place) (ρ place) (A place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n (n - κ.val) I)) :
    n.choose (n - κ.val) - 1 ≤
      Erdos407.RankDrop.realSApproximationRank
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val)) Q c := by
  apply exteriorSpan_finrank_ge_pred hv (tailExteriorIndex κ)
    (Erdos407.RankDrop.realSApproximationSpan
      (exteriorLocalForms (permutedLocalForms L π)
        (permutedLocalForms_nonsingular hL π) (n - κ.val)) Q c)
  intro J
  apply Erdos407.RankDrop.mem_realSApproximationSpan
  exact omittedWedges_mem_realSIntegralApproximationDomain_weighted
    κ hκ L hL π v hvS μ ρ A hA hρ hμ hmono hentry Q c hradius J

/-- Certificate-consuming form of the weighted omitted-wedge construction.
The split is chosen internally by minimizing the adjacent ratios of the
ordered successive minima. -/
theorem orderedCertificate_omittedWedges_mem_realSIntegralDomain
    {n : ℕ} (hn : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (B : OrderedMinimaData n)
    (ρ : Place23 → Fin n → ℝ) (hρ : ∀ place i, 0 ≤ ρ place i)
    (E : WeightedEvertseData L B ρ)
    (Q : ℕ)
    (c : HeightBoxes.LocalConstants
      (n.choose (n - (certificateSplitIndex hn B).val)))
    (hradius : ∀ place I,
      weightedOmittedWedgeRowRadius (certificateSplitIndex hn B)
          (certificateSplitIndex_pos hn B)
          (certificatePlaceScale B place)
          (fun i ↦ ρ place (E.permutation place i)) (E.coefficient place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n
            (n - (certificateSplitIndex hn B).val) I)) :
    ∀ J : OmittedExteriorIndex
        (tailExteriorIndex (certificateSplitIndex hn B)),
      finExteriorBasisWedge E.vector J.1 ∈
        Erdos407.RankDrop.realSIntegralApproximationDomain
          (exteriorLocalForms (permutedLocalForms L E.permutation)
            (permutedLocalForms_nonsingular hL E.permutation)
            (n - (certificateSplitIndex hn B).val)) Q c := by
  exact omittedWedges_mem_realSIntegralApproximationDomain_weighted
    (certificateSplitIndex hn B) (certificateSplitIndex_pos hn B)
    L hL E.permutation E.vector E.sIntegral
    (certificatePlaceScale B)
    (fun place i ↦ ρ place (E.permutation place i))
    E.coefficient E.coefficient_nonneg (fun place i ↦ hρ place _)
    (certificatePlaceScale_pos B) (certificatePlaceScale_monotone B)
    E.pairwise Q c hradius

/-- Consequently the exterior approximation domain built from a concrete
ordered-minima certificate has rank at least `D-1`. -/
theorem orderedCertificate_realSApproximationRank_ge_pred
    {n : ℕ} (hn : 2 ≤ n)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (B : OrderedMinimaData n)
    (ρ : Place23 → Fin n → ℝ) (hρ : ∀ place i, 0 ≤ ρ place i)
    (E : WeightedEvertseData L B ρ)
    (Q : ℕ)
    (c : HeightBoxes.LocalConstants
      (n.choose (n - (certificateSplitIndex hn B).val)))
    (hradius : ∀ place I,
      weightedOmittedWedgeRowRadius (certificateSplitIndex hn B)
          (certificateSplitIndex_pos hn B)
          (certificatePlaceScale B place)
          (fun i ↦ ρ place (E.permutation place i)) (E.coefficient place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n
            (n - (certificateSplitIndex hn B).val) I)) :
    n.choose (n - (certificateSplitIndex hn B).val) - 1 ≤
      Erdos407.RankDrop.realSApproximationRank
        (exteriorLocalForms (permutedLocalForms L E.permutation)
          (permutedLocalForms_nonsingular hL E.permutation)
          (n - (certificateSplitIndex hn B).val)) Q c := by
  exact realSApproximationRank_ge_pred_of_omittedWedges_weighted
    (certificateSplitIndex hn B) (certificateSplitIndex_pos hn B)
    L hL E.permutation E.vector E.independent E.sIntegral
    (certificatePlaceScale B)
    (fun place i ↦ ρ place (E.permutation place i))
    E.coefficient E.coefficient_nonneg (fun place i ↦ hρ place _)
    (certificatePlaceScale_pos B) (certificatePlaceScale_monotone B)
    E.pairwise Q c hradius

/-- All `D-1` omitted wedges are actual `Z[1/6]` witnesses in the exterior
approximation domain consumed by `RankDrop`. -/
theorem omittedWedges_mem_realSIntegralApproximationDomain
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (μ : Place23 → Fin n → ℝ) (A : Place23 → ℝ)
    (hA : ∀ place, 0 ≤ A place)
    (hμ : ∀ place i, 0 < μ place i)
    (hmono : ∀ place, Monotone (μ place))
    (hentry : ∀ place i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A place * min (μ place i) (μ place j))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose (n - κ.val)))
    (hradius : ∀ place I,
      omittedWedgeRowRadius κ hκ (μ place) (A place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n (n - κ.val) I)) :
    ∀ J : OmittedExteriorIndex (tailExteriorIndex κ),
      finExteriorBasisWedge v J.1 ∈
        Erdos407.RankDrop.realSIntegralApproximationDomain
          (exteriorLocalForms (permutedLocalForms L π)
            (permutedLocalForms_nonsingular hL π) (n - κ.val)) Q c := by
  intro J
  exact finExteriorBasisWedge_mem_realSIntegralApproximationDomain
    (permutedLocalForms L π) (permutedLocalForms_nonsingular hL π)
    v hvS Q c J.1
      (omittedWedge_mem_approximationBox κ hκ L hL π v μ A
        hA hμ hmono hentry Q c hradius J.1 J.2)

/-- The omitted wedges give the lower `D-1` rank bound in precisely the
S-integral domain used by the rank-drop theorem. -/
theorem realSApproximationRank_ge_pred_of_omittedWedges
    {n : ℕ} (κ : Fin n) (hκ : 0 < κ.val)
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n))
    (v : Fin n → Fin n → ℚ) (hv : LinearIndependent ℚ v)
    (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (μ : Place23 → Fin n → ℝ) (A : Place23 → ℝ)
    (hA : ∀ place, 0 ≤ A place)
    (hμ : ∀ place i, 0 < μ place i)
    (hmono : ∀ place, Monotone (μ place))
    (hentry : ∀ place i j,
      HeightBoxes.realPlaceNorm place
          (permutedLocalForms L π place i (v j)) ≤
        A place * min (μ place i) (μ place j))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose (n - κ.val)))
    (hradius : ∀ place I,
      omittedWedgeRowRadius κ hκ (μ place) (A place) I ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n (n - κ.val) I)) :
    n.choose (n - κ.val) - 1 ≤
      Erdos407.RankDrop.realSApproximationRank
        (exteriorLocalForms (permutedLocalForms L π)
          (permutedLocalForms_nonsingular hL π) (n - κ.val)) Q c := by
  apply exteriorSpan_finrank_ge_pred hv (tailExteriorIndex κ)
    (Erdos407.RankDrop.realSApproximationSpan
      (exteriorLocalForms (permutedLocalForms L π)
        (permutedLocalForms_nonsingular hL π) (n - κ.val)) Q c)
  intro J
  apply Erdos407.RankDrop.mem_realSApproximationSpan
  exact omittedWedges_mem_realSIntegralApproximationDomain
    κ hκ L hL π v hvS μ A hA hμ hmono hentry Q c hradius J

/-! ## Exterior exponents and discretization -/

/-- The undiscretized exterior exponents after reindexing the original
forms by the Evertse permutations. -/
noncomputable def permutedExteriorLocalConstants {n q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    HeightBoxes.LocalConstants (n.choose q) :=
  fun place i ↦
    let J := (exteriorIndexEquivFin n q).symm i
    (∑ a : Fin q,
      c place (π place (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
      if J = J₀ place then saving place else 0

theorem permutedExteriorLocalConstants_eq {n q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) (place : Place23) (i : Fin (n.choose q)) :
    permutedExteriorLocalConstants c π J₀ saving place i =
      let J := (exteriorIndexEquivFin n q).symm i
      (∑ a : Fin q,
        c place (π place (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
      if J = J₀ place then saving place else 0 := by
  simp [permutedExteriorLocalConstants]

/-- Exact total exponent identity, including the single saved coordinate at
each of the three places. -/
theorem sum_permutedExteriorLocalConstants {n q : ℕ} (hq : 0 < q)
    (c : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    (∑ place, ∑ i, permutedExteriorLocalConstants c π J₀ saving place i) =
      (n - 1).choose (q - 1) * (∑ place, ∑ i, c place i) +
        ∑ place, saving place := by
  calc
    _ = ∑ place, ∑ J : Set.powersetCard (Fin n) q,
        ((∑ a : Fin q,
          c place (π place (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
          if J = J₀ place then saving place else 0) := by
      apply Finset.sum_congr rfl
      intro place _
      simpa [permutedExteriorLocalConstants] using
        (Equiv.sum_comp (exteriorIndexEquivFin n q).symm
          (fun J : Set.powersetCard (Fin n) q ↦
            ((∑ a : Fin q,
              c place (π place
                (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
              if J = J₀ place then saving place else 0)))
    _ = _ := sum_localExteriorCoordinateSums_with_saving hq c π J₀ saving

/-- Upward discretization preserves half of a supplied negative exterior
margin. -/
theorem sum_discretizedPermutedExteriorLocalConstants_lt_neg_half
    {n q : ℕ} (hq : 0 < q) (hd : 0 < n.choose q)
    (c : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) {γ δ : ℝ}
    (hγ : 0 < γ)
    (hmargin :
      (n - 1).choose (q - 1) * (∑ place, ∑ i, c place i) +
        ∑ place, saving place ≤ -δ)
    (hmesh : 3 * (n.choose q) * γ ≤ δ / 2) :
    (∑ place, ∑ i,
      discretizedLocalConstants γ
        (permutedExteriorLocalConstants c π J₀ saving) place i) <
      -(δ / 2) := by
  apply sum_discretizedLocalConstants_lt_neg_half hd
    (permutedExteriorLocalConstants c π J₀ saving) hγ
  · rw [sum_permutedExteriorLocalConstants hq]
    exact hmargin
  · exact hmesh

/-! ### Corrected weighted raw exponents -/

/-- Real logarithm to base `Q`, used only when `1 < Q` in applications. -/
noncomputable def logBase (Q x : ℝ) : ℝ :=
  Real.log x / Real.log Q

theorem rpow_logBase {Q x : ℝ} (hQ : 1 < Q) (hx : 0 < x) :
    Q ^ logBase Q x = x := by
  exact Real.rpow_logb (zero_lt_one.trans hQ) hQ.ne' hx

theorem rpow_sum_finset {Q : ℝ} (hQ : 0 < Q) {a : Type*}
    (s : Finset a) (f : a → ℝ) :
    Q ^ (∑ i ∈ s, f i) = ∏ i ∈ s, Q ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, Real.rpow_add hQ, ih]

theorem rpow_sum_fintype {Q : ℝ} (hQ : 0 < Q) {a : Type*} [Fintype a]
    (f : a → ℝ) : Q ^ (∑ i, f i) = ∏ i, Q ^ f i := by
  simpa using rpow_sum_finset hQ Finset.univ f

/-- Logarithmic exponent of the successive-minimum factor.  It vanishes at
the finite places because rational adelic dilation occurs only at infinity. -/
noncomputable def certificateMinimaLog {n : ℕ} (Q : ℝ)
    (B : OrderedMinimaData n) : HeightBoxes.LocalConstants n :=
  fun place i ↦
    if place = Place23.infinite then logBase Q (B.lambda i) else 0

/-- Logarithmic saving furnished by the selected adjacent ratio. -/
noncomputable def certificateGapSaving {n : ℕ} (hn : 2 ≤ n)
    (Q : ℝ) (B : OrderedMinimaData n) : Place23 → ℝ :=
  fun place ↦
    if place = Place23.infinite then
      logBase Q (ambientAdjacentRatio B.lambda (certificateGapIndex hn B))
    else 0

/-- Logarithmic saving for an arbitrary positive split.  This is the form
used by the recovery-compatible rank-tail selector. -/
noncomputable def splitGapSaving {n : ℕ} (Q : ℝ)
    (B : OrderedMinimaData n) (κ : Fin n) (hκ : 0 < κ.val) :
    Place23 → ℝ :=
  fun place ↦
    if place = Place23.infinite then
      logBase Q (distinguishedRatio κ hκ B.lambda)
    else 0

/-- Fixed logarithmic contribution of the determinant expansion and the
weighted Evertse coefficient: `log_Q(q! * A_v^q)`. -/
noncomputable def weightedDeterminantConstant {n q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {B : OrderedMinimaData n} {ρ : Place23 → Fin n → ℝ}
    (Q : ℝ) (E : WeightedEvertseData L B ρ) : Place23 → ℝ :=
  fun place ↦ logBase Q
    ((Nat.factorial q : ℝ) * (E.coefficient place) ^ q)

/-- The determinant/Evertse contribution expressed solely through the fixed
forms-dependent coefficient. -/
noncomputable def fixedWeightedDeterminantConstant {n q : ℕ}
    (Q : ℝ) (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) : Place23 → ℝ :=
  fun place ↦ logBase Q
    ((Nat.factorial q : ℝ) *
      (fixedWeightedEvertseCoefficient L hL place) ^ q)

theorem weightedDeterminantConstant_eq_fixed {n q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n} (hL : IsNonsingularFamily L)
    {B : OrderedMinimaData n} {ρ : Place23 → Fin n → ℝ}
    (Q : ℝ) (E : WeightedEvertseData L B ρ)
    (hcoeff : E.coefficient = fixedWeightedEvertseCoefficient L hL) :
    weightedDeterminantConstant (q := q) Q E =
      fixedWeightedDeterminantConstant (q := q) Q L hL := by
  ext place
  simp [weightedDeterminantConstant, fixedWeightedDeterminantConstant, hcoeff]

theorem rpow_certificateMinimaLog {n : ℕ} {Q : ℝ} (hQ : 1 < Q)
    (B : OrderedMinimaData n) (place : Place23) (i : Fin n) :
    Q ^ certificateMinimaLog Q B place i = certificatePlaceScale B place i := by
  by_cases hplace : place = Place23.infinite
  · subst place
    simpa [certificateMinimaLog, certificatePlaceScale] using
      rpow_logBase hQ (B.lambda_pos i)
  · simp [certificateMinimaLog, certificatePlaceScale, hplace]

theorem rpow_certificateGapSaving {n : ℕ} (hn : 2 ≤ n)
    {Q : ℝ} (hQ : 1 < Q) (B : OrderedMinimaData n) (place : Place23) :
    Q ^ certificateGapSaving hn Q B place =
      distinguishedRatio (certificateSplitIndex hn B)
        (certificateSplitIndex_pos hn B) (certificatePlaceScale B place) := by
  by_cases hplace : place = Place23.infinite
  · subst place
    rw [certificateGapSaving, if_pos rfl,
      distinguishedRatio_certificatePlaceScale_infinite]
    apply rpow_logBase hQ
    exact div_pos (B.lambda_pos _) (B.lambda_pos _)
  · rw [certificateGapSaving, if_neg hplace,
      distinguishedRatio_certificatePlaceScale_finite hn B place hplace]
    simp

theorem rpow_splitGapSaving {n : ℕ} {Q : ℝ} (hQ : 1 < Q)
    (B : OrderedMinimaData n) (κ : Fin n) (hκ : 0 < κ.val)
    (place : Place23) :
    Q ^ splitGapSaving Q B κ hκ place =
      distinguishedRatio κ hκ (certificatePlaceScale B place) := by
  by_cases hplace : place = Place23.infinite
  · subst place
    rw [splitGapSaving, if_pos rfl]
    change Q ^ logBase Q (distinguishedRatio κ hκ B.lambda) =
      distinguishedRatio κ hκ B.lambda
    apply rpow_logBase hQ
    exact div_pos (B.lambda_pos _) (B.lambda_pos _)
  · rw [splitGapSaving, if_neg hplace, distinguishedRatio]
    simp [certificatePlaceScale, hplace]

theorem rpow_weightedDeterminantConstant {n q : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    {B : OrderedMinimaData n} {ρ : Place23 → Fin n → ℝ}
    {Q : ℝ} (hQ : 1 < Q) (E : WeightedEvertseData L B ρ)
    (place : Place23) :
    Q ^ weightedDeterminantConstant (q := q) Q E place =
      (Nat.factorial q : ℝ) * (E.coefficient place) ^ q := by
  apply rpow_logBase hQ
  exact mul_pos (by positivity) (pow_pos (E.coefficient_pos place) q)

/-- The original row exponent plus the logarithmic successive-minimum
exponent, expressed in the Evertse-permuted row ordering. -/
noncomputable def weightedRowLocalConstants {n : ℕ}
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n)) : HeightBoxes.LocalConstants n :=
  fun place i ↦ c place (π place i) + ell place i

theorem sum_weightedRowLocalConstants {n : ℕ}
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n)) :
    (∑ place, ∑ i, weightedRowLocalConstants c ell π place i) =
      (∑ place, ∑ i, c place i) +
        ∑ place, ∑ i, ell place i := by
  simp only [weightedRowLocalConstants, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro place _
  simpa only [Function.comp_apply] using
    (Equiv.sum_comp (π place) (c place))

/-- The complete raw exterior exponent.  Besides the original row exponents
`c`, it includes every logarithmic minimum exponent `ell`, the saved tail
ratio once, and the fixed determinant/Evertse contribution once in every
exterior coordinate. -/
noncomputable def weightedRawExteriorLocalConstants {n q : ℕ}
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) :
    HeightBoxes.LocalConstants (n.choose q) :=
  fun place i ↦
    exteriorLocalConstants (weightedRowLocalConstants c ell π)
      J₀ saving place i + constant place

/-- Corrected weighted raw exponents for an arbitrary positive split. -/
noncomputable def splitWeightedRawExteriorLocalConstants
    {n : ℕ} (Q : ℝ) (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ)
    (κ : Fin n) (hκ : 0 < κ.val) :
    HeightBoxes.LocalConstants (n.choose (n - κ.val)) :=
  weightedRawExteriorLocalConstants c (certificateMinimaLog Q B)
    E.permutation (fun _ ↦ tailExteriorIndex κ)
    (splitGapSaving Q B κ hκ)
    (weightedDeterminantConstant (q := n - κ.val) Q E)

theorem weightedRawExteriorLocalConstants_eq {n q : ℕ}
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) (place : Place23)
    (i : Fin (n.choose q)) :
    weightedRawExteriorLocalConstants c ell π J₀ saving constant place i =
      let J := (exteriorIndexEquivFin n q).symm i
      (∑ a : Fin q,
        (c place (π place (Set.powersetCard.ofFinEmbEquiv.symm J a)) +
          ell place (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
        (if J = J₀ place then saving place else 0) + constant place := by
  simp [weightedRawExteriorLocalConstants, exteriorLocalConstants,
    weightedRowLocalConstants]

/-- Fully concrete raw exponent array attached to an ordered-minima
certificate and its weighted Evertse output. -/
noncomputable def certificateWeightedRawExteriorLocalConstants
    {n : ℕ} (hn : 2 ≤ n) (Q : ℝ) (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ) :
    HeightBoxes.LocalConstants
      (n.choose (n - (certificateSplitIndex hn B).val)) :=
  weightedRawExteriorLocalConstants c (certificateMinimaLog Q B)
    E.permutation (fun _ ↦ tailExteriorIndex (certificateSplitIndex hn B))
    (certificateGapSaving hn Q B)
    (weightedDeterminantConstant
      (q := n - (certificateSplitIndex hn B).val) Q E)

/-- Exact radius identity for any positive split.  It includes the original
row radii, every successive-minimum factor, the one tail saving, and the
fixed determinant/Evertse coefficient. -/
theorem weightedOmittedWedgeRowRadius_eq_splitExponentRadius
    {n : ℕ} {Q : ℝ} (hQ : 1 < Q)
    (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ)
    (hρ : ∀ place i,
      ρ place i = HeightBoxes.exponentRadius Q c place i)
    (κ : Fin n) (hκ : 0 < κ.val) (place : Place23)
    (I : Set.powersetCard (Fin n) (n - κ.val)) :
    weightedOmittedWedgeRowRadius κ hκ (certificatePlaceScale B place)
        (fun i ↦ ρ place (E.permutation place i)) (E.coefficient place) I =
      HeightBoxes.exponentRadius Q
        (splitWeightedRawExteriorLocalConstants Q c B E κ hκ) place
        (exteriorIndexEquivFin n (n - κ.val) I) := by
  let q := n - κ.val
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hrows :
      Q ^ (∑ a : Fin q,
        (c place (E.permutation place
            (Set.powersetCard.ofFinEmbEquiv.symm I a)) +
          certificateMinimaLog Q B place
            (Set.powersetCard.ofFinEmbEquiv.symm I a))) =
        ∏ a : Fin q,
          ρ place (E.permutation place
              (Set.powersetCard.ofFinEmbEquiv.symm I a)) *
            certificatePlaceScale B place
              (Set.powersetCard.ofFinEmbEquiv.symm I a) := by
    rw [rpow_sum_fintype hQpos]
    apply Finset.prod_congr rfl
    intro a _
    rw [Real.rpow_add hQpos,
      rpow_certificateMinimaLog hQ B place]
    rw [hρ]
    rfl
  have hsave :
      Q ^ (if I = tailExteriorIndex κ then
          splitGapSaving Q B κ hκ place else 0) =
        if I = tailExteriorIndex κ then
          distinguishedRatio κ hκ (certificatePlaceScale B place) else 1 := by
    by_cases hI : I = tailExteriorIndex κ
    · simp only [hI, if_pos]
      exact rpow_splitGapSaving hQ B κ hκ place
    · simp [hI]
  change (Nat.factorial q : ℝ) *
      (if I = tailExteriorIndex κ then
        distinguishedRatio κ hκ (certificatePlaceScale B place) else 1) *
        (∏ a : Fin q,
          E.coefficient place *
            ρ place (E.permutation place
              (Set.powersetCard.ofFinEmbEquiv.symm I a)) *
            certificatePlaceScale B place
              (Set.powersetCard.ofFinEmbEquiv.symm I a)) = _
  rw [HeightBoxes.exponentRadius]
  unfold splitWeightedRawExteriorLocalConstants
  rw [weightedRawExteriorLocalConstants_eq]
  simp only [weightedRowLocalConstants, Equiv.symm_apply_apply]
  rw [Real.rpow_add hQpos, Real.rpow_add hQpos, hrows, hsave,
    rpow_weightedDeterminantConstant hQ E place]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

theorem weightedOmittedWedgeRowRadius_le_discretizedSplitRadius
    {n : ℕ} {Q : ℝ} (hQ : 1 < Q) {γ : ℝ} (hγ : 0 < γ)
    (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n)
    (E : WeightedEvertseData L B
      (fun place i ↦ HeightBoxes.exponentRadius Q c place i))
    (κ : Fin n) (hκ : 0 < κ.val) (place : Place23)
    (I : Set.powersetCard (Fin n) (n - κ.val)) :
    weightedOmittedWedgeRowRadius κ hκ (certificatePlaceScale B place)
        (fun i ↦ HeightBoxes.exponentRadius Q c place
          (E.permutation place i)) (E.coefficient place) I ≤
      HeightBoxes.exponentRadius Q
        (discretizedLocalConstants γ
          (splitWeightedRawExteriorLocalConstants Q c B E κ hκ)) place
        (exteriorIndexEquivFin n (n - κ.val) I) := by
  rw [weightedOmittedWedgeRowRadius_eq_splitExponentRadius
    hQ c B E (fun _ _ ↦ rfl) κ hκ place I]
  apply Real.rpow_le_rpow_of_exponent_le hQ.le
  exact le_discretizedExponent hγ

/-- The corrected raw exponent is not merely a bookkeeping device: raising
`Q` to it gives exactly the explicit weighted determinant row radius. -/
theorem weightedOmittedWedgeRowRadius_eq_certificateExponentRadius
    {n : ℕ} (hn : 2 ≤ n) {Q : ℝ} (hQ : 1 < Q)
    (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ)
    (hρ : ∀ place i,
      ρ place i = HeightBoxes.exponentRadius Q c place i)
    (place : Place23)
    (I : Set.powersetCard (Fin n)
      (n - (certificateSplitIndex hn B).val)) :
    weightedOmittedWedgeRowRadius (certificateSplitIndex hn B)
        (certificateSplitIndex_pos hn B) (certificatePlaceScale B place)
        (fun i ↦ ρ place (E.permutation place i)) (E.coefficient place) I =
      HeightBoxes.exponentRadius Q
        (certificateWeightedRawExteriorLocalConstants hn Q c B E) place
        (exteriorIndexEquivFin n
          (n - (certificateSplitIndex hn B).val) I) := by
  let κ := certificateSplitIndex hn B
  let q := n - κ.val
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hrows :
      Q ^ (∑ a : Fin q,
        (c place (E.permutation place
            (Set.powersetCard.ofFinEmbEquiv.symm I a)) +
          certificateMinimaLog Q B place
            (Set.powersetCard.ofFinEmbEquiv.symm I a))) =
        ∏ a : Fin q,
          ρ place (E.permutation place
              (Set.powersetCard.ofFinEmbEquiv.symm I a)) *
            certificatePlaceScale B place
              (Set.powersetCard.ofFinEmbEquiv.symm I a) := by
    rw [rpow_sum_fintype hQpos]
    apply Finset.prod_congr rfl
    intro a _
    rw [Real.rpow_add hQpos,
      rpow_certificateMinimaLog hQ B place]
    rw [hρ]
    rfl
  have hsave :
      Q ^ (if I = tailExteriorIndex κ then
          certificateGapSaving hn Q B place else 0) =
        if I = tailExteriorIndex κ then
          distinguishedRatio κ (certificateSplitIndex_pos hn B)
            (certificatePlaceScale B place) else 1 := by
    by_cases hI : I = tailExteriorIndex κ
    · simp only [hI, if_pos]
      exact rpow_certificateGapSaving hn hQ B place
    · simp [hI]
  change (Nat.factorial q : ℝ) *
      (if I = tailExteriorIndex κ then
        distinguishedRatio κ (certificateSplitIndex_pos hn B)
          (certificatePlaceScale B place) else 1) *
        (∏ a : Fin q,
          E.coefficient place *
            ρ place (E.permutation place
              (Set.powersetCard.ofFinEmbEquiv.symm I a)) *
            certificatePlaceScale B place
              (Set.powersetCard.ofFinEmbEquiv.symm I a)) = _
  rw [HeightBoxes.exponentRadius]
  unfold certificateWeightedRawExteriorLocalConstants
  rw [weightedRawExteriorLocalConstants_eq]
  simp only [weightedRowLocalConstants, Equiv.symm_apply_apply]
  rw [Real.rpow_add hQpos, Real.rpow_add hQpos, hrows, hsave,
    rpow_weightedDeterminantConstant hQ E place]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-- Upward grid rounding automatically supplies the radius-domination
hypothesis required by the omitted-wedge box theorem. -/
theorem weightedOmittedWedgeRowRadius_le_discretizedCertificateRadius
    {n : ℕ} (hn : 2 ≤ n) {Q : ℝ} (hQ : 1 < Q) {γ : ℝ} (hγ : 0 < γ)
    (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n)
    (E : WeightedEvertseData L B
      (fun place i ↦ HeightBoxes.exponentRadius Q c place i))
    (place : Place23)
    (I : Set.powersetCard (Fin n)
      (n - (certificateSplitIndex hn B).val)) :
    weightedOmittedWedgeRowRadius (certificateSplitIndex hn B)
        (certificateSplitIndex_pos hn B) (certificatePlaceScale B place)
        (fun i ↦ HeightBoxes.exponentRadius Q c place
          (E.permutation place i)) (E.coefficient place) I ≤
      HeightBoxes.exponentRadius Q
        (discretizedLocalConstants γ
          (certificateWeightedRawExteriorLocalConstants hn Q c B E)) place
        (exteriorIndexEquivFin n
          (n - (certificateSplitIndex hn B).val) I) := by
  rw [weightedOmittedWedgeRowRadius_eq_certificateExponentRadius
    hn hQ c B E (fun _ _ ↦ rfl) place I]
  apply Real.rpow_le_rpow_of_exponent_le hQ.le
  exact le_discretizedExponent hγ

/-- Exact corrected exponent sum:

`choose(n-1,q-1) * (sum c + sum ell) + sum saving
  + choose(n,q) * sum constant`.
-/
theorem sum_weightedRawExteriorLocalConstants {n q : ℕ} (hq : 0 < q)
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) :
    (∑ place, ∑ i,
      weightedRawExteriorLocalConstants c ell π J₀ saving constant place i) =
      (n - 1).choose (q - 1) *
          ((∑ place, ∑ i, c place i) +
            ∑ place, ∑ i, ell place i) +
        ∑ place, saving place +
          n.choose q * ∑ place, constant place := by
  calc
    _ = (∑ place, ∑ i,
          exteriorLocalConstants (weightedRowLocalConstants c ell π)
            J₀ saving place i) +
        ∑ place, ∑ _i : Fin (n.choose q), constant place := by
      simp only [weightedRawExteriorLocalConstants, Finset.sum_add_distrib]
    _ = ((n - 1).choose (q - 1) *
          (∑ place, ∑ i, weightedRowLocalConstants c ell π place i) +
            ∑ place, saving place) +
        ∑ place, ∑ _i : Fin (n.choose q), constant place := by
      rw [sum_exteriorLocalConstants hq]
    _ = _ := by
      rw [sum_weightedRowLocalConstants]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]

/-- Exact total sum for the concrete certificate-selected split. -/
theorem sum_certificateWeightedRawExteriorLocalConstants
    {n : ℕ} (hn : 2 ≤ n) (Q : ℝ) (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ) :
    (∑ place, ∑ i,
      certificateWeightedRawExteriorLocalConstants hn Q c B E place i) =
      (n - 1).choose
          ((n - (certificateSplitIndex hn B).val) - 1) *
          ((∑ place, ∑ i, c place i) +
            ∑ place, ∑ i, certificateMinimaLog Q B place i) +
        ∑ place, certificateGapSaving hn Q B place +
          n.choose (n - (certificateSplitIndex hn B).val) *
            ∑ place, weightedDeterminantConstant
              (q := n - (certificateSplitIndex hn B).val) Q E place := by
  exact sum_weightedRawExteriorLocalConstants
    (by have := (certificateSplitIndex hn B).isLt; omega)
    c (certificateMinimaLog Q B) E.permutation
    (fun _ ↦ tailExteriorIndex (certificateSplitIndex hn B))
    (certificateGapSaving hn Q B)
    (weightedDeterminantConstant
      (q := n - (certificateSplitIndex hn B).val) Q E)

/-- Exact corrected total sum for any positive split, in particular the
recovery-compatible rank-tail split. -/
theorem sum_splitWeightedRawExteriorLocalConstants
    {n : ℕ} (Q : ℝ) (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ)
    (κ : Fin n) (hκ : 0 < κ.val) :
    (∑ place, ∑ i,
      splitWeightedRawExteriorLocalConstants Q c B E κ hκ place i) =
      (n - 1).choose ((n - κ.val) - 1) *
          ((∑ place, ∑ i, c place i) +
            ∑ place, ∑ i, certificateMinimaLog Q B place i) +
        ∑ place, splitGapSaving Q B κ hκ place +
          n.choose (n - κ.val) *
            ∑ place, weightedDeterminantConstant
              (q := n - κ.val) Q E place := by
  exact sum_weightedRawExteriorLocalConstants
    (by have := κ.isLt; omega)
    c (certificateMinimaLog Q B) E.permutation
    (fun _ ↦ tailExteriorIndex κ) (splitGapSaving Q B κ hκ)
    (weightedDeterminantConstant (q := n - κ.val) Q E)

/-- The total minimum exponent is the logarithm of the product of the
Archimedean successive minima. -/
theorem sum_certificateMinimaLog_eq_logBase_prod {n : ℕ}
    (Q : ℝ) (B : OrderedMinimaData n) :
    (∑ place, ∑ i, certificateMinimaLog Q B place i) =
      logBase Q (∏ i, B.lambda i) := by
  simp only [certificateMinimaLog]
  simp [Fin.sum_univ_succ, Place23.infinite]
  unfold logBase
  rw [Real.log_prod (fun i _ ↦ (B.lambda_pos i).ne')]
  rw [Finset.sum_div]

/-- Logarithmic form of an upper product certificate. -/
theorem sum_certificateMinimaLog_le_of_product
    {n : ℕ} {Q upper total : ℝ}
    (hQ : 1 < Q) (hupper : 0 < upper) (B : OrderedMinimaData n)
    (hprod : (∏ i, B.lambda i) ≤ upper * Q ^ (-total)) :
    (∑ place, ∑ i, certificateMinimaLog Q B place i) ≤
      logBase Q upper - total := by
  rw [sum_certificateMinimaLog_eq_logBase_prod]
  rw [← (Real.strictMono_rpow_of_base_gt_one hQ).le_iff_le]
  rw [rpow_logBase hQ (Finset.prod_pos (fun i _ ↦ B.lambda_pos i))]
  rw [Real.rpow_sub (zero_lt_one.trans hQ),
    rpow_logBase hQ hupper, div_eq_mul_inv,
    ← Real.rpow_neg (zero_lt_one.trans hQ).le]
  exact hprod

theorem sum_splitGapSaving_eq_logBase {n : ℕ}
    (Q : ℝ) (B : OrderedMinimaData n) (κ : Fin n) (hκ : 0 < κ.val) :
    (∑ place, splitGapSaving Q B κ hκ place) =
      logBase Q (distinguishedRatio κ hκ B.lambda) := by
  simp [splitGapSaving, Fin.sum_univ_succ, Place23.infinite]

/-- Convert a multiplicative selected-gap estimate into the exact saving
term used by the raw exterior exponent sum. -/
theorem sum_splitGapSaving_le {n : ℕ}
    {Q : ℝ} (hQ : 1 < Q) (B : OrderedMinimaData n)
    (κ : Fin n) (hκ : 0 < κ.val) (saving : ℝ)
    (hratio : distinguishedRatio κ hκ B.lambda ≤ Q ^ saving) :
    (∑ place, splitGapSaving Q B κ hκ place) ≤ saving := by
  rw [sum_splitGapSaving_eq_logBase]
  rw [← (Real.strictMono_rpow_of_base_gt_one hQ).le_iff_le]
  calc
    Q ^ logBase Q (distinguishedRatio κ hκ B.lambda) =
        distinguishedRatio κ hκ B.lambda :=
      rpow_logBase hQ (div_pos (B.lambda_pos _) (B.lambda_pos _))
    _ ≤ Q ^ saving := hratio

/-- Insert an upper product bound for the logarithmic successive minima into
the exact exterior sum.  This is the algebraic cancellation point in §5.3. -/
theorem sum_weightedRawExteriorLocalConstants_le_of_minimaProduct
    {n q : ℕ} (hq : 0 < q)
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) (ellUpper : ℝ)
    (hell : (∑ place, ∑ i, ell place i) ≤ ellUpper) :
    (∑ place, ∑ i,
      weightedRawExteriorLocalConstants c ell π J₀ saving constant place i) ≤
      (n - 1).choose (q - 1) *
          ((∑ place, ∑ i, c place i) + ellUpper) +
        ∑ place, saving place + n.choose q * ∑ place, constant place := by
  rw [sum_weightedRawExteriorLocalConstants hq]
  gcongr

/-- Certificate-local cancellation wrapper.  An upper bound on the actual
minimum product cancels the complete original exponent sum, while a separate
selected-ratio bound supplies the one negative tail saving. -/
theorem sum_splitWeightedRawExteriorLocalConstants_le_of_product_and_gap
    {n : ℕ} {Q upper : ℝ} (hQ : 1 < Q) (hupper : 0 < upper)
    (c : HeightBoxes.LocalConstants n)
    {L : Place23 → Fin n → RatLinearForm n}
    (B : OrderedMinimaData n) {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L B ρ)
    (κ : Fin n) (hκ : 0 < κ.val) (saving : ℝ)
    (hprod : (∏ i, B.lambda i) ≤
      upper * Q ^ (-(∑ place, ∑ i, c place i)))
    (hgap : distinguishedRatio κ hκ B.lambda ≤ Q ^ saving) :
    (∑ place, ∑ i,
      splitWeightedRawExteriorLocalConstants Q c B E κ hκ place i) ≤
      (n - 1).choose ((n - κ.val) - 1) * logBase Q upper + saving +
        n.choose (n - κ.val) *
          ∑ place, weightedDeterminantConstant
            (q := n - κ.val) Q E place := by
  have hell :
      (∑ place, ∑ i, certificateMinimaLog Q B place i) ≤
        logBase Q upper - ∑ place, ∑ i, c place i :=
    sum_certificateMinimaLog_le_of_product hQ hupper B hprod
  have hsaving :
      (∑ place, splitGapSaving Q B κ hκ place) ≤ saving :=
    sum_splitGapSaving_le hQ B κ hκ saving hgap
  calc
    (∑ place, ∑ i,
        splitWeightedRawExteriorLocalConstants Q c B E κ hκ place i) ≤
        (n - 1).choose ((n - κ.val) - 1) *
            ((∑ place, ∑ i, c place i) +
              (logBase Q upper - ∑ place, ∑ i, c place i)) +
          ∑ place, splitGapSaving Q B κ hκ place +
            n.choose (n - κ.val) *
              ∑ place, weightedDeterminantConstant
                (q := n - κ.val) Q E place := by
      exact sum_weightedRawExteriorLocalConstants_le_of_minimaProduct
        (by have := κ.isLt; omega) c (certificateMinimaLog Q B)
        E.permutation (fun _ ↦ tailExteriorIndex κ)
        (splitGapSaving Q B κ hκ)
        (weightedDeterminantConstant (q := n - κ.val) Q E)
        (logBase Q upper - ∑ place, ∑ i, c place i) hell
    _ ≤ (n - 1).choose ((n - κ.val) - 1) *
          ((∑ place, ∑ i, c place i) +
            (logBase Q upper - ∑ place, ∑ i, c place i)) + saving +
          n.choose (n - κ.val) *
            ∑ place, weightedDeterminantConstant
              (q := n - κ.val) Q E place := by gcongr
    _ = _ := by ring

/-- Rank-tail specialization: the adapted scale-one boundary and a last
minimum lower bound furnish the gap estimate automatically. -/
theorem sum_adaptedRankTailRaw_le_of_product_and_last
    {n : ℕ} (L : AdelicMinima.LocalForms n) {Q : ℕ} (hQ : 2 ≤ Q)
    (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) ρ)
    {upper a : ℝ} (hupper : 0 < upper)
    (hprod : (∏ i, B₀.lambda i) ≤
      upper * (Q : ℝ) ^ (-(∑ place, ∑ i, c place i)))
    (hlast : (Q : ℝ) ^ a ≤ B₀.lambda ⟨n - 1, by omega⟩) :
    (∑ place, ∑ i,
      splitWeightedRawExteriorLocalConstants (Q : ℝ) c
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
        (rankTailSelectedSplit hRpos hRlt B₀.lambda)
        (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda) place i) ≤
      (n - 1).choose
          ((n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val) - 1) *
          logBase (Q : ℝ) upper +
        (-a / (n - B₀.rank : ℕ)) +
        n.choose (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val) *
          ∑ place, weightedDeterminantConstant
            (q := n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val)
            (Q : ℝ) E place := by
  apply sum_splitWeightedRawExteriorLocalConstants_le_of_product_and_gap
    (by exact_mod_cast hQ) hupper c
    (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
    (rankTailSelectedSplit hRpos hRlt B₀.lambda)
    (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda)
    (-a / (n - B₀.rank : ℕ)) hprod
  exact adaptedRankTailSelectedRatio_le_rpow L c B₀ hRpos hRlt
    (by exact_mod_cast hQ) hlast

/-- Direct specialization to the genuine upper successive-minima
certificate.  No product inequality is supplied by the caller: it is the
`product_le` field constructed from the finite lattice and Minkowski's second
theorem. -/
theorem sum_upperAdaptedRankTailRaw_le_of_last
    {n : ℕ} (L : AdelicMinima.LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 2 ≤ Q)
    (c : HeightBoxes.LocalConstants n)
    (A : AdelicMinimaUpper.UpperAdaptedBasisCertificate
      L Q c (AdelicMinimaUpper.upperConstant L))
    (hRpos : 0 < A.toAdaptedBasisCertificate.rank)
    (hRlt : A.toAdaptedBasisCertificate.rank < n)
    {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate
        A.toAdaptedBasisCertificate) ρ)
    {a : ℝ}
    (hlast : (Q : ℝ) ^ a ≤
      A.toAdaptedBasisCertificate.lambda ⟨n - 1, by omega⟩) :
    (∑ place, ∑ i,
      splitWeightedRawExteriorLocalConstants (Q : ℝ) c
        (OrderedMinimaData.ofAdaptedBasisCertificate
          A.toAdaptedBasisCertificate) E
        (rankTailSelectedSplit hRpos hRlt
          A.toAdaptedBasisCertificate.lambda)
        (rankTailSelectedSplit_pos hRpos hRlt
          A.toAdaptedBasisCertificate.lambda) place i) ≤
      (n - 1).choose
          ((n - (rankTailSelectedSplit hRpos hRlt
            A.toAdaptedBasisCertificate.lambda).val) - 1) *
          logBase (Q : ℝ) (AdelicMinimaUpper.upperConstant L) +
        (-a / (n - A.toAdaptedBasisCertificate.rank : ℕ)) +
        n.choose (n - (rankTailSelectedSplit hRpos hRlt
          A.toAdaptedBasisCertificate.lambda).val) *
          ∑ place, weightedDeterminantConstant
            (q := n - (rankTailSelectedSplit hRpos hRlt
              A.toAdaptedBasisCertificate.lambda).val) (Q : ℝ) E place := by
  apply sum_adaptedRankTailRaw_le_of_product_and_last L hQ c
    A.toAdaptedBasisCertificate hRpos hRlt E
    (AdelicMinimaUpper.upperConstant_pos L hL)
    (A.product_le_rpow_neg_sum (by omega)) hlast

/-- Fully combined rank-tail product bound, last-minimum gap, fixed-constant
budget, and upward-grid discretization. -/
theorem sum_discretizedAdaptedRankTailRaw_lt_neg_half
    {n : ℕ} (L : AdelicMinima.LocalForms n) {Q : ℕ} (hQ : 2 ≤ Q)
    (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) ρ)
    {upper a γ δ : ℝ} (hupper : 0 < upper) (hγ : 0 < γ)
    (hprod : (∏ i, B₀.lambda i) ≤
      upper * (Q : ℝ) ^ (-(∑ place, ∑ i, c place i)))
    (hlast : (Q : ℝ) ^ a ≤ B₀.lambda ⟨n - 1, by omega⟩)
    (hbudget :
      (n - 1).choose
          ((n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val) - 1) *
          logBase (Q : ℝ) upper +
        (-a / (n - B₀.rank : ℕ)) +
        n.choose (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val) *
          ∑ place, weightedDeterminantConstant
            (q := n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val)
            (Q : ℝ) E place ≤ -δ)
    (hmesh :
      3 * n.choose (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val) *
        γ ≤ δ / 2) :
    (∑ place, ∑ i,
      discretizedLocalConstants γ
        (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
          (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
          (rankTailSelectedSplit hRpos hRlt B₀.lambda)
          (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda)) place i) <
      -(δ / 2) := by
  let κ := rankTailSelectedSplit hRpos hRlt B₀.lambda
  apply sum_discretizedLocalConstants_lt_neg_half
    (Nat.choose_pos (Nat.sub_le n κ.val))
    (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E κ
      (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda)) hγ
  · exact (sum_adaptedRankTailRaw_le_of_product_and_last L hQ c B₀
      hRpos hRlt E hupper hprod hlast).trans hbudget
  · exact hmesh

/-- Discretized terminal bound consuming the genuine upper certificate
directly. -/
theorem sum_discretizedUpperAdaptedRankTailRaw_lt_neg_half
    {n : ℕ} (L : AdelicMinima.LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 2 ≤ Q)
    (c : HeightBoxes.LocalConstants n)
    (A : AdelicMinimaUpper.UpperAdaptedBasisCertificate
      L Q c (AdelicMinimaUpper.upperConstant L))
    (hRpos : 0 < A.toAdaptedBasisCertificate.rank)
    (hRlt : A.toAdaptedBasisCertificate.rank < n)
    {ρ : Place23 → Fin n → ℝ}
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate
        A.toAdaptedBasisCertificate) ρ)
    {a γ δ : ℝ} (hγ : 0 < γ)
    (hlast : (Q : ℝ) ^ a ≤
      A.toAdaptedBasisCertificate.lambda ⟨n - 1, by omega⟩)
    (hbudget :
      (n - 1).choose
          ((n - (rankTailSelectedSplit hRpos hRlt
            A.toAdaptedBasisCertificate.lambda).val) - 1) *
          logBase (Q : ℝ) (AdelicMinimaUpper.upperConstant L) +
        (-a / (n - A.toAdaptedBasisCertificate.rank : ℕ)) +
        n.choose (n - (rankTailSelectedSplit hRpos hRlt
          A.toAdaptedBasisCertificate.lambda).val) *
          ∑ place, weightedDeterminantConstant
            (q := n - (rankTailSelectedSplit hRpos hRlt
              A.toAdaptedBasisCertificate.lambda).val) (Q : ℝ) E place ≤ -δ)
    (hmesh :
      3 * n.choose (n - (rankTailSelectedSplit hRpos hRlt
        A.toAdaptedBasisCertificate.lambda).val) * γ ≤ δ / 2) :
    (∑ place, ∑ i,
      discretizedLocalConstants γ
        (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
          (OrderedMinimaData.ofAdaptedBasisCertificate
            A.toAdaptedBasisCertificate) E
          (rankTailSelectedSplit hRpos hRlt
            A.toAdaptedBasisCertificate.lambda)
          (rankTailSelectedSplit_pos hRpos hRlt
            A.toAdaptedBasisCertificate.lambda)) place i) <
      -(δ / 2) := by
  exact sum_discretizedAdaptedRankTailRaw_lt_neg_half L hQ c
    A.toAdaptedBasisCertificate hRpos hRlt E
    (AdelicMinimaUpper.upperConstant_pos L hL) hγ
    (A.product_le_rpow_neg_sum (by omega)) hlast hbudget hmesh

/-- A minima-product upper bound together with the selected-gap saving and
the fixed-constant budget yields the required negative raw margin. -/
theorem sum_weightedRawExteriorLocalConstants_le_neg_of_product_gap
    {n q : ℕ} (hq : 0 < q)
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) (ellUpper δ : ℝ)
    (hell : (∑ place, ∑ i, ell place i) ≤ ellUpper)
    (hgap :
      (n - 1).choose (q - 1) *
          ((∑ place, ∑ i, c place i) + ellUpper) +
        ∑ place, saving place + n.choose q * ∑ place, constant place ≤ -δ) :
    (∑ place, ∑ i,
      weightedRawExteriorLocalConstants c ell π J₀ saving constant place i) ≤
      -δ :=
  (sum_weightedRawExteriorLocalConstants_le_of_minimaProduct
    hq c ell π J₀ saving constant ellUpper hell).trans hgap

/-- Discretization retains half of a negative margin for the complete
weighted exponent, including the fixed constants. -/
theorem sum_discretizedWeightedRawExteriorLocalConstants_lt_neg_half
    {n q : ℕ} (hq : 0 < q) (hd : 0 < n.choose q)
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) {γ δ : ℝ}
    (hγ : 0 < γ)
    (hmargin :
      (n - 1).choose (q - 1) *
          ((∑ place, ∑ i, c place i) +
            ∑ place, ∑ i, ell place i) +
        ∑ place, saving place + n.choose q * ∑ place, constant place ≤ -δ)
    (hmesh : 3 * (n.choose q) * γ ≤ δ / 2) :
    (∑ place, ∑ i,
      discretizedLocalConstants γ
        (weightedRawExteriorLocalConstants c ell π J₀ saving constant) place i) <
      -(δ / 2) := by
  apply sum_discretizedLocalConstants_lt_neg_half hd
    (weightedRawExteriorLocalConstants c ell π J₀ saving constant) hγ
  · rw [sum_weightedRawExteriorLocalConstants hq]
    exact hmargin
  · exact hmesh

/-- Fully combined product-bound, gap-saving, and discretization estimate. -/
theorem sum_discretizedWeightedRawExteriorLocalConstants_lt_neg_half_of_product_gap
    {n q : ℕ} (hq : 0 < q) (hd : 0 < n.choose q)
    (c ell : HeightBoxes.LocalConstants n)
    (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving constant : Place23 → ℝ) (ellUpper : ℝ) {γ δ : ℝ}
    (hγ : 0 < γ)
    (hell : (∑ place, ∑ i, ell place i) ≤ ellUpper)
    (hgap :
      (n - 1).choose (q - 1) *
          ((∑ place, ∑ i, c place i) + ellUpper) +
        ∑ place, saving place + n.choose q * ∑ place, constant place ≤ -δ)
    (hmesh : 3 * (n.choose q) * γ ≤ δ / 2) :
    (∑ place, ∑ i,
      discretizedLocalConstants γ
        (weightedRawExteriorLocalConstants c ell π J₀ saving constant) place i) <
      -(δ / 2) := by
  apply sum_discretizedLocalConstants_lt_neg_half hd
    (weightedRawExteriorLocalConstants c ell π J₀ saving constant) hγ
  · exact sum_weightedRawExteriorLocalConstants_le_neg_of_product_gap
      hq c ell π J₀ saving constant ellUpper δ hell hgap
  · exact hmesh

/-! ## Fully constructed adapted-certificate endpoint -/

/-- The rank-tail omitted-wedge conclusion for a supplied weighted Evertse
output.  The existential constructors below differ only in whether they also
expose the uniform fixed-coefficient identity. -/
theorem adaptedRankTail_omittedWedges_mem_discretizedRaw_of_E
    {n : ℕ}
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {γ : ℝ} (hγ : 0 < γ)
    (E : WeightedEvertseData L
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
      (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i)) :
    ∀ J : OmittedExteriorIndex
        (tailExteriorIndex
          (rankTailSelectedSplit hRpos hRlt B₀.lambda)),
      finExteriorBasisWedge E.vector J.1 ∈
        Erdos407.RankDrop.realSIntegralApproximationDomain
          (exteriorLocalForms (permutedLocalForms L E.permutation)
            (permutedLocalForms_nonsingular hL E.permutation)
            (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val)) Q
          (discretizedLocalConstants γ
            (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
              (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
              (rankTailSelectedSplit hRpos hRlt B₀.lambda)
              (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda))) := by
  let B := OrderedMinimaData.ofAdaptedBasisCertificate B₀
  let κ := rankTailSelectedSplit hRpos hRlt B₀.lambda
  let hκ : 0 < κ.val := rankTailSelectedSplit_pos hRpos hRlt B₀.lambda
  apply omittedWedges_mem_realSIntegralApproximationDomain_weighted
    κ hκ L hL E.permutation E.vector E.sIntegral
    (certificatePlaceScale B)
    (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place
      (E.permutation place i))
    E.coefficient E.coefficient_nonneg
    (fun place i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c place _))
    (certificatePlaceScale_pos B) (certificatePlaceScale_monotone B)
    E.pairwise Q
    (discretizedLocalConstants γ
      (splitWeightedRawExteriorLocalConstants (Q : ℝ) c B E κ hκ))
  intro place I
  apply weightedOmittedWedgeRowRadius_le_discretizedSplitRadius
    (by exact_mod_cast hQ) hγ c B E κ hκ place I

/-- Uniform-coefficient version of the constructed rank-tail endpoint.  The
displayed equality makes the determinant constants independent of
`Q`, `c`, and the selected successive-minimum basis. -/
theorem exists_adaptedRankTail_fixedCoefficient_omittedWedges
    {n : ℕ}
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ E : WeightedEvertseData L
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
        (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
      E.coefficient = fixedWeightedEvertseCoefficient L hL ∧
      ∀ J : OmittedExteriorIndex
          (tailExteriorIndex
            (rankTailSelectedSplit hRpos hRlt B₀.lambda)),
        finExteriorBasisWedge E.vector J.1 ∈
          Erdos407.RankDrop.realSIntegralApproximationDomain
            (exteriorLocalForms (permutedLocalForms L E.permutation)
              (permutedLocalForms_nonsingular hL E.permutation)
              (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val)) Q
            (discretizedLocalConstants γ
              (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
                (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
                (rankTailSelectedSplit hRpos hRlt B₀.lambda)
                (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda))) := by
  have hQone : 1 ≤ Q := by omega
  obtain ⟨E, hcoeff⟩ :=
    exists_weightedEvertseData_fixedCoefficient_of_adaptedBasisCertificate
      L hL hQone c B₀
  exact ⟨E, hcoeff,
    adaptedRankTail_omittedWedges_mem_discretizedRaw_of_E
      L hL hQ c B₀ hRpos hRlt hγ E⟩

/-- Recovery-compatible endpoint.  Starting from a genuine adapted
certificate with `0 < rank < n`, construct the weighted Evertse basis,
select the minimum gap only in the rank tail, and put all `D-1` omitted
wedges in the rounded corrected box. -/
theorem exists_adaptedRankTail_omittedWedges_mem_discretizedRaw
    {n : ℕ}
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ E : WeightedEvertseData L
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
        (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
      ∀ J : OmittedExteriorIndex
          (tailExteriorIndex
            (rankTailSelectedSplit hRpos hRlt B₀.lambda)),
        finExteriorBasisWedge E.vector J.1 ∈
          Erdos407.RankDrop.realSIntegralApproximationDomain
            (exteriorLocalForms (permutedLocalForms L E.permutation)
              (permutedLocalForms_nonsingular hL E.permutation)
              (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val)) Q
            (discretizedLocalConstants γ
              (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
                (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
                (rankTailSelectedSplit hRpos hRlt B₀.lambda)
                (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda))) := by
  have hQone : 1 ≤ Q := by omega
  obtain ⟨E⟩ := nonempty_weightedEvertseData_of_adaptedBasisCertificate
    L hL hQone c B₀
  refine ⟨E, ?_⟩
  let B := OrderedMinimaData.ofAdaptedBasisCertificate B₀
  let κ := rankTailSelectedSplit hRpos hRlt B₀.lambda
  let hκ : 0 < κ.val := rankTailSelectedSplit_pos hRpos hRlt B₀.lambda
  apply omittedWedges_mem_realSIntegralApproximationDomain_weighted
    κ hκ L hL E.permutation E.vector E.sIntegral
    (certificatePlaceScale B)
    (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place
      (E.permutation place i))
    E.coefficient E.coefficient_nonneg
    (fun place i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c place _))
    (certificatePlaceScale_pos B) (certificatePlaceScale_monotone B)
    E.pairwise Q
    (discretizedLocalConstants γ
      (splitWeightedRawExteriorLocalConstants (Q : ℝ) c B E κ hκ))
  intro place I
  apply weightedOmittedWedgeRowRadius_le_discretizedSplitRadius
    (by exact_mod_cast hQ) hγ c B E κ hκ place I

/-- Rank form of the recovery-compatible `D-1` omitted-wedge witness
family. -/
theorem exists_adaptedRankTail_realSApproximationRank_ge_pred
    {n : ℕ}
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    (hRpos : 0 < B₀.rank) (hRlt : B₀.rank < n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ E : WeightedEvertseData L
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
        (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
      n.choose (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val) - 1 ≤
        Erdos407.RankDrop.realSApproximationRank
          (exteriorLocalForms (permutedLocalForms L E.permutation)
            (permutedLocalForms_nonsingular hL E.permutation)
            (n - (rankTailSelectedSplit hRpos hRlt B₀.lambda).val)) Q
          (discretizedLocalConstants γ
            (splitWeightedRawExteriorLocalConstants (Q : ℝ) c
              (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E
              (rankTailSelectedSplit hRpos hRlt B₀.lambda)
              (rankTailSelectedSplit_pos hRpos hRlt B₀.lambda))) := by
  have hQone : 1 ≤ Q := by omega
  obtain ⟨E⟩ := nonempty_weightedEvertseData_of_adaptedBasisCertificate
    L hL hQone c B₀
  refine ⟨E, ?_⟩
  let B := OrderedMinimaData.ofAdaptedBasisCertificate B₀
  let κ := rankTailSelectedSplit hRpos hRlt B₀.lambda
  let hκ : 0 < κ.val := rankTailSelectedSplit_pos hRpos hRlt B₀.lambda
  apply realSApproximationRank_ge_pred_of_omittedWedges_weighted
    κ hκ L hL E.permutation E.vector E.independent E.sIntegral
    (certificatePlaceScale B)
    (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place
      (E.permutation place i))
    E.coefficient E.coefficient_nonneg
    (fun place i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c place _))
    (certificatePlaceScale_pos B) (certificatePlaceScale_monotone B)
    E.pairwise Q
    (discretizedLocalConstants γ
      (splitWeightedRawExteriorLocalConstants (Q : ℝ) c B E κ hκ))
  intro place I
  apply weightedOmittedWedgeRowRadius_le_discretizedSplitRadius
    (by exact_mod_cast hQ) hγ c B E κ hκ place I

/-- Starting from the genuine adapted-basis certificate, construct the
weighted Evertse basis, select the minimum adjacent ratio, and place all
`D-1` omitted wedges in the correctly discretized exterior domain. -/
theorem exists_adaptedCertificate_omittedWedges_mem_discretizedRaw
    {n : ℕ} (hn : 2 ≤ n)
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ E : WeightedEvertseData L
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
        (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
      ∀ J : OmittedExteriorIndex
          (tailExteriorIndex (certificateSplitIndex hn
            (OrderedMinimaData.ofAdaptedBasisCertificate B₀))),
        finExteriorBasisWedge E.vector J.1 ∈
          Erdos407.RankDrop.realSIntegralApproximationDomain
            (exteriorLocalForms (permutedLocalForms L E.permutation)
              (permutedLocalForms_nonsingular hL E.permutation)
              (n - (certificateSplitIndex hn
                (OrderedMinimaData.ofAdaptedBasisCertificate B₀)).val)) Q
            (discretizedLocalConstants γ
              (certificateWeightedRawExteriorLocalConstants hn (Q : ℝ) c
                (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E)) := by
  have hQone : 1 ≤ Q := by omega
  obtain ⟨E⟩ := nonempty_weightedEvertseData_of_adaptedBasisCertificate
    L hL hQone c B₀
  refine ⟨E, ?_⟩
  apply orderedCertificate_omittedWedges_mem_realSIntegralDomain
    hn L hL (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
    (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i)
    (fun place i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c place i)) E Q
    (discretizedLocalConstants γ
      (certificateWeightedRawExteriorLocalConstants hn (Q : ℝ) c
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E))
  intro place I
  apply weightedOmittedWedgeRowRadius_le_discretizedCertificateRadius
    hn (by exact_mod_cast hQ) hγ c
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E place I

/-- Rank form of the preceding fully constructed witness family. -/
theorem exists_adaptedCertificate_realSApproximationRank_ge_pred
    {n : ℕ} (hn : 2 ≤ n)
    (L : AdelicMinima.LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 2 ≤ Q) (c : HeightBoxes.LocalConstants n)
    (B₀ : AdelicMinima.AdaptedBasisCertificate L Q c)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ E : WeightedEvertseData L
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
        (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i),
      n.choose (n - (certificateSplitIndex hn
          (OrderedMinimaData.ofAdaptedBasisCertificate B₀)).val) - 1 ≤
        Erdos407.RankDrop.realSApproximationRank
          (exteriorLocalForms (permutedLocalForms L E.permutation)
            (permutedLocalForms_nonsingular hL E.permutation)
            (n - (certificateSplitIndex hn
              (OrderedMinimaData.ofAdaptedBasisCertificate B₀)).val)) Q
          (discretizedLocalConstants γ
            (certificateWeightedRawExteriorLocalConstants hn (Q : ℝ) c
              (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E)) := by
  have hQone : 1 ≤ Q := by omega
  obtain ⟨E⟩ := nonempty_weightedEvertseData_of_adaptedBasisCertificate
    L hL hQone c B₀
  refine ⟨E, ?_⟩
  apply orderedCertificate_realSApproximationRank_ge_pred
    hn L hL (OrderedMinimaData.ofAdaptedBasisCertificate B₀)
    (fun place i ↦ HeightBoxes.exponentRadius (Q : ℝ) c place i)
    (fun place i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c place i)) E Q
    (discretizedLocalConstants γ
      (certificateWeightedRawExteriorLocalConstants hn (Q : ℝ) c
        (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E))
  intro place I
  apply weightedOmittedWedgeRowRadius_le_discretizedCertificateRadius
    hn (by exact_mod_cast hQ) hγ c
      (OrderedMinimaData.ofAdaptedBasisCertificate B₀) E place I

end ExteriorWedgeBounds

end Erdos407.PadicSubspace
