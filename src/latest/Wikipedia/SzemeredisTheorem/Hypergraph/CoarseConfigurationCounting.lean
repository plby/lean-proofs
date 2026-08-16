import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseOrderedRemoval
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedConfigurationCounting

/-!
# Positive counts for mixed-good coarse configurations

A closed configuration in this file selects atoms of the coarse complex.
The selected coarse upper atom is decomposed using conditional expectation
first on the fine lower boundary and then on the coarse lower boundary.
Thus the main density and defect are exactly those controlled by
`ClosedOrderedAtomConfiguration.IsMixedGood`, while the uniform term is
controlled by regularity of the fine lower boundary against the coarse upper
partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A diagonal pair used only for coarse boundary support -/

/-- Regard the coarse endpoint as both sides of a coarse/fine pair.  This
lets the generic boundary-support lemmas for configuration weights be reused
without introducing a second copy of their combinatorial proof. -/
def OrderedCoarseFineComplex.coarseDiagonal
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    OrderedCoarseFineComplex G k r where
  coarse := P.coarse
  fine := P.coarse
  refines := OrderedPartitionComplex.Refines.refl P.coarse

/-! ## Mixed coarse/fine conditional decomposition -/

/-- Coarse-boundary conditional density of the selected coarse upper atom. -/
noncomputable def mixedConfigurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

/-- Fine-boundary conditional density of the selected coarse upper atom. -/
noncomputable def mixedConfigurationFineDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.fine e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    y

/-- Fine-boundary density minus the coarse-boundary density selected by the
configuration witness. -/
noncomputable def mixedConfigurationDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationFineDensity P A e y -
    mixedConfigurationCoarseDensity P A e

/-- Residual of a coarse upper atom after conditioning on the fine lower
boundary. -/
noncomputable def mixedConfigurationUniform
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFaceWeight A e y -
    mixedConfigurationFineDensity P A e y

/-- Indicator of the canonical coarse boundary atom determined by the
coarse configuration witness. -/
noncomputable def mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    (orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness))
    y

theorem mixedConfigurationCoarseDensity_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    0 ≤ mixedConfigurationCoarseDensity P A e := by
  exact conditionalMean_nonneg _
    (partitionAtomIndicator_nonneg _ _) _

theorem mixedConfigurationCoarseDensity_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    mixedConfigurationCoarseDensity P A e ≤ 1 := by
  exact conditionalMean_le_one _
    (partitionAtomIndicator_le_one _ _) _

theorem mixedConfigurationBoundaryIndicator_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ mixedConfigurationBoundaryIndicator P A e y :=
  partitionAtomIndicator_nonneg _ _ _

theorem mixedConfigurationBoundaryIndicator_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    mixedConfigurationBoundaryIndicator P A e y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

/-- Exact three-term decomposition of a selected coarse atom. -/
theorem mixedConfigurationFaceWeight_decompose
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y =
      mixedConfigurationCoarseDensity P A e +
        mixedConfigurationDefect P A e y +
        mixedConfigurationUniform P A e y := by
  unfold mixedConfigurationDefect mixedConfigurationUniform
  ring

/-! ## Coarse boundary support and selected-face decomposition -/

/-- A nonzero immediate boundary weight lies in the coarse boundary atom
selected by the coarse configuration. -/
theorem coarse_boundary_mem_of_coarse_configuration_weight_ne_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  exact
    coarse_boundary_mem_of_boundary_weight_ne_zero
      P.coarseDiagonal A e hpos i x hweight

/-- The remainder of a downward-closed coarse configuration is supported on
the selected coarse boundary atom. -/
theorem mixedConfigurationBoundaryIndicator_mul_remainder
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (x : Fin k → G) :
    mixedConfigurationBoundaryIndicator P A e
          (orderedFaceTuple e.face x) *
        partialConfigurationWeight A (s.erase e) x =
      partialConfigurationWeight A (s.erase e) x := by
  simpa [mixedConfigurationBoundaryIndicator,
    configurationBoundaryIndicator,
    OrderedCoarseFineComplex.coarseDiagonal] using
    (configurationBoundaryIndicator_mul_remainder
      P.coarseDiagonal A s hclosed e he x)

/-- Exact decomposition of a partial coarse-configuration count at one
selected face. -/
theorem partialConfigurationCount_mixed_decompose
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r) (he : e ∈ s) :
    partialConfigurationCount A s =
      mixedConfigurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e) +
        configurationContribution A s e
          (mixedConfigurationDefect P A e) +
        configurationContribution A s e
          (mixedConfigurationUniform P A e) := by
  rw [partialConfigurationCount, partialConfigurationCount]
  have hpoint :
      partialConfigurationWeight A s =
        fun x =>
          mixedConfigurationCoarseDensity P A e *
              partialConfigurationWeight A (s.erase e) x +
            mixedConfigurationDefect P A e
                (orderedFaceTuple e.face x) *
              partialConfigurationWeight A (s.erase e) x +
            mixedConfigurationUniform P A e
                (orderedFaceTuple e.face x) *
              partialConfigurationWeight A (s.erase e) x := by
    funext x
    rw [partialConfigurationWeight_eq_face_mul_erase
      A s e he x,
      mixedConfigurationFaceWeight_decompose P A e]
    ring
  rw [hpoint, mean_add, mean_add, mean_smul]
  rfl

/-! ## Mixed coarse-upper regularity and the uniform contribution -/

/-- At every rank, the fine lower boundary is regular against the coarse
upper atom family. -/
def IsFullyMixedPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (τ : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ)
      (τ j)

/-- Mixed goodness specializes to a positive ordered face. -/
theorem ClosedOrderedAtomConfiguration.IsMixedGood.atPositiveFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (e : PositiveOrderedFace k r) :
    OrderedAtomIsGoodAtBoundary
      (positiveFaceLowerLayer P.fine e)
      (positiveFaceLowerLayer P.coarse e)
      e.face
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
      (orderedFaceTuple e.face A.witness)
      (α e.rank) (β e.rank) := by
  rcases e with ⟨⟨j, hj⟩, e⟩
  exact hgood j hj e

/-- Mixed all-rank preliminary regularity specializes to the selected coarse
upper atom at a positive face. -/
theorem mixedConfigurationFace_isFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (e : PositiveOrderedFace k r) :
    (⟨orderedBoundaryPartition
        (positiveFaceLowerLayer P.fine e) e.face⟩ :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G)).IsFaceCutRegular
      (partitionAtomIndicator
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face))
      (τ e.lowerRank) := by
  rw [positiveFaceLowerLayer]
  exact
    (hregular e.lowerRank).toBounded
      e.face
      (A.atom e.lowerRank.succ e.face)

/-- After freezing the outside coordinates, the mixed uniform contribution
is a fine-boundary cut correlation of the selected coarse upper atom. -/
theorem mixedConfigurationContribution_uniform_eq_mean_faceCutCorrelation
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (a : G) :
    configurationContribution A s e
        (mixedConfigurationUniform P A e) =
      mean fun z : OrderedFaceComplement e.face → G =>
        (⟨orderedBoundaryPartition
            (positiveFaceLowerLayer P.fine e) e.face⟩ :
          FaceRegularityState
            (Fin (e.lowerRank.1 + 1) → G)).faceCutCorrelation
          (partitionAtomIndicator
            (P.coarse.partition e.lowerRank.succ e.face)
            (A.atom e.lowerRank.succ e.face))
          (configurationRemainderCutTest
            A s e hmax a z) := by
  unfold configurationContribution
  rw [mean_splitOrderedFace e.face, mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext z
  unfold FaceRegularityState.faceCutCorrelation
  apply congrArg mean
  funext y
  rw [cutTestProduct_configurationRemainderCutTest
    A s e hmax a y z]
  simp only [orderedFaceTuple_splitOrderedFaceEquiv_symm]
  rfl

/-- Mixed coarse-upper regularity bounds the uniform term by its scheduled
rankwise tolerance. -/
theorem abs_mixedConfigurationContribution_uniform_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank) :
    |configurationContribution A s e
        (mixedConfigurationUniform P A e)| ≤
      τ e.lowerRank := by
  rw [
    mixedConfigurationContribution_uniform_eq_mean_faceCutCorrelation
      P A s e hmax (Classical.choice inferInstance)]
  let S :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G) :=
    ⟨orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face⟩
  let f :
      (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
    partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
  calc
    |mean fun z : OrderedFaceComplement e.face → G =>
        S.faceCutCorrelation f
          (configurationRemainderCutTest A s e hmax
            (Classical.choice inferInstance) z)| ≤
        mean fun z : OrderedFaceComplement e.face → G =>
          |S.faceCutCorrelation f
            (configurationRemainderCutTest A s e hmax
              (Classical.choice inferInstance) z)| :=
      Finset.abs_expect_le Finset.univ _
    _ ≤
        mean fun _z : OrderedFaceComplement e.face → G =>
          τ e.lowerRank := by
      apply mean_mono
      intro z
      exact
        mixedConfigurationFace_isFaceCutRegular
          P A τ hregular e
          (configurationRemainderCutTest A s e hmax
            (Classical.choice inferInstance) z)
          (configurationRemainderCutTest_bounded
            A s e hmax (Classical.choice inferInstance) z)
    _ = τ e.lowerRank := mean_const _

/-- Fine-upper regularity transfers to the mixed coarse-upper regularity
needed by counting, with one fine-upper complexity factor. -/
theorem isFullyMixedPreliminaryOrderedRegular_of_fine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (M : Fin r → ℕ)
    (hε : ∀ j, 0 ≤ ε j)
    (hcomplexity :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M j) :
    IsFullyMixedPreliminaryOrderedRegular P
      (fun j => (M j : ℝ) * ε j) := by
  intro j
  exact P.preliminaryRegular_coarseUpper
    ε hregular j (M j) (hε j) (hcomplexity j)

/-- Fine regularity gives the explicit one-complexity-factor uniform error. -/
theorem abs_mixedConfigurationContribution_uniform_le_of_fine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (M : Fin r → ℕ)
    (hε : ∀ j, 0 ≤ ε j)
    (hcomplexity :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M j)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank) :
    |configurationContribution A s e
        (mixedConfigurationUniform P A e)| ≤
      (M e.lowerRank : ℝ) * ε e.lowerRank := by
  exact
    abs_mixedConfigurationContribution_uniform_le
      P A (fun j => (M j : ℝ) * ε j)
      (isFullyMixedPreliminaryOrderedRegular_of_fine
        P ε hregular M hε hcomplexity)
      s e hmax

/-! ## Localized mixed defect contribution -/

/-- On the canonical coarse boundary atom, the mixed configuration defect
is the usual fine-minus-coarse boundary defect of the selected coarse upper
atom. -/
theorem mixedConfigurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    mixedConfigurationDefect P A e y *
        mixedConfigurationBoundaryIndicator P A e y =
      orderedAtomBoundaryDefect
          (positiveFaceLowerLayer P.fine e)
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face) y *
        mixedConfigurationBoundaryIndicator P A e y := by
  let Q :=
    orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face
  let b : Q.parts :=
    orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness)
  let f :
      (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
    partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
  by_cases hy : y ∈ b.1
  · have hcoarse :
        conditionalMean Q f y =
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) := by
      exact conditionalMean_eq_of_mem_part Q f hy
    rw [mixedConfigurationBoundaryIndicator,
      partitionAtomIndicator_of_mem _ _ hy,
      mul_one, mul_one]
    change
      conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f
            (orderedFaceTuple e.face A.witness) =
        conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.fine e) e.face)
            f y -
          conditionalMean Q f y
    rw [hcoarse]
  · rw [mixedConfigurationBoundaryIndicator,
      partitionAtomIndicator_of_not_mem _ _ hy,
      mul_zero, mul_zero]

/-- The squared localized mixed defect is the canonical localized atom
defect mass for the selected coarse upper atom. -/
theorem mean_sq_mixedConfigurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    mean (fun y =>
      (mixedConfigurationDefect P A e y *
        mixedConfigurationBoundaryIndicator P A e y) ^ 2) =
      orderedLocalizedAtomDefectSq
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face)
        (orderedBoundaryAtomAt
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (orderedFaceTuple e.face A.witness)) := by
  unfold orderedLocalizedAtomDefectSq
  apply congrArg mean
  funext y
  rw [mixedConfigurationDefect_mul_boundaryIndicator P A e y,
    mul_pow]
  rw [show
    mixedConfigurationBoundaryIndicator P A e y ^ 2 =
      mixedConfigurationBoundaryIndicator P A e y by
        exact partitionAtomIndicator_sq _ _ _]
  rfl

/-- Boundary support inserts the canonical coarse atom indicator into the
mixed defect contribution without changing it. -/
theorem mixedConfigurationContribution_defect_eq_localized
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s) :
    configurationContribution A s e
        (mixedConfigurationDefect P A e) =
      mean fun x : Fin k → G =>
        (mixedConfigurationDefect P A e
            (orderedFaceTuple e.face x) *
          mixedConfigurationBoundaryIndicator P A e
            (orderedFaceTuple e.face x)) *
        partialConfigurationWeight A (s.erase e) x := by
  unfold configurationContribution
  apply congrArg mean
  funext x
  rw [mul_assoc,
    mixedConfigurationBoundaryIndicator_mul_remainder
      P A s hclosed e he x]

/-- Mixed goodness bounds the square of the selected defect contribution by
the scheduled rank-dependent threshold. -/
theorem mixedConfigurationContribution_defect_sq_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hβ : 0 ≤ β e.rank) :
    configurationContribution A s e
        (mixedConfigurationDefect P A e) ^ 2 ≤
      β e.rank := by
  let u : (Fin k → G) → ℝ :=
    fun x =>
      mixedConfigurationDefect P A e
          (orderedFaceTuple e.face x) *
        mixedConfigurationBoundaryIndicator P A e
          (orderedFaceTuple e.face x)
  let v : (Fin k → G) → ℝ :=
    partialConfigurationWeight A (s.erase e)
  have hlocal :
      mean (fun x : Fin k → G => u x ^ 2) ≤
        β e.rank := by
    have hgoodLocal :=
      (hgood.atPositiveFace P A α β e).localized_defect
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face)
        (orderedFaceTuple e.face A.witness)
        (α e.rank) (β e.rank)
    have hmass :
        orderedBoundaryAtomMass
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (orderedBoundaryAtomAt
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedFaceTuple e.face A.witness)) ≤
          1 :=
      orderedBoundaryAtomMass_le_one _ _ _
    calc
      mean (fun x : Fin k → G => u x ^ 2) =
          mean (fun y =>
            (mixedConfigurationDefect P A e y *
              mixedConfigurationBoundaryIndicator P A e y) ^ 2) := by
        exact mean_comp_orderedFaceTuple e.face
          (fun y =>
            (mixedConfigurationDefect P A e y *
              mixedConfigurationBoundaryIndicator P A e y) ^ 2)
      _ =
          orderedLocalizedAtomDefectSq
            (positiveFaceLowerLayer P.fine e)
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (P.coarse.partition e.lowerRank.succ e.face)
            (A.atom e.lowerRank.succ e.face)
            (orderedBoundaryAtomAt
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedFaceTuple e.face A.witness)) :=
        mean_sq_mixedConfigurationDefect_mul_boundaryIndicator
          P A e
      _ ≤
          β e.rank *
            orderedBoundaryAtomMass
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedBoundaryAtomAt
                (positiveFaceLowerLayer P.coarse e)
                e.face
                (orderedFaceTuple e.face A.witness)) :=
        hgoodLocal
      _ ≤ β e.rank := by
        exact mul_le_of_le_one_right hβ hmass
  have hv0 :
      0 ≤ mean (fun x : Fin k → G => v x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  have hv1 :
      mean (fun x : Fin k → G => v x ^ 2) ≤ 1 :=
    mean_sq_partialConfigurationWeight_le_one
      A (s.erase e)
  calc
    configurationContribution A s e
        (mixedConfigurationDefect P A e) ^ 2 =
        mean (fun x : Fin k → G => u x * v x) ^ 2 := by
      rw [mixedConfigurationContribution_defect_eq_localized
        P A s hclosed e he]
    _ ≤
        mean (fun x : Fin k → G => u x ^ 2) *
          mean (fun x : Fin k → G => v x ^ 2) :=
      mean_mul_sq_le_product u v
    _ ≤
        β e.rank *
          mean (fun x : Fin k → G => v x ^ 2) :=
      mul_le_mul_of_nonneg_right hlocal hv0
    _ ≤ β e.rank :=
      mul_le_of_le_one_right hβ hv1

/-- If the mixed-goodness defect threshold is at most `δ²`, the absolute
defect contribution is at most `δ`. -/
theorem abs_mixedConfigurationContribution_defect_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hβ0 : 0 ≤ β e.rank)
    (hβδ : β e.rank ≤ δ ^ 2) :
    |configurationContribution A s e
        (mixedConfigurationDefect P A e)| ≤ δ := by
  have hsquare :
      |configurationContribution A s e
          (mixedConfigurationDefect P A e)| ^ 2 ≤
        δ ^ 2 := by
    rw [sq_abs]
    exact le_trans
      (mixedConfigurationContribution_defect_sq_le
        P A α β hgood s hclosed e he hβ0)
      hβδ
  exact
    (sq_le_sq₀
      (abs_nonneg
        (configurationContribution A s e
          (mixedConfigurationDefect P A e)))
      hδ).mp hsquare

/-! ## One-face recurrence -/

/-- At a maximum-rank face of a downward-closed family, the mixed coarse
configuration count obeys the multiplicative recurrence with one defect and
one coarse-upper uniform error. -/
theorem abs_partialConfigurationCount_sub_mixedDensity_mul_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (hβ0 : 0 ≤ β e.rank)
    (hβδ : β e.rank ≤ δ ^ 2) :
    |partialConfigurationCount A s -
        mixedConfigurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| ≤
      δ + τ e.lowerRank := by
  have hdefect :
      |configurationContribution A s e
        (mixedConfigurationDefect P A e)| ≤ δ :=
    abs_mixedConfigurationContribution_defect_le
      P A α β hgood hδ s hclosed e he hβ0 hβδ
  have huniform :
      |configurationContribution A s e
        (mixedConfigurationUniform P A e)| ≤
          τ e.lowerRank :=
    abs_mixedConfigurationContribution_uniform_le
      P A τ hregular s e hmax
  rw [partialConfigurationCount_mixed_decompose
    P A s e he]
  calc
    |mixedConfigurationCoarseDensity P A e *
            partialConfigurationCount A (s.erase e) +
          configurationContribution A s e
            (mixedConfigurationDefect P A e) +
          configurationContribution A s e
            (mixedConfigurationUniform P A e) -
        mixedConfigurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| =
        |configurationContribution A s e
            (mixedConfigurationDefect P A e) +
          configurationContribution A s e
            (mixedConfigurationUniform P A e)| := by
      congr 1
      ring
    _ ≤
        |configurationContribution A s e
            (mixedConfigurationDefect P A e)| +
          |configurationContribution A s e
            (mixedConfigurationUniform P A e)| :=
      abs_add_le _ _
    _ ≤ δ + τ e.lowerRank :=
      add_le_add hdefect huniform

/-- Fine regularity specializes the one-face recurrence with the explicit
fine-upper complexity loss. -/
theorem abs_partialConfigurationCount_sub_mixedDensity_mul_le_of_fine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (M : Fin r → ℕ)
    (hε : ∀ j, 0 ≤ ε j)
    (hcomplexity :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (hβ0 : 0 ≤ β e.rank)
    (hβδ : β e.rank ≤ δ ^ 2) :
    |partialConfigurationCount A s -
        mixedConfigurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| ≤
      δ + (M e.lowerRank : ℝ) * ε e.lowerRank := by
  exact
    abs_partialConfigurationCount_sub_mixedDensity_mul_le
      P A α β hgood
      (fun j => (M j : ℝ) * ε j)
      (isFullyMixedPreliminaryOrderedRegular_of_fine
        P ε hregular M hε hcomplexity)
      hδ s hclosed e he hmax hβ0 hβδ

/-! ## Rank-dependent totalized recurrence -/

/-- Extend a partial coarse-configuration count to arbitrary face families.
As in the fine-configuration argument, non-downward-closed families use the
exact product of their mixed coarse densities only as an induction device. -/
noncomputable def mixedExtendedConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (s : Finset (PositiveOrderedFace k r)) : ℝ := by
  classical
  exact
    if IsDownwardClosedPositiveFaces s then
      partialConfigurationCount A s
    else
      ∏ e ∈ s, mixedConfigurationCoarseDensity P A e

@[simp]
theorem mixedExtendedConfigurationCount_empty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    mixedExtendedConfigurationCount P A ∅ = 1 := by
  rw [mixedExtendedConfigurationCount,
    if_pos downwardClosed_empty,
    partialConfigurationCount_empty]

/-- On the full positive-face family, the totalized count is the genuine
coarse-configuration count. -/
theorem mixedExtendedConfigurationCount_univ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    mixedExtendedConfigurationCount P A Finset.univ =
      fullConfigurationCount A := by
  rw [mixedExtendedConfigurationCount,
    if_pos downwardClosed_univ]
  rfl

/-- Mixed goodness lower-bounds every selected coarse main density. -/
theorem mixedConfigurationCoarseDensity_lower
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (e : PositiveOrderedFace k r) :
    α e.rank ≤ mixedConfigurationCoarseDensity P A e :=
  (hgood.atPositiveFace P A α β e).1

/-- The totalized mixed count has one prescribed analytic error per selected
positive face.  Closed families remove a maximum-rank face; non-closed
families use an exact product step. -/
theorem mixedExtendedConfigurationCount_step_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (δ : ℕ → ℝ)
    (hτ : ∀ j, 0 ≤ τ j)
    (hδ : ∀ n, 0 ≤ δ n)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ (δ n) ^ 2)
    (s : Finset (PositiveOrderedFace k r))
    (hs : s.Nonempty) :
    ∃ e ∈ s,
      |mixedExtendedConfigurationCount P A s -
          mixedConfigurationCoarseDensity P A e *
            mixedExtendedConfigurationCount P A (s.erase e)| ≤
        δ e.rank + τ e.lowerRank := by
  classical
  by_cases hclosed : IsDownwardClosedPositiveFaces s
  · obtain ⟨e, he, hmax⟩ :=
      exists_maxRank_mem s hs
    have hclosedErase :
        IsDownwardClosedPositiveFaces (s.erase e) :=
      hclosed.erase_maxRank he hmax
    refine ⟨e, he, ?_⟩
    rw [mixedExtendedConfigurationCount,
      if_pos hclosed,
      mixedExtendedConfigurationCount,
      if_pos hclosedErase]
    exact
      abs_partialConfigurationCount_sub_mixedDensity_mul_le
        P A α β hgood τ hregular (hδ e.rank)
        s hclosed e he
        (fun f hf => hmax f (Finset.mem_of_mem_erase hf))
        (hβ0 e.rank) (hβδ e.rank)
  · unfold IsDownwardClosedPositiveFaces at hclosed
    push Not at hclosed
    obtain ⟨f, hf, hpos, i, hboundary⟩ := hclosed
    by_cases hrest : s.erase f = ∅
    · have hsEq : s = {f} := by
        rcases (Finset.erase_eq_empty_iff s f).mp hrest with
          hsEmpty | hsSingleton
        · exact (hs.ne_empty hsEmpty).elim
        · exact hsSingleton
      refine ⟨f, hf, ?_⟩
      have hcountS :
          mixedExtendedConfigurationCount P A s =
            mixedConfigurationCoarseDensity P A f := by
        rw [mixedExtendedConfigurationCount, if_neg]
        · simp [hsEq]
        · intro h
          exact hboundary (h f hf hpos i)
      have hcountErase :
          mixedExtendedConfigurationCount P A (s.erase f) = 1 := by
        rw [hrest, mixedExtendedConfigurationCount_empty]
      rw [hcountS, hcountErase, mul_one, sub_self, abs_zero]
      exact add_nonneg (hδ f.rank) (hτ f.lowerRank)
    · obtain ⟨e, heRest⟩ :
          (s.erase f).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hrest
      have heS : e ∈ s :=
        Finset.mem_of_mem_erase heRest
      have hef : e ≠ f :=
        (Finset.mem_erase.mp heRest).1
      have hfEraseE : f ∈ s.erase e :=
        Finset.mem_erase.mpr ⟨hef.symm, hf⟩
      have hclosedErase :
          ¬IsDownwardClosedPositiveFaces (s.erase e) := by
        intro h
        have hb := h f hfEraseE hpos i
        exact hboundary (Finset.mem_of_mem_erase hb)
      refine ⟨e, heS, ?_⟩
      have hcountS :
          mixedExtendedConfigurationCount P A s =
            ∏ g ∈ s,
              mixedConfigurationCoarseDensity P A g := by
        rw [mixedExtendedConfigurationCount, if_neg]
        intro h
        exact hboundary (h f hf hpos i)
      have hcountErase :
          mixedExtendedConfigurationCount P A (s.erase e) =
            ∏ g ∈ s.erase e,
              mixedConfigurationCoarseDensity P A g := by
        rw [mixedExtendedConfigurationCount,
          if_neg hclosedErase]
      rw [hcountS, hcountErase]
      have hprod :
          mixedConfigurationCoarseDensity P A e *
              (∏ g ∈ s.erase e,
                mixedConfigurationCoarseDensity P A g) =
            ∏ g ∈ s,
              mixedConfigurationCoarseDensity P A g :=
        Finset.mul_prod_erase s
          (mixedConfigurationCoarseDensity P A) heS
      rw [hprod, sub_self, abs_zero]
      exact add_nonneg (hδ e.rank) (hτ e.lowerRank)

/-! ## Rankwise full-count lower bounds -/

/-- A mixed-good coarse configuration has count at least the product of its
rankwise density floors minus the sum of its facewise defect and
coarse-upper uniform errors. -/
theorem mixedFullConfigurationCount_lower_bound_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (δ : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hτ : ∀ j, 0 ≤ τ j)
    (hδ : ∀ n, 0 ≤ δ n)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ (δ n) ^ 2) :
    (∏ e : PositiveOrderedFace k r, α e.rank) -
        (∑ e : PositiveOrderedFace k r,
          (δ e.rank + τ e.lowerRank)) ≤
      fullConfigurationCount A := by
  let count :
      Finset (PositiveOrderedFace k r) → ℝ :=
    mixedExtendedConfigurationCount P A
  let p : PositiveOrderedFace k r → ℝ :=
    mixedConfigurationCoarseDensity P A
  let error : PositiveOrderedFace k r → ℝ :=
    fun e => δ e.rank + τ e.lowerRank
  have hempty : count ∅ = 1 :=
    mixedExtendedConfigurationCount_empty P A
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    exact
      ⟨mixedConfigurationCoarseDensity_nonneg P A e,
        mixedConfigurationCoarseDensity_le_one P A e⟩
  have hpLower : ∀ e, α e.rank ≤ p e := by
    intro e
    exact mixedConfigurationCoarseDensity_lower
      P A α β hgood e
  have herror : ∀ e, 0 ≤ error e := by
    intro e
    exact add_nonneg (hδ e.rank) (hτ e.lowerRank)
  have hstep :
      ∀ s : Finset (PositiveOrderedFace k r), s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e := by
    intro s hs
    exact
      mixedExtendedConfigurationCount_step_rankwise
        P A α β hgood τ hregular δ hτ hδ hβ0 hβδ s hs
  have hbound :=
    finiteCount_prod_sub_sum_error_le
      count p error herror hempty hp hstep
      (Finset.univ :
        Finset (PositiveOrderedFace k r))
  have hproduct :
      (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        ∏ e : PositiveOrderedFace k r, p e := by
    apply Finset.prod_le_prod
    · intro e _he
      exact hα e.rank
    · intro e _he
      exact hpLower e
  have hcountUniv :
      count
          (Finset.univ :
            Finset (PositiveOrderedFace k r)) =
        fullConfigurationCount A :=
    mixedExtendedConfigurationCount_univ P A
  rw [hcountUniv] at hbound
  calc
    (∏ e : PositiveOrderedFace k r, α e.rank) -
          (∑ e : PositiveOrderedFace k r,
            (δ e.rank + τ e.lowerRank)) ≤
        (∏ e : PositiveOrderedFace k r, p e) -
          (∑ e : PositiveOrderedFace k r, error e) := by
      exact sub_le_sub hproduct (le_refl _)
    _ ≤ fullConfigurationCount A := by
      simpa [p, error] using hbound

/-- Rankwise strict domination of all analytic errors gives a positive
coarse-configuration count. -/
theorem mixedFullConfigurationCount_pos_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (δ : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hτ : ∀ j, 0 ≤ τ j)
    (hδ : ∀ n, 0 ≤ δ n)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ (δ n) ^ 2)
    (hsmall :
      (∑ e : PositiveOrderedFace k r,
          (δ e.rank + τ e.lowerRank)) <
        ∏ e : PositiveOrderedFace k r, α e.rank) :
    0 < fullConfigurationCount A := by
  have hlower :=
    mixedFullConfigurationCount_lower_bound_rankwise
      P A α β hgood τ hregular δ
      hα hτ hδ hβ0 hβδ
  linarith

/-! ## Fine-regular complexity corollaries -/

/-- Fine preliminary regularity yields the rankwise coarse-configuration
lower bound with exactly one fine-upper complexity factor in each uniform
error. -/
theorem mixedFullConfigurationCount_lower_bound_of_fine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (M : Fin r → ℕ)
    (hcomplexity :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M j)
    (δ : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hε : ∀ j, 0 ≤ ε j)
    (hδ : ∀ n, 0 ≤ δ n)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ (δ n) ^ 2) :
    (∏ e : PositiveOrderedFace k r, α e.rank) -
        (∑ e : PositiveOrderedFace k r,
          (δ e.rank +
            (M e.lowerRank : ℝ) * ε e.lowerRank)) ≤
      fullConfigurationCount A := by
  apply
    mixedFullConfigurationCount_lower_bound_rankwise
      P A α β hgood
      (fun j => (M j : ℝ) * ε j)
      (isFullyMixedPreliminaryOrderedRegular_of_fine
        P ε hregular M hε hcomplexity)
      δ hα
  · intro j
    exact mul_nonneg (Nat.cast_nonneg _) (hε j)
  · exact hδ
  · exact hβ0
  · exact hβδ

/-- Fine regularity plus the sharp rankwise strict inequality gives a
positive coarse-configuration count. -/
theorem mixedFullConfigurationCount_pos_of_fine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (ε : OrderedRegularityTolerance r)
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    (M : Fin r → ℕ)
    (hcomplexity :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (P.fine.partition j.succ e) ≤ M j)
    (δ : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hε : ∀ j, 0 ≤ ε j)
    (hδ : ∀ n, 0 ≤ δ n)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβδ : ∀ n, β n ≤ (δ n) ^ 2)
    (hsmall :
      (∑ e : PositiveOrderedFace k r,
          (δ e.rank +
            (M e.lowerRank : ℝ) * ε e.lowerRank)) <
        ∏ e : PositiveOrderedFace k r, α e.rank) :
    0 < fullConfigurationCount A := by
  have hlower :=
    mixedFullConfigurationCount_lower_bound_of_fine
      P A α β hgood ε hregular M hcomplexity δ
      hα hε hδ hβ0 hβδ
  linarith

end Wikipedia.SzemeredisTheorem
