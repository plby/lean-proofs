import ErdosProblems.Erdos1002.GaussPrefixAnnularTaggedMarkedMeasure
import ErdosProblems.Erdos1002.GaussPrefixAnnularShortMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite coefficient bridge for annular Gauss-prefix tuples

This file contains only exact finite identities.  It first removes
cross-label depth collisions from the literal labeled mixed Fourier
coefficient when the marked cells are pairwise disjoint.  It then
chronologically sorts the surviving deterministic depth-box surrogate and
identifies its labeled torus character with the tag-dependent character
used by the reindexed marked tuple measure.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι]

/-! ## Literal collision removal -/

/-- For pairwise disjoint marked cells, the literal labeled mixed Fourier
coefficient is exactly the sum over globally injective depth tuples.
Every omitted tuple vanishes pointwise, rather than merely contributing a
small asymptotic error. -/
theorem gaussPrefixMarkedMixedFourierCoefficient_eq_sum_globalInjective
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hdisjoint : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixMarkedMixedFourierCoefficient N B k h =
      ∑ F : GloballyInjectiveMixedDepthTuple N k,
        ∫ x, gaussPrefixMarkedMixedTupleCharacter
          N B k h F.1 x ∂uniform01Measure := by
  classical
  let term : GaussPrefixMixedDepthTuple N k → ℂ := fun F ↦
    ∫ x, gaussPrefixMarkedMixedTupleCharacter
      N B k h F x ∂uniform01Measure
  let p : GaussPrefixMixedDepthTuple N k → Prop :=
    IsGloballyInjectiveMixedDepthTuple N k
  have hbad :
      ∑ F ∈ (Finset.univ : Finset (GaussPrefixMixedDepthTuple N k)).filter
          (fun F ↦ ¬ p F), term F = 0 := by
    apply Finset.sum_eq_zero
    intro F hF
    have hnot : ¬ IsGloballyInjectiveMixedDepthTuple N k F := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, p] using! hF
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x ↦
      gaussPrefixMarkedMixedTupleCharacter_eq_zero_of_not_globalInjective
        N B hdisjoint k h F hnot x
  have hgood :
      ∑ F ∈ (Finset.univ : Finset (GaussPrefixMixedDepthTuple N k)).filter p,
          term F =
        ∑ F : GloballyInjectiveMixedDepthTuple N k, term F.1 := by
    change
      ∑ F ∈ (Finset.univ :
          Finset (GaussPrefixMixedDepthTuple N k)).filter p, term F =
        ∑ F : {F : GaussPrefixMixedDepthTuple N k // p F}, term F.1
    let : Fintype {F : GaussPrefixMixedDepthTuple N k // p F} :=
      Fintype.ofFinite _
    rw [Finset.sum_subtype
      (p := p)
      ((Finset.univ : Finset (GaussPrefixMixedDepthTuple N k)).filter p)
      (by intro F; simp)
      term]
  unfold gaussPrefixMarkedMixedFourierCoefficient
  change (∑ F : GaussPrefixMixedDepthTuple N k, term F) = _
  calc
    (∑ F : GaussPrefixMixedDepthTuple N k, term F) =
        ∑ F ∈ (Finset.univ :
            Finset (GaussPrefixMixedDepthTuple N k)).filter p, term F +
          ∑ F ∈ (Finset.univ :
            Finset (GaussPrefixMixedDepthTuple N k)).filter
              (fun F ↦ ¬ p F), term F := by
      simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using!
        (Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (GaussPrefixMixedDepthTuple N k))
          p term).symm
    _ = ∑ F : GloballyInjectiveMixedDepthTuple N k, term F.1 := by
      rw [hbad, add_zero, hgood]
    _ = ∑ F : GloballyInjectiveMixedDepthTuple N k,
        ∫ x, gaussPrefixMarkedMixedTupleCharacter
          N B k h F.1 x ∂uniform01Measure := by
      rfl

/-- The surviving literal terms admit an exact disjoint partition by
their canonical chronological occurrence order. -/
theorem gaussPrefixMarkedMixedFourierCoefficient_eq_sum_canonicalOrders
    [DecidableEq ι]
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hdisjoint : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixMarkedMixedFourierCoefficient N B k h =
      ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
        ∑ F ∈ canonicalMixedOrderClass N k e,
          ∫ x, gaussPrefixMarkedMixedTupleCharacter
            N B k h F.1 x ∂uniform01Measure := by
  classical
  let order :
      GloballyInjectiveMixedDepthTuple N k →
        (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :=
    canonicalMixedOccurrenceOrder N k
  let term : GloballyInjectiveMixedDepthTuple N k → ℂ := fun F ↦
    ∫ x, gaussPrefixMarkedMixedTupleCharacter
      N B k h F.1 x ∂uniform01Measure
  rw [gaussPrefixMarkedMixedFourierCoefficient_eq_sum_globalInjective
    N B hdisjoint k h]
  change (∑ F : GloballyInjectiveMixedDepthTuple N k, term F) = _
  rw [← Finset.sum_fiberwise
    (Finset.univ : Finset (GloballyInjectiveMixedDepthTuple N k))
    order term]
  apply Finset.sum_congr rfl
  intro e _he
  congr 1
  ext F
  simp only [canonicalMixedOrderClass, Finset.mem_filter,
    Finset.mem_univ, true_and, order]

/-- Annular grid cells satisfy the disjointness hypothesis of the exact
canonical-order expansion. -/
theorem gaussPrefixMarkedMixedFourierCoefficient_annularGrid_eq_orders
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixMarkedMixedFourierCoefficient
        N (annularGridCell ε A grid) k h =
      ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
        ∑ F ∈ canonicalMixedOrderClass N k e,
          ∫ x, gaussPrefixMarkedMixedTupleCharacter
            N (annularGridCell ε A grid) k h F.1 x
              ∂uniform01Measure := by
  exact
    gaussPrefixMarkedMixedFourierCoefficient_eq_sum_canonicalOrders
      N (annularGridCell ε A grid)
      (fun i i' hii' ↦
        pairwise_disjoint_annularGridCell hε hεA hgrid hii')
      k h

/-! ## Reindexing one globally injective tuple -/

/-- Flattening a labeled torus mode and a labeled depth tuple through any
occurrence order does not change their product character.  This is the
pointwise character identity underlying the tagged reindexing. -/
theorem gaussMovingMarkedTupleCharacter_fixedOrder_eq_labeled
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GloballyInjectiveMixedDepthTuple N k) (x : ℝ) :
    gaussMovingMarkedTupleCharacter N
        (flattenedAnnularFourierMode e h)
        (fixedOrderMixedTimes N k e F) x =
      ∏ z : GaussPrefixMixedOccurrence k,
        paperExp ((h z.1 z.2 : ℝ) *
          gaussSelectedPrefixTorusMark
            N (F.1 z.1 z.2 : ℕ) x) := by
  classical
  unfold gaussMovingMarkedTupleCharacter
    flattenedAnnularFourierMode fixedOrderMixedTimes
  exact Fintype.prod_equiv e _ _ (fun _j ↦ rfl)

/-- On a simultaneous literal tuple event, its labeled character is the
same torus character as the chronological tag representation. -/
theorem gaussPrefixMarkedMixedTupleCharacter_eq_fixedOrderCharacter_of_events
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    (B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ))
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    {x : ℝ}
    (hx : ∀ z : GaussPrefixMixedOccurrence k,
      x ∈ gaussPrefixMarkedEvent N (B z.1) (F.1 z.1 z.2)) :
    gaussPrefixMarkedMixedTupleCharacter N B k h F.1 x =
      gaussMovingMarkedTupleCharacter N
        (flattenedAnnularFourierMode e h)
        (fixedOrderMixedTimes N k e F) x := by
  classical
  rw [gaussMovingMarkedTupleCharacter_fixedOrder_eq_labeled]
  unfold gaussPrefixMarkedMixedTupleCharacter
  rw [← Fintype.prod_sigma']
  apply Finset.prod_congr rfl
  intro z _hz
  unfold gaussPrefixMarkedDepthCharacter
  rw [if_pos (hx z)]
  rfl

/-! ## An exact deterministic-depth surrogate -/

/-- The source tuples whose canonical order is `e` and whose depths obey
the deterministic annular time boxes and prescribed sign parity. -/
def annularCanonicalOrderSource
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (GloballyInjectiveMixedDepthTuple N k) := by
  classical
  exact (canonicalMixedOrderClass N k e).filter fun F ↦
    ∀ j,
      fixedOrderMixedTimes N k e F j ∈
          annularOccurrenceDepthBoxes N k (e j) ∧
        fixedOrderMixedTimes N k e F j % 2 =
          (annularOccurrenceParity k (e j)).1

/-- The preceding source is literally the `e`-fiber of the eligible
globally injective tuples. -/
theorem annularCanonicalOrderSource_eq_eligible_filter
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    annularCanonicalOrderSource N k e =
      (eligibleAnnularGloballyInjectiveMixedTuples N k).filter
        (fun F ↦ canonicalMixedOccurrenceOrder N k F = e) := by
  classical
  ext F
  simp only [annularCanonicalOrderSource,
    eligibleAnnularGloballyInjectiveMixedTuples,
    canonicalMixedOrderClass, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨horder, hbox⟩
    refine ⟨?_, horder⟩
    simpa only [horder] using! hbox
  · rintro ⟨hbox, horder⟩
    refine ⟨horder, ?_⟩
    simpa only [horder] using! hbox

/-- The signed-window Fourier integrand attached to one eligible labeled
tuple, expressed in its canonical chronological order.  This is an exact
deterministic-depth surrogate: no actual denominator-time cell is
silently identified with a depth box. -/
def gaussPrefixAnnularCanonicalDepthTupleIntegrand
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GloballyInjectiveMixedDepthTuple N k) (x : ℝ) : ℂ :=
  let e := canonicalMixedOccurrenceOrder N k F
  gaussMovingSignedMarkedTupleIntegrand
    N (Real.log (N : ℝ))
    (flattenedAnnularSignedLower ε A e)
    (flattenedAnnularSignedUpper ε A e)
    (flattenedAnnularFourierMode e h)
    (fixedOrderMixedTimes N k e F) x

/-- On the order fiber `e`, the canonical surrogate unfolds to the
tag-`e` moving signed marked integrand. -/
theorem gaussPrefixAnnularCanonicalDepthTupleIntegrand_eq_of_order
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (horder : canonicalMixedOccurrenceOrder N k F = e) (x : ℝ) :
    gaussPrefixAnnularCanonicalDepthTupleIntegrand ε A N k h F x =
      gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (flattenedAnnularFourierMode e h)
        (fixedOrderMixedTimes N k e F) x := by
  unfold gaussPrefixAnnularCanonicalDepthTupleIntegrand
  rw [horder]

/-- The complete labeled deterministic-depth surrogate coefficient. -/
def gaussPrefixAnnularCanonicalDepthFourierCoefficient
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) : ℂ :=
  ∑ F ∈ eligibleAnnularGloballyInjectiveMixedTuples N k,
    ∫ x, gaussPrefixAnnularCanonicalDepthTupleIntegrand
      ε A N k h F x ∂uniform01Measure

/-- For one order tag, summing the labeled surrogate over its source
fiber is exactly the moving marked Fourier sum over the corresponding
chronological tuple family.  Injectivity of `fixedOrderMixedTimes` ensures
that the image operation loses no multiplicity. -/
theorem sum_integral_annularCanonicalOrderSource_eq_markedFourierTupleSum
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    (∑ F ∈ annularCanonicalOrderSource N k e,
        ∫ x, gaussPrefixAnnularCanonicalDepthTupleIntegrand
          ε A N k h F x ∂uniform01Measure) =
      uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (flattenedAnnularFourierMode e h)
        (canonicalAnnularGridTupleFamily N k e) := by
  classical
  let source : Finset (GloballyInjectiveMixedDepthTuple N k) :=
    annularCanonicalOrderSource N k e
  let times :
      GloballyInjectiveMixedDepthTuple N k →
        Fin (MixedOccurrenceCount k) → ℕ :=
    fixedOrderMixedTimes N k e
  let summand : (Fin (MixedOccurrenceCount k) → ℕ) → ℂ :=
    fun t ↦
      ∫ x, gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (flattenedAnnularFourierMode e h) t x
        ∂uniform01Measure
  have hsource :
      source =
        (canonicalMixedOrderClass N k e).filter fun F ↦
          ∀ j,
            fixedOrderMixedTimes N k e F j ∈
                annularOccurrenceDepthBoxes N k (e j) ∧
              fixedOrderMixedTimes N k e F j % 2 =
                (annularOccurrenceParity k (e j)).1 := by
    rfl
  have hfamily :
      canonicalAnnularGridTupleFamily N k e = source.image times := by
    unfold canonicalAnnularGridTupleFamily
      canonicalMixedOrderParityBoxTimes
    rw [hsource]
  have htimes : Function.Injective times := by
    exact fixedOrderMixedTimes_injective N k e
  rw [hfamily]
  unfold uniformMovingSignedMarkedFourierTupleSum
    movingSignedMarkedFourierTupleSum
  change
    (∑ F ∈ source,
        ∫ x, gaussPrefixAnnularCanonicalDepthTupleIntegrand
          ε A N k h F x ∂uniform01Measure) =
      ∑ t ∈ source.image times, summand t
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro F hF
    have horder :
        canonicalMixedOccurrenceOrder N k F = e := by
      have hmem : F ∈ canonicalMixedOrderClass N k e := by
        have hmem' := hF
        rw [hsource] at hmem'
        exact (Finset.mem_filter.mp hmem').1
      exact mem_canonicalMixedOrderClass_iff.mp hmem
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦
      gaussPrefixAnnularCanonicalDepthTupleIntegrand_eq_of_order
        ε A N k h F e horder x
  · intro F _hF G _hG hFG
    exact htimes hFG

/-- Exact global bridge from the labeled deterministic-depth surrogate to
the sum of the tag-dependent chronological Fourier coefficients. -/
theorem gaussPrefixAnnularCanonicalDepthFourierCoefficient_eq_taggedSum
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixAnnularCanonicalDepthFourierCoefficient ε A N k h =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (flattenedAnnularFourierMode e h)
          (canonicalAnnularGridTupleFamily N k e) := by
  classical
  let eligible : Finset (GloballyInjectiveMixedDepthTuple N k) :=
    eligibleAnnularGloballyInjectiveMixedTuples N k
  let order :
      GloballyInjectiveMixedDepthTuple N k →
        (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :=
    canonicalMixedOccurrenceOrder N k
  let term : GloballyInjectiveMixedDepthTuple N k → ℂ := fun F ↦
    ∫ x, gaussPrefixAnnularCanonicalDepthTupleIntegrand
      ε A N k h F x ∂uniform01Measure
  unfold gaussPrefixAnnularCanonicalDepthFourierCoefficient
  change (∑ F ∈ eligible, term F) = _
  rw [← Finset.sum_fiberwise eligible order term]
  apply Finset.sum_congr rfl
  intro e _he
  have hsource :=
    annularCanonicalOrderSource_eq_eligible_filter N k e
  change
    (∑ F ∈ eligible with order F = e, term F) =
      uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (flattenedAnnularFourierMode e h)
        (canonicalAnnularGridTupleFamily N k e)
  rw [← hsource]
  exact
    sum_integral_annularCanonicalOrderSource_eq_markedFourierTupleSum
      ε A N k h e

/-- The same exact bridge in the reference-coordinate notation used by
the reindexed tagged finite measure. -/
theorem gaussPrefixAnnularCanonicalDepthFourierCoefficient_eq_reindexed
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixAnnularCanonicalDepthFourierCoefficient ε A N k h =
      reindexedAnnularUniformMarkedFourierTupleSum
        (ε := ε) (A := A) N k e₀
          (flattenedAnnularFourierMode e₀ h) := by
  rw [gaussPrefixAnnularCanonicalDepthFourierCoefficient_eq_taggedSum]
  unfold reindexedAnnularUniformMarkedFourierTupleSum
  apply Finset.sum_congr rfl
  intro e _he
  congr 2
  funext j
  have he :
      e₀ (e₀.symm (e j)) = e j :=
    e₀.apply_symm_apply (e j)
  simp only [flattenedAnnularFourierMode]
  rw [he]

/-- Equivalently, the labeled deterministic-depth coefficient is exactly
the reference-coordinate Fourier integral of the reindexed positive
finite measure. -/
theorem gaussPrefixAnnularCanonicalDepthFourierCoefficient_eq_integral_reindexed
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixAnnularCanonicalDepthFourierCoefficient ε A N k h =
      ∫ z, UnitAddTorus.mFourier
          (flattenedAnnularFourierMode e₀ h) z
        ∂(reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀ :
            Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))) := by
  rw [gaussPrefixAnnularCanonicalDepthFourierCoefficient_eq_reindexed]
  exact
    (integral_reindexedAnnularUniformMarkedTupleFiniteMeasure_mFourier
      (ε := ε) (A := A) N k e₀
        (flattenedAnnularFourierMode e₀ h)).symm

end

end Erdos1002
