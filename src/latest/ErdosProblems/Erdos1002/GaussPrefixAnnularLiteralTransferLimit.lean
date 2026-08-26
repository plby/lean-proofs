import ErdosProblems.Erdos1002.GaussPrefixAnnularLiteralEventBridge
import ErdosProblems.Erdos1002.GaussPrefixAnnularBadEventMoments
import ErdosProblems.Erdos1002.GaussPrefixAnnularSeparatedMarked
import ErdosProblems.Erdos1002.GaussPrefixAnnularInteriorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Completion of the literal-to-canonical annular transfer

This file proves the unconditional literal-transfer input used by the
annular factorial-moment assembly.  The comparison is made on a fixed
denominator good event, with contracted and expanded deterministic time
boxes.  Its two errors are then removed in the required order:

* for fixed positive boundary width, the denominator-bad contribution
  tends to zero by a genuine high-moment estimate;
* after that limit, the deterministic time-boundary mass tends to zero as
  the boundary width tends to zero.

All finite sums below retain the chronological-order tag and all labeled
occurrences.  In particular, no absolute value is moved outside a tuple
sum.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance gaussPrefixAnnularLiteralTransferLimitPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 4000000

/-! ## Restricted finite masses -/

/-- The exact chronological expansion of the literal mixed factorial
moment, restricted to a measurable carrier. -/
def aggregateLiteralAnnularRestrictedMass
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) (carrier : Set ℝ) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
    ∑ F ∈ canonicalMixedOrderClass N k e,
      uniform01Measure.real
        (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩ carrier)

/-- The canonical source-coordinate mass for a tag-dependent source
family, restricted to a carrier. -/
def aggregateCanonicalSourceRestrictedMass
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (source :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Finset (GloballyInjectiveMixedDepthTuple N k))
    (carrier : Set ℝ) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
    ∑ F ∈ source e,
      uniform01Measure.real
        (canonicalAnnularSignedTorusTupleEvent ε A N e
          (fixedOrderMixedTimes N k e F) ∩ carrier)

theorem aggregateLiteralAnnularRestrictedMass_univ
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (N : ℕ) (k : AnnularGridIndex grid → ℕ) :
    aggregateLiteralAnnularRestrictedMass ε A N k Set.univ =
      mixedFactorialMoment
        (gaussPrefixMarkedCountVectorLaw N
          (annularGridCell ε A grid)
          (fun i ↦ measurableSet_annularGridCell ε A grid i))
        k := by
  rw [mixedFactorialMoment_gaussPrefixAnnular_eq_orderedLiteralMass
    hε hεA hgrid N k]
  unfold aggregateLiteralAnnularRestrictedMass
  simp only [inter_univ]

theorem aggregateCanonicalSourceRestrictedMass_univ_contracted
    (ε A : ℝ) (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    aggregateCanonicalSourceRestrictedMass ε A N k
        (fun e ↦ contractedAnnularCanonicalOrderSource N eta k e) Set.univ =
      aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
        (fun e ↦ contractedCanonicalAnnularGridTupleFamily N eta k e) := by
  unfold aggregateCanonicalSourceRestrictedMass
    aggregateUniformAnnularSignedTorusTupleMassSum
  apply Finset.sum_congr rfl
  intro e _he
  rw [uniformAnnularSignedTorusTupleMassSum_contracted_eq_source]
  simp only [inter_univ]

theorem aggregateCanonicalSourceRestrictedMass_univ_expanded
    (ε A : ℝ) (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    aggregateCanonicalSourceRestrictedMass ε A N k
        (fun e ↦ expandedAnnularCanonicalOrderSource N eta k e) Set.univ =
      aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
        (fun e ↦ expandedCanonicalAnnularGridTupleFamily N eta k e) := by
  unfold aggregateCanonicalSourceRestrictedMass
    aggregateUniformAnnularSignedTorusTupleMassSum
  apply Finset.sum_congr rfl
  intro e _he
  rw [uniformAnnularSignedTorusTupleMassSum_expanded_eq_source]
  simp only [inter_univ]

/-! ## Elementary measure and integral tools -/

/-- Almost-everywhere inclusion gives monotonicity of real-valued finite
measure. -/
theorem measureReal_mono_ae_of_finite
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu] {s t : Set α}
    (h : s ≤ᶠ[ae mu] t) :
    mu.real s ≤ mu.real t := by
  rw [measureReal_def, measureReal_def,
    ENNReal.toReal_le_toReal (measure_ne_top mu s) (measure_ne_top mu t)]
  exact measure_mono_ae h

/-- A finite sum of event masses restricted to `bad` is bounded by a
restricted integral whenever the corresponding pointwise indicator sum
is bounded. -/
theorem sum_measureReal_inter_le_setIntegral
    {α ι : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu]
    (s : Finset ι) (E : ι → Set α) (bad : Set α) (f : α → ℝ)
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hf : Integrable f mu)
    (hpoint : ∀ x,
      (∑ i ∈ s, (E i).indicator (fun _ ↦ (1 : ℝ)) x) ≤ f x) :
    (∑ i ∈ s, mu.real (E i ∩ bad)) ≤ ∫ x in bad, f x ∂mu := by
  have hleft :
      Integrable
        (fun x ↦ ∑ i ∈ s, (E i).indicator (fun _ ↦ (1 : ℝ)) x)
        (mu.restrict bad) := by
    apply integrable_finset_sum
    intro i hi
    exact ((integrable_const (1 : ℝ)).indicator (hE i hi)).mono_measure
      Measure.restrict_le_self
  have hright : Integrable f (mu.restrict bad) :=
    hf.mono_measure Measure.restrict_le_self
  calc
    (∑ i ∈ s, mu.real (E i ∩ bad)) =
        ∫ x, (∑ i ∈ s,
          (E i).indicator (fun _ ↦ (1 : ℝ)) x) ∂(mu.restrict bad) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        symm
        calc
          (∫ x in bad,
              (E i).indicator (fun _ ↦ (1 : ℝ)) x ∂mu) =
              ∫ x, (E i).indicator (fun _ ↦ (1 : ℝ)) x
                ∂(mu.restrict bad) := rfl
          _ = (mu.restrict bad).real (E i) :=
            integral_indicator_one (hE i hi)
          _ = mu.real (E i ∩ bad) := by
            unfold Measure.real
            rw [Measure.restrict_apply (hE i hi)]
      · intro i hi
        exact ((integrable_const (1 : ℝ)).indicator
          (hE i hi)).mono_measure Measure.restrict_le_self
    _ ≤ ∫ x, f x ∂(mu.restrict bad) :=
      integral_mono hleft hright hpoint
    _ = ∫ x in bad, f x ∂mu := rfl

theorem measureReal_le_inter_add_inter_compl
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu] (E G : Set α) :
    mu.real E ≤ mu.real (E ∩ G) + mu.real (E ∩ Gᶜ) := by
  calc
    mu.real E =
        mu.real ((E ∩ G) ∪ (E ∩ Gᶜ)) := by
      rw [inter_union_compl]
    _ ≤ mu.real (E ∩ G) + mu.real (E ∩ Gᶜ) :=
      measureReal_union_le _ _

theorem aggregateLiteralRestrictedMass_le_univ
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) (carrier : Set ℝ) :
    aggregateLiteralAnnularRestrictedMass ε A N k carrier ≤
      aggregateLiteralAnnularRestrictedMass ε A N k Set.univ := by
  unfold aggregateLiteralAnnularRestrictedMass
  apply Finset.sum_le_sum
  intro e _he
  apply Finset.sum_le_sum
  intro F _hF
  apply measureReal_mono
    (h₂ := measure_ne_top uniform01Measure _)
  intro x hx
  exact ⟨hx.1, Set.mem_univ x⟩

theorem aggregateCanonicalSourceRestrictedMass_le_univ
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (source :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Finset (GloballyInjectiveMixedDepthTuple N k))
    (carrier : Set ℝ) :
    aggregateCanonicalSourceRestrictedMass ε A N k source carrier ≤
      aggregateCanonicalSourceRestrictedMass ε A N k source Set.univ := by
  unfold aggregateCanonicalSourceRestrictedMass
  apply Finset.sum_le_sum
  intro e _he
  apply Finset.sum_le_sum
  intro F _hF
  apply measureReal_mono
    (h₂ := measure_ne_top uniform01Measure _)
  intro x hx
  exact ⟨hx.1, Set.mem_univ x⟩

theorem aggregateLiteral_univ_le_good_add_bad
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) (good : Set ℝ) :
    aggregateLiteralAnnularRestrictedMass ε A N k Set.univ ≤
      aggregateLiteralAnnularRestrictedMass ε A N k good +
        aggregateLiteralAnnularRestrictedMass ε A N k goodᶜ := by
  unfold aggregateLiteralAnnularRestrictedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro F _hF
  simpa only [inter_univ] using!
    measureReal_le_inter_add_inter_compl uniform01Measure
      (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F) good

theorem aggregateCanonicalSource_univ_le_good_add_bad
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (source :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Finset (GloballyInjectiveMixedDepthTuple N k))
    (good : Set ℝ) :
    aggregateCanonicalSourceRestrictedMass ε A N k source Set.univ ≤
      aggregateCanonicalSourceRestrictedMass ε A N k source good +
        aggregateCanonicalSourceRestrictedMass ε A N k source goodᶜ := by
  unfold aggregateCanonicalSourceRestrictedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _he
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro F _hF
  simpa only [inter_univ] using!
    measureReal_le_inter_add_inter_compl uniform01Measure
      (canonicalAnnularSignedTorusTupleEvent ε A N e
        (fixedOrderMixedTimes N k e F)) good

/-! ## Coordinate control on canonical signed events -/

/-- A canonical closed signed cell in the compact annulus forces the
Legendre cutoff, including at its endpoints. -/
theorem
    approximationCoordinate_lt_half_of_canonicalAnnularSignedTorusEvent
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {N : ℕ} (hN : 2 ≤ N)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (times : Fin (MixedOccurrenceCount k) → ℕ)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hxCanonical :
      x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e times) :
    ∀ j : Fin (MixedOccurrenceCount k),
      gaussApproximationCoordinate (times j) x < (1 : ℝ) / 2 := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hsignedTuple :=
    (mem_canonicalAnnularSignedTorusTupleEvent_iff e times x).mp
      hxCanonical
  have hall :=
    mem_orderedEventIntersection_ofFn_iff.mp hsignedTuple.1
  intro j
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hindex := hsigned (e j).1 hactive
  have hj := hall j
  have hjValue :
      gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) (times j) x ∈
        Icc (flattenedAnnularSignedLower ε A e j)
          (flattenedAnnularSignedUpper ε A e j) := hj.2
  have hlowerAbs :
      |flattenedAnnularSignedLower ε A e j| ≤ A := by
    simpa only [← annularOccurrenceSignedLower_flattened] using!
      abs_annularOccurrenceSignedLower_le
        hε hεA hgrid (e j).1 hindex
  have hupperAbs :
      |flattenedAnnularSignedUpper ε A e j| ≤ A := by
    simpa only [← annularOccurrenceSignedUpper_flattened] using!
      abs_annularOccurrenceSignedUpper_le
        hε hεA hgrid (e j).1 hindex
  have hvalueAbs :
      |gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) (times j) x| ≤ A := by
    apply abs_le.mpr
    exact ⟨(abs_le.mp hlowerAbs).1.trans hjValue.1,
      hjValue.2.trans (abs_le.mp hupperAbs).2⟩
  let w : PositiveDigitWord (times j) :=
    selectedGaussPrefixWord (times j) x
  have hdomain :
      x ∈ positivePrefixDomain (times j) :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  have hxCylinder :
      x ∈ positivePrefixCylinder (times j) w :=
    selectedGaussPrefixWord_mem hdomain
  have hex : x ∉ gaussPrefixExceptional (times j + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating
      hxUnit hxNonterm (times j + 1)
  have htheta :
      0 < gaussApproximationCoordinate (times j) x :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix
      w hxUnit hex hxCylinder
  have habsFormula :
      |gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) (times j) x| =
        Real.log (N : ℝ) *
          gaussApproximationCoordinate (times j) x := by
    unfold gaussSignedScaledApproximationCoordinate
      gaussScaledApproximationCoordinate
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_pos hlog, abs_of_pos htheta]
  have hthetaLe :
      gaussApproximationCoordinate (times j) x ≤
        A / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlog).2
    calc
      gaussApproximationCoordinate (times j) x *
          Real.log (N : ℝ) =
        Real.log (N : ℝ) *
          gaussApproximationCoordinate (times j) x := mul_comm _ _
      _ = |gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) (times j) x| := habsFormula.symm
      _ ≤ A := hvalueAbs
  exact hthetaLe.trans_lt hsmall

/-! ## The finite good-event sandwich -/

/-- One contracted canonical source term is, almost everywhere on the
denominator good event, contained in the corresponding literal event.
The only endpoint issue is discharged by the proved closed/half-open
signed-window null-boundary theorem. -/
theorem ae_contractedCanonicalEvent_inter_good_subset_literalEvent
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (hF : F ∈ contractedAnnularCanonicalOrderSource N eta k e)
    (hbound : ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e
            (fixedOrderMixedTimes N k e F) ∩
          gaussDenominatorLinearGoodEvent C L Delta →
        x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
          gaussDenominatorLinearGoodEvent C L Delta := by
  have hsource := Finset.mem_filter.mp hF
  have hboxes :
      ∀ j, fixedOrderMixedTimes N k e F j ∈
        contractedAnnularTimeDepthBox N eta (e j).1 :=
    fun j ↦ (hsource.2 j).1
  have hdenPoint :
      ∀ x ∈ gaussDenominatorLinearGoodEvent C L Delta,
        ∀ z : GaussPrefixMixedOccurrence k,
          cfTerminalDenominator
            (selectedGaussPrefixWord (F.1 z.1 z.2) x).1 ≤ N := by
    intro x hxGood
    exact forall_selectedDenominator_le_of_contractedAnnularBoxes
      hgrid (Real.log_pos (by exact_mod_cast hN)) e F htime
      hxGood hbound hmargin hboxes
  have hendpoint :=
    ae_mem_gaussSignedApproximationTupleEvent_iff_Ico_of_carrier
      hN
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (fixedOrderMixedTimes N k e F)
  filter_upwards [ae_nonterminating_uniform01, hendpoint] with
      x hxNonterm hxEndpoint hxLeft
  rcases hxLeft with ⟨hxCanonical, hxGood⟩
  have htheta :=
    approximationCoordinate_lt_half_of_canonicalAnnularSignedTorusEvent
      hε hεA hgrid hN hsigned e
      (fixedOrderMixedTimes N k e F)
      hxNonterm.1 hxNonterm.2 hsmall hxCanonical
  have hdenChron :
      ∀ j : Fin (MixedOccurrenceCount k),
        cfTerminalDenominator
            (selectedGaussPrefixWord
              (fixedOrderMixedTimes N k e F j) x).1 ≤ N := by
    intro j
    simpa only [fixedOrderMixedTimes] using! hdenPoint x hxGood (e j)
  have hsignedClosed :=
    (mem_canonicalAnnularSignedTorusTupleEvent_iff_real_cells
      hgrid htorus e (fixedOrderMixedTimes N k e F) x).mp hxCanonical
  have hsignedIco :
      x ∈ gaussSignedApproximationTupleEventIco
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (fixedOrderMixedTimes N k e F) :=
    (hxEndpoint (fun j ↦ ⟨hdenChron j, htheta j⟩)).mp
      hsignedClosed.1
  have hliteralTime :
      gaussPrefixAnnularLiteralTimeCondition
        (N := N) e (fixedOrderMixedTimes N k e F) x :=
    literalTimeCondition_of_contracted_on_good
      e (fixedOrderMixedTimes N k e F) htime
      (Real.log_pos (by exact_mod_cast hN)) hxGood
      hbound hmargin hboxes
  refine ⟨?_, hxGood⟩
  apply
    (mem_gaussPrefixAnnularLiteralMixedTupleEvent_iff_coordinates
      F e hxNonterm.1 hxNonterm.2).mpr
  intro j
  have hsignedJ :=
    mem_orderedEventIntersection_ofFn_iff.mp hsignedIco j
  refine ⟨hdenChron j, htheta j, hliteralTime j, ?_,
    hsignedClosed.2 j⟩
  unfold intervalGridCell
  rw [if_pos (hsigned (e j).1 (by
    have hj := (e j).2.isLt
    omega))]
  simpa only [flattenedAnnularSignedLower,
    flattenedAnnularSignedUpper, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_Ico] using! hsignedJ.2

/-- One literal term on the good event is almost everywhere contained in
its expanded canonical term; if the deterministic expanded-source
condition fails, the restricted literal term is null. -/
theorem ae_literalEvent_inter_good_subset_expandedCanonicalEvent
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (hForder : F ∈ canonicalMixedOrderClass N k e)
    (hbound : ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ)) :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
          gaussDenominatorLinearGoodEvent C L Delta →
        x ∈
          (if F ∈ expandedAnnularCanonicalOrderSource N eta k e then
            canonicalAnnularSignedTorusTupleEvent ε A N e
                (fixedOrderMixedTimes N k e F) ∩
              gaussDenominatorLinearGoodEvent C L Delta
          else ∅) := by
  filter_upwards [ae_nonterminating_uniform01] with x hxNonterm hxLeft
  rcases hxLeft with ⟨hxLiteral, hxGood⟩
  have hbridge :=
    expandedSource_and_canonicalEvent_of_literalEvent_on_good
      hε hεA hgrid hN k htime hsigned htorus e F hForder
      hxNonterm.1 hxNonterm.2 hxGood hbound hmargin hxLiteral
  rw [if_pos hbridge.1]
  exact ⟨hbridge.2, hxGood⟩

theorem ae_literalEvent_inter_good_subset_expandedCanonicalEvent_of_eventBound
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (hForder : F ∈ canonicalMixedOrderClass N k e)
    (hbound :
      ∀ x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F,
        ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ)) :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
          gaussDenominatorLinearGoodEvent C L Delta →
        x ∈
          (if F ∈ expandedAnnularCanonicalOrderSource N eta k e then
            canonicalAnnularSignedTorusTupleEvent ε A N e
                (fixedOrderMixedTimes N k e F) ∩
              gaussDenominatorLinearGoodEvent C L Delta
          else ∅) := by
  filter_upwards [ae_nonterminating_uniform01] with x hxNonterm hxLeft
  rcases hxLeft with ⟨hxLiteral, hxGood⟩
  have hbridge :=
    expandedSource_and_canonicalEvent_of_literalEvent_on_good
      hε hεA hgrid hN k htime hsigned htorus e F hForder
      hxNonterm.1 hxNonterm.2 hxGood (hbound x hxLiteral)
      hmargin hxLiteral
  rw [if_pos hbridge.1]
  exact ⟨hbridge.2, hxGood⟩

theorem aggregate_contractedCanonical_good_le_literal_good
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (hbound : ∀ e
      (F : GloballyInjectiveMixedDepthTuple N k),
      F ∈ contractedAnnularCanonicalOrderSource N eta k e →
        ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    aggregateCanonicalSourceRestrictedMass ε A N k
        (fun e ↦ contractedAnnularCanonicalOrderSource N eta k e)
        (gaussDenominatorLinearGoodEvent C L Delta) ≤
      aggregateLiteralAnnularRestrictedMass ε A N k
        (gaussDenominatorLinearGoodEvent C L Delta) := by
  unfold aggregateCanonicalSourceRestrictedMass
    aggregateLiteralAnnularRestrictedMass
  apply Finset.sum_le_sum
  intro e _he
  calc
    (∑ F ∈ contractedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
              (fixedOrderMixedTimes N k e F) ∩
            gaussDenominatorLinearGoodEvent C L Delta)) ≤
      ∑ F ∈ contractedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
            gaussDenominatorLinearGoodEvent C L Delta) := by
      apply Finset.sum_le_sum
      intro F hF
      exact measureReal_mono_ae_of_finite uniform01Measure
        (ae_contractedCanonicalEvent_inter_good_subset_literalEvent
          hε hεA hgrid hN k htime hsigned htorus e F hF
          (hbound e F hF) hmargin hsmall)
    _ ≤
      ∑ F ∈ canonicalMixedOrderClass N k e,
        uniform01Measure.real
          (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
            gaussDenominatorLinearGoodEvent C L Delta) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro F hF
        exact (Finset.mem_filter.mp hF).1
      · intro _F _hF _hnot
        exact measureReal_nonneg

theorem aggregate_literal_good_le_expandedCanonical_good
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (hbound : ∀ e
      (F : GloballyInjectiveMixedDepthTuple N k),
      F ∈ canonicalMixedOrderClass N k e →
        ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ)) :
    aggregateLiteralAnnularRestrictedMass ε A N k
        (gaussDenominatorLinearGoodEvent C L Delta) ≤
      aggregateCanonicalSourceRestrictedMass ε A N k
        (fun e ↦ expandedAnnularCanonicalOrderSource N eta k e)
        (gaussDenominatorLinearGoodEvent C L Delta) := by
  unfold aggregateCanonicalSourceRestrictedMass
    aggregateLiteralAnnularRestrictedMass
  apply Finset.sum_le_sum
  intro e _he
  calc
    (∑ F ∈ canonicalMixedOrderClass N k e,
        uniform01Measure.real
          (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
            gaussDenominatorLinearGoodEvent C L Delta)) ≤
      ∑ F ∈ canonicalMixedOrderClass N k e,
        if F ∈ expandedAnnularCanonicalOrderSource N eta k e then
          uniform01Measure.real
            (canonicalAnnularSignedTorusTupleEvent ε A N e
                (fixedOrderMixedTimes N k e F) ∩
              gaussDenominatorLinearGoodEvent C L Delta)
        else 0 := by
      apply Finset.sum_le_sum
      intro F hF
      have hmono :=
        measureReal_mono_ae_of_finite uniform01Measure
          (s :=
            gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
              gaussDenominatorLinearGoodEvent C L Delta)
          (t :=
            if F ∈ expandedAnnularCanonicalOrderSource N eta k e then
              canonicalAnnularSignedTorusTupleEvent ε A N e
                  (fixedOrderMixedTimes N k e F) ∩
                gaussDenominatorLinearGoodEvent C L Delta
            else ∅)
          (ae_literalEvent_inter_good_subset_expandedCanonicalEvent
            hε hεA hgrid hN k htime hsigned htorus e F hF
            (hbound e F hF) hmargin)
      split_ifs with hExpanded
      · simpa only [hExpanded, if_true] using! hmono
      · simpa only [hExpanded, if_false, measureReal_empty] using! hmono
    _ =
      ∑ F ∈ expandedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
              (fixedOrderMixedTimes N k e F) ∩
            gaussDenominatorLinearGoodEvent C L Delta) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext F
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_horder, hExpanded⟩
          exact hExpanded
        · intro hExpanded
          exact ⟨(Finset.mem_filter.mp hExpanded).1, hExpanded⟩
      · intro F hF
        rfl

theorem aggregate_literal_good_le_expandedCanonical_good_of_eventBound
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (hbound : ∀ e
      (F : GloballyInjectiveMixedDepthTuple N k),
      F ∈ canonicalMixedOrderClass N k e →
        ∀ x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F,
          ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ)) :
    aggregateLiteralAnnularRestrictedMass ε A N k
        (gaussDenominatorLinearGoodEvent C L Delta) ≤
      aggregateCanonicalSourceRestrictedMass ε A N k
        (fun e ↦ expandedAnnularCanonicalOrderSource N eta k e)
        (gaussDenominatorLinearGoodEvent C L Delta) := by
  unfold aggregateCanonicalSourceRestrictedMass
    aggregateLiteralAnnularRestrictedMass
  apply Finset.sum_le_sum
  intro e _he
  calc
    (∑ F ∈ canonicalMixedOrderClass N k e,
        uniform01Measure.real
          (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
            gaussDenominatorLinearGoodEvent C L Delta)) ≤
      ∑ F ∈ canonicalMixedOrderClass N k e,
        if F ∈ expandedAnnularCanonicalOrderSource N eta k e then
          uniform01Measure.real
            (canonicalAnnularSignedTorusTupleEvent ε A N e
                (fixedOrderMixedTimes N k e F) ∩
              gaussDenominatorLinearGoodEvent C L Delta)
        else 0 := by
      apply Finset.sum_le_sum
      intro F hF
      have hmono :=
        measureReal_mono_ae_of_finite uniform01Measure
          (s :=
            gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
              gaussDenominatorLinearGoodEvent C L Delta)
          (t :=
            if F ∈ expandedAnnularCanonicalOrderSource N eta k e then
              canonicalAnnularSignedTorusTupleEvent ε A N e
                  (fixedOrderMixedTimes N k e F) ∩
                gaussDenominatorLinearGoodEvent C L Delta
            else ∅)
          (ae_literalEvent_inter_good_subset_expandedCanonicalEvent_of_eventBound
            hε hεA hgrid hN k htime hsigned htorus e F hF
            (hbound e F hF) hmargin)
      split_ifs with hExpanded
      · simpa only [hExpanded, if_true] using! hmono
      · simpa only [hExpanded, if_false, measureReal_empty] using! hmono
    _ =
      ∑ F ∈ expandedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
              (fixedOrderMixedTimes N k e F) ∩
            gaussDenominatorLinearGoodEvent C L Delta) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext F
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_horder, hExpanded⟩
          exact hExpanded
        · intro hExpanded
          exact ⟨(Finset.mem_filter.mp hExpanded).1, hExpanded⟩
      · intro F _hF
        rfl

/-! ## Absolute deletion of the literal denominator-bad mass -/

/-- The single finset carrying both the chronological order tag and its
literal globally-injective source tuple. -/
def orderedLiteralTupleIndex
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ) :
    Finset
      (Σ _e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        GloballyInjectiveMixedDepthTuple N k) :=
  (Finset.univ :
      Finset (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)).sigma
    (canonicalMixedOrderClass N k)

theorem aggregateLiteralAnnularRestrictedMass_eq_orderedIndex
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) (carrier : Set ℝ) :
    aggregateLiteralAnnularRestrictedMass ε A N k carrier =
      ∑ z ∈ orderedLiteralTupleIndex N k,
        uniform01Measure.real
          (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k z.2 ∩
            carrier) := by
  unfold aggregateLiteralAnnularRestrictedMass orderedLiteralTupleIndex
  exact Finset.sum_sigma'
    (Finset.univ :
      Finset (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k))
    (canonicalMixedOrderClass N k)
    (fun _e F ↦
      uniform01Measure.real
        (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ∩
          carrier))

/-- At each point, the full chronological literal indicator sum is
bounded by the exact mixed falling-factorial statistic.  This is the
pointwise version needed to keep the bad-event absolute value inside the
finite tuple sum. -/
theorem orderedLiteral_indicatorSum_le_mixedDescFactorial
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) (x : ℝ) :
    (∑ z ∈ orderedLiteralTupleIndex N k,
      (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k z.2).indicator
        (fun _ ↦ (1 : ℝ)) x) ≤
      mixedDescFactorial k
        (gaussPrefixMarkedCountVector N
          (annularGridCell ε A grid) x) := by
  classical
  let E : AnnularGridIndex grid → ℕ → Set ℝ :=
    fun i ↦ gaussPrefixMarkedEvent N (annularGridCell ε A grid i)
  let term : GloballyInjectiveMixedDepthTuple N k → ℝ :=
    fun F ↦
      (mixedTupleEvent E F.1).indicator (fun _ ↦ (1 : ℝ)) x
  let order :
      GloballyInjectiveMixedDepthTuple N k →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) :=
    canonicalMixedOccurrenceOrder N k
  have hordered :
      (∑ z ∈ orderedLiteralTupleIndex N k,
        (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k z.2).indicator
          (fun _ ↦ (1 : ℝ)) x) =
        ∑ F : GloballyInjectiveMixedDepthTuple N k, term F := by
    unfold orderedLiteralTupleIndex
    rw [Finset.sum_sigma]
    change
      (∑ e, ∑ F ∈ canonicalMixedOrderClass N k e, term F) =
        ∑ F, term F
    rw [← Finset.sum_fiberwise
      (Finset.univ : Finset (GloballyInjectiveMixedDepthTuple N k))
      order term]
    apply Finset.sum_congr rfl
    intro e _he
    apply Finset.sum_congr
    · ext F
      simp only [canonicalMixedOrderClass, Finset.mem_filter,
        Finset.mem_univ, true_and, order]
    · intro F _hF
      rfl
  rw [hordered]
  have hsubtype :
      (∑ F : GloballyInjectiveMixedDepthTuple N k, term F) =
        ∑ F ∈
          (Finset.univ :
            Finset (GaussPrefixMixedDepthTuple N k)).filter
              (IsGloballyInjectiveMixedDepthTuple N k),
          (mixedTupleEvent E F).indicator (fun _ ↦ (1 : ℝ)) x := by
    symm
    exact Finset.sum_subtype
      ((Finset.univ :
        Finset (GaussPrefixMixedDepthTuple N k)).filter
          (IsGloballyInjectiveMixedDepthTuple N k))
      (by intro F; simp)
      (fun F ↦
        (mixedTupleEvent E F).indicator (fun _ ↦ (1 : ℝ)) x)
  rw [hsubtype]
  calc
    (∑ F ∈
        (Finset.univ :
          Finset (GaussPrefixMixedDepthTuple N k)).filter
            (IsGloballyInjectiveMixedDepthTuple N k),
        (mixedTupleEvent E F).indicator (fun _ ↦ (1 : ℝ)) x) ≤
      ∑ F : GaussPrefixMixedDepthTuple N k,
        (mixedTupleEvent E F).indicator (fun _ ↦ (1 : ℝ)) x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro F _hF _hnot
        exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
    _ =
      mixedDescFactorial k
        (fun i ↦ finiteEventCount (Finset.Icc 0 N) (E i) x) := by
      rw [mixedDescFactorial_finiteEventCount_eq_sum_indicators]
      apply Finset.sum_congr
      · ext F
        simp only [Finset.mem_univ]
      · intro F _hF
        rfl
    _ =
      mixedDescFactorial k
        (gaussPrefixMarkedCountVector N
          (annularGridCell ε A grid) x) := by
      congr 2

/-- The finite Gauss-prefix mixed statistic is integrable. -/
theorem integrable_mixedDescFactorial_gaussPrefixMarkedCountVector
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Integrable
      (fun x ↦
        mixedDescFactorial k
          (gaussPrefixMarkedCountVector N
            (annularGridCell ε A grid) x))
      uniform01Measure := by
  have hmeas :
      Measurable
        (fun x ↦
          mixedDescFactorial k
            (gaussPrefixMarkedCountVector N
              (annularGridCell ε A grid) x)) :=
    measurable_mixedDescFactorial_comp k
      (gaussPrefixMarkedCountVector N (annularGridCell ε A grid))
      (fun i ↦ measurable_gaussPrefixMarkedCount N
        (measurableSet_annularGridCell ε A grid i))
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (((N + 1 : ℕ) : ℝ) ^ (∑ i, k i))
  filter_upwards with x
  rw [Real.norm_of_nonneg (by
    unfold mixedDescFactorial
    positivity)]
  apply mixedDescFactorial_le_dominator_pow
  intro i
  unfold gaussPrefixMarkedCountVector gaussPrefixMarkedCount
  calc
    (∑ n ∈ Finset.Icc 0 N,
        if x ∈ gaussPrefixMarkedEvent N
            (annularGridCell ε A grid i) n then 1 else 0) ≤
      ∑ _n ∈ Finset.Icc 0 N, 1 := by
        apply Finset.sum_le_sum
        intro n _hn
        split <;> omega
    _ = N + 1 := by simp

/-- The literal bad-event tuple mass is bounded by the restricted mixed
falling-factorial integral. -/
theorem aggregateLiteral_bad_le_mixedDescFactorial_integral
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) (bad : Set ℝ) :
    aggregateLiteralAnnularRestrictedMass ε A N k bad ≤
      ∫ x in bad,
        mixedDescFactorial k
          (gaussPrefixMarkedCountVector N
            (annularGridCell ε A grid) x)
        ∂uniform01Measure := by
  rw [aggregateLiteralAnnularRestrictedMass_eq_orderedIndex]
  exact sum_measureReal_inter_le_setIntegral
    uniform01Measure (orderedLiteralTupleIndex N k)
    (fun z ↦ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k z.2)
    bad
    (fun x ↦
      mixedDescFactorial k
        (gaussPrefixMarkedCountVector N
          (annularGridCell ε A grid) x))
    (fun z _hz ↦
      measurableSet_gaussPrefixAnnularLiteralMixedTupleEvent
        ε A N k z.2)
    (integrable_mixedDescFactorial_gaussPrefixMarkedCountVector
      ε A N k)
    (orderedLiteral_indicatorSum_le_mixedDescFactorial ε A N k)

theorem ae_mixedDescFactorial_gaussPrefixGrid_le_compactAnnularCount_pow
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {N : ℕ} (hN : 2 ≤ N) (hlog : 2 * A < Real.log (N : ℝ))
    (k : AnnularGridIndex grid → ℕ) :
    ∀ᵐ x ∂uniform01Measure,
      mixedDescFactorial k
          (gaussPrefixMarkedCountVector N
            (annularGridCell ε A grid) x) ≤
        (markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) x : ℝ) ^
            MixedOccurrenceCount k := by
  have hall :
      ∀ᵐ x ∂uniform01Measure,
        ∀ i : AnnularGridIndex grid,
          gaussPrefixMarkedCount N (annularGridCell ε A grid i) x ≤
            markedResonanceCount N N
              (compactAnnularMarkedRegion ε A) x := by
    rw [ae_all_iff]
    intro i
    filter_upwards
      [ae_markedResonanceCount_eq_gaussPrefixMarkedCount
        hN hε.le hlog
        (annularGridCell_subset_compactAnnularMarkedRegion
          hεA hgrid i)] with x hx
    rw [← hx]
    exact markedResonanceCount_mono_set N N
      (annularGridCell_subset_compactAnnularMarkedRegion
        hεA hgrid i) x
  filter_upwards [hall] with x hx
  have hdom :=
    mixedDescFactorial_le_dominator_pow k
      (gaussPrefixMarkedCountVector N
        (annularGridCell ε A grid) x)
      (markedResonanceCount N N
        (compactAnnularMarkedRegion ε A) x)
      (by
        intro i
        exact hx i)
  simpa only [← card_gaussPrefixMixedOccurrence] using! hdom

theorem tendsto_aggregateLiteral_denominatorBad_mass_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {eta : ℝ} (heta : 0 < eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (Cdepth : ℕ) (hCdepth : 0 < Cdepth) :
    Tendsto
      (fun N ↦
        aggregateLiteralAnnularRestrictedMass ε A N k
          (gaussDenominatorLinearBadEvent Cdepth
            (expandedAnnularDepthAmbientSize N eta)
            (annularBoundaryDenominatorTolerance eta)))
      atTop (nhds 0) := by
  let bad : ℕ → Set ℝ := fun N ↦
    gaussDenominatorLinearBadEvent Cdepth
      (expandedAnnularDepthAmbientSize N eta)
      (annularBoundaryDenominatorTolerance eta)
  let upper : ℕ → ℝ := fun N ↦
    ∫ x in bad N,
      (markedResonanceCount N N
        (compactAnnularMarkedRegion ε A) x : ℝ) ^
          MixedOccurrenceCount k
      ∂uniform01Measure
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa only [upper, bad] using!
      tendsto_compactAnnularMarkedResonanceCount_pow_on_denominatorBadEvent
        (fun N ↦ expandedAnnularDepthAmbientSize N eta)
        (MixedOccurrenceCount k) Cdepth hr hε hεA hCdepth
        (annularBoundaryDenominatorTolerance_pos heta)
        (tendsto_expandedAnnularDepthAmbientSize_atTop heta.le)
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      unfold aggregateLiteralAnnularRestrictedMass
      positivity
  · filter_upwards
      [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)] with
      N hN hlog
    calc
      aggregateLiteralAnnularRestrictedMass ε A N k (bad N) ≤
          ∫ x in bad N,
            mixedDescFactorial k
              (gaussPrefixMarkedCountVector N
                (annularGridCell ε A grid) x)
            ∂uniform01Measure :=
        aggregateLiteral_bad_le_mixedDescFactorial_integral
          ε A N k (bad N)
      _ ≤ upper N := by
        apply integral_mono_ae
        · exact
            (integrable_mixedDescFactorial_gaussPrefixMarkedCountVector
              ε A N k).mono_measure Measure.restrict_le_self
        · exact
            (integrable_markedResonanceCount_pow N N
              (MixedOccurrenceCount k)
              (measurableSet_compactAnnularMarkedRegion ε A)).mono_measure
                Measure.restrict_le_self
        · exact (ae_mono Measure.restrict_le_self)
            (ae_mixedDescFactorial_gaussPrefixGrid_le_compactAnnularCount_pow
              hε hεA hgrid hN hlog k)
  · exact hupper

/-! ## Absolute deletion of the canonical denominator-bad mass -/

theorem epsilon_le_flattenedAnnular_oriented_lower
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    ε ≤
      gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j := by
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hidx : (e j).1.signed.1 + 1 ≤ grid :=
    Nat.succ_le_iff.mpr (hsigned (e j).1 hactive)
  have hlowerIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid (Nat.le_of_lt (hsigned (e j).1 hactive))
  have hupperIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le hgrid hidx
  cases hs : (e j).1.sign
  · rw [flattenedAnnular_oriented_lower_of_sign_false ε A e j hs]
    unfold flattenedAnnularSignedUpper
    simp only [signedGridLower, signedGridUpper, hs,
      Bool.false_eq_true, if_false] at hupperIcc ⊢
    simpa only [neg_neg] using! neg_le_neg hupperIcc.2
  · rw [flattenedAnnular_oriented_lower_of_sign_true ε A e j hs]
    unfold flattenedAnnularSignedLower
    simp only [signedGridLower, signedGridUpper, hs, if_true]
      at hlowerIcc ⊢
    exact hlowerIcc.1

/-- A contracted source tuple, regarded as an ordered distinct embedding
into the common expanded depth horizon. -/
def contractedSourceRangeEmbedding
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : {F : GloballyInjectiveMixedDepthTuple N k //
      F ∈ contractedAnnularCanonicalOrderSource N eta k e}) :
    Fin (MixedOccurrenceCount k) ↪
      (Finset.range (expandedAnnularDepthAmbientSize N eta) :
        Finset ℕ) where
  toFun j := by
    let t := fixedOrderMixedTimes N k e F.1
    have hsource := Finset.mem_filter.mp F.2
    have hparityBox :
        t j ∈ mixedOccurrenceParityBox
          (contractedAnnularOccurrenceDepthBoxes N eta k)
          (annularOccurrenceParity k) (e j) := by
      exact Finset.mem_filter.mpr
        ⟨(hsource.2 j).1, (hsource.2 j).2⟩
    exact ⟨t j, Finset.mem_range.mpr
      (contractedAnnularOccurrenceParityBox_lt_ambient
        hgrid heta k htime N (e j) (t j) hparityBox)⟩
  inj' := by
    intro a b hab
    have hsource := Finset.mem_filter.mp F.2
    have hstrict :=
      strictMono_canonicalMixedOccurrenceOrder N k F.1
    rw [mem_canonicalMixedOrderClass_iff.mp hsource.1] at hstrict
    apply hstrict.injective
    have habNat := congrArg
      (fun q :
        (Finset.range (expandedAnnularDepthAmbientSize N eta) :
          Finset ℕ) ↦ (q : ℕ)) hab
    change
      fixedOrderMixedTimes N k e F.1 a =
        fixedOrderMixedTimes N k e F.1 b at habNat
    exact habNat

theorem contractedSourceRangeEmbedding_injective
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Function.Injective
      (contractedSourceRangeEmbedding (N := N)
        hgrid heta k htime e) := by
  intro F G hFG
  apply Subtype.ext
  apply fixedOrderMixedTimes_injective N k e
  funext j
  have hj := congrArg
    (fun f : Fin (MixedOccurrenceCount k) ↪
        (Finset.range (expandedAnnularDepthAmbientSize N eta) :
          Finset ℕ) ↦ ((f j : _) : ℕ)) hFG
  exact hj

theorem canonicalAnnularEvent_subset_commonApproximationTuple
    {ε A : ℝ} (hεA : ε < A)
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    {k : AnnularGridIndex grid → ℕ}
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : {F : GloballyInjectiveMixedDepthTuple N k //
      F ∈ contractedAnnularCanonicalOrderSource N eta k e})
    {x : ℝ}
    (hx :
      x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e
        (fixedOrderMixedTimes N k e F.1)) :
    x ∈ tupleEvent
      (fun n ↦ gaussApproximationWindow
        (Real.log (N : ℝ)) n ε A)
      (contractedSourceRangeEmbedding hgrid heta k htime e F) := by
  have hsignedTuple :=
    (mem_canonicalAnnularSignedTorusTupleEvent_iff
      e (fixedOrderMixedTimes N k e F.1) x).mp hx
  have hall :=
    mem_orderedEventIntersection_ofFn_iff.mp hsignedTuple.1
  have hsource := Finset.mem_filter.mp F.2
  apply Set.mem_iInter.mpr
  intro j
  have hparity :
      fixedOrderMixedTimes N k e F.1 j % 2 =
        (flattenedAnnularParity e j).1 := (hsource.2 j).2
  have hlower :
      gaussParityOrientedLower
          (fixedOrderMixedTimes N k e F.1 j)
          (flattenedAnnularSignedLower ε A e j)
          (flattenedAnnularSignedUpper ε A e j) =
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity e)
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e) j := by
    exact gaussParityOrientedLower_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (flattenedAnnularParity e j).isLt]
        exact hparity)
      _ _
  have hupper :
      gaussParityOrientedUpper
          (fixedOrderMixedTimes N k e F.1 j)
          (flattenedAnnularSignedLower ε A e j)
          (flattenedAnnularSignedUpper ε A e j) =
        gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity e)
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e) j := by
    exact gaussParityOrientedUpper_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (flattenedAnnularParity e j).isLt]
        exact hparity)
      _ _
  have hj := hall j
  rw [gaussSignedApproximationWindow_eq_oriented,
    hlower, hupper] at hj
  apply mem_gaussApproximationWindow_iff.mpr
  refine ⟨(mem_gaussApproximationWindow_iff.mp hj).1, ?_⟩
  have hjBounds := (mem_gaussApproximationWindow_iff.mp hj).2
  exact ⟨
    (epsilon_le_flattenedAnnular_oriented_lower
      hεA hgrid hsigned e j).trans hjBounds.1,
    hjBounds.2.trans
      (flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned e j)⟩

theorem contractedCanonical_indicatorSum_le_approximationWindowCount_pow
    {ε A : ℝ} (hεA : ε < A)
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (x : ℝ) :
    (∑ F ∈ contractedAnnularCanonicalOrderSource N eta k e,
      (canonicalAnnularSignedTorusTupleEvent ε A N e
        (fixedOrderMixedTimes N k e F)).indicator
          (fun _ ↦ (1 : ℝ)) x) ≤
      (gaussApproximationWindowCount
        (Real.log (N : ℝ))
        (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
          MixedOccurrenceCount k := by
  classical
  let source :=
    contractedAnnularCanonicalOrderSource N eta k e
  let Emb :=
    Fin (MixedOccurrenceCount k) ↪
      (Finset.range (expandedAnnularDepthAmbientSize N eta) :
        Finset ℕ)
  let phi :
      {F : GloballyInjectiveMixedDepthTuple N k // F ∈ source} → Emb :=
    fun F ↦ contractedSourceRangeEmbedding hgrid heta k htime e F
  let E : ℕ → Set ℝ :=
    fun n ↦ gaussApproximationWindow (Real.log (N : ℝ)) n ε A
  let canonTerm : GloballyInjectiveMixedDepthTuple N k → ℝ :=
    fun F ↦
      (canonicalAnnularSignedTorusTupleEvent ε A N e
        (fixedOrderMixedTimes N k e F)).indicator
          (fun _ ↦ (1 : ℝ)) x
  let approxTerm : Emb → ℝ :=
    fun f ↦ (tupleEvent E f).indicator (fun _ ↦ (1 : ℝ)) x
  change (∑ F ∈ source, canonTerm F) ≤ _
  rw [Finset.sum_subtype source (fun F ↦ by rfl) canonTerm]
  calc
    (∑ F : {F : GloballyInjectiveMixedDepthTuple N k // F ∈ source},
        canonTerm F.1) ≤
      ∑ F : {F : GloballyInjectiveMixedDepthTuple N k // F ∈ source},
        approxTerm (phi F) := by
      apply Finset.sum_le_sum
      intro F _hF
      by_cases hxCanonical :
          x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e
            (fixedOrderMixedTimes N k e F.1)
      · dsimp only [canonTerm, approxTerm, phi, E]
        rw [Set.indicator_of_mem hxCanonical]
        rw [Set.indicator_of_mem]
        exact canonicalAnnularEvent_subset_commonApproximationTuple
          hεA hgrid heta htime hsigned e F hxCanonical
      · dsimp only [canonTerm, approxTerm, phi, E]
        rw [Set.indicator_of_notMem hxCanonical]
        exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
    _ =
      ∑ f ∈
          (Finset.univ :
            Finset {F : GloballyInjectiveMixedDepthTuple N k //
              F ∈ source}).image phi,
        approxTerm f := by
      symm
      rw [Finset.sum_image]
      intro F _hF G _hG hFG
      exact contractedSourceRangeEmbedding_injective
        hgrid heta k htime e hFG
    _ ≤ ∑ f : Emb, approxTerm f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro f _hf _hnot
        exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
    _ =
      ((finiteEventCount
        (Finset.range (expandedAnnularDepthAmbientSize N eta))
          E x).descFactorial (MixedOccurrenceCount k) : ℝ) := by
      rw [cast_finiteEventCount_descFactorial_eq_sum_indicators]
    _ ≤
      (gaussApproximationWindowCount
        (Real.log (N : ℝ))
        (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
          MixedOccurrenceCount k := by
      exact_mod_cast Nat.descFactorial_le_pow
        (gaussApproximationWindowCount
          (Real.log (N : ℝ))
          (expandedAnnularDepthAmbientSize N eta) ε A x)
        (MixedOccurrenceCount k)

theorem contractedCanonicalSource_bad_le_approximationMoment
    {ε A : ℝ} (hεA : ε < A)
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (bad : Set ℝ) :
    (∑ F ∈ contractedAnnularCanonicalOrderSource N eta k e,
      uniform01Measure.real
        (canonicalAnnularSignedTorusTupleEvent ε A N e
            (fixedOrderMixedTimes N k e F) ∩ bad)) ≤
      ∫ x in bad,
        (gaussApproximationWindowCount
          (Real.log (N : ℝ))
          (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
            MixedOccurrenceCount k
        ∂uniform01Measure := by
  exact sum_measureReal_inter_le_setIntegral
    uniform01Measure
    (contractedAnnularCanonicalOrderSource N eta k e)
    (fun F ↦ canonicalAnnularSignedTorusTupleEvent ε A N e
      (fixedOrderMixedTimes N k e F))
    bad
    (fun x ↦
      (gaussApproximationWindowCount
        (Real.log (N : ℝ))
        (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
          MixedOccurrenceCount k)
    (fun F _hF ↦
      measurableSet_canonicalAnnularSignedTorusTupleEvent
        hgrid htorus e (fixedOrderMixedTimes N k e F))
    (integrable_gaussApproximationWindowCount_pow
      (Real.log (N : ℝ))
      (expandedAnnularDepthAmbientSize N eta)
      (MixedOccurrenceCount k) ε A)
    (contractedCanonical_indicatorSum_le_approximationWindowCount_pow
      hεA hgrid heta k htime hsigned e)

theorem aggregateContractedCanonical_bad_le_approximationMoment
    {ε A : ℝ} (hεA : ε < A)
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (bad : Set ℝ) :
    aggregateCanonicalSourceRestrictedMass ε A N k
        (fun e ↦ contractedAnnularCanonicalOrderSource N eta k e) bad ≤
      (Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) : ℝ) *
        ∫ x in bad,
          (gaussApproximationWindowCount
            (Real.log (N : ℝ))
            (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
              MixedOccurrenceCount k
          ∂uniform01Measure := by
  unfold aggregateCanonicalSourceRestrictedMass
  calc
    (∑ e,
      ∑ F ∈ contractedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
              (fixedOrderMixedTimes N k e F) ∩ bad)) ≤
      ∑ _e :
          Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
        ∫ x in bad,
          (gaussApproximationWindowCount
            (Real.log (N : ℝ))
            (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
              MixedOccurrenceCount k
          ∂uniform01Measure := by
      apply Finset.sum_le_sum
      intro e _he
      exact contractedCanonicalSource_bad_le_approximationMoment
        hεA hgrid heta k htime hsigned htorus e bad
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul]

theorem expandedAnnularDepthAmbientSize_eventually_linear
    {eta : ℝ} (heta : 0 ≤ eta) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ N : ℕ in atTop,
        (expandedAnnularDepthAmbientSize N eta : ℝ) ≤
          D * Real.log (N : ℝ) := by
  let ell : ℝ := (1 + eta) / gaussRoofMean
  let D : ℝ := |ell| + 1
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hellD : ell < D := by
    dsimp only [D]
    exact (le_abs_self ell).trans_lt (lt_add_one |ell|)
  have hratio :
      ∀ᶠ N : ℕ in atTop,
        (expandedAnnularDepthAmbientSize N eta : ℝ) /
            Real.log (N : ℝ) < D :=
    (tendsto_expandedAnnularDepthAmbientSize_div_log
      heta).eventually_lt_const hellD
  refine ⟨D, hD, ?_⟩
  filter_upwards
    [hratio,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hratioN hlog
  exact ((div_lt_iff₀ hlog).mp hratioN).le

theorem tendsto_aggregateContractedCanonical_denominatorBad_mass_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {eta : ℝ} (heta : 0 < eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (Cdepth : ℕ) (hCdepth : 0 < Cdepth) :
    Tendsto
      (fun N ↦
        aggregateCanonicalSourceRestrictedMass ε A N k
          (fun e ↦
            contractedAnnularCanonicalOrderSource N eta k e)
          (gaussDenominatorLinearBadEvent Cdepth
            (expandedAnnularDepthAmbientSize N eta)
            (annularBoundaryDenominatorTolerance eta)))
      atTop (nhds 0) := by
  let bad : ℕ → Set ℝ := fun N ↦
    gaussDenominatorLinearBadEvent Cdepth
      (expandedAnnularDepthAmbientSize N eta)
      (annularBoundaryDenominatorTolerance eta)
  let orderCount : ℝ :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
  let moment : ℕ → ℝ := fun N ↦
    ∫ x in bad N,
      (gaussApproximationWindowCount
        (Real.log (N : ℝ))
        (expandedAnnularDepthAmbientSize N eta) ε A x : ℝ) ^
          MixedOccurrenceCount k
      ∂uniform01Measure
  have hmoment : Tendsto moment atTop (nhds 0) := by
    simpa only [moment, bad] using!
      tendsto_gaussApproximationWindowCount_pow_on_denominatorBadEvent
        (fun N ↦ expandedAnnularDepthAmbientSize N eta)
        (fun N ↦ expandedAnnularDepthAmbientSize N eta)
        (MixedOccurrenceCount k) Cdepth hr hε hεA
        (expandedAnnularDepthAmbientSize_eventually_linear heta.le)
        hCdepth
        (annularBoundaryDenominatorTolerance_pos heta)
        (tendsto_expandedAnnularDepthAmbientSize_atTop heta.le)
  have hupper :
      Tendsto (fun N ↦ orderCount * moment N) atTop (nhds 0) := by
    simpa only [mul_zero] using! hmoment.const_mul orderCount
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      unfold aggregateCanonicalSourceRestrictedMass
      positivity
  · exact Eventually.of_forall fun N ↦
      aggregateContractedCanonical_bad_le_approximationMoment
        hεA hgrid heta.le k htime hsigned htorus (bad N)
  · simpa only [orderCount, moment] using! hupper

/-! ## A common good-event horizon -/

theorem literalMixedTupleEvent_depth_lt_coarseAmbient
    {ε A : ℝ} {grid N : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    {x : ℝ}
    (hx :
      x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F) :
    ∀ j : Fin (MixedOccurrenceCount k),
      fixedOrderMixedTimes N k e F j <
        gaussCoarseDepthAmbientSize N := by
  intro j
  have hxLabeled :
      x ∈ gaussPrefixMarkedEvent N
        (annularGridCell ε A grid (e j).1)
        (F.1 (e j).1 (e j).2) := by
    have hi :=
      Set.mem_iInter.mp
        (show x ∈ mixedTupleEvent
          (fun i ↦ gaussPrefixMarkedEvent N
            (annularGridCell ε A grid i)) F.1 from hx) (e j).1
    exact Set.mem_iInter.mp hi (e j).2
  have hdata := selectedGaussPrefixWord_data_of_mem hxLabeled
  simpa only [fixedOrderMixedTimes] using!
    depth_lt_gaussCoarseDepthAmbientSize_of_denominator_le
      (selectedGaussPrefixWord
        (F.1 (e j).1 (e j).2 : ℕ) x)
      hdata.2.1

theorem exists_coarseDepth_le_mul_expandedDepth_eventually
    {eta : ℝ} (heta : 0 ≤ eta) :
    ∃ C : ℕ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        gaussCoarseDepthAmbientSize N ≤
          C * expandedAnnularDepthAmbientSize N eta := by
  let ell : ℝ := (1 + eta) / gaussRoofMean
  have hell : 0 < ell := by
    dsimp only [ell]
    exact div_pos (by linarith) gaussRoofMean_pos
  obtain ⟨C, hC⟩ := exists_nat_gt (10 / ell)
  have hCpos : 0 < C := by
    by_contra hCzero
    have : C = 0 := Nat.eq_zero_of_not_pos hCzero
    subst C
    norm_num at hC
    have hten : 0 < (10 : ℝ) / ell := div_pos (by norm_num) hell
    linarith
  have hExpanded :
      ∀ᶠ N : ℕ in atTop,
        ell / 2 <
          (expandedAnnularDepthAmbientSize N eta : ℝ) /
            Real.log (N : ℝ) := by
    have hlt : ell / 2 < ell := by linarith
    exact
      (tendsto_expandedAnnularDepthAmbientSize_div_log
        heta).eventually_const_lt hlt
  have hCoarse :
      ∀ᶠ N : ℕ in atTop,
        (gaussCoarseDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ) < 5 :=
    tendsto_gaussCoarseDepthAmbientSize_div_log.eventually_lt_const
      (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  filter_upwards
    [hExpanded, hCoarse,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hExpandedN hCoarseN hlog
  have hExpandedMul :
      ell / 2 * Real.log (N : ℝ) <
        (expandedAnnularDepthAmbientSize N eta : ℝ) :=
    (lt_div_iff₀ hlog).mp hExpandedN
  have hCoarseMul :
      (gaussCoarseDepthAmbientSize N : ℝ) <
        5 * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlog).mp hCoarseN
  have hCReal : 10 / ell < (C : ℝ) := by exact_mod_cast hC
  have hCell : 5 < (C : ℝ) * (ell / 2) := by
    have := (div_lt_iff₀ hell).mp hCReal
    nlinarith
  have hreal :
      (gaussCoarseDepthAmbientSize N : ℝ) <
        (C : ℝ) * (expandedAnnularDepthAmbientSize N eta : ℝ) := by
    have hlogNonneg := hlog.le
    nlinarith
  exact_mod_cast hreal.le

/-! ## Finite absolute comparison -/

theorem abs_sub_le_boundary_add_bad_of_sandwich
    {literalFull literalGood literalBad contractedFull contractedGood
      contractedBad expandedFull expandedGood canonical boundary : ℝ}
    (hliteralSplit : literalFull ≤ literalGood + literalBad)
    (hcontractedSplit :
      contractedFull ≤ contractedGood + contractedBad)
    (hcontractedGoodLiteral : contractedGood ≤ literalGood)
    (hliteralGoodFull : literalGood ≤ literalFull)
    (hliteralGoodExpanded : literalGood ≤ expandedGood)
    (hexpandedGoodFull : expandedGood ≤ expandedFull)
    (hcanonicalContracted : canonical - contractedFull ≤ boundary)
    (hexpandedCanonical : expandedFull - canonical ≤ boundary)
    (hcontractedBadNonneg : 0 ≤ contractedBad) :
    |literalFull - canonical| ≤
      boundary + literalBad + contractedBad := by
  rw [abs_le]
  constructor <;> linarith

theorem abs_literalMass_sub_canonicalBoxMass_le_boundary_add_bad
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    {N C : ℕ} (hN : 2 ≤ N) (hC : 0 < C)
    {eta : ℝ} (heta : 0 < eta)
    (hcoarse :
      gaussCoarseDepthAmbientSize N ≤
        C * expandedAnnularDepthAmbientSize N eta)
    (hmargin :
      annularBoundaryDenominatorTolerance eta *
          (expandedAnnularDepthAmbientSize N eta : ℝ) ≤
        eta * Real.log (N : ℝ))
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    |aggregateLiteralAnnularRestrictedMass ε A N k Set.univ -
        (reindexedAnnularUniformMarkedTupleFiniteMeasure
            (ε := ε) (A := A) N k e₀ :
          Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
          (unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e₀)
            (flattenedAnnularTorusUpper e₀))| ≤
      aggregateUniformMovingSignedApproximationTupleMassSum
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) +
        aggregateLiteralAnnularRestrictedMass ε A N k
          (gaussDenominatorLinearBadEvent C
            (expandedAnnularDepthAmbientSize N eta)
            (annularBoundaryDenominatorTolerance eta)) +
        aggregateCanonicalSourceRestrictedMass ε A N k
          (fun e ↦
            contractedAnnularCanonicalOrderSource N eta k e)
          (gaussDenominatorLinearBadEvent C
            (expandedAnnularDepthAmbientSize N eta)
            (annularBoundaryDenominatorTolerance eta)) := by
  let L := expandedAnnularDepthAmbientSize N eta
  let Delta := annularBoundaryDenominatorTolerance eta
  let good := gaussDenominatorLinearGoodEvent C L Delta
  let bad := gaussDenominatorLinearBadEvent C L Delta
  let literalFull :=
    aggregateLiteralAnnularRestrictedMass ε A N k Set.univ
  let literalGood :=
    aggregateLiteralAnnularRestrictedMass ε A N k good
  let literalBad :=
    aggregateLiteralAnnularRestrictedMass ε A N k bad
  let contractedSource :=
    fun e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k ↦
      contractedAnnularCanonicalOrderSource N eta k e
  let expandedSource :=
    fun e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k ↦
      expandedAnnularCanonicalOrderSource N eta k e
  let contractedFull :=
    aggregateCanonicalSourceRestrictedMass ε A N k
      contractedSource Set.univ
  let contractedGood :=
    aggregateCanonicalSourceRestrictedMass ε A N k
      contractedSource good
  let contractedBad :=
    aggregateCanonicalSourceRestrictedMass ε A N k
      contractedSource bad
  let expandedFull :=
    aggregateCanonicalSourceRestrictedMass ε A N k
      expandedSource Set.univ
  let expandedGood :=
    aggregateCanonicalSourceRestrictedMass ε A N k
      expandedSource good
  let canonical :=
    (reindexedAnnularUniformMarkedTupleFiniteMeasure
        (ε := ε) (A := A) N k e₀ :
      Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
      (unitTorusHalfOpenBox
        (flattenedAnnularTorusLower e₀)
        (flattenedAnnularTorusUpper e₀))
  let boundary :=
    aggregateUniformMovingSignedApproximationTupleMassSum
      (Real.log (N : ℝ))
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ annularCanonicalTimeBoundaryTupleFamily N eta k e)
  have hcontractedBound :
      ∀ e (F : GloballyInjectiveMixedDepthTuple N k),
        F ∈ contractedAnnularCanonicalOrderSource N eta k e →
          ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L := by
    intro e F hF j
    have hsource := Finset.mem_filter.mp hF
    have hparityBox :
        fixedOrderMixedTimes N k e F j ∈
          mixedOccurrenceParityBox
            (contractedAnnularOccurrenceDepthBoxes N eta k)
            (annularOccurrenceParity k) (e j) :=
      Finset.mem_filter.mpr
        ⟨(hsource.2 j).1, (hsource.2 j).2⟩
    have hlt :
        fixedOrderMixedTimes N k e F j < L := by
      exact contractedAnnularOccurrenceParityBox_lt_ambient
        hgrid heta.le k htime N (e j)
          (fixedOrderMixedTimes N k e F j) hparityBox
    have hL : L ≤ C * L := by
      have : 1 ≤ C := hC
      nlinarith
    exact hlt.le.trans hL
  have hliteralEventBound :
      ∀ e (F : GloballyInjectiveMixedDepthTuple N k),
        F ∈ canonicalMixedOrderClass N k e →
          ∀ x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F,
            ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L := by
    intro e F _hF x hx j
    exact
      (literalMixedTupleEvent_depth_lt_coarseAmbient e F hx j).le.trans
        hcoarse
  have hcontractedGoodLiteral :
      contractedGood ≤ literalGood := by
    exact aggregate_contractedCanonical_good_le_literal_good
      hε hεA hgrid hN k htime hsigned htorus
      hcontractedBound (by simpa only [L, Delta] using! hmargin) hsmall
  have hliteralGoodExpanded :
      literalGood ≤ expandedGood := by
    exact
      aggregate_literal_good_le_expandedCanonical_good_of_eventBound
        hε hεA hgrid hN k htime hsigned htorus
        hliteralEventBound (by simpa only [L, Delta] using! hmargin)
  have hliteralSplit :
      literalFull ≤ literalGood + literalBad := by
    have h :=
      aggregateLiteral_univ_le_good_add_bad ε A N k good
    rw [← gaussDenominatorLinearBadEvent_eq_compl C L Delta]
      at h
    exact h
  have hcontractedSplit :
      contractedFull ≤ contractedGood + contractedBad := by
    have h :=
      aggregateCanonicalSource_univ_le_good_add_bad
        ε A N k contractedSource good
    rw [← gaussDenominatorLinearBadEvent_eq_compl C L Delta]
      at h
    exact h
  have hliteralGoodFull : literalGood ≤ literalFull :=
    aggregateLiteralRestrictedMass_le_univ ε A N k good
  have hexpandedGoodFull : expandedGood ≤ expandedFull :=
    aggregateCanonicalSourceRestrictedMass_le_univ
      ε A N k expandedSource good
  have hcanonicalContracted :
      canonical - contractedFull ≤ boundary := by
    dsimp only [contractedFull, contractedSource, canonical, boundary]
    rw [aggregateCanonicalSourceRestrictedMass_univ_contracted]
    exact
      canonical_torusBox_mass_sub_contracted_le_timeBoundary_mass
        (ε := ε) (A := A) (N := N)
        hgrid heta.le k htorus e₀
  have hexpandedCanonical :
      expandedFull - canonical ≤ boundary := by
    dsimp only [expandedFull, expandedSource, canonical, boundary]
    rw [aggregateCanonicalSourceRestrictedMass_univ_expanded]
    exact
      expanded_torusBox_mass_sub_canonical_le_timeBoundary_mass
        (ε := ε) (A := A) (N := N)
        hgrid heta.le k htorus e₀
  have hcontractedBadNonneg : 0 ≤ contractedBad := by
    dsimp only [contractedBad]
    unfold aggregateCanonicalSourceRestrictedMass
    positivity
  have habstract :
    |literalFull - canonical| ≤
      boundary + literalBad + contractedBad :=
    abs_sub_le_boundary_add_bad_of_sandwich
      hliteralSplit hcontractedSplit hcontractedGoodLiteral
      hliteralGoodFull hliteralGoodExpanded hexpandedGoodFull
      hcanonicalContracted hexpandedCanonical hcontractedBadNonneg
  simpa only [literalFull, canonical, boundary, literalBad,
    contractedBad, contractedSource, bad, L, Delta] using! habstract

/-! ## Removal of both comparison errors -/

/-- The literal mixed factorial moment and the canonical marked tuple
measure have the same limit.  The proof fixes a positive boundary width,
removes the denominator-bad event at that fixed width, and only then
chooses the width small enough to remove the deterministic time boundary.
-/
theorem gaussPrefixAnnularLiteralCanonicalBoxTransfer :
    GaussPrefixAnnularLiteralCanonicalBoxTransfer := by
  intro ε A hε hεA grid hgrid k hr htime hsigned htorus e₀
  rw [Metric.tendsto_nhds]
  intro delta hdelta
  have hthird : 0 < delta / 3 := by positivity
  have hboundaryOuter :=
    eventually_eventually_aggregateUniform_annularTimeBoundary_mass_lt
      hε hεA hgrid k hr htime hsigned hthird
  rcases (eventually_atTop.1 hboundaryOuter) with ⟨m, hm⟩
  let eta : ℝ := 1 / ((m : ℝ) + 1)
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have hboundary :
      ∀ᶠ N : ℕ in atTop,
        aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) <
          delta / 3 := by
    simpa only [eta] using! hm m le_rfl
  obtain ⟨C, hC, hcoarse⟩ :=
    exists_coarseDepth_le_mul_expandedDepth_eventually heta.le
  have hliteralBad :=
    (tendsto_aggregateLiteral_denominatorBad_mass_zero
      hε hεA hgrid heta k hr C hC).eventually_lt_const hthird
  have hcanonicalBad :=
    (tendsto_aggregateContractedCanonical_denominatorBad_mass_zero
      hε hεA hgrid heta k hr htime hsigned htorus C hC).eventually_lt_const
        hthird
  have hmargin := eventually_annularBoundaryDenominator_margin heta
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    filter_upwards
      [tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)] with
        N hlog
    have hA : 0 < A := hε.trans hεA
    have hlogPos : 0 < Real.log (N : ℝ) :=
      (mul_pos (by norm_num) hA).trans hlog
    rw [div_lt_iff₀ hlogPos]
    linarith
  filter_upwards
    [eventually_ge_atTop 2, hcoarse, hmargin, hsmall,
      hboundary, hliteralBad, hcanonicalBad] with
      N hN hcoarseN hmarginN hsmallN hboundaryN
      hliteralBadN hcanonicalBadN
  rw [Real.dist_eq, sub_zero]
  have hfinite :=
    abs_literalMass_sub_canonicalBoxMass_le_boundary_add_bad
      hε hεA hgrid k htime hsigned htorus e₀
      hN hC heta hcoarseN hmarginN hsmallN
  rw [aggregateLiteralAnnularRestrictedMass_univ
    hε hεA hgrid N k] at hfinite
  exact hfinite.trans_lt (by linarith)

end

end Erdos1002
