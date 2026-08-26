import ErdosProblems.Erdos1002.GaussPrefixDeepestCylinder
import ErdosProblems.Erdos1002.GaussDenominatorWeakLaw
import ErdosProblems.Erdos1002.GaussFactorialTupleReplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pure digit events as genuine finite-prefix events

The digit observed at Gauss time `n` is the `(n+1)`-st continued-fraction
digit.  Consequently every finite intersection of one-digit events at times
at most `b` is determined by the selected positive word of length `b+1`.

The selected word has a harmless default value off its positive-prefix
domain.  Thus the selected-word event need not be literally equal to the raw
orbit event at terminating rationals or outside the Gauss state space.  The
two events are, however, equal almost everywhere for Gauss measure.  The
results below keep that qualification explicit.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixDigitMeasurabilityPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-! ## Reading one digit from a selected finite word -/

/-- The digit in zero-based position `n` of a positive word of length `b`. -/
def positiveDigitWordDigit {b : ℕ} (n : ℕ) (hn : n < b)
    (w : PositiveDigitWord b) : ℕ :=
  w.1.get ⟨n, by simpa only [w.2.1] using! hn⟩

theorem positiveDigitWordDigit_pos
    {b n : ℕ} (hn : n < b) (w : PositiveDigitWord b) :
    0 < positiveDigitWordDigit n hn w := by
  unfold positiveDigitWordDigit
  apply w.2.2
  exact List.get_mem _ _

/-- On a nonterminating orbit, the analytic digit at time `n` is exactly
the digit read from any deeper selected word. -/
theorem gaussDigitAt_eq_positiveDigitWordDigit_of_mem
    {b n : ℕ} (hn : n < b) (w : PositiveDigitWord b)
    {x : ℝ} (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ positivePrefixCylinder b w) :
    gaussDigitAt n x = positiveDigitWordDigit n hn w := by
  let u : PositiveDigitWord (n + 1) :=
    positiveDigitWordTake (n + 1) (by omega) w
  have hxu : x ∈ positivePrefixCylinder (n + 1) u :=
    mem_positivePrefixCylinder_positiveDigitWordTake
      (by omega) w hxUnit hx
  let q : ℕ := positiveDigitWordDigit n hn w
  have hq : 0 < q := positiveDigitWordDigit_pos hn w
  have hlen : n < w.1.length := by
    rw [w.2.1]
    exact hn
  have huval : u.1 = w.1.take n ++ [q] := by
    simp only [u, positiveDigitWordTake_val]
    symm
    simpa only [q, positiveDigitWordDigit, List.concat_eq_append] using!
      (List.take_concat_get hlen)
  change gaussDigitAt n x = q
  have hdigit :=
    gaussDigitAt_eq_of_mem_append_singleton
      (w := w.1.take n) hq hxUnit
      (by simpa only [positivePrefixCylinder, u, huval] using! hxu)
  have htakeLength : (w.1.take n).length = n := by
    rw [List.length_take, w.2.1, Nat.min_eq_left hn.le]
  rw [htakeLength] at hdigit
  exact hdigit

/-- Pointwise selected-word formula on the full nonterminating state set. -/
theorem gaussDigitAt_eq_positiveDigitWordDigit_selected
    {b n : ℕ} (hn : n < b) {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0) :
    gaussDigitAt n x =
      positiveDigitWordDigit n hn (selectedGaussPrefixWord b x) := by
  have hxDomain : x ∈ positivePrefixDomain b :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  exact gaussDigitAt_eq_positiveDigitWordDigit_of_mem hn
    (selectedGaussPrefixWord b x) ⟨hxUnit.1.le, hxUnit.2⟩
    (selectedGaussPrefixWord_mem hxDomain)

/-! ## A selected-word realization of one-digit orbit events -/

/-- The depth-`b` selected-word event saying that its digit at time `n`
belongs to `digits`. -/
def gaussPrefixSelectedDigitEvent
    (b n : ℕ) (hn : n < b) (digits : Set ℕ) : Set ℝ :=
  (selectedGaussPrefixWord b) ⁻¹'
    {w : PositiveDigitWord b | positiveDigitWordDigit n hn w ∈ digits}

theorem measurableSet_gaussPrefixSelectedDigitEvent
    (b n : ℕ) (hn : n < b) (digits : Set ℕ) :
    @MeasurableSet ℝ (gaussPrefixMeasurableSpace b)
      (gaussPrefixSelectedDigitEvent b n hn digits) := by
  letI : MeasurableSpace (PositiveDigitWord b) := ⊤
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{w : PositiveDigitWord b |
      positiveDigitWordDigit n hn w ∈ digits}, ?_, rfl⟩
  exact MeasurableSet.of_discrete

/-- Every one-digit event pulled back to time `n<b` agrees almost
everywhere with its selected-word realization at depth `b`. -/
theorem gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixSelected
    {A : Set ℝ} (hA : IsGaussOneDigitEvent A)
    {b n : ℕ} (hn : n < b) :
    (gaussOrbit n) ⁻¹' A =ᵐ[gaussMeasure]
      gaussPrefixSelectedDigitEvent b n hn
        (Classical.choose hA) := by
  let digits : Set ℕ := Classical.choose hA
  have hAeq :
      A = Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits :=
    Classical.choose_spec hA
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  have horbit : gaussOrbit n x ∈ Ioc (0 : ℝ) 1 := by
    exact gaussOrbit_mem_Ioc_of_not_mem_exceptional
      ⟨hx.1.1, hx.1.2.le⟩
      (not_mem_gaussPrefixExceptional_of_nonterminating
        hx.1 hx.2 (n + 1))
      (by omega)
  have hdigit :
      gaussFirstDigitNat (gaussOrbit n x) =
        positiveDigitWordDigit n hn
          (selectedGaussPrefixWord b x) := by
    change gaussDigitAt n x =
      positiveDigitWordDigit n hn (selectedGaussPrefixWord b x)
    exact gaussDigitAt_eq_positiveDigitWordDigit_selected hn hx.1 hx.2
  change
    (gaussOrbit n x ∈ A) =
      (positiveDigitWordDigit n hn
        (selectedGaussPrefixWord b x) ∈ digits)
  rw [hAeq]
  simp only [mem_inter_iff, mem_preimage, horbit, true_and, hdigit]

/-! ## Finite intersections -/

/-- Selected-word realization of a finite tuple of one-digit orbit events,
all lying strictly before the depth-`b` cutoff. -/
def gaussPrefixSelectedOneDigitTupleEvent
    {r : ℕ} (b : ℕ) (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i)) : Set ℝ :=
  ⋂ i, gaussPrefixSelectedDigitEvent b (times i) (htimes i)
    (Classical.choose (hOne i))

theorem measurableSet_gaussPrefixSelectedOneDigitTupleEvent
    {r : ℕ} (b : ℕ) (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i)) :
    @MeasurableSet ℝ (gaussPrefixMeasurableSpace b)
      (gaussPrefixSelectedOneDigitTupleEvent
        b times htimes events hOne) := by
  unfold gaussPrefixSelectedOneDigitTupleEvent
  exact MeasurableSet.iInter fun i ↦
    measurableSet_gaussPrefixSelectedDigitEvent
      b (times i) (htimes i) (Classical.choose (hOne i))

/-- A finite intersection of one-digit events before `b` agrees almost
everywhere with its genuinely depth-`b` prefix-measurable realization. -/
theorem iInter_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
    {r : ℕ} {b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i)) :
    (⋂ i, (gaussOrbit (times i)) ⁻¹' events i) =ᵐ[gaussMeasure]
      gaussPrefixSelectedOneDigitTupleEvent
        b times htimes events hOne := by
  unfold gaussPrefixSelectedOneDigitTupleEvent
  exact Filter.EventuallyEq.iInter fun i ↦
    gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixSelected
      (hOne i) (htimes i)

/-- The same bridge in the ordered-list convention used by the factorial
tuple modules. -/
theorem orderedIntersection_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
    {r : ℕ} {b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i)) :
    orderedEventIntersection
        (List.ofFn fun i ↦ (gaussOrbit (times i)) ⁻¹' events i)
      =ᵐ[gaussMeasure]
      gaussPrefixSelectedOneDigitTupleEvent
        b times htimes events hOne := by
  rw [orderedEventIntersection_ofFn]
  exact iInter_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
    times htimes events hOne

/-- Convenient endpoint form: events at times `≤ b` are determined by the
selected word of length `b+1`. -/
theorem iInter_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple_succ
    {r b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i, times i ≤ b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i)) :
    (⋂ i, (gaussOrbit (times i)) ⁻¹' events i) =ᵐ[gaussMeasure]
      gaussPrefixSelectedOneDigitTupleEvent
        (b + 1) times
          (fun i ↦ Nat.lt_succ_of_le (htimes i)) events hOne := by
  exact iInter_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
    times (fun i ↦ Nat.lt_succ_of_le (htimes i)) events hOne

/-- Almost-everywhere equality remains valid after intersection with an
arbitrary event, in particular with a complete future digit block. -/
theorem iInter_gaussOrbit_preimage_oneDigitEvent_inter_ae_eq_prefixTuple
    {r : ℕ} {b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i))
    (future : Set ℝ) :
    Filter.EventuallyEq (ae gaussMeasure)
      (Set.inter
        (⋂ i, (gaussOrbit (times i)) ⁻¹' events i) future)
      (Set.inter
        (gaussPrefixSelectedOneDigitTupleEvent
          b times htimes events hOne) future) := by
  exact
    (iInter_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
      times htimes events hOne).inter
        (Filter.EventuallyEq.refl (ae gaussMeasure) future)

/-- Consequently the raw and selected-word joint events have exactly the
same Gauss measure, with no measurability requirement on the extra factor. -/
theorem gaussMeasure_iInter_gaussOrbit_preimage_oneDigitEvent_inter_eq_prefixTuple
    {r : ℕ} {b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i))
    (future : Set ℝ) :
    gaussMeasure
        ((⋂ i, (gaussOrbit (times i)) ⁻¹' events i) ∩ future) =
      gaussMeasure
        (gaussPrefixSelectedOneDigitTupleEvent
          b times htimes events hOne ∩ future) :=
  (iInter_gaussOrbit_preimage_oneDigitEvent_inter_ae_eq_prefixTuple
    times htimes events hOne future).measure_eq

/-- Real-valued measure form of the same exact transfer. -/
theorem gaussMeasure_real_iInter_gaussOrbit_preimage_oneDigitEvent_inter_eq_prefixTuple
    {r : ℕ} {b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i, IsGaussOneDigitEvent (events i))
    (future : Set ℝ) :
    gaussMeasure.real
        ((⋂ i, (gaussOrbit (times i)) ⁻¹' events i) ∩ future) =
      gaussMeasure.real
        (gaussPrefixSelectedOneDigitTupleEvent
          b times htimes events hOne ∩ future) := by
  simpa only [measureReal_def] using! congrArg ENNReal.toReal
    (gaussMeasure_iInter_gaussOrbit_preimage_oneDigitEvent_inter_eq_prefixTuple
      times htimes events hOne future)

/-! ## Masked tuples, with literal `univ` outside the prefix block -/

/-- Selected-word realization of a masked tuple.  Coordinates outside
`prefixIndices` impose no condition at all. -/
def gaussPrefixSelectedMaskedOneDigitTupleEvent
    {r : ℕ} (prefixIndices : Finset (Fin r))
    (b : ℕ) (times : Fin r → ℕ)
    (htimes : ∀ i ∈ prefixIndices, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i ∈ prefixIndices,
      IsGaussOneDigitEvent (events i)) : Set ℝ :=
  ⋂ i, if hi : i ∈ prefixIndices then
    gaussPrefixSelectedDigitEvent b (times i) (htimes i hi)
      (Classical.choose (hOne i hi))
  else Set.univ

theorem measurableSet_gaussPrefixSelectedMaskedOneDigitTupleEvent
    {r : ℕ} (prefixIndices : Finset (Fin r))
    (b : ℕ) (times : Fin r → ℕ)
    (htimes : ∀ i ∈ prefixIndices, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i ∈ prefixIndices,
      IsGaussOneDigitEvent (events i)) :
    @MeasurableSet ℝ (gaussPrefixMeasurableSpace b)
      (gaussPrefixSelectedMaskedOneDigitTupleEvent
        prefixIndices b times htimes events hOne) := by
  unfold gaussPrefixSelectedMaskedOneDigitTupleEvent
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ prefixIndices
  · rw [dif_pos hi]
    exact measurableSet_gaussPrefixSelectedDigitEvent
      b (times i) (htimes i hi) (Classical.choose (hOne i hi))
  · rw [dif_neg hi]
    exact MeasurableSet.univ

/-- The raw masked tuple (one-digit events on the prefix indices, literal
`univ` elsewhere) is almost everywhere the selected-word event. -/
theorem iInter_masked_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
    {r : ℕ} (prefixIndices : Finset (Fin r))
    {b : ℕ} (times : Fin r → ℕ)
    (htimes : ∀ i ∈ prefixIndices, times i < b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i ∈ prefixIndices,
      IsGaussOneDigitEvent (events i)) :
    (⋂ i, if i ∈ prefixIndices then
        (gaussOrbit (times i)) ⁻¹' events i
      else Set.univ) =ᵐ[gaussMeasure]
      gaussPrefixSelectedMaskedOneDigitTupleEvent
        prefixIndices b times htimes events hOne := by
  unfold gaussPrefixSelectedMaskedOneDigitTupleEvent
  apply Filter.EventuallyEq.iInter
  intro i
  by_cases hi : i ∈ prefixIndices
  · simp only [hi, if_pos, dif_pos]
    exact gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixSelected
      (hOne i hi) (htimes i hi)
  · simp [hi]

/-- Endpoint form for a masked tuple whose active times are at most `b`. -/
theorem iInter_masked_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple_succ
    {r b : ℕ} (prefixIndices : Finset (Fin r))
    (times : Fin r → ℕ)
    (htimes : ∀ i ∈ prefixIndices, times i ≤ b)
    (events : Fin r → Set ℝ)
    (hOne : ∀ i ∈ prefixIndices,
      IsGaussOneDigitEvent (events i)) :
    (⋂ i, if i ∈ prefixIndices then
        (gaussOrbit (times i)) ⁻¹' events i
      else Set.univ) =ᵐ[gaussMeasure]
      gaussPrefixSelectedMaskedOneDigitTupleEvent
        prefixIndices (b + 1) times
          (fun i hi ↦ Nat.lt_succ_of_le (htimes i hi))
          events hOne := by
  exact
    iInter_masked_gaussOrbit_preimage_oneDigitEvent_ae_eq_prefixTuple
      prefixIndices times
        (fun i hi ↦ Nat.lt_succ_of_le (htimes i hi)) events hOne

end

end Erdos1002
