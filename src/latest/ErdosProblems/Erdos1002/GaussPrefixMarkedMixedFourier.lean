import ErdosProblems.Erdos1002.GaussPrefixMarkedFourierVanishing
import ErdosProblems.Erdos1002.ChronologicalShortTupleCounting
import ErdosProblems.Erdos1002.PsiMixing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Literal mixed Fourier coefficients of the marked Gauss-prefix process

This module fixes the exact finite object whose nonzero torus Fourier modes
have to vanish in the marked-Poisson argument.  The definition is made
directly from `gaussPrefixMarkedEvent`; no abstract point process and no
equidistribution hypothesis occurs.

For a labeled falling-factorial order `k`, a tuple index consists of one
embedding into the finite depth set for every label.  Repetitions between
different labels are deliberately retained, exactly as in
`mixedDescFactorial`; when the labeled mark sets are disjoint their
simultaneous event is empty.  Each selected depth carries its literal torus
character.

Two exact bridges are proved below.

* At the zero Fourier mode the coefficient is the complexification of the
  mixed factorial moment of `gaussPrefixMarkedCountVectorLaw`.
* On the nonterminating full-measure set, a simultaneous tuple character is
  one ordinary phase `oscillatoryPhase (N * D) x`, where `D` is the signed
  integer combination of the terminal denominators.  This is the carrier
  to which the deterministic cylinder-sum estimate applies.

The last section proves the finite-family aggregate form of functional
`psi`-mixing.  It keeps the absolute value outside the complete double sum,
which is the quantifier placement needed in the late-prefix argument.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

local instance gaussPrefixMarkedMixedFourierPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

open MultivariateFactorialMomentMethod

/-! ## One literal marked depth character -/

/-- Data belonging to the unique selected positive prefix on a marked event. -/
theorem selectedGaussPrefixWord_data_of_mem
    {N n : ℕ} {B : Set (ℝ × ℝ × ℝ)} {x : ℝ}
    (hx : x ∈ gaussPrefixMarkedEvent N B n) :
    x ∈ positivePrefixCylinder n (selectedGaussPrefixWord n x) ∧
      cfTerminalDenominator (selectedGaussPrefixWord n x).1 ≤ N ∧
      gaussApproximationCoordinate n x < (1 : ℝ) / 2 ∧
      gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x ∈ B := by
  obtain ⟨w, hw, hden, htheta, hpoint⟩ :=
    mem_gaussPrefixMarkedEvent_iff.mp hx
  have hselected : selectedGaussPrefixWord n x = w :=
    selectedGaussPrefixWord_eq_of_mem w hw
  simpa only [hselected] using! And.intro hw ⟨hden, htheta, hpoint⟩

/-- Exact fibre description of the selected prefix.  Off the prefix domain
the definition uses the canonical default word; on the domain the half-open
cylinder partition makes the selected word unique. -/
theorem selectedGaussPrefixWord_eq_iff
    {n : ℕ} {x : ℝ} (w : PositiveDigitWord n) :
    selectedGaussPrefixWord n x = w ↔
      x ∈ positivePrefixCylinder n w ∨
        (x ∉ positivePrefixDomain n ∧ w = defaultPositiveDigitWord n) := by
  by_cases hdomain : x ∈ positivePrefixDomain n
  · constructor
    · intro hselected
      left
      rw [← hselected]
      exact selectedGaussPrefixWord_mem hdomain
    · rintro (hw | hoff)
      · exact selectedGaussPrefixWord_eq_of_mem w hw
      · exact (hoff.1 hdomain).elim
  · have hnotCylinder : x ∉ positivePrefixCylinder n w := by
      intro hw
      apply hdomain
      exact Set.mem_iUnion.mpr ⟨w, hw⟩
    rw [selectedGaussPrefixWord, dif_neg hdomain]
    constructor
    · intro hdefault
      exact Or.inr ⟨hdomain, hdefault.symm⟩
    · rintro (hw | hoff)
      · exact (hnotCylinder hw).elim
      · exact hoff.2.symm

/-- The selected prefix word is measurable when the countable word space is
given its discrete sigma-algebra. -/
theorem measurable_selectedGaussPrefixWord (n : ℕ) :
    @Measurable ℝ (PositiveDigitWord n) inferInstance ⊤
      (selectedGaussPrefixWord n) := by
  let : MeasurableSpace (PositiveDigitWord n) := ⊤
  apply measurable_to_countable
  intro y
  let w : PositiveDigitWord n := selectedGaussPrefixWord n y
  have hpreimage :
      (selectedGaussPrefixWord n) ⁻¹' {w} =
        positivePrefixCylinder n w ∪
          if w = defaultPositiveDigitWord n then
            (positivePrefixDomain n)ᶜ else ∅ := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff,
      selectedGaussPrefixWord_eq_iff]
    by_cases hw : w = defaultPositiveDigitWord n
    · simp [hw]
    · simp [hw]
  rw [hpreimage]
  apply MeasurableSet.union (measurableSet_positivePrefixCylinder n w)
  by_cases hw : w = defaultPositiveDigitWord n
  · rw [if_pos hw]
    exact (measurableSet_positivePrefixDomain n).compl
  · rw [if_neg hw]
    exact MeasurableSet.empty

/-- The actual torus character attached to one marked Gauss-prefix event.
It is zero off the event. -/
def gaussPrefixMarkedDepthCharacter
    (N : ℕ) (B : Set (ℝ × ℝ × ℝ)) (n : ℕ) (h : ℤ)
    (x : ℝ) : ℂ :=
  if x ∈ gaussPrefixMarkedEvent N B n then
    paperExp ((h : ℝ) *
      (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.2)
  else 0

/-- Measurability of the literal marked depth character.  The proof does
not treat the choice of a prefix word as opaque: it uses the measurable
fibres of the countable half-open cylinder partition above. -/
theorem measurable_gaussPrefixMarkedDepthCharacter
    (N n : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) (h : ℤ) :
    Measurable (gaussPrefixMarkedDepthCharacter N B n h) := by
  let : MeasurableSpace (PositiveDigitWord n) := ⊤
  have hselected : Measurable (selectedGaussPrefixWord n) :=
    measurable_selectedGaussPrefixWord n
  let G : PositiveDigitWord n × ℝ → ℂ := fun z ↦
    paperExp ((h : ℝ) * (gaussPrefixMarkedPoint N n z.1 z.2).2.2)
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro w
    dsimp [G]
    have hpoint : Measurable
        (fun x ↦ (gaussPrefixMarkedPoint N n w x).2.2) :=
      (measurable_gaussPrefixMarkedPoint N n w).snd.snd
    unfold paperExp
    fun_prop
  have hchosen : Measurable (fun x ↦
      paperExp ((h : ℝ) *
        (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.2)) := by
    change Measurable
      (G ∘ fun x : ℝ ↦ (selectedGaussPrefixWord n x, x))
    exact hG.comp (hselected.prodMk measurable_id)
  unfold gaussPrefixMarkedDepthCharacter
  exact Measurable.ite (measurableSet_gaussPrefixMarkedEvent N n hB)
    hchosen measurable_const

@[simp] theorem gaussPrefixMarkedDepthCharacter_zero
    (N : ℕ) (B : Set (ℝ × ℝ × ℝ)) (n : ℕ) (x : ℝ) :
    gaussPrefixMarkedDepthCharacter N B n 0 x =
      if x ∈ gaussPrefixMarkedEvent N B n then 1 else 0 := by
  unfold gaussPrefixMarkedDepthCharacter
  by_cases hx : x ∈ gaussPrefixMarkedEvent N B n
  · simp [hx, paperExp]
  · simp [hx]

theorem norm_gaussPrefixMarkedDepthCharacter
    (N : ℕ) (B : Set (ℝ × ℝ × ℝ)) (n : ℕ) (h : ℤ) (x : ℝ) :
    ‖gaussPrefixMarkedDepthCharacter N B n h x‖ =
      if x ∈ gaussPrefixMarkedEvent N B n then 1 else 0 := by
  unfold gaussPrefixMarkedDepthCharacter
  by_cases hx : x ∈ gaussPrefixMarkedEvent N B n
  · simp only [if_pos hx]
    unfold paperExp
    rw [Complex.norm_exp]
    simp
  · simp [hx]

/-- The literal depth character is integrable under every finite measure. -/
theorem integrable_gaussPrefixMarkedDepthCharacter
    (N n : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B)
    (h : ℤ) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Integrable (gaussPrefixMarkedDepthCharacter N B n h) mu := by
  apply Integrable.of_bound
    (measurable_gaussPrefixMarkedDepthCharacter N n hB h).aestronglyMeasurable 1
  filter_upwards with x
  rw [norm_gaussPrefixMarkedDepthCharacter]
  split <;> norm_num

/-- On the full-measure nonterminating set, the literal torus character of
one marked prefix is precisely the ordinary affine carrier with frequency
`N * h * Q_n`. -/
theorem gaussPrefixMarkedDepthCharacter_eq_oscillatoryPhase
    {N n : ℕ} {B : Set (ℝ × ℝ × ℝ)} {h : ℤ} {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ m : ℕ, (gaussMap^[m]) x ≠ 0)
    (hxEvent : x ∈ gaussPrefixMarkedEvent N B n) :
    gaussPrefixMarkedDepthCharacter N B n h x =
      oscillatoryPhase
        ((N : ℝ) * (h : ℝ) *
          (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ)) x := by
  have hdata := selectedGaussPrefixWord_data_of_mem hxEvent
  let w : PositiveDigitWord n := selectedGaussPrefixWord n x
  have hw : x ∈ positivePrefixCylinder n w := hdata.1
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hxUnit hxNonterm (n + 1)
  have hpoint :=
    markedResonancePoint_terminalDenominator_eq_gaussPrefixMarkedPoint
      (N := N) w hxUnit hex hw hdata.2.2.1
  have htorus :
      (gaussPrefixMarkedPoint N n w x).2.2 =
        resonanceTorusCoordinate N (cfTerminalDenominator w.1) x := by
    exact (congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.2) hpoint).symm
  rw [gaussPrefixMarkedDepthCharacter, if_pos hxEvent]
  change paperExp ((h : ℝ) * (gaussPrefixMarkedPoint N n w x).2.2) = _
  rw [htorus, paperExp_mul_resonanceTorusCoordinate,
    paperExp_scaledMarkedCell_eq_oscillatoryPhase]
  congr 2
  ring

/-! ## Literal labeled mixed factorial Fourier coefficient -/

variable {ι : Type*} [Fintype ι]

/-- A family of internally distinct depth tuples, one for every label. -/
abbrev GaussPrefixMixedDepthTuple (N : ℕ) (k : ι → ℕ) :=
  ∀ i, Fin (k i) ↪ (Finset.Icc 0 N : Finset ℕ)

/-- Product of all literal depth characters in one labeled tuple. -/
def gaussPrefixMarkedMixedTupleCharacter
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (x : ℝ) : ℂ :=
  ∏ i, ∏ j,
    gaussPrefixMarkedDepthCharacter N (B i) (F i j) (h i j) x

theorem measurable_gaussPrefixMarkedMixedTupleCharacter
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) :
    Measurable (gaussPrefixMarkedMixedTupleCharacter N B k h F) := by
  unfold gaussPrefixMarkedMixedTupleCharacter
  apply Finset.measurable_fun_prod
  intro i _hi
  apply Finset.measurable_fun_prod
  intro j _hj
  exact measurable_gaussPrefixMarkedDepthCharacter N (F i j) (hB i) (h i j)

theorem norm_gaussPrefixMarkedMixedTupleCharacter_le_one
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (x : ℝ) :
    ‖gaussPrefixMarkedMixedTupleCharacter N B k h F x‖ ≤ 1 := by
  classical
  unfold gaussPrefixMarkedMixedTupleCharacter
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro i _hi
    exact norm_nonneg _
  · intro i _hi
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro j _hj
      exact norm_nonneg _
    · intro j _hj
      rw [norm_gaussPrefixMarkedDepthCharacter]
      split <;> norm_num

theorem integrable_gaussPrefixMarkedMixedTupleCharacter
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Integrable (gaussPrefixMarkedMixedTupleCharacter N B k h F) mu := by
  apply Integrable.of_bound
    (measurable_gaussPrefixMarkedMixedTupleCharacter N hB k h F).aestronglyMeasurable
    1
  exact Eventually.of_forall fun x ↦
    norm_gaussPrefixMarkedMixedTupleCharacter_le_one N B k h F x

/-- Pointwise mixed Fourier statistic before expectation. -/
def gaussPrefixMarkedMixedFourierStatistic
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (x : ℝ) : ℂ :=
  ∑ F : GaussPrefixMixedDepthTuple N k,
    gaussPrefixMarkedMixedTupleCharacter N B k h F x

/-- The finite mixed factorial Fourier coefficient of the actual marked
Gauss-prefix process. -/
def gaussPrefixMarkedMixedFourierCoefficient
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) : ℂ :=
  ∑ F : GaussPrefixMixedDepthTuple N k,
    ∫ x, gaussPrefixMarkedMixedTupleCharacter N B k h F x
      ∂uniform01Measure

/-- The coefficient is the expectation of the literal finite statistic. -/
theorem gaussPrefixMarkedMixedFourierCoefficient_eq_integral
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) :
    gaussPrefixMarkedMixedFourierCoefficient N B k h =
      ∫ x, gaussPrefixMarkedMixedFourierStatistic N B k h x
        ∂uniform01Measure := by
  unfold gaussPrefixMarkedMixedFourierCoefficient
  unfold gaussPrefixMarkedMixedFourierStatistic
  rw [MeasureTheory.integral_finset_sum]
  intro F _hF
  exact integrable_gaussPrefixMarkedMixedTupleCharacter
    N hB k h F uniform01Measure

/-- The depth-indexed count is literally a `finiteEventCount`. -/
theorem gaussPrefixMarkedCount_eq_finiteEventCount
    (N : ℕ) (B : Set (ℝ × ℝ × ℝ)) (x : ℝ) :
    gaussPrefixMarkedCount N B x =
      finiteEventCount (Finset.Icc 0 N)
        (gaussPrefixMarkedEvent N B) x := by
  rfl

/-- At zero mode one tuple character is exactly the complex indicator of
its simultaneous mixed tuple event. -/
theorem gaussPrefixMarkedMixedTupleCharacter_zero
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N B k (fun _ _ ↦ 0) F x =
      (mixedTupleEvent (fun i ↦ gaussPrefixMarkedEvent N (B i)) F).indicator
        (fun _ ↦ (1 : ℂ)) x := by
  classical
  unfold gaussPrefixMarkedMixedTupleCharacter
  by_cases hall : ∀ i j,
      x ∈ gaussPrefixMarkedEvent N (B i) (F i j)
  · have hmixed :
        x ∈ mixedTupleEvent (fun i ↦ gaussPrefixMarkedEvent N (B i)) F := by
      exact Set.mem_iInter.mpr fun i ↦ Set.mem_iInter.mpr (hall i)
    rw [Set.indicator_of_mem hmixed]
    apply Finset.prod_eq_one
    intro i _hi
    apply Finset.prod_eq_one
    intro j _hj
    rw [gaussPrefixMarkedDepthCharacter_zero, if_pos (hall i j)]
  · have hmixed :
        x ∉ mixedTupleEvent (fun i ↦ gaussPrefixMarkedEvent N (B i)) F := by
      simpa only [mixedTupleEvent, tupleEvent, Set.mem_iInter] using! hall
    rw [Set.indicator_of_notMem hmixed]
    push_neg at hall
    obtain ⟨i, j, hj⟩ := hall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [gaussPrefixMarkedDepthCharacter_zero, if_neg hj]

/-- Mixed factorial moments of the Gauss-prefix count-vector law are the
corresponding Lebesgue integrals. -/
theorem mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ) :
    mixedFactorialMoment (gaussPrefixMarkedCountVectorLaw N B hB) k =
      ∫ x, mixedDescFactorial k (gaussPrefixMarkedCountVector N B x)
        ∂uniform01Measure := by
  unfold mixedFactorialMoment gaussPrefixMarkedCountVectorLaw uniform01
  change ∫ y, mixedDescFactorial k y
      ∂Measure.map (gaussPrefixMarkedCountVector N B) uniform01Measure = _
  exact integral_map
    (measurable_gaussPrefixMarkedCountVector N hB).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Exact zero-mode identity: the mixed Fourier coefficient is not merely
asymptotic to a factorial moment; it is its literal complexification. -/
theorem gaussPrefixMarkedMixedFourierCoefficient_zero
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ) :
    gaussPrefixMarkedMixedFourierCoefficient N B k (fun _ _ ↦ 0) =
      (mixedFactorialMoment (gaussPrefixMarkedCountVectorLaw N B hB) k : ℂ) := by
  classical
  let E : ι → ℕ → Set ℝ := fun i ↦ gaussPrefixMarkedEvent N (B i)
  have hE : ∀ (i : ι) (q : ℕ), q ∈ Finset.Icc 0 N →
      MeasurableSet (E i q) := by
    intro i q _hq
    exact measurableSet_gaussPrefixMarkedEvent N q (hB i)
  have hfac := integral_mixedDescFactorial_finiteEventCount
    (Finset.Icc 0 N) E k uniform01Measure hE
  rw [gaussPrefixMarkedMixedFourierCoefficient]
  calc
    (∑ F : GaussPrefixMixedDepthTuple N k,
        ∫ x, gaussPrefixMarkedMixedTupleCharacter N B k
          (fun _ _ ↦ 0) F x ∂uniform01Measure) =
        ∑ F : GaussPrefixMixedDepthTuple N k,
          (uniform01Measure.real (mixedTupleEvent E F) : ℂ) := by
      apply Finset.sum_congr rfl
      intro F _hF
      rw [show gaussPrefixMarkedMixedTupleCharacter N B k
          (fun _ _ ↦ 0) F =
          (mixedTupleEvent E F).indicator (fun _ ↦ (1 : ℂ)) by
        funext x
        exact gaussPrefixMarkedMixedTupleCharacter_zero N B k F x]
      rw [MeasureTheory.integral_indicator_const (1 : ℂ)
        (measurableSet_mixedTupleEvent hE F)]
      simp
    _ = ((∑ F : GaussPrefixMixedDepthTuple N k,
          uniform01Measure.real (mixedTupleEvent E F) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
    _ = ((∫ x, mixedDescFactorial k
          (fun i ↦ finiteEventCount (Finset.Icc 0 N) (E i) x)
            ∂uniform01Measure : ℝ) : ℂ) := by
      rw [hfac]
    _ = (mixedFactorialMoment
          (gaussPrefixMarkedCountVectorLaw N B hB) k : ℂ) := by
      rw [mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw]
      congr 2

/-! ## Exact reduction of a simultaneous tuple to one carrier -/

/-- Signed terminal-denominator carrier of one labeled depth tuple. -/
def gaussPrefixMarkedMixedCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (x : ℝ) : ℝ :=
  ∑ i, ∑ j,
    (h i j : ℝ) *
      (cfTerminalDenominator
        (selectedGaussPrefixWord (F i j) x).1 : ℝ)

private theorem oscillatoryPhase_add (K M x : ℝ) :
    oscillatoryPhase (K + M) x =
      oscillatoryPhase K x * oscillatoryPhase M x := by
  unfold oscillatoryPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem prod_oscillatoryPhase_eq_sum
    {α : Type*} [Fintype α] (K : α → ℝ) (x : ℝ) :
    ∏ a, oscillatoryPhase (K a) x =
      oscillatoryPhase (∑ a, K a) x := by
  classical
  have hfinite (s : Finset α) :
      (∏ a ∈ s, oscillatoryPhase (K a) x) =
        oscillatoryPhase (∑ a ∈ s, K a) x := by
    induction s using Finset.induction_on with
    | empty => simp [oscillatoryPhase]
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
          ← oscillatoryPhase_add]
  simpa using! hfinite (Finset.univ : Finset α)

/-- If every component event occurs, the product of the literal torus
characters is exactly one affine phase with the summed carrier. -/
theorem gaussPrefixMarkedMixedTupleCharacter_eq_oscillatoryPhase
    {N : ℕ} {B : ι → Set (ℝ × ℝ × ℝ)} {k : ι → ℕ}
    {h : ∀ i, Fin (k i) → ℤ}
    {F : GaussPrefixMixedDepthTuple N k} {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ m : ℕ, (gaussMap^[m]) x ≠ 0)
    (hxEvents : ∀ i j,
      x ∈ gaussPrefixMarkedEvent N (B i) (F i j)) :
    gaussPrefixMarkedMixedTupleCharacter N B k h F x =
      oscillatoryPhase
        ((N : ℝ) * gaussPrefixMarkedMixedCarrier N k h F x) x := by
  classical
  unfold gaussPrefixMarkedMixedTupleCharacter
  have hone (i : ι) (j : Fin (k i)) :
      gaussPrefixMarkedDepthCharacter N (B i) (F i j) (h i j) x =
        oscillatoryPhase
          ((N : ℝ) * ((h i j : ℝ) *
            (cfTerminalDenominator
              (selectedGaussPrefixWord (F i j) x).1 : ℝ))) x := by
    simpa only [mul_assoc] using!
      (gaussPrefixMarkedDepthCharacter_eq_oscillatoryPhase
        hxUnit hxNonterm (hxEvents i j))
  simp_rw [hone]
  let K : (i : ι) → Fin (k i) → ℝ := fun i j ↦
    (N : ℝ) * ((h i j : ℝ) *
      (cfTerminalDenominator
        (selectedGaussPrefixWord (F i j) x).1 : ℝ))
  calc
    (∏ i, ∏ j, oscillatoryPhase (K i j) x) =
        ∏ i, oscillatoryPhase (∑ j, K i j) x := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact prod_oscillatoryPhase_eq_sum (K i) x
    _ = oscillatoryPhase (∑ i, ∑ j, K i j) x :=
      prod_oscillatoryPhase_eq_sum (fun i ↦ ∑ j, K i j) x
    _ = oscillatoryPhase
        ((N : ℝ) * gaussPrefixMarkedMixedCarrier N k h F x) x := by
      congr 2
      unfold K gaussPrefixMarkedMixedCarrier
      simp_rw [Finset.mul_sum]

/-! ## Aggregate prefix-freezing estimate -/

/-- The complex prefix term before or after freezing. -/
def oscillatoryWindowProduct {r : ℕ}
    (a b coordinate : Fin r → ℝ) (K location : ℝ) : ℂ :=
  oscillatoryPhase K location *
    (closedIntervalIndicatorProduct a b coordinate : ℂ)

/-- The complete nonnegative pointwise error envelope from the prefix
freezing lemma. -/
def oscillatoryPrefixFreezingEnvelope {r : ℕ}
    (a b coordinate : Fin r → ℝ)
    (K phaseRadius eta : ℝ) : ℝ :=
  (2 * Real.pi * |K| * phaseRadius) *
      closedIntervalIndicatorProduct
        (fun i ↦ a i - eta) (fun i ↦ b i + eta) coordinate +
    ∑ i,
      closedIntervalBoundaryIndicator (a i) (b i) eta (coordinate i) *
        ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
          closedIntervalIndicator (a j - eta) (b j + eta) (coordinate j)

/-- Pointwise specialization written with the two prefix functions and the
named envelope used in aggregate estimates. -/
theorem norm_oscillatoryWindowProduct_sub_le_freezingEnvelope
    {r : ℕ} (a b coordinate frozenCoordinate : Fin r → ℝ)
    (K alpha representative : ℝ) {phaseRadius eta : ℝ}
    (hphaseRadius : 0 ≤ phaseRadius) (heta : 0 ≤ eta)
    (halpha : |alpha - representative| ≤ phaseRadius)
    (hcoordinate : ∀ i,
      |coordinate i - frozenCoordinate i| ≤ eta) :
    ‖oscillatoryWindowProduct a b coordinate K alpha -
        oscillatoryWindowProduct a b frozenCoordinate K representative‖ ≤
      oscillatoryPrefixFreezingEnvelope
        a b coordinate K phaseRadius eta := by
  exact norm_oscillatoryPhase_mul_intervalProducts_sub_le_freezingError
    a b coordinate frozenCoordinate K alpha representative
      hphaseRadius heta halpha hcoordinate

/-- Summed integrated freezing estimate.  The norm remains inside the
integral and the sum, so this proves the absolute summability required before
the late-prefix covariance argument. -/
theorem sum_integral_norm_oscillatoryWindowProduct_sub_le
    {Ω U : Type*} [MeasurableSpace Ω] [Fintype U]
    (mu : Measure Ω) {r : ℕ}
    (a b : U → Fin r → ℝ)
    (coordinate frozenCoordinate : U → Ω → Fin r → ℝ)
    (K phaseRadius eta : U → ℝ)
    (alpha representative : U → Ω → ℝ)
    (hphaseRadius : ∀ u, 0 ≤ phaseRadius u)
    (heta : ∀ u, 0 ≤ eta u)
    (halpha : ∀ u ω,
      |alpha u ω - representative u ω| ≤ phaseRadius u)
    (hcoordinate : ∀ u ω i,
      |coordinate u ω i - frozenCoordinate u ω i| ≤ eta u)
    (hactual : ∀ u, Integrable (fun ω ↦
      oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
        (K u) (alpha u ω)) mu)
    (hfrozen : ∀ u, Integrable (fun ω ↦
      oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
        (K u) (representative u ω)) mu)
    (henvelope : ∀ u, Integrable (fun ω ↦
      oscillatoryPrefixFreezingEnvelope (a u) (b u) (coordinate u ω)
        (K u) (phaseRadius u) (eta u)) mu) :
    (∑ u, ∫ ω,
      ‖oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
          (K u) (alpha u ω) -
        oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
          (K u) (representative u ω)‖ ∂mu) ≤
      ∑ u, ∫ ω,
        oscillatoryPrefixFreezingEnvelope (a u) (b u) (coordinate u ω)
          (K u) (phaseRadius u) (eta u) ∂mu := by
  apply Finset.sum_le_sum
  intro u _hu
  apply integral_mono ((hactual u).sub (hfrozen u)).norm (henvelope u)
  intro ω
  exact norm_oscillatoryWindowProduct_sub_le_freezingEnvelope
    (a u) (b u) (coordinate u ω) (frozenCoordinate u ω)
    (K u) (alpha u ω) (representative u ω)
    (hphaseRadius u) (heta u) (halpha u ω) (hcoordinate u ω)

/-- The same aggregate estimate with the norm outside the complete finite
sum of integrals. -/
theorem norm_sum_integral_oscillatoryWindowProduct_sub_le
    {Ω U : Type*} [MeasurableSpace Ω] [Fintype U]
    (mu : Measure Ω) {r : ℕ}
    (a b : U → Fin r → ℝ)
    (coordinate frozenCoordinate : U → Ω → Fin r → ℝ)
    (K phaseRadius eta : U → ℝ)
    (alpha representative : U → Ω → ℝ)
    (hphaseRadius : ∀ u, 0 ≤ phaseRadius u)
    (heta : ∀ u, 0 ≤ eta u)
    (halpha : ∀ u ω,
      |alpha u ω - representative u ω| ≤ phaseRadius u)
    (hcoordinate : ∀ u ω i,
      |coordinate u ω i - frozenCoordinate u ω i| ≤ eta u)
    (hactual : ∀ u, Integrable (fun ω ↦
      oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
        (K u) (alpha u ω)) mu)
    (hfrozen : ∀ u, Integrable (fun ω ↦
      oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
        (K u) (representative u ω)) mu)
    (henvelope : ∀ u, Integrable (fun ω ↦
      oscillatoryPrefixFreezingEnvelope (a u) (b u) (coordinate u ω)
        (K u) (phaseRadius u) (eta u)) mu) :
    ‖∑ u, ∫ ω,
        (oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
            (K u) (alpha u ω) -
          oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
            (K u) (representative u ω)) ∂mu‖ ≤
      ∑ u, ∫ ω,
        oscillatoryPrefixFreezingEnvelope (a u) (b u) (coordinate u ω)
          (K u) (phaseRadius u) (eta u) ∂mu := by
  calc
    ‖∑ u, ∫ ω,
        (oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
            (K u) (alpha u ω) -
          oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
            (K u) (representative u ω)) ∂mu‖ ≤
        ∑ u, ‖∫ ω,
          (oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
              (K u) (alpha u ω) -
            oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
              (K u) (representative u ω)) ∂mu‖ := norm_sum_le _ _
    _ ≤ ∑ u, ∫ ω,
        ‖oscillatoryWindowProduct (a u) (b u) (coordinate u ω)
            (K u) (alpha u ω) -
          oscillatoryWindowProduct (a u) (b u) (frozenCoordinate u ω)
            (K u) (representative u ω)‖ ∂mu := by
      apply Finset.sum_le_sum
      intro u _hu
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∑ u, ∫ ω,
        oscillatoryPrefixFreezingEnvelope (a u) (b u) (coordinate u ω)
          (K u) (phaseRadius u) (eta u) ∂mu :=
      sum_integral_norm_oscillatoryWindowProduct_sub_le mu
        a b coordinate frozenCoordinate K phaseRadius eta
        alpha representative hphaseRadius heta halpha hcoordinate
        hactual hfrozen henvelope

/-! ## Convergence wrapper for the deterministic cylinder sum -/

/-- Sequence-level form of the deterministic oscillatory cylinder bound.
All tuple and cylinder cardinalities remain internal to the cited theorem;
the only asymptotic input is that its explicit right-hand side tends to
zero. -/
theorem tendsto_oscillatoryCylinderTupleSum_zero
    {d : ℕ} (L R N : ℕ → ℕ)
    (boxes : ∀ _n, Fin d → Finset ℕ)
    (hboxes : ∀ n j, (boxes n j).card ≤ L n)
    (cells : ∀ n, OscillatoryPrefixTuple (boxes n) →
      Finset (BoundedPositiveTerminalWord (R n)))
    (left right D : ∀ n, OscillatoryPrefixTuple (boxes n) →
      BoundedPositiveTerminalWord (R n) → ℝ)
    (denominatorFloor : ℕ → ℝ)
    (hN : ∀ n, 0 < N n)
    (hfloor : ∀ n, 0 < denominatorFloor n)
    (hD : ∀ n u w, w ∈ cells n u →
      denominatorFloor n ≤ |D n u w|)
    (hboundZero : Tendsto
      (fun n ↦ ((2 * L n ^ d * (R n + 1) ^ 2 : ℕ) : ℝ) /
        (Real.pi * (N n : ℝ) * denominatorFloor n))
      atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ ∑ u : OscillatoryPrefixTuple (boxes n),
        ‖∑ w ∈ cells n u,
          ∫ x : ℝ in left n u w..right n u w,
            oscillatoryPhase ((N n : ℝ) * D n u w) x‖)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun _u _hu ↦ norm_nonneg _
  · exact Eventually.of_forall fun n ↦
      sum_norm_sum_intervalIntegral_oscillatory_cylinders_le
        (hN n) (boxes n) (hboxes n) (cells n)
        (left n) (right n) (D n) (hfloor n) (hD n)
  · exact hboundZero

/-! ## Aggregate functional `psi`-mixing -/

variable {Ω U V : Type*}

/-- Finite-family aggregate covariance estimate.  This is the summed
function version of event `psi`-mixing used after prefix freezing. -/
theorem norm_sum_complex_covariances_le
    [Fintype U] [Fintype V]
    (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
    (hmix : EventRelativeMixing m₁ m₂ mu epsilon)
    (f : U → Ω → ℂ) (g : V → Ω → ℂ)
    (hfM : ∀ u, @Measurable Ω ℂ m₁ (borel ℂ) (f u))
    (hgM : ∀ v, @Measurable Ω ℂ m₂ (borel ℂ) (g v))
    (hfi : ∀ u, Integrable (f u) mu)
    (hgi : ∀ v, Integrable (g v) mu) :
    ‖∑ u, ∑ v,
        ((∫ x, f u x * g v x ∂mu) -
          (∫ x, f u x ∂mu) * ∫ x, g v x ∂mu)‖ ≤
      4 * epsilon *
        (∑ u, ∫ x, ‖f u x‖ ∂mu) *
        (∑ v, ∫ x, ‖g v x‖ ∂mu) := by
  have hcov (u : U) (v : V) :
      ‖(∫ x, f u x * g v x ∂mu) -
          (∫ x, f u x ∂mu) * ∫ x, g v x ∂mu‖ ≤
        4 * epsilon * (∫ x, ‖f u x‖ ∂mu) *
          ∫ x, ‖g v x‖ ∂mu :=
    (hmix.covariance_complex m₁ m₂ mu epsilon hepsilon hm₁ hm₂
      (hfM u) (hgM v) (hfi u) (hgi v)).2
  calc
    ‖∑ u, ∑ v,
        ((∫ x, f u x * g v x ∂mu) -
          (∫ x, f u x ∂mu) * ∫ x, g v x ∂mu)‖ ≤
        ∑ u, ∑ v,
          ‖(∫ x, f u x * g v x ∂mu) -
            (∫ x, f u x ∂mu) * ∫ x, g v x ∂mu‖ := by
      exact (norm_sum_le _ _).trans <|
        Finset.sum_le_sum fun u _hu ↦ norm_sum_le _ _
    _ ≤ ∑ u, ∑ v,
        4 * epsilon * (∫ x, ‖f u x‖ ∂mu) *
          ∫ x, ‖g v x‖ ∂mu := by
      exact Finset.sum_le_sum fun u _hu ↦
        Finset.sum_le_sum fun v _hv ↦ hcov u v
    _ = 4 * epsilon *
        (∑ u, ∫ x, ‖f u x‖ ∂mu) *
        (∑ v, ∫ x, ‖g v x‖ ∂mu) := by
      calc
        (∑ u, ∑ v,
            4 * epsilon * (∫ x, ‖f u x‖ ∂mu) *
              ∫ x, ‖g v x‖ ∂mu) =
            ∑ u, (4 * epsilon * (∫ x, ‖f u x‖ ∂mu)) *
              (∑ v, ∫ x, ‖g v x‖ ∂mu) := by
          apply Finset.sum_congr rfl
          intro u _hu
          rw [Finset.mul_sum]
        _ = (∑ u, 4 * epsilon * (∫ x, ‖f u x‖ ∂mu)) *
              (∑ v, ∫ x, ‖g v x‖ ∂mu) := by
          rw [Finset.sum_mul]
        _ = 4 * epsilon *
              (∑ u, ∫ x, ‖f u x‖ ∂mu) *
              (∑ v, ∫ x, ‖g v x‖ ∂mu) := by
          congr 1
          rw [Finset.mul_sum]

/-- A convergence-ready aggregate consequence.  Uniform `L¹` masses and a
mixing error tending to zero force the complete covariance sum to vanish. -/
theorem tendsto_sum_complex_covariances_zero
    [Fintype U] [Fintype V]
    (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 ≤ epsilon n)
    (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
    (hmix : ∀ n, EventRelativeMixing m₁ m₂ mu (epsilon n))
    (f : ℕ → U → Ω → ℂ) (g : ℕ → V → Ω → ℂ)
    (hfM : ∀ n u, @Measurable Ω ℂ m₁ (borel ℂ) (f n u))
    (hgM : ∀ n v, @Measurable Ω ℂ m₂ (borel ℂ) (g n v))
    (hfi : ∀ n u, Integrable (f n u) mu)
    (hgi : ∀ n v, Integrable (g n v) mu)
    (hMassF : ∃ CF : ℝ, ∀ n,
      (∑ u, ∫ x, ‖f n u x‖ ∂mu) ≤ CF)
    (hMassG : ∃ CG : ℝ, ∀ n,
      (∑ v, ∫ x, ‖g n v x‖ ∂mu) ≤ CG)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto
      (fun n ↦ ∑ u, ∑ v,
        ((∫ x, f n u x * g n v x ∂mu) -
          (∫ x, f n u x ∂mu) * ∫ x, g n v x ∂mu))
      atTop (𝓝 0) := by
  obtain ⟨CF, hCF⟩ := hMassF
  obtain ⟨CG, hCG⟩ := hMassG
  have hCF0 : 0 ≤ CF := by
    exact (Finset.sum_nonneg fun u _hu ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      |>.trans (hCF 0)
  have hCG0 : 0 ≤ CG := by
    exact (Finset.sum_nonneg fun v _hv ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      |>.trans (hCG 0)
  have hUpper : Tendsto (fun n ↦ 4 * epsilon n * CF * CG)
      atTop (𝓝 0) := by
    have hfour : Tendsto (fun _ : ℕ ↦ (4 : ℝ)) atTop (𝓝 4) :=
      tendsto_const_nhds
    have hCFconst : Tendsto (fun _ : ℕ ↦ CF) atTop (𝓝 CF) :=
      tendsto_const_nhds
    have hCGconst : Tendsto (fun _ : ℕ ↦ CG) atTop (𝓝 CG) :=
      tendsto_const_nhds
    simpa using! (((hfour.mul hepsilonZero).mul hCFconst).mul hCGconst)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards with n
    calc
      ‖∑ u, ∑ v,
          ((∫ x, f n u x * g n v x ∂mu) -
            (∫ x, f n u x ∂mu) * ∫ x, g n v x ∂mu)‖ ≤
          4 * epsilon n *
            (∑ u, ∫ x, ‖f n u x‖ ∂mu) *
            (∑ v, ∫ x, ‖g n v x‖ ∂mu) :=
        norm_sum_complex_covariances_le m₁ m₂ mu (epsilon n)
          (hepsilon n) hm₁ hm₂ (hmix n) (f n) (g n)
          (hfM n) (hgM n) (hfi n) (hgi n)
      _ ≤ 4 * epsilon n * CF * CG := by
        have hcoef : 0 ≤ 4 * epsilon n :=
          mul_nonneg (by norm_num) (hepsilon n)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hCF n) hcoef)
          (hCG n)
          (Finset.sum_nonneg fun v _hv ↦
            integral_nonneg fun _ ↦ norm_nonneg _)
          (mul_nonneg hcoef hCF0)
  · exact hUpper

end

end Erdos1002
