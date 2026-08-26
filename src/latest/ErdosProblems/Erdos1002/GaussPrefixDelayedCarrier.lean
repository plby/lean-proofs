import ErdosProblems.Erdos1002.GaussPrefixLateMeasurability
import ErdosProblems.Erdos1002.GaussPrefixAnnularDelayedFreezing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Oscillatory prefix carriers at a shallow prefix cutoff

The existing late-prefix carrier lemma places the last nonzero occurrence
at the cylinder depth.  In the upper-retained argument the shallow cutoff
may lie after that occurrence.  This file proves the corresponding carrier
floor with a main occurrence at an arbitrary depth `s ≤ d`.  The theorem is
used at the shallow cutoff `d = midpoint - gap`; the later delayed depth is
used only for freezing and mixing, never for oscillatory decay.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixDelayedCarrierPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

private theorem shallow_half_le_abs_sum_finset_of_dominant
    {α : Type*} [DecidableEq α] (S : Finset α) (term : α → ℝ) (z₀ : α)
    (hz₀ : z₀ ∈ S) {Q : ℝ}
    (hmain : Q ≤ |term z₀|)
    (hrest : ∑ z ∈ S.erase z₀, |term z| ≤ Q / 2) :
    Q / 2 ≤ |∑ z ∈ S, term z| := by
  let rest : ℝ := ∑ z ∈ S.erase z₀, term z
  have hdecomp : term z₀ + rest = ∑ z ∈ S, term z :=
    Finset.add_sum_erase S term hz₀
  have hrestAbs : |rest| ≤ Q / 2 := by
    calc
      |rest| ≤ ∑ z ∈ S.erase z₀, |term z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ Q / 2 := hrest
  have htriangle : |term z₀| ≤ |∑ z ∈ S, term z| + |rest| := by
    calc
      |term z₀| = |(∑ z ∈ S, term z) - rest| := by
        rw [← hdecomp]
        ring_nf
      _ ≤ |∑ z ∈ S, term z| + |rest| := abs_sub _ _
  linarith

/-- Deterministic non-cancellation for a prefix carrier whose last
nonzero occurrence may lie strictly before the cylinder depth. -/
theorem
    half_centerPrefixDenominator_le_abs_exactDepthCylinderMixedPrefixCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m gap : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcenter : (F z₀.1 z₀.2 : ℕ) ≤ m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ)) :
    (cfTerminalDenominator
        (positiveDigitWordTake
          (F z₀.1 z₀.2 : ℕ) hcenter w.toPositive).1 : ℝ) / 2 ≤
      |exactDepthCylinderMixedPrefixCarrier N k h F w| := by
  classical
  let S : Finset (GaussPrefixMixedOccurrence k) :=
    (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)
  let representative : ℝ := gaussPrefixRepresentative w.1.1
  let q : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (cfTerminalDenominator
      (selectedGaussPrefixWord (F z.1 z.2) representative).1 : ℝ)
  let weight : GaussPrefixMixedOccurrence k → ℝ :=
    fun z ↦ |(h z.1 z.2 : ℝ)|
  let term : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (h z.1 z.2 : ℝ) * q z
  let P : ℝ := ((2 ^ (gap / 2) : ℕ) : ℝ)
  let u : PositiveDigitWord (F z₀.1 z₀.2 : ℕ) :=
    positiveDigitWordTake (F z₀.1 z₀.2 : ℕ) hcenter w.toPositive
  let Q : ℝ := (cfTerminalDenominator u.1 : ℝ)
  have hrepMem : representative ∈ positivePrefixCylinder m w.toPositive :=
    gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : representative ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : representative ∈ Ioo (0 : ℝ) 1 := by
      dsimp only [representative]
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  have hz₀S : z₀ ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ z₀, hcenter⟩
  have hdenominatorCenter :
      cfTerminalDenominator
          (selectedGaussPrefixWord
            (F z₀.1 z₀.2 : ℕ) representative).1 =
        cfTerminalDenominator u.1 := by
    have hselected :
        selectedGaussPrefixWord (F z₀.1 z₀.2 : ℕ) representative =
          positiveDigitWordTake
            (F z₀.1 z₀.2 : ℕ) hcenter w.toPositive :=
      selectedGaussPrefixWord_eq_positiveDigitWordTake
        hcenter w.toPositive hrepUnit hrepMem
    rw [hselected]
  have habsCoeff : (1 : ℝ) ≤ |(h z₀.1 z₀.2 : ℝ)| := by
    have hnat : 1 ≤ (h z₀.1 z₀.2).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcoeff)
    calc
      (1 : ℝ) ≤ ((h z₀.1 z₀.2).natAbs : ℝ) := by
        exact_mod_cast hnat
      _ = |(h z₀.1 z₀.2 : ℝ)| := by simp
  have hmain : Q ≤ |term z₀| := by
    dsimp only [term, q, Q]
    rw [hdenominatorCenter, abs_mul,
      abs_of_nonneg (show 0 ≤ (cfTerminalDenominator u.1 : ℝ) by
        positivity)]
    simpa only [one_mul] using!
      (mul_le_mul_of_nonneg_right habsCoeff
        (show 0 ≤ (cfTerminalDenominator u.1 : ℝ) by positivity))
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hscale : ∀ z ∈ S.erase z₀,
      weight z = 0 ∨ P * q z ≤ Q := by
    intro z hz
    have hzS := (Finset.mem_erase.mp hz).2
    have hzNe := (Finset.mem_erase.mp hz).1
    have hzDepth : (F z.1 z.2 : ℕ) ≤ m :=
      (Finset.mem_filter.mp hzS).2
    by_cases hzero : h z.1 z.2 = 0
    · left
      dsimp only [weight]
      simp only [hzero, Int.cast_zero, abs_zero]
    right
    have hgapz := hgap z hzNe hzero
    have hzCenter :
        (F z.1 z.2 : ℕ) ≤ (F z₀.1 z₀.2 : ℕ) := by
      omega
    have hexponent :
        gap / 2 ≤
          ((F z₀.1 z₀.2 : ℕ) - (F z.1 z.2 : ℕ)) / 2 := by
      omega
    have hpow : 2 ^ (gap / 2) ≤
        2 ^ (((F z₀.1 z₀.2 : ℕ) -
          (F z.1 z.2 : ℕ)) / 2) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    have hselected :
        selectedGaussPrefixWord (F z.1 z.2 : ℕ) representative =
          positiveDigitWordTake
            (F z.1 z.2 : ℕ) hzDepth w.toPositive :=
      selectedGaussPrefixWord_eq_positiveDigitWordTake
        hzDepth w.toPositive hrepUnit hrepMem
    have hgrowth :=
      pow_two_depthGap_mul_cfTerminalDenominator_take_le
        (F z.1 z.2 : ℕ) hzCenter u
    have htake :
        (positiveDigitWordTake
          (F z.1 z.2 : ℕ) hzCenter u).1 =
        (positiveDigitWordTake
          (F z.1 z.2 : ℕ) hzDepth w.toPositive).1 := by
      simp only [positiveDigitWordTake_val, u, List.take_take,
        Nat.min_eq_left hzCenter]
    have hmul :
        2 ^ (gap / 2) *
            cfTerminalDenominator
              (selectedGaussPrefixWord
                (F z.1 z.2) representative).1 ≤
          cfTerminalDenominator u.1 := by
      rw [hselected, ← htake]
      exact (Nat.mul_le_mul_right _ hpow).trans hgrowth
    dsimp only [P, q, Q]
    exact_mod_cast hmul
  have htwo : 2 * (∑ z ∈ S.erase z₀, weight z * q z) ≤ Q :=
    two_mul_sum_weight_mul_le_of_common_scale (S.erase z₀) weight q
      hP hQ (fun z _hz ↦ abs_nonneg _) hscale (by
        simpa only [S, weight, P] using! hweightBudget)
  have hrest : ∑ z ∈ S.erase z₀, |term z| ≤ Q / 2 := by
    have hrewrite :
        (∑ z ∈ S.erase z₀, |term z|) =
          ∑ z ∈ S.erase z₀, weight z * q z := by
      apply Finset.sum_congr rfl
      intro z _hz
      dsimp only [term, weight]
      rw [abs_mul, abs_of_nonneg (show 0 ≤ q z by
        dsimp only [q]
        positivity)]
    rw [hrewrite]
    linarith
  change Q / 2 ≤ |∑ z ∈ S, term z|
  apply shallow_half_le_abs_sum_finset_of_dominant
    S term z₀ hz₀S hmain
  simpa using! hrest

/-- On a prefix-good depth-`m` word, the delayed prefix carrier is bounded
below by the exponential denominator scale at the main depth. -/
theorem
    exp_center_le_two_abs_exactDepthCylinderMixedPrefixCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {L m gap : ℕ} {Delta : ℝ}
    (w : ExactDepthBoundedPositiveWord N m)
    (hw : w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcenter : (F z₀.1 z₀.2 : ℕ) ≤ m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ)) :
    Real.exp
        (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
          Delta * (L : ℝ)) ≤
      2 * |exactDepthCylinderMixedPrefixCarrier N k h F w| := by
  have hQ :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w.toPositive hw hcenter).1
  have hcarrier :=
    half_centerPrefixDenominator_le_abs_exactDepthCylinderMixedPrefixCarrier
      N k h F w z₀ hcenter hcoeff hgap hweightBudget
  linarith

/-- One-cylinder oscillatory prefix estimate at a delayed cylinder depth,
with the denominator floor taken at the earlier main carrier depth. -/
theorem
    norm_setIntegral_mixedPrefixCharacter_compactValue_le_centerGoodWord
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {L m gap : ℕ} {Delta A : ℝ}
    (w : ExactDepthBoundedPositiveWord N m)
    (hw : w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcenter : (F z₀.1 z₀.2 : ℕ) ≤ m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∫ y in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m y ∂uniform01Measure‖ ≤
      2 / (Real.pi * (N : ℝ) *
        Real.exp
          (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
            Delta * (L : ℝ))) := by
  obtain ⟨left, right, _hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_mixedPrefixCharacter_compactValue
      N hN k h F w lower upper hlower hupper hsmall
  rw [hinterval]
  let E : ℝ :=
    Real.exp
      (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
        Delta * (L : ℝ))
  let D : ℝ := exactDepthCylinderMixedPrefixCarrier N k h F w
  have hDfloor : E / 2 ≤ |D| := by
    have hraw :=
      exp_center_le_two_abs_exactDepthCylinderMixedPrefixCarrier
        N k h F w hw z₀ hcenter hcoeff hgap hweightBudget
    dsimp only [E, D]
    linarith
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hDfloor
    have hE : 0 < E := by
      dsimp only [E]
      positivity
    linarith
  have hone :=
    norm_intervalIntegral_oscillatoryPhase_nat_mul_le
      left right D N (by omega) hD
  calc
    ‖∫ y : ℝ in left..right,
        oscillatoryPhase ((N : ℝ) * D) y‖ ≤
        1 / (Real.pi * (N : ℝ) * |D|) := hone
    _ ≤ 1 / (Real.pi * (N : ℝ) * (E / 2)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact mul_le_mul_of_nonneg_left hDfloor (by positivity)
    _ = 2 / (Real.pi * (N : ℝ) * E) := by
      field_simp

/-- Tighten only the denominator cutoff carried by an exact-depth word. -/
def shallowExactDepthBoundedPositiveWordTighten
    {N R m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (hR : cfTerminalDenominator w.1.1 ≤ R) :
    ExactDepthBoundedPositiveWord R m :=
  ⟨⟨w.1.1, w.1.2.1, w.1.2.2.1, hR⟩, w.2⟩

@[simp] theorem shallowExactDepthBoundedPositiveWordTighten_word
    {N R m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (hR : cfTerminalDenominator w.1.1 ≤ R) :
    (shallowExactDepthBoundedPositiveWordTighten w hR).1.1 = w.1.1 := rfl

/-- A finite depth-`m` family whose actual denominators are bounded by `R`
inherits the quadratic word-count bound at `R`. -/
theorem card_shallowExactDepthCells_le_of_terminalDenominator_le
    {N R m : ℕ}
    (cells : Finset (ExactDepthBoundedPositiveWord N m))
    (hR : ∀ w ∈ cells, cfTerminalDenominator w.1.1 ≤ R) :
    cells.card ≤ 2 * (R + 1) ^ 2 := by
  let f : (↥cells) → ExactDepthBoundedPositiveWord R m :=
    fun w ↦ shallowExactDepthBoundedPositiveWordTighten
      w.1 (hR w.1 w.2)
  have hf : Function.Injective f := by
    intro w v hwv
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u ↦ u.1.1) hwv
  calc
    cells.card = Fintype.card (↥cells) := by simp
    _ ≤ Fintype.card (ExactDepthBoundedPositiveWord R m) :=
      Fintype.card_le_of_injective f hf
    _ ≤ 2 * (R + 1) ^ 2 :=
      card_exactDepthBoundedPositiveWord_le R m

/-- Prefix-good cells at one shallow cutoff. -/
def shallowExactDepthPrefixGoodCells
    (N m L : ℕ) (Delta : ℝ) :
    Finset (ExactDepthBoundedPositiveWord N m) :=
  Finset.univ.filter fun w ↦
    w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta

@[simp] theorem mem_shallowExactDepthPrefixGoodCells_iff
    {N m L : ℕ} {Delta : ℝ}
    {w : ExactDepthBoundedPositiveWord N m} :
    w ∈ shallowExactDepthPrefixGoodCells N m L Delta ↔
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta := by
  simp [shallowExactDepthPrefixGoodCells]

/-- The ceiling in the terminal cutoff costs at most a factor nine after
squaring. -/
theorem shallow_natCeil_exp_add_one_sq_le
    {x : ℝ} (hx : 0 ≤ x) :
    (((⌈Real.exp x⌉₊ + 1) ^ 2 : ℕ) : ℝ) ≤
      9 * Real.exp (2 * x) := by
  have hexpOne : 1 ≤ Real.exp x := by
    simpa only [Real.exp_zero] using! Real.exp_le_exp.mpr hx
  have hceil :
      (⌈Real.exp x⌉₊ : ℝ) < Real.exp x + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos x).le
  have hlinear :
      ((⌈Real.exp x⌉₊ : ℝ) + 1) ≤ 3 * Real.exp x := by
    linarith
  have hnonneg : 0 ≤ ((⌈Real.exp x⌉₊ : ℝ) + 1) := by positivity
  have hsquare := pow_le_pow_left₀ hnonneg hlinear 2
  push_cast
  calc
    ((⌈Real.exp x⌉₊ : ℝ) + 1) ^ 2 ≤
        (3 * Real.exp x) ^ 2 := hsquare
    _ = 9 * Real.exp (2 * x) := by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring

/-- Explicit shallow-prefix cylinder envelope. -/
def shallowPrefixCylinderEnvelope
    (N L depth center : ℕ) (Delta : ℝ) : ℝ :=
  (36 / Real.pi) *
    Real.exp
      (2 * (depth : ℝ) * gaussRoofMean -
        (center : ℝ) * gaussRoofMean -
        Real.log (N : ℝ) + 3 * Delta * (L : ℝ))

/-- Sum over all prefix-good depth-`m` cells.  The resulting exponent is
`2m μ - s μ - log N + 3 ΔL`, with no suppressed rounding term. -/
theorem
    norm_sum_exactDepthPrefixGoodCells_mixedPrefixCharacter_le_centerEnvelope
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {L m gap : ℕ} {Delta A : ℝ}
    (hDelta : 0 ≤ Delta)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcenter : (F z₀.1 z₀.2 : ℕ) ≤ m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∑ w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F m y ∂uniform01Measure‖ ≤
      shallowPrefixCylinderEnvelope
        N L m (F z₀.1 z₀.2 : ℕ) Delta := by
  let x : ℝ :=
    (m : ℝ) * gaussRoofMean + Delta * (L : ℝ)
  let R : ℕ := ⌈Real.exp x⌉₊
  have hterminal :
      ∀ w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
        cfTerminalDenominator w.1.1 ≤ R := by
    intro w hw
    have hupperQ :=
      (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
        w.toPositive (mem_shallowExactDepthPrefixGoodCells_iff.mp hw)
        (le_refl m)).2
    have htake : w.toPositive.1.take m = w.toPositive.1 :=
      List.take_of_length_le w.toPositive.2.1.le
    have hupperQ' :
        (cfTerminalDenominator w.1.1 : ℝ) ≤
          Real.exp x := by
      simpa only [positiveDigitWordTake_val, htake] using! hupperQ
    exact_mod_cast
      (hupperQ'.trans (Nat.le_ceil _))
  let cellBound : ℝ :=
    2 / (Real.pi * (N : ℝ) *
      Real.exp
        (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
          Delta * (L : ℝ)))
  have hcellBound : 0 ≤ cellBound := by
    dsimp only [cellBound]
    positivity
  have hOne
      (w : ExactDepthBoundedPositiveWord N m)
      (hw : w ∈ shallowExactDepthPrefixGoodCells N m L Delta) :
      ‖∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F m y ∂uniform01Measure‖ ≤ cellBound := by
    simpa only [cellBound] using!
      norm_setIntegral_mixedPrefixCharacter_compactValue_le_centerGoodWord
        N hN k h F w (mem_shallowExactDepthPrefixGoodCells_iff.mp hw)
        z₀ hcenter hcoeff hgap hweightBudget
        lower upper hlower hupper hsmall
  have hcard :
      (shallowExactDepthPrefixGoodCells N m L Delta).card ≤
        2 * (R + 1) ^ 2 :=
    card_shallowExactDepthCells_le_of_terminalDenominator_le
      (shallowExactDepthPrefixGoodCells N m L Delta) hterminal
  have hx :
      0 ≤ x := by
    dsimp only [x]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg m) gaussRoofMean_pos.le)
      (mul_nonneg hDelta (Nat.cast_nonneg L))
  have hsq := shallow_natCeil_exp_add_one_sq_le hx
  have hsq' :
      ((R : ℝ) + 1) ^ 2 ≤ 9 * Real.exp (2 * x) := by
    simpa only [R, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using! hsq
  calc
    ‖∑ w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F m y ∂uniform01Measure‖ ≤
        ∑ w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
          ‖∫ y in exactDepthBoundedCylinder w,
            gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
              k h F m y ∂uniform01Measure‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w ∈ shallowExactDepthPrefixGoodCells N m L Delta,
        cellBound := Finset.sum_le_sum fun w hw ↦ hOne w hw
    _ = ((shallowExactDepthPrefixGoodCells N m L Delta).card : ℝ) *
        cellBound := by simp
    _ ≤ ((2 * (R + 1) ^ 2 : ℕ) : ℝ) * cellBound := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard) hcellBound
    _ ≤ (2 * (9 * Real.exp (2 * x))) * cellBound := by
      apply mul_le_mul_of_nonneg_right _ hcellBound
      push_cast
      exact mul_le_mul_of_nonneg_left
        hsq' (by norm_num)
    _ = shallowPrefixCylinderEnvelope
        N L m (F z₀.1 z₀.2 : ℕ) Delta := by
      unfold shallowPrefixCylinderEnvelope
      dsimp only [cellBound]
      have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
      rw [show
        2 * (m : ℝ) * gaussRoofMean -
              ((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Real.log (N : ℝ) + 3 * Delta * (L : ℝ) =
            2 * x -
              (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
                Delta * (L : ℝ)) -
              Real.log (N : ℝ) by
        dsimp only [x]
        ring]
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hNpos]
      field_simp [ne_of_gt Real.pi_pos]
      rw [show
        2 * x -
              (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
                Delta * (L : ℝ)) =
            2 * x +
              (Delta * (L : ℝ) -
                ((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean) by ring]
      rw [Real.exp_add, Real.exp_sub]
      field_simp
      ring

end

end Erdos1002
