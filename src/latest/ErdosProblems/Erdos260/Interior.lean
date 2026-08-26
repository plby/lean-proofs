import ErdosProblems.Erdos260.AffineLocking

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Long-interior contribution

This module corresponds to Section 6 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace Erdos260

/-- Primitive normalization preserves the rational normalized slope. -/
theorem AffineLine.canonicalGeometricLine_slope (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) :
    line.canonicalGeometricLine.slope Q = line.slope Q := by
  have hdpos : (0 : ℤ) < (line.directionGCD : ℤ) := by
    exact_mod_cast line.directionGCD_pos
  have hdne : (line.directionGCD : ℤ) ≠ 0 := ne_of_gt hdpos
  have hHfactor :
      line.primitiveHorizontalInt * (line.directionGCD : ℤ) = line.H :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  have hKfactor :
      line.primitiveVertical * (line.directionGCD : ℤ) = line.K :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right line.H line.K)
  have hdneQ : ((line.directionGCD : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast hdne
  have hpneQ : (line.primitiveHorizontalInt : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt line.primitiveHorizontalInt_pos)
  rw [GeometricLine.slope, AffineLine.slope]
  change ((line.primitiveVertical : ℤ) : ℚ) /
      ((Q : ℚ) * (line.canonicalGeometricLine.H : ℚ)) =
    (line.K : ℚ) / ((Q : ℚ) * (line.H : ℚ))
  have hHcast : (line.canonicalGeometricLine.H : ℚ) =
      (line.primitiveHorizontalInt : ℚ) := by
    exact_mod_cast line.canonicalGeometricLine_H_cast
  rw [hHcast]
  have hHfactorQ : (line.primitiveHorizontalInt : ℚ) *
      (line.directionGCD : ℚ) = (line.H : ℚ) := by
    exact_mod_cast hHfactor
  have hKfactorQ : (line.primitiveVertical : ℚ) *
      (line.directionGCD : ℚ) = (line.K : ℚ) := by
    exact_mod_cast hKfactor
  rw [← hHfactorQ, ← hKfactorQ]
  field_simp [hpneQ, hdneQ]
  exact (mul_div_cancel_right₀ (line.primitiveVertical : ℚ) hdneQ).symm

/-- Exact one-gap monodromy for the integer intercept numerator. -/
theorem AffineLine.interceptNumerator_transform (Q g : ℕ)
    (line : AffineLine) :
    (line.transform Q g).interceptNumerator =
      (2 : ℤ) ^ g * line.interceptNumerator -
        (2 : ℤ) ^ g * line.K * g := by
  simp only [AffineLine.interceptNumerator, AffineLine.transform]
  ring

/-- Applying one fixed shared word to two lines with the same direction
multiplies their intercept-numerator difference by the exact dyadic span. -/
theorem AffineLine.interceptDifference_transformWord (Q : ℕ)
    (u v : AffineLine) (w : GapWord) (hH : u.H = v.H) (hK : u.K = v.K) :
    (u.transformWord Q w).interceptNumerator -
        (v.transformWord Q w).interceptNumerator =
      (2 : ℤ) ^ w.span *
        (u.interceptNumerator - v.interceptNumerator) := by
  induction w generalizing u v with
  | nil => simp [AffineLine.transformWord, GapWord.span]
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      have hH' : (u.transform Q g).H = (v.transform Q g).H := by
        simpa [AffineLine.transform] using hH
      have hK' : (u.transform Q g).K = (v.transform Q g).K := by
        simp only [AffineLine.transform]
        rw [hH, hK]
      rw [ih (u.transform Q g) (v.transform Q g) hH' hK']
      rw [AffineLine.interceptNumerator_transform,
        AffineLine.interceptNumerator_transform]
      simp only [GapWord.span, List.sum_cons, pow_add]
      rw [hK]
      ring

/-- For a primitive raw direction, canonical geometric membership is exactly
membership in the original integer parameterization. -/
theorem AffineLine.contains_of_canonicalGeometricLine_of_primitive
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1)
    (x r : ℤ) (hcontains : line.canonicalGeometricLine.Contains x r) :
    line.Contains x r := by
  have hcanonicalH : (line.canonicalGeometricLine.H : ℤ) = line.H := by
    rw [line.canonicalGeometricLine_H_cast]
    simp [AffineLine.primitiveHorizontalInt, AffineLine.directionGCD,
      hprimitive]
  have hcanonicalK : line.canonicalGeometricLine.K = line.K := by
    simp [AffineLine.canonicalGeometricLine, AffineLine.primitiveVertical,
      AffineLine.directionGCD, hprimitive]
  have hcanonicalIntercept : line.canonicalGeometricLine.intercept =
      line.interceptNumerator := by
    simp [AffineLine.canonicalGeometricLine, AffineLine.directionGCD,
      hprimitive]
  rw [GeometricLine.Contains, hcanonicalH, hcanonicalK,
    hcanonicalIntercept] at hcontains
  have hmul : line.H * (r - line.C) = line.K * (x - line.A) := by
    simp only [AffineLine.interceptNumerator] at hcontains
    linarith
  have hdvdMul : line.H ∣ line.K * (x - line.A) := by
    exact ⟨r - line.C, hmul.symm⟩
  have hdvd : line.H ∣ x - line.A :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hdvdMul hprimitive
  rcases hdvd with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · linarith
  · have hHne : line.H ≠ 0 := ne_of_gt line.H_pos
    apply mul_left_cancel₀ hHne
    calc
      line.H * r = line.H * line.C + line.K * (x - line.A) := by
        linarith
      _ = line.H * (line.C + line.K * t) := by
        rw [ht]
        ring

/-- A stabilized interior segment with one reduced odd denominator. -/
structure OddDenominatorSegment where
  startLine : AffineLine
  gaps : GapWord
  slopes : List ℚ
  q : ℕ

namespace OddDenominatorSegment

/-- The exact normalized slopes along every prefix of a shared gap word. -/
def slopeTrace (Q : ℕ) (line : AffineLine) (gaps : GapWord) : List ℚ :=
  (List.range (gaps.length + 1)).map fun r =>
    (line.transformWord Q (gaps.take r)).slope Q

def Valid (Q : ℕ) (segment : OddDenominatorSegment) : Prop :=
  0 < Q ∧ segment.gaps.Positive ∧
    Int.gcd segment.startLine.H segment.startLine.K = 1 ∧
    segment.slopes = slopeTrace Q segment.startLine segment.gaps ∧
    1 < segment.q ∧ Odd segment.q ∧
    ∀ μ ∈ segment.slopes,
      μ ∈ Set.Ioo (0 : ℚ) 1 ∧ μ.den = segment.q ∧ Odd μ.num

def span (segment : OddDenominatorSegment) : ℕ := segment.gaps.span

def gapCount (segment : OddDenominatorSegment) : ℕ := segment.gaps.length

end OddDenominatorSegment

/-- A retained completed logarithmic block. -/
structure LowGapBlock where
  offset : ℕ
  gaps : GapWord
  deriving DecidableEq, Repr

namespace LowGapBlock

def span (block : LowGapBlock) : ℕ := block.gaps.span

/-- The block occurs at its recorded offset in the supplied segment. -/
def OccursIn (segment : OddDenominatorSegment) (block : LowGapBlock) : Prop :=
  block.offset + block.gaps.length ≤ segment.gaps.length ∧
    (segment.gaps.drop block.offset).take block.gaps.length = block.gaps

end LowGapBlock

def blocksWithOffsetsFrom : ℕ → List GapWord → List LowGapBlock
  | _, [] => []
  | offset, gaps :: rest =>
      ⟨offset, gaps⟩ :: blocksWithOffsetsFrom (offset + gaps.length) rest

/-- The maximal initial list of completed blocks whose genuine post-block
suffix still has the required forward span. -/
private def forwardEligibleWords (remainder : GapWord) (forward : ℕ) :
    List GapWord → List GapWord
  | [] => []
  | block :: rest =>
      if forward ≤ GapWord.span (rest.flatten ++ remainder) then
        block :: forwardEligibleWords remainder forward rest
      else []

/-- The complementary final list discarded by the forward-span rule. -/
private def forwardDiscardedWords (remainder : GapWord) (forward : ℕ) :
    List GapWord → List GapWord
  | [] => []
  | block :: rest =>
      if forward ≤ GapWord.span (rest.flatten ++ remainder) then
        forwardDiscardedWords remainder forward rest
      else block :: rest

/-- Deterministically retained completed low-gap blocks.  The construction is
spatial: it depends on the segment and fixed band parameters, never on a
threshold coordinate. -/
def selectedBlocks (segment : OddDenominatorSegment) (B : ℝ)
    (ell Z forward : ℕ) : List LowGapBlock :=
  let decomposition :=
    GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))
  let eligible :=
    forwardEligibleWords decomposition.remainder forward decomposition.completed
  (blocksWithOffsetsFrom 0 eligible).filter fun block =>
    Z * block.gaps.length ≤ 4 * block.span

/-- The equivalent pointwise form used by the encoding argument: forward
eligibility is tested separately at every completed-block offset. -/
private def pointwiseSelectedBlocks (segment : OddDenominatorSegment) (B : ℝ)
    (ell Z forward : ℕ) : List LowGapBlock :=
  let decomposition :=
    GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))
  (blocksWithOffsetsFrom 0 decomposition.completed).filter fun block =>
    Z * block.gaps.length ≤ 4 * block.span ∧
      block.offset + block.gaps.length ≤ segment.gaps.length ∧
      forward ≤
        GapWord.span
          (segment.gaps.drop (block.offset + block.gaps.length))

/-- Data retained by the block encoding map `Σ`. -/
@[ext] structure BlockEncoding where
  D : ℕ
  Z : ℕ
  h : ℕ
  r : ℕ
  gaps : GapWord
  deriving DecidableEq

namespace BlockEncoding

def Valid (σ : BlockEncoding) : Prop :=
  (∃ k : ℕ, σ.D = 2 ^ k) ∧ (∃ k : ℕ, σ.Z = 2 ^ k) ∧
    σ.h = σ.gaps.span ∧ σ.r = σ.gaps.length ∧ σ.gaps.Positive

end BlockEncoding

/-- Encoding of a concrete retained block. -/
def encodeBlock (D Z : ℕ) (block : LowGapBlock) : BlockEncoding where
  D := D
  Z := Z
  h := block.span
  r := block.gaps.length
  gaps := block.gaps

/-- Candidate encodings in fixed denominator and mean-gap bands. -/
def encodingCandidates (D Z : ℕ) (B : ℝ) : Set BlockEncoding :=
  {σ | σ.Valid ∧ σ.D = D ∧ σ.Z = Z ∧
    B * Nat.ceil (Real.logb 2 (4 * D)) ≤ σ.h ∧
    (σ.h : ℝ) ≤ (B + 1) * Nat.ceil (Real.logb 2 (4 * D)) ∧
    (σ.r : ℝ) ≤ 4 * σ.h / Z}

/-- The selected blocks occur in order inside the stabilized segment, are
greedy completed blocks, and cover at least half its span. -/
def IsLowGapCover (segment : OddDenominatorSegment) (B : ℝ)
    (ell Z forward : ℕ) (blocks : List LowGapBlock) : Prop :=
  blocks = selectedBlocks segment B ell Z forward ∧
    (∀ block ∈ blocks, LowGapBlock.OccursIn segment block ∧
      GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block.gaps ∧
      Z * block.gaps.length ≤ 4 * block.span) ∧
    segment.span ≤ 2 * (blocks.map LowGapBlock.span).sum

/-- Exact nonnegative component weight used for the interior refinement. -/
def interiorComponentWeight (y : ℝ) (blocks : List LowGapBlock)
    (block : LowGapBlock) : ℝ :=
  y * block.span / (blocks.map LowGapBlock.span).sum

/-- A line realizes an encoding when its normalized slope has denominator in
the recorded band and its shared gap word is exactly the encoded word. -/
def LineRealizesEncoding (Q : ℕ) (line : AffineLine)
    (σ : BlockEncoding) : Prop :=
  σ.D ≤ (line.slope Q).den ∧ (line.slope Q).den < 2 * σ.D ∧
    ∃ finish : AffineLine, SharedGapTrajectory Q line σ.gaps finish

def GeometricLineRealizesEncoding (Q : ℕ) (line : GeometricLine)
    (σ : BlockEncoding) : Prop :=
  σ.D ≤ (line.slope Q).den ∧ (line.slope Q).den < 2 * σ.D ∧
    slopeAfter σ.gaps (line.slope Q : ℝ) ∈ Set.Ioo (0 : ℝ) 1

/-- Actual stabilized-segment data selected deterministically for one anchor.
The `before` word starts at the end of the initial long prefix. -/
structure AnchorInteriorData where
  baseLine : AffineLine
  before : GapWord
  segment : OddDenominatorSegment

namespace AnchorInteriorData

/-- Semantic validity of one anchor's stabilized segment.  This records only
facts supplied by the actual support window and shared-gap dynamics. -/
def Valid (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) : Prop :=
  W.s ≤ k ∧ k ∈ highAnchors W Z0 ∧
    IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
    IsOccurrenceLine W Z0 (initialLongPrefix W k) data.baseLine ∧
    data.segment.Valid Q ∧
    (∃ after : GapWord,
      actualPostPrefixGaps W k =
        data.before ++ data.segment.gaps ++ after) ∧
    (data.baseLine.transformWord Q data.before).canonicalGeometricLine =
      data.segment.startLine.canonicalGeometricLine

end AnchorInteriorData

/-- At most one deterministic stabilized segment is retained for each anchor. -/
abbrev InteriorAnchorSelection := ℕ → Option AnchorInteriorData

def ValidInteriorAnchorSelection (Q : ℕ) (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) : Prop :=
  ∀ k data, selection k = some data → data.Valid Q W Z0 k

/-- The block's absolute position among the gaps of the anchored order-`m`
window. -/
def sourceWindowOffset (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) : ℕ :=
  (initialLongPrefix W k).length + data.before.length + block.offset

/-- Raw affine line at the start of a selected block. -/
def sourceRawLine (Q : ℕ) (data : AnchorInteriorData)
    (block : LowGapBlock) : AffineLine :=
  data.segment.startLine.transformWord Q
    (data.segment.gaps.take block.offset)

/-- Absolute support coordinate at the selected block start. -/
def sourceCoordinate (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) : ℕ :=
  W.enumeration.a (k - W.s + sourceWindowOffset W k data block)

/-- The proposed spatial injection code: absolute block-start coordinate and
its offset from the left edge of the anchored window.  Injectivity is a theorem
to be derived from line uniqueness and the strict support enumeration, not a
field of the source data. -/
def spatialSourceCode (W : WindowSystem) (selection : InteriorAnchorSelection)
    (kb : ℕ × LowGapBlock) : Option (ℕ × ℕ) :=
  (selection kb.1).map fun data =>
    (sourceCoordinate W kb.1 data kb.2,
      sourceWindowOffset W kb.1 data kb.2)

@[simp] theorem spatialSourceCode_of_selected (W : WindowSystem)
    (selection : InteriorAnchorSelection) (k : ℕ) (block : LowGapBlock)
    (data : AnchorInteriorData) (hdata : selection k = some data) :
    spatialSourceCode W selection (k, block) =
      some (sourceCoordinate W k data block,
        sourceWindowOffset W k data block) := by
  simp [spatialSourceCode, hdata]

/-- Original parameters whose horizontal coordinates lie in the enlarged
dyadic corridor. -/
def horizontalParameters (X : ℕ) (line : AffineLine) : Set ℤ :=
  {t | -(X : ℤ) ≤ line.A + line.H * t ∧
    line.A + line.H * t ≤ 3 * X}

/-- The original integer parameter realizes the actual block-start support
point on the unreduced affine line. -/
def IsOriginalSourceParameter (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) (t : ℤ) : Prop :=
  let raw := sourceRawLine Q data block
  let x := sourceCoordinate W k data block
  (x : ℤ) = raw.A + raw.H * t ∧
    carryInt W.rational x = raw.C + raw.K * t ∧
    t ∈ horizontalParameters W.X raw

theorem sourceCoordinate_on_canonicalLine (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) (t : ℤ)
    (hparameter : IsOriginalSourceParameter Q W k data block t) :
    (sourceRawLine Q data block).canonicalGeometricLine.Contains
      (sourceCoordinate W k data block : ℤ)
      (carryInt W.rational (sourceCoordinate W k data block)) := by
  apply (sourceRawLine Q data block).contains_canonicalGeometricLine
  exact ⟨t, hparameter.1, hparameter.2.1⟩

theorem originalSourceParameter_mem_corridor (Q : ℕ) (W : WindowSystem)
    (k : ℕ) (data : AnchorInteriorData) (block : LowGapBlock) (t : ℤ)
    (hparameter : IsOriginalSourceParameter Q W k data block t) :
    t ∈ horizontalParameters W.X (sourceRawLine Q data block) :=
  hparameter.2.2

/-- Logarithmic block length attached to the denominator band in an encoding. -/
def encodingLogLength (σ : BlockEncoding) : ℕ :=
  Nat.ceil (Real.logb 2 (4 * σ.D))

/-- Forward reserve retained after every selected interior block. -/
def reconstructionForwardLength (W : WindowSystem) (Cgap : ℕ) : ℕ :=
  3 * W.L + 2 * Cgap

/-- The actual interior suffix beginning immediately after a retained block. -/
def sourceForwardSuffix (data : AnchorInteriorData)
    (block : LowGapBlock) : GapWord :=
  data.segment.gaps.drop (block.offset + block.gaps.length)

/-- The deterministic shortest reconstruction word cut from the actual
post-block interior suffix. -/
def sourceForwardWord (W : WindowSystem) (Cgap : ℕ)
    (data : AnchorInteriorData) (block : LowGapBlock) : GapWord :=
  (sourceForwardSuffix data block).firstPrefixAbove (2 * W.L + Cgap)

/-- The raw affine line at the end of the encoded block, before any primitive
renormalization. -/
def sourceBlockEndLine (Q : ℕ) (data : AnchorInteriorData)
    (block : LowGapBlock) : AffineLine :=
  (sourceRawLine Q data block).transformWord Q block.gaps

/-- A canonical line reconstructed from one *actual* selected spatial source.
The source anchor, selected segment, retained block, raw primitive line, and
forward word are all fixed in the arguments.  In particular, the forward
word is not existential data: it is the shortest prefix of the genuine
post-block suffix whose span exceeds the paper's reconstruction threshold. -/
def IsReconstructedOccurrenceLine (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (k : ℕ) (data : AnchorInteriorData) (block : LowGapBlock)
    (line : GeometricLine) : Prop :=
  selection k = some data ∧
    data.Valid Q W Z0 k ∧
    IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
    block ∈ selectedBlocks data.segment B (encodingLogLength σ) σ.Z
      (reconstructionForwardLength W Cgap) ∧
    LowGapBlock.OccursIn data.segment block ∧
    sourceWindowOffset W k data block < W.m ∧
    σ ∈ encodingCandidates σ.D σ.Z B ∧
    0 < σ.D ∧
    encodeBlock σ.D σ.Z block = σ ∧
    Int.gcd (sourceRawLine Q data block).H
      (sourceRawLine Q data block).K = 1 ∧
    (sourceRawLine Q data block).canonicalGeometricLine = line ∧
    ((sourceRawLine Q data block).canonicalGeometricLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W ∧
    LineRealizesEncoding Q (sourceRawLine Q data block) σ ∧
    GeometricLineRealizesEncoding Q line σ ∧
    SharedGapTrajectory Q (sourceRawLine Q data block) block.gaps
      (sourceBlockEndLine Q data block) ∧
    2 * W.L + Cgap < (sourceForwardWord W Cgap data block).span ∧
    (sourceForwardWord W Cgap data block).span ≤
      reconstructionForwardLength W Cgap ∧
    (sourceForwardWord W Cgap data block).Positive ∧
    IsInteriorTrajectory Q (sourceBlockEndLine Q data block)
      (sourceForwardWord W Cgap data block)

/-- A genuine spatial source of an encoding.  Every field is tied to the
actual anchored suffix and deterministic block rule.  In particular no
fibre-size or injectivity assertion is included here. -/
def IsSpatialEncodingSource (Q Cgap : ℕ) (B Cstep : ℝ) (W : WindowSystem)
    (Z0 : ℕ) (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (kb : ℕ × LowGapBlock) : Prop :=
  ∃ data : AnchorInteriorData, ∃ t : ℤ,
    IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      kb.1 data kb.2
        (sourceRawLine Q data kb.2).canonicalGeometricLine ∧
    IsOriginalSourceParameter Q W kb.1 data kb.2 t

/-- Spatial preimage of one encoding, before threshold integration. -/
def spatialPreimage (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding) :
    Set (ℕ × LowGapBlock) :=
  {kb | IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ kb}

/-- Canonical geometric lines actually represented by the spatial preimage
of one encoding.  This image contains no arbitrary reconstructed line. -/
def spatialCanonicalLines (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding) :
    Set GeometricLine :=
  {line | ∃ k : ℕ, ∃ data : AnchorInteriorData, ∃ block : LowGapBlock,
    IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ (k, block) ∧
      selection k = some data ∧
      (sourceRawLine Q data block).canonicalGeometricLine = line}

/-- The spatial code is injective on genuine sources.  This is the single
order factor in the paper's fibre argument: no threshold coordinate is
present, and the offset contributes exactly one factor of `m`. -/
theorem spatialSourceCode_injective (Q Cgap : ℕ) (B Cstep : ℝ)
    (W : WindowSystem) (Z0 : ℕ) (selection : InteriorAnchorSelection)
    (σ : BlockEncoding) :
    Set.InjOn (spatialSourceCode W selection)
      (spatialPreimage Q Cgap B Cstep W Z0 selection σ) := by
  rintro ⟨k₁, block₁⟩ hsource₁ ⟨k₂, block₂⟩ hsource₂ hcode
  change IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ
    (k₁, block₁) at hsource₁
  change IsSpatialEncodingSource Q Cgap B Cstep W Z0 selection σ
    (k₂, block₂) at hsource₂
  rcases hsource₁ with
    ⟨data₁, t₁, hreconstructed₁, _hparameter₁⟩
  rcases hsource₂ with
    ⟨data₂, t₂, hreconstructed₂, _hparameter₂⟩
  rcases hreconstructed₁ with
    ⟨hselected₁, hvalid₁, _hfrequent₁, _hblock₁, _hoccurs₁,
      _hoffsetBound₁, _hcandidate₁, _hD₁, hencoding₁,
      _hprimitive₁, _hline₁, _hstep₁, _hrealizes₁, _hgeometric₁,
      _hblockTrajectory₁, _hlower₁, _hupper₁, _hpositive₁,
      _hinterior₁⟩
  rcases hreconstructed₂ with
    ⟨hselected₂, hvalid₂, _hfrequent₂, _hblock₂, _hoccurs₂,
      _hoffsetBound₂, _hcandidate₂, _hD₂, hencoding₂,
      _hprimitive₂, _hline₂, _hstep₂, _hrealizes₂, _hgeometric₂,
      _hblockTrajectory₂, _hlower₂, _hupper₂, _hpositive₂,
      _hinterior₂⟩
  rw [spatialSourceCode_of_selected W selection k₁ block₁ data₁ hselected₁,
    spatialSourceCode_of_selected W selection k₂ block₂ data₂ hselected₂] at hcode
  have hpair := Option.some.inj hcode
  have hcoordinate := congrArg Prod.fst hpair
  have hoffset := congrArg Prod.snd hpair
  have hindex :
      k₁ - W.s + sourceWindowOffset W k₁ data₁ block₁ =
        k₂ - W.s + sourceWindowOffset W k₂ data₂ block₂ := by
    apply W.enumeration.strictMono.injective
    simpa only [sourceCoordinate] using hcoordinate
  have hanchor : k₁ = k₂ := by
    have hs₁ : W.s ≤ k₁ := hvalid₁.1
    have hs₂ : W.s ≤ k₂ := hvalid₂.1
    omega
  subst k₂
  have hdata : data₁ = data₂ := by
    rw [hselected₁] at hselected₂
    exact Option.some.inj hselected₂
  subst data₂
  have hblockOffset : block₁.offset = block₂.offset := by
    simp only [sourceWindowOffset] at hoffset
    omega
  have hblockGaps : block₁.gaps = block₂.gaps := by
    have hencoding :
        encodeBlock σ.D σ.Z block₁ = encodeBlock σ.D σ.Z block₂ :=
      hencoding₁.trans hencoding₂.symm
    exact congrArg BlockEncoding.gaps hencoding
  have hblock : block₁ = block₂ := by
    cases block₁
    cases block₂
    simp_all
  subst block₂
  rfl

/-! The next lemmas identify every post-prefix subword with the corresponding
run of genuine support gaps and propagate the actual carry point along that
run.  They are kept public because the interior uniqueness and exterior
first-exit arguments use the same source geometry. -/

theorem enumerationGapWord_append {S : Set ℕ}
    (e : SupportEnumeration S) (i r n : ℕ) :
    enumerationGapWord e i (r + n) =
      enumerationGapWord e i r ++ enumerationGapWord e (i + r) n := by
  induction r generalizing i with
  | zero => simp [enumerationGapWord]
  | succ r ih =>
      rw [show r + 1 + n = (r + n) + 1 by omega,
        enumerationGapWord_succ, enumerationGapWord_succ, ih]
      congr 1
      simp [Nat.add_comm, Nat.add_left_comm]

theorem rawWindowGapWord_eq_enumerationGapWord
    (W : WindowSystem) (k : ℕ) (hsk : W.s ≤ k) :
    W.rawWindowGapWord k =
      enumerationGapWord W.enumeration (k - W.s) W.m := by
  simp [WindowSystem.rawWindowGapWord, hsk, WindowSystem.window,
    windowGapWord, enumerationGapWord, WindowSystem.m]

theorem actualPostPrefixGaps_eq_enumerationGapWord
    (W : WindowSystem) (Z0 k : ℕ) (hsk : W.s ≤ k)
    (hk : k ∈ highAnchors W Z0) :
    actualPostPrefixGaps W k =
      enumerationGapWord W.enumeration
        (k - W.s + (initialLongPrefix W k).length)
        (W.m - (initialLongPrefix W k).length) := by
  let p := initialLongPrefix W k
  have hpword : p =
      enumerationGapWord W.enumeration (k - W.s) p.length :=
    initialPrefix_eq_enumerationGapWord W Z0 k p hk rfl
  have hprefix : p.IsPrefix (W.rawWindowGapWord k) := by
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hlen : p.length ≤ W.m :=
    hprefix.length_le.trans (rawWindowGapWord_length_le W k)
  have hsplit := enumerationGapWord_append W.enumeration
    (k - W.s) p.length (W.m - p.length)
  rw [Nat.add_sub_of_le hlen] at hsplit
  unfold actualPostPrefixGaps
  rw [rawWindowGapWord_eq_enumerationGapWord W k hsk, hsplit]
  rw [← hpword]
  simp [p]

theorem prefix_actualPostPrefixGaps_eq_enumerationGapWord
    (W : WindowSystem) (Z0 k : ℕ) (hsk : W.s ≤ k)
    (hk : k ∈ highAnchors W Z0) (before : GapWord)
    (hbefore : before.IsPrefix (actualPostPrefixGaps W k)) :
    before = enumerationGapWord W.enumeration
      (k - W.s + (initialLongPrefix W k).length) before.length := by
  let j := k - W.s + (initialLongPrefix W k).length
  let n := W.m - (initialLongPrefix W k).length
  have hactual : actualPostPrefixGaps W k =
      enumerationGapWord W.enumeration j n := by
    simpa [j, n] using
      actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
  have hlen : before.length ≤ n := by
    have := hbefore.length_le
    rw [hactual] at this
    simpa [enumerationGapWord] using this
  have henumPrefix :
      (enumerationGapWord W.enumeration j before.length).IsPrefix
        (actualPostPrefixGaps W k) := by
    rw [hactual]
    rw [show n = before.length + (n - before.length) by omega,
      enumerationGapWord_append]
    exact List.prefix_append _ _
  have hb := List.prefix_iff_eq_take.mp hbefore
  have he := List.prefix_iff_eq_take.mp henumPrefix
  have hlength :
      (enumerationGapWord W.enumeration j before.length).length =
        before.length := by simp [enumerationGapWord]
  rw [hlength] at he
  exact hb.trans he.symm

theorem AffineLine.contains_transform_supportGap (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i : ℕ)
    (hcontains : line.Contains (e.a i) (carryInt R (e.a i))) :
    (line.transform Q (supportGap e i)).Contains
      (e.a (i + 1)) (carryInt R (e.a (i + 1))) := by
  rcases hcontains with ⟨t, hx, hr⟩
  refine ⟨t, ?_, ?_⟩
  · simp only [AffineLine.transform]
    have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
      simp only [supportGap]
      exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
    have hendpointInt :
        (e.a (i + 1) : ℤ) = (e.a i : ℤ) + supportGap e i := by
      exact_mod_cast hendpoint.symm
    rw [hx] at hendpointInt
    linarith
  · have hgap := supportGap_isSupportGap e i
    have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
      simp only [supportGap]
      exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
    rw [← hendpoint,
      carryInt_across_supportGap R (e.a i) (supportGap e i) hgap]
    simp only [AffineLine.transform]
    rw [hQ, hr, hx]
    ring

/-- A genuine support-gap transformation preserves the original integer
parameter, not merely membership in the transformed line. -/
theorem AffineLine.transform_supportGap_parameter (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i : ℕ) (t : ℤ)
    (hx : (e.a i : ℤ) = line.A + line.H * t)
    (hr : carryInt R (e.a i) = line.C + line.K * t) :
    (e.a (i + 1) : ℤ) =
        (line.transform Q (supportGap e i)).A +
          (line.transform Q (supportGap e i)).H * t ∧
      carryInt R (e.a (i + 1)) =
        (line.transform Q (supportGap e i)).C +
          (line.transform Q (supportGap e i)).K * t := by
  have hxExplicit :
      (e.a (i + 1) : ℤ) =
        (line.transform Q (supportGap e i)).A +
          (line.transform Q (supportGap e i)).H * t := by
    simp only [AffineLine.transform]
    have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
      simp only [supportGap]
      exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
    have hendpointInt :
        (e.a (i + 1) : ℤ) = (e.a i : ℤ) + supportGap e i := by
      exact_mod_cast hendpoint.symm
    rw [hx] at hendpointInt
    linarith
  refine ⟨hxExplicit, ?_⟩
  have hgap := supportGap_isSupportGap e i
  have hendpoint : e.a i + supportGap e i = e.a (i + 1) := by
    simp only [supportGap]
    exact Nat.add_sub_of_le (e.strictMono (Nat.lt_succ_self i)).le
  rw [← hendpoint,
    carryInt_across_supportGap R (e.a i) (supportGap e i) hgap]
  simp only [AffineLine.transform]
  rw [hQ, hr, hx]
  ring

theorem AffineLine.transformWord_contains_enumerationGapWord (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i n : ℕ)
    (hcontains : line.Contains (e.a i) (carryInt R (e.a i))) :
    (line.transformWord Q (enumerationGapWord e i n)).Contains
      (e.a (i + n)) (carryInt R (e.a (i + n))) := by
  induction n generalizing i line with
  | zero => simpa [enumerationGapWord, AffineLine.transformWord] using hcontains
  | succ n ih =>
      rw [enumerationGapWord_succ]
      simp only [AffineLine.transformWord]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (line := line.transform Q (supportGap e i))
          (line.contains_transform_supportGap Q R hQ e i hcontains)

/-- Iterating a genuine support run preserves one fixed original integer
parameter through every raw affine transformation. -/
theorem AffineLine.transformWord_parameter_enumerationGapWord (Q : ℕ)
    (R : RationalSupport) (hQ : R.eta.den = Q)
    (e : SupportEnumeration R.S) (line : AffineLine) (i n : ℕ) (t : ℤ)
    (hx : (e.a i : ℤ) = line.A + line.H * t)
    (hr : carryInt R (e.a i) = line.C + line.K * t) :
    let finish := line.transformWord Q (enumerationGapWord e i n)
    (e.a (i + n) : ℤ) = finish.A + finish.H * t ∧
      carryInt R (e.a (i + n)) = finish.C + finish.K * t := by
  induction n generalizing i line with
  | zero => simpa [enumerationGapWord, AffineLine.transformWord] using And.intro hx hr
  | succ n ih =>
      rw [enumerationGapWord_succ]
      simp only [AffineLine.transformWord]
      obtain ⟨hxnext, hrnext⟩ :=
        line.transform_supportGap_parameter Q R hQ e i t hx hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (line := line.transform Q (supportGap e i))
          hxnext hrnext

theorem occurrence_transformWord_contains_actualPrefix
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q) (hsk : W.s ≤ k)
    (hk : k ∈ highAnchors W Z0) (line : AffineLine)
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) line)
    (before : GapWord)
    (hbefore : before.IsPrefix (actualPostPrefixGaps W k)) :
    (line.transformWord Q before).Contains
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + before.length))
      (carryInt W.rational (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + before.length))) := by
  let i := k - W.s
  let p := initialLongPrefix W k
  let j := i + p.length
  have hpword : p = enumerationGapWord W.enumeration i p.length := by
    exact initialPrefix_eq_enumerationGapWord W Z0 k p hk rfl
  have hpspan := enumerationGapWord_span W.enumeration i p.length
  rw [← hpword] at hpspan
  have hx : W.enumeration.a i + p.span = W.enumeration.a j := by
    dsimp [j]
    have hmono := W.enumeration.strictMono.monotone
      (show i ≤ i + p.length by omega)
    omega
  have hbase : line.Contains (W.enumeration.a j)
      (carryInt W.rational (W.enumeration.a j)) := by
    rw [← hx]
    exact hoccurrence k hk rfl
  have hbeforeWord : before =
      enumerationGapWord W.enumeration j before.length := by
    simpa [i, p, j] using
      prefix_actualPostPrefixGaps_eq_enumerationGapWord
        W Z0 k hsk hk before hbefore
  rw [hbeforeWord]
  simpa [i, p, j, Nat.add_assoc, enumerationGapWord] using
    line.transformWord_contains_enumerationGapWord Q W.rational hden
      W.enumeration j before.length hbase

/-- The stabilized segment word in valid anchor data is the literal support
gap run beginning after `before`; it cannot be replaced by an unrelated word. -/
theorem AnchorInteriorData.segmentGaps_eq_enumerationGapWord
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k) :
    data.segment.gaps = enumerationGapWord W.enumeration
      (k - W.s + (initialLongPrefix W k).length + data.before.length)
      data.segment.gaps.length := by
  rcases hvalid.2.2.2.2.2.1 with ⟨after, hactual⟩
  have hbeforePrefix : data.before.IsPrefix (actualPostPrefixGaps W k) := by
    exact ⟨data.segment.gaps ++ after,
      by simpa [List.append_assoc] using hactual.symm⟩
  have htotalPrefix :
      (data.before ++ data.segment.gaps).IsPrefix
        (actualPostPrefixGaps W k) := by
    exact ⟨after, hactual.symm⟩
  have hbefore :=
    prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k
      hvalid.1 hvalid.2.1 data.before hbeforePrefix
  have htotal :=
    prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k
      hvalid.1 hvalid.2.1 (data.before ++ data.segment.gaps) htotalPrefix
  have hsplit := enumerationGapWord_append W.enumeration
    (k - W.s + (initialLongPrefix W k).length)
    data.before.length data.segment.gaps.length
  simp only [List.length_append] at htotal
  rw [hsplit, ← hbefore] at htotal
  exact List.append_right_injective data.before htotal

/-- The longest initial subword for which every successive state remains in
the open slope interval.  This depends only on the anchor word and its locked
line, never on the threshold coordinate. -/
def maximalInteriorPrefix (Q : ℕ) (line : AffineLine) : GapWord → GapWord
  | [] => []
  | g :: gs =>
      if classifySlope ((line.transform Q g).slope Q) = .interior then
        g :: maximalInteriorPrefix Q (line.transform Q g) gs
      else []

theorem maximalInteriorPrefix_isPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (maximalInteriorPrefix Q line word).IsPrefix word := by
  induction word generalizing line with
  | nil => simp [maximalInteriorPrefix]
  | cons g gs ih =>
      simp only [maximalInteriorPrefix]
      split_ifs
      · rcases ih (line.transform Q g) with ⟨tail, htail⟩
        exact ⟨tail, by simpa using congrArg (List.cons g) htail⟩
      · exact List.nil_prefix

theorem isInteriorTrajectory_iff_transformWord (Q : ℕ)
    (line : AffineLine) (word : GapWord) :
    IsInteriorTrajectory Q line word ↔
      ∀ r ≤ word.length,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) =
          .interior := by
  constructor
  · intro h r hr
    obtain ⟨state, htrajectory, hinterior⟩ := h r hr
    have hstate :=
      (sharedGapTrajectory_iff_transformWord Q line _ _).mp htrajectory
    subst state
    exact hinterior
  · intro h r hr
    exact ⟨line.transformWord Q (word.take r),
      (sharedGapTrajectory_iff_transformWord Q line _ _).mpr rfl, h r hr⟩

theorem isInteriorTrajectory_cons_iff (Q : ℕ) (line : AffineLine)
    (g : ℕ) (word : GapWord) :
    IsInteriorTrajectory Q line (g :: word) ↔
      classifySlope (line.slope Q) = .interior ∧
      classifySlope ((line.transform Q g).slope Q) = .interior ∧
      IsInteriorTrajectory Q (line.transform Q g) word := by
  rw [isInteriorTrajectory_iff_transformWord,
    isInteriorTrajectory_iff_transformWord]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [AffineLine.transformWord] using h 0 (by simp)
    · simpa [AffineLine.transformWord] using h 1 (by simp)
    · intro r hr
      have hall := h (r + 1) (by simp; omega)
      simpa [AffineLine.transformWord_append, AffineLine.transformWord] using hall
  · rintro ⟨hzero, _hone, htail⟩ r hr
    cases r with
    | zero => simpa [AffineLine.transformWord] using hzero
    | succ r =>
        simpa [AffineLine.transformWord_append, AffineLine.transformWord] using
          htail r (by simp at hr; omega)

theorem maximalInteriorPrefix_interior (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hline : classifySlope (line.slope Q) = .interior) :
    IsInteriorTrajectory Q line (maximalInteriorPrefix Q line word) := by
  induction word generalizing line with
  | nil =>
      rw [isInteriorTrajectory_iff_transformWord]
      simpa [maximalInteriorPrefix, AffineLine.transformWord] using hline
  | cons g gs ih =>
      simp only [maximalInteriorPrefix]
      by_cases hnext : classifySlope ((line.transform Q g).slope Q) = .interior
      · rw [if_pos hnext, isInteriorTrajectory_cons_iff]
        exact ⟨hline, hnext, ih (line.transform Q g) hnext⟩
      · rw [if_neg hnext, isInteriorTrajectory_iff_transformWord]
        simpa [AffineLine.transformWord] using hline

theorem maximalInteriorPrefix_maximal (Q : ℕ) (line : AffineLine)
    (word u : GapWord) (hp : u.IsPrefix word)
    (hinterior : IsInteriorTrajectory Q line u) :
    u.IsPrefix (maximalInteriorPrefix Q line word) := by
  induction u generalizing line word with
  | nil => exact List.nil_prefix
  | cons g gs ih =>
      obtain ⟨tail, rfl⟩ := hp
      have hparts := (isInteriorTrajectory_cons_iff Q line g gs).mp hinterior
      change (g :: gs).IsPrefix
        (if classifySlope ((line.transform Q g).slope Q) = .interior then
          g :: maximalInteriorPrefix Q (line.transform Q g) (gs ++ tail)
        else [])
      rw [if_pos hparts.2.1]
      rcases ih (line.transform Q g) (gs ++ tail)
          (List.prefix_append gs tail) hparts.2.2 with ⟨rest, hrest⟩
      exact ⟨rest, by simpa using congrArg (List.cons g) hrest⟩

theorem isInteriorTrajectory_append_iff (Q : ℕ) (line : AffineLine)
    (u v : GapWord) :
    IsInteriorTrajectory Q line (u ++ v) ↔
      IsInteriorTrajectory Q line u ∧
        IsInteriorTrajectory Q (line.transformWord Q u) v := by
  induction u generalizing line with
  | nil =>
      simp only [List.nil_append, AffineLine.transformWord]
      constructor
      · intro h
        have hzero :=
          (isInteriorTrajectory_iff_transformWord Q line v).mp h 0 (by simp)
        refine ⟨?_, h⟩
        rw [isInteriorTrajectory_iff_transformWord]
        simpa [AffineLine.transformWord] using hzero
      · exact fun h => h.2
  | cons g gs ih =>
      simp only [List.cons_append]
      rw [isInteriorTrajectory_cons_iff,
        isInteriorTrajectory_cons_iff, ih]
      simp only [AffineLine.transformWord]
      tauto

/-- Primitive reduction of a raw affine parameterization, retaining its
chosen origin. -/
def AffineLine.primitiveReduction (line : AffineLine) : AffineLine where
  A := line.A
  C := line.C
  H := line.primitiveHorizontalInt
  K := line.primitiveVertical
  H_pos := line.primitiveHorizontalInt_pos

theorem AffineLine.primitiveReduction_primitive (line : AffineLine) :
    Int.gcd line.primitiveReduction.H line.primitiveReduction.K = 1 := by
  change Int.gcd
    (line.H / (line.directionGCD : ℤ))
    (line.K / (line.directionGCD : ℤ)) = 1
  exact Int.gcd_div_gcd_div_gcd line.directionGCD_pos

theorem AffineLine.primitiveReduction_canonicalGeometricLine
    (line : AffineLine) :
    line.primitiveReduction.canonicalGeometricLine =
      line.canonicalGeometricLine := by
  have hdir : line.primitiveReduction.directionGCD = 1 :=
    line.primitiveReduction_primitive
  rw [GeometricLine.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · change ((line.primitiveReduction.H /
      (line.primitiveReduction.directionGCD : ℤ)).natAbs) =
        line.primitiveHorizontalInt.natAbs
    rw [hdir]
    simp [AffineLine.primitiveReduction]
  · change line.primitiveReduction.K /
      (line.primitiveReduction.directionGCD : ℤ) = line.primitiveVertical
    rw [hdir]
    simp [AffineLine.primitiveReduction]
  · change line.primitiveReduction.interceptNumerator /
      (line.primitiveReduction.directionGCD : ℤ) =
        line.interceptNumerator / (line.directionGCD : ℤ)
    rw [hdir]
    simp only [Nat.cast_one, Int.ediv_one]
    change line.primitiveHorizontalInt * line.C -
        line.primitiveVertical * line.A =
      line.interceptNumerator / (line.directionGCD : ℤ)
    unfold AffineLine.primitiveHorizontalInt AffineLine.primitiveVertical
      AffineLine.interceptNumerator AffineLine.directionGCD
    have hHfactor :
        line.H / (Int.gcd line.H line.K : ℤ) *
            (Int.gcd line.H line.K : ℤ) = line.H :=
      Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
    have hKfactor :
        line.K / (Int.gcd line.H line.K : ℤ) *
            (Int.gcd line.H line.K : ℤ) = line.K :=
      Int.ediv_mul_cancel (Int.gcd_dvd_right line.H line.K)
    have hdvd : (Int.gcd line.H line.K : ℤ) ∣
        line.H * line.C - line.K * line.A := by
      exact dvd_sub
        (dvd_mul_of_dvd_left (Int.gcd_dvd_left line.H line.K) line.C)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right line.H line.K) line.A)
    have hdne : (Int.gcd line.H line.K : ℤ) ≠ 0 := by
      exact_mod_cast line.directionGCD_pos.ne'
    apply mul_right_cancel₀ hdne
    rw [Int.ediv_mul_cancel hdvd]
    calc
      (line.H / (Int.gcd line.H line.K : ℤ) * line.C -
          line.K / (Int.gcd line.H line.K : ℤ) * line.A) *
            (Int.gcd line.H line.K : ℤ) =
          (line.H / (Int.gcd line.H line.K : ℤ) *
              (Int.gcd line.H line.K : ℤ)) * line.C -
            (line.K / (Int.gcd line.H line.K : ℤ) *
              (Int.gcd line.H line.K : ℤ)) * line.A := by ring
      _ = line.H * line.C - line.K * line.A := by
        rw [hHfactor, hKfactor]

theorem AnchorInteriorData.segmentStart_contains_actual
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k) :
    data.segment.startLine.Contains
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length))
      (carryInt W.rational (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length))) := by
  rcases hvalid.2.2.2.2.2.1 with ⟨after, hactual⟩
  have hbeforePrefix : data.before.IsPrefix (actualPostPrefixGaps W k) := by
    exact ⟨data.segment.gaps ++ after,
      by simpa [List.append_assoc] using hactual.symm⟩
  have hraw := occurrence_transformWord_contains_actualPrefix
    Q W Z0 k hden hvalid.1 hvalid.2.1 data.baseLine
      hvalid.2.2.2.1 data.before hbeforePrefix
  have hcanonical :=
    (data.baseLine.transformWord Q data.before).contains_canonicalGeometricLine
      _ _ hraw
  rw [hvalid.2.2.2.2.2.2] at hcanonical
  apply data.segment.startLine.contains_of_canonicalGeometricLine_of_primitive
    hvalid.2.2.2.2.1.2.2.1
  exact hcanonical

theorem odd_den_pow_mul_of_padicValNat_le (μ : ℚ) (G : ℕ)
    (hG : padicValNat 2 μ.den ≤ G) :
    Odd (((2 : ℚ) ^ G * μ).den) := by
  rw [Rat.mul_den]
  simp only [Rat.den_pow, Rat.den_ofNat, one_pow, one_mul,
    Rat.num_pow, Rat.num_ofNat]
  let a := padicValNat 2 μ.den
  let oddPart := μ.den.divMaxPow 2
  let d := Nat.gcd ((2 : ℤ) ^ G * μ.num).natAbs μ.den
  have hden : 2 ^ a * oddPart = μ.den := by
    exact Nat.pow_padicValNat_mul_divMaxPow 2 μ.den
  have hpowDiv : 2 ^ a ∣ 2 ^ G * μ.num.natAbs := by
    exact (Nat.pow_dvd_pow 2 hG).trans (dvd_mul_right _ _)
  have habs : ((2 : ℤ) ^ G * μ.num).natAbs =
      2 ^ G * μ.num.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  have hpowDen : 2 ^ a ∣ μ.den := pow_padicValNat_dvd
  have hpowGcd : 2 ^ a ∣ d := by
    exact Nat.dvd_gcd (by simpa [d, habs] using hpowDiv) hpowDen
  have hdDiv : d ∣ μ.den := Nat.gcd_dvd_right _ _
  have hquotDiv : μ.den / d ∣ oddPart := by
    have hmain := Nat.div_dvd_div_left hdDiv hpowGcd
    have hpowPos : 0 < 2 ^ a := pow_pos (by norm_num) _
    have hoddEq : μ.den / 2 ^ a = oddPart := by
      rw [← hden, Nat.mul_comm, Nat.mul_div_left _ hpowPos]
    simpa [hoddEq] using hmain
  have hoddPart : Odd oddPart := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact Nat.not_dvd_divMaxPow (by norm_num) μ.den_ne_zero
  simpa [d] using Odd.of_dvd_nat hoddPart hquotDiv

theorem den_pow_mul_sub_one_of_odd (μ : ℚ) (g : ℕ)
    (hodd : Odd μ.den) :
    ((2 : ℚ) ^ g * μ - 1).den = μ.den := by
  rw [Rat.sub_ofNat_den, Rat.mul_den]
  simp only [Rat.den_pow, Rat.den_ofNat, one_pow, one_mul,
    Rat.num_pow, Rat.num_ofNat]
  have htwo : Nat.Coprime (2 ^ g) μ.den :=
    (Nat.coprime_two_left.mpr hodd).pow_left g
  have hprod : Nat.Coprime (2 ^ g * μ.num.natAbs) μ.den :=
    htwo.mul_left μ.reduced
  rw [Int.natAbs_mul, Int.natAbs_pow]
  norm_num
  rw [hprod.gcd_eq_one, Nat.div_one]

theorem odd_num_pow_mul_sub_one (μ : ℚ) (g : ℕ) (hg : 0 < g)
    (hodd : Odd μ.den) :
    Odd (((2 : ℚ) ^ g * μ - 1).num) := by
  let ν := (2 : ℚ) ^ g * μ - 1
  have hden : ν.den = μ.den := den_pow_mul_sub_one_of_odd μ g hodd
  have hrepr : ν =
      ((2 : ℚ) ^ g * (μ.num : ℚ) - μ.den) / μ.den := by
    dsimp [ν]
    calc
      (2 : ℚ) ^ g * μ - 1 =
          (2 : ℚ) ^ g * ((μ.num : ℚ) / μ.den) - 1 := by
            rw [μ.num_div_den]
      _ = ((2 : ℚ) ^ g * (μ.num : ℚ) - μ.den) / μ.den := by
        field_simp
  have hnumRat : (ν.num : ℚ) =
      (2 : ℚ) ^ g * (μ.num : ℚ) - μ.den := by
    have hcanonical := ν.num_div_den
    rw [hden] at hcanonical
    conv_rhs at hcanonical => rw [hrepr]
    field_simp at hcanonical
    exact hcanonical
  have hnumInt : ν.num = (2 : ℤ) ^ g * μ.num - μ.den := by
    exact_mod_cast hnumRat
  rw [hnumInt]
  have hevenPow : Even ((2 : ℤ) ^ g) :=
    Even.pow_of_ne_zero (even_two : Even (2 : ℤ)) hg.ne'
  have hevenProduct : Even ((2 : ℤ) ^ g * μ.num) :=
    hevenPow.mul_right μ.num
  exact hevenProduct.sub_odd (by exact_mod_cast hodd)

def stabilizationSlopeOffset : GapWord → ℕ
  | [] => 0
  | _g :: gs => 2 ^ GapWord.span gs + stabilizationSlopeOffset gs

theorem AffineLine.transformWord_slope_formula (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) :
    (line.transformWord Q word).slope Q =
      (2 : ℚ) ^ word.span * line.slope Q - stabilizationSlopeOffset word := by
  induction word generalizing line with
  | nil => simp [AffineLine.transformWord, GapWord.span, stabilizationSlopeOffset]
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      rw [ih, AffineLine.slope_transform Q hQ]
      simp only [GapWord.span, List.sum_cons, stabilizationSlopeOffset, pow_add]
      push_cast
      ring

theorem AffineLine.transformWord_den_odd_of_padicVal_le_span
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (hspan : padicValNat 2 (line.slope Q).den ≤ word.span) :
    Odd ((line.transformWord Q word).slope Q).den := by
  rw [line.transformWord_slope_formula Q hQ]
  have hden :
      ((2 : ℚ) ^ word.span * line.slope Q -
          stabilizationSlopeOffset word).den =
        ((2 : ℚ) ^ word.span * line.slope Q).den :=
    Rat.sub_ofNat_den _ _
  rw [hden]
  exact odd_den_pow_mul_of_padicValNat_le (line.slope Q) word.span hspan

theorem AffineLine.transformWord_odd_stable (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hpositive : word.Positive)
    (hdenOdd : Odd (line.slope Q).den)
    (hnumOdd : Odd (line.slope Q).num) :
    ((line.transformWord Q word).slope Q).den = (line.slope Q).den ∧
      Odd ((line.transformWord Q word).slope Q).num := by
  induction word generalizing line with
  | nil => exact ⟨rfl, hnumOdd⟩
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgs : GapWord.Positive gs := by
        intro x hx
        exact hpositive x (by simp [hx])
      simp only [AffineLine.transformWord]
      have hden : ((line.transform Q g).slope Q).den =
          (line.slope Q).den := by
        rw [AffineLine.slope_transform Q hQ]
        exact den_pow_mul_sub_one_of_odd (line.slope Q) g hdenOdd
      have hnextDenOdd : Odd ((line.transform Q g).slope Q).den := by
        rw [hden]
        exact hdenOdd
      have hnextNumOdd : Odd ((line.transform Q g).slope Q).num := by
        rw [AffineLine.slope_transform Q hQ]
        exact odd_num_pow_mul_sub_one (line.slope Q) g hg hdenOdd
      obtain ⟨hfinalDen, hfinalNum⟩ :=
        ih (line.transform Q g) hgs hnextDenOdd hnextNumOdd
      exact ⟨hfinalDen.trans hden, hfinalNum⟩

/-- The denominator of a primitive normalized direction determines its
positive horizontal step. -/
theorem primitiveDirectionDenominator (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1) :
    line.H.natAbs = (line.slope Q).den /
      Nat.gcd (line.slope Q).den Q := by
  have hHne : line.H ≠ 0 := ne_of_gt line.H_pos
  have hHnat : 0 < line.H.natAbs := Int.natAbs_pos.mpr hHne
  have hcop : Nat.Coprime line.H.natAbs line.K.natAbs := by
    exact hprimitive
  have hQint : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hden : (line.slope Q).den =
      Q * line.H.natAbs / Nat.gcd Q line.K.natAbs := by
    rw [AffineLine.slope]
    have hcast : (Q : ℚ) * (line.H : ℚ) =
        ((((Q : ℤ) * line.H : ℤ) : ℚ)) := by norm_num
    rw [hcast]
    rw [← Rat.divInt_eq_div, Rat.den_divInt,
      if_neg (mul_ne_zero hQint hHne)]
    simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.gcd_def]
    rw [hcop.gcd_mul_right_cancel Q]
  rw [hden]
  exact show line.H.natAbs =
      (Q * line.H.natAbs / Nat.gcd Q line.K.natAbs) /
        Nat.gcd (Q * line.H.natAbs / Nat.gcd Q line.K.natAbs) Q from by
    let d := Nat.gcd Q line.K.natAbs
    let e := Q / d
    have hdQ : d ∣ Q := Nat.gcd_dvd_left Q line.K.natAbs
    have hdK : d ∣ line.K.natAbs := Nat.gcd_dvd_right Q line.K.natAbs
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left line.K.natAbs hQ
    have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hQ hdQ) hdpos
    have hQeq : e * d = Q := by
      dsimp [e]
      exact Nat.div_mul_cancel hdQ
    have hcopHd : Nat.Coprime line.H.natAbs d :=
      Nat.Coprime.of_dvd_right hdK hcop
    have hq : Q * line.H.natAbs / d = e * line.H.natAbs := by
      rw [← hQeq]
      calc
        e * d * line.H.natAbs / d =
            (e * line.H.natAbs) * d / d := by
          rw [Nat.mul_right_comm e d line.H.natAbs]
        _ = e * line.H.natAbs := Nat.mul_div_left _ hdpos
    rw [show Nat.gcd Q line.K.natAbs = d by rfl, hq, ← hQeq,
      Nat.gcd_mul_left, hcopHd.gcd_eq_one, Nat.mul_one]
    have hcancel : e * line.H.natAbs / e = line.H.natAbs := by
      simpa [Nat.mul_comm] using Nat.mul_div_left line.H.natAbs hepos
    exact hcancel.symm

theorem AffineLine.transformWord_H (Q : ℕ) (line : AffineLine)
    (word : GapWord) : (line.transformWord Q word).H = line.H := by
  induction word generalizing line with
  | nil => rfl
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      rw [ih]
      rfl

theorem stableSegment_span_firstPrefixAtLeast_le_add (w : GapWord) (bound cap : ℕ)
    (hcap : ∀ g ∈ w, g ≤ cap) :
    (w.firstPrefixAtLeast bound).span ≤ bound + cap := by
  induction w generalizing bound with
  | nil => simp [GapWord.firstPrefixAtLeast, GapWord.span]
  | cons g gs ih =>
      have hgcap : g ≤ cap := hcap g (by simp)
      have htailcap : ∀ x ∈ gs, x ≤ cap := by
        intro x hx
        exact hcap x (by simp [hx])
      simp only [GapWord.firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg, GapWord.span]
        omega
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have hrec : (GapWord.firstPrefixAtLeast gs (bound - g)).sum ≤
            (bound - g) + cap := by
          simpa only [GapWord.span] using ih (bound - g) htailcap
        omega

theorem stableSegment_prefix_append_drop {α : Type*} (u w : List α)
    (hprefix : u.IsPrefix w) : u ++ w.drop u.length = w := by
  nth_rw 1 [List.prefix_iff_eq_take.mp hprefix]
  exact List.take_append_drop _ _

def denominatorStabilizationPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  word.firstPrefixAtLeast (padicValNat 2 (line.slope Q).den)

def parityStabilizationPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  let denPrefix := denominatorStabilizationPrefix Q line word
  let remainder := word.drop denPrefix.length
  if Odd ((line.transformWord Q denPrefix).slope Q).num then []
  else remainder.take 1

def stabilizationPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  denominatorStabilizationPrefix Q line word ++ parityStabilizationPrefix Q line word

def stabilizedGaps (Q : ℕ) (line : AffineLine)
    (word : GapWord) : GapWord :=
  word.drop (stabilizationPrefix Q line word).length

theorem denominatorStabilizationPrefix_isPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (denominatorStabilizationPrefix Q line word).IsPrefix word := by
  exact GapWord.firstPrefixAtLeast_isPrefix _ _

theorem parityStabilizationPrefix_isPrefix_remainder (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (parityStabilizationPrefix Q line word).IsPrefix
      (word.drop (denominatorStabilizationPrefix Q line word).length) := by
  change (if Odd ((line.transformWord Q
      (denominatorStabilizationPrefix Q line word)).slope Q).num then []
    else (word.drop (denominatorStabilizationPrefix Q line word).length).take 1).IsPrefix _
  by_cases hodd : Odd ((line.transformWord Q
      (denominatorStabilizationPrefix Q line word)).slope Q).num
  · rw [if_pos hodd]
    exact List.nil_prefix
  · rw [if_neg hodd]
    exact List.take_prefix 1 _

theorem stabilizationPrefix_append_stabilizedGaps
    (Q : ℕ) (line : AffineLine) (word : GapWord) :
    stabilizationPrefix Q line word ++
        stabilizedGaps Q line word = word := by
  let d := denominatorStabilizationPrefix Q line word
  let p := parityStabilizationPrefix Q line word
  have hd : d ++ word.drop d.length = word :=
    stableSegment_prefix_append_drop d word (denominatorStabilizationPrefix_isPrefix Q line word)
  have hp : p ++ (word.drop d.length).drop p.length = word.drop d.length :=
    stableSegment_prefix_append_drop p (word.drop d.length)
      (parityStabilizationPrefix_isPrefix_remainder Q line word)
  change (d ++ p) ++ word.drop (d ++ p).length = word
  rw [List.length_append, ← List.drop_drop]
  rw [List.append_assoc, hp, hd]

theorem stabilizationPrefix_isPrefix (Q : ℕ) (line : AffineLine)
    (word : GapWord) :
    (stabilizationPrefix Q line word).IsPrefix word := by
  exact ⟨stabilizedGaps Q line word,
    stabilizationPrefix_append_stabilizedGaps Q line word⟩

theorem stabilizationPrefix_positive (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hpositive : word.Positive) :
    (stabilizationPrefix Q line word).Positive := by
  intro g hg
  exact hpositive g ((stabilizationPrefix_isPrefix Q line word).mem hg)

theorem stabilizedGaps_positive (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hpositive : word.Positive) :
    (stabilizedGaps Q line word).Positive := by
  intro g hg
  exact hpositive g (List.mem_of_mem_drop hg)

theorem stabilizationPrefix_span_le (Q cap : ℕ) (line : AffineLine)
    (word : GapWord) (hcap : ∀ g ∈ word, g ≤ cap) :
    (stabilizationPrefix Q line word).span ≤
      padicValNat 2 (line.slope Q).den + 2 * cap := by
  let d := denominatorStabilizationPrefix Q line word
  let p := parityStabilizationPrefix Q line word
  have hdspan : d.span ≤ padicValNat 2 (line.slope Q).den + cap := by
    exact stableSegment_span_firstPrefixAtLeast_le_add word _ cap hcap
  have hpspan : p.span ≤ cap := by
    change (parityStabilizationPrefix Q line word).span ≤ cap
    unfold parityStabilizationPrefix
    by_cases hodd : Odd ((line.transformWord Q
        (denominatorStabilizationPrefix Q line word)).slope Q).num
    · rw [if_pos hodd]
      simp [GapWord.span]
    · rw [if_neg hodd]
      let remainder := word.drop d.length
      change GapWord.span (remainder.take 1) ≤ cap
      have hremcap : ∀ x ∈ remainder, x ≤ cap := by
        intro x hx
        exact hcap x (List.mem_of_mem_drop hx)
      cases hrem : remainder with
      | nil => simp [GapWord.span]
      | cons g gs =>
          simp only [List.take, GapWord.span, List.sum_cons, List.sum_nil,
            add_zero]
          apply hremcap g
          rw [hrem]
          exact List.mem_cons_self
  change GapWord.span (d ++ p) ≤ _
  simp only [GapWord.span, List.sum_append] at hdspan hpspan ⊢
  omega

theorem stableSegment_primitiveReduction_slope (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) : line.primitiveReduction.slope Q = line.slope Q := by
  calc
    line.primitiveReduction.slope Q =
        line.primitiveReduction.canonicalGeometricLine.slope Q :=
      (AffineLine.canonicalGeometricLine_slope Q hQ line.primitiveReduction).symm
    _ = line.canonicalGeometricLine.slope Q := by
      rw [line.primitiveReduction_canonicalGeometricLine]
    _ = line.slope Q := AffineLine.canonicalGeometricLine_slope Q hQ line

theorem stableSegment_one_lt_den_of_mem_Ioo (μ : ℚ) (hμ : μ ∈ Set.Ioo (0 : ℚ) 1) :
    1 < μ.den := by
  have hnumPos : 0 < μ.num := Rat.num_pos.mpr hμ.1
  have hnumPos' : (1 : ℤ) ≤ μ.num := (Int.add_one_le_iff).2 hnumPos
  have hnumLtDenQ : (μ.num : ℚ) < μ.den := by
    have hdenPos : (0 : ℚ) < μ.den := by positivity
    apply (div_lt_one hdenPos).mp
    rw [μ.num_div_den]
    exact hμ.2
  have hnumLtDen : μ.num < (μ.den : ℤ) := by exact_mod_cast hnumLtDenQ
  omega

theorem stableSegment_classifySlope_eq_interior_iff (μ : ℚ) :
    classifySlope μ = .interior ↔ μ ∈ Set.Ioo (0 : ℚ) 1 := by
  by_cases hzero : μ = 0
  · simp [classifySlope, hzero]
  by_cases hone : μ = 1
  · simp [classifySlope, hone]
  by_cases hi : 0 < μ ∧ μ < 1
  · simp [classifySlope, hzero, hone, hi]
  · simp [classifySlope, hzero, hone, hi]

theorem stabilizationPrefix_odd (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hpositive : word.Positive)
    (hcross : padicValNat 2 (line.slope Q).den ≤ word.span)
    (hproper : (stabilizationPrefix Q line word).span < word.span) :
    let finish := line.transformWord Q (stabilizationPrefix Q line word)
    Odd (finish.slope Q).den ∧ Odd (finish.slope Q).num := by
  let d := denominatorStabilizationPrefix Q line word
  let remainder := word.drop d.length
  let afterDen := line.transformWord Q d
  have hdspan : padicValNat 2 (line.slope Q).den ≤ d.span := by
    exact GapWord.span_firstPrefixAtLeast_ge word _ hcross
  have hdOdd : Odd (afterDen.slope Q).den := by
    exact line.transformWord_den_odd_of_padicVal_le_span Q hQ d hdspan
  by_cases hnum : Odd (afterDen.slope Q).num
  · have hbefore : stabilizationPrefix Q line word = d := by
      simp [stabilizationPrefix, parityStabilizationPrefix, d, afterDen, hnum]
    simpa [hbefore, afterDen] using And.intro hdOdd hnum
  · have hremNonempty : remainder ≠ [] := by
      intro hrem
      have hdEq : d = word := by
        have happ := stableSegment_prefix_append_drop d word
          (denominatorStabilizationPrefix_isPrefix Q line word)
        simpa [remainder, hrem] using happ
      have hbefore : stabilizationPrefix Q line word = d := by
        simp [stabilizationPrefix, parityStabilizationPrefix, d, remainder,
          afterDen, hnum, hrem]
      rw [hbefore, hdEq] at hproper
      exact (Nat.lt_irrefl _ hproper)
    obtain ⟨g, gs, hrem⟩ := List.exists_cons_of_ne_nil hremNonempty
    have hgmem : g ∈ word := by
      have hgdrop : g ∈ word.drop d.length := by
        change g ∈ remainder
        rw [hrem]
        exact List.mem_cons_self
      exact List.mem_of_mem_drop hgdrop
    have hg : 0 < g := hpositive g hgmem
    have hbefore : stabilizationPrefix Q line word = d ++ [g] := by
      simp [stabilizationPrefix, parityStabilizationPrefix, d, remainder,
        afterDen, hnum, hrem]
    have hslope :
        (line.transformWord Q (stabilizationPrefix Q line word)).slope Q =
          (afterDen.transform Q g).slope Q := by
      rw [hbefore, AffineLine.transformWord_append]
      rfl
    dsimp only
    rw [hslope, AffineLine.slope_transform Q hQ]
    exact ⟨by
        rw [den_pow_mul_sub_one_of_odd (afterDen.slope Q) g hdOdd]
        exact hdOdd,
      odd_num_pow_mul_sub_one (afterDen.slope Q) g hg hdOdd⟩

def stabilizedSegment (Q : ℕ) (line : AffineLine)
    (word : GapWord) : OddDenominatorSegment :=
  let before := stabilizationPrefix Q line word
  let raw := line.transformWord Q before
  let start := raw.primitiveReduction
  let gaps := stabilizedGaps Q line word
  { startLine := start
    gaps := gaps
    slopes := OddDenominatorSegment.slopeTrace Q start gaps
    q := (raw.slope Q).den }

theorem stabilizedSegment_valid (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hpositive : word.Positive)
    (hinterior : IsInteriorTrajectory Q line word)
    (hcross : padicValNat 2 (line.slope Q).den ≤ word.span)
    (hproper : (stabilizationPrefix Q line word).span < word.span) :
    (stabilizedSegment Q line word).Valid Q := by
  let before := stabilizationPrefix Q line word
  let raw := line.transformWord Q before
  let start := raw.primitiveReduction
  let gaps := stabilizedGaps Q line word
  have hdecomp : before ++ gaps = word :=
    stabilizationPrefix_append_stabilizedGaps Q line word
  have hsplit :
      IsInteriorTrajectory Q line before ∧
        IsInteriorTrajectory Q raw gaps := by
    apply (isInteriorTrajectory_append_iff Q line before gaps).mp
    rw [hdecomp]
    exact hinterior
  have hrawInterior : classifySlope (raw.slope Q) = .interior := by
    have hzero := (isInteriorTrajectory_iff_transformWord Q raw gaps).mp
      hsplit.2 0 (by simp)
    simpa [AffineLine.transformWord] using hzero
  have hstartSlope : start.slope Q = raw.slope Q := by
    exact stableSegment_primitiveReduction_slope Q hQ raw
  have hstartInterior : classifySlope (start.slope Q) = .interior := by
    rw [hstartSlope]
    exact hrawInterior
  have hstartTrajectory : IsInteriorTrajectory Q start gaps := by
    rw [isInteriorTrajectory_iff_transformWord]
    intro r hr
    have hrawState :=
      (isInteriorTrajectory_iff_transformWord Q raw gaps).mp hsplit.2 r hr
    rw [start.transformWord_slope_eq_of_slope_eq Q hQ raw (gaps.take r)
      hstartSlope]
    exact hrawState
  have hoddRaw := stabilizationPrefix_odd Q hQ line word hpositive
    hcross hproper
  change Odd ((line.transformWord Q before).slope Q).den ∧
      Odd ((line.transformWord Q before).slope Q).num at hoddRaw
  have hoddStartDen : Odd (start.slope Q).den := by
    rw [hstartSlope]
    exact hoddRaw.1
  have hoddStartNum : Odd (start.slope Q).num := by
    rw [hstartSlope]
    exact hoddRaw.2
  have hgapsPositive : gaps.Positive :=
    stabilizedGaps_positive Q line word hpositive
  have hallOdd : ∀ r ≤ gaps.length,
      ((start.transformWord Q (gaps.take r)).slope Q).den =
          (start.slope Q).den ∧
        Odd ((start.transformWord Q (gaps.take r)).slope Q).num := by
    intro r hr
    apply start.transformWord_odd_stable Q hQ (gaps.take r)
    · intro g hg
      exact hgapsPositive g (List.mem_of_mem_take hg)
    · exact hoddStartDen
    · exact hoddStartNum
  have hqEq : (raw.slope Q).den = (start.slope Q).den := by
    rw [hstartSlope]
  have hstartIoo : start.slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
    (stableSegment_classifySlope_eq_interior_iff _).mp hstartInterior
  have hqOne : 1 < (raw.slope Q).den := by
    rw [hqEq]
    exact stableSegment_one_lt_den_of_mem_Ioo (start.slope Q) hstartIoo
  refine ⟨hQ, hgapsPositive, raw.primitiveReduction_primitive,
    rfl, hqOne, ?_, ?_⟩
  · exact hoddRaw.1
  · intro μ hμ
    change μ ∈ OddDenominatorSegment.slopeTrace Q start gaps at hμ
    unfold OddDenominatorSegment.slopeTrace at hμ
    rcases List.mem_map.mp hμ with ⟨r, hr, rfl⟩
    have hrle : r ≤ gaps.length := by
      rw [List.mem_range] at hr
      omega
    have hinteriorState :=
      (isInteriorTrajectory_iff_transformWord Q start gaps).mp
        hstartTrajectory r hrle
    have hoddState := hallOdd r hrle
    exact ⟨(stableSegment_classifySlope_eq_interior_iff _).mp hinteriorState,
      hoddState.1.trans hqEq.symm, hoddState.2⟩

def anchorInteriorWord (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (line : AffineLine) : GapWord :=
  maximalInteriorPrefix Q line (actualPostPrefixGaps W k)

def anchorInteriorData (Q : ℕ) (W : WindowSystem) (k : ℕ)
    (line : AffineLine) : AnchorInteriorData :=
  let word := anchorInteriorWord Q W k line
  { baseLine := line
    before := stabilizationPrefix Q line word
    segment := stabilizedSegment Q line word }

theorem anchorInteriorData_valid (Q : ℕ) (hQ : 0 < Q)
    (W : WindowSystem) (Z0 k : ℕ) (line : AffineLine)
    (hsk : W.s ≤ k) (hk : k ∈ highAnchors W Z0)
    (hfrequent : IsFrequentPrefix W Z0 (initialLongPrefix W k))
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) line)
    (hlineInterior : classifySlope (line.slope Q) = .interior)
    (hcross : padicValNat 2 (line.slope Q).den ≤
      (anchorInteriorWord Q W k line).span)
    (hproper : (stabilizationPrefix Q line
        (anchorInteriorWord Q W k line)).span <
      (anchorInteriorWord Q W k line).span) :
    (anchorInteriorData Q W k line).Valid Q W Z0 k := by
  let word := anchorInteriorWord Q W k line
  let before := stabilizationPrefix Q line word
  let segment := stabilizedSegment Q line word
  have hactualPositive : (actualPostPrefixGaps W k).Positive := by
    intro g hg
    exact rawWindowGapWord_positive W k g (List.mem_of_mem_drop hg)
  have hwordPrefix : word.IsPrefix (actualPostPrefixGaps W k) :=
    maximalInteriorPrefix_isPrefix Q line _
  have hwordPositive : word.Positive := by
    intro g hg
    exact hactualPositive g (hwordPrefix.mem hg)
  have hwordInterior : IsInteriorTrajectory Q line word :=
    maximalInteriorPrefix_interior Q line _ hlineInterior
  have hsegmentValid : segment.Valid Q := by
    exact stabilizedSegment_valid Q hQ line word hwordPositive
      hwordInterior (by simpa [word] using hcross)
      (by simpa [word, before] using hproper)
  rcases hwordPrefix with ⟨after, hafter⟩
  have hstabilized : before ++ segment.gaps = word := by
    exact stabilizationPrefix_append_stabilizedGaps Q line word
  refine ⟨hsk, hk, hfrequent, hoccurrence, hsegmentValid, ?_, ?_⟩
  · refine ⟨after, ?_⟩
    calc
      actualPostPrefixGaps W k = word ++ after := hafter.symm
      _ = (before ++ segment.gaps) ++ after := by rw [hstabilized]
      _ = before ++ segment.gaps ++ after := rfl
  · change (line.transformWord Q before).canonicalGeometricLine =
      (line.transformWord Q before).primitiveReduction.canonicalGeometricLine
    exact (line.transformWord Q before).primitiveReduction_canonicalGeometricLine.symm

theorem stableSegment_nat_log_mul_pow_two (C L : ℕ) (hC : 0 < C) :
    Nat.log 2 (C * 2 ^ L) = Nat.log 2 C + L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [pow_succ]
      rw [← Nat.mul_assoc, Nat.log_mul_base Nat.one_lt_two]
      · rw [ih]
        omega
      · exact mul_ne_zero hC.ne' (pow_ne_zero _ (by norm_num))

theorem stableSegment_primitiveReduction_H_le (line : AffineLine) :
    (line.primitiveReduction.H : ℝ) ≤ line.H := by
  have hfactor : line.primitiveHorizontalInt *
      (line.directionGCD : ℤ) = line.H :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  have hfactorReal : (line.primitiveHorizontalInt : ℝ) *
      (line.directionGCD : ℝ) = line.H := by
    exact_mod_cast hfactor
  have hdOne : (1 : ℝ) ≤ line.directionGCD := by
    exact_mod_cast line.directionGCD_pos
  have hpNonneg : (0 : ℝ) ≤ line.primitiveHorizontalInt := by
    exact_mod_cast line.primitiveHorizontalInt_pos.le
  change (line.primitiveHorizontalInt : ℝ) ≤ line.H
  nlinarith

theorem stableSegment_longInterior_anchorWord
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (base : AffineLine)
    (hden : W.rational.eta.den = Q)
    (hcutoff : 1 < frequencyCutoff W)
    (hbase : IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base)
    (hlong : LongInteriorPair W Z0 e) :
    classifySlope (base.slope Q) = .interior ∧
      W.excess e / 8 ≤ (anchorInteriorWord Q W e.1 base).span := by
  rcases hlong.2.2 with ⟨line, gaps, hcontinuation, hinterior, hspan⟩
  have hcanonical := occurrenceLines_canonical_eq_of_frequent W Z0
    (initialLongPrefix W e.1) hcutoff hlong.2.1 base line
    hbase hcontinuation.1
  have hslope : base.slope Q = line.slope Q := by
    calc
      base.slope Q = base.canonicalGeometricLine.slope Q :=
        (base.canonicalGeometricLine_slope Q hQ).symm
      _ = line.canonicalGeometricLine.slope Q := by rw [hcanonical]
      _ = line.slope Q := line.canonicalGeometricLine_slope Q hQ
  have hinteriorQ : IsInteriorTrajectory Q line gaps := by
    simpa only [hden] using hinterior
  have hlineInterior : classifySlope (line.slope Q) = .interior := by
    have hzero := (isInteriorTrajectory_iff_transformWord Q line gaps).mp
      hinteriorQ 0 (by simp)
    simpa [AffineLine.transformWord] using hzero
  have hbaseInterior : classifySlope (base.slope Q) = .interior := by
    rw [hslope]
    exact hlineInterior
  have hbaseTrajectory : IsInteriorTrajectory Q base gaps := by
    rw [isInteriorTrajectory_iff_transformWord]
    intro r hr
    have hstate := (isInteriorTrajectory_iff_transformWord Q line gaps).mp
      hinteriorQ r hr
    rw [base.transformWord_slope_eq_of_slope_eq Q hQ line
      (gaps.take r) hslope]
    exact hstate
  have hprefix : gaps.IsPrefix (actualPostPrefixGaps W e.1) :=
    hcontinuation.2.1
  have hmaxPrefix : gaps.IsPrefix
      (anchorInteriorWord Q W e.1 base) := by
    exact maximalInteriorPrefix_maximal Q base _ gaps hprefix hbaseTrajectory
  have hspanNat : gaps.span ≤
      (anchorInteriorWord Q W e.1 base).span := by
    rcases hmaxPrefix with ⟨tail, htail⟩
    rw [← htail]
    simp [GapWord.span]
  refine ⟨hbaseInterior, hspan.trans ?_⟩
  exact_mod_cast hspanNat

theorem stableSegment_stabilizationPrefix_span_le_four_levels
    (Q : ℕ) (hQ : 0 < Q) (gap : GapParams Q)
    (Clock : ℝ) (hClock : 0 < Clock)
    (W : WindowSystem) (L k : ℕ) (base : AffineLine)
    (hlevel : W.L = L)
    (hprimitive : Int.gcd base.H base.K = 1)
    (hheight : (base.H : ℝ) ≤
      Clock * W.X / frequencyCutoff W)
    (hfrequencyOne : (1 : ℝ) ≤ frequencyCutoff W)
    (hL : Nat.log 2 (Q * Nat.ceil Clock) +
      2 * (gap.Cgap + 1) ≤ L)
    (hcap : ∀ g ∈ actualPostPrefixGaps W k,
      g ≤ L + gap.Cgap + 1) :
    padicValNat 2 (base.slope Q).den ≤ 4 * L ∧
      (stabilizationPrefix Q base
        (anchorInteriorWord Q W k base)).span ≤ 4 * L := by
  have hfrequencyPos : (0 : ℝ) < frequencyCutoff W :=
    lt_of_lt_of_le zero_lt_one hfrequencyOne
  have hstepBase : (base.H : ℝ) ≤ Clock * W.X := by
    refine hheight.trans ?_
    rw [div_le_iff₀ hfrequencyPos]
    have hnonneg : (0 : ℝ) ≤ Clock * W.X := by positivity
    nlinarith
  have hHnatReal : (base.H.natAbs : ℝ) = (base.H : ℝ) := by
    have hHnatInt : (base.H.natAbs : ℤ) = base.H :=
      Int.natAbs_of_nonneg base.H_pos.le
    calc
      (base.H.natAbs : ℝ) = ((base.H.natAbs : ℤ) : ℝ) := by norm_num
      _ = (base.H : ℝ) := by rw [hHnatInt]
  have hClockCeil : Clock ≤ (Nat.ceil Clock : ℝ) := Nat.le_ceil Clock
  have hHceilReal : (base.H.natAbs : ℝ) ≤
      (Nat.ceil Clock : ℝ) * W.X := by
    rw [hHnatReal]
    have hXnonneg : (0 : ℝ) ≤ W.X := by positivity
    exact hstepBase.trans (mul_le_mul_of_nonneg_right hClockCeil hXnonneg)
  have hHceil : base.H.natAbs ≤ Nat.ceil Clock * W.X := by
    exact_mod_cast hHceilReal
  let q := (base.slope Q).den
  let d := Nat.gcd q Q
  have hdvd : d ∣ q := Nat.gcd_dvd_left q Q
  have hdQ : d ≤ Q := Nat.gcd_le_right q hQ
  have hqboundH : q ≤ base.H.natAbs * Q := by
    have hformula := primitiveDirectionDenominator Q hQ base hprimitive
    calc
      q = q / d * d := (Nat.div_mul_cancel hdvd).symm
      _ ≤ q / d * Q := Nat.mul_le_mul_left _ hdQ
      _ = base.H.natAbs * Q := by rw [hformula]
  have hqbound : q ≤ (Q * Nat.ceil Clock) * 2 ^ L := by
    have hX : W.X = 2 ^ L := by
      rw [WindowSystem.X, dyadicScale, hlevel]
    rw [hX] at hHceil
    calc
      q ≤ base.H.natAbs * Q := hqboundH
      _ ≤ (Nat.ceil Clock * 2 ^ L) * Q :=
        Nat.mul_le_mul_right Q hHceil
      _ = (Q * Nat.ceil Clock) * 2 ^ L := by ring
  have hCpos : 0 < Q * Nat.ceil Clock := by
    exact mul_pos hQ (Nat.ceil_pos.mpr hClock)
  have hpadic : padicValNat 2 q ≤ Nat.log 2 (Q * Nat.ceil Clock) + L := by
    calc
      padicValNat 2 q ≤ Nat.log 2 q := padicValNat_le_nat_log q
      _ ≤ Nat.log 2 ((Q * Nat.ceil Clock) * 2 ^ L) :=
        Nat.log_mono_right hqbound
      _ = Nat.log 2 (Q * Nat.ceil Clock) + L :=
        stableSegment_nat_log_mul_pow_two _ _ hCpos
  have hwordPrefix : (anchorInteriorWord Q W k base).IsPrefix
      (actualPostPrefixGaps W k) :=
    maximalInteriorPrefix_isPrefix Q base _
  have hwordCap : ∀ g ∈ anchorInteriorWord Q W k base,
      g ≤ L + gap.Cgap + 1 := by
    intro g hg
    exact hcap g (hwordPrefix.mem hg)
  have hstabilization := stabilizationPrefix_span_le Q
    (L + gap.Cgap + 1) base (anchorInteriorWord Q W k base)
    hwordCap
  have hpadic' : padicValNat 2 (base.slope Q).den ≤
      Nat.log 2 (Q * Nat.ceil Clock) + L := by
    simpa only [q] using hpadic
  constructor <;> omega

theorem stableSegment_four_levels_lt_excess_sixteen
    (kappa : ℝ) (hkappa : 0 < kappa)
    (W : WindowSystem) (L Z0 : ℕ) (e : WindowThreshold)
    (hoffset : W.s = Nat.floor (kappa * (L : ℝ)))
    (hZ : (64 : ℝ) ≤ kappa * (Z0 : ℝ))
    (hlarge : e ∈ W.largePairs Z0) :
    (4 * L : ℝ) < W.excess e / 16 := by
  have hmLower : kappa * (L : ℝ) < (W.m : ℝ) := by
    rw [WindowSystem.m, hoffset]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (kappa * (L : ℝ)))
  have hZpos : (0 : ℝ) < Z0 := by
    have hkZpos : (0 : ℝ) < kappa * (Z0 : ℝ) :=
      lt_of_lt_of_le (by norm_num) hZ
    nlinarith
  have hmul : kappa * (L : ℝ) * (Z0 : ℝ) <
      (W.m : ℝ) * Z0 :=
    mul_lt_mul_of_pos_right hmLower hZpos
  have hsixtyfour : (64 : ℝ) * L ≤
      kappa * Z0 * L := by
    have := mul_le_mul_of_nonneg_right hZ (Nat.cast_nonneg L)
    nlinarith
  have hexcess : (W.m : ℝ) * Z0 < W.excess e := by
    simpa only [Set.mem_setOf_eq] using hlarge.2
  nlinarith

def StableSegmentAnchorGood (Q : ℕ) (W : WindowSystem) (Z0 : ℕ)
    (Cstep : ℝ) (k : ℕ) (data : AnchorInteriorData) : Prop :=
  data.Valid Q W Z0 k ∧
    ∀ e : WindowThreshold, e.1 = k → LongInteriorPair W Z0 e →
      W.excess e / 16 ≤ data.segment.span ∧
      1 ≤ data.segment.gapCount ∧
      data.segment.gapCount ≤ W.m ∧
      (data.segment.startLine.H : ℝ) ≤
        Cstep * W.X / frequencyCutoff W

theorem stableSegment_anchorGood_construct
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (L Z0 k : ℕ)
    (Clock : ℝ) (base : AffineLine)
    (hden : W.rational.eta.den = Q)
    (hcutoff : 1 < frequencyCutoff W)
    (hsk : W.s ≤ k) (hk : k ∈ highAnchors W Z0)
    (hfrequent : IsFrequentPrefix W Z0 (initialLongPrefix W k))
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) base)
    (_hprimitive : Int.gcd base.H base.K = 1)
    (hheight : (base.H : ℝ) ≤ Clock * W.X / frequencyCutoff W)
    (hpadicFour : padicValNat 2 (base.slope Q).den ≤ 4 * L)
    (hbeforeFour : (stabilizationPrefix Q base
      (anchorInteriorWord Q W k base)).span ≤ 4 * L)
    (hfourAll : ∀ e : WindowThreshold, e.1 = k →
      LongInteriorPair W Z0 e → (4 * L : ℝ) < W.excess e / 16)
    (seed : WindowThreshold) (hseedFirst : seed.1 = k)
    (hseed : LongInteriorPair W Z0 seed) :
    StableSegmentAnchorGood Q W Z0 Clock k
      (anchorInteriorData Q W k base) := by
  have hseedAnchor := stableSegment_longInterior_anchorWord Q hQ W Z0 seed base
    hden hcutoff (by simpa only [hseedFirst] using hoccurrence) hseed
  have hseedFour := hfourAll seed hseedFirst hseed
  have hcross : padicValNat 2 (base.slope Q).den ≤
      (anchorInteriorWord Q W k base).span := by
    have hwordLower : W.excess seed / 8 ≤
        (anchorInteriorWord Q W k base).span := by
      simpa only [hseedFirst] using hseedAnchor.2
    have hpadicReal : (padicValNat 2 (base.slope Q).den : ℝ) ≤
        4 * L := by exact_mod_cast hpadicFour
    have hcrossReal : (padicValNat 2 (base.slope Q).den : ℝ) <
        (anchorInteriorWord Q W k base).span := by
      nlinarith
    exact_mod_cast hcrossReal.le
  have hproper : (stabilizationPrefix Q base
      (anchorInteriorWord Q W k base)).span <
      (anchorInteriorWord Q W k base).span := by
    have hwordLower : W.excess seed / 8 ≤
        (anchorInteriorWord Q W k base).span := by
      simpa only [hseedFirst] using hseedAnchor.2
    have hbeforeReal : ((stabilizationPrefix Q base
        (anchorInteriorWord Q W k base)).span : ℝ) ≤ 4 * L := by
      exact_mod_cast hbeforeFour
    have hproperReal : ((stabilizationPrefix Q base
        (anchorInteriorWord Q W k base)).span : ℝ) <
        (anchorInteriorWord Q W k base).span := by
      nlinarith
    exact_mod_cast hproperReal
  have hbaseInterior : classifySlope (base.slope Q) = .interior := by
    simpa only [hseedFirst] using hseedAnchor.1
  have hvalid : (anchorInteriorData Q W k base).Valid Q W Z0 k :=
    anchorInteriorData_valid Q hQ W Z0 k base hsk hk hfrequent
      hoccurrence hbaseInterior hcross hproper
  refine ⟨hvalid, ?_⟩
  intro e heFirst hlong
  have hanchor := stableSegment_longInterior_anchorWord Q hQ W Z0 e base
    hden hcutoff (by simpa only [heFirst] using hoccurrence) hlong
  have hwordLower : W.excess e / 8 ≤
      (anchorInteriorWord Q W k base).span := by
    simpa only [heFirst] using hanchor.2
  have hfour := hfourAll e heFirst hlong
  let data := anchorInteriorData Q W k base
  let before := stabilizationPrefix Q base
    (anchorInteriorWord Q W k base)
  let segment := stabilizedSegment Q base
    (anchorInteriorWord Q W k base)
  have hdecomp : before ++ segment.gaps =
      anchorInteriorWord Q W k base := by
    exact stabilizationPrefix_append_stabilizedGaps Q base
      (anchorInteriorWord Q W k base)
  have hspanEq : (anchorInteriorWord Q W k base).span =
      before.span + segment.span := by
    rw [← hdecomp]
    simp [OddDenominatorSegment.span, GapWord.span]
  have hspanEqReal : ((anchorInteriorWord Q W k base).span : ℝ) =
      before.span + segment.span := by exact_mod_cast hspanEq
  have hbeforeReal : (before.span : ℝ) ≤ 4 * L := by
    exact_mod_cast hbeforeFour
  have hsegmentLower : W.excess e / 16 ≤ (segment.span : ℝ) := by
    nlinarith
  have hexcessPos : 0 < W.excess e := by
    have hlarge := hlong.1.2
    have hnonneg : (0 : ℝ) ≤ W.m * Z0 := by positivity
    linarith
  have hsegmentSpanPos : 0 < segment.span := by
    have hreal : (0 : ℝ) < segment.span := by nlinarith
    exact_mod_cast hreal
  have hsegmentCountPos : 1 ≤ segment.gapCount := by
    have hne : segment.gaps ≠ [] := by
      intro hempty
      simp [OddDenominatorSegment.span, GapWord.span, hempty] at hsegmentSpanPos
    change 1 ≤ segment.gaps.length
    have hlengthPos : 0 < segment.gaps.length :=
      List.length_pos_iff.mpr hne
    omega
  have hsegmentCountLe : segment.gapCount ≤ W.m := by
    rcases hvalid.2.2.2.2.2.1 with ⟨after, hactual⟩
    have hactual' : actualPostPrefixGaps W k =
        before ++ segment.gaps ++ after := by
      simpa only [data, before, segment, anchorInteriorData] using hactual
    have hlength : segment.gaps.length ≤
        (actualPostPrefixGaps W k).length := by
      rw [hactual']
      simp only [List.length_append]
      omega
    exact hlength.trans (actualPostPrefixGaps_length_le W k)
  have hstartHeight : (segment.startLine.H : ℝ) ≤
      Clock * W.X / frequencyCutoff W := by
    have hreduce := stableSegment_primitiveReduction_H_le
      (base.transformWord Q before)
    have hraw : ((base.transformWord Q before).H : ℝ) =
        (base.H : ℝ) := by
      rw [AffineLine.transformWord_H]
    change (((base.transformWord Q before).primitiveReduction.H : ℤ) : ℝ) ≤
      Clock * W.X / frequencyCutoff W
    rw [hraw] at hreduce
    exact hreduce.trans hheight
  change W.excess e / 16 ≤
      (anchorInteriorData Q W k base).segment.span ∧ _
  simpa only [anchorInteriorData, data, before, segment] using
    And.intro hsegmentLower
      (And.intro hsegmentCountPos (And.intro hsegmentCountLe hstartHeight))

/-- Paper label: `lem:stable-segment` (Section 6).  The primitive-step
constant and cutoff are selected at denominator/context level.  For every
compatible family and sufficiently large scale, the selected segment depends
only on the anchor, not on the threshold. -/
theorem lem_stable_segment (context : FixedScaleContext)
    (gap : GapParams context.Q) :
    ∃ Cstep : ℝ, 0 < Cstep ∧ ∃ Zmin : ℕ,
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∃ selection : InteriorAnchorSelection,
              ValidInteriorAnchorSelection context.Q (F.system L) Z0 selection ∧
              ∀ e : WindowThreshold, LongInteriorPair (F.system L) Z0 e →
                ∃ data : AnchorInteriorData,
                  selection e.1 = some data ∧
                  data.Valid context.Q (F.system L) Z0 e.1 ∧
                  (F.system L).excess e / 16 ≤ data.segment.span ∧
                  1 ≤ data.segment.gapCount ∧
                  data.segment.gapCount ≤ (F.system L).m ∧
                  (data.segment.startLine.H : ℝ) ≤
                    Cstep * (F.system L).X /
                      frequencyCutoff (F.system L) := by
  classical
  obtain ⟨Cline, Clock, hClock, hlocking⟩ :=
    lem_ap_locking context.Q context.Q_pos
  obtain ⟨CQ, hCQ, hfirstExists⟩ := lem_firstdeep_exists context
  let Cdiscard : ℕ := Nat.log 2 (context.Q * Nat.ceil Clock) +
    2 * (gap.Cgap + 1)
  let Zfirst : ℕ := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zdense : ℕ := Nat.ceil (64 / context.entropy.kappa)
  let Zmin : ℕ := max Zfirst Zdense
  refine ⟨Clock, hClock, Zmin, ?_⟩
  intro Z0 hZ0 F hF
  have hZfirst : Zfirst ≤ Z0 := (le_max_left _ _).trans hZ0
  have hZdense : Zdense ≤ Z0 := (le_max_right _ _).trans hZ0
  have hZreal : (64 : ℝ) ≤
      context.entropy.kappa * (Z0 : ℝ) := by
    have hquot : 64 / context.entropy.kappa ≤ (Z0 : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hZdense)
    simpa [mul_comm] using
      (div_le_iff₀ context.entropy.kappa_pos).mp hquot
  have hfirstEvent := hfirstExists Z0
    (by simpa only [Zfirst] using hZfirst) F hF
  have hgapEvent := eventually_rawWindowGap_le context gap F hF
  let lineSlack : ℝ := context.structural.Caff - 2
  have hlineSlack : 0 < lineSlack := by
    dsimp [lineSlack]
    linarith [context.structural.Caff_gt]
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlineTop : Tendsto (fun L : ℕ => lineSlack * (L : ℝ))
      atTop atTop := Filter.Tendsto.const_mul_atTop hlineSlack hnatTop
  have hlineEvent : ∀ᶠ L : ℕ in atTop,
      (Cline : ℝ) < lineSlack * (L : ℝ) :=
    hlineTop.eventually_gt_atTop Cline
  filter_upwards [hfirstEvent, hgapEvent, hlineEvent,
    eventually_ge_atTop (max Cdiscard 1)]
      with L hfirstL hgapL hlineL hL
  let W := F.system L
  have hden : W.rational.eta.den = context.Q := by
    change (F.system L).rational.eta.den = context.Q
    rw [F.rational_eq, hF.1]
  have hstruct : W.structural = context.structural := by
    change (F.system L).structural = context.structural
    rw [F.structural_eq, hF.2.1]
  have hentropy : W.entropy = context.entropy := by
    change (F.system L).entropy = context.entropy
    rw [F.entropy_eq, hF.2.2.1]
  have hlevel : W.L = L := F.level_eq L
  have hLdiscard : Cdiscard ≤ L := (le_max_left _ _).trans hL
  have hLone : 1 ≤ L := (le_max_right _ _).trans hL
  have hfrequency : 1 < frequencyCutoff W := by
    unfold frequencyCutoff
    have hX : (1 : ℝ) < W.X := by
      rw [WindowSystem.X, hlevel, dyadicScale]
      exact_mod_cast (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ))
        (Nat.ne_of_gt hLone))
    apply Real.one_lt_rpow hX
    rw [hstruct]
    linarith [context.structural.rho_pos]
  have hfrequencyOne : (1 : ℝ) ≤ frequencyCutoff W := hfrequency.le
  have hoffset : W.s =
      Nat.floor (context.entropy.kappa * (L : ℝ)) := by
    change (F.system L).s = _
    rw [F.offset_eq, hF.2.2.1]
  have candidateExists (k : ℕ)
      (hexists : ∃ seed : WindowThreshold,
        seed.1 = k ∧ LongInteriorPair W Z0 seed) :
      ∃ data : AnchorInteriorData,
        StableSegmentAnchorGood context.Q W Z0 Clock k data := by
    obtain ⟨seed, hseedFirst, hseed⟩ := hexists
    have hk : k ∈ highAnchors W Z0 := by
      rw [highAnchors, Finset.mem_filter]
      refine ⟨?_, seed.2, ?_, ?_⟩
      · simpa only [hseedFirst] using hseed.1.1.1
      · simpa only [hseedFirst] using hseed.1.1.2
      · simpa only [← hseedFirst, Prod.eta, Set.mem_setOf_eq] using
          hseed.1.2
    let p := initialLongPrefix W k
    have hpMem : p ∈ initialPrefixes W Z0 := by
      rw [initialPrefixes, Finset.mem_image]
      exact ⟨k, hk, rfl⟩
    have hpData := hfirstL seed hseed.1
    dsimp only at hpData
    have hpLower : context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
      have hpLower' := hpData.1
      change W.structural.Caff * (W.L : ℝ) <
        (initialLongPrefix W seed.1).span at hpLower'
      rw [hstruct, hlevel, hseedFirst] at hpLower'
      exact hpLower'
    have hsk : W.s ≤ k := by
      by_contra hnot
      have hpzero : p = [] := by
        dsimp [p, initialLongPrefix]
        simp [WindowSystem.rawWindowGapWord, GapWord.firstPrefixAbove, hnot]
      have hCaffPos : 0 < context.structural.Caff :=
        lt_trans (by norm_num) context.structural.Caff_gt
      rw [hpzero] at hpLower
      simp [GapWord.span] at hpLower
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hLone
      nlinarith
    have hpLong : 2 * W.L + Cline < p.span := by
      have htarget : ((2 * W.L + Cline : ℕ) : ℝ) <
          (p.span : ℝ) := by
        rw [hlevel]
        push_cast
        dsimp [lineSlack] at hlineL
        nlinarith
      exact_mod_cast htarget
    have hfrequent : IsFrequentPrefix W Z0 p := by
      simpa only [p, hseedFirst] using hseed.2.1
    rcases hlocking W hden Z0 p hpMem hpLong hfrequent with
      ⟨base, hoccurrence, hprimitive, hheight⟩
    have hcap : ∀ g ∈ actualPostPrefixGaps W k,
        g ≤ L + gap.Cgap + 1 := by
      intro g hg
      apply hgapL k
      · simpa only [hseedFirst] using hseed.1.1.1
      · exact List.mem_of_mem_drop hg
    have hdiscard := stableSegment_stabilizationPrefix_span_le_four_levels
      context.Q context.Q_pos gap Clock hClock W L k base hlevel
      hprimitive hheight hfrequencyOne
      (by simpa only [Cdiscard] using hLdiscard) hcap
    have hfourAll : ∀ e : WindowThreshold, e.1 = k →
        LongInteriorPair W Z0 e →
        (4 * L : ℝ) < W.excess e / 16 := by
      intro e _heFirst heLong
      exact stableSegment_four_levels_lt_excess_sixteen context.entropy.kappa
        context.entropy.kappa_pos W L Z0 e hoffset hZreal heLong.1
    refine ⟨anchorInteriorData context.Q W k base, ?_⟩
    exact stableSegment_anchorGood_construct context.Q context.Q_pos W L Z0 k Clock
      base hden hfrequency hsk hk hfrequent hoccurrence hprimitive hheight
      hdiscard.1 hdiscard.2 hfourAll seed hseedFirst hseed
  let selection : InteriorAnchorSelection := fun k =>
    if h : ∃ data : AnchorInteriorData,
        StableSegmentAnchorGood context.Q W Z0 Clock k data then
      some (Classical.choose h)
    else none
  refine ⟨selection, ?_, ?_⟩
  · intro k data hselected
    dsimp only [selection] at hselected
    split at hselected
    next hgood =>
      simp only [Option.some.injEq] at hselected
      subst data
      exact (Classical.choose_spec hgood).1
    next hnone => simp at hselected
  · intro e hlong
    have hexists : ∃ data : AnchorInteriorData,
        StableSegmentAnchorGood context.Q W Z0 Clock e.1 data :=
      candidateExists e.1 ⟨e, rfl, hlong⟩
    let data : AnchorInteriorData := Classical.choose hexists
    have hgood : StableSegmentAnchorGood context.Q W Z0 Clock e.1 data :=
      Classical.choose_spec hexists
    have hfacts := hgood.2 e rfl hlong
    refine ⟨data, ?_, hgood.1, hfacts⟩
    dsimp only [selection]
    rw [dif_pos hexists]

/-- Paper label: `lem:primitive-direction` (Section 6). -/
theorem lem_primitive_direction (Q X : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1) :
    line.H.natAbs = (line.slope Q).den / Nat.gcd (line.slope Q).den Q ∧
      (horizontalParameters X line).Finite ∧
      ((horizontalParameters X line).ncard : ℝ) ≤
        1 + 4 * Q * X / (line.slope Q).den := by
  have hden := primitiveDirectionDenominator Q hQ line hprimitive
  refine ⟨hden, ?_⟩
  let C : ℤ := 3 * (X : ℤ) - line.A
  let J : ℤ := -line.H
  let B : ℤ := 4 * (X : ℤ)
  have hJ : J < 0 := by
    dsimp [J]
    exact neg_lt_zero.mpr line.H_pos
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbound : ∀ t ∈ horizontalParameters X line,
      0 ≤ C + J * t ∧ C + J * t ≤ B := by
    intro t ht
    change -(X : ℤ) ≤ line.A + line.H * t ∧
      line.A + line.H * t ≤ 3 * X at ht
    dsimp [C, J, B]
    constructor <;> linarith
  have hcount := integerAffineIntervalCount
    (horizontalParameters X line) C J B hJ hB hbound
  refine ⟨hcount.1, hcount.2.trans ?_⟩
  have hHreal : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
  have hqreal : (0 : ℝ) < (line.slope Q).den := by positivity
  have hHnatcast : (line.H.natAbs : ℝ) = (line.H : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hHreal]
  have hqle_nat : (line.slope Q).den ≤ Q * line.H.natAbs := by
    let q := (line.slope Q).den
    let g := Nat.gcd q Q
    have hgdiv : g ∣ q := Nat.gcd_dvd_left q Q
    have hqeq : q / g * g = q := Nat.div_mul_cancel hgdiv
    have hHg : line.H.natAbs * g = q := by
      rw [hden]
      exact hqeq
    have hgQ : g ≤ Q := Nat.gcd_le_right q hQ
    calc
      (line.slope Q).den = line.H.natAbs * g := by
        simpa [q] using hHg.symm
      _ ≤ line.H.natAbs * Q := Nat.mul_le_mul_left _ hgQ
      _ = Q * line.H.natAbs := Nat.mul_comm _ _
  have hqle : ((line.slope Q).den : ℝ) ≤
      (Q : ℝ) * (line.H : ℝ) := by
    rw [← hHnatcast]
    exact_mod_cast hqle_nat
  have hcross : (4 : ℝ) * X * (line.slope Q).den ≤
      (4 * Q * X) * line.H := by
    have := mul_le_mul_of_nonneg_left hqle
      (show (0 : ℝ) ≤ 4 * X by positivity)
    nlinarith
  have hdiv : (4 : ℝ) * X / line.H ≤
      4 * Q * X / (line.slope Q).den := by
    exact (div_le_div_iff₀ hHreal hqreal).2 hcross
  simpa [C, J, B] using add_le_add_left hdiv 1

/-- Paper label: `lem:denominator-span` (Section 6). -/
theorem lem_denominator_span (Q : ℕ) (hQ : 0 < Q) :
    ∃ cspan : ℝ, 0 < cspan ∧
      ∀ segment : OddDenominatorSegment,
        segment.Valid Q → 0 < segment.gapCount →
        cspan * Real.rpow 2 ((segment.span : ℝ) / segment.gapCount) ≤ segment.q := by
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  intro segment hsegment hcount
  rcases hsegment with
    ⟨_hQ, _hpositive, _hprimitive, htrace, _hq_one, _hq_odd, hslopes⟩
  have hlength : 0 < segment.gaps.length := by
    simpa [OddDenominatorSegment.gapCount] using hcount
  let g := segment.gaps.maximum_of_length_pos hlength
  have hgmem : g ∈ segment.gaps :=
    segment.gaps.maximum_of_length_pos_mem hlength
  have hallg : ∀ x ∈ segment.gaps, x ≤ g := by
    intro x hx
    exact segment.gaps.le_maximum_of_length_pos_of_mem hx hlength
  have hsum : segment.gaps.sum ≤ segment.gaps.length * g := by
    simpa using segment.gaps.sum_le_card_nsmul g hallg
  have hsumReal : (segment.gaps.sum : ℝ) ≤
      (segment.gaps.length : ℝ) * g := by
    exact_mod_cast hsum
  have havg : (segment.span : ℝ) / segment.gapCount ≤ (g : ℝ) := by
    rw [OddDenominatorSegment.span, OddDenominatorSegment.gapCount,
      GapWord.span]
    exact (div_le_iff₀
      (by positivity : (0 : ℝ) < segment.gaps.length)).2 (by
        simpa [mul_comm] using hsumReal)
  obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hgmem
  have hμmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hνmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hμmem :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hμmemTrace
  have hνmem :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hνmemTrace
  let μ := (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q
  let ν :=
    (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q
  have hμdata := hslopes μ (by simpa [μ] using hμmem)
  have hνdata := hslopes ν (by simpa [ν] using hνmem)
  have htake : segment.gaps.take (r + 1) =
      segment.gaps.take r ++ [g] := by
    rw [← hget]
    simpa only [List.concat_eq_append] using (List.take_concat_get hr).symm
  have hνμ : ν = (2 : ℚ) ^ g * μ - 1 := by
    calc
      ν = (segment.startLine.transformWord Q
          (segment.gaps.take r ++ [g])).slope Q := by
            rw [← htake]
      _ = ((segment.startLine.transformWord Q (segment.gaps.take r)).transformWord
          Q [g]).slope Q := by rw [AffineLine.transformWord_append]
      _ = ((segment.startLine.transformWord Q
          (segment.gaps.take r)).transform Q g).slope Q := rfl
      _ = (2 : ℚ) ^ g * μ - 1 := by
        rw [AffineLine.slope_transform Q hQ]
  have hμlower : (1 : ℚ) / segment.q ≤ μ := by
    have hdenpos : (0 : ℚ) < μ.den := by positivity
    have hnumone : (1 : ℚ) ≤ μ.num := by
      exact_mod_cast (show (1 : ℤ) ≤ μ.num by
        exact (Int.add_one_le_iff).2 (Rat.num_pos.mpr hμdata.1.1))
    calc
      (1 : ℚ) / segment.q = 1 / μ.den := by rw [hμdata.2.1]
      _ ≤ (μ.num : ℚ) / μ.den :=
        (div_le_div_iff_of_pos_right hdenpos).2 hnumone
      _ = μ := Rat.num_div_den μ
  have hpowμ : (2 : ℚ) ^ g * μ < 2 := by
    rw [hνμ] at hνdata
    linarith [hνdata.1.2]
  have hqpos : (0 : ℚ) < segment.q := by positivity
  have hpowdiv : (2 : ℚ) ^ g / segment.q < 2 := by
    calc
      (2 : ℚ) ^ g / segment.q = (2 : ℚ) ^ g * (1 / segment.q) := by ring
      _ ≤ (2 : ℚ) ^ g * μ :=
        mul_le_mul_of_nonneg_left hμlower (by positivity)
      _ < 2 := hpowμ
  have hpowltRat : (2 : ℚ) ^ g < 2 * segment.q :=
    (div_lt_iff₀ hqpos).1 hpowdiv
  have hpowltReal : (2 : ℝ) ^ g < 2 * (segment.q : ℝ) := by
    exact_mod_cast hpowltRat
  have hrpow : Real.rpow 2
      ((segment.span : ℝ) / segment.gapCount) ≤ (2 : ℝ) ^ g := by
    calc
      Real.rpow 2 ((segment.span : ℝ) / segment.gapCount) ≤
          Real.rpow 2 (g : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) havg
      _ = (2 : ℝ) ^ g := Real.rpow_natCast 2 g
  nlinarith

/-- Paper label: `lem:sparse-cover` (Section 6). -/
private theorem forwardEligible_append_discarded (remainder : GapWord)
    (forward : ℕ) (words : List GapWord) :
    forwardEligibleWords remainder forward words ++
      forwardDiscardedWords remainder forward words = words := by
  induction words with
  | nil => rfl
  | cons block rest ih =>
      simp only [forwardEligibleWords, forwardDiscardedWords]
      split_ifs with h
      · simpa using congrArg (List.cons block) ih
      · simp

private theorem forwardDiscarded_span_add_remainder_le
    (remainder : GapWord) (forward cap : ℕ) (words : List GapWord)
    (hcap : ∀ block ∈ words, GapWord.span block ≤ cap)
    (hremainder : GapWord.span remainder ≤ cap) :
    GapWord.span (forwardDiscardedWords remainder forward words).flatten +
        GapWord.span remainder ≤ forward + cap := by
  induction words with
  | nil =>
      simpa [forwardDiscardedWords, GapWord.span] using
        (hremainder.trans (Nat.le_add_left cap forward))
  | cons block rest ih =>
      have hblock : GapWord.span block ≤ cap := hcap block (by simp)
      have hrest : ∀ word ∈ rest, GapWord.span word ≤ cap := by
        intro word hword
        exact hcap word (by simp [hword])
      simp only [forwardDiscardedWords]
      by_cases hsuffix : forward ≤ GapWord.span (rest.flatten ++ remainder)
      · rw [if_pos hsuffix]
        exact ih hrest
      · rw [if_neg hsuffix]
        simp only [List.flatten_cons, GapWord.span, List.sum_append]
        change block.sum + rest.flatten.sum + remainder.sum ≤ forward + cap
        change block.sum ≤ cap at hblock
        have hsuffix' : rest.flatten.sum + remainder.sum < forward := by
          simp only [GapWord.span, List.sum_append] at hsuffix
          omega
        omega

private theorem list_sum_filter_add_filter_not
    {alpha : Type} (p : alpha → Bool)
    (f : alpha → ℕ) (items : List alpha) :
    ((items.filter p).map f).sum +
        ((items.filter fun x => !p x).map f).sum =
      (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      cases hx : p x <;> simp [hx] <;> omega

private theorem list_sum_filter_le
    {alpha : Type} (p : alpha → Bool)
    (f : alpha → ℕ) (items : List alpha) :
    ((items.filter p).map f).sum ≤ (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      cases hx : p x <;> simp [hx] <;> omega

private theorem list_filter_filter_commute {alpha : Type}
    (items : List alpha) (p q : alpha → Bool) :
    (items.filter p).filter q =
      items.filter fun x => q x && p x := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;> simp [hp, hq, ih]

private theorem list_filter_congr_on {alpha : Type}
    (items : List alpha) (p q : alpha → Bool)
    (h : ∀ x ∈ items, p x = q x) :
    items.filter p = items.filter q := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have htail : ∀ y ∈ xs, p y = q y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.filter_cons]
      rw [hx.symm]
      cases hp : p x <;> simp [ih htail]

private theorem flatten_span_eq_sum_map_span (items : List GapWord) :
    GapWord.span items.flatten = (items.map GapWord.span).sum := by
  induction items with
  | nil => simp [GapWord.span]
  | cons block rest ih =>
      simp only [List.flatten_cons, GapWord.span, List.sum_append, List.map_cons,
        List.sum_cons]
      simp only [GapWord.span] at ih
      omega

private theorem blocksWithOffsetsFrom_mem_split (offset : ℕ)
    (words : List GapWord) (block : LowGapBlock)
    (hblock : block ∈ blocksWithOffsetsFrom offset words) :
    ∃ before after : List GapWord,
      words = before ++ block.gaps :: after ∧
        block.offset = offset + before.flatten.length := by
  induction words generalizing offset with
  | nil => simp [blocksWithOffsetsFrom] at hblock
  | cons word rest ih =>
      simp only [blocksWithOffsetsFrom, List.mem_cons] at hblock
      rcases hblock with rfl | hblock
      · exact ⟨[], rest, by simp⟩
      · rcases ih (offset + word.length) hblock with
          ⟨before, after, hrest, hoffset⟩
        refine ⟨word :: before, after, ?_, ?_⟩
        · simp [hrest]
        · simp only [List.flatten_cons, List.length_append]
          omega

private theorem blocksWithOffsetsFrom_offset_lower (offset : ℕ)
    (words : List GapWord) (block : LowGapBlock)
    (hblock : block ∈ blocksWithOffsetsFrom offset words) :
    offset ≤ block.offset := by
  rcases blocksWithOffsetsFrom_mem_split offset words block hblock with
    ⟨before, _after, _hwords, hoffset⟩
  omega

private theorem blocksWithOffsetsFrom_nodup (offset : ℕ)
    (words : List GapWord) (hne : ∀ word ∈ words, word ≠ []) :
    (blocksWithOffsetsFrom offset words).Nodup := by
  induction words generalizing offset with
  | nil => simp [blocksWithOffsetsFrom]
  | cons word rest ih =>
      simp only [blocksWithOffsetsFrom, List.nodup_cons]
      constructor
      · intro hmem
        have hlower := blocksWithOffsetsFrom_offset_lower
          (offset + word.length) rest ⟨offset, word⟩ hmem
        have hword : word ≠ [] := hne word (by simp)
        have hlength : 0 < word.length := List.length_pos_iff.mpr hword
        change offset + word.length ≤ offset at hlower
        omega
      · apply ih
        intro tail htail
        exact hne tail (by simp [htail])

private theorem blocksWithOffsetsFrom_occurs
    (segment : OddDenominatorSegment) (words : List GapWord)
    (remainder : GapWord)
    (hconcat : words.flatten ++ remainder = segment.gaps)
    (block : LowGapBlock)
    (hblock : block ∈ blocksWithOffsetsFrom 0 words) :
    LowGapBlock.OccursIn segment block := by
  rcases blocksWithOffsetsFrom_mem_split 0 words block hblock with
    ⟨before, after, hwords, hoffset⟩
  have hsource : segment.gaps =
      before.flatten ++ block.gaps ++ after.flatten ++ remainder := by
    calc
      segment.gaps = words.flatten ++ remainder := hconcat.symm
      _ = (before ++ block.gaps :: after).flatten ++ remainder := by rw [hwords]
      _ = before.flatten ++ block.gaps ++ after.flatten ++ remainder := by
        simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
  constructor
  · have hlength := congrArg List.length hsource
    simp only [List.length_append] at hlength
    omega
  · rw [hsource, hoffset]
    simp

private theorem forwardEligibleWords_eq_nil_of_span_lt
    (remainder : GapWord) (forward : ℕ) (words : List GapWord)
    (hspan : GapWord.span (words.flatten ++ remainder) < forward) :
    forwardEligibleWords remainder forward words = [] := by
  cases words with
  | nil => rfl
  | cons word rest =>
      have hsuffix : GapWord.span (rest.flatten ++ remainder) < forward := by
        simp only [List.flatten_cons, GapWord.span, List.sum_append] at hspan ⊢
        omega
      simp [forwardEligibleWords, Nat.not_le.mpr hsuffix]

/-- The prefix implementation of forward eligibility is exactly the ordered
pointwise filter by the genuine post-block suffix. -/
private theorem forwardEligibleBlocks_eq_filter
    (source initial remainder : GapWord) (forward : ℕ)
    (words : List GapWord)
    (hsource : initial ++ words.flatten ++ remainder = source) :
    blocksWithOffsetsFrom initial.length
        (forwardEligibleWords remainder forward words) =
      (blocksWithOffsetsFrom initial.length words).filter fun block =>
        forward ≤ GapWord.span
          (source.drop (block.offset + block.gaps.length)) := by
  induction words generalizing initial with
  | nil => simp [forwardEligibleWords, blocksWithOffsetsFrom]
  | cons word rest ih =>
      have hsourceTail :
          (initial ++ word) ++ rest.flatten ++ remainder = source := by
        simpa [List.append_assoc] using hsource
      have hsuffix :
          source.drop (initial.length + word.length) =
            rest.flatten ++ remainder := by
        rw [← hsource]
        simp [List.append_assoc]
      have htail := ih (initial ++ word) hsourceTail
      have htail' :
          blocksWithOffsetsFrom (initial.length + word.length)
              (forwardEligibleWords remainder forward rest) =
            (blocksWithOffsetsFrom (initial.length + word.length) rest).filter
              fun block =>
                forward ≤ GapWord.span
                  (source.drop (block.offset + block.gaps.length)) := by
        simpa [List.length_append] using htail
      by_cases hforward :
          forward ≤ GapWord.span (rest.flatten ++ remainder)
      · have hhead :
            forward ≤ GapWord.span
              (source.drop (initial.length + word.length)) := by
          rw [hsuffix]
          exact hforward
        simp [forwardEligibleWords, blocksWithOffsetsFrom, hforward, hhead,
          htail']
      · have hforwardLt :
            GapWord.span (rest.flatten ++ remainder) < forward :=
          Nat.lt_of_not_ge hforward
        have hrestNil := forwardEligibleWords_eq_nil_of_span_lt remainder
          forward rest hforwardLt
        have hhead : ¬ forward ≤ GapWord.span
            (source.drop (initial.length + word.length)) := by
          rw [hsuffix]
          exact hforward
        have htailFilter :
            ((blocksWithOffsetsFrom (initial.length + word.length) rest).filter
              fun block =>
                forward ≤ GapWord.span
                  (source.drop (block.offset + block.gaps.length))) = [] := by
          rw [← htail']
          simp [hrestNil, blocksWithOffsetsFrom]
        simp [forwardEligibleWords, blocksWithOffsetsFrom, hforward, hhead,
          htailFilter]

private theorem selectedBlocks_eq_pointwise_of_bound_pos
    (segment : OddDenominatorSegment) (B : ℝ) (ell Z forward : ℕ)
    (hbound : 0 < Nat.ceil (B * ell)) :
    selectedBlocks segment B ell Z forward =
      pointwiseSelectedBlocks segment B ell Z forward := by
  let decomposition :=
    GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))
  have hvalid := GapWord.greedyDecompose_valid segment.gaps
    (Nat.ceil (B * ell)) hbound
  change decomposition.Valid segment.gaps (Nat.ceil (B * ell)) at hvalid
  rcases hvalid with ⟨hconcat, _hgreedy, _hremainder⟩
  have hsource :
      [] ++ decomposition.completed.flatten ++ decomposition.remainder =
        segment.gaps := by
    simpa using hconcat
  have hforward := forwardEligibleBlocks_eq_filter segment.gaps []
    decomposition.remainder forward decomposition.completed hsource
  have hforward' :
      blocksWithOffsetsFrom 0
          (forwardEligibleWords decomposition.remainder forward
            decomposition.completed) =
        (blocksWithOffsetsFrom 0 decomposition.completed).filter fun block =>
          forward ≤ GapWord.span
            (segment.gaps.drop (block.offset + block.gaps.length)) := by
    simpa using hforward
  unfold selectedBlocks pointwiseSelectedBlocks
  change
    ((blocksWithOffsetsFrom 0
        (forwardEligibleWords decomposition.remainder forward
          decomposition.completed)).filter fun block =>
      decide (Z * block.gaps.length ≤ 4 * block.span)) =
    ((blocksWithOffsetsFrom 0 decomposition.completed).filter fun block =>
      decide (Z * block.gaps.length ≤ 4 * block.span ∧
        block.offset + block.gaps.length ≤ segment.gaps.length ∧
        forward ≤ GapWord.span
          (segment.gaps.drop (block.offset + block.gaps.length))))
  rw [hforward', list_filter_filter_commute]
  apply list_filter_congr_on
  intro block hblock
  have hlength := (blocksWithOffsetsFrom_occurs segment
    decomposition.completed decomposition.remainder hconcat block hblock).1
  simp [hlength]

private theorem greedyDecompose_zero (word : GapWord) :
    GapWord.greedyDecompose word 0 = ⟨[], word⟩ := by
  cases word <;> simp [GapWord.greedyDecompose, GapWord.greedyDecomposeAux]

/-- The forward-prefix and pointwise formulations select the same blocks in
the same order, including the degenerate zero-bound case. -/
theorem selectedBlocks_eq_pointwiseSelectedBlocks
    (segment : OddDenominatorSegment) (B : ℝ) (ell Z forward : ℕ) :
    selectedBlocks segment B ell Z forward =
      pointwiseSelectedBlocks segment B ell Z forward := by
  by_cases hbound : 0 < Nat.ceil (B * ell)
  · exact selectedBlocks_eq_pointwise_of_bound_pos segment B ell Z forward hbound
  · have hzero : Nat.ceil (B * ell) = 0 := Nat.eq_zero_of_not_pos hbound
    simp [selectedBlocks, pointwiseSelectedBlocks, hzero, greedyDecompose_zero,
      forwardEligibleWords, blocksWithOffsetsFrom]

private theorem blocksWithOffsetsFrom_filter_span_sum (offset : ℕ)
    (words : List GapWord) (p : GapWord → Bool) :
    (((blocksWithOffsetsFrom offset words).filter fun block => p block.gaps).map
        LowGapBlock.span).sum =
      (((words.filter p).map GapWord.span).sum) := by
  induction words generalizing offset with
  | nil => simp [blocksWithOffsetsFrom]
  | cons word rest ih =>
      cases hp : p word <;>
        simp [blocksWithOffsetsFrom, hp, LowGapBlock.span, ih]

private theorem greedyBlock_span_le_add (bound ell : ℕ) (block : GapWord)
    (hgreedy : GapWord.IsGreedyBlock bound block)
    (hgap : ∀ g ∈ block, g ≤ ell) :
    GapWord.span block ≤ bound + ell := by
  have hne : block ≠ [] := hgreedy.1
  have hlength : 0 < block.length := List.length_pos_iff.mpr hne
  have hprefix := hgreedy.2.2 (block.length - 1) (by omega)
  have hprefix' : block.dropLast.sum < bound := by
    simpa [GapWord.prefixSpan, List.dropLast_eq_take] using hprefix
  have hlast : block.getLast hne ≤ ell :=
    hgap (block.getLast hne) (List.getLast_mem hne)
  have hsplit := congrArg List.sum (List.dropLast_append_getLast hne)
  simp only [List.sum_append, List.sum_singleton] at hsplit
  change block.sum ≤ bound + ell
  omega

private theorem lowForwardWords_cover
    (words : List GapWord) (remainder : GapWord) (forward cap Z totalLength totalSpan : ℕ)
    (hcap : ∀ block ∈ words, GapWord.span block ≤ cap)
    (hremainder : GapWord.span remainder ≤ cap)
    (hlength : words.flatten.length + remainder.length = totalLength)
    (hspan : GapWord.span words.flatten + GapWord.span remainder = totalSpan)
    (hmean : Z * totalLength ≤ totalSpan)
    (hlarge : 4 * (forward + cap) ≤ totalSpan) :
    totalSpan ≤ 2 *
      (((forwardEligibleWords remainder forward words).filter fun block =>
        decide (Z * block.length ≤ 4 * GapWord.span block)).map GapWord.span).sum := by
  let eligible := forwardEligibleWords remainder forward words
  let discarded := forwardDiscardedWords remainder forward words
  let low := eligible.filter fun block =>
    decide (Z * block.length ≤ 4 * GapWord.span block)
  let bad := eligible.filter fun block =>
    !decide (Z * block.length ≤ 4 * GapWord.span block)
  have hpartition := forwardEligible_append_discarded remainder forward words
  change eligible ++ discarded = words at hpartition
  have heligibleMem : ∀ block ∈ eligible, block ∈ words := by
    intro block hblock
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hblock)
  have hdiscardCap : ∀ block ∈ discarded, GapWord.span block ≤ cap := by
    intro block hblock
    exact hcap block (by
      rw [← hpartition]
      exact List.mem_append.mpr (Or.inr hblock))
  have htail : GapWord.span discarded.flatten + GapWord.span remainder ≤
      forward + cap := by
    simpa [discarded] using
      (forwardDiscarded_span_add_remainder_le remainder forward cap words hcap hremainder)
  have htailFour : 4 * (GapWord.span discarded.flatten + GapWord.span remainder) ≤
      totalSpan :=
    (Nat.mul_le_mul_left 4 htail).trans hlarge
  have hbadPoint : ∀ block ∈ bad,
      4 * GapWord.span block ≤ Z * block.length := by
    intro block hblock
    have hnot : ¬ Z * block.length ≤ 4 * GapWord.span block := by
      have hp := (List.mem_filter.mp hblock).2
      simpa using hp
    omega
  have hbadScaled : 4 * ((bad.map GapWord.span).sum) ≤
      Z * ((bad.map List.length).sum) := by
    calc
      4 * ((bad.map GapWord.span).sum) =
          (bad.map fun block => 4 * GapWord.span block).sum := by
            rw [List.sum_map_mul_left]
      _ ≤ (bad.map fun block => Z * block.length).sum :=
        List.sum_le_sum hbadPoint
      _ = Z * ((bad.map List.length).sum) := by
        rw [List.sum_map_mul_left]
  have hbadLength : (bad.map List.length).sum ≤ totalLength := by
    calc
      (bad.map List.length).sum ≤ (eligible.map List.length).sum :=
        list_sum_filter_le
          (fun block => !decide (Z * block.length ≤ 4 * GapWord.span block))
          List.length eligible
      _ ≤ (words.map List.length).sum := by
        rw [← List.length_flatten, ← List.length_flatten]
        have hsub : eligible.flatten.length ≤ words.flatten.length := by
          rw [← hpartition, List.flatten_append, List.length_append]
          omega
        exact hsub
      _ ≤ totalLength := by
        rw [← List.length_flatten]
        omega
  have hbadFour : 4 * (bad.map GapWord.span).sum ≤ totalSpan := by
    calc
      4 * (bad.map GapWord.span).sum ≤ Z * (bad.map List.length).sum := hbadScaled
      _ ≤ Z * totalLength := Nat.mul_le_mul_left Z hbadLength
      _ ≤ totalSpan := hmean
  have heligibleSplit :
      (low.map GapWord.span).sum + (bad.map GapWord.span).sum =
        (eligible.map GapWord.span).sum := by
    exact list_sum_filter_add_filter_not
      (fun block => decide (Z * block.length ≤ 4 * GapWord.span block))
      GapWord.span eligible
  have htotalSplit : totalSpan =
      (eligible.map GapWord.span).sum + GapWord.span discarded.flatten +
        GapWord.span remainder := by
    calc
      totalSpan = GapWord.span words.flatten + GapWord.span remainder := hspan.symm
      _ = GapWord.span (eligible.flatten ++ discarded.flatten) +
          GapWord.span remainder := by
        rw [← List.flatten_append, hpartition]
      _ = GapWord.span eligible.flatten + GapWord.span discarded.flatten +
          GapWord.span remainder := by
        simp [GapWord.span]
      _ = (eligible.map GapWord.span).sum + GapWord.span discarded.flatten +
          GapWord.span remainder := by rw [flatten_span_eq_sum_map_span]
  change totalSpan ≤ 2 * (low.map GapWord.span).sum
  omega

theorem lem_sparse_cover (Q : ℕ) (B : ℝ) (hB : 2 < B)
    (segment : OddDenominatorSegment) (_hsegment : segment.Valid Q)
    (ell Z forward : ℕ) (hell : 0 < ell) (_hZ : 0 < Z)
    (hgap : ∀ g ∈ segment.gaps, g ≤ ell)
    (hmean : Z * segment.gapCount ≤ segment.span ∧
      segment.span < 2 * Z * segment.gapCount)
    (hlarge : 4 * (forward + Nat.ceil ((B + 1) * ell)) ≤ segment.span)
    (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 16 * segment.span) :
    ∃ blocks : List LowGapBlock,
      IsLowGapCover segment B ell Z forward blocks ∧
      blocks.Nodup ∧
      (∀ block ∈ blocks, 0 ≤ interiorComponentWeight y blocks block) ∧
      (∀ block ∈ blocks,
        interiorComponentWeight y blocks block ≤
          32 * Nat.ceil ((B + 1) * ell)) ∧
      (blocks.map (fun block => interiorComponentWeight y blocks block)).sum = y := by
  let bound := Nat.ceil (B * ell)
  let cap := Nat.ceil ((B + 1) * ell)
  let decomposition := GapWord.greedyDecompose segment.gaps bound
  let eligible := forwardEligibleWords decomposition.remainder forward
    decomposition.completed
  let discarded := forwardDiscardedWords decomposition.remainder forward
    decomposition.completed
  let blocks :=
    (blocksWithOffsetsFrom 0 eligible).filter fun block =>
      Z * block.gaps.length ≤ 4 * block.span
  have hboundPos : 0 < bound := by
    apply Nat.ceil_pos.mpr
    have hBpos : 0 < B := lt_trans (by norm_num) hB
    positivity
  have hcapEq : cap = bound + ell := by
    dsimp [cap, bound]
    rw [show (B + 1) * (ell : ℝ) = B * ell + ell by ring]
    exact Nat.ceil_add_natCast (by positivity) ell
  have hcapPos : 0 < cap := by omega
  have hvalid := GapWord.greedyDecompose_valid segment.gaps bound hboundPos
  change decomposition.Valid segment.gaps bound at hvalid
  rcases hvalid with ⟨hconcat, hgreedy, hremainder⟩
  have hcompletedGap : ∀ word ∈ decomposition.completed,
      ∀ g ∈ word, g ≤ ell := by
    intro word hword g hg
    apply hgap g
    rw [← hconcat]
    exact List.mem_append.mpr (Or.inl
      (List.mem_flatten.mpr ⟨word, hword, hg⟩))
  have hcompletedCap : ∀ word ∈ decomposition.completed,
      GapWord.span word ≤ cap := by
    intro word hword
    have hadd := greedyBlock_span_le_add bound ell word
      (hgreedy word hword) (hcompletedGap word hword)
    simpa [hcapEq] using hadd
  have hremainderCap : GapWord.span decomposition.remainder ≤ cap := by
    omega
  have hlengthRaw := congrArg List.length hconcat
  have hlength : decomposition.completed.flatten.length +
      decomposition.remainder.length = segment.gapCount := by
    simpa [OddDenominatorSegment.gapCount] using hlengthRaw
  have hspanRaw := congrArg List.sum hconcat
  have hspan : GapWord.span decomposition.completed.flatten +
      GapWord.span decomposition.remainder = segment.span := by
    simpa [OddDenominatorSegment.span, GapWord.span] using hspanRaw
  have hcoverWords := lowForwardWords_cover decomposition.completed
    decomposition.remainder forward cap Z segment.gapCount segment.span
    hcompletedCap hremainderCap hlength hspan hmean.1 (by
      simpa [cap] using hlarge)
  have hpartition := forwardEligible_append_discarded decomposition.remainder
    forward decomposition.completed
  change eligible ++ discarded = decomposition.completed at hpartition
  have heligibleMem : ∀ word ∈ eligible, word ∈ decomposition.completed := by
    intro word hword
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hword)
  have heligibleGreedy : ∀ word ∈ eligible,
      GapWord.IsGreedyBlock bound word := by
    intro word hword
    exact hgreedy word (heligibleMem word hword)
  have heligibleNonempty : ∀ word ∈ eligible, word ≠ [] := by
    intro word hword
    exact (heligibleGreedy word hword).1
  have heligibleConcat :
      eligible.flatten ++ (discarded.flatten ++ decomposition.remainder) =
        segment.gaps := by
    calc
      eligible.flatten ++ (discarded.flatten ++ decomposition.remainder) =
          (eligible ++ discarded).flatten ++ decomposition.remainder := by
            simp [List.flatten_append, List.append_assoc]
      _ = decomposition.completed.flatten ++ decomposition.remainder := by
        rw [hpartition]
      _ = segment.gaps := hconcat
  have hblocksNodup : blocks.Nodup := by
    dsimp [blocks]
    exact (blocksWithOffsetsFrom_nodup 0 eligible heligibleNonempty).filter _
  have hblocksSpan : (blocks.map LowGapBlock.span).sum =
      (((eligible.filter fun word =>
        decide (Z * word.length ≤ 4 * GapWord.span word)).map
          GapWord.span).sum) := by
    dsimp [blocks]
    exact blocksWithOffsetsFrom_filter_span_sum 0 eligible
      (fun word => decide (Z * word.length ≤ 4 * GapWord.span word))
  have hcover : segment.span ≤ 2 * (blocks.map LowGapBlock.span).sum := by
    rw [hblocksSpan]
    exact hcoverWords
  have hsegmentSpanPos : 0 < segment.span := by omega
  have hsumPos : 0 < (blocks.map LowGapBlock.span).sum := by omega
  have hselected : blocks = selectedBlocks segment B ell Z forward := by
    rfl
  have hblockData : ∀ block ∈ blocks,
      LowGapBlock.OccursIn segment block ∧
        GapWord.IsGreedyBlock bound block.gaps ∧
        Z * block.gaps.length ≤ 4 * block.span := by
    intro block hblock
    have hmem := List.mem_filter.mp hblock
    have hlow : Z * block.gaps.length ≤ 4 * block.span := by
      simpa using hmem.2
    have hoccurs := blocksWithOffsetsFrom_occurs segment eligible
      (discarded.flatten ++ decomposition.remainder) heligibleConcat block hmem.1
    rcases blocksWithOffsetsFrom_mem_split 0 eligible block hmem.1 with
      ⟨before, after, hwords, _hoffset⟩
    have hword : block.gaps ∈ eligible := by
      rw [hwords]
      simp
    exact ⟨hoccurs, heligibleGreedy block.gaps hword, hlow⟩
  have hcoverCertificate : IsLowGapCover segment B ell Z forward blocks := by
    exact ⟨hselected, hblockData, hcover⟩
  have hdenPos : (0 : ℝ) < (blocks.map LowGapBlock.span).sum := by
    exact_mod_cast hsumPos
  have hcoverReal : (segment.span : ℝ) ≤
      2 * ((blocks.map LowGapBlock.span).sum : ℝ) := by
    exact_mod_cast hcover
  have hyDen : y ≤ 32 * ((blocks.map LowGapBlock.span).sum : ℝ) := by
    nlinarith
  have hweightNonneg : ∀ block ∈ blocks,
      0 ≤ interiorComponentWeight y blocks block := by
    intro block _hblock
    unfold interiorComponentWeight
    exact div_nonneg (mul_nonneg hy0 (by positivity)) hdenPos.le
  have hweightUpper : ∀ block ∈ blocks,
      interiorComponentWeight y blocks block ≤ (32 : ℝ) * cap := by
    intro block hblock
    have hmem := List.mem_filter.mp hblock
    rcases blocksWithOffsetsFrom_mem_split 0 eligible block hmem.1 with
      ⟨before, after, hwords, _hoffset⟩
    have hword : block.gaps ∈ eligible := by
      rw [hwords]
      simp
    have hblockCap : block.span ≤ cap :=
      hcompletedCap block.gaps (heligibleMem block.gaps hword)
    unfold interiorComponentWeight
    have hfirst :
        y * (block.span : ℝ) /
            ((blocks.map LowGapBlock.span).sum : ℝ) ≤
          32 * (block.span : ℝ) := by
      apply (div_le_iff₀ hdenPos).2
      have hmul := mul_le_mul_of_nonneg_right hyDen
        (show (0 : ℝ) ≤ block.span by positivity)
      nlinarith
    exact hfirst.trans (by exact_mod_cast
      (Nat.mul_le_mul_left 32 hblockCap))
  have hcastSpan :
      (blocks.map (fun block => (block.span : ℝ))).sum =
        ((blocks.map LowGapBlock.span).sum : ℝ) := by
    induction blocks with
    | nil => simp
    | cons block rest ih => simp [ih]
  have hsumWeights :
      (blocks.map (fun block =>
        interiorComponentWeight y blocks block)).sum = y := by
    change
      (blocks.map (fun block =>
        y * (block.span : ℝ) /
          ((blocks.map LowGapBlock.span).sum : ℝ))).sum = y
    calc
      _ = (blocks.map (fun block =>
          (y / ((blocks.map LowGapBlock.span).sum : ℝ)) *
            (block.span : ℝ))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro block _hblock
            ring
      _ = (y / ((blocks.map LowGapBlock.span).sum : ℝ)) *
          (blocks.map (fun block => (block.span : ℝ))).sum := by
            rw [List.sum_map_mul_left]
      _ = (y / ((blocks.map LowGapBlock.span).sum : ℝ)) *
          ((blocks.map LowGapBlock.span).sum : ℝ) := by rw [hcastSpan]
      _ = y := by field_simp
  refine ⟨blocks, hcoverCertificate, hblocksNodup, hweightNonneg, ?_,
    hsumWeights⟩
  simpa [cap] using hweightUpper

/-- Paper label: `lem:signature-entropy` (Section 6). -/
private def compositionShiftEmbedding (n : ℕ) :
    Function.Embedding (Fin (n - 1)) (Fin (n + 1)) :=
  (Fin.succEmb (n - 1)).trans
    (Fin.castLEEmb (Nat.add_le_add_right (Nat.sub_le n 1) 1))

private theorem compositionAsSetEquiv_symm_length (n : ℕ) (hn : 0 < n)
    (s : Finset (Fin (n - 1))) :
    ((compositionAsSetEquiv n).symm s).length = s.card + 1 := by
  let d := (compositionAsSetEquiv n).symm s
  have hboundaries :
      d.boundaries =
        insert 0 (insert (Fin.last n) (s.map (compositionShiftEmbedding n))) := by
    ext i
    dsimp [d, compositionAsSetEquiv]
    change i ∈ ({i : Fin (n + 1) | i = 0 ∨ i = Fin.last n ∨
      ∃ j : Fin (n - 1), ∃ _hj : j ∈ s, i.val = j.val + 1} : Set _).toFinset ↔ _
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_map]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, hv⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · right
        right
        exact ⟨j, hj, by
          apply Fin.ext
          simpa [compositionShiftEmbedding] using hv.symm⟩
    · rintro (rfl | rfl | ⟨j, hj, hv⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · right
        right
        exact ⟨j, hj, by
          have hval := congrArg Fin.val hv
          simpa [compositionShiftEmbedding] using hval.symm⟩
  rw [CompositionAsSet.length, hboundaries]
  have hzero :
      (0 : Fin (n + 1)) ∉ s.map (compositionShiftEmbedding n) := by
    simp only [Finset.mem_map]
    rintro ⟨j, _hj, h⟩
    have hval := congrArg Fin.val h
    simp [compositionShiftEmbedding] at hval
  have hlast :
      Fin.last n ∉ s.map (compositionShiftEmbedding n) := by
    simp only [Finset.mem_map]
    rintro ⟨j, _hj, h⟩
    have hval := congrArg Fin.val h
    simp [compositionShiftEmbedding] at hval
    omega
  have hzeroLast : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem hlast, Finset.card_map]
    omega
  · simp [hzero, hzeroLast]

private def compositionCuts {n : ℕ} (c : Composition n) :
    Finset (Fin (n - 1)) :=
  (compositionAsSetEquiv n) ((compositionEquiv n) c)

private theorem compositionCuts_card {n : ℕ} (hn : 0 < n)
    (c : Composition n) :
    (compositionCuts c).card = c.length - 1 := by
  let s := compositionCuts c
  have hinv : (compositionAsSetEquiv n).symm s = (compositionEquiv n) c := by
    exact (compositionAsSetEquiv n).symm_apply_apply ((compositionEquiv n) c)
  have hleft := compositionAsSetEquiv_symm_length n hn s
  rw [hinv] at hleft
  have hleft' : c.length = s.card + 1 := by
    simpa [compositionEquiv] using hleft
  change s.card = c.length - 1
  omega

private theorem compositionCuts_injective {n : ℕ} :
    Function.Injective (compositionCuts : Composition n → Finset (Fin (n - 1))) := by
  exact ((compositionEquiv n).trans (compositionAsSetEquiv n)).injective

private def cutCodeFinset (H rMax : ℕ) : Finset (Finset (Fin H)) :=
  (Finset.Icc 1 rMax).biUnion fun r ↦
    (Finset.univ : Finset (Fin H)).powersetCard (r - 1)

private theorem cutCodeFinset_card (H rMax : ℕ) :
    (cutCodeFinset H rMax).card =
      ∑ r ∈ Finset.Icc 1 rMax, Nat.choose H (r - 1) := by
  have hdisjoint :
      ((Finset.Icc 1 rMax : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun r ↦ (Finset.univ : Finset (Fin H)).powersetCard (r - 1)) := by
    intro r hr t ht hrt
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hsr hst
    have hrcard := (Finset.mem_powersetCard.mp hsr).2
    have htcard := (Finset.mem_powersetCard.mp hst).2
    have hrone : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have htone : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    apply hrt
    omega
  rw [cutCodeFinset, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def paddedComposition (H : ℕ) (w : GapWord)
    (hpos : w.Positive) (hspan : w.span ≤ H) : Composition (H + 1) where
  blocks := w ++ [H + 1 - w.span]
  blocks_pos := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hpos g hg
    · simp only [List.mem_singleton] at hg
      subst g
      omega
  blocks_sum := by
    change w.sum ≤ H at hspan
    change (w ++ [H + 1 - w.sum]).sum = H + 1
    simp only [List.sum_append, List.sum_singleton]
    omega

private theorem paddedComposition_injective (H : ℕ) :
    Set.InjOn
      (fun x : {w : GapWord // w.Positive ∧ w.span ≤ H} ↦
        paddedComposition H x.1 x.2.1 x.2.2)
      Set.univ := by
  intro u _hu v _hv huv
  apply Subtype.ext
  have hblocks := congrArg Composition.blocks huv
  have hdrop := congrArg List.dropLast hblocks
  simpa [paddedComposition] using hdrop

private def encodingHeight (B : ℝ) (D : ℕ) : ℕ :=
  Nat.ceil ((B + 1) * Nat.ceil (Real.logb 2 (4 * D)))

private theorem encodingCandidate_positive {D Z : ℕ} {B : ℝ}
    {sigma : BlockEncoding} (hsigma : sigma ∈ encodingCandidates D Z B) :
    sigma.gaps.Positive := by
  exact hsigma.1.2.2.2.2

private theorem encodingCandidate_span_le_height {D Z : ℕ} {B : ℝ}
    {sigma : BlockEncoding} (hsigma : sigma ∈ encodingCandidates D Z B) :
    sigma.gaps.span ≤ encodingHeight B D := by
  have hheight : (sigma.h : ℝ) ≤
      (B + 1) * Nat.ceil (Real.logb 2 (4 * D)) := hsigma.2.2.2.2.1
  have hceil :
      (B + 1) * Nat.ceil (Real.logb 2 (4 * D)) ≤
        (encodingHeight B D : ℝ) := by
    exact Nat.le_ceil _
  have hnat : sigma.h ≤ encodingHeight B D := by
    exact_mod_cast hheight.trans hceil
  simpa [BlockEncoding.Valid] using
    (show sigma.gaps.span ≤ encodingHeight B D by
      rw [← hsigma.1.2.2.1]
      exact hnat)

private def encodingPaddedComposition {D Z : ℕ} {B : ℝ}
    (sigma : {sigma : BlockEncoding // sigma ∈ encodingCandidates D Z B}) :
    Composition (encodingHeight B D + 1) :=
  paddedComposition (encodingHeight B D) sigma.1.gaps
    (encodingCandidate_positive sigma.2)
    (encodingCandidate_span_le_height sigma.2)

private def encodingCutCode {D Z : ℕ} {B : ℝ}
    (sigma : {sigma : BlockEncoding // sigma ∈ encodingCandidates D Z B}) :
    Finset (Fin (encodingHeight B D)) :=
  compositionCuts (encodingPaddedComposition sigma)

private theorem encodingCutCode_injective {D Z : ℕ} {B : ℝ} :
    Function.Injective
      (encodingCutCode (D := D) (Z := Z) (B := B)) := by
  intro sigma tau heq
  have hcompositions :
      encodingPaddedComposition sigma = encodingPaddedComposition tau := by
    apply compositionCuts_injective
    exact heq
  let wsigma : {w : GapWord // w.Positive ∧ w.span ≤ encodingHeight B D} :=
    ⟨sigma.1.gaps, encodingCandidate_positive sigma.2,
      encodingCandidate_span_le_height sigma.2⟩
  let wtau : {w : GapWord // w.Positive ∧ w.span ≤ encodingHeight B D} :=
    ⟨tau.1.gaps, encodingCandidate_positive tau.2,
      encodingCandidate_span_le_height tau.2⟩
  have hwords : wsigma = wtau :=
    paddedComposition_injective (encodingHeight B D)
      (Set.mem_univ wsigma) (Set.mem_univ wtau) hcompositions
  have hgaps : sigma.1.gaps = tau.1.gaps := congrArg Subtype.val hwords
  apply Subtype.ext
  apply BlockEncoding.ext
  · exact sigma.2.2.1.trans tau.2.2.1.symm
  · exact sigma.2.2.2.1.trans tau.2.2.2.1.symm
  · rw [sigma.2.1.2.2.1, tau.2.1.2.2.1, hgaps]
  · rw [sigma.2.1.2.2.2.1, tau.2.1.2.2.2.1, hgaps]
  · exact hgaps

private theorem eventually_le_encodingHeight (B cBand : ℝ)
    (hB : 2 < B) (hcBand : 0 < cBand) :
    ∀ᶠ Z : ℕ in atTop, ∀ D : ℕ,
      cBand * (2 : ℝ) ^ Z ≤ D → Z ≤ encodingHeight B D := by
  have hpowers :
      ∀ᶠ n : ℕ in atTop, (1 / cBand : ℝ) ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpowers
  filter_upwards [eventually_ge_atTop (max (2 * N) 2)] with Z hZ
  intro D hD
  have hNhalf : N ≤ Z / 2 := by omega
  have honeDiv : (1 / cBand : ℝ) ≤ (2 : ℝ) ^ (Z / 2) :=
    (hN N le_rfl).trans (pow_le_pow_right₀ (by norm_num) hNhalf)
  have hone : (1 : ℝ) ≤ cBand * (2 : ℝ) ^ (Z / 2) := by
    have := mul_le_mul_of_nonneg_left honeDiv hcBand.le
    field_simp at this
    exact this
  have hhalfD : (2 : ℝ) ^ (Z / 2) ≤ D := by
    calc
      (2 : ℝ) ^ (Z / 2) ≤
          (cBand * (2 : ℝ) ^ (Z / 2)) * (2 : ℝ) ^ (Z / 2) := by
            calc
              (2 : ℝ) ^ (Z / 2) = 1 * (2 : ℝ) ^ (Z / 2) := by ring
              _ ≤ (cBand * (2 : ℝ) ^ (Z / 2)) * (2 : ℝ) ^ (Z / 2) :=
                mul_le_mul_of_nonneg_right hone (by positivity)
      _ = cBand * (2 : ℝ) ^ (2 * (Z / 2)) := by
        rw [show 2 * (Z / 2) = Z / 2 + Z / 2 by omega, pow_add]
        ring
      _ ≤ cBand * (2 : ℝ) ^ Z := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (by omega)) hcBand.le
      _ ≤ D := hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hhalfD
  have hlogD : ((Z / 2 : ℕ) : ℝ) ≤ Real.logb 2 (D : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hDpos]
    simpa [Real.rpow_natCast] using hhalfD
  have hlog4D : ((Z / 2 : ℕ) : ℝ) ≤ Real.logb 2 (4 * D) := by
    have hDle : (D : ℝ) ≤ 4 * D := by nlinarith [hDpos]
    exact hlogD.trans
      (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hDpos hDle)
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hhalfEll : Z / 2 ≤ ell := by
    have hhalfEllReal : ((Z / 2 : ℕ) : ℝ) ≤ (ell : ℝ) := by
      simpa [ell] using hlog4D.trans (Nat.le_ceil (Real.logb 2 (4 * D)))
    exact_mod_cast hhalfEllReal
  have hellPos : 0 < ell := by
    have : 1 ≤ Z / 2 := by omega
    omega
  have hthree : 3 * ell ≤ encodingHeight B D := by
    have hceil : (B + 1) * (ell : ℝ) ≤ (encodingHeight B D : ℝ) := by
      simpa [encodingHeight, ell] using
        (Nat.le_ceil ((B + 1) * (ell : ℝ)))
    have hellReal : (0 : ℝ) < ell := by exact_mod_cast hellPos
    exact_mod_cast (show (3 : ℝ) * ell ≤ encodingHeight B D by
      nlinarith)
  omega

private theorem encodingCutCode_mem {D Z : ℕ} {B : ℝ}
    (hZ : 0 < Z) (hZH : Z ≤ encodingHeight B D)
    (sigma : {sigma : BlockEncoding // sigma ∈ encodingCandidates D Z B}) :
    encodingCutCode sigma ∈
      cutCodeFinset (encodingHeight B D)
        (Nat.floor ((5 / (Z : ℝ)) * (encodingHeight B D + 1))) := by
  let H := encodingHeight B D
  let rMax := Nat.floor ((5 / (Z : ℝ)) * (H + 1))
  have hHspan : sigma.1.h ≤ H := by
    rw [sigma.2.1.2.2.1]
    exact encodingCandidate_span_le_height sigma.2
  have hZreal : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hrbound : (sigma.1.r : ℝ) ≤ 4 * sigma.1.h / Z :=
    sigma.2.2.2.2.2.2
  have hscaled : (sigma.1.r : ℝ) * Z ≤ 4 * sigma.1.h := by
    exact (le_div_iff₀ hZreal).mp hrbound
  have hrMaxReal : ((sigma.1.r + 1 : ℕ) : ℝ) ≤
      (5 / (Z : ℝ)) * (H + 1) := by
    have hZHreal : (Z : ℝ) ≤ H := by exact_mod_cast hZH
    have hhreal : (sigma.1.h : ℝ) ≤ H := by exact_mod_cast hHspan
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hZreal]
    push_cast
    nlinarith
  have hrMaxNat : sigma.1.r + 1 ≤ rMax := by
    exact Nat.le_floor hrMaxReal
  rw [cutCodeFinset, Finset.mem_biUnion]
  refine ⟨sigma.1.r + 1, ?_, ?_⟩
  · exact Finset.mem_Icc.mpr ⟨by omega, hrMaxNat⟩
  · rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.subset_univ _
    · have hcard := compositionCuts_card
          (show 0 < H + 1 by omega) (encodingPaddedComposition sigma)
      have hlength : (encodingPaddedComposition sigma).length = sigma.1.r + 1 := by
        change (sigma.1.gaps ++ [H + 1 - sigma.1.gaps.span]).length = _
        simp [sigma.2.1.2.2.2.1]
      change (compositionCuts (encodingPaddedComposition sigma)).card = _
      rw [hcard, hlength]

theorem lem_signature_entropy (B cBand : ℝ) (hB : 2 < B)
    (hcBand : 0 < cBand) :
    ∃ Zstar : ℕ, ∃ CB : ℝ, 0 < CB ∧ ∀ D Z : ℕ,
      Zstar ≤ Z → cBand * (2 : ℝ) ^ Z ≤ D →
      (encodingCandidates D Z B).Finite ∧
      ((encodingCandidates D Z B).ncard : ℝ) ≤
          CB * (Nat.ceil (Real.logb 2 (4 * D)) : ℝ) ^ 3 *
            Real.rpow 2
              ((B + 1) * Nat.ceil (Real.logb 2 (4 * D)) *
                binaryEntropy (5 / Z)) ∧
      ((encodingCandidates D Z B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D := by
  let CB : ℝ := 4 * (B + 3) ^ 2
  have hCB : 0 < CB := by
    dsimp [CB]
    positivity
  obtain ⟨Zheight, hheight⟩ := eventually_atTop.mp
    (eventually_le_encodingHeight B cBand hB hcBand)
  obtain ⟨Zquant, hquant⟩ := lem_quant_entropy B cBand CB hB hcBand hCB
  refine ⟨max (max Zheight Zquant) 10, CB, hCB, ?_⟩
  intro D Z hZ hD
  have hZten : 10 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZpos : 0 < Z := by omega
  have hZH : Z ≤ encodingHeight B D :=
    hheight Z (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hZ)) D hD
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  let H := encodingHeight B D
  let alpha : ℝ := 5 / Z
  let rMax := Nat.floor (alpha * (H + 1))
  have hHpos : 0 < H := lt_of_lt_of_le hZpos hZH
  have hHtwo : 2 ≤ H + 1 := by omega
  have halphaPos : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halphaHalf : alpha ≤ (1 : ℝ) / 2 := by
    dsimp [alpha]
    have hZreal : (10 : ℝ) ≤ Z := by exact_mod_cast hZten
    have hZrealPos : (0 : ℝ) < Z := by positivity
    rw [div_le_iff₀ hZrealPos]
    nlinarith
  have halphaNonneg : 0 ≤ alpha := halphaPos.le
  have hargNonneg : 0 ≤ alpha * (H + 1 : ℝ) := by positivity
  have hrMax : (rMax : ℝ) ≤ alpha * (H + 1) := by
    exact Nat.floor_le hargNonneg
  have hrMax' : (rMax : ℝ) ≤ alpha * (((H + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrMax
  have hcomposition :=
    lem_composition_entropy (H + 1) rMax alpha hHtwo halphaPos halphaHalf hrMax'
  let source : Set BlockEncoding := encodingCandidates D Z B
  let code := encodingCutCode (D := D) (Z := Z) (B := B)
  let codes := cutCodeFinset H rMax
  have hcodeMem (sigma : source) : code sigma ∈ codes := by
    simpa [code, codes, H, alpha, rMax] using
      (encodingCutCode_mem hZpos hZH sigma)
  have hcodeInjective : Function.Injective code := by
    simpa [code] using
      (encodingCutCode_injective (D := D) (Z := Z) (B := B))
  have himageFinite : (code '' (Set.univ : Set source)).Finite := by
    apply codes.finite_toSet.subset
    rintro y ⟨sigma, _hsigma, rfl⟩
    exact hcodeMem sigma
  have hunivFinite : (Set.univ : Set source).Finite :=
    himageFinite.of_finite_image (Set.injOn_univ.mpr hcodeInjective)
  letI : Finite source := Set.finite_univ_iff.mp hunivFinite
  letI : Fintype source := Fintype.ofFinite source
  have hcardNat : source.ncard ≤ codes.card := by
    have hle := Fintype.card_le_of_injective
      (fun sigma : source ↦ (⟨code sigma, hcodeMem sigma⟩ : codes))
      (fun _ _ h ↦ hcodeInjective (congrArg Subtype.val h))
    simpa [source, codes, Nat.card_eq_fintype_card] using hle
  have hcodesCard : codes.card =
      ∑ r ∈ Finset.Icc 1 rMax, Nat.choose H (r - 1) := by
    simpa [codes] using cutCodeFinset_card H rMax
  have hcountComposition : (source.ncard : ℝ) ≤
      ((H + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) := by
    calc
      (source.ncard : ℝ) ≤ codes.card := by exact_mod_cast hcardNat
      _ = (∑ r ∈ Finset.Icc 1 rMax,
          Nat.choose ((H + 1) - 1) (r - 1) : ℕ) := by
            rw [hcodesCard]
            simp only [Nat.add_sub_cancel]
      _ ≤ ((H + 1 : ℕ) : ℝ) ^ 2 *
          Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) :=
            hcomposition
  have hellPos : 0 < ell := by
    by_contra hell
    have hellZero : ell = 0 := Nat.eq_zero_of_not_pos hell
    have hHZero : H = 0 := by simp [H, encodingHeight, ell, hellZero]
    omega
  have hellReal : (0 : ℝ) < ell := by exact_mod_cast hellPos
  have hheightLt : (H : ℝ) < (B + 1) * ell + 1 := by
    have hnonneg : 0 ≤ (B + 1) * (ell : ℝ) := by positivity
    simpa [H, encodingHeight, ell] using Nat.ceil_lt_add_one hnonneg
  have hentropyEq :
      binaryEntropy alpha = Real.binEntropy alpha / Real.log 2 := by
    rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, Real.logb]
    ring
  have hentropyNonneg : 0 ≤ binaryEntropy alpha := by
    rw [hentropyEq]
    exact div_nonneg
      (Real.binEntropy_nonneg halphaNonneg (halphaHalf.trans (by norm_num)))
      (Real.log_nonneg (by norm_num))
  have hentropyOne : binaryEntropy alpha ≤ 1 := by
    rw [hentropyEq]
    exact (div_le_one (Real.log_pos (by norm_num))).2 Real.binEntropy_le_log_two
  have hpoly : (((H + 1 : ℕ) : ℝ) ^ 2) ≤
      (B + 3) ^ 2 * (ell : ℝ) ^ 2 := by
    have hlinear : ((H + 1 : ℕ) : ℝ) ≤ (B + 3) * ell := by
      push_cast
      have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast hellPos
      nlinarith
    simpa [mul_pow] using pow_le_pow_left₀ (by positivity) hlinear 2
  have hexponent : (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) ≤
      (B + 1) * ell * binaryEntropy alpha + 2 := by
    have hHplus : (((H + 1 : ℕ) : ℝ) ≤ (B + 1) * ell + 2) := by
      push_cast
      linarith
    nlinarith
  have hrpow :
      Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) ≤
        4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
    calc
      Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) ≤
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha + 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ = 4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
        change (2 : ℝ) ^ ((B + 1) * ell * binaryEntropy alpha + 2) =
          4 * (2 : ℝ) ^ ((B + 1) * ell * binaryEntropy alpha)
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num [Real.rpow_natCast]
        ring
  have hcount : ((encodingCandidates D Z B).ncard : ℝ) ≤
      CB * (ell : ℝ) ^ 3 *
        Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
    have hrpowNonneg :
        0 ≤ Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) :=
      Real.rpow_nonneg (by norm_num) _
    have hleftNonneg : (0 : ℝ) ≤ (((H + 1 : ℕ) : ℝ) ^ 2) := by positivity
    calc
      ((encodingCandidates D Z B).ncard : ℝ) = (source.ncard : ℝ) := rfl
      _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2) *
          Real.rpow 2 (((H + 1 : ℕ) : ℝ) * binaryEntropy alpha) :=
            hcountComposition
      _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2) *
          (4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) :=
            mul_le_mul_of_nonneg_left hrpow hleftNonneg
      _ ≤ ((B + 3) ^ 2 * (ell : ℝ) ^ 2) *
          (4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) := by
            exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ ≤ CB * (ell : ℝ) ^ 3 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
            dsimp [CB]
            have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast hellPos
            have hepow : (ell : ℝ) ^ 2 ≤ ell ^ 3 := by
              nlinarith [sq_nonneg (ell : ℝ)]
            calc
              (B + 3) ^ 2 * ell ^ 2 *
                  (4 * Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) =
                  (4 * (B + 3) ^ 2 *
                    Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) * ell ^ 2 := by
                      ring
              _ ≤ (4 * (B + 3) ^ 2 *
                    Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) * ell ^ 3 :=
                  mul_le_mul_of_nonneg_left hepow (by positivity)
              _ = 4 * (B + 3) ^ 2 * ell ^ 3 *
                    Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by
                      ring
  constructor
  · exact Set.toFinite _
  constructor
  · simpa [ell, alpha] using hcount
  · have hquantApply := hquant Z D
        (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hZ)) hD
    have hmul := mul_le_mul_of_nonneg_right hcount (by positivity : (0 : ℝ) ≤ ell)
    calc
      ((encodingCandidates D Z B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * D)) =
          ((encodingCandidates D Z B).ncard : ℝ) * ell := by rfl
      _ ≤ (CB * (ell : ℝ) ^ 3 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha)) * ell := hmul
      _ = CB * (ell : ℝ) ^ 4 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy alpha) := by ring
      _ ≤ Real.sqrt D := by simpa [ell, alpha] using hquantApply

/-- Paper label: `lem:word-slope` (Section 6). -/
theorem lem_word_slope (B : ℝ) (hB : 2 < B) (D : ℕ) (hD : 0 < D)
    (w : GapWord)
    (hspan : B * Nat.ceil (Real.logb 2 (4 * D)) ≤ w.span) :
    Set.Subsingleton
      {μ : ℚ | D ≤ μ.den ∧ μ.den < 2 * D ∧
        slopeAfter w μ ∈ Set.Ioo (0 : ℝ) 1} := by
  intro μ hμ ν hν
  by_contra hne
  let ell := Nat.ceil (Real.logb 2 (4 * (D : ℝ)))
  have hell_eq : ell = Nat.clog 2 (4 * D) := by
    dsimp [ell]
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  have hfourD : 4 * D ≤ 2 ^ ell := by
    rw [hell_eq]
    exact Nat.le_pow_clog (by omega) _
  have hellpos : 0 < ell := by
    rw [hell_eq, Nat.lt_clog_iff_pow_lt (by omega)]
    simp
    omega
  have htwoellR : (2 * ell : ℝ) < (w.span : ℝ) := by
    have hmul : (2 : ℝ) * ell < B * ell :=
      mul_lt_mul_of_pos_right hB (by exact_mod_cast hellpos)
    have hspan' : B * (ell : ℝ) ≤ (w.span : ℝ) := by
      simpa [ell] using hspan
    nlinarith
  have htwoell : 2 * ell < w.span := by exact_mod_cast htwoellR
  have hbandpow : (4 * D) ^ 2 ≤ 2 ^ (2 * ell) := by
    calc
      (4 * D) ^ 2 ≤ (2 ^ ell) ^ 2 := Nat.pow_le_pow_left hfourD 2
      _ = 2 ^ (2 * ell) := by
        rw [← pow_mul]
        congr 1
        omega
  have hpowlt : 2 ^ (2 * ell) < 2 ^ w.span := by
    exact Nat.pow_lt_pow_right (by omega) htwoell
  have hdenpowNat : 4 * D ^ 2 < 2 ^ w.span := by
    have hD1 : 1 ≤ D := hD
    calc
      4 * D ^ 2 ≤ (4 * D) ^ 2 := by nlinarith
      _ ≤ 2 ^ (2 * ell) := hbandpow
      _ < 2 ^ w.span := hpowlt
  have hdenpow : (4 : ℝ) * (D : ℝ) ^ 2 < (2 : ℝ) ^ w.span := by
    exact_mod_cast hdenpowNat
  have hdenpos : (0 : ℝ) < 4 * (D : ℝ) ^ 2 := by positivity
  have hrecip : 1 / (2 : ℝ) ^ w.span < 1 / (4 * (D : ℝ) ^ 2) :=
    one_div_lt_one_div_of_lt hdenpos hdenpow
  have hμcyl := lem_word_cylinder w (μ : ℝ) hμ.2.2
  have hνcyl := lem_word_cylinder w (ν : ℝ) hν.2.2
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ w.span := by positivity
  have hwidth :
      (((wordMultiplier w : ℝ) + 1) / (2 : ℝ) ^ w.span) -
          ((wordMultiplier w : ℝ) / (2 : ℝ) ^ w.span) =
        1 / (2 : ℝ) ^ w.span := by
    field_simp
    ring
  have habs : |(μ : ℝ) - (ν : ℝ)| < 1 / (2 : ℝ) ^ w.span := by
    rw [abs_lt]
    constructor <;> linarith [hμcyl.1, hμcyl.2, hνcyl.1, hνcyl.2, hwidth]
  have hfracne : (μ.num : ℚ) / μ.den ≠ (ν.num : ℚ) / ν.den := by
    intro heq
    apply hne
    rw [← μ.num_div_den, ← ν.num_div_den]
    exact heq
  have hfarey := lem_farey μ.num ν.num μ.den ν.den D
    (Rat.den_pos μ) (Rat.den_pos ν) hμ.2.1 hν.2.1 hfracne
  have hcastdiff :
      ((μ.num : ℝ) / μ.den - (ν.num : ℝ) / ν.den) =
        (μ : ℝ) - (ν : ℝ) := by
    simp only [Rat.cast_def]
  rw [hcastdiff] at hfarey
  linarith

theorem classifySlope_eq_interior_iff (μ : ℚ) :
    classifySlope μ = .interior ↔ μ ∈ Set.Ioo (0 : ℚ) 1 := by
  simp only [classifySlope, Set.mem_Ioo]
  split_ifs with h0 h1 hi
  · simp_all
  · simp_all
  · simp_all
  · simp_all

theorem GapWord.prefixSpan_firstPrefixAbove_le
    (w : GapWord) (bound : ℕ) :
    ∀ r < (w.firstPrefixAbove bound).length,
      (w.firstPrefixAbove bound).prefixSpan r ≤ bound := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAbove]
  | cons g gs ih =>
      simp only [firstPrefixAbove]
      by_cases hbg : bound < g
      · rw [if_pos hbg]
        intro r hr
        have hr0 : r = 0 := by simp at hr; omega
        subst r
        simp [GapWord.prefixSpan]
      · rw [if_neg hbg]
        intro r hr
        have hgle : g ≤ bound := Nat.le_of_not_gt hbg
        cases r with
        | zero => simp [GapWord.prefixSpan]
        | succ r =>
            have hrTail : r < (firstPrefixAbove gs (bound - g)).length := by
              simpa using hr
            have hrec := ih (bound - g) r hrTail
            simp only [GapWord.prefixSpan, List.take_succ_cons, List.sum_cons]
            simp only [GapWord.prefixSpan] at hrec
            omega

theorem IsInteriorTrajectory.tail (Q g : ℕ) (line : AffineLine)
    (gs : GapWord) (h : IsInteriorTrajectory Q line (g :: gs)) :
    IsInteriorTrajectory Q (line.transform Q g) gs := by
  intro r hr
  obtain ⟨state, htrajectory, hinterior⟩ := h (r + 1) (by simpa using hr)
  have hstate := (sharedGapTrajectory_iff_transformWord Q line _ _).mp htrajectory
  refine ⟨(line.transform Q g).transformWord Q (gs.take r),
    (sharedGapTrajectory_iff_transformWord Q (line.transform Q g) _ _).mpr rfl, ?_⟩
  have hstate' : state =
      (line.transform Q g).transformWord Q (gs.take r) := by
    simpa [AffineLine.transformWord] using hstate
  rw [← hstate']
  exact hinterior

theorem interiorWords_comparable (Q : ℕ) (hQ : 0 < Q)
    (u v : AffineLine) (w z : GapWord)
    (hslope : u.slope Q = v.slope Q)
    (hwpos : w.Positive) (hzpos : z.Positive)
    (hw : IsInteriorTrajectory Q u w)
    (hz : IsInteriorTrajectory Q v z) :
    w.IsPrefix z ∨ z.IsPrefix w := by
  induction w generalizing u v z with
  | nil => exact Or.inl List.nil_prefix
  | cons g gs ih =>
      cases z with
      | nil => exact Or.inr List.nil_prefix
      | cons h hs =>
          have hg : 1 ≤ g := hwpos g (by simp)
          have hh : 1 ≤ h := hzpos h (by simp)
          obtain ⟨u0, hu0traj, hu0int⟩ := hw 0 (by simp)
          obtain ⟨ug, hugtraj, hugint⟩ := hw 1 (by simp)
          obtain ⟨vh, hvhtraj, hvhint⟩ := hz 1 (by simp)
          have hu0 : u0 = u :=
            (sharedGapTrajectory_iff_transformWord Q u [] u0).mp hu0traj
          subst u0
          have hug : ug = u.transform Q g := by
            simpa [AffineLine.transformWord] using
              (sharedGapTrajectory_iff_transformWord Q u [g] ug).mp hugtraj
          have hvh : vh = v.transform Q h := by
            simpa [AffineLine.transformWord] using
              (sharedGapTrajectory_iff_transformWord Q v [h] vh).mp hvhtraj
          subst ug
          subst vh
          have hμ : (u.slope Q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
            have hμq : u.slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
              (classifySlope_eq_interior_iff _).mp hu0int
            exact ⟨by exact_mod_cast hμq.1, by exact_mod_cast hμq.2⟩
          have hgmem : g ∈ {d : ℕ | 1 ≤ d ∧
              (2 : ℝ) ^ d * (u.slope Q : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1} := by
            refine ⟨hg, ?_⟩
            have hnextq : (u.transform Q g).slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
              (classifySlope_eq_interior_iff _).mp hugint
            have hnext : ((u.transform Q g).slope Q : ℝ) ∈
                Set.Ioo (0 : ℝ) 1 :=
              ⟨by exact_mod_cast hnextq.1, by exact_mod_cast hnextq.2⟩
            rw [AffineLine.slope_transform Q hQ] at hnext
            exact_mod_cast hnext
          have hhmem : h ∈ {d : ℕ | 1 ≤ d ∧
              (2 : ℝ) ^ d * (u.slope Q : ℝ) - 1 ∈ Set.Ioo (0 : ℝ) 1} := by
            refine ⟨hh, ?_⟩
            have hnextq : (v.transform Q h).slope Q ∈ Set.Ioo (0 : ℚ) 1 :=
              (classifySlope_eq_interior_iff _).mp hvhint
            have hnext : ((v.transform Q h).slope Q : ℝ) ∈
                Set.Ioo (0 : ℝ) 1 :=
              ⟨by exact_mod_cast hnextq.1, by exact_mod_cast hnextq.2⟩
            rw [AffineLine.slope_transform Q hQ] at hnext
            rw [← hslope] at hnext
            exact_mod_cast hnext
          have hgh : g = h := (lem_strict_unique (u.slope Q : ℝ) hμ) hgmem hhmem
          subst h
          have hslope' : (u.transform Q g).slope Q =
              (v.transform Q g).slope Q := by
            rw [AffineLine.slope_transform Q hQ,
              AffineLine.slope_transform Q hQ, hslope]
          have htail := ih (u.transform Q g) (v.transform Q g) hs hslope'
            (by
              intro x hx
              exact hwpos x (by simp [hx]))
            (by
              intro x hx
              exact hzpos x (by simp [hx]))
            (IsInteriorTrajectory.tail Q g u gs hw)
            (IsInteriorTrajectory.tail Q g v hs hz)
          rcases htail with hpre | hpre
          · rcases hpre with ⟨tail, htail⟩
            refine Or.inl ⟨tail, ?_⟩
            simpa using congrArg (List.cons g) htail
          · rcases hpre with ⟨tail, htail⟩
            refine Or.inr ⟨tail, ?_⟩
            simpa using congrArg (List.cons g) htail

theorem crossingInteriorWords_eq (Q bound : ℕ) (hQ : 0 < Q)
    (u v : AffineLine) (w z : GapWord)
    (hslope : u.slope Q = v.slope Q)
    (hwpos : w.Positive) (hzpos : z.Positive)
    (hw : IsInteriorTrajectory Q u w)
    (hz : IsInteriorTrajectory Q v z)
    (hwcross : bound < w.span) (hzcross : bound < z.span)
    (hwminimal : ∀ r < w.length, w.prefixSpan r ≤ bound)
    (hzminimal : ∀ r < z.length, z.prefixSpan r ≤ bound) :
    w = z := by
  rcases interiorWords_comparable Q hQ u v w z hslope hwpos hzpos hw hz with
    hwz | hzw
  · by_contra hne
    have hlen : w.length < z.length :=
      lt_of_le_of_ne hwz.length_le (fun heq =>
        hne (hwz.eq_of_length heq))
    have htake : z.take w.length = w := (List.prefix_iff_eq_take.mp hwz).symm
    have hmin := hzminimal w.length hlen
    rw [GapWord.prefixSpan, htake] at hmin
    exact (Nat.not_lt_of_ge hmin) hwcross
  · by_contra hne
    have hlen : z.length < w.length :=
      lt_of_le_of_ne hzw.length_le (fun heq =>
        hne (hzw.eq_of_length heq).symm)
    have htake : w.take z.length = z := (List.prefix_iff_eq_take.mp hzw).symm
    have hmin := hwminimal z.length hlen
    rw [GapWord.prefixSpan, htake] at hmin
    exact (Nat.not_lt_of_ge hmin) hzcross

theorem primitiveLines_direction_eq_of_slope_eq
    (Q : ℕ) (hQ : 0 < Q) (u v : AffineLine)
    (hu : Int.gcd u.H u.K = 1) (hv : Int.gcd v.H v.K = 1)
    (hslope : u.slope Q = v.slope Q) :
    u.H = v.H ∧ u.K = v.K := by
  have hHnat : u.H.natAbs = v.H.natAbs := by
    rw [primitiveDirectionDenominator Q hQ u hu,
      primitiveDirectionDenominator Q hQ v hv, hslope]
  have huH : (u.H.natAbs : ℤ) = u.H :=
    Int.natAbs_of_nonneg u.H_pos.le
  have hvH : (v.H.natAbs : ℤ) = v.H :=
    Int.natAbs_of_nonneg v.H_pos.le
  have hH : u.H = v.H := by
    calc
      u.H = (u.H.natAbs : ℤ) := huH.symm
      _ = (v.H.natAbs : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hHnat
      _ = v.H := hvH
  refine ⟨hH, ?_⟩
  have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hH0 : (u.H : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt u.H_pos)
  rw [AffineLine.slope, AffineLine.slope, ← hH] at hslope
  field_simp [hQ0, hH0] at hslope
  exact_mod_cast hslope

theorem reconstructed_direction_forward_eq
    (Q Cgap : ℕ) (hQ : 0 < Q) (B Cstep : ℝ) (hB : 2 < B)
    (W : WindowSystem) (Z0 : ℕ) (selection : InteriorAnchorSelection)
    (σ : BlockEncoding)
    (k₁ k₂ : ℕ) (data₁ data₂ : AnchorInteriorData)
    (block₁ block₂ : LowGapBlock)
    (hrec₁ : IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      k₁ data₁ block₁ (sourceRawLine Q data₁ block₁).canonicalGeometricLine)
    (hrec₂ : IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      k₂ data₂ block₂ (sourceRawLine Q data₂ block₂).canonicalGeometricLine) :
    (sourceRawLine Q data₁ block₁).H =
        (sourceRawLine Q data₂ block₂).H ∧
      (sourceRawLine Q data₁ block₁).K =
        (sourceRawLine Q data₂ block₂).K ∧
      sourceForwardWord W Cgap data₁ block₁ =
        sourceForwardWord W Cgap data₂ block₂ := by
  rcases hrec₁ with
    ⟨hselected₁, hvalid₁, hfrequent₁, hblock₁, hoccurs₁,
      hoffset₁, hcandidate₁, hD₁, hencoding₁, hprimitive₁,
      hline₁, hstep₁, hrealizes₁, hgeometric₁, hblockTrajectory₁,
      hlower₁, hupper₁, hpositive₁, hinterior₁⟩
  rcases hrec₂ with
    ⟨hselected₂, hvalid₂, hfrequent₂, hblock₂, hoccurs₂,
      hoffset₂, hcandidate₂, hD₂, hencoding₂, hprimitive₂,
      hline₂, hstep₂, hrealizes₂, hgeometric₂, hblockTrajectory₂,
      hlower₂, hupper₂, hpositive₂, hinterior₂⟩
  have hlong : B * Nat.ceil (Real.logb 2 (4 * σ.D)) ≤ σ.gaps.span := by
    rw [← hcandidate₁.1.2.2.1]
    exact hcandidate₁.2.2.2.1
  have hgeometric₁' := hgeometric₁
  have hgeometric₂' := hgeometric₂
  unfold GeometricLineRealizesEncoding at hgeometric₁' hgeometric₂'
  rw [(sourceRawLine Q data₁ block₁).canonicalGeometricLine_slope Q hQ]
    at hgeometric₁'
  rw [(sourceRawLine Q data₂ block₂).canonicalGeometricLine_slope Q hQ]
    at hgeometric₂'
  have hslope : (sourceRawLine Q data₁ block₁).slope Q =
      (sourceRawLine Q data₂ block₂).slope Q :=
    (lem_word_slope B hB σ.D hD₁ σ.gaps hlong)
      hgeometric₁' hgeometric₂'
  obtain ⟨hH, hK⟩ := primitiveLines_direction_eq_of_slope_eq
    Q hQ (sourceRawLine Q data₁ block₁) (sourceRawLine Q data₂ block₂)
    hprimitive₁ hprimitive₂ hslope
  refine ⟨hH, hK, ?_⟩
  have hblockGaps₁ : block₁.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₁
  have hblockGaps₂ : block₂.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₂
  have hendSlope :
      (sourceBlockEndLine Q data₁ block₁).slope Q =
        (sourceBlockEndLine Q data₂ block₂).slope Q := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact AffineLine.transformWord_slope_eq_of_slope_eq Q hQ _ _ _ hslope
  let bound := 2 * W.L + Cgap
  apply crossingInteriorWords_eq Q bound hQ
    (sourceBlockEndLine Q data₁ block₁)
    (sourceBlockEndLine Q data₂ block₂)
    (sourceForwardWord W Cgap data₁ block₁)
    (sourceForwardWord W Cgap data₂ block₂)
    hendSlope hpositive₁ hpositive₂ hinterior₁ hinterior₂
    hlower₁ hlower₂
  · intro r hr
    exact GapWord.prefixSpan_firstPrefixAbove_le
      (sourceForwardSuffix data₁ block₁) bound r hr
  · intro r hr
    exact GapWord.prefixSpan_firstPrefixAbove_le
      (sourceForwardSuffix data₂ block₂) bound r hr

theorem prefix_enumerationGapWord_eq {S : Set ℕ}
    (e : SupportEnumeration S) (i n : ℕ) (word : GapWord)
    (hword : word.IsPrefix (enumerationGapWord e i n)) :
    word = enumerationGapWord e i word.length := by
  have hlen : word.length ≤ n := by
    have := hword.length_le
    simpa [enumerationGapWord] using this
  have hcanonical :
      (enumerationGapWord e i word.length).IsPrefix
        (enumerationGapWord e i n) := by
    rw [show n = word.length + (n - word.length) by omega,
      enumerationGapWord_append]
    exact List.prefix_append _ _
  have hwordTake := List.prefix_iff_eq_take.mp hword
  have hcanonicalTake := List.prefix_iff_eq_take.mp hcanonical
  have hcanonicalLength :
      (enumerationGapWord e i word.length).length = word.length := by
    simp [enumerationGapWord]
  calc
    word = (enumerationGapWord e i n).take word.length := hwordTake
    _ = (enumerationGapWord e i n).take
        (enumerationGapWord e i word.length).length := by
      rw [hcanonicalLength]
    _ = enumerationGapWord e i word.length := hcanonicalTake.symm

theorem drop_enumerationGapWord_eq {S : Set ℕ}
    (e : SupportEnumeration S) (i n offset : ℕ) (hoffset : offset ≤ n) :
    (enumerationGapWord e i n).drop offset =
      enumerationGapWord e (i + offset) (n - offset) := by
  rw [show n = offset + (n - offset) by omega,
    enumerationGapWord_append]
  simp [enumerationGapWord]

theorem actualPoint_intercept_bound
    (Q X x : ℕ) (R : RationalSupport) (hden : R.eta.den = Q)
    (line : AffineLine)
    (hcontains : line.Contains (x : ℤ) (carryInt R x))
    (hx : x ≤ 3 * X) (hX : 1 ≤ X)
    (hinterior : classifySlope (line.slope Q) = .interior) :
    |(line.interceptNumerator : ℝ)| ≤
      8 * (Q : ℝ) * (line.H : ℝ) * X := by
  have hQ : 0 < Q := by
    rw [← hden]
    exact Rat.den_pos R.eta
  have hμ := (classifySlope_eq_interior_iff _).mp hinterior
  have hQr : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hHr : (0 : ℚ) < line.H := by exact_mod_cast line.H_pos
  have hdenQ : (0 : ℚ) < (Q : ℚ) * (line.H : ℚ) :=
    mul_pos hQr hHr
  have hKq : (0 : ℚ) < line.K := by
    rw [AffineLine.slope] at hμ
    exact (div_pos_iff_of_pos_right hdenQ).mp hμ.1
  have hKltq : (line.K : ℚ) < (Q : ℚ) * line.H := by
    rw [AffineLine.slope] at hμ
    exact (div_lt_one hdenQ).mp hμ.2
  have hKnonneg : (0 : ℝ) ≤ line.K := by
    exact_mod_cast hKq.le
  have hKupper : (line.K : ℝ) ≤ (Q : ℝ) * line.H := by
    exact_mod_cast hKltq.le
  have hcarryNonneg : (0 : ℝ) ≤ carryInt R x := by
    exact_mod_cast (prop_carry R).2.1 x
  have hcarryUpper : (carryInt R x : ℝ) ≤ (Q : ℝ) * (x + 2) := by
    have hi := (prop_carry R).2.2.1 x
    rw [hden] at hi
    exact_mod_cast hi
  rcases hcontains with ⟨t, hcoord, hcarry⟩
  have hbInt : line.interceptNumerator =
      line.H * carryInt R x - line.K * (x : ℤ) := by
    unfold AffineLine.interceptNumerator
    rw [hcoord, hcarry]
    ring
  have hbReal : (line.interceptNumerator : ℝ) =
      (line.H : ℝ) * carryInt R x - (line.K : ℝ) * x := by
    exact_mod_cast hbInt
  rw [hbReal]
  have hHnonneg : (0 : ℝ) ≤ line.H := by exact_mod_cast line.H_pos.le
  have hxnonneg : (0 : ℝ) ≤ x := by positivity
  have hQnonneg : (0 : ℝ) ≤ Q := by positivity
  have hXreal : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hxreal : (x : ℝ) ≤ 3 * X := by exact_mod_cast hx
  have habs : |(line.H : ℝ) * carryInt R x - (line.K : ℝ) * x| ≤
      (line.H : ℝ) * carryInt R x + (line.K : ℝ) * x := by
    simpa [abs_of_nonneg (mul_nonneg hHnonneg hcarryNonneg),
      abs_of_nonneg (mul_nonneg hKnonneg hxnonneg)] using
        abs_sub_le ((line.H : ℝ) * carryInt R x) 0 ((line.K : ℝ) * x)
  calc
    |(line.H : ℝ) * carryInt R x - (line.K : ℝ) * x| ≤
        (line.H : ℝ) * carryInt R x + (line.K : ℝ) * x := habs
    _ ≤ (line.H : ℝ) * ((Q : ℝ) * (x + 2)) +
        ((Q : ℝ) * line.H) * x := by gcongr
    _ ≤ 8 * (Q : ℝ) * (line.H : ℝ) * X := by
      nlinarith [mul_nonneg hQnonneg hHnonneg,
        mul_nonneg (mul_nonneg hQnonneg hHnonneg)
          (zero_le_one.trans hXreal)]

theorem selectedBlockFollowWord_eq_enumerationGapWord
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block)) :
    block.gaps ++ word = enumerationGapWord W.enumeration
      (k - W.s + (initialLongPrefix W k).length + data.before.length +
        block.offset)
      (block.gaps.length + word.length) := by
  let start := k - W.s + (initialLongPrefix W k).length + data.before.length
  have hsegment := data.segmentGaps_eq_enumerationGapWord Q W Z0 k hvalid
  have hoffset : block.offset ≤ data.segment.gaps.length :=
    le_trans (Nat.le_add_right block.offset block.gaps.length) hoccurs.1
  have hdrop : data.segment.gaps.drop block.offset =
      enumerationGapWord W.enumeration (start + block.offset)
        (data.segment.gaps.length - block.offset) := by
    let n := data.segment.gaps.length
    calc
      data.segment.gaps.drop block.offset =
          (enumerationGapWord W.enumeration
            (k - W.s + (initialLongPrefix W k).length + data.before.length)
            n).drop block.offset := by rw [hsegment]
      _ = enumerationGapWord W.enumeration
          (k - W.s + (initialLongPrefix W k).length + data.before.length +
            block.offset) (n - block.offset) :=
        drop_enumerationGapWord_eq W.enumeration _ n block.offset hoffset
      _ = enumerationGapWord W.enumeration (start + block.offset)
          (data.segment.gaps.length - block.offset) := by rfl
  have hsplit : data.segment.gaps.drop block.offset =
      block.gaps ++ data.segment.gaps.drop (block.offset + block.gaps.length) := by
    calc
      data.segment.gaps.drop block.offset =
          (data.segment.gaps.drop block.offset).take block.gaps.length ++
            (data.segment.gaps.drop block.offset).drop block.gaps.length :=
        (List.take_append_drop _ _).symm
      _ = block.gaps ++
          data.segment.gaps.drop (block.offset + block.gaps.length) := by
        rw [hoccurs.2, List.drop_drop]
  have hprefix : (block.gaps ++ word).IsPrefix
      (data.segment.gaps.drop block.offset) := by
    rcases hword with ⟨tail, htail⟩
    refine ⟨tail, ?_⟩
    rw [hsplit]
    simp only [List.append_assoc]
    rw [htail]
    rfl
  rw [hdrop] at hprefix
  simpa [start, Nat.add_assoc] using
    prefix_enumerationGapWord_eq W.enumeration
      (start + block.offset) (data.segment.gaps.length - block.offset)
      (block.gaps ++ word) hprefix

theorem sourceBlockEnd_forward_contains
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (t : ℤ) (hparameter : IsOriginalSourceParameter Q W k data block t)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block)) :
    ((sourceBlockEndLine Q data block).transformWord Q word).Contains
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length))
      (carryInt W.rational (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length))) := by
  let i := k - W.s + (initialLongPrefix W k).length + data.before.length +
    block.offset
  have hstart : (sourceRawLine Q data block).Contains
      (W.enumeration.a i) (carryInt W.rational (W.enumeration.a i)) := by
    rcases hparameter with ⟨hx, hr, ht⟩
    have hi : k - W.s + sourceWindowOffset W k data block = i := by
      unfold sourceWindowOffset
      dsimp [i]
      omega
    change (W.enumeration.a (k - W.s + sourceWindowOffset W k data block) : ℤ) =
        (sourceRawLine Q data block).A + (sourceRawLine Q data block).H * t at hx
    change carryInt W.rational
        (W.enumeration.a (k - W.s + sourceWindowOffset W k data block)) =
          (sourceRawLine Q data block).C + (sourceRawLine Q data block).K * t at hr
    refine ⟨t, ?_, ?_⟩
    · rw [← hi]
      exact hx
    · rw [← hi]
      exact hr
  have hwordEnum := selectedBlockFollowWord_eq_enumerationGapWord
    Q W Z0 k data hvalid block hoccurs word hword
  have hpoint := (sourceRawLine Q data block).transformWord_contains_enumerationGapWord
    Q W.rational hden W.enumeration i (block.gaps.length + word.length) hstart
  rw [← hwordEnum, AffineLine.transformWord_append] at hpoint
  simpa [i, sourceBlockEndLine, Nat.add_assoc] using hpoint

theorem sourceEndpointIndex_le_succ
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block)) :
    k - W.s + (initialLongPrefix W k).length + data.before.length +
        block.offset + block.gaps.length + word.length ≤ k + 1 := by
  have hwordLen : word.length ≤ (sourceForwardSuffix data block).length :=
    hword.length_le
  have hblockEnd : block.offset + block.gaps.length ≤
      data.segment.gaps.length := hoccurs.1
  have hsourceSuffixLen : (sourceForwardSuffix data block).length =
      data.segment.gaps.length - (block.offset + block.gaps.length) := by
    simp [sourceForwardSuffix]
  rw [hsourceSuffixLen] at hwordLen
  obtain ⟨after, hactual⟩ := hvalid.2.2.2.2.2.1
  have hbeforeSegment : data.before.length + data.segment.gaps.length ≤
      (actualPostPrefixGaps W k).length := by
    rw [hactual]
    simp
  have hinitialPrefix : (initialLongPrefix W k).IsPrefix
      (W.rawWindowGapWord k) := GapWord.firstPrefixAbove_isPrefix _ _
  have hpLen : (initialLongPrefix W k).length ≤
      (W.rawWindowGapWord k).length := hinitialPrefix.length_le
  have hactualLen : (actualPostPrefixGaps W k).length =
      (W.rawWindowGapWord k).length - (initialLongPrefix W k).length := by
    simp [actualPostPrefixGaps]
  have hrawLen : (W.rawWindowGapWord k).length ≤ W.m :=
    rawWindowGapWord_length_le W k
  rw [hactualLen] at hbeforeSegment
  have hsk : W.s ≤ k := hvalid.1
  rw [WindowSystem.m] at hrawLen
  omega

theorem sourceEndpointCoordinate_le_threeX
    (Q Cgap : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (word : GapWord) (hword : word.IsPrefix (sourceForwardSuffix data block))
    (hgap : supportGap W.enumeration k ≤ W.L + Cgap + 1)
    (hscale : W.L + Cgap + 1 ≤ W.X) :
    W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length) ≤ 3 * W.X := by
  classical
  let j := k - W.s + (initialLongPrefix W k).length + data.before.length +
    block.offset + block.gaps.length + word.length
  have hj : j ≤ k + 1 := by
    exact sourceEndpointIndex_le_succ Q W Z0 k data hvalid block hoccurs
      word hword
  have hmono : W.enumeration.a j ≤ W.enumeration.a (k + 1) :=
    W.enumeration.strictMono.monotone hj
  have hkAnchor : k ∈ W.anchors := by
    have hhigh := hvalid.2.1
    rw [highAnchors, Finset.mem_filter] at hhigh
    exact hhigh.1
  have hkUpper : W.enumeration.a k ≤ 2 * W.X :=
    (Finset.mem_filter.mp hkAnchor).2.2
  have hnext : W.enumeration.a (k + 1) =
      W.enumeration.a k + supportGap W.enumeration k := by
    simp only [supportGap]
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono (Nat.lt_succ_self k)).le).symm
  dsimp [j] at hmono
  rw [hnext] at hmono
  omega

theorem AffineLine.transformWord_direction_eq
    (Q : ℕ) (u v : AffineLine) (word : GapWord)
    (hH : u.H = v.H) (hK : u.K = v.K) :
    (u.transformWord Q word).H = (v.transformWord Q word).H ∧
      (u.transformWord Q word).K = (v.transformWord Q word).K := by
  induction word generalizing u v with
  | nil => exact ⟨hH, hK⟩
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      apply ih
      · simpa [AffineLine.transform] using hH
      · simp only [AffineLine.transform]
        rw [hH, hK]

theorem IsInteriorTrajectory.start_interior
    (Q : ℕ) (line : AffineLine) (word : GapWord)
    (h : IsInteriorTrajectory Q line word) :
    classifySlope (line.slope Q) = .interior := by
  obtain ⟨state, htrajectory, hinterior⟩ := h 0 (by simp)
  have hstate := (sharedGapTrajectory_iff_transformWord Q line [] state).mp
    htrajectory
  rw [hstate] at hinterior
  simpa [AffineLine.transformWord] using hinterior

theorem IsInteriorTrajectory.end_interior
    (Q : ℕ) (line : AffineLine) (word : GapWord)
    (h : IsInteriorTrajectory Q line word) :
    classifySlope ((line.transformWord Q word).slope Q) = .interior := by
  obtain ⟨state, htrajectory, hinterior⟩ := h word.length (by simp)
  have hstate := (sharedGapTrajectory_iff_transformWord Q line
    (word.take word.length) state).mp htrajectory
  rw [hstate] at hinterior
  simpa using hinterior

theorem supportGap_mem_rawWindowGapWord
    (W : WindowSystem) (k : ℕ) (hsk : W.s ≤ k) :
    supportGap W.enumeration k ∈ W.rawWindowGapWord k := by
  rw [WindowSystem.rawWindowGapWord, dif_pos hsk]
  simp only [WindowSystem.window, windowGapWord, List.mem_map, List.mem_range]
  refine ⟨W.s, ?_, ?_⟩
  · simp
  · congr 1
    omega

theorem two_mul_le_two_pow (L : ℕ) (hL : 1 ≤ L) :
    2 * L ≤ 2 ^ L := by
  induction L with
  | zero => omega
  | succ L ih =>
      by_cases hL0 : L = 0
      · subst L
        norm_num
      · have hLpos : 1 ≤ L := by omega
        have hrec := ih hLpos
        rw [pow_succ]
        nlinarith

theorem frequencyCutoff_tendsto (context : FixedScaleContext)
    (F : ScaleFamily) (hF : F.MatchesContext context) :
    Tendsto (fun L : ℕ => frequencyCutoff (F.system L)) atTop atTop := by
  have hXtop : Tendsto (fun L : ℕ => ((F.system L).X : ℝ)) atTop atTop := by
    simpa [WindowSystem.X, F.level_eq, dyadicScale] using
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num))
  have hexponent : 0 < (1 : ℝ) / 2 + context.structural.rho := by
    linarith [context.structural.rho_pos]
  have hpow := (tendsto_rpow_atTop hexponent).comp hXtop
  apply hpow.congr'
  filter_upwards [] with L
  unfold frequencyCutoff
  rw [F.structural_eq L, hF.2.1]
  rfl

theorem eventually_scale_dominates_gap (Cgap : ℕ) (F : ScaleFamily) :
    ∀ᶠ L : ℕ in atTop,
      (F.system L).L + Cgap + 1 ≤ (F.system L).X := by
  filter_upwards [eventually_ge_atTop (max 1 (Cgap + 1))] with L hL
  have hLone : 1 ≤ L := (le_max_left _ _).trans hL
  have hLC : Cgap + 1 ≤ L := (le_max_right _ _).trans hL
  rw [F.level_eq, WindowSystem.X, F.level_eq, dyadicScale]
  have htwo := two_mul_le_two_pow L hLone
  omega

theorem reconstructed_endpoint_intercept_bounds
    (Q Cgap : ℕ) (B Cstep : ℝ) (W : WindowSystem) (Z0 k : ℕ)
    (selection : InteriorAnchorSelection) (σ : BlockEncoding)
    (data : AnchorInteriorData) (block : LowGapBlock)
    (hden : W.rational.eta.den = Q)
    (hgap : ∀ j : ℕ, j ∈ W.anchors →
      ∀ g ∈ W.rawWindowGapWord j, g ≤ W.L + Cgap + 1)
    (hscale : W.L + Cgap + 1 ≤ W.X)
    (hrec : IsReconstructedOccurrenceLine Q Cgap B Cstep W Z0 selection σ
      k data block (sourceRawLine Q data block).canonicalGeometricLine)
    (t : ℤ) (hparameter : IsOriginalSourceParameter Q W k data block t) :
    |((sourceBlockEndLine Q data block).interceptNumerator : ℝ)| ≤
        8 * (Q : ℝ) * ((sourceBlockEndLine Q data block).H : ℝ) * W.X ∧
      |(((sourceBlockEndLine Q data block).transformWord Q
          (sourceForwardWord W Cgap data block)).interceptNumerator : ℝ)| ≤
        8 * (Q : ℝ) *
          (((sourceBlockEndLine Q data block).transformWord Q
            (sourceForwardWord W Cgap data block)).H : ℝ) * W.X := by
  classical
  rcases hrec with
    ⟨_hselected, hvalid, _hfrequent, _hblock, hoccurs, _hoffset,
      _hcandidate, _hD, _hencoding, _hprimitive, _hline, _hstep,
      _hrealizes, _hgeometric, _hblockTrajectory, _hlower, _hupper,
      _hpositive, hinterior⟩
  let word := sourceForwardWord W Cgap data block
  have hword : word.IsPrefix (sourceForwardSuffix data block) := by
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hkAnchor : k ∈ W.anchors := by
    have hhigh := hvalid.2.1
    rw [highAnchors, Finset.mem_filter] at hhigh
    exact hhigh.1
  have hgapAt : supportGap W.enumeration k ≤ W.L + Cgap + 1 :=
    hgap k hkAnchor _ (supportGap_mem_rawWindowGapWord W k hvalid.1)
  have hXone : 1 ≤ W.X := by
    rw [WindowSystem.X, dyadicScale]
    exact Left.one_le_pow_of_le (by norm_num : (1 : ℕ) ≤ 2) W.L
  have hendContains := sourceBlockEnd_forward_contains Q W Z0 k hden
    data hvalid block hoccurs t hparameter [] List.nil_prefix
  have hendCoord := sourceEndpointCoordinate_le_threeX Q Cgap W Z0 k
    data hvalid block hoccurs [] List.nil_prefix hgapAt hscale
  have hfinalContains := sourceBlockEnd_forward_contains Q W Z0 k hden
    data hvalid block hoccurs t hparameter word hword
  have hfinalCoord := sourceEndpointCoordinate_le_threeX Q Cgap W Z0 k
    data hvalid block hoccurs word hword hgapAt hscale
  have hstartInterior := IsInteriorTrajectory.start_interior Q
    (sourceBlockEndLine Q data block) word hinterior
  have hendInterior := IsInteriorTrajectory.end_interior Q
    (sourceBlockEndLine Q data block) word hinterior
  constructor
  · simpa [word, AffineLine.transformWord] using
      actualPoint_intercept_bound Q W.X
        (W.enumeration.a
          (k - W.s + (initialLongPrefix W k).length + data.before.length +
            block.offset + block.gaps.length + [].length))
        W.rational hden (sourceBlockEndLine Q data block)
        (by simpa [AffineLine.transformWord] using hendContains)
        hendCoord hXone hstartInterior
  · exact actualPoint_intercept_bound Q W.X
      (W.enumeration.a
        (k - W.s + (initialLongPrefix W k).length + data.before.length +
          block.offset + block.gaps.length + word.length))
      W.rational hden
      ((sourceBlockEndLine Q data block).transformWord Q word)
      hfinalContains hfinalCoord hXone hendInterior

theorem intercept_eq_of_long_transform
    (Q X : ℕ) (Cstep frequency : ℝ) (u v : AffineLine) (word : GapWord)
    (hQ : 0 < Q) (hCstep : 0 < Cstep) (hX : 0 < X)
    (hfrequency : 16 * (Q : ℝ) * Cstep < frequency)
    (hH : u.H = v.H) (hK : u.K = v.K)
    (hstep : (u.H : ℝ) ≤ Cstep * X / frequency)
    (hspan : (X : ℝ) ^ 2 < (2 : ℝ) ^ word.span)
    (huBound : |((u.transformWord Q word).interceptNumerator : ℝ)| ≤
      8 * (Q : ℝ) * (u.H : ℝ) * X)
    (hvBound : |((v.transformWord Q word).interceptNumerator : ℝ)| ≤
      8 * (Q : ℝ) * (u.H : ℝ) * X) :
    u.interceptNumerator = v.interceptNumerator := by
  by_contra hne
  let δ : ℤ := u.interceptNumerator - v.interceptNumerator
  have hδne : δ ≠ 0 := sub_ne_zero.mpr hne
  have hδabsInt : (1 : ℤ) ≤ |δ| := by
    exact Int.add_one_le_iff.mpr (abs_pos.mpr hδne)
  have hδabs : (1 : ℝ) ≤ |(δ : ℝ)| := by
    exact_mod_cast hδabsInt
  have hmonoInt := AffineLine.interceptDifference_transformWord
    Q u v word hH hK
  have hmonoReal :
      ((u.transformWord Q word).interceptNumerator : ℝ) -
          ((v.transformWord Q word).interceptNumerator : ℝ) =
        (2 : ℝ) ^ word.span * (δ : ℝ) := by
    exact_mod_cast hmonoInt
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ word.span := by positivity
  have hpowLeDiff : (2 : ℝ) ^ word.span ≤
      |((u.transformWord Q word).interceptNumerator : ℝ) -
        ((v.transformWord Q word).interceptNumerator : ℝ)| := by
    rw [hmonoReal, abs_mul, abs_of_pos hpowPos]
    nlinarith
  have hdiffUpper :
      |((u.transformWord Q word).interceptNumerator : ℝ) -
          ((v.transformWord Q word).interceptNumerator : ℝ)| ≤
        16 * (Q : ℝ) * (u.H : ℝ) * X := by
    calc
      |((u.transformWord Q word).interceptNumerator : ℝ) -
          ((v.transformWord Q word).interceptNumerator : ℝ)| ≤
          |((u.transformWord Q word).interceptNumerator : ℝ)| +
            |((v.transformWord Q word).interceptNumerator : ℝ)| :=
        abs_sub _ _
      _ ≤ 16 * (Q : ℝ) * (u.H : ℝ) * X := by
        nlinarith
  have hfrequencyPos : 0 < frequency := by
    have hQC : 0 < 16 * (Q : ℝ) * Cstep := by positivity
    linarith
  have hHfrequency : (u.H : ℝ) * frequency ≤ Cstep * X := by
    exact (le_div_iff₀ hfrequencyPos).mp hstep
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hHreal : (0 : ℝ) < u.H := by exact_mod_cast u.H_pos
  have hpowUpper : (2 : ℝ) ^ word.span ≤
      16 * (Q : ℝ) * (u.H : ℝ) * X :=
    hpowLeDiff.trans hdiffUpper
  have hmulUpper : (2 : ℝ) ^ word.span * frequency ≤
      (16 * (Q : ℝ) * Cstep) * (X : ℝ) ^ 2 := by
    calc
      (2 : ℝ) ^ word.span * frequency ≤
          (16 * (Q : ℝ) * (u.H : ℝ) * X) * frequency := by
        exact mul_le_mul_of_nonneg_right hpowUpper hfrequencyPos.le
      _ = (16 * (Q : ℝ) * X) * ((u.H : ℝ) * frequency) := by ring
      _ ≤ (16 * (Q : ℝ) * X) * (Cstep * X) := by
        exact mul_le_mul_of_nonneg_left hHfrequency (by positivity)
      _ = (16 * (Q : ℝ) * Cstep) * (X : ℝ) ^ 2 := by ring
  have hconstantPos : 0 < 16 * (Q : ℝ) * Cstep := by positivity
  have hpowRealPos : 0 < (2 : ℝ) ^ word.span := by positivity
  have hmulLower₁ :
      (X : ℝ) ^ 2 * (16 * (Q : ℝ) * Cstep) <
        (2 : ℝ) ^ word.span * (16 * (Q : ℝ) * Cstep) :=
    mul_lt_mul_of_pos_right hspan hconstantPos
  have hmulLower₂ :
      (2 : ℝ) ^ word.span * (16 * (Q : ℝ) * Cstep) <
        (2 : ℝ) ^ word.span * frequency :=
    mul_lt_mul_of_pos_left hfrequency hpowRealPos
  have hmulLower :
      (16 * (Q : ℝ) * Cstep) * (X : ℝ) ^ 2 <
        (2 : ℝ) ^ word.span * frequency := by
    rw [mul_comm (16 * (Q : ℝ) * Cstep) ((X : ℝ) ^ 2)]
    exact hmulLower₁.trans hmulLower₂
  linarith

theorem forward_span_power (Cgap : ℕ) (W : WindowSystem)
    (word : GapWord) (hspan : 2 * W.L + Cgap < word.span) :
    (W.X : ℝ) ^ 2 < (2 : ℝ) ^ word.span := by
  have hexponent : 2 * W.L < word.span := by omega
  have hnat : 2 ^ (2 * W.L) < 2 ^ word.span :=
    Nat.pow_lt_pow_right (by omega) hexponent
  have hreal : (2 : ℝ) ^ (2 * W.L) < (2 : ℝ) ^ word.span := by
    exact_mod_cast hnat
  rw [WindowSystem.X, dyadicScale, Nat.cast_pow, Nat.cast_ofNat]
  convert hreal using 1
  ring

theorem AffineLine.canonicalGeometricLine_eq_of_primitive_direction_intercept
    (u v : AffineLine) (hu : Int.gcd u.H u.K = 1)
    (hv : Int.gcd v.H v.K = 1) (hH : u.H = v.H) (hK : u.K = v.K)
    (hb : u.interceptNumerator = v.interceptNumerator) :
    u.canonicalGeometricLine = v.canonicalGeometricLine := by
  unfold AffineLine.canonicalGeometricLine AffineLine.primitiveHorizontalInt
    AffineLine.primitiveVertical AffineLine.directionGCD
  simp only [hu, hv]
  congr 1
  · simpa using congrArg Int.natAbs hH
  · simpa using hK
  · simpa using hb

/-- Paper label: `lem:line-unique` (Section 6). -/
theorem lem_line_unique (context : FixedScaleContext)
    (gap : GapParams context.Q) (Cstep : ℝ) (hCstep : 0 < Cstep) :
    ∃ Zmin : ℕ,
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∀ selection : InteriorAnchorSelection,
              ValidInteriorAnchorSelection context.Q (F.system L) Z0 selection →
                ∀ σ : BlockEncoding,
                  σ ∈ encodingCandidates σ.D σ.Z context.structural.B →
                    0 < σ.D →
                      Set.Subsingleton
                        (spatialCanonicalLines context.Q gap.Cgap
                          context.structural.B Cstep (F.system L) Z0
                          selection σ) := by
  classical
  refine ⟨0, ?_⟩
  intro Z0 _hZ0 F hF
  have hfrequencyTop := frequencyCutoff_tendsto context F hF
  have hfrequencyEventually : ∀ᶠ L : ℕ in atTop,
      16 * (context.Q : ℝ) * Cstep < frequencyCutoff (F.system L) := by
    filter_upwards [tendsto_atTop.1 hfrequencyTop
      (16 * (context.Q : ℝ) * Cstep + 1)] with L hL
    linarith
  filter_upwards [eventually_rawWindowGap_le context gap F hF,
    eventually_scale_dominates_gap gap.Cgap F,
    hfrequencyEventually] with L hgapL hscaleL hfrequencyL
  intro selection _hselection σ _hσ _hD
  rintro line₁ ⟨k₁, data₁, block₁, hsource₁, hselected₁, hline₁⟩
    line₂ ⟨k₂, data₂, block₂, hsource₂, hselected₂, hline₂⟩
  change IsSpatialEncodingSource context.Q gap.Cgap context.structural.B
    Cstep (F.system L) Z0 selection σ (k₁, block₁) at hsource₁
  change IsSpatialEncodingSource context.Q gap.Cgap context.structural.B
    Cstep (F.system L) Z0 selection σ (k₂, block₂) at hsource₂
  rcases hsource₁ with ⟨data₁', t₁, hrec₁', hparameter₁'⟩
  rcases hsource₂ with ⟨data₂', t₂, hrec₂', hparameter₂'⟩
  have hdata₁ : data₁' = data₁ := by
    apply Option.some.inj
    exact hrec₁'.1.symm.trans hselected₁
  have hdata₂ : data₂' = data₂ := by
    apply Option.some.inj
    exact hrec₂'.1.symm.trans hselected₂
  subst data₁'
  subst data₂'
  have hrec₁ := hrec₁'
  have hrec₂ := hrec₂'
  have hparameter₁ := hparameter₁'
  have hparameter₂ := hparameter₂'
  obtain ⟨hrawH, hrawK, hword⟩ := reconstructed_direction_forward_eq
    context.Q gap.Cgap context.Q_pos context.structural.B Cstep
      context.structural.B_gt (F.system L) Z0 selection σ
      k₁ k₂ data₁ data₂ block₁ block₂ hrec₁ hrec₂
  have hden : (F.system L).rational.eta.den = context.Q := by
    rw [F.rational_eq]
    exact hF.1
  have hgapW : ∀ j : ℕ, j ∈ (F.system L).anchors →
      ∀ g ∈ (F.system L).rawWindowGapWord j,
        g ≤ (F.system L).L + gap.Cgap + 1 := by
    intro j hj g hg
    rw [F.level_eq]
    exact hgapL j hj g hg
  have hbounds₁ := reconstructed_endpoint_intercept_bounds
    context.Q gap.Cgap context.structural.B Cstep (F.system L) Z0 k₁
      selection σ data₁ block₁ hden hgapW hscaleL hrec₁ t₁ hparameter₁
  have hbounds₂ := reconstructed_endpoint_intercept_bounds
    context.Q gap.Cgap context.structural.B Cstep (F.system L) Z0 k₂
      selection σ data₂ block₂ hden hgapW hscaleL hrec₂ t₂ hparameter₂
  rcases hrec₁' with
    ⟨_hselectedRec₁, _hvalid₁, _hfrequent₁, _hblock₁, _hoccurs₁,
      _hoffset₁, _hcandidate₁, _hD₁, hencoding₁, hprimitive₁,
      _hlineRec₁, hstep₁, _hrealizes₁, _hgeometric₁,
      _hblockTrajectory₁, hlower₁, _hupper₁, _hpositive₁, _hinterior₁⟩
  rcases hrec₂' with
    ⟨_hselectedRec₂, _hvalid₂, _hfrequent₂, _hblock₂, _hoccurs₂,
      _hoffset₂, _hcandidate₂, _hD₂, hencoding₂, hprimitive₂,
      _hlineRec₂, _hstep₂, _hrealizes₂, _hgeometric₂,
      _hblockTrajectory₂, _hlower₂, _hupper₂, _hpositive₂, _hinterior₂⟩
  have hblockGaps₁ : block₁.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₁
  have hblockGaps₂ : block₂.gaps = σ.gaps :=
    congrArg BlockEncoding.gaps hencoding₂
  have hendH : (sourceBlockEndLine context.Q data₁ block₁).H =
      (sourceBlockEndLine context.Q data₂ block₂).H := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact (AffineLine.transformWord_direction_eq context.Q
      (sourceRawLine context.Q data₁ block₁)
      (sourceRawLine context.Q data₂ block₂) σ.gaps hrawH hrawK).1
  have hendK : (sourceBlockEndLine context.Q data₁ block₁).K =
      (sourceBlockEndLine context.Q data₂ block₂).K := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact (AffineLine.transformWord_direction_eq context.Q
      (sourceRawLine context.Q data₁ block₁)
      (sourceRawLine context.Q data₂ block₂) σ.gaps hrawH hrawK).2
  have hcanonHInt :
      ((sourceRawLine context.Q data₁ block₁).canonicalGeometricLine.H : ℤ) =
        (sourceRawLine context.Q data₁ block₁).H := by
    rw [(sourceRawLine context.Q data₁ block₁).canonicalGeometricLine_H_cast]
    simp [AffineLine.primitiveHorizontalInt, AffineLine.directionGCD,
      hprimitive₁]
  have hcanonHReal :
      ((sourceRawLine context.Q data₁ block₁).canonicalGeometricLine.H : ℝ) =
        ((sourceRawLine context.Q data₁ block₁).H : ℝ) := by
    exact_mod_cast hcanonHInt
  have hrawStep : ((sourceRawLine context.Q data₁ block₁).H : ℝ) ≤
      Cstep * (F.system L).X / frequencyCutoff (F.system L) := by
    rw [← hcanonHReal]
    exact hstep₁
  have hendRawH : (sourceBlockEndLine context.Q data₁ block₁).H =
      (sourceRawLine context.Q data₁ block₁).H := by
    exact AffineLine.transformWord_H context.Q _ _
  have hendStep : ((sourceBlockEndLine context.Q data₁ block₁).H : ℝ) ≤
      Cstep * (F.system L).X / frequencyCutoff (F.system L) := by
    rw [hendRawH]
    exact hrawStep
  have huBound :
      |(((sourceBlockEndLine context.Q data₁ block₁).transformWord context.Q
          (sourceForwardWord (F.system L) gap.Cgap data₁ block₁)).interceptNumerator : ℝ)| ≤
        8 * (context.Q : ℝ) *
          ((sourceBlockEndLine context.Q data₁ block₁).H : ℝ) *
            (F.system L).X := by
    simpa only [AffineLine.transformWord_H] using hbounds₁.2
  have hvBound :
      |(((sourceBlockEndLine context.Q data₂ block₂).transformWord context.Q
          (sourceForwardWord (F.system L) gap.Cgap data₁ block₁)).interceptNumerator : ℝ)| ≤
        8 * (context.Q : ℝ) *
          ((sourceBlockEndLine context.Q data₁ block₁).H : ℝ) *
            (F.system L).X := by
    rw [hword, hendH]
    simpa only [AffineLine.transformWord_H] using hbounds₂.2
  have hspanPower : ((F.system L).X : ℝ) ^ 2 <
      (2 : ℝ) ^ (sourceForwardWord (F.system L) gap.Cgap data₁ block₁).span :=
    forward_span_power gap.Cgap (F.system L)
      (sourceForwardWord (F.system L) gap.Cgap data₁ block₁) hlower₁
  have hXpos : 0 < (F.system L).X := by
    rw [WindowSystem.X, dyadicScale]
    positivity
  have hendIntercept :
      (sourceBlockEndLine context.Q data₁ block₁).interceptNumerator =
        (sourceBlockEndLine context.Q data₂ block₂).interceptNumerator := by
    apply intercept_eq_of_long_transform context.Q (F.system L).X
      Cstep (frequencyCutoff (F.system L))
      (sourceBlockEndLine context.Q data₁ block₁)
      (sourceBlockEndLine context.Q data₂ block₂)
      (sourceForwardWord (F.system L) gap.Cgap data₁ block₁)
      context.Q_pos hCstep hXpos hfrequencyL hendH hendK hendStep
      hspanPower huBound hvBound
  have hblockMono :
      (sourceBlockEndLine context.Q data₁ block₁).interceptNumerator -
          (sourceBlockEndLine context.Q data₂ block₂).interceptNumerator =
        (2 : ℤ) ^ σ.gaps.span *
          ((sourceRawLine context.Q data₁ block₁).interceptNumerator -
            (sourceRawLine context.Q data₂ block₂).interceptNumerator) := by
    unfold sourceBlockEndLine
    rw [hblockGaps₁, hblockGaps₂]
    exact AffineLine.interceptDifference_transformWord context.Q
      (sourceRawLine context.Q data₁ block₁)
      (sourceRawLine context.Q data₂ block₂) σ.gaps hrawH hrawK
  have hrawIntercept :
      (sourceRawLine context.Q data₁ block₁).interceptNumerator =
        (sourceRawLine context.Q data₂ block₂).interceptNumerator := by
    have hproduct : (2 : ℤ) ^ σ.gaps.span *
        ((sourceRawLine context.Q data₁ block₁).interceptNumerator -
          (sourceRawLine context.Q data₂ block₂).interceptNumerator) = 0 := by
      rw [← hblockMono, hendIntercept]
      simp
    have hpowNe : (2 : ℤ) ^ σ.gaps.span ≠ 0 := pow_ne_zero _ (by norm_num)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hpowNe)
  have hcanonical :
      (sourceRawLine context.Q data₁ block₁).canonicalGeometricLine =
        (sourceRawLine context.Q data₂ block₂).canonicalGeometricLine :=
    AffineLine.canonicalGeometricLine_eq_of_primitive_direction_intercept
      _ _ hprimitive₁ hprimitive₂ hrawH hrawK hrawIntercept
  calc
    line₁ = (sourceRawLine context.Q data₁ block₁).canonicalGeometricLine := hline₁.symm
    _ = (sourceRawLine context.Q data₂ block₂).canonicalGeometricLine := hcanonical
    _ = line₂ := hline₂

/-- Paper label: `lem:source-fibre` (Section 6).

The remaining proof uses: `lem_line_unique`; the primitive raw-line
converse to `AffineLine.contains_canonicalGeometricLine`; equality of raw and
canonical normalized slopes in the primitive case; and finite-cardinality
transport through `spatialSourceCode_injective`.  None of these facts is
encoded as an assumption in the source data. -/
theorem lem_source_fibre (context : FixedScaleContext)
    (gap : GapParams context.Q) (Cstep : ℝ) (hCstep : 0 < Cstep) :
    ∃ Zmin : ℕ,
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∀ selection : InteriorAnchorSelection,
              ValidInteriorAnchorSelection context.Q (F.system L) Z0 selection →
                ∀ σ : BlockEncoding,
                  σ ∈ encodingCandidates σ.D σ.Z context.structural.B →
                    0 < σ.D →
                      (spatialPreimage context.Q gap.Cgap
                          context.structural.B Cstep (F.system L) Z0
                          selection σ).Finite ∧
                        ((spatialPreimage context.Q gap.Cgap
                            context.structural.B Cstep (F.system L) Z0
                            selection σ).ncard : ℝ) ≤
                          (context.Q : ℝ) * (Cstep + 4) *
                            (F.system L).m * (F.system L).X / σ.D := by
  classical
  obtain ⟨Zmin, hline⟩ := lem_line_unique context gap Cstep hCstep
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0 F hF
  filter_upwards [hline Z0 hZ0 F hF] with L hlineL
  intro selection hselection σ hσ hD
  let W := F.system L
  let S := spatialPreimage context.Q gap.Cgap context.structural.B
    Cstep W Z0 selection σ
  have hsubsingleton := hlineL selection hselection σ hσ hD
  by_cases hSne : S.Nonempty
  · rcases hSne with ⟨⟨k₀, block₀⟩, hsource₀⟩
    have hsource₀' := hsource₀
    change IsSpatialEncodingSource context.Q gap.Cgap
      context.structural.B Cstep W Z0 selection σ (k₀, block₀) at hsource₀'
    rcases hsource₀' with ⟨data₀, t₀, hrec₀, hparameter₀⟩
    rcases hrec₀ with
      ⟨hselected₀, hvalid₀, hfrequent₀, hblock₀, hoccurs₀,
        hoffset₀, hcandidate₀, hD₀, hencoding₀, hprimitive₀,
        hline₀, hstep₀, hrealizes₀, hgeometric₀, hblockTrajectory₀,
        hlower₀, hupper₀, hpositive₀, hinterior₀⟩
    let base := sourceRawLine context.Q data₀ block₀
    have hbaseMem : base.canonicalGeometricLine ∈
        spatialCanonicalLines context.Q gap.Cgap context.structural.B
          Cstep W Z0 selection σ := by
      exact ⟨k₀, data₀, block₀, hsource₀, hselected₀, rfl⟩
    let P : Set ℤ := horizontalParameters W.X base
    let J : Set ℕ := Set.Iio W.m
    let parameterCode : ℤ × ℕ → Option (ℕ × ℕ) := fun tj =>
      some ((base.A + base.H * tj.1).toNat, tj.2)
    let envelope : Set (Option (ℕ × ℕ)) := parameterCode '' (P ×ˢ J)
    have hPfinite : P.Finite := by
      exact (lem_primitive_direction context.Q W.X context.Q_pos base
        hprimitive₀).2.1
    have hPJfinite : (P ×ˢ J).Finite :=
      hPfinite.prod (Set.finite_Iio W.m)
    have henvelopeFinite : envelope.Finite := hPJfinite.image parameterCode
    have himageSubset : spatialSourceCode W selection '' S ⊆ envelope := by
      rintro _ ⟨⟨k, block⟩, hsource, rfl⟩
      have hsource' := hsource
      change IsSpatialEncodingSource context.Q gap.Cgap
        context.structural.B Cstep W Z0 selection σ (k, block) at hsource'
      rcases hsource' with ⟨data, tsource, hrec, hparameter⟩
      rcases hrec with
        ⟨hselected, hvalid, hfrequent, hblock, hoccurs,
          hoffset, hcandidate, hDsource, hencoding, hprimitive,
          hline, hstep, hrealizes, hgeometric, hblockTrajectory,
          hlower, hupper, hpositive, hinterior⟩
      have hlineMem : (sourceRawLine context.Q data block).canonicalGeometricLine ∈
          spatialCanonicalLines context.Q gap.Cgap context.structural.B
            Cstep W Z0 selection σ :=
        ⟨k, data, block, hsource, hselected, rfl⟩
      have hlineEq : base.canonicalGeometricLine =
          (sourceRawLine context.Q data block).canonicalGeometricLine :=
        hsubsingleton hbaseMem hlineMem
      have hxOwn := sourceCoordinate_on_canonicalLine context.Q W k data block
        tsource hparameter
      have hxBase : base.canonicalGeometricLine.Contains
          (sourceCoordinate W k data block : ℤ)
          (carryInt W.rational (sourceCoordinate W k data block)) := by
        rw [hlineEq]
        exact hxOwn
      obtain ⟨t, hxt, hrt⟩ :=
        base.contains_of_canonicalGeometricLine_of_primitive hprimitive₀
          (sourceCoordinate W k data block : ℤ)
          (carryInt W.rational (sourceCoordinate W k data block)) hxBase
      have hsourceCorridor :=
        originalSourceParameter_mem_corridor context.Q W k data block
          tsource hparameter
      have hxsource := hparameter.1
      change -(W.X : ℤ) ≤
          (sourceRawLine context.Q data block).A +
              (sourceRawLine context.Q data block).H * tsource ∧
        (sourceRawLine context.Q data block).A +
              (sourceRawLine context.Q data block).H * tsource ≤
            3 * W.X at hsourceCorridor
      rw [← hxsource] at hsourceCorridor
      have htP : t ∈ P := by
        change -(W.X : ℤ) ≤ base.A + base.H * t ∧
          base.A + base.H * t ≤ 3 * W.X
        rw [← hxt]
        exact hsourceCorridor
      have htJ : sourceWindowOffset W k data block ∈ J := hoffset
      refine ⟨(t, sourceWindowOffset W k data block), ⟨htP, htJ⟩, ?_⟩
      have htoNat : (base.A + base.H * t).toNat =
          sourceCoordinate W k data block := by
        rw [← hxt]
        simp
      rw [spatialSourceCode_of_selected W selection k block data hselected]
      simp [parameterCode, htoNat]
    have hcodeImageFinite : (spatialSourceCode W selection '' S).Finite :=
      henvelopeFinite.subset himageSubset
    have hinjective := spatialSourceCode_injective context.Q gap.Cgap
      context.structural.B Cstep W Z0 selection σ
    have hSfinite : S.Finite :=
      Set.Finite.of_finite_image hcodeImageFinite hinjective
    refine ⟨hSfinite, ?_⟩
    have hcardImage : S.ncard =
        (spatialSourceCode W selection '' S).ncard :=
      hinjective.ncard_image.symm
    have hcardSubset :
        (spatialSourceCode W selection '' S).ncard ≤ envelope.ncard :=
      Set.ncard_le_ncard himageSubset henvelopeFinite
    have hcardEnvelope : envelope.ncard ≤ (P ×ˢ J).ncard := by
      exact Set.ncard_image_le hPJfinite
    have hcardNat : S.ncard ≤ P.ncard * W.m := by
      rw [hcardImage]
      calc
        (spatialSourceCode W selection '' S).ncard ≤ envelope.ncard := hcardSubset
        _ ≤ (P ×ˢ J).ncard := hcardEnvelope
        _ = P.ncard * J.ncard := Set.ncard_prod
        _ = P.ncard * W.m := by rw [Set.ncard_Iio_nat]
    have hcardReal : (S.ncard : ℝ) ≤ (P.ncard : ℝ) * W.m := by
      exact_mod_cast hcardNat
    have hPbound := (lem_primitive_direction context.Q W.X context.Q_pos base
      hprimitive₀).2.2
    have hdenBand : σ.D ≤ (base.slope context.Q).den := hrealizes₀.1
    have hHden := (lem_primitive_direction context.Q W.X context.Q_pos base
      hprimitive₀).1
    have hgcdLe : Nat.gcd (base.slope context.Q).den context.Q ≤ context.Q :=
      Nat.gcd_le_right _ context.Q_pos
    have hgcdDvd : Nat.gcd (base.slope context.Q).den context.Q ∣
        (base.slope context.Q).den := Nat.gcd_dvd_left _ _
    have hdenStepNat : (base.slope context.Q).den ≤
        base.H.natAbs * context.Q := by
      calc
        (base.slope context.Q).den =
            (base.slope context.Q).den /
                Nat.gcd (base.slope context.Q).den context.Q *
              Nat.gcd (base.slope context.Q).den context.Q :=
          (Nat.div_mul_cancel hgcdDvd).symm
        _ ≤ (base.slope context.Q).den /
                Nat.gcd (base.slope context.Q).den context.Q * context.Q :=
          Nat.mul_le_mul_left _ hgcdLe
        _ = base.H.natAbs * context.Q := by rw [hHden]
    have hprimitiveBase : Int.gcd base.H base.K = 1 := hprimitive₀
    have hcanonHInt : (base.canonicalGeometricLine.H : ℤ) = base.H := by
      rw [base.canonicalGeometricLine_H_cast]
      simp only [AffineLine.primitiveHorizontalInt,
        AffineLine.directionGCD, hprimitiveBase]
      norm_num
    have hcanonHReal : (base.canonicalGeometricLine.H : ℝ) = (base.H : ℝ) := by
      exact_mod_cast hcanonHInt
    have hXone : (1 : ℝ) ≤ W.X := by
      rw [WindowSystem.X, dyadicScale]
      exact_mod_cast Nat.one_le_two_pow
    have hfrequencyOne : (1 : ℝ) ≤ frequencyCutoff W := by
      unfold frequencyCutoff
      exact Real.one_le_rpow hXone (by
        have := W.structural.rho_pos
        linarith)
    have hfrequencyPos : (0 : ℝ) < frequencyCutoff W :=
      lt_of_lt_of_le zero_lt_one hfrequencyOne
    have hstepBase : (base.H : ℝ) ≤ Cstep * W.X := by
      rw [← hcanonHReal]
      refine hstep₀.trans ?_
      rw [div_le_iff₀ hfrequencyPos]
      have hnonneg : 0 ≤ Cstep * (W.X : ℝ) := by positivity
      nlinarith
    have hHnatReal : (base.H.natAbs : ℝ) = (base.H : ℝ) := by
      have hHnatInt : (base.H.natAbs : ℤ) = base.H :=
        Int.natAbs_of_nonneg base.H_pos.le
      calc
        (base.H.natAbs : ℝ) = ((base.H.natAbs : ℤ) : ℝ) := by norm_num
        _ = (base.H : ℝ) := by rw [hHnatInt]
    have hdenStepReal : ((base.slope context.Q).den : ℝ) ≤
        (context.Q : ℝ) * Cstep * W.X := by
      have hcast : ((base.slope context.Q).den : ℝ) ≤
          (base.H.natAbs : ℝ) * context.Q := by exact_mod_cast hdenStepNat
      rw [hHnatReal] at hcast
      nlinarith [show (0 : ℝ) ≤ context.Q by positivity]
    have hDStep : (σ.D : ℝ) ≤ (context.Q : ℝ) * Cstep * W.X := by
      have hDden : (σ.D : ℝ) ≤ ((base.slope context.Q).den : ℝ) := by
        exact_mod_cast hdenBand
      exact hDden.trans hdenStepReal
    have hDreal : (0 : ℝ) < σ.D := by exact_mod_cast hD
    have hDdenReal : (σ.D : ℝ) ≤ (base.slope context.Q).den := by
      exact_mod_cast hdenBand
    have hfourFraction :
        4 * (context.Q : ℝ) * W.X / (base.slope context.Q).den ≤
          4 * (context.Q : ℝ) * W.X / σ.D := by
      exact div_le_div_of_nonneg_left (by positivity) hDreal hDdenReal
    have honeFraction : (1 : ℝ) ≤
        (context.Q : ℝ) * Cstep * W.X / σ.D := by
      rw [le_div_iff₀ hDreal]
      simpa [one_mul] using hDStep
    have hPfinal : (P.ncard : ℝ) ≤
        (context.Q : ℝ) * (Cstep + 4) * W.X / σ.D := by
      calc
        (P.ncard : ℝ) ≤ 1 +
            4 * (context.Q : ℝ) * W.X /
              (base.slope context.Q).den := hPbound
        _ ≤ (context.Q : ℝ) * Cstep * W.X / σ.D +
            4 * (context.Q : ℝ) * W.X / σ.D :=
          add_le_add honeFraction hfourFraction
        _ = (context.Q : ℝ) * (Cstep + 4) * W.X / σ.D := by ring
    have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
    calc
      (S.ncard : ℝ) ≤ (P.ncard : ℝ) * W.m := hcardReal
      _ ≤ ((context.Q : ℝ) * (Cstep + 4) * W.X / σ.D) * W.m :=
        mul_le_mul_of_nonneg_right hPfinal hmnonneg
      _ = (context.Q : ℝ) * (Cstep + 4) * W.m * W.X / σ.D := by ring
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    have hemptyResult : S.Finite ∧
        (S.ncard : ℝ) ≤ (context.Q : ℝ) * (Cstep + 4) *
          W.m * W.X / σ.D := by
      rw [hSempty]
      constructor
      · exact Set.finite_empty
      · simp
        positivity
    simpa [S, W] using hemptyResult

/-- Largest power of two not exceeding a positive natural number.  At zero
the definition takes the harmless default value `1`; all uses in the strict
cone decomposition carry a positivity proof. -/
def dyadicFloorBand (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

@[simp] theorem dyadicFloorBand_pos (n : ℕ) : 0 < dyadicFloorBand n := by
  simp [dyadicFloorBand]

theorem dyadicFloorBand_isPow (n : ℕ) :
    ∃ k : ℕ, dyadicFloorBand n = 2 ^ k := by
  exact ⟨Nat.log 2 n, rfl⟩

theorem dyadicFloorBand_le {n : ℕ} (hn : 0 < n) :
    dyadicFloorBand n ≤ n := by
  exact Nat.pow_log_le_self 2 hn.ne'

theorem dyadicFloorBand_lt_two_mul (n : ℕ) :
    n < 2 * dyadicFloorBand n := by
  simpa [dyadicFloorBand, pow_succ, Nat.mul_comm] using
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n)

/-- Dyadic lower band of the integer average gap. -/
def meanGapBand (span count : ℕ) : ℕ :=
  dyadicFloorBand (span / count)

theorem meanGapBand_bounds {span count : ℕ}
    (hcount : 0 < count) (hcountSpan : count ≤ span) :
    0 < meanGapBand span count ∧
      meanGapBand span count * count ≤ span ∧
      span < 2 * meanGapBand span count * count := by
  have hquotPos : 0 < span / count := Nat.div_pos hcountSpan hcount
  have hlower := dyadicFloorBand_le hquotPos
  have hupper := dyadicFloorBand_lt_two_mul (span / count)
  refine ⟨dyadicFloorBand_pos _, ?_, ?_⟩
  · exact (Nat.le_div_iff_mul_le hcount).mp hlower
  · exact (Nat.div_lt_iff_lt_mul hcount).mp hupper

/-- A segment whose span carries a fixed fraction of the parent excess has
mean-gap band strictly beyond the cutoff scale. -/
theorem meanGapBand_above_cutoff
    {span count m Z Z0 : ℕ} {y : ℝ}
    (hm : 0 < m) (hcount : count ≤ m)
    (hy : (m : ℝ) * Z0 < y) (hspan : y / 16 ≤ span)
    (hmeanUpper : span < 2 * Z * count) :
    (Z0 : ℝ) / 32 < Z := by
  have hcountReal : (count : ℝ) ≤ m := by exact_mod_cast hcount
  have hspanReal : (span : ℝ) < 2 * Z * count := by exact_mod_cast hmeanUpper
  have hcoef : (0 : ℝ) ≤ 2 * Z := by positivity
  have hcountScaled : (2 : ℝ) * Z * count ≤ 2 * Z * m :=
    mul_le_mul_of_nonneg_left hcountReal hcoef
  have hmReal : (0 : ℝ) < m := by positivity
  nlinarith

/-- Combining denominator--span with the dyadic denominator band gives the
lower band used by the signature-entropy estimate. -/
theorem denominatorBand_lower
    {span count q D Z : ℕ} {cspan : ℝ}
    (hcspan : 0 < cspan)
    (hZavg : (Z : ℝ) ≤ (span : ℝ) / count)
    (hden : cspan * Real.rpow 2 ((span : ℝ) / count) ≤ q)
    (hqband : q < 2 * D) :
    cspan / 2 * (2 : ℝ) ^ Z ≤ D := by
  have hrpow : Real.rpow 2 (Z : ℝ) ≤
      Real.rpow 2 ((span : ℝ) / count) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hZavg
  have hpow : (2 : ℝ) ^ Z ≤
      Real.rpow 2 ((span : ℝ) / count) := by
    simpa [Real.rpow_natCast] using hrpow
  have hscaled := mul_le_mul_of_nonneg_left hpow hcspan.le
  have hqbandReal : (q : ℝ) < 2 * D := by exact_mod_cast hqband
  nlinarith

/-- Every gap on a fixed odd-denominator segment is short enough for the
logarithmic greedy scale associated with any dyadic band containing that
denominator. -/
theorem OddDenominatorSegment.gap_le_logBand
    (Q D : ℕ) (hQ : 0 < Q)
    (segment : OddDenominatorSegment) (hsegment : segment.Valid Q)
    (hqband : segment.q < 2 * D) :
    ∀ g ∈ segment.gaps,
      g ≤ Nat.ceil (Real.logb 2 (4 * D)) := by
  intro g hg
  rcases hsegment with
    ⟨_hQ, _hpositive, _hprimitive, htrace, _hq_one, _hq_odd, hslopes⟩
  obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hg
  have hμmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hνmemTrace :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    apply List.mem_map_of_mem
    exact List.mem_range.mpr (by omega)
  have hμmem :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hμmemTrace
  have hνmem :
      (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q ∈
        segment.slopes := by
    rw [htrace]
    exact hνmemTrace
  let μ := (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q
  let ν :=
    (segment.startLine.transformWord Q (segment.gaps.take (r + 1))).slope Q
  have hμdata := hslopes μ (by simpa [μ] using hμmem)
  have hνdata := hslopes ν (by simpa [ν] using hνmem)
  have htake : segment.gaps.take (r + 1) =
      segment.gaps.take r ++ [g] := by
    rw [← hget]
    simpa only [List.concat_eq_append] using (List.take_concat_get hr).symm
  have hνμ : ν = (2 : ℚ) ^ g * μ - 1 := by
    calc
      ν = (segment.startLine.transformWord Q
          (segment.gaps.take r ++ [g])).slope Q := by rw [← htake]
      _ = ((segment.startLine.transformWord Q (segment.gaps.take r)).transformWord
          Q [g]).slope Q := by rw [AffineLine.transformWord_append]
      _ = ((segment.startLine.transformWord Q
          (segment.gaps.take r)).transform Q g).slope Q := rfl
      _ = (2 : ℚ) ^ g * μ - 1 := by
        rw [AffineLine.slope_transform Q hQ]
  have hμlower : (1 : ℚ) / segment.q ≤ μ := by
    have hdenpos : (0 : ℚ) < μ.den := by positivity
    have hnumone : (1 : ℚ) ≤ μ.num := by
      exact_mod_cast (show (1 : ℤ) ≤ μ.num by
        exact (Int.add_one_le_iff).2 (Rat.num_pos.mpr hμdata.1.1))
    calc
      (1 : ℚ) / segment.q = 1 / μ.den := by rw [hμdata.2.1]
      _ ≤ (μ.num : ℚ) / μ.den :=
        (div_le_div_iff_of_pos_right hdenpos).2 hnumone
      _ = μ := Rat.num_div_den μ
  have hpowμ : (2 : ℚ) ^ g * μ < 2 := by
    rw [hνμ] at hνdata
    linarith [hνdata.1.2]
  have hqpos : (0 : ℚ) < segment.q := by positivity
  have hpowdiv : (2 : ℚ) ^ g / segment.q < 2 := by
    calc
      (2 : ℚ) ^ g / segment.q = (2 : ℚ) ^ g * (1 / segment.q) := by ring
      _ ≤ (2 : ℚ) ^ g * μ :=
        mul_le_mul_of_nonneg_left hμlower (by positivity)
      _ < 2 := hpowμ
  have hpowltRat : (2 : ℚ) ^ g < 2 * segment.q :=
    (div_lt_iff₀ hqpos).1 hpowdiv
  have hpowlt : 2 ^ g < 4 * D := by
    have hpowltNat : 2 ^ g < 2 * segment.q := by exact_mod_cast hpowltRat
    omega
  have hellEq : Nat.ceil (Real.logb 2 (4 * D)) = Nat.clog 2 (4 * D) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  rw [hellEq]
  exact ((Nat.lt_clog_iff_pow_lt (by omega)).2 hpowlt).le

/-- Every genuine selected block start retains the original integer parameter
of the affine support run.  The strict offset bound keeps that point inside
the enlarged dyadic corridor. -/
theorem exists_originalSourceParameter
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (hden : W.rational.eta.den = Q)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : LowGapBlock.OccursIn data.segment block)
    (hoffset : sourceWindowOffset W k data block < W.m) :
    ∃ t : ℤ, IsOriginalSourceParameter Q W k data block t := by
  classical
  let i := k - W.s + (initialLongPrefix W k).length + data.before.length
  have hstart := data.segmentStart_contains_actual Q W Z0 k hden hvalid
  rcases hstart with ⟨t, hx, hr⟩
  have hsegment := data.segmentGaps_eq_enumerationGapWord Q W Z0 k hvalid
  have hoffsetSegment : block.offset ≤ data.segment.gaps.length :=
    le_trans (Nat.le_add_right block.offset block.gaps.length) hoccurs.1
  have htakePrefix : (data.segment.gaps.take block.offset).IsPrefix
      (enumerationGapWord W.enumeration i data.segment.gaps.length) := by
    rw [← hsegment]
    exact List.take_prefix _ _
  have htakeLen : (data.segment.gaps.take block.offset).length = block.offset := by
    simp [hoffsetSegment]
  have htake : data.segment.gaps.take block.offset =
      enumerationGapWord W.enumeration i block.offset := by
    have := prefix_enumerationGapWord_eq W.enumeration i
      data.segment.gaps.length (data.segment.gaps.take block.offset) htakePrefix
    simpa [htakeLen] using this
  have hpoint := data.segment.startLine.transformWord_parameter_enumerationGapWord
    Q W.rational hden W.enumeration i block.offset t hx hr
  rw [← htake] at hpoint
  have hindex : i + block.offset =
      k - W.s + sourceWindowOffset W k data block := by
    unfold sourceWindowOffset
    dsimp [i]
    omega
  have hindexLe : k - W.s + sourceWindowOffset W k data block ≤ k := by
    rw [WindowSystem.m] at hoffset
    have hsk : W.s ≤ k := hvalid.1
    omega
  have hkAnchor : k ∈ W.anchors := by
    have hhigh := hvalid.2.1
    rw [highAnchors, Finset.mem_filter] at hhigh
    exact hhigh.1
  have hxUpper : sourceCoordinate W k data block ≤ 2 * W.X := by
    unfold sourceCoordinate
    calc
      W.enumeration.a (k - W.s + sourceWindowOffset W k data block) ≤
          W.enumeration.a k := W.enumeration.strictMono.monotone hindexLe
      _ ≤ 2 * W.X := (Finset.mem_filter.mp hkAnchor).2.2
  refine ⟨t, ?_, ?_, ?_⟩
  · unfold sourceCoordinate sourceRawLine
    rw [← hindex]
    exact hpoint.1
  · unfold sourceCoordinate sourceRawLine
    rw [← hindex]
    exact hpoint.2
  · change -(W.X : ℤ) ≤ (sourceRawLine Q data block).A +
        (sourceRawLine Q data block).H * t ∧
      (sourceRawLine Q data block).A +
        (sourceRawLine Q data block).H * t ≤ 3 * W.X
    have hxEq : (sourceRawLine Q data block).A +
        (sourceRawLine Q data block).H * t =
          (sourceCoordinate W k data block : ℤ) := by
      symm
      unfold sourceCoordinate sourceRawLine
      rw [← hindex]
      exact hpoint.1
    rw [hxEq]
    constructor
    · have hneg : -(W.X : ℤ) ≤ 0 := neg_nonpos.mpr (by positivity)
      exact hneg.trans (by positivity)
    · exact_mod_cast (hxUpper.trans (by omega : 2 * W.X ≤ 3 * W.X))

local instance affineLineCountableForStrict : Countable AffineLine := by
  let code : AffineLine → ℤ × ℤ × ℤ × ℤ := fun line =>
    (line.A, line.C, line.H, line.K)
  exact (show Function.Injective code from by
    intro line₁ line₂ h
    cases line₁
    cases line₂
    simp only [code, Prod.mk.injEq] at h
    simp_all).countable

private theorem measurableSet_exists_le_countable_strict {α β : Type*}
    [Countable α] [MeasurableSpace β] (f : β → ℝ) (hf : Measurable f)
    (P : α → Prop) (c : α → ℝ) :
    MeasurableSet {x | ∃ a, P a ∧ f x ≤ c a} := by
  classical
  rw [show {x | ∃ a, P a ∧ f x ≤ c a} =
      ⋃ a, if P a then {x | f x ≤ c a} else ∅ by
    ext x
    simp]
  exact MeasurableSet.iUnion fun a => by
    by_cases ha : P a
    · simpa [ha] using measurableSet_le hf measurable_const
    · simp [ha]

private theorem measurableSet_windowThreshold_of_sections_strict
    (E : Set WindowThreshold)
    (hsection : ∀ k : ℕ, MeasurableSet {T : ℝ | (k, T) ∈ E}) :
    MeasurableSet E := by
  rw [show E = ⋃ k : ℕ, Set.prod {k} {T : ℝ | (k, T) ∈ E} by
    ext e
    rcases e with ⟨k, T⟩
    rw [Set.mem_iUnion]
    change (k, T) ∈ E ↔
      ∃ i : ℕ, (k, T) ∈ Set.prod {i} {u : ℝ | (i, u) ∈ E}
    constructor
    · intro h
      exact ⟨k, ⟨by simp, h⟩⟩
    · rintro ⟨i, hi⟩
      have hik : k = i := hi.1
      subst i
      exact hi.2]
  exact MeasurableSet.iUnion fun k =>
    (MeasurableSet.singleton k).prod (hsection k)

theorem measurableSet_largePairs_strict (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (W.largePairs Z0) := by
  exact W.measurableSet_pairSet.inter
    (measurableSet_lt
      (measurable_const : Measurable
        (fun _ : WindowThreshold => (W.m : ℝ) * Z0))
      W.measurable_excess)

private theorem measurableSet_longInteriorPair_section_strict
    (W : WindowSystem) (Z0 k : ℕ) :
    MeasurableSet {T : ℝ | LongInteriorPair W Z0 (k, T)} := by
  classical
  have hlargeSection :
      MeasurableSet {T : ℝ | (k, T) ∈ W.largePairs Z0} :=
    (measurableSet_largePairs_strict W Z0).preimage measurable_prodMk_left
  let P : AffineLine × GapWord → Prop := fun lg =>
    IsActualInitialContinuation W Z0 (k, 0) lg.1 lg.2 ∧
      IsInteriorTrajectory W.rational.eta.den lg.1 lg.2
  have hexists : MeasurableSet
      {T : ℝ | ∃ lg : AffineLine × GapWord,
        P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
    apply measurableSet_exists_le_countable_strict
    exact W.measurable_excess.comp measurable_prodMk_left |>.div_const 8
  by_cases hfreq : IsFrequentPrefix W Z0 (initialLongPrefix W k)
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} =
        {T | (k, T) ∈ W.largePairs Z0 ∧
          ∃ lg : AffineLine × GapWord,
            P lg ∧ W.excess (k, T) / 8 ≤ (lg.2.span : ℝ)} := by
      ext T
      change
        ((k, T) ∈ W.largePairs Z0 ∧
          IsFrequentPrefix W Z0 (initialLongPrefix W k) ∧
          ∃ line gaps,
            IsActualInitialContinuation W Z0 (k, T) line gaps ∧
            IsInteriorTrajectory W.rational.eta.den line gaps ∧
            W.excess (k, T) / 8 ≤ (gaps.span : ℝ)) ↔ _
      have hactual : ∀ line gaps,
          IsActualInitialContinuation W Z0 (k, T) line gaps ↔
            IsActualInitialContinuation W Z0 (k, 0) line gaps := by
        intro line gaps
        rfl
      simp only [hfreq, true_and, hactual, P]
      constructor <;> aesop
    rw [heq]
    exact hlargeSection.inter hexists
  · have heq : {T : ℝ | LongInteriorPair W Z0 (k, T)} = ∅ := by
      ext T
      constructor
      · intro h
        exact (hfreq h.2.1).elim
      · intro h
        exact h.elim
    rw [heq]
    exact MeasurableSet.empty

theorem measurableSet_interiorPairs_strict (W : WindowSystem) (Z0 : ℕ) :
    MeasurableSet (interiorPairs W Z0) := by
  apply measurableSet_windowThreshold_of_sections_strict
  intro k
  exact measurableSet_longInteriorPair_section_strict W Z0 k

theorem interiorPairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    interiorPairs W Z0 ⊆ W.pairSet := by
  intro e he
  exact he.1.1

/-- Dyadic denominator band fixed by the anchor's selected segment. -/
def selectedDenominatorBand (selection : InteriorAnchorSelection) (k : ℕ) : ℕ :=
  match selection k with
  | none => 1
  | some data => dyadicFloorBand data.segment.q

/-- Dyadic lower band of the selected segment's integer average gap. -/
def selectedMeanGapBand (selection : InteriorAnchorSelection) (k : ℕ) : ℕ :=
  match selection k with
  | none => 1
  | some data => meanGapBand data.segment.span data.segment.gapCount

def selectedLogLength (selection : InteriorAnchorSelection) (k : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (4 * selectedDenominatorBand selection k))

def selectedForwardLength (W : WindowSystem) (gap : GapParams W.rational.eta.den)
    (_k : ℕ) : ℕ :=
  reconstructionForwardLength W gap.Cgap

/-- The deterministic threshold-independent block list attached to an anchor.
Unselected anchors carry the empty list. -/
def selectedInteriorBlocks (W : WindowSystem)
    (selection : InteriorAnchorSelection) (gap : GapParams W.rational.eta.den)
    (k : ℕ) : List LowGapBlock :=
  match selection k with
  | none => []
  | some data => selectedBlocks data.segment W.structural.B
      (selectedLogLength selection k) (selectedMeanGapBand selection k)
      (selectedForwardLength W gap k)

@[simp] theorem selectedDenominatorBand_pos
    (selection : InteriorAnchorSelection) (k : ℕ) :
    0 < selectedDenominatorBand selection k := by
  simp only [selectedDenominatorBand]
  split <;> simp

@[simp] theorem selectedMeanGapBand_pos
    (selection : InteriorAnchorSelection) (k : ℕ) :
    0 < selectedMeanGapBand selection k := by
  simp only [selectedMeanGapBand]
  split <;> simp [meanGapBand]

@[simp] theorem selectedLogLength_eq
    (selection : InteriorAnchorSelection) (k : ℕ) :
    selectedLogLength selection k =
      Nat.ceil (Real.logb 2 (4 * selectedDenominatorBand selection k)) := rfl

@[simp] theorem selectedForwardLength_eq
    (W : WindowSystem) (gap : GapParams W.rational.eta.den) (k : ℕ) :
    selectedForwardLength W gap k = reconstructionForwardLength W gap.Cgap := rfl

theorem selectedInteriorBlocks_eq_of_selected
    (W : WindowSystem) (selection : InteriorAnchorSelection)
    (gap : GapParams W.rational.eta.den) (k : ℕ)
    (data : AnchorInteriorData) (hselected : selection k = some data) :
    selectedInteriorBlocks W selection gap k =
      selectedBlocks data.segment W.structural.B
        (selectedLogLength selection k) (selectedMeanGapBand selection k)
        (selectedForwardLength W gap k) := by
  simp [selectedInteriorBlocks, hselected]

/-- Once the selected segment has enough span to pay for the forward reserve
and final greedy remainder, its deterministic anchor-level blocks form the
nonnegative sparse cover used in the strict mass refinement. -/
theorem selectedInteriorBlocks_sparseCover
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 : ℕ)
    (selection : InteriorAnchorSelection)
    (gap : GapParams W.rational.eta.den) (e : WindowThreshold)
    (data : AnchorInteriorData) (hselected : selection e.1 = some data)
    (hvalid : data.Valid Q W Z0 e.1)
    (hspan : W.excess e / 16 ≤ data.segment.span)
    (hcount : 1 ≤ data.segment.gapCount)
    (hlarge :
      4 * (selectedForwardLength W gap e.1 +
        Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1)) ≤
          data.segment.span) :
    let blocks := selectedInteriorBlocks W selection gap e.1
    IsLowGapCover data.segment W.structural.B
        (selectedLogLength selection e.1)
        (selectedMeanGapBand selection e.1)
        (selectedForwardLength W gap e.1) blocks ∧
      blocks.Nodup ∧
      (∀ block ∈ blocks,
        0 ≤ interiorComponentWeight (W.excess e) blocks block) ∧
      (∀ block ∈ blocks,
        interiorComponentWeight (W.excess e) blocks block ≤
          32 * Nat.ceil ((W.structural.B + 1) *
            selectedLogLength selection e.1)) ∧
      (blocks.map (fun block =>
        interiorComponentWeight (W.excess e) blocks block)).sum = W.excess e := by
  let D := selectedDenominatorBand selection e.1
  let Z := selectedMeanGapBand selection e.1
  let ell := selectedLogLength selection e.1
  let forward := selectedForwardLength W gap e.1
  let blocks := selectedInteriorBlocks W selection gap e.1
  have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
  have hqpos : 0 < data.segment.q :=
    lt_trans (by omega) hsegment.2.2.2.2.1
  have hD : D = dyadicFloorBand data.segment.q := by
    simp [D, selectedDenominatorBand, hselected]
  have hDpos : 0 < D := by simp [D]
  have hqband : data.segment.q < 2 * D := by
    rw [hD]
    exact dyadicFloorBand_lt_two_mul _
  have hcountPos : 0 < data.segment.gapCount := by omega
  have hcountSpan : data.segment.gapCount ≤ data.segment.span := by
    rw [OddDenominatorSegment.gapCount, OddDenominatorSegment.span,
      GapWord.span]
    exact List.length_le_sum_of_one_le data.segment.gaps fun g hg =>
      hsegment.2.1 g hg
  have hmean : Z * data.segment.gapCount ≤ data.segment.span ∧
      data.segment.span < 2 * Z * data.segment.gapCount := by
    have hm := meanGapBand_bounds hcountPos hcountSpan
    simpa [Z, selectedMeanGapBand, hselected] using hm.2
  have hell : ell = Nat.ceil (Real.logb 2 (4 * D)) := by
    simp [ell, D]
  have hellPos : 0 < ell := by
    have hellEq : Nat.ceil (Real.logb 2 (4 * D)) = Nat.clog 2 (4 * D) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using
        Real.natCeil_logb_natCast 2 (4 * D)
    rw [hell, hellEq, Nat.lt_clog_iff_pow_lt (by omega)]
    simp
    omega
  have hgap : ∀ g ∈ data.segment.gaps, g ≤ ell := by
    rw [hell]
    exact data.segment.gap_le_logBand Q D hQ hsegment hqband
  have hy0 : 0 ≤ W.excess e := by
    unfold WindowSystem.excess
    positivity
  have hyUpper : W.excess e ≤ 16 * data.segment.span := by
    nlinarith
  obtain ⟨result, hcover, hnodup, hnonneg, hbound, hsum⟩ :=
    lem_sparse_cover Q W.structural.B W.structural.B_gt data.segment hsegment
      ell Z forward hellPos (by simp [Z]) hgap hmean
      (by simpa [ell, forward] using hlarge) (W.excess e) hy0 hyUpper
  have hdet : blocks = selectedBlocks data.segment W.structural.B ell Z forward := by
    simpa [blocks, ell, Z, forward] using
      selectedInteriorBlocks_eq_of_selected W selection gap e.1 data hselected
  have hresult : result = blocks := hcover.1.trans hdet.symm
  subst result
  exact ⟨hcover, hnodup, hnonneg, hbound, hsum⟩

theorem OddDenominatorSegment.startSlope_den_eq
    (Q : ℕ) (segment : OddDenominatorSegment) (hsegment : segment.Valid Q) :
    (segment.startLine.slope Q).den = segment.q := by
  have hmem : segment.startLine.slope Q ∈ segment.slopes := by
    rw [hsegment.2.2.2.1]
    unfold OddDenominatorSegment.slopeTrace
    have hz := List.mem_map_of_mem
      (f := fun r =>
        (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q)
      (a := 0) (List.mem_range.mpr (by simp : 0 < segment.gaps.length + 1))
    simpa [AffineLine.transformWord] using hz
  exact (hsegment.2.2.2.2.2.2 _ hmem).2.1

theorem primitive_slope_den_le_Q_mul_H
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine)
    (hprimitive : Int.gcd line.H line.K = 1) :
    (line.slope Q).den ≤ Q * line.H.natAbs := by
  let q := (line.slope Q).den
  let g := Nat.gcd q Q
  have hformula := primitiveDirectionDenominator Q hQ line hprimitive
  have hgdvd : g ∣ q := Nat.gcd_dvd_left q Q
  have hgQ : g ≤ Q := Nat.gcd_le_right q hQ
  calc
    (line.slope Q).den = q := rfl
    _ = (q / g) * g := (Nat.div_mul_cancel hgdvd).symm
    _ = line.H.natAbs * g := by rw [hformula]
    _ ≤ line.H.natAbs * Q := Nat.mul_le_mul_left _ hgQ
    _ = Q * line.H.natAbs := Nat.mul_comm _ _

/-- The stabilized primitive-step bound forces the dyadic logarithmic block
length below the forward-gap allowance once the frequency cutoff dominates
the fixed denominator-level constant. -/
theorem selectedLogLength_le_of_step
    (Q Cgap : ℕ) (hQ : 0 < Q) (Cstep : ℝ)
    (W : WindowSystem) (Z0 k : ℕ) (selection : InteriorAnchorSelection)
    (data : AnchorInteriorData) (hselected : selection k = some data)
    (hvalid : data.Valid Q W Z0 k)
    (hstep : (data.segment.startLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W)
    (hfrequency : 4 * (Q : ℝ) * Cstep ≤ frequencyCutoff W) :
    selectedLogLength selection k ≤ W.L + Cgap := by
  let D := selectedDenominatorBand selection k
  have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
  have hqpos : 0 < data.segment.q :=
    lt_trans (by omega) hsegment.2.2.2.2.1
  have hD : D = dyadicFloorBand data.segment.q := by
    simp [D, selectedDenominatorBand, hselected]
  have hDleq : D ≤ data.segment.q := by
    rw [hD]
    exact dyadicFloorBand_le hqpos
  have hprimitive : Int.gcd data.segment.startLine.H
      data.segment.startLine.K = 1 := hsegment.2.2.1
  have hdenEq := data.segment.startSlope_den_eq Q hsegment
  have hqHnat : data.segment.q ≤ Q * data.segment.startLine.H.natAbs := by
    rw [← hdenEq]
    exact primitive_slope_den_le_Q_mul_H Q hQ data.segment.startLine hprimitive
  have hHcast : (data.segment.startLine.H.natAbs : ℝ) =
      (data.segment.startLine.H : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos]
    exact_mod_cast data.segment.startLine.H_pos
  have hqH' : (data.segment.q : ℝ) ≤
      ((Q * data.segment.startLine.H.natAbs : ℕ) : ℝ) := by
    exact_mod_cast hqHnat
  have hqH : (data.segment.q : ℝ) ≤
      (Q : ℝ) * data.segment.startLine.H := by
    simpa [hHcast] using hqH'
  have hfreqPos : 0 < frequencyCutoff W := by
    unfold frequencyCutoff
    apply Real.rpow_pos_of_pos
    rw [WindowSystem.X, dyadicScale]
    positivity
  have hXnonneg : (0 : ℝ) ≤ W.X := by positivity
  have hscaledFrequency :
      4 * (Q : ℝ) * Cstep * W.X ≤ W.X * frequencyCutoff W := by
    nlinarith [mul_le_mul_of_nonneg_right hfrequency hXnonneg]
  have hratio :
      4 * (Q : ℝ) * (Cstep * W.X / frequencyCutoff W) ≤ W.X := by
    rw [show 4 * (Q : ℝ) * (Cstep * W.X / frequencyCutoff W) =
      (4 * Q * Cstep * W.X) / frequencyCutoff W by ring]
    exact (div_le_iff₀ hfreqPos).2 (by nlinarith)
  have hfourDReal : (4 * D : ℕ) ≤ W.X := by
    have hDqReal : (D : ℝ) ≤ data.segment.q := by exact_mod_cast hDleq
    have hchain : (4 : ℝ) * D ≤ W.X := by
      calc
        (4 : ℝ) * D ≤ 4 * data.segment.q :=
          mul_le_mul_of_nonneg_left hDqReal (by norm_num)
        _ ≤ 4 * ((Q : ℝ) * data.segment.startLine.H) :=
          mul_le_mul_of_nonneg_left hqH (by norm_num)
        _ ≤ 4 * (Q : ℝ) * (Cstep * W.X / frequencyCutoff W) := by
          nlinarith [mul_le_mul_of_nonneg_left hstep
            (show (0 : ℝ) ≤ 4 * Q by positivity)]
        _ ≤ W.X := hratio
    exact_mod_cast hchain
  have hfourDpow : 4 * D ≤ 2 ^ (W.L + Cgap) := by
    calc
      4 * D ≤ W.X := hfourDReal
      _ = 2 ^ W.L := rfl
      _ ≤ 2 ^ (W.L + Cgap) := Nat.pow_le_pow_right (by omega) (by omega)
  have hellEq : selectedLogLength selection k = Nat.clog 2 (4 * D) := by
    rw [selectedLogLength]
    have hDdef : selectedDenominatorBand selection k = D := rfl
    rw [hDdef]
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  rw [hellEq, Nat.clog_le_iff_le_pow (by omega)]
  exact hfourDpow

/-- An odd primitive horizontal direction remains primitive after one raw
shared-gap transformation. -/
theorem AffineLine.transform_primitive_of_odd_horizontal
    (Q g : ℕ) (line : AffineLine)
    (hprimitive : Int.gcd line.H line.K = 1)
    (hodd : Odd line.H.natAbs) :
    Int.gcd (line.transform Q g).H (line.transform Q g).K = 1 := by
  have hHK : Nat.Coprime line.H.natAbs line.K.natAbs := hprimitive
  have hHpow : Nat.Coprime line.H.natAbs (2 ^ g) :=
    hodd.coprime_two_right.pow_right g
  have hHmul : Nat.Coprime line.H.natAbs (2 ^ g * line.K.natAbs) :=
    hHpow.mul_right hHK
  have hmulGcd : Int.gcd line.H ((2 : ℤ) ^ g * line.K) = 1 := by
    rw [Int.gcd_def]
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hHmul
  change Int.gcd line.H ((2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H) = 1
  calc
    Int.gcd line.H ((2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H) =
        Int.gcd ((2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H) line.H :=
      Int.gcd_comm _ _
    _ = Int.gcd ((2 : ℤ) ^ g * line.K) line.H :=
      Int.gcd_sub_mul_right_left line.H ((2 : ℤ) ^ g * line.K) Q
    _ = Int.gcd line.H ((2 : ℤ) ^ g * line.K) := Int.gcd_comm _ _
    _ = 1 := hmulGcd

/-- Primitivity persists along every prefix of a fixed odd-horizontal raw
direction. -/
theorem AffineLine.transformWord_primitive_of_odd_horizontal
    (Q : ℕ) (line : AffineLine) (word : GapWord)
    (hprimitive : Int.gcd line.H line.K = 1)
    (hodd : Odd line.H.natAbs) :
    Int.gcd (line.transformWord Q word).H
      (line.transformWord Q word).K = 1 := by
  induction word generalizing line with
  | nil => exact hprimitive
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      apply ih (line.transform Q g)
      · exact line.transform_primitive_of_odd_horizontal Q g hprimitive hodd
      · simpa [AffineLine.transform] using hodd

/-- The primitive horizontal step of a valid fixed odd-denominator segment is
itself odd. -/
theorem OddDenominatorSegment.startLine_horizontal_odd
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) : Odd segment.startLine.H.natAbs := by
  have hden := segment.startSlope_den_eq Q hsegment
  have hformula := primitiveDirectionDenominator Q hsegment.1 segment.startLine
    hsegment.2.2.1
  let d := Nat.gcd segment.q Q
  have hdvd : d ∣ segment.q := Nat.gcd_dvd_left segment.q Q
  have hquotDvd : segment.q / d ∣ segment.q := by
    refine ⟨d, ?_⟩
    exact (Nat.div_mul_cancel hdvd).symm
  have hquotOdd : Odd (segment.q / d) :=
    Odd.of_dvd_nat hsegment.2.2.2.2.2.1 hquotDvd
  rw [hformula, hden]
  exact hquotOdd

/-- Every raw prefix direction in a valid fixed odd-denominator segment is
primitive. -/
theorem OddDenominatorSegment.prefixLine_primitive
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) (r : ℕ) :
    Int.gcd (segment.startLine.transformWord Q (segment.gaps.take r)).H
      (segment.startLine.transformWord Q (segment.gaps.take r)).K = 1 := by
  exact segment.startLine.transformWord_primitive_of_odd_horizontal Q
    (segment.gaps.take r) hsegment.2.2.1
      (segment.startLine_horizontal_odd Q hsegment)

/-- The slope datum attached to every genuine prefix of a valid segment. -/
theorem OddDenominatorSegment.prefixSlope_data
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) (r : ℕ) (hr : r ≤ segment.gaps.length) :
    let μ := (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q
    μ ∈ Set.Ioo (0 : ℚ) 1 ∧ μ.den = segment.q ∧ Odd μ.num := by
  have htrace :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        OddDenominatorSegment.slopeTrace Q segment.startLine segment.gaps := by
    unfold OddDenominatorSegment.slopeTrace
    exact List.mem_map_of_mem (List.mem_range.mpr (by omega))
  have hmem :
      (segment.startLine.transformWord Q (segment.gaps.take r)).slope Q ∈
        segment.slopes := by
    rw [hsegment.2.2.2.1]
    exact htrace
  exact hsegment.2.2.2.2.2.2 _ hmem

/-- A valid fixed odd-denominator segment is an interior trajectory at every
prefix. -/
theorem OddDenominatorSegment.interiorTrajectory
    (Q : ℕ) (segment : OddDenominatorSegment)
    (hsegment : segment.Valid Q) :
    IsInteriorTrajectory Q segment.startLine segment.gaps := by
  rw [isInteriorTrajectory_iff_transformWord]
  intro r hr
  exact (classifySlope_eq_interior_iff _).2
    (segment.prefixSlope_data Q hsegment r hr).1

/-- The deterministic forward reconstruction word remains on the actual
interior trajectory after its selected block. -/
theorem sourceForwardWord_interior
    (Q Cgap : ℕ) (W : WindowSystem) (data : AnchorInteriorData)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hoccurs : LowGapBlock.OccursIn data.segment block) :
    IsInteriorTrajectory Q (sourceBlockEndLine Q data block)
      (sourceForwardWord W Cgap data block) := by
  have hfull := data.segment.interiorTrajectory Q hsegment
  have hdecomp : data.segment.gaps.take block.offset ++ block.gaps ++
      sourceForwardSuffix data block = data.segment.gaps := by
    unfold sourceForwardSuffix
    calc
      data.segment.gaps.take block.offset ++ block.gaps ++
          data.segment.gaps.drop (block.offset + block.gaps.length) =
        data.segment.gaps.take block.offset ++
          ((data.segment.gaps.drop block.offset).take block.gaps.length ++
            (data.segment.gaps.drop block.offset).drop block.gaps.length) := by
              rw [hoccurs.2]
              simp [List.drop_drop, List.append_assoc]
      _ = data.segment.gaps.take block.offset ++
          data.segment.gaps.drop block.offset := by rw [List.take_append_drop]
      _ = data.segment.gaps := List.take_append_drop _ _
  have hdecomp' : data.segment.gaps.take block.offset ++
      (block.gaps ++ sourceForwardSuffix data block) = data.segment.gaps := by
    simpa [List.append_assoc] using hdecomp
  rw [← hdecomp', isInteriorTrajectory_append_iff] at hfull
  have hafterPrefix := hfull.2
  rw [isInteriorTrajectory_append_iff] at hafterPrefix
  have hafterBlock : IsInteriorTrajectory Q (sourceBlockEndLine Q data block)
      (sourceForwardSuffix data block) := by
    simpa [sourceRawLine, sourceBlockEndLine] using hafterPrefix.2
  have hprefix := GapWord.firstPrefixAbove_isPrefix
    (sourceForwardSuffix data block) (2 * W.L + Cgap)
  rcases hprefix with ⟨rest, hrest⟩
  rw [← hrest, isInteriorTrajectory_append_iff] at hafterBlock
  exact hafterBlock.1

/-- The retained forward reserve gives the exact lower and upper reconstruction
span bounds and preserves positivity. -/
theorem sourceForwardWord_spec
    (Q Cgap : ℕ) (W : WindowSystem) (data : AnchorInteriorData)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hforward : reconstructionForwardLength W Cgap ≤
      (sourceForwardSuffix data block).span)
    (hell : ∀ g ∈ data.segment.gaps, g ≤ W.L + Cgap)
    (hL : 1 ≤ W.L) :
    2 * W.L + Cgap < (sourceForwardWord W Cgap data block).span ∧
      (sourceForwardWord W Cgap data block).span ≤
        reconstructionForwardLength W Cgap ∧
      (sourceForwardWord W Cgap data block).Positive := by
  let suffix := sourceForwardSuffix data block
  let bound := 2 * W.L + Cgap
  have hcross : bound < suffix.span := by
    have : bound < reconstructionForwardLength W Cgap := by
      unfold bound reconstructionForwardLength
      omega
    exact this.trans_le hforward
  have hgapSuffix : ∀ g ∈ suffix, g ≤ W.L + Cgap := by
    intro g hg
    apply hell g
    exact List.mem_of_mem_drop hg
  refine ⟨?_, ?_, ?_⟩
  · exact GapWord.lt_span_firstPrefixAbove_of_lt_span suffix bound hcross
  · have hupper :=
      GapWord.span_firstPrefixAbove_le_add suffix bound (W.L + Cgap) hgapSuffix
    have hsum : bound + (W.L + Cgap) = reconstructionForwardLength W Cgap := by
      unfold bound reconstructionForwardLength
      omega
    change (suffix.firstPrefixAbove bound).span ≤ reconstructionForwardLength W Cgap
    rw [← hsum]
    exact hupper
  · apply GapWord.firstPrefixAbove_positive suffix bound
    intro g hg
    exact hsegment.2.1 g (List.mem_of_mem_drop hg)

/-- Membership in the deterministic selected-block list exposes all four
semantic properties used by reconstruction. -/
theorem selectedBlocks_mem_spec
    (segment : OddDenominatorSegment) (B : ℝ) (ell Z forward : ℕ)
    (block : LowGapBlock)
    (hblock : block ∈ selectedBlocks segment B ell Z forward) :
    LowGapBlock.OccursIn segment block ∧
      GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block.gaps ∧
      Z * block.gaps.length ≤ 4 * block.span ∧
      forward ≤ GapWord.span
        (segment.gaps.drop (block.offset + block.gaps.length)) := by
  rw [selectedBlocks_eq_pointwiseSelectedBlocks] at hblock
  change block ∈
    ((blocksWithOffsetsFrom 0
      (GapWord.greedyDecompose segment.gaps
        (Nat.ceil (B * ell))).completed).filter fun block =>
          Z * block.gaps.length ≤ 4 * block.span ∧
          block.offset + block.gaps.length ≤ segment.gaps.length ∧
          forward ≤ GapWord.span
            (segment.gaps.drop (block.offset + block.gaps.length))) at hblock
  have hbound : 0 < Nat.ceil (B * ell) := by
    by_contra hzero
    have hboundZero : Nat.ceil (B * ell) = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hboundZero] at hblock
    rw [greedyDecompose_zero] at hblock
    simp [blocksWithOffsetsFrom] at hblock
  have hfilter := List.mem_filter.mp hblock
  have hpred :
      Z * block.gaps.length ≤ 4 * block.span ∧
        block.offset + block.gaps.length ≤ segment.gaps.length ∧
        forward ≤ GapWord.span
          (segment.gaps.drop (block.offset + block.gaps.length)) :=
    of_decide_eq_true hfilter.2
  have hvalid := GapWord.greedyDecompose_valid segment.gaps
    (Nat.ceil (B * ell)) hbound
  have hwordMem : block.gaps ∈
      (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).completed := by
    rcases blocksWithOffsetsFrom_mem_split 0
        (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).completed
        block hfilter.1 with ⟨before, after, hwords, _⟩
    rw [hwords]
    simp
  refine ⟨?_, hvalid.2.1 block.gaps hwordMem, hpred.1, hpred.2.2⟩
  · exact blocksWithOffsetsFrom_occurs segment
      (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).completed
      (GapWord.greedyDecompose segment.gaps (Nat.ceil (B * ell))).remainder
      hvalid.1 block hfilter.1

/-- A completed greedy block has the paper's real upper span bound, without
losing a ceiling unit. -/
theorem greedyBlock_span_le_real
    (B : ℝ) (ell : ℕ) (block : GapWord)
    (hgreedy : GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block)
    (hgap : ∀ g ∈ block, g ≤ ell) :
    (block.span : ℝ) ≤ (B + 1) * ell := by
  have hne : block ≠ [] := hgreedy.1
  have hlength : 0 < block.length := List.length_pos_iff.mpr hne
  have hprefixNat : block.dropLast.sum < Nat.ceil (B * ell) := by
    simpa [GapWord.prefixSpan, List.dropLast_eq_take] using
      hgreedy.2.2 (block.length - 1) (by omega)
  have hprefixReal : (block.dropLast.sum : ℝ) < B * ell :=
    (Nat.lt_ceil.mp hprefixNat)
  have hlastNat : block.getLast hne ≤ ell :=
    hgap (block.getLast hne) (List.getLast_mem hne)
  have hlastReal : (block.getLast hne : ℝ) ≤ ell := by exact_mod_cast hlastNat
  have hsplitNat := congrArg List.sum (List.dropLast_append_getLast hne)
  simp only [List.sum_append, List.sum_singleton] at hsplitNat
  have hsplitReal : (block.span : ℝ) =
      block.dropLast.sum + block.getLast hne := by
    exact_mod_cast hsplitNat.symm
  rw [hsplitReal]
  nlinarith

/-- The concrete block encoding of a selected low-gap greedy block lies in the
candidate set for its two dyadic bands. -/
theorem encodeBlock_mem_encodingCandidates
    (B : ℝ) (D Z ell : ℕ) (block : LowGapBlock)
    (hDpow : ∃ d : ℕ, D = 2 ^ d) (hZpow : ∃ z : ℕ, Z = 2 ^ z)
    (hell : ell = Nat.ceil (Real.logb 2 (4 * D)))
    (hgreedy : GapWord.IsGreedyBlock (Nat.ceil (B * ell)) block.gaps)
    (hgap : ∀ g ∈ block.gaps, g ≤ ell)
    (hlow : Z * block.gaps.length ≤ 4 * block.span)
    (hpositive : block.gaps.Positive) :
    encodeBlock D Z block ∈ encodingCandidates D Z B := by
  have hZpos : 0 < Z := by
    rcases hZpow with ⟨z, rfl⟩
    positivity
  have hlower : B * ell ≤ (block.span : ℝ) := by
    calc
      B * ell ≤ Nat.ceil (B * ell) := Nat.le_ceil _
      _ ≤ block.span := by exact_mod_cast hgreedy.2.1
  have hupper : (block.span : ℝ) ≤ (B + 1) * ell :=
    greedyBlock_span_le_real B ell block.gaps hgreedy hgap
  have hlowReal : (block.gaps.length : ℝ) ≤ 4 * block.span / Z := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Z)]
    have hcast : (Z : ℝ) * block.gaps.length ≤ 4 * block.span := by
      exact_mod_cast hlow
    nlinarith
  refine ⟨?_, rfl, rfl, ?_, ?_, hlowReal⟩
  · exact ⟨hDpow, hZpow, rfl, rfl, hpositive⟩
  · simpa [encodeBlock, LowGapBlock.span, hell] using hlower
  · simpa [encodeBlock, LowGapBlock.span, hell] using hupper

/-- A gap belonging to an occurring block belongs to its ambient segment. -/
theorem LowGapBlock.mem_segment
    (segment : OddDenominatorSegment) (block : LowGapBlock)
    (hoccurs : block.OccursIn segment) {g : ℕ} (hg : g ∈ block.gaps) :
    g ∈ segment.gaps := by
  have htake : g ∈ (segment.gaps.drop block.offset).take block.gaps.length := by
    rw [hoccurs.2]
    exact hg
  exact List.mem_of_mem_drop (List.mem_of_mem_take htake)

/-- The start of a nonempty selected block has a strict order-window offset. -/
theorem sourceWindowOffset_lt
    (Q : ℕ) (W : WindowSystem) (Z0 k : ℕ)
    (data : AnchorInteriorData) (hvalid : data.Valid Q W Z0 k)
    (block : LowGapBlock) (hoccurs : block.OccursIn data.segment)
    (hne : block.gaps ≠ []) :
    sourceWindowOffset W k data block < W.m := by
  have hindex := sourceEndpointIndex_le_succ Q W Z0 k data hvalid block
    hoccurs [] List.nil_prefix
  have hlen : 0 < block.gaps.length := List.length_pos_iff.mpr hne
  rw [WindowSystem.m]
  unfold sourceWindowOffset
  have hsk := hvalid.1
  simp only [List.length_nil, Nat.add_zero] at hindex
  omega

/-- The stable primitive-step bound transfers unchanged to the canonical line
at the start of every selected block. -/
theorem sourceRawLine_step
    (Q : ℕ) (W : WindowSystem) (data : AnchorInteriorData) (Cstep : ℝ)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hstep : (data.segment.startLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W) :
    ((sourceRawLine Q data block).canonicalGeometricLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W := by
  have hprimitive := data.segment.prefixLine_primitive Q hsegment block.offset
  have hprimitiveRaw : Int.gcd (sourceRawLine Q data block).H
      (sourceRawLine Q data block).K = 1 := by
    simpa [sourceRawLine] using hprimitive
  have hcanonical :
      ((sourceRawLine Q data block).canonicalGeometricLine.H : ℤ) =
        (sourceRawLine Q data block).H := by
    rw [(sourceRawLine Q data block).canonicalGeometricLine_H_cast]
    simp [AffineLine.primitiveHorizontalInt, AffineLine.directionGCD, hprimitiveRaw]
  have hcanonicalReal :
      ((sourceRawLine Q data block).canonicalGeometricLine.H : ℝ) =
        ((sourceRawLine Q data block).H : ℝ) := by exact_mod_cast hcanonical
  rw [hcanonicalReal]
  simpa [sourceRawLine, AffineLine.transformWord_H] using hstep

/-- A genuine selected block realizes its encoding on both the raw affine line
and its canonical geometric line. -/
theorem sourceBlock_realizes
    (Q D Z : ℕ) (hQ : 0 < Q) (data : AnchorInteriorData)
    (hsegment : data.segment.Valid Q) (block : LowGapBlock)
    (hoccurs : block.OccursIn data.segment)
    (hDle : D ≤ data.segment.q) (hqD : data.segment.q < 2 * D) :
    LineRealizesEncoding Q (sourceRawLine Q data block) (encodeBlock D Z block) ∧
      GeometricLineRealizesEncoding Q
        (sourceRawLine Q data block).canonicalGeometricLine
        (encodeBlock D Z block) ∧
      SharedGapTrajectory Q (sourceRawLine Q data block) block.gaps
        (sourceBlockEndLine Q data block) := by
  have hoffset : block.offset ≤ data.segment.gaps.length :=
    le_trans (Nat.le_add_right block.offset block.gaps.length) hoccurs.1
  have hrawData := data.segment.prefixSlope_data Q hsegment block.offset hoffset
  have hrawDen : ((sourceRawLine Q data block).slope Q).den = data.segment.q := by
    simpa [sourceRawLine] using hrawData.2.1
  have htrajectory : SharedGapTrajectory Q (sourceRawLine Q data block) block.gaps
      (sourceBlockEndLine Q data block) := by
    rw [sharedGapTrajectory_iff_transformWord]
    rfl
  have htakeEnd : data.segment.gaps.take (block.offset + block.gaps.length) =
      data.segment.gaps.take block.offset ++ block.gaps := by
    calc
      data.segment.gaps.take (block.offset + block.gaps.length) =
          data.segment.gaps.take block.offset ++
            (data.segment.gaps.drop block.offset).take block.gaps.length :=
        List.take_add
      _ = data.segment.gaps.take block.offset ++ block.gaps := by rw [hoccurs.2]
  have hendData := data.segment.prefixSlope_data Q hsegment
    (block.offset + block.gaps.length) hoccurs.1
  have hendSlope :
      (sourceBlockEndLine Q data block).slope Q =
        (data.segment.startLine.transformWord Q
          (data.segment.gaps.take (block.offset + block.gaps.length))).slope Q := by
    unfold sourceBlockEndLine sourceRawLine
    rw [htakeEnd, AffineLine.transformWord_append]
  have hendInteriorRat : (sourceBlockEndLine Q data block).slope Q ∈
      Set.Ioo (0 : ℚ) 1 := by
    rw [hendSlope]
    exact hendData.1
  have hendInteriorReal : ((sourceBlockEndLine Q data block).slope Q : ℝ) ∈
      Set.Ioo (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hendInteriorRat.1, by exact_mod_cast hendInteriorRat.2⟩
  have hcanonicalSlope :=
    (sourceRawLine Q data block).canonicalGeometricLine_slope Q hQ
  have hslopeAfter :
      slopeAfter block.gaps
          ((sourceRawLine Q data block).canonicalGeometricLine.slope Q : ℝ) =
        ((sourceBlockEndLine Q data block).slope Q : ℝ) := by
    rw [hcanonicalSlope]
    exact (AffineLine.transformWord_slope_real Q hQ
      (sourceRawLine Q data block) block.gaps).symm
  refine ⟨?_, ?_, htrajectory⟩
  · exact ⟨by simpa [encodeBlock, hrawDen] using hDle,
      by simpa [encodeBlock, hrawDen] using hqD,
      ⟨sourceBlockEndLine Q data block, htrajectory⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [encodeBlock, hcanonicalSlope, hrawDen] using hDle
    · simpa [encodeBlock, hcanonicalSlope, hrawDen] using hqD
    · change slopeAfter block.gaps
        ((sourceRawLine Q data block).canonicalGeometricLine.slope Q : ℝ) ∈
          Set.Ioo (0 : ℝ) 1
      rw [hslopeAfter]
      exact hendInteriorReal

/-- Every genuine deterministic selected block, with the eventual logarithmic
cap and stable step bound, constructs the full spatial source required by the
interior fibre argument. -/
theorem selectedBlock_isSpatialEncodingSource
    (Q Cgap : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 k : ℕ)
    (selection : InteriorAnchorSelection) (data : AnchorInteriorData)
    (Cstep : ℝ) (block : LowGapBlock)
    (hden : W.rational.eta.den = Q)
    (hselected : selection k = some data)
    (hvalid : data.Valid Q W Z0 k)
    (hstep : (data.segment.startLine.H : ℝ) ≤
      Cstep * W.X / frequencyCutoff W)
    (hellCap : selectedLogLength selection k ≤ W.L + Cgap)
    (hL : 1 ≤ W.L)
    (hblock : block ∈ selectedBlocks data.segment W.structural.B
      (selectedLogLength selection k) (selectedMeanGapBand selection k)
      (reconstructionForwardLength W Cgap)) :
    IsSpatialEncodingSource Q Cgap W.structural.B Cstep W Z0 selection
      (encodeBlock (selectedDenominatorBand selection k)
        (selectedMeanGapBand selection k) block) (k, block) := by
  let D := selectedDenominatorBand selection k
  let Z := selectedMeanGapBand selection k
  let ell := selectedLogLength selection k
  have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
  have hqpos : 0 < data.segment.q := lt_trans (by omega) hsegment.2.2.2.2.1
  have hD : D = dyadicFloorBand data.segment.q := by
    simp [D, selectedDenominatorBand, hselected]
  have hZ : Z = meanGapBand data.segment.span data.segment.gapCount := by
    simp [Z, selectedMeanGapBand, hselected]
  have hDle : D ≤ data.segment.q := by
    rw [hD]
    exact dyadicFloorBand_le hqpos
  have hqD : data.segment.q < 2 * D := by
    rw [hD]
    exact dyadicFloorBand_lt_two_mul _
  have hell : ell = Nat.ceil (Real.logb 2 (4 * D)) := by rfl
  have hgapEll : ∀ g ∈ data.segment.gaps, g ≤ ell := by
    rw [hell]
    exact data.segment.gap_le_logBand Q D hQ hsegment hqD
  have hspec := selectedBlocks_mem_spec data.segment W.structural.B ell Z
    (reconstructionForwardLength W Cgap) block (by simpa [ell, Z] using hblock)
  rcases hspec with ⟨hoccurs, hgreedy, hlow, hforward⟩
  have hblockPositive : block.gaps.Positive := by
    intro g hg
    exact hsegment.2.1 g (block.mem_segment data.segment hoccurs hg)
  have hblockGap : ∀ g ∈ block.gaps, g ≤ ell := by
    intro g hg
    exact hgapEll g (block.mem_segment data.segment hoccurs hg)
  have hDpow : ∃ d : ℕ, D = 2 ^ d := by
    rw [hD]
    exact dyadicFloorBand_isPow _
  have hZpow : ∃ z : ℕ, Z = 2 ^ z := by
    rw [hZ]
    unfold meanGapBand
    exact dyadicFloorBand_isPow _
  have hcandidate : encodeBlock D Z block ∈ encodingCandidates D Z W.structural.B :=
    encodeBlock_mem_encodingCandidates W.structural.B D Z ell block hDpow
      hZpow hell hgreedy hblockGap hlow hblockPositive
  have hoffset : sourceWindowOffset W k data block < W.m :=
    sourceWindowOffset_lt Q W Z0 k data hvalid block hoccurs hgreedy.1
  have hprimitive : Int.gcd (sourceRawLine Q data block).H
      (sourceRawLine Q data block).K = 1 := by
    simpa [sourceRawLine] using
      data.segment.prefixLine_primitive Q hsegment block.offset
  have hcanonicalStep := sourceRawLine_step Q W data Cstep hsegment block hstep
  obtain ⟨hlineRealizes, hgeometricRealizes, hblockTrajectory⟩ :=
    sourceBlock_realizes Q D Z hQ data hsegment block hoccurs hDle hqD
  have hgapCap : ∀ g ∈ data.segment.gaps, g ≤ W.L + Cgap := by
    intro g hg
    exact (hgapEll g hg).trans (by simpa [ell] using hellCap)
  obtain ⟨hforwardLower, hforwardUpper, hforwardPositive⟩ :=
    sourceForwardWord_spec Q Cgap W data hsegment block hforward hgapCap hL
  have hforwardInterior :=
    sourceForwardWord_interior Q Cgap W data hsegment block hoccurs
  obtain ⟨t, hparameter⟩ := exists_originalSourceParameter Q W Z0 k hden data
    hvalid block hoccurs hoffset
  refine ⟨data, t, ?_, hparameter⟩
  refine ⟨hselected, hvalid, hvalid.2.2.1, ?_, hoccurs, hoffset, ?_, ?_, ?_,
    hprimitive, rfl, hcanonicalStep, ?_, ?_, hblockTrajectory,
    hforwardLower, hforwardUpper, hforwardPositive, hforwardInterior⟩
  · simpa [ell, Z, encodingLogLength, encodeBlock] using hblock
  · simpa [D, Z, encodeBlock] using hcandidate
  · simp [encodeBlock]
  · rfl
  · simpa [D, Z] using hlineRealizes
  · simpa [D, Z] using hgeometricRealizes

/-- Certified real mass of the long-interior parent family. -/
def interiorPairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (interiorPairs W Z0)
    (interiorPairs_subset_pairSet W Z0)

/-- The tail of a nonnegative real geometric series, written as an indicator
on all natural-number exponents. -/
theorem tsum_geometric_indicator_ge
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑' i : ℕ, if n ≤ i then r ^ i else 0) = r ^ n * (1 - r)⁻¹ := by
  have hsummable : Summable (fun i : ℕ ↦ if n ≤ i then r ^ i else 0) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).indicator
      {i : ℕ | n ≤ i}).congr ?_
    intro i
    simp [Set.indicator_apply]
  have hprefix :
      (∑ i ∈ Finset.range n, if n ≤ i then r ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [Nat.not_le.mpr hi]
  rw [← hsummable.sum_add_tsum_nat_add n, hprefix, zero_add]
  simp only [Nat.le_add_left, if_true, pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1, mul_comm]

/-- Any finite collection of distinct exponents lying above `n` is bounded by
the full geometric tail beginning at `n`. -/
theorem finset_geometric_tail_le
    (s : Finset ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hmin : ∀ i ∈ s, n ≤ i) :
    (∑ i ∈ s, r ^ i) ≤ r ^ n * (1 - r)⁻¹ := by
  have hsummable : Summable (fun i : ℕ ↦ if n ≤ i then r ^ i else 0) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).indicator
      {i : ℕ | n ≤ i}).congr ?_
    intro i
    simp [Set.indicator_apply]
  calc
    (∑ i ∈ s, r ^ i) = ∑ i ∈ s, (if n ≤ i then r ^ i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hmin i hi]
    _ ≤ ∑' i : ℕ, (if n ≤ i then r ^ i else 0) := by
      exact hsummable.sum_le_tsum s (fun i _ ↦ by positivity)
    _ = r ^ n * (1 - r)⁻¹ := tsum_geometric_indicator_ge hr0 hr1 n

/-- Reindexing version of `finset_geometric_tail_le`.  It is useful when the
objects being summed are bands, while `exponent` extracts their dyadic
exponents. -/
theorem finset_geometric_tail_le_of_inj
    { α : Type* } [DecidableEq α] (s : Finset α) (exponent : α → ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hinj : Set.InjOn exponent s)
    (hmin : ∀ a ∈ s, n ≤ exponent a) :
    (∑ a ∈ s, r ^ exponent a) ≤ r ^ n * (1 - r)⁻¹ := by
  calc
    (∑ a ∈ s, r ^ exponent a) =
        ∑ i ∈ s.image exponent, r ^ i :=
      (Finset.sum_image hinj).symm
    _ ≤ r ^ n * (1 - r)⁻¹ := by
      apply finset_geometric_tail_le (s.image exponent) hr0 hr1 n
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact hmin a ha

/-- Weighted outer-band form.  If the contribution of band `i` is bounded by
`C * r^i`, summing any finite collection above `n` costs one geometric-tail
factor. -/
theorem finset_weighted_geometric_tail_le
    (s : Finset ℕ) (weight : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hmin : ∀ i ∈ s, n ≤ i)
    (hweight : ∀ i ∈ s, weight i ≤ C * r ^ i) :
    (∑ i ∈ s, weight i) ≤ C * (r ^ n * (1 - r)⁻¹) := by
  calc
    (∑ i ∈ s, weight i) ≤ ∑ i ∈ s, C * r ^ i :=
      Finset.sum_le_sum hweight
    _ = C * ∑ i ∈ s, r ^ i := by
      rw [Finset.mul_sum]
    _ ≤ C * (r ^ n * (1 - r)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (finset_geometric_tail_le s hr0 hr1 n hmin) hC

/-- Ratio associated with the weight `D⁻¹ᐚ²` when `D = 2^d`. -/
def strictMassRatio : ℝ := (√2)⁻¹

theorem strictMassRatio_nonneg : 0 ≤ strictMassRatio := by
  unfold strictMassRatio
  positivity

theorem strictMassRatio_pos : 0 < strictMassRatio := by
  unfold strictMassRatio
  positivity

theorem strictMassRatio_lt_one : strictMassRatio < 1 := by
  unfold strictMassRatio
  exact (inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))).2 Real.one_lt_sqrt_two

theorem strictMassRatio_le_one : strictMassRatio ≤ 1 :=
  strictMassRatio_lt_one.le

theorem strictMassRatio_sq : strictMassRatio ^ 2 = (1 : ℝ) / 2 := by
  unfold strictMassRatio
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Ratio for the second (`Z`) geometric summation.  Its square is the
denominator ratio, so it absorbs the floor in `Z / 2`. -/
def strictMassOuterRatio : ℝ := √strictMassRatio

theorem strictMassOuterRatio_nonneg : 0 ≤ strictMassOuterRatio := by
  unfold strictMassOuterRatio
  exact Real.sqrt_nonneg _

theorem strictMassOuterRatio_pos : 0 < strictMassOuterRatio := by
  unfold strictMassOuterRatio
  exact Real.sqrt_pos.2 strictMassRatio_pos

theorem strictMassOuterRatio_lt_one : strictMassOuterRatio < 1 := by
  unfold strictMassOuterRatio
  calc
    √strictMassRatio < √(1 : ℝ) :=
      Real.sqrt_lt_sqrt strictMassRatio_nonneg strictMassRatio_lt_one
    _ = 1 := Real.sqrt_one

theorem strictMassOuterRatio_le_one : strictMassOuterRatio ≤ 1 :=
  strictMassOuterRatio_lt_one.le

theorem strictMassOuterRatio_sq :
    strictMassOuterRatio ^ 2 = strictMassRatio := by
  unfold strictMassOuterRatio
  exact Real.sq_sqrt strictMassRatio_nonneg

theorem strictMassOuterRatio_fourth :
    strictMassOuterRatio ^ 4 = (1 : ℝ) / 2 := by
  calc
    strictMassOuterRatio ^ 4 = (strictMassOuterRatio ^ 2) ^ 2 := by
      ring
    _ = strictMassRatio ^ 2 := by rw [strictMassOuterRatio_sq]
    _ = (1 : ℝ) / 2 := strictMassRatio_sq

/-- The floor in `Z / 2` costs only one fixed outer-ratio factor. -/
theorem strictMassRatio_pow_div_two_le_outer (Z : ℕ) :
    strictMassRatio ^ (Z / 2) ≤
      strictMassOuterRatio⁻¹ * strictMassOuterRatio ^ Z := by
  apply (le_inv_mul_iff₀ strictMassOuterRatio_pos).2
  calc
    strictMassOuterRatio * strictMassRatio ^ (Z / 2) =
        strictMassOuterRatio ^ (2 * (Z / 2) + 1) := by
      rw [pow_add, pow_mul, strictMassOuterRatio_sq, pow_one]
      ring
    _ ≤ strictMassOuterRatio ^ Z :=
      pow_le_pow_of_le_one strictMassOuterRatio_nonneg
        strictMassOuterRatio_le_one (by omega)

/-- Four outer-ratio powers equal one factor `1/2`; hence the lower cutoff
`Z₀/32` produces the advertised exponent `Z₀/128`. -/
theorem strictMassOuterRatio_pow_div32_le (Z₀ : ℕ) :
    strictMassOuterRatio ^ (Z₀ / 32) ≤
      ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
  calc
    strictMassOuterRatio ^ (Z₀ / 32) ≤
        strictMassOuterRatio ^ (4 * (Z₀ / 128)) :=
      pow_le_pow_of_le_one strictMassOuterRatio_nonneg
        strictMassOuterRatio_le_one (by omega)
    _ = ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
      rw [pow_mul, strictMassOuterRatio_fourth]

theorem sqrt_two_pow (d : ℕ) :
    √((2 : ℝ) ^ d) = (√2) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- Exact conversion from a dyadic denominator to a geometric weight. -/
theorem inv_sqrt_nat_two_pow (d : ℕ) :
    1 / √(((2 ^ d : ℕ) : ℝ)) = strictMassRatio ^ d := by
  rw [Nat.cast_pow, Nat.cast_ofNat, sqrt_two_pow]
  simp [strictMassRatio, div_eq_mul_inv]

/-- Single-layer denominator-band estimate.  It is the directly composable
form for one fixed mean-gap band `Z`: use `n = Z / 2`. -/
theorem dyadicExponentBandTail
    (exponents : Finset ℕ) (n : ℕ)
    (hmin : ∀ d ∈ exponents, n ≤ d) :
    (∑ d ∈ exponents, 1 / √(((2 ^ d : ℕ) : ℝ))) ≤
      strictMassRatio ^ n * (1 - strictMassRatio)⁻¹ := by
  simp_rw [inv_sqrt_nat_two_pow]
  exact finset_geometric_tail_le exponents strictMassRatio_nonneg
    strictMassRatio_lt_one n hmin

/-- The constant left after summing a single denominator band. -/
def strictMassTailConstant : ℝ := (1 - strictMassRatio)⁻¹

theorem strictMassTailConstant_pos : 0 < strictMassTailConstant := by
  unfold strictMassTailConstant
  exact inv_pos.mpr (sub_pos.mpr strictMassRatio_lt_one)

/-- Explicit cutoff tail used by the final strict-mass estimate. -/
def strictMassTail (Z₀ : ℕ) : ℝ :=
  strictMassTailConstant * ((1 : ℝ) / 2) ^ (Z₀ / 128)

theorem strictMassTail_nonneg (Z₀ : ℕ) : 0 ≤ strictMassTail Z₀ := by
  unfold strictMassTail
  exact mul_nonneg strictMassTailConstant_pos.le (pow_nonneg (by norm_num) _)

theorem strictMassTail_tendsto_zero :
    Tendsto strictMassTail atTop (𝓝 0) := by
  change Tendsto
    (fun Z₀ : ℕ ↦ strictMassTailConstant * ((1 : ℝ) / 2) ^ (Z₀ / 128))
    atTop (𝓝 0)
  have hdiv : Tendsto (fun Z₀ : ℕ ↦ Z₀ / 128) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hpow : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hconst :
      Tendsto (fun _ : ℕ ↦ strictMassTailConstant) atTop
        (𝓝 strictMassTailConstant) :=
    tendsto_const_nhds
  simpa only [Function.comp_apply, mul_zero] using
    hconst.mul (hpow.comp hdiv)

/-- Dividing first by `64` leaves at least twice the exponent obtained by
dividing by `128`; this is the bookkeeping behind the paper's `Z₀/128`
decay. -/
theorem twice_div_128_le_div_64 (Z₀ : ℕ) :
    2 * (Z₀ / 128) ≤ Z₀ / 64 := by
  omega

theorem strictMassRatio_pow_div64_le (Z₀ : ℕ) :
    strictMassRatio ^ (Z₀ / 64) ≤
      ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
  calc
    strictMassRatio ^ (Z₀ / 64) ≤
        strictMassRatio ^ (2 * (Z₀ / 128)) :=
      pow_le_pow_of_le_one strictMassRatio_nonneg strictMassRatio_le_one
        (twice_div_128_le_div_64 Z₀)
    _ = ((1 : ℝ) / 2) ^ (Z₀ / 128) := by
      rw [pow_mul, strictMassRatio_sq]

/-- A one-layer dyadic family whose exponent is eventually at least
`Z₀/64` already contributes at most the explicit `Z₀/128` tail. -/
theorem dyadicExponentBandTail_le_strictMassTail
    (exponents : Finset ℕ) (Z₀ : ℕ)
    (hmin : ∀ d ∈ exponents, Z₀ / 64 ≤ d) :
    (∑ d ∈ exponents, 1 / √(((2 ^ d : ℕ) : ℝ))) ≤
      strictMassTail Z₀ := by
  calc
    (∑ d ∈ exponents, 1 / √(((2 ^ d : ℕ) : ℝ))) ≤
        strictMassRatio ^ (Z₀ / 64) * strictMassTailConstant := by
      simpa only [strictMassTailConstant] using
        dyadicExponentBandTail exponents (Z₀ / 64) hmin
    _ ≤ ((1 : ℝ) / 2) ^ (Z₀ / 128) * strictMassTailConstant := by
      exact mul_le_mul_of_nonneg_right (strictMassRatio_pow_div64_le Z₀)
        strictMassTailConstant_pos.le
    _ = strictMassTail Z₀ := by
      simp only [strictMassTail]
      ring

/-- Two-layer tail in the representation used by the interior band sum.

`keys` stores `(D,Z)`.  The witness `exponent` records `D = 2^d`; within a
fixed `Z`-fiber this makes `exponent` injective automatically.  The only
analytic lower bound needed here is `Z/2 ≤ d`.  In the application it follows,
for all sufficiently large `Z`, from the stronger manuscript estimate
`cBand * 2^Z ≤ D`.
-/
theorem finite_dyadic_band_pair_tail
    (keys : Finset (ℕ × ℕ)) (exponent : ℕ × ℕ → ℕ) (Z₀ : ℕ)
    (hdyadic : ∀ key ∈ keys, key.1 = 2 ^ exponent key)
    (hcutoff : ∀ key ∈ keys, Z₀ / 32 ≤ key.2)
    (hlower : ∀ key ∈ keys, key.2 / 2 ≤ exponent key) :
    (∑ key ∈ keys, 1 / √((key.1 : ℝ))) ≤
      strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
        strictMassTail Z₀ := by
  let zBands : Finset ℕ := keys.image Prod.snd
  let fiberWeight : ℕ → ℝ := fun Z ↦
    ∑ key ∈ keys with key.2 = Z, 1 / √((key.1 : ℝ))
  have hratioInv : 0 ≤ strictMassOuterRatio⁻¹ :=
    inv_nonneg.mpr strictMassOuterRatio_nonneg
  have houterTailInv : 0 ≤ (1 - strictMassOuterRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr strictMassOuterRatio_le_one)
  have hsingleConstant :
      0 ≤ strictMassOuterRatio⁻¹ * strictMassTailConstant :=
    mul_nonneg hratioInv strictMassTailConstant_pos.le
  have hfiber (Z : ℕ) (hZ : Z ∈ zBands) :
      fiberWeight Z ≤
        (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
          strictMassOuterRatio ^ Z := by
    let fiber : Finset (ℕ × ℕ) := keys.filter fun key ↦ key.2 = Z
    have hinj : Set.InjOn exponent fiber := by
      intro a ha b hb hab
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      apply Prod.ext
      · rw [hdyadic a ha'.1, hdyadic b hb'.1, hab]
      · exact ha'.2.trans hb'.2.symm
    have hmin : ∀ key ∈ fiber, Z / 2 ≤ exponent key := by
      intro key hkey
      have hkey' := Finset.mem_filter.mp hkey
      simpa only [hkey'.2] using hlower key hkey'.1
    have hrewrite :
        fiberWeight Z = ∑ key ∈ fiber, strictMassRatio ^ exponent key := by
      apply Finset.sum_congr rfl
      intro key hkey
      have hkey' := Finset.mem_filter.mp hkey
      rw [hdyadic key hkey'.1, inv_sqrt_nat_two_pow]
    rw [hrewrite]
    calc
      (∑ key ∈ fiber, strictMassRatio ^ exponent key) ≤
          strictMassRatio ^ (Z / 2) * strictMassTailConstant := by
        simpa only [strictMassTailConstant] using
          finset_geometric_tail_le_of_inj fiber exponent
            strictMassRatio_nonneg strictMassRatio_lt_one (Z / 2) hinj hmin
      _ ≤
          (strictMassOuterRatio⁻¹ * strictMassOuterRatio ^ Z) *
            strictMassTailConstant :=
        mul_le_mul_of_nonneg_right
          (strictMassRatio_pow_div_two_le_outer Z)
          strictMassTailConstant_pos.le
      _ = (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
          strictMassOuterRatio ^ Z := by ring
  have hzMin : ∀ Z ∈ zBands, Z₀ / 32 ≤ Z := by
    intro Z hZ
    obtain ⟨key, hkey, rfl⟩ := Finset.mem_image.mp hZ
    exact hcutoff key hkey
  calc
    (∑ key ∈ keys, 1 / √((key.1 : ℝ))) =
        ∑ Z ∈ zBands, fiberWeight Z := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := keys) (t := zBands) (g := Prod.snd) (M := ℝ)
        (fun key hkey ↦ Finset.mem_image_of_mem Prod.snd hkey)
        (fun key ↦ 1 / √((key.1 : ℝ)))
    _ ≤ (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
        (strictMassOuterRatio ^ (Z₀ / 32) *
          (1 - strictMassOuterRatio)⁻¹) :=
      finset_weighted_geometric_tail_le zBands fiberWeight
        (strictMassOuterRatio⁻¹ * strictMassTailConstant) hsingleConstant
        strictMassOuterRatio_nonneg strictMassOuterRatio_lt_one (Z₀ / 32)
        hzMin hfiber
    _ ≤ (strictMassOuterRatio⁻¹ * strictMassTailConstant) *
        (((1 : ℝ) / 2) ^ (Z₀ / 128) *
          (1 - strictMassOuterRatio)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hsingleConstant
      exact mul_le_mul_of_nonneg_right
        (strictMassOuterRatio_pow_div32_le Z₀) houterTailInv
    _ = strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
        strictMassTail Z₀ := by
      rw [strictMassTail]
      ac_rfl

/-- For every fixed positive band constant, the manuscript lower bound
`cBand * 2^Z ≤ 2^d` eventually implies the deliberately weaker exponent
bound `Z/2 ≤ d` used by `finite_dyadic_band_pair_tail`. -/
theorem exists_dyadic_exponent_cutoff (cBand : ℝ) (hcBand : 0 < cBand) :
    ∃ Zc : ℕ, ∀ {Z d : ℕ}, Zc ≤ Z →
      cBand * (2 : ℝ) ^ Z ≤ (2 : ℝ) ^ d → Z / 2 ≤ d := by
  obtain ⟨K, hK⟩ :=
    pow_unbounded_of_one_lt cBand⁻¹ (by norm_num : (1 : ℝ) < 2)
  refine ⟨2 * K, ?_⟩
  intro Z d hZ hband
  have hpow : (2 : ℝ) ^ Z ≤ (2 : ℝ) ^ (K + d) := by
    calc
      (2 : ℝ) ^ Z ≤ cBand⁻¹ * (2 : ℝ) ^ d :=
        (le_inv_mul_iff₀ hcBand).2 hband
      _ ≤ (2 : ℝ) ^ K * (2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hK.le (by positivity)
      _ = (2 : ℝ) ^ (K + d) := by rw [pow_add]
  have hZd : Z ≤ K + d :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

/-- Direct arbitrary-`cBand` wrapper for finite `(D,Z)` band keys.  The
returned `Zc` depends only on `cBand`, not on the key set, `Z₀`, or the
support. -/
theorem exists_finite_dyadic_band_pair_tail_of_lower
    (cBand : ℝ) (hcBand : 0 < cBand) :
    ∃ Zc : ℕ, ∀ (keys : Finset (ℕ × ℕ))
      (exponent : ℕ × ℕ → ℕ) (Z₀ : ℕ),
      (∀ key ∈ keys, key.1 = 2 ^ exponent key) →
      (∀ key ∈ keys, Z₀ / 32 ≤ key.2) →
      (∀ key ∈ keys, Zc ≤ key.2) →
      (∀ key ∈ keys,
        cBand * (2 : ℝ) ^ key.2 ≤ (key.1 : ℝ)) →
      (∑ key ∈ keys, 1 / √((key.1 : ℝ))) ≤
        strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
          strictMassTail Z₀ := by
  obtain ⟨Zc, hZc⟩ := exists_dyadic_exponent_cutoff cBand hcBand
  refine ⟨Zc, ?_⟩
  intro keys exponent Z₀ hdyadic hcutoff hlarge hband
  apply finite_dyadic_band_pair_tail keys exponent Z₀ hdyadic hcutoff
  intro key hkey
  apply hZc (hlarge key hkey)
  have h := hband key hkey
  rw [hdyadic key hkey, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h


def strictCoverLinearConstant (B : ℝ) : ℕ :=
  64 * (5 + 2 * Nat.ceil (B + 1))

def strictCoverCutoff (B kappa : ℝ) : ℕ :=
  Nat.ceil (strictCoverLinearConstant B / kappa) + 1

theorem selectedCoverReserve_le_segment
    (W : WindowSystem) (gap : GapParams W.rational.eta.den)
    (selection : InteriorAnchorSelection) (e : WindowThreshold)
    (data : AnchorInteriorData) (Z0 : ℕ) (kappa : ℝ)
    (hkappa : 0 < kappa)
    (hlevel : max 1 gap.Cgap ≤ W.L)
    (hcutoff : strictCoverCutoff W.structural.B kappa ≤ Z0)
    (hm : kappa * W.L < W.m)
    (hlargePair : (W.m : ℝ) * Z0 < W.excess e)
    (hspan : W.excess e / 16 ≤ data.segment.span)
    (hell : selectedLogLength selection e.1 ≤ W.L + gap.Cgap) :
    4 * (selectedForwardLength W gap e.1 +
      Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1)) ≤
        data.segment.span := by
  let C := Nat.ceil (W.structural.B + 1)
  let A := selectedForwardLength W gap e.1 +
    Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1)
  let K := strictCoverLinearConstant W.structural.B
  have hLone : 1 ≤ W.L := (le_max_left _ _).trans hlevel
  have hgapL : gap.Cgap ≤ W.L := (le_max_right _ _).trans hlevel
  have hCbound : W.structural.B + 1 ≤ (C : ℝ) := by
    exact Nat.le_ceil _
  have hcap : Nat.ceil ((W.structural.B + 1) *
      selectedLogLength selection e.1) ≤ C * selectedLogLength selection e.1 := by
    rw [Nat.ceil_le]
    have hellNonneg : (0 : ℝ) ≤ selectedLogLength selection e.1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hCbound hellNonneg
    exact_mod_cast hmul
  have hforward : selectedForwardLength W gap e.1 ≤ 5 * W.L := by
    simp only [selectedForwardLength, reconstructionForwardLength]
    omega
  have hellTwo : selectedLogLength selection e.1 ≤ 2 * W.L := by omega
  have hALinear : A ≤ (5 + 2 * C) * W.L := by
    dsimp [A]
    calc
      selectedForwardLength W gap e.1 +
          Nat.ceil ((W.structural.B + 1) * selectedLogLength selection e.1) ≤
          5 * W.L + C * selectedLogLength selection e.1 :=
        Nat.add_le_add hforward hcap
      _ ≤ 5 * W.L + C * (2 * W.L) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left C hellTwo) _
      _ = (5 + 2 * C) * W.L := by ring
  have hKLinear : 64 * A ≤ K * W.L := by
    calc
      64 * A ≤ 64 * ((5 + 2 * C) * W.L) :=
        Nat.mul_le_mul_left 64 hALinear
      _ = K * W.L := by
        simp [K, strictCoverLinearConstant, C]
        ring
  have hKappaCutoff : (K : ℝ) < kappa * strictCoverCutoff W.structural.B kappa := by
    have hcutoffEq : strictCoverCutoff W.structural.B kappa =
        Nat.ceil ((K : ℝ) / kappa) + 1 := by
      simp [strictCoverCutoff, K]
    have hquot : (K : ℝ) / kappa < strictCoverCutoff W.structural.B kappa := by
      rw [hcutoffEq]
      have hle : (K : ℝ) / kappa ≤
          Nat.ceil ((K : ℝ) / kappa) := Nat.le_ceil _
      have hsucc : ((Nat.ceil ((K : ℝ) / kappa) : ℕ) : ℝ) <
          ((Nat.ceil ((K : ℝ) / kappa) + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_self (Nat.ceil ((K : ℝ) / kappa)))
      exact hle.trans_lt hsucc
    simpa only [mul_comm] using (div_lt_iff₀ hkappa).1 hquot
  have hKZ : (K : ℝ) < kappa * Z0 := by
    have hcutoffReal : (strictCoverCutoff W.structural.B kappa : ℝ) ≤ Z0 := by
      exact_mod_cast hcutoff
    nlinarith [mul_le_mul_of_nonneg_left hcutoffReal hkappa.le]
  have hLpos : (0 : ℝ) < W.L := by exact_mod_cast hLone
  have hKL : (K : ℝ) * W.L < kappa * Z0 * W.L :=
    mul_lt_mul_of_pos_right hKZ hLpos
  have hmZ : kappa * Z0 * W.L < (W.m : ℝ) * Z0 := by
    have hZpos : (0 : ℝ) < Z0 := by
      have hcutoffPos : 0 < strictCoverCutoff W.structural.B kappa := by
        simp [strictCoverCutoff]
      exact_mod_cast lt_of_lt_of_le hcutoffPos hcutoff
    nlinarith [mul_lt_mul_of_pos_right hm hZpos]
  have h64A : (64 * A : ℕ) < W.m * Z0 := by
    have h64AReal : ((64 * A : ℕ) : ℝ) < ((W.m * Z0 : ℕ) : ℝ) := by
      calc
        ((64 * A : ℕ) : ℝ) ≤ ((K * W.L : ℕ) : ℝ) := by exact_mod_cast hKLinear
        _ < kappa * Z0 * W.L := by simpa using hKL
        _ < (W.m : ℝ) * Z0 := hmZ
        _ = ((W.m * Z0 : ℕ) : ℝ) := by norm_num
    exact_mod_cast h64AReal
  have hmassSpan : ((W.m * Z0 : ℕ) : ℝ) < 16 * data.segment.span := by
    have hspan16 : W.excess e ≤ 16 * (data.segment.span : ℝ) := by
      nlinarith
    calc
      ((W.m * Z0 : ℕ) : ℝ) = (W.m : ℝ) * Z0 := by norm_num
      _ < W.excess e := hlargePair
      _ ≤ 16 * (data.segment.span : ℝ) := hspan16
  have h64ASpan : 64 * A < 16 * data.segment.span := by
    have hmassSpanNat : W.m * Z0 < 16 * data.segment.span := by
      exact_mod_cast hmassSpan
    omega
  dsimp [A] at h64ASpan ⊢
  omega

/-- A concrete finite, nonnegative refinement of each interior pair.  The
certificate lives in the interior layer because its actual anchor selection
and deterministic block decomposition are produced by the Section 6
argument, before the exact parent partition is assembled. -/
structure InteriorRefinement (W : WindowSystem) (Z0 : ℕ) where
  /-- The stabilized segment actually selected at each spatial anchor. -/
  selection : InteriorAnchorSelection
  selection_valid :
    ValidInteriorAnchorSelection W.rational.eta.den W Z0 selection
  /-- Denominator-level gap data and the affine step constant are fixed for
  the whole refinement, rather than chosen separately by a block. -/
  gap : GapParams W.rational.eta.den
  Cstep : ℝ
  Cstep_pos : 0 < Cstep
  /-- Anchor-level parameters used by the deterministic greedy rule. -/
  ell : ℕ → ℕ
  meanGap : ℕ → ℕ
  forward : ℕ → ℕ
  denominatorBand : ℕ → ℕ
  blocks : ℕ → List LowGapBlock
  denominatorBand_pos : ∀ k, 0 < denominatorBand k
  meanGap_pos : ∀ k, 0 < meanGap k
  ell_eq : ∀ k,
    ell k = Nat.ceil (Real.logb 2 (4 * denominatorBand k))
  forward_eq : ∀ k,
    forward k = reconstructionForwardLength W gap.Cgap
  /-- Every interior pair is backed by the actual selected segment at its
  anchor, and its block list is exactly the threshold-independent greedy
  selection from that segment. -/
  selected_data : ∀ e, e ∈ interiorPairs W Z0 →
    ∃ data : AnchorInteriorData,
      selection e.1 = some data ∧
      data.Valid W.rational.eta.den W Z0 e.1 ∧
      blocks e.1 = selectedBlocks data.segment W.structural.B
        (ell e.1) (meanGap e.1) (forward e.1)
  blocks_nodup : ∀ k, (blocks k).Nodup
  /-- Each retained block is a genuine spatial source of its actual encoding.
  This is the bridge from the anchor-level refinement to line uniqueness and
  the source-fibre estimate. -/
  source_valid : ∀ e, e ∈ interiorPairs W Z0 →
    ∀ block ∈ blocks e.1,
      IsSpatialEncodingSource W.rational.eta.den gap.Cgap
        W.structural.B Cstep W Z0 selection
        (encodeBlock (denominatorBand e.1) (meanGap e.1) block)
        (e.1, block)
  labels : WindowThreshold → Finset LowGapBlock
  weight : WindowThreshold → LowGapBlock → ℝ
  labels_eq : ∀ e, e ∈ interiorPairs W Z0 →
    labels e = (blocks e.1).toFinset
  weight_eq : ∀ e, e ∈ interiorPairs W Z0 → ∀ b ∈ labels e,
    weight e b = interiorComponentWeight (W.excess e) (blocks e.1) b
  weight_nonneg : ∀ e b, 0 ≤ weight e b
  sums_to_excess : ∀ e, e ∈ interiorPairs W Z0 →
    (∑ b ∈ labels e, weight e b) = W.excess e
  outside_zero : ∀ e, e ∉ interiorPairs W Z0 → labels e = ∅

structure InteriorRefinementUniformFacts {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (cBand Cstep : ℝ)
    (Cgap : ℕ) : Prop where
  cBand_pos : 0 < cBand
  Cstep_eq : refinement.Cstep = Cstep
  gap_Cgap_eq : refinement.gap.Cgap = Cgap
  selected_quantitative : ∀ e ∈ interiorPairs W Z0,
    ∃ data : AnchorInteriorData,
      refinement.selection e.1 = some data ∧
      data.Valid W.rational.eta.den W Z0 e.1 ∧
      W.excess e / 16 ≤ data.segment.span ∧
      1 ≤ data.segment.gapCount ∧
      data.segment.gapCount ≤ W.m ∧
      (data.segment.startLine.H : ℝ) ≤
        refinement.Cstep * W.X / frequencyCutoff W
  component_bound : ∀ e ∈ interiorPairs W Z0,
    ∀ block ∈ refinement.blocks e.1,
      interiorComponentWeight (W.excess e) (refinement.blocks e.1) block ≤
        32 * Nat.ceil ((W.structural.B + 1) * refinement.ell e.1)
  component_sum : ∀ e ∈ interiorPairs W Z0,
    (refinement.blocks e.1 |>.map fun block =>
      interiorComponentWeight (W.excess e) (refinement.blocks e.1) block).sum =
        W.excess e
  meanGap_cutoff : ∀ e ∈ interiorPairs W Z0,
    (Z0 : ℝ) / 32 < refinement.meanGap e.1
  denominator_lower : ∀ e ∈ interiorPairs W Z0,
    cBand * (2 : ℝ) ^ (refinement.meanGap e.1) ≤
      refinement.denominatorBand e.1
  denominator_isPow : ∀ k, ∃ d : ℕ, refinement.denominatorBand k = 2 ^ d
  meanGap_isPow : ∀ k, ∃ z : ℕ, refinement.meanGap k = 2 ^ z
  candidate : ∀ e ∈ interiorPairs W Z0,
    ∀ block ∈ refinement.blocks e.1,
      encodeBlock (refinement.denominatorBand e.1)
          (refinement.meanGap e.1) block ∈
        encodingCandidates (refinement.denominatorBand e.1)
          (refinement.meanGap e.1) W.structural.B

theorem interiorRefinement_exists_of_stable
    (Q : ℕ) (hQ : 0 < Q) (W : WindowSystem) (Z0 : ℕ)
    (gap : GapParams W.rational.eta.den) (Cstep : ℝ) (hCstep : 0 < Cstep)
    (selection : InteriorAnchorSelection)
    (hden : W.rational.eta.den = Q)
    (hselection : ValidInteriorAnchorSelection Q W Z0 selection)
    (hstable : ∀ e : WindowThreshold, LongInteriorPair W Z0 e →
      ∃ data : AnchorInteriorData,
        selection e.1 = some data ∧ data.Valid Q W Z0 e.1 ∧
        W.excess e / 16 ≤ data.segment.span ∧
        1 ≤ data.segment.gapCount ∧
        data.segment.gapCount ≤ W.m ∧
        (data.segment.startLine.H : ℝ) ≤
          Cstep * W.X / frequencyCutoff W)
    (hfrequency : 4 * (Q : ℝ) * Cstep ≤ frequencyCutoff W)
    (hlevel : max 1 gap.Cgap ≤ W.L)
    (hcutoff : strictCoverCutoff W.structural.B W.entropy.kappa ≤ Z0)
    (hm : W.entropy.kappa * W.L < W.m)
    (cspan : ℝ) (hcspan : 0 < cspan)
    (hdenSpan : ∀ segment : OddDenominatorSegment,
      segment.Valid Q → 0 < segment.gapCount →
      cspan * Real.rpow 2
        ((segment.span : ℝ) / segment.gapCount) ≤ segment.q) :
    ∃ refinement : InteriorRefinement W Z0,
      InteriorRefinementUniformFacts refinement (cspan / 2) Cstep gap.Cgap := by
  classical
  let ActiveAnchor : ℕ → Prop := fun k =>
    ∃ e : WindowThreshold, e.1 = k ∧ LongInteriorPair W Z0 e
  let trimmed : InteriorAnchorSelection := fun k =>
    if h : ActiveAnchor k then selection k else none
  have htrimmed_of_long (e : WindowThreshold)
      (he : LongInteriorPair W Z0 e) : trimmed e.1 = selection e.1 := by
    dsimp only [trimmed]
    split
    next => rfl
    next h => exact (h ⟨e, rfl, he⟩).elim
  have htrimmed_valid :
      ValidInteriorAnchorSelection Q W Z0 trimmed := by
    intro k data hdata
    by_cases hk : ActiveAnchor k
    · have horiginal : selection k = some data := by
        simpa [trimmed, hk] using hdata
      exact hselection k data horiginal
    · simp [trimmed, hk] at hdata
  have hstableTrimmed (e : WindowThreshold)
      (he : LongInteriorPair W Z0 e) :
      ∃ data : AnchorInteriorData,
        trimmed e.1 = some data ∧ data.Valid Q W Z0 e.1 ∧
        W.excess e / 16 ≤ data.segment.span ∧
        1 ≤ data.segment.gapCount ∧
        data.segment.gapCount ≤ W.m ∧
        (data.segment.startLine.H : ℝ) ≤
          Cstep * W.X / frequencyCutoff W := by
    rcases hstable e he with ⟨data, hselected, hrest⟩
    exact ⟨data, (htrimmed_of_long e he).trans hselected, hrest⟩
  let blocks : ℕ → List LowGapBlock :=
    selectedInteriorBlocks W trimmed gap
  have pairSpec (e : WindowThreshold) (he : e ∈ interiorPairs W Z0) :
      ∃ data : AnchorInteriorData,
        trimmed e.1 = some data ∧
        data.Valid Q W Z0 e.1 ∧
        W.excess e / 16 ≤ data.segment.span ∧
        1 ≤ data.segment.gapCount ∧
        data.segment.gapCount ≤ W.m ∧
        (data.segment.startLine.H : ℝ) ≤
          Cstep * W.X / frequencyCutoff W ∧
        (blocks e.1).Nodup ∧
        (∀ block ∈ blocks e.1,
          0 ≤ interiorComponentWeight (W.excess e) (blocks e.1) block) ∧
        (∀ block ∈ blocks e.1,
          interiorComponentWeight (W.excess e) (blocks e.1) block ≤
            32 * Nat.ceil ((W.structural.B + 1) *
              selectedLogLength trimmed e.1)) ∧
        ((blocks e.1).map (fun block =>
          interiorComponentWeight (W.excess e) (blocks e.1) block)).sum =
            W.excess e ∧
        (Z0 : ℝ) / 32 < selectedMeanGapBand trimmed e.1 ∧
        (cspan / 2) * (2 : ℝ) ^
            (selectedMeanGapBand trimmed e.1) ≤
          selectedDenominatorBand trimmed e.1 := by
    change LongInteriorPair W Z0 e at he
    rcases hstableTrimmed e he with
      ⟨data, hselected, hvalid, hspan, hcount, hcountLe, hstep⟩
    have hell : selectedLogLength trimmed e.1 ≤ W.L + gap.Cgap :=
      selectedLogLength_le_of_step Q gap.Cgap hQ Cstep W Z0 e.1 trimmed
        data hselected hvalid hstep hfrequency
    have hreserve :
        4 * (selectedForwardLength W gap e.1 +
          Nat.ceil ((W.structural.B + 1) * selectedLogLength trimmed e.1)) ≤
            data.segment.span :=
      selectedCoverReserve_le_segment W gap trimmed e data Z0
        W.entropy.kappa W.entropy.kappa_pos hlevel hcutoff hm he.1.2
        hspan hell
    have hsparse := selectedInteriorBlocks_sparseCover Q hQ W Z0 trimmed gap e
      data hselected hvalid hspan hcount hreserve
    dsimp only at hsparse
    have hblocksEq : blocks e.1 = selectedInteriorBlocks W trimmed gap e.1 := rfl
    rw [hblocksEq]
    let Z := selectedMeanGapBand trimmed e.1
    let D := selectedDenominatorBand trimmed e.1
    have hsegment : data.segment.Valid Q := hvalid.2.2.2.2.1
    have hcountPos : 0 < data.segment.gapCount := by omega
    have hcountSpan : data.segment.gapCount ≤ data.segment.span := by
      rw [OddDenominatorSegment.gapCount, OddDenominatorSegment.span,
        GapWord.span]
      exact List.length_le_sum_of_one_le data.segment.gaps fun g hg =>
        hsegment.2.1 g hg
    have hmean := meanGapBand_bounds hcountPos hcountSpan
    have hZeq : Z = meanGapBand data.segment.span data.segment.gapCount := by
      simp [Z, selectedMeanGapBand, hselected]
    have hmeanLower : Z * data.segment.gapCount ≤ data.segment.span := by
      simpa only [hZeq] using hmean.2.1
    have hmeanUpper : data.segment.span <
        2 * Z * data.segment.gapCount := by
      simpa only [hZeq] using hmean.2.2
    have hZcut : (Z0 : ℝ) / 32 < Z :=
      meanGapBand_above_cutoff (m := W.m) (Z0 := Z0)
        (y := W.excess e) (Z := Z) (by simp [WindowSystem.m]) hcountLe
        he.1.2 hspan hmeanUpper
    have hDeq : D = dyadicFloorBand data.segment.q := by
      simp [D, selectedDenominatorBand, hselected]
    have hqband : data.segment.q < 2 * D := by
      rw [hDeq]
      exact dyadicFloorBand_lt_two_mul _
    have hZavg : (Z : ℝ) ≤
        (data.segment.span : ℝ) / data.segment.gapCount := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < data.segment.gapCount)]
      exact_mod_cast hmeanLower
    have hDlower := denominatorBand_lower
      (cspan := cspan) (Z := Z) (D := D)
      hcspan hZavg (hdenSpan data.segment hsegment hcountPos) hqband
    refine ⟨data, hselected, hvalid, hspan, hcount, hcountLe, hstep,
      hsparse.2.1, hsparse.2.2.1, hsparse.2.2.2.1, hsparse.2.2.2.2,
      ?_, ?_⟩
    · simpa only [Z] using hZcut
    · simpa only [D, Z] using hDlower
  have hblocks_nodup : ∀ k, (blocks k).Nodup := by
    intro k
    by_cases hk : ActiveAnchor k
    · rcases hk with ⟨e, heFirst, he⟩
      have heMem : e ∈ interiorPairs W Z0 := by exact he
      rcases pairSpec e heMem with ⟨data, hselected, hvalid, hspan,
        hcount, hcountLe, hstep, hnodup, hrest⟩
      simpa only [heFirst] using hnodup
    · simp [blocks, selectedInteriorBlocks, trimmed, hk]
  let labels : WindowThreshold → Finset LowGapBlock := fun e =>
    if e ∈ interiorPairs W Z0 then (blocks e.1).toFinset else ∅
  let weight : WindowThreshold → LowGapBlock → ℝ := fun e block =>
    interiorComponentWeight (W.excess e) (blocks e.1) block
  let refinement : InteriorRefinement W Z0 :=
    { selection := trimmed
      selection_valid := by simpa only [hden] using htrimmed_valid
      gap := gap
      Cstep := Cstep
      Cstep_pos := hCstep
      ell := selectedLogLength trimmed
      meanGap := selectedMeanGapBand trimmed
      forward := selectedForwardLength W gap
      denominatorBand := selectedDenominatorBand trimmed
      blocks := blocks
      denominatorBand_pos := selectedDenominatorBand_pos trimmed
      meanGap_pos := selectedMeanGapBand_pos trimmed
      ell_eq := selectedLogLength_eq trimmed
      forward_eq := selectedForwardLength_eq W gap
      selected_data := by
        intro e he
        rcases pairSpec e he with ⟨data, hselected, hvalid, hrest⟩
        refine ⟨data, hselected, by simpa only [hden] using hvalid, ?_⟩
        exact selectedInteriorBlocks_eq_of_selected W trimmed gap e.1 data
          hselected
      blocks_nodup := hblocks_nodup
      source_valid := by
        intro e he block hblock
        rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
          hcountLe, hstep, hrest⟩
        have heLong : LongInteriorPair W Z0 e := he
        have hell : selectedLogLength trimmed e.1 ≤ W.L + gap.Cgap :=
          selectedLogLength_le_of_step Q gap.Cgap hQ Cstep W Z0 e.1 trimmed
            data hselected hvalid hstep hfrequency
        have hblock' : block ∈ selectedBlocks data.segment W.structural.B
            (selectedLogLength trimmed e.1) (selectedMeanGapBand trimmed e.1)
            (reconstructionForwardLength W gap.Cgap) := by
          have hblocksEq := selectedInteriorBlocks_eq_of_selected W trimmed gap
            e.1 data hselected
          change block ∈ selectedInteriorBlocks W trimmed gap e.1 at hblock
          rw [hblocksEq] at hblock
          simpa only [selectedForwardLength_eq] using hblock
        simpa only [hden] using
          selectedBlock_isSpatialEncodingSource Q gap.Cgap hQ W Z0 e.1
            trimmed data Cstep block hden hselected hvalid hstep hell
            (le_max_left _ _ |>.trans hlevel) hblock'
      labels := labels
      weight := weight
      labels_eq := by
        intro e he
        simp [labels, he]
      weight_eq := by
        intro e he block hblock
        rfl
      weight_nonneg := by
        intro e block
        dsimp only [weight]
        unfold interiorComponentWeight
        have hexcess : 0 ≤ W.excess e := by
          unfold WindowSystem.excess
          positivity
        positivity
      sums_to_excess := by
        intro e he
        rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
          hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hrest⟩
        dsimp only [labels, weight]
        rw [if_pos he]
        rw [List.sum_toFinset _ hnodup]
        exact hsum
      outside_zero := by
        intro e he
        simp [labels, he] }
  refine ⟨refinement, ?_⟩
  refine {
    cBand_pos := div_pos hcspan (by norm_num)
    Cstep_eq := rfl
    gap_Cgap_eq := rfl
    selected_quantitative := ?_
    component_bound := ?_
    component_sum := ?_
    meanGap_cutoff := ?_
    denominator_lower := ?_
    denominator_isPow := ?_
    meanGap_isPow := ?_
    candidate := ?_ }
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hrest⟩
    exact ⟨data, hselected, by simpa only [hden] using hvalid,
      hspan, hcount, hcountLe, hstep⟩
  · intro e he block hblock
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hbound block hblock
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hsum
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hZcut
  · intro e he
    rcases pairSpec e he with ⟨data, hselected, hvalid, hspan, hcount,
      hcountLe, hstep, hnodup, hnonneg, hbound, hsum, hZcut, hDlower⟩
    exact hDlower
  · intro k
    simp only [refinement]
    unfold selectedDenominatorBand
    split
    · exact ⟨0, by simp⟩
    · exact dyadicFloorBand_isPow _
  · intro k
    simp only [refinement]
    unfold selectedMeanGapBand meanGapBand
    split
    · exact ⟨0, by simp⟩
    · exact dyadicFloorBand_isPow _
  · intro e he block hblock
    have hsource := refinement.source_valid e he block hblock
    rcases hsource with ⟨data, t, hreconstructed, hparameter⟩
    exact hreconstructed.2.2.2.2.2.2.1

theorem eventually_exists_interiorRefinement_certificate
    (context : FixedScaleContext) :
    ∃ gap : GapParams context.Q, ∃ Cstep : ℝ, 0 < Cstep ∧
      ∃ Zmin : ℕ, ∃ cBand : ℝ, 0 < cBand ∧
        ∀ Z0 : ℕ, Zmin ≤ Z0 →
          ∀ F : ScaleFamily, F.MatchesContext context →
            ∀ᶠ L : ℕ in atTop,
              ∃ refinement : InteriorRefinement (F.system L) Z0,
                InteriorRefinementUniformFacts refinement cBand Cstep gap.Cgap := by
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨Cstep, hCstep, Zstable, hstable⟩ :=
    lem_stable_segment context gap
  obtain ⟨cspan, hcspan, hdenSpan⟩ :=
    lem_denominator_span context.Q context.Q_pos
  let Zmin := max Zstable
    (strictCoverCutoff context.structural.B context.entropy.kappa)
  refine ⟨gap, Cstep, hCstep, Zmin, cspan / 2,
    div_pos hcspan (by norm_num), ?_⟩
  intro Z0 hZ0 F hF
  have hZstable : Zstable ≤ Z0 :=
    (le_max_left Zstable
      (strictCoverCutoff context.structural.B context.entropy.kappa)).trans hZ0
  have hZcover :
      strictCoverCutoff context.structural.B context.entropy.kappa ≤ Z0 :=
    (le_max_right Zstable
      (strictCoverCutoff context.structural.B context.entropy.kappa)).trans hZ0
  have hstableEvent := hstable Z0 hZstable F hF
  have hfrequencyTop := frequencyCutoff_tendsto context F hF
  have hfrequencyEvent : ∀ᶠ L : ℕ in atTop,
      4 * (context.Q : ℝ) * Cstep ≤ frequencyCutoff (F.system L) := by
    filter_upwards [tendsto_atTop.1 hfrequencyTop
      (4 * (context.Q : ℝ) * Cstep + 1)] with L hL
    linarith
  filter_upwards [hstableEvent, hfrequencyEvent,
      eventually_ge_atTop (max 1 gap.Cgap)] with
      L hselection hfrequency hlevel
  rcases hselection with ⟨selection, hselectionValid, hstableSelection⟩
  have hden : (F.system L).rational.eta.den = context.Q := by
    rw [F.rational_eq]
    exact hF.1
  let gapW : GapParams (F.system L).rational.eta.den :=
    { Cgap := gap.Cgap
      x0 := gap.x0
      bound := by
        intro R hR
        exact gap.bound R (hR.trans hden) }
  have hlevelW : max 1 gapW.Cgap ≤ (F.system L).L := by
    rw [F.level_eq]
    exact hlevel
  have hcutoffW :
      strictCoverCutoff (F.system L).structural.B
          (F.system L).entropy.kappa ≤ Z0 := by
    rw [F.structural_eq, hF.2.1, F.entropy_eq, hF.2.2.1]
    exact hZcover
  have hoffset : (F.system L).s =
      Nat.floor (context.entropy.kappa * (L : ℝ)) := by
    rw [F.offset_eq, hF.2.2.1]
  have hmContext : context.entropy.kappa * (L : ℝ) <
      ((F.system L).m : ℝ) := by
    rw [WindowSystem.m, hoffset]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (context.entropy.kappa * (L : ℝ)))
  have hmW : (F.system L).entropy.kappa * (F.system L).L <
      (F.system L).m := by
    rw [F.entropy_eq, hF.2.2.1, F.level_eq]
    exact hmContext
  exact interiorRefinement_exists_of_stable context.Q context.Q_pos
    (F.system L) Z0 gapW Cstep hCstep selection hden hselectionValid
    hstableSelection hfrequency hlevelW hcutoffW hmW cspan hcspan hdenSpan

/-- Refined interior mass with counting over finite labels inside the same
window-threshold integral. -/
def refinedInteriorMass {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : ℝ≥0∞ :=
  ∫⁻ e in interiorPairs W Z0,
    ENNReal.ofReal
      (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b)
    ∂windowThresholdMeasure

theorem refinedInteriorMass_eq_mass_strict {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) :
    refinedInteriorMass refinement = mass (interiorPairs W Z0) W.excess := by
  unfold refinedInteriorMass mass
  apply setLIntegral_congr_fun (measurableSet_interiorPairs_strict W Z0)
  intro e he
  apply congrArg ENNReal.ofReal
  have hsum := refinement.sums_to_excess e he
  calc
    (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b) =
        ∑ b ∈ refinement.labels e, refinement.weight e b := by
          rw [refinement.labels_eq e he]
          apply Finset.sum_congr rfl
          intro b hb
          symm
          apply refinement.weight_eq e he b
          simpa [refinement.labels_eq e he] using hb
    _ = W.excess e := hsum

theorem lintegral_anchorCharge_pairSet
    (W : WindowSystem) (charge : ℕ → ℝ)
    (hcharge : ∀ k ∈ W.anchors, 0 ≤ charge k) :
    (∫⁻ e in W.pairSet, ENNReal.ofReal (charge e.1)
        ∂windowThresholdMeasure) =
      ENNReal.ofReal
        ((∑ k ∈ W.anchors, charge k) * thresholdLength W) := by
  rw [WindowSystem.pairSet_eq_prod]
  unfold windowThresholdMeasure
  change (∫⁻ e : WindowThreshold,
      ENNReal.ofReal (charge e.1) ∂
        (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds)) = _
  have hmeasure :
      (Measure.count.prod volume).restrict
          (Set.prod (W.anchors : Set ℕ) W.thresholds) =
        (Measure.count.restrict (W.anchors : Set ℕ)).prod
          (volume.restrict W.thresholds) :=
    (Measure.prod_restrict (μ := Measure.count) (ν := volume)
      (W.anchors : Set ℕ) W.thresholds).symm
  rw [hmeasure, MeasureTheory.lintegral_prod_symm]
  · have hsum :
        (∑ k ∈ W.anchors, ENNReal.ofReal (charge k)) =
          ENNReal.ofReal (∑ k ∈ W.anchors, charge k) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro k hk
      exact hcharge k hk
    simp_rw [MeasureTheory.lintegral_finset]
    simp
    have hsumNonneg : 0 ≤ ∑ k ∈ W.anchors, charge k :=
      Finset.sum_nonneg fun k hk => hcharge k hk
    have hlength : 0 ≤ thresholdLength W := by
      unfold thresholdLength
      exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
    rw [hsum, WindowSystem.thresholds, thresholdInterval, Real.volume_Icc]
    have hdiff :
        2 * (W.L : ℝ) + W.structural.C0 + W.structural.cI * W.L -
            (2 * (W.L : ℝ) + W.structural.C0) = thresholdLength W := by
      unfold thresholdLength
      ring
    rw [hdiff]
    rw [← ENNReal.ofReal_mul hsumNonneg]
  · exact ((measurable_of_countable charge).comp measurable_fst).ennreal_ofReal.aemeasurable

theorem mass_le_anchorCharge
    (W : WindowSystem) (E : Set WindowThreshold) (hE : E ⊆ W.pairSet)
    (charge : ℕ → ℝ) (hcharge : ∀ k ∈ W.anchors, 0 ≤ charge k)
    (hbound : ∀ e ∈ E, W.excess e ≤ charge e.1) :
    mass E W.excess ≤
      ENNReal.ofReal
        ((∑ k ∈ W.anchors, charge k) * thresholdLength W) := by
  unfold mass
  calc
    (∫⁻ e in E, ENNReal.ofReal (W.excess e) ∂windowThresholdMeasure) ≤
        ∫⁻ e in E, ENNReal.ofReal (charge e.1) ∂windowThresholdMeasure := by
      apply setLIntegral_mono
      · exact ((measurable_of_countable charge).comp measurable_fst).ennreal_ofReal
      · intro e he
        exact ENNReal.ofReal_le_ofReal (hbound e he)
    _ ≤ ∫⁻ e in W.pairSet,
        ENNReal.ofReal (charge e.1) ∂windowThresholdMeasure :=
      lintegral_mono_set hE
    _ = ENNReal.ofReal
        ((∑ k ∈ W.anchors, charge k) * thresholdLength W) :=
      lintegral_anchorCharge_pairSet W charge hcharge

def refinementAnchorCharge {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (blockBound : ℕ → LowGapBlock → ℝ) (k : ℕ) : ℝ :=
  ∑ b ∈ (refinement.blocks k).toFinset, blockBound k b

theorem interiorPairsMass_le_refinementAnchorCharge
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (blockBound : ℕ → LowGapBlock → ℝ)
    (hboundNonneg : ∀ k b, 0 ≤ blockBound k b)
    (hcomponentSum : ∀ e, e ∈ interiorPairs W Z0 →
      (refinement.blocks e.1 |>.map fun b =>
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b).sum =
          W.excess e)
    (hcomponentBound : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          blockBound e.1 b) :
    interiorPairsMass W Z0 ≤
      (∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) *
        thresholdLength W := by
  let charge := refinementAnchorCharge refinement blockBound
  have hcharge : ∀ k ∈ W.anchors, 0 ≤ charge k := by
    intro k _hk
    apply Finset.sum_nonneg
    intro b hb
    exact hboundNonneg k b
  have hpoint : ∀ e ∈ interiorPairs W Z0, W.excess e ≤ charge e.1 := by
    intro e he
    rw [← hcomponentSum e he]
    have hlist := List.sum_toFinset
      (fun b => interiorComponentWeight (W.excess e) (refinement.blocks e.1) b)
      (refinement.blocks_nodup e.1)
    rw [← hlist]
    apply Finset.sum_le_sum
    intro b hb
    apply hcomponentBound e he b
    simpa using hb
  have hmass := mass_le_anchorCharge W (interiorPairs W Z0)
    (interiorPairs_subset_pairSet W Z0) charge hcharge hpoint
  have hleftTop : mass (interiorPairs W Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (interiorPairs W Z0)
      (interiorPairs_subset_pairSet W Z0)).ne_top
  have hsumNonneg : 0 ≤
      (∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) := by
    apply Finset.sum_nonneg
    intro k hk
    exact hcharge k hk
  have hlength : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrightNonneg : 0 ≤
      (∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) *
        thresholdLength W := mul_nonneg hsumNonneg hlength
  have hrightTop : ENNReal.ofReal
      ((∑ k ∈ W.anchors, refinementAnchorCharge refinement blockBound k) *
        thresholdLength W) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hto := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  change (mass (interiorPairs W Z0) W.excess).toReal ≤ _
  simpa [interiorPairsMass, ENNReal.toReal_ofReal hrightNonneg] using hto

theorem finite_ncard_real_le_card_mul_of_bounded_fibres
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Set α) (t : Set β) (hs : s.Finite) (ht : t.Finite)
    (f : α → β) (M : ℝ) (_hM : 0 ≤ M)
    (hmap : ∀ x ∈ s, f x ∈ t)
    (hfibre : ∀ y ∈ t, (s ∩ f ⁻¹' {y}).Finite)
    (hbound : ∀ y ∈ t, ((s ∩ f ⁻¹' {y}).ncard : ℝ) ≤ M) :
    (s.ncard : ℝ) ≤ (t.ncard : ℝ) * M := by
  classical
  let fibres : β → Finset α := fun y =>
    if hy : y ∈ t then (hfibre y hy).toFinset else ∅
  have hsub : hs.toFinset ⊆ ht.toFinset.biUnion fibres := by
    intro x hx
    have hxs : x ∈ s := hs.mem_toFinset.mp hx
    have hfx : f x ∈ t := hmap x hxs
    rw [Finset.mem_biUnion]
    refine ⟨f x, ht.mem_toFinset.mpr hfx, ?_⟩
    simp only [fibres, dif_pos hfx]
    apply (hfibre (f x) hfx).mem_toFinset.mpr
    exact ⟨hxs, rfl⟩
  have hcardNat : hs.toFinset.card ≤
      (ht.toFinset.biUnion fibres).card := Finset.card_le_card hsub
  calc
    (s.ncard : ℝ) = (hs.toFinset.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card s hs]
    _ ≤ ((ht.toFinset.biUnion fibres).card : ℕ) := by exact_mod_cast hcardNat
    _ ≤ (∑ y ∈ ht.toFinset, (fibres y).card : ℕ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := ht.toFinset) (t := fibres))
    _ = ∑ y ∈ ht.toFinset, ((fibres y).card : ℝ) := by norm_num
    _ ≤ ∑ _y ∈ ht.toFinset, M := by
      apply Finset.sum_le_sum
      intro y hy
      have hyt : y ∈ t := ht.mem_toFinset.mp hy
      simp only [fibres, dif_pos hyt]
      rw [← Set.ncard_eq_toFinset_card (s ∩ f ⁻¹' {y}) (hfibre y hyt)]
      exact hbound y hyt
    _ = (ht.toFinset.card : ℝ) * M := by simp
    _ = (t.ncard : ℝ) * M := by rw [Set.ncard_eq_toFinset_card t ht]

noncomputable def interiorAnchorFinset (W : WindowSystem) (Z0 : ℕ) : Finset ℕ :=
  by
    classical
    exact W.anchors.filter fun k => ∃ T : ℝ, (k, T) ∈ interiorPairs W Z0

noncomputable def refinementSourceFinset {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : Finset (ℕ × LowGapBlock) :=
  by
    classical
    exact (interiorAnchorFinset W Z0).biUnion fun k =>
      (refinement.blocks k).toFinset.image fun b => (k, b)

noncomputable def refinementSourceBandFinset {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (D Z : ℕ) :
    Finset (ℕ × LowGapBlock) :=
  by
    classical
    exact (refinementSourceFinset refinement).filter fun kb =>
      refinement.denominatorBand kb.1 = D ∧ refinement.meanGap kb.1 = Z

theorem mem_refinementSourceFinset_iff
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0)
    (kb : ℕ × LowGapBlock) :
    kb ∈ refinementSourceFinset refinement ↔
      kb.1 ∈ interiorAnchorFinset W Z0 ∧ kb.2 ∈ refinement.blocks kb.1 := by
  classical
  constructor
  · intro hkb
    rw [refinementSourceFinset, Finset.mem_biUnion] at hkb
    rcases hkb with ⟨k, hk, hkb⟩
    rw [Finset.mem_image] at hkb
    rcases hkb with ⟨b, hb, hpair⟩
    have hkEq : k = kb.1 := congrArg Prod.fst hpair
    have hbEq : b = kb.2 := congrArg Prod.snd hpair
    subst k
    subst b
    exact ⟨hk, by simpa using hb⟩
  · rintro ⟨hk, hb⟩
    rw [refinementSourceFinset, Finset.mem_biUnion]
    refine ⟨kb.1, hk, ?_⟩
    rw [Finset.mem_image]
    exact ⟨kb.2, by simpa using hb, Prod.ext rfl rfl⟩

theorem refinementSourceBand_card_real_le
    {W : WindowSystem} {Z0 D Z : ℕ} (M : ℝ) (hM : 0 ≤ M)
    (refinement : InteriorRefinement W Z0)
    (hcandidates : (encodingCandidates D Z W.structural.B).Finite)
    (hfibres : ∀ σ ∈ encodingCandidates D Z W.structural.B,
      (spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
        ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤ M) :
    ((refinementSourceBandFinset refinement D Z).card : ℝ) ≤
      ((encodingCandidates D Z W.structural.B).ncard : ℝ) * M := by
  classical
  let s : Set (ℕ × LowGapBlock) :=
    (refinementSourceBandFinset refinement D Z : Finset (ℕ × LowGapBlock))
  let t : Set BlockEncoding := encodingCandidates D Z W.structural.B
  let f : (ℕ × LowGapBlock) → BlockEncoding := fun kb => encodeBlock D Z kb.2
  have hs : s.Finite := (refinementSourceBandFinset refinement D Z).finite_toSet
  have hmap : ∀ kb ∈ s, f kb ∈ t := by
    intro kb hkb
    change kb ∈ refinementSourceBandFinset refinement D Z at hkb
    rw [refinementSourceBandFinset, Finset.mem_filter] at hkb
    rcases hkb with ⟨hsourceFinset, hD, hZ⟩
    have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsourceFinset
    rw [interiorAnchorFinset, Finset.mem_filter] at hsourceData
    rcases hsourceData with ⟨⟨_hkAnchor, T, he⟩, hb⟩
    have hsource := refinement.source_valid (kb.1, T) he kb.2 hb
    change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
      W.structural.B refinement.Cstep W Z0 refinement.selection
        (encodeBlock (refinement.denominatorBand kb.1)
          (refinement.meanGap kb.1) kb.2) kb at hsource
    rcases hsource with ⟨sourceData, tsource, hrec, hparameter⟩
    change encodeBlock D Z kb.2 ∈ encodingCandidates D Z W.structural.B
    simpa [hD, hZ, encodeBlock] using hrec.2.2.2.2.2.2.1
  have hfibreSubset : ∀ σ ∈ t, (s ∩ f ⁻¹' {σ}) ⊆
      spatialPreimage W.rational.eta.den refinement.gap.Cgap
        W.structural.B refinement.Cstep W Z0 refinement.selection σ := by
    intro σ hσ kb hkb
    rcases hkb with ⟨hkbS, hencode⟩
    change kb ∈ refinementSourceBandFinset refinement D Z at hkbS
    rw [refinementSourceBandFinset, Finset.mem_filter] at hkbS
    rcases hkbS with ⟨hsourceFinset, hD, hZ⟩
    have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsourceFinset
    rw [interiorAnchorFinset, Finset.mem_filter] at hsourceData
    rcases hsourceData with ⟨⟨_hkAnchor, T, he⟩, hb⟩
    have hsource := refinement.source_valid (kb.1, T) he kb.2 hb
    change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
      W.structural.B refinement.Cstep W Z0 refinement.selection
        (encodeBlock (refinement.denominatorBand kb.1)
          (refinement.meanGap kb.1) kb.2) kb at hsource
    change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
      W.structural.B refinement.Cstep W Z0 refinement.selection σ kb
    have hencode' : encodeBlock D Z kb.2 = σ := by simpa [f] using hencode
    simpa [hD, hZ, hencode'] using hsource
  have hfibreFinite : ∀ σ ∈ t, (s ∩ f ⁻¹' {σ}).Finite := by
    intro σ hσ
    exact (hfibres σ hσ).1.subset (hfibreSubset σ hσ)
  have hfibreBound : ∀ σ ∈ t, ((s ∩ f ⁻¹' {σ}).ncard : ℝ) ≤ M := by
    intro σ hσ
    calc
      ((s ∩ f ⁻¹' {σ}).ncard : ℝ) ≤
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard (hfibreSubset σ hσ) (hfibres σ hσ).1
      _ ≤ M := (hfibres σ hσ).2
  have hcard := finite_ncard_real_le_card_mul_of_bounded_fibres
    s t hs hcandidates f M hM hmap hfibreFinite hfibreBound
  simpa [s, t] using hcard

def strictAnchorBlockCap {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (k : ℕ) : ℝ :=
  32 * Nat.ceil ((W.structural.B + 1) * refinement.ell k)

def strictBandBlockCap (W : WindowSystem) (D : ℕ) : ℝ :=
  32 * Nat.ceil ((W.structural.B + 1) *
    Nat.ceil (Real.logb 2 (4 * D)))

noncomputable def refinementBandKeys {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : Finset (ℕ × ℕ) :=
  (refinementSourceFinset refinement).image fun kb =>
    (refinement.denominatorBand kb.1, refinement.meanGap kb.1)

theorem interiorAnchorFinset_subset_anchors (W : WindowSystem) (Z0 : ℕ) :
    interiorAnchorFinset W Z0 ⊆ W.anchors := by
  classical
  intro k hk
  rw [interiorAnchorFinset, Finset.mem_filter] at hk
  exact hk.1

theorem sum_refinementSourceFinset
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0)
    (f : ℕ × LowGapBlock → ℝ) :
    (∑ kb ∈ refinementSourceFinset refinement, f kb) =
      ∑ k ∈ interiorAnchorFinset W Z0,
        ∑ b ∈ (refinement.blocks k).toFinset, f (k, b) := by
  classical
  have hdisjoint : Set.PairwiseDisjoint
      (interiorAnchorFinset W Z0 : Set ℕ)
      (fun k => (refinement.blocks k).toFinset.image fun b => (k, b)) := by
    intro k hk k' hk' hne
    change Disjoint
      ((refinement.blocks k).toFinset.image fun b => (k, b))
      ((refinement.blocks k').toFinset.image fun b => (k', b))
    rw [Finset.disjoint_left]
    intro kb hkb hkb'
    rcases Finset.mem_image.mp hkb with ⟨b, hb, rfl⟩
    rcases Finset.mem_image.mp hkb' with ⟨b', hb', hpair⟩
    have hfirst := congrArg Prod.fst hpair
    exact hne (by simpa using hfirst.symm)
  rw [refinementSourceFinset, Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_image]
  intro b hb b' hb' hpair
  exact congrArg Prod.snd hpair

theorem anchorCharge_sum_eq_sourceCap_sum
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0) :
    (∑ k ∈ W.anchors,
        refinementAnchorCharge refinement
          (fun k _ => if k ∈ interiorAnchorFinset W Z0 then
            strictAnchorBlockCap refinement k else 0) k) =
      ∑ kb ∈ refinementSourceFinset refinement,
        strictAnchorBlockCap refinement kb.1 := by
  classical
  let I := interiorAnchorFinset W Z0
  let cap : ℕ → ℝ := strictAnchorBlockCap refinement
  have hsubset : I ⊆ W.anchors := interiorAnchorFinset_subset_anchors W Z0
  have houter :
      (∑ k ∈ W.anchors,
          refinementAnchorCharge refinement
            (fun k _ => if k ∈ I then cap k else 0) k) =
        ∑ k ∈ I, ∑ b ∈ (refinement.blocks k).toFinset, cap k := by
    calc
      (∑ k ∈ W.anchors,
          refinementAnchorCharge refinement
            (fun k _ => if k ∈ I then cap k else 0) k) =
          ∑ k ∈ W.anchors,
            if k ∈ I then
              ∑ b ∈ (refinement.blocks k).toFinset, cap k
            else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hkI : k ∈ I <;>
                simp [refinementAnchorCharge, hkI]
      _ = ∑ k ∈ I, ∑ b ∈ (refinement.blocks k).toFinset, cap k := by
        calc
          (∑ k ∈ W.anchors,
              if k ∈ I then
                ∑ b ∈ (refinement.blocks k).toFinset, cap k
              else 0) =
              ∑ k ∈ I,
                if k ∈ I then
                  ∑ b ∈ (refinement.blocks k).toFinset, cap k
                else 0 := by
                  symm
                  apply Finset.sum_subset hsubset
                  intro k hkAnchor hkNotI
                  simp [hkNotI]
          _ = ∑ k ∈ I,
              ∑ b ∈ (refinement.blocks k).toFinset, cap k := by
                apply Finset.sum_congr rfl
                intro k hkI
                simp [hkI]
  rw [houter]
  rw [sum_refinementSourceFinset refinement]

theorem sourceCap_sum_eq_bandCap_sum
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0) :
    (∑ kb ∈ refinementSourceFinset refinement,
        strictAnchorBlockCap refinement kb.1) =
      ∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1 := by
  classical
  let source := refinementSourceFinset refinement
  let key : (ℕ × LowGapBlock) → ℕ × ℕ := fun kb =>
    (refinement.denominatorBand kb.1, refinement.meanGap kb.1)
  let keys := refinementBandKeys refinement
  have hmaps : ∀ kb ∈ source, key kb ∈ keys := by
    intro kb hkb
    exact Finset.mem_image.mpr ⟨kb, hkb, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun kb => strictAnchorBlockCap refinement kb.1)
  rw [← hfiber]
  have hbandFinset : ∀ keyValue : ℕ × ℕ,
      refinementSourceBandFinset refinement keyValue.1 keyValue.2 =
        source.filter fun kb => key kb = keyValue := by
    intro keyValue
    ext kb
    simp [refinementSourceBandFinset, source, key, Prod.ext_iff]
  change (∑ keyValue ∈ keys,
      ∑ kb ∈ source with key kb = keyValue,
        strictAnchorBlockCap refinement kb.1) =
    ∑ keyValue ∈ keys,
      ((refinementSourceBandFinset refinement
        keyValue.1 keyValue.2).card : ℝ) *
        strictBandBlockCap W keyValue.1
  apply Finset.sum_congr rfl
  intro keyValue hkeyValue
  rw [hbandFinset keyValue]
  calc
    (∑ kb ∈ source with key kb = keyValue,
        strictAnchorBlockCap refinement kb.1) =
        ∑ _kb ∈ source.filter (fun kb => key kb = keyValue),
          strictBandBlockCap W keyValue.1 := by
            apply Finset.sum_congr rfl
            intro kb hkb
            have hkey : key kb = keyValue := (Finset.mem_filter.mp hkb).2
            have hD : refinement.denominatorBand kb.1 = keyValue.1 :=
              congrArg Prod.fst hkey
            simp only [strictAnchorBlockCap, strictBandBlockCap]
            rw [refinement.ell_eq kb.1, hD]
    _ = ((source.filter fun kb => key kb = keyValue).card : ℝ) *
          strictBandBlockCap W keyValue.1 := by simp

theorem strictLogLength_pos {D : ℕ} (hD : 0 < D) :
    0 < Nat.ceil (Real.logb 2 (4 * D)) := by
  have hellEq : Nat.ceil (Real.logb 2 (4 * D)) =
      Nat.clog 2 (4 * D) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      Real.natCeil_logb_natCast 2 (4 * D)
  rw [hellEq, Nat.lt_clog_iff_pow_lt (by omega)]
  simp
  omega

theorem strictBandBlockCap_le (W : WindowSystem) {D : ℕ} (hD : 0 < D) :
    strictBandBlockCap W D ≤
      32 * (W.structural.B + 2) *
        Nat.ceil (Real.logb 2 (4 * D)) := by
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hellPos : 0 < ell := strictLogLength_pos hD
  have hBnonneg : 0 ≤ W.structural.B + 1 := by
    linarith [W.structural.B_gt]
  have hargNonneg : 0 ≤ (W.structural.B + 1) * (ell : ℝ) :=
    mul_nonneg hBnonneg (Nat.cast_nonneg _)
  have hceil : (Nat.ceil ((W.structural.B + 1) * (ell : ℝ)) : ℝ) ≤
      (W.structural.B + 2) * ell := by
    have hlt := Nat.ceil_lt_add_one hargNonneg
    have hone : (1 : ℝ) ≤ ell := by exact_mod_cast hellPos
    nlinarith
  unfold strictBandBlockCap
  change 32 * (Nat.ceil ((W.structural.B + 1) * (ell : ℝ)) : ℝ) ≤
    32 * (W.structural.B + 2) * ell
  nlinarith

theorem fixedBandCharge_le_sqrt
    {W : WindowSystem} {Z0 D Z : ℕ} (hD : 0 < D)
    (refinement : InteriorRefinement W Z0)
    (hcandidates : (encodingCandidates D Z W.structural.B).Finite)
    (hentropy :
      ((encodingCandidates D Z W.structural.B).ncard : ℝ) *
        Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D)
    (hfibres : ∀ σ ∈ encodingCandidates D Z W.structural.B,
      (spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
        ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
          W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
          (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X / D) :
    ((refinementSourceBandFinset refinement D Z).card : ℝ) *
        strictBandBlockCap W D ≤
      32 * (W.structural.B + 2) *
        ((W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X) /
          Real.sqrt D := by
  let ell : ℝ := Nat.ceil (Real.logb 2 (4 * D))
  let N : ℝ := (encodingCandidates D Z W.structural.B).ncard
  let C : ℝ :=
    (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X
  let K : ℝ := 32 * (W.structural.B + 2) * C
  have hC : 0 ≤ C := by
    dsimp [C]
    have hstep : 0 ≤ refinement.Cstep + 4 := by
      linarith [refinement.Cstep_pos]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    have hB : 0 ≤ W.structural.B + 2 := by
      linarith [W.structural.B_gt]
    positivity
  have hDreal : (0 : ℝ) < D := by positivity
  have hsqrtPos : 0 < Real.sqrt D := Real.sqrt_pos.2 hDreal
  have hcard : ((refinementSourceBandFinset refinement D Z).card : ℝ) ≤
      N * (C / D) := by
    apply refinementSourceBand_card_real_le (C / D)
      (div_nonneg hC hDreal.le) refinement hcandidates
    intro σ hσ
    simpa [C] using hfibres σ hσ
  have hcap : strictBandBlockCap W D ≤
      32 * (W.structural.B + 2) * ell := by
    simpa [ell] using strictBandBlockCap_le W hD
  have hcapNonneg : 0 ≤ strictBandBlockCap W D := by
    unfold strictBandBlockCap
    positivity
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have hellNonneg : 0 ≤ ell := by
    dsimp [ell]
    positivity
  have hupperNonneg : 0 ≤ 32 * (W.structural.B + 2) * ell := by
    have hB : 0 ≤ W.structural.B + 2 := by
      linarith [W.structural.B_gt]
    positivity
  have hNell : N * ell ≤ Real.sqrt D := by
    simpa [N, ell] using hentropy
  have hsq : Real.sqrt D * Real.sqrt D = (D : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ D by positivity)]
  calc
    ((refinementSourceBandFinset refinement D Z).card : ℝ) *
          strictBandBlockCap W D ≤
        (N * (C / D)) * (32 * (W.structural.B + 2) * ell) := by
      exact mul_le_mul hcard hcap hcapNonneg
        (mul_nonneg hNnonneg (div_nonneg hC hDreal.le))
    _ = K * (N * ell) / D := by
      dsimp [K]
      ring
    _ ≤ K * Real.sqrt D / D := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNell hK) hDreal.le
    _ = K / Real.sqrt D := by
      calc
        K * Real.sqrt D / (D : ℝ) =
            K * Real.sqrt D / (Real.sqrt D * Real.sqrt D) := by
          exact congrArg (fun x : ℝ => K * Real.sqrt D / x) hsq.symm
        _ = K / Real.sqrt D := by field_simp
    _ = 32 * (W.structural.B + 2) *
        ((W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X) /
          Real.sqrt D := by rfl

theorem InteriorRefinement.component_sum_eq
    {W : WindowSystem} {Z0 : ℕ} (refinement : InteriorRefinement W Z0)
    (e : WindowThreshold) (he : e ∈ interiorPairs W Z0) :
    (refinement.blocks e.1 |>.map fun b =>
      interiorComponentWeight (W.excess e) (refinement.blocks e.1) b).sum =
        W.excess e := by
  rw [← List.sum_toFinset _ (refinement.blocks_nodup e.1)]
  have hsum := refinement.sums_to_excess e he
  calc
    (∑ b ∈ (refinement.blocks e.1).toFinset,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b) =
        ∑ b ∈ refinement.labels e, refinement.weight e b := by
      rw [refinement.labels_eq e he]
      apply Finset.sum_congr rfl
      intro b hb
      symm
      apply refinement.weight_eq e he b
      simpa [refinement.labels_eq e he] using hb
    _ = W.excess e := hsum

theorem interiorPairsMass_le_bandCharge
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hcomponentCap : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          strictAnchorBlockCap refinement e.1) :
    interiorPairsMass W Z0 ≤
      (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) * thresholdLength W := by
  classical
  let I := interiorAnchorFinset W Z0
  let blockBound : ℕ → LowGapBlock → ℝ := fun k _ =>
    if k ∈ I then strictAnchorBlockCap refinement k else 0
  have hblockNonneg : ∀ k b, 0 ≤ blockBound k b := by
    intro k b
    dsimp [blockBound]
    split
    · unfold strictAnchorBlockCap
      positivity
    · positivity
  have hcomponentBound : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          blockBound e.1 b := by
    intro e he b hb
    have hpair : e ∈ W.pairSet := interiorPairs_subset_pairSet W Z0 he
    have hanchor : e.1 ∈ W.anchors := by
      simpa [WindowSystem.pairSet_eq_prod] using hpair.1
    have hI : e.1 ∈ I := by
      change e.1 ∈ interiorAnchorFinset W Z0
      rw [interiorAnchorFinset, Finset.mem_filter]
      exact ⟨hanchor, ⟨e.2, he⟩⟩
    simpa [blockBound, hI] using hcomponentCap e he b hb
  have hmass := interiorPairsMass_le_refinementAnchorCharge refinement blockBound
    hblockNonneg (refinement.component_sum_eq) hcomponentBound
  have hanchorEq := anchorCharge_sum_eq_sourceCap_sum refinement
  have hbandEq := sourceCap_sum_eq_bandCap_sum refinement
  simpa [blockBound, I, hanchorEq, hbandEq] using hmass

def strictInteriorConstant {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) : ℝ :=
  32 * (W.structural.B + 2) *
    (W.rational.eta.den : ℝ) * (refinement.Cstep + 4)

theorem bandCharge_sum_le_reciprocalSqrt
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hentropy : ∀ key ∈ refinementBandKeys refinement,
      (encodingCandidates key.1 key.2 W.structural.B).Finite ∧
        ((encodingCandidates key.1 key.2 W.structural.B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * key.1)) ≤ Real.sqrt key.1)
    (hfibres : ∀ key ∈ refinementBandKeys refinement,
      ∀ σ ∈ encodingCandidates key.1 key.2 W.structural.B,
        (spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
            (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
              W.m * W.X / key.1) :
    (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) ≤
      strictInteriorConstant refinement * W.m * W.X *
        ∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1 := by
  have hsum : (∑ key ∈ refinementBandKeys refinement,
      ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
        strictBandBlockCap W key.1) ≤
      ∑ key ∈ refinementBandKeys refinement,
        strictInteriorConstant refinement * W.m * W.X *
          (1 / Real.sqrt key.1) := by
    apply Finset.sum_le_sum
    intro key hkey
    have hD : 0 < key.1 := by
      rcases Finset.mem_image.mp hkey with ⟨kb, hkb, hkeyEq⟩
      have hpos := refinement.denominatorBand_pos kb.1
      have hDvalue : refinement.denominatorBand kb.1 = key.1 :=
        congrArg Prod.fst hkeyEq
      rw [← hDvalue]
      exact hpos
    have hfixed := fixedBandCharge_le_sqrt hD refinement
      (hentropy key hkey).1 (hentropy key hkey).2 (hfibres key hkey)
    calc
      ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1 ≤
        32 * (W.structural.B + 2) *
          ((W.rational.eta.den : ℝ) * (refinement.Cstep + 4) * W.m * W.X) /
            Real.sqrt key.1 := hfixed
      _ = strictInteriorConstant refinement * W.m * W.X *
          (1 / Real.sqrt key.1) := by
        unfold strictInteriorConstant
        ring
  calc
    (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) ≤
      ∑ key ∈ refinementBandKeys refinement,
        strictInteriorConstant refinement * W.m * W.X *
          (1 / Real.sqrt key.1) := hsum
    _ = strictInteriorConstant refinement * W.m * W.X *
        ∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1 := by
      rw [Finset.mul_sum]

theorem bandEntropy_of_key_bounds
    {W : WindowSystem} {Z0 Zstar : ℕ} {cBand : ℝ}
    (refinement : InteriorRefinement W Z0)
    (hsignature : ∀ D Z : ℕ,
      Zstar ≤ Z → cBand * (2 : ℝ) ^ Z ≤ D →
        (encodingCandidates D Z W.structural.B).Finite ∧
          ((encodingCandidates D Z W.structural.B).ncard : ℝ) *
            Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D)
    (hZ : ∀ key ∈ refinementBandKeys refinement, Zstar ≤ key.2)
    (hD : ∀ key ∈ refinementBandKeys refinement,
      cBand * (2 : ℝ) ^ key.2 ≤ key.1) :
    ∀ key ∈ refinementBandKeys refinement,
      (encodingCandidates key.1 key.2 W.structural.B).Finite ∧
        ((encodingCandidates key.1 key.2 W.structural.B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * key.1)) ≤ Real.sqrt key.1 := by
  intro key hkey
  have h := hsignature key.1 key.2 (hZ key hkey) (hD key hkey)
  exact h

theorem bandKeys_property_of_pairs
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0) (P : ℕ → ℕ → Prop)
    (hP : ∀ e ∈ interiorPairs W Z0,
      P (refinement.denominatorBand e.1) (refinement.meanGap e.1)) :
    ∀ key ∈ refinementBandKeys refinement, P key.1 key.2 := by
  classical
  intro key hkey
  rcases Finset.mem_image.mp hkey with ⟨kb, hsource, hkeyEq⟩
  have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsource
  have hkInterior := hsourceData.1
  rw [interiorAnchorFinset, Finset.mem_filter] at hkInterior
  rcases hkInterior.2 with ⟨T, he⟩
  have hp := hP (kb.1, T) he
  have hD : refinement.denominatorBand kb.1 = key.1 :=
    congrArg Prod.fst hkeyEq
  have hZ : refinement.meanGap kb.1 = key.2 :=
    congrArg Prod.snd hkeyEq
  simpa [hD, hZ] using hp

def strictBandExponent (key : ℕ × ℕ) : ℕ := Nat.log 2 key.1

theorem bandKey_isPow
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (key : ℕ × ℕ) (hkey : key ∈ refinementBandKeys refinement) :
    (∃ d : ℕ, key.1 = 2 ^ d) ∧ (∃ z : ℕ, key.2 = 2 ^ z) := by
  classical
  rcases Finset.mem_image.mp hkey with ⟨kb, hsource, hkeyEq⟩
  have hsourceData := (mem_refinementSourceFinset_iff refinement kb).mp hsource
  have hkInterior := hsourceData.1
  rw [interiorAnchorFinset, Finset.mem_filter] at hkInterior
  rcases hkInterior.2 with ⟨T, he⟩
  have hspatial := refinement.source_valid (kb.1, T) he kb.2 hsourceData.2
  change IsSpatialEncodingSource W.rational.eta.den refinement.gap.Cgap
    W.structural.B refinement.Cstep W Z0 refinement.selection
      (encodeBlock (refinement.denominatorBand kb.1)
        (refinement.meanGap kb.1) kb.2) kb at hspatial
  rcases hspatial with ⟨data, t, hrec, hparameter⟩
  have hcandidate := hrec.2.2.2.2.2.2.1
  have hvalidEncoding :
      (encodeBlock (refinement.denominatorBand kb.1)
        (refinement.meanGap kb.1) kb.2).Valid := hcandidate.1
  have hDpow : ∃ d : ℕ, refinement.denominatorBand kb.1 = 2 ^ d := by
    simpa [encodeBlock] using hvalidEncoding.1
  have hZpow : ∃ z : ℕ, refinement.meanGap kb.1 = 2 ^ z := by
    simpa [encodeBlock] using hvalidEncoding.2.1
  have hD : refinement.denominatorBand kb.1 = key.1 :=
    congrArg Prod.fst hkeyEq
  have hZ : refinement.meanGap kb.1 = key.2 :=
    congrArg Prod.snd hkeyEq
  simpa [hD, hZ] using And.intro hDpow hZpow

theorem bandKey_eq_two_pow_strictBandExponent
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (key : ℕ × ℕ) (hkey : key ∈ refinementBandKeys refinement) :
    key.1 = 2 ^ strictBandExponent key := by
  rcases (bandKey_isPow refinement key hkey).1 with ⟨d, hd⟩
  have hlog : Nat.log 2 key.1 = d := by
    calc
      Nat.log 2 key.1 = Nat.log 2 (2 ^ d) := congrArg (Nat.log 2) hd
      _ = d := Nat.log_pow (by omega : 1 < 2) d
  calc
    key.1 = 2 ^ d := hd
    _ = 2 ^ strictBandExponent key := by rw [strictBandExponent, hlog]

theorem realMeanGapCutoff_implies_nat
    {Z0 Z : ℕ} (h : (Z0 : ℝ) / 32 < Z) : Z0 / 32 ≤ Z := by
  have hfloor : ((Z0 / 32 : ℕ) : ℝ) ≤ (Z0 : ℝ) / 32 :=
    Nat.cast_div_le
  exact_mod_cast (hfloor.trans h.le)

theorem bandFibres_of_globalSourceFibre
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hsource : ∀ selection : InteriorAnchorSelection,
      ValidInteriorAnchorSelection W.rational.eta.den W Z0 selection →
        ∀ σ : BlockEncoding,
          σ ∈ encodingCandidates σ.D σ.Z W.structural.B →
            0 < σ.D →
              (spatialPreimage W.rational.eta.den refinement.gap.Cgap
                  W.structural.B refinement.Cstep W Z0 selection σ).Finite ∧
                ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
                  W.structural.B refinement.Cstep W Z0 selection σ).ncard : ℝ) ≤
                    (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                      W.m * W.X / σ.D) :
    ∀ key ∈ refinementBandKeys refinement,
      ∀ σ ∈ encodingCandidates key.1 key.2 W.structural.B,
        (spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
              (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                W.m * W.X / key.1 := by
  intro key hkey σ hσ
  have hσD : σ.D = key.1 := hσ.2.1
  have hσZ : σ.Z = key.2 := hσ.2.2.1
  have hσOwn : σ ∈ encodingCandidates σ.D σ.Z W.structural.B := by
    simpa [hσD, hσZ] using hσ
  have hDpos : 0 < σ.D := by
    rw [hσD]
    rcases Finset.mem_image.mp hkey with ⟨kb, hkb, hkeyEq⟩
    have hkeyD : refinement.denominatorBand kb.1 = key.1 :=
      congrArg Prod.fst hkeyEq
    rw [← hkeyD]
    exact refinement.denominatorBand_pos kb.1
  have h := hsource refinement.selection refinement.selection_valid σ hσOwn hDpos
  simpa [hσD] using h

theorem interiorPairsMass_le_tail
    {W : WindowSystem} {Z0 : ℕ}
    (refinement : InteriorRefinement W Z0)
    (hcomponentCap : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          strictAnchorBlockCap refinement e.1)
    (hentropy : ∀ key ∈ refinementBandKeys refinement,
      (encodingCandidates key.1 key.2 W.structural.B).Finite ∧
        ((encodingCandidates key.1 key.2 W.structural.B).ncard : ℝ) *
          Nat.ceil (Real.logb 2 (4 * key.1)) ≤ Real.sqrt key.1)
    (hfibres : ∀ key ∈ refinementBandKeys refinement,
      ∀ σ ∈ encodingCandidates key.1 key.2 W.structural.B,
        (spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).Finite ∧
          ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
            W.structural.B refinement.Cstep W Z0 refinement.selection σ).ncard : ℝ) ≤
              (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                W.m * W.X / key.1)
    (tail : ℝ) (htail :
      (∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1) ≤ tail) :
    interiorPairsMass W Z0 ≤
      strictInteriorConstant refinement * tail * W.m * W.X * thresholdLength W := by
  have hmass := interiorPairsMass_le_bandCharge refinement hcomponentCap
  have hbands := bandCharge_sum_le_reciprocalSqrt refinement hentropy hfibres
  have hconstantNonneg : 0 ≤ strictInteriorConstant refinement := by
    unfold strictInteriorConstant
    have hB : 0 ≤ W.structural.B + 2 := by linarith [W.structural.B_gt]
    have hstep : 0 ≤ refinement.Cstep + 4 := by linarith [refinement.Cstep_pos]
    positivity
  have hmXNonneg : 0 ≤ strictInteriorConstant refinement * W.m * W.X := by
    exact mul_nonneg
      (mul_nonneg hconstantNonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hbandTail :
      (∑ key ∈ refinementBandKeys refinement,
        ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
          strictBandBlockCap W key.1) ≤
        strictInteriorConstant refinement * W.m * W.X * tail :=
    hbands.trans (mul_le_mul_of_nonneg_left htail hmXNonneg)
  have hlength : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  calc
    interiorPairsMass W Z0 ≤
        (∑ key ∈ refinementBandKeys refinement,
          ((refinementSourceBandFinset refinement key.1 key.2).card : ℝ) *
            strictBandBlockCap W key.1) * thresholdLength W := hmass
    _ ≤ (strictInteriorConstant refinement * W.m * W.X * tail) *
        thresholdLength W := mul_le_mul_of_nonneg_right hbandTail hlength
    _ = strictInteriorConstant refinement * tail * W.m * W.X *
        thresholdLength W := by ring
def strictBandPairTail (Z0 : ℕ) : ℝ :=
  strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ * strictMassTail Z0

theorem strictBandPairTail_nonneg (Z0 : ℕ) : 0 ≤ strictBandPairTail Z0 := by
  unfold strictBandPairTail
  have houterInv : 0 ≤ strictMassOuterRatio⁻¹ :=
    inv_nonneg.mpr strictMassOuterRatio_nonneg
  have htailInv : 0 ≤ (1 - strictMassOuterRatio)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr strictMassOuterRatio_le_one)
  exact mul_nonneg (mul_nonneg houterInv htailInv) (strictMassTail_nonneg Z0)

theorem strictBandPairTail_tendsto_zero :
    Tendsto strictBandPairTail atTop (𝓝 0) := by
  let C : ℝ := strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have h := hconst.mul strictMassTail_tendsto_zero
  change Tendsto (fun Z0 : ℕ =>
    strictMassOuterRatio⁻¹ * (1 - strictMassOuterRatio)⁻¹ *
      strictMassTail Z0) atTop (𝓝 0)
  simpa [C] using h
/-- Paper label: `thm:strict-mass` (Section 6).  A denominator-level cutoff
and one nonnegative coefficient function tending to zero are selected before
the compatible rational-support family.  At every cutoff beyond that fixed
threshold, all sufficiently large scales simultaneously carry an actual
interior refinement certificate and obey the strict interior mass bound. -/
theorem thm_strict_mass (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∃ ηQ : ℕ → ℝ, (∀ Z0, 0 ≤ ηQ Z0) ∧
      Tendsto ηQ atTop (𝓝 0) ∧
      ∀ Z0 : ℕ, Zmin ≤ Z0 →
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ∃ _refinement : InteriorRefinement (F.system L) Z0,
              interiorPairsMass (F.system L) Z0 ≤
                ηQ Z0 * (F.system L).m * (F.system L).X *
                  thresholdLength (F.system L) := by
  obtain ⟨gap, Cstep, hCstep, Zcertificate, cBand, hcBand, hcertificate⟩ :=
    eventually_exists_interiorRefinement_certificate context
  obtain ⟨Zstar, CB, hCB, hsignature⟩ :=
    lem_signature_entropy context.structural.B cBand
      context.structural.B_gt hcBand
  obtain ⟨Ztail, htail⟩ :=
    exists_finite_dyadic_band_pair_tail_of_lower cBand hcBand
  obtain ⟨Zsource, hsource⟩ :=
    lem_source_fibre context gap Cstep hCstep
  let Zband := max Zstar Ztail
  let Zmin := max Zcertificate (max Zsource (32 * Zband))
  let Cmass : ℝ :=
    32 * (context.structural.B + 2) * (context.Q : ℝ) * (Cstep + 4)
  let ηQ : ℕ → ℝ := fun Z0 => Cmass * strictBandPairTail Z0
  have hCmass : 0 ≤ Cmass := by
    dsimp [Cmass]
    have hB : 0 ≤ context.structural.B + 2 := by
      linarith [context.structural.B_gt]
    have hstep : 0 ≤ Cstep + 4 := by linarith
    positivity
  have hηNonneg : ∀ Z0, 0 ≤ ηQ Z0 := by
    intro Z0
    exact mul_nonneg hCmass (strictBandPairTail_nonneg Z0)
  have hηTendsto : Tendsto ηQ atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => Cmass) atTop (𝓝 Cmass) :=
      tendsto_const_nhds
    simpa [ηQ] using hconst.mul strictBandPairTail_tendsto_zero
  refine ⟨Zmin, ηQ, hηNonneg, hηTendsto, ?_⟩
  intro Z0 hZ0 F hF
  have hZcertificate : Zcertificate ≤ Z0 :=
    (le_max_left Zcertificate (max Zsource (32 * Zband))).trans hZ0
  have hZsource : Zsource ≤ Z0 :=
    (le_trans (le_max_left Zsource (32 * Zband))
      (le_max_right Zcertificate (max Zsource (32 * Zband)))).trans hZ0
  have hZbandScale : 32 * Zband ≤ Z0 :=
    (le_trans (le_max_right Zsource (32 * Zband))
      (le_max_right Zcertificate (max Zsource (32 * Zband)))).trans hZ0
  have hZbandBase : Zband ≤ Z0 / 32 := by
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 32)).2
      (by simpa [Nat.mul_comm] using hZbandScale)
  filter_upwards [hcertificate Z0 hZcertificate F hF,
      hsource Z0 hZsource F hF] with L hcertificateL hsourceL
  rcases hcertificateL with ⟨refinement, hfacts⟩
  refine ⟨refinement, ?_⟩
  let W := F.system L
  have hstructural : W.structural = context.structural := by
    dsimp [W]
    rw [F.structural_eq, hF.2.1]
  have hdenominator : W.rational.eta.den = context.Q := by
    dsimp [W]
    rw [F.rational_eq]
    exact hF.1
  have hcomponentCap : ∀ e, e ∈ interiorPairs W Z0 →
      ∀ b ∈ refinement.blocks e.1,
        interiorComponentWeight (W.excess e) (refinement.blocks e.1) b ≤
          strictAnchorBlockCap refinement e.1 := by
    intro e he b hb
    simpa [strictAnchorBlockCap] using hfacts.component_bound e he b hb
  have hmeanKey : ∀ key ∈ refinementBandKeys refinement,
      (Z0 : ℝ) / 32 < key.2 :=
    bandKeys_property_of_pairs refinement
      (fun _ Z => (Z0 : ℝ) / 32 < Z)
      (by
        intro e he
        exact hfacts.meanGap_cutoff e he)
  have hdenKey : ∀ key ∈ refinementBandKeys refinement,
      cBand * (2 : ℝ) ^ key.2 ≤ key.1 :=
    bandKeys_property_of_pairs refinement
      (fun D Z => cBand * (2 : ℝ) ^ Z ≤ D)
      (by
        intro e he
        exact hfacts.denominator_lower e he)
  have hcutoffKey : ∀ key ∈ refinementBandKeys refinement,
      Z0 / 32 ≤ key.2 := by
    intro key hkey
    exact realMeanGapCutoff_implies_nat (hmeanKey key hkey)
  have hZstarKey : ∀ key ∈ refinementBandKeys refinement,
      Zstar ≤ key.2 := by
    intro key hkey
    exact (le_max_left Zstar Ztail).trans
      (hZbandBase.trans (hcutoffKey key hkey))
  have hZtailKey : ∀ key ∈ refinementBandKeys refinement,
      Ztail ≤ key.2 := by
    intro key hkey
    exact (le_max_right Zstar Ztail).trans
      (hZbandBase.trans (hcutoffKey key hkey))
  have hsignatureW : ∀ D Z : ℕ,
      Zstar ≤ Z → cBand * (2 : ℝ) ^ Z ≤ D →
        (encodingCandidates D Z W.structural.B).Finite ∧
          ((encodingCandidates D Z W.structural.B).ncard : ℝ) *
            Nat.ceil (Real.logb 2 (4 * D)) ≤ Real.sqrt D := by
    intro D Z hZ hD
    have h := hsignature D Z hZ hD
    rw [hstructural]
    exact ⟨h.1, h.2.2⟩
  have hentropy := bandEntropy_of_key_bounds refinement hsignatureW
    hZstarKey hdenKey
  have hsourceForRefinement :
      ∀ selection : InteriorAnchorSelection,
        ValidInteriorAnchorSelection W.rational.eta.den W Z0 selection →
          ∀ σ : BlockEncoding,
            σ ∈ encodingCandidates σ.D σ.Z W.structural.B →
              0 < σ.D →
                (spatialPreimage W.rational.eta.den refinement.gap.Cgap
                    W.structural.B refinement.Cstep W Z0 selection σ).Finite ∧
                  ((spatialPreimage W.rational.eta.den refinement.gap.Cgap
                    W.structural.B refinement.Cstep W Z0 selection σ).ncard : ℝ) ≤
                      (W.rational.eta.den : ℝ) * (refinement.Cstep + 4) *
                        W.m * W.X / σ.D := by
    intro selection hselection σ hσ hσD
    have hselectionContext :
        ValidInteriorAnchorSelection context.Q W Z0 selection := by
      simpa [hdenominator] using hselection
    have hσContext :
        σ ∈ encodingCandidates σ.D σ.Z context.structural.B := by
      simpa [hstructural] using hσ
    have h := hsourceL selection hselectionContext σ hσContext hσD
    simpa [hdenominator, hstructural, hfacts.gap_Cgap_eq,
      hfacts.Cstep_eq] using h
  have hfibres := bandFibres_of_globalSourceFibre refinement
    hsourceForRefinement
  have hdyadic : ∀ key ∈ refinementBandKeys refinement,
      key.1 = 2 ^ strictBandExponent key :=
    bandKey_eq_two_pow_strictBandExponent refinement
  have htailBound :
      (∑ key ∈ refinementBandKeys refinement, 1 / Real.sqrt key.1) ≤
        strictBandPairTail Z0 := by
    exact htail (refinementBandKeys refinement) strictBandExponent Z0
      hdyadic hcutoffKey hZtailKey hdenKey
  have hmass := interiorPairsMass_le_tail refinement hcomponentCap
    hentropy hfibres (strictBandPairTail Z0) htailBound
  have hconstant : strictInteriorConstant refinement = Cmass := by
    unfold strictInteriorConstant
    dsimp [Cmass]
    rw [hfacts.Cstep_eq, hstructural, hdenominator]
  simpa [W, hconstant, ηQ] using hmass

end Erdos260
