import ErdosProblems.Erdos260.Pressure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Affine locking and the interior/exterior dichotomy

This module corresponds to Section 5 and incorporates the indexing conventions
from Appendices B and C.
-/

noncomputable section

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators ENNReal

namespace Erdos260

/-- An integer affine line of carry states. -/
structure AffineLine where
  A : ℤ
  C : ℤ
  H : ℤ
  K : ℤ
  H_pos : 0 < H

namespace AffineLine

/-- Normalized slope `K/(QH)`. -/
def slope (Q : ℕ) (line : AffineLine) : ℚ :=
  (line.K : ℚ) / ((Q : ℚ) * line.H)

/-- Shared-gap transformation retaining the original horizontal parameter. -/
def transform (Q g : ℕ) (line : AffineLine) : AffineLine where
  A := line.A + g
  C := (2 : ℤ) ^ g * line.C - (Q : ℤ) * (line.A + g)
  H := line.H
  K := (2 : ℤ) ^ g * line.K - (Q : ℤ) * line.H
  H_pos := line.H_pos

def transformWord (Q : ℕ) : AffineLine → GapWord → AffineLine
  | line, [] => line
  | line, g :: gs => transformWord Q (line.transform Q g) gs

/-- Integer intercept numerator `HC-KA`. -/
def interceptNumerator (line : AffineLine) : ℤ :=
  line.H * line.C - line.K * line.A

/-- Membership of an integer point in the original integer parameterization. -/
def Contains (line : AffineLine) (x r : ℤ) : Prop :=
  ∃ t : ℤ, x = line.A + line.H * t ∧ r = line.C + line.K * t

/-- Horizontal step after primitive reduction. -/
def primitiveHorizontalStep (line : AffineLine) : ℕ :=
  line.H.natAbs / Int.gcd line.H line.K

end AffineLine

/-- Canonical geometric data for an affine lattice line.  Unlike
`AffineLine`, this object has no chosen parameter origin: the primitive
direction and the integer intercept determine the locus. -/
structure GeometricLine where
  H : ℕ
  K : ℤ
  intercept : ℤ
  H_pos : 0 < H
  primitive : Nat.gcd H K.natAbs = 1

namespace GeometricLine

def Contains (line : GeometricLine) (x r : ℤ) : Prop :=
  (line.H : ℤ) * r - line.K * x = line.intercept

def slope (Q : ℕ) (line : GeometricLine) : ℚ :=
  (line.K : ℚ) / ((Q : ℚ) * line.H)

end GeometricLine

/-- A parameterized line and a canonical line have the same integer locus. -/
def RepresentsGeometricLine (line : AffineLine) (geometric : GeometricLine) : Prop :=
  ∀ x r : ℤ, line.Contains x r ↔ geometric.Contains x r

namespace AffineLine

/-- Common divisor removed from the raw integer direction. -/
def directionGCD (line : AffineLine) : ℕ :=
  Int.gcd line.H line.K

theorem directionGCD_pos (line : AffineLine) : 0 < line.directionGCD := by
  exact Int.gcd_pos_of_ne_zero_left line.K (ne_of_gt line.H_pos)

/-- Positive horizontal coordinate of the primitive direction, before
converting it to a natural number. -/
def primitiveHorizontalInt (line : AffineLine) : ℤ :=
  line.H / (line.directionGCD : ℤ)

/-- Vertical coordinate of the primitive direction. -/
def primitiveVertical (line : AffineLine) : ℤ :=
  line.K / (line.directionGCD : ℤ)

theorem primitiveHorizontalInt_pos (line : AffineLine) :
    0 < line.primitiveHorizontalInt := by
  have hd : (0 : ℤ) < line.directionGCD := by
    exact_mod_cast line.directionGCD_pos
  have hfactor :
      line.primitiveHorizontalInt * (line.directionGCD : ℤ) = line.H := by
    exact Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  nlinarith [line.H_pos]

/-- Change only the integer parameter origin, retaining the same raw direction. -/
def shiftOrigin (line : AffineLine) (t : ℤ) : AffineLine where
  A := line.A + line.H * t
  C := line.C + line.K * t
  H := line.H
  K := line.K
  H_pos := line.H_pos

/-- Canonical primitive direction and intercept of the geometric line
underlying a raw integer parameterization. -/
def canonicalGeometricLine (line : AffineLine) : GeometricLine where
  H := line.primitiveHorizontalInt.natAbs
  K := line.primitiveVertical
  intercept := line.interceptNumerator / (line.directionGCD : ℤ)
  H_pos := Int.natAbs_pos.mpr (ne_of_gt line.primitiveHorizontalInt_pos)
  primitive := by
    change Int.gcd
      (line.H / (line.directionGCD : ℤ))
      (line.K / (line.directionGCD : ℤ)) = 1
    exact Int.gcd_div_gcd_div_gcd line.directionGCD_pos

theorem canonicalGeometricLine_H_cast (line : AffineLine) :
    (line.canonicalGeometricLine.H : ℤ) = line.primitiveHorizontalInt := by
  simp [canonicalGeometricLine, abs_of_pos line.primitiveHorizontalInt_pos]

/-- Translating the parameter origin along the raw direction leaves the
canonical geometric line unchanged. -/
theorem canonicalGeometricLine_shiftOrigin (line : AffineLine) (t : ℤ) :
    (line.shiftOrigin t).canonicalGeometricLine = line.canonicalGeometricLine := by
  unfold canonicalGeometricLine shiftOrigin primitiveHorizontalInt primitiveVertical
    directionGCD interceptNumerator
  congr 1
  ring_nf

/-- Every point in the raw integer parameterization lies on its canonical
geometric line.  The converse requires a primitive raw direction and is false
for arbitrary `AffineLine`s. -/
theorem contains_canonicalGeometricLine (line : AffineLine) (x r : ℤ)
    (h : line.Contains x r) : line.canonicalGeometricLine.Contains x r := by
  rcases h with ⟨t, rfl, rfl⟩
  rw [GeometricLine.Contains, canonicalGeometricLine_H_cast]
  have hHfactor :
      line.primitiveHorizontalInt * (line.directionGCD : ℤ) = line.H := by
    exact Int.ediv_mul_cancel (Int.gcd_dvd_left line.H line.K)
  have hKfactor :
      line.primitiveVertical * (line.directionGCD : ℤ) = line.K := by
    exact Int.ediv_mul_cancel (Int.gcd_dvd_right line.H line.K)
  have hdvdIntercept :
      (line.directionGCD : ℤ) ∣ line.interceptNumerator := by
    refine ⟨line.primitiveHorizontalInt * line.C -
      line.primitiveVertical * line.A, ?_⟩
    simp only [interceptNumerator]
    rw [← hHfactor, ← hKfactor]
    ring
  have hdne : (line.directionGCD : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt line.directionGCD_pos)
  change
    line.primitiveHorizontalInt * (line.C + line.K * t) -
        line.primitiveVertical * (line.A + line.H * t) =
      line.interceptNumerator / (line.directionGCD : ℤ)
  apply mul_right_cancel₀ hdne
  rw [Int.ediv_mul_cancel hdvdIntercept]
  simp only [← hHfactor, ← hKfactor, interceptNumerator]
  ring

end AffineLine

namespace GeometricLine

/-- Two distinct common integer points determine a canonical primitive
geometric line.  This is the occurrence-line uniqueness principle in a form
that does not depend on any later denominator computation. -/
theorem eq_of_two_common_points
    (u v : GeometricLine) (x₁ r₁ x₂ r₂ : ℤ) (hx : x₁ ≠ x₂)
    (hu₁ : u.Contains x₁ r₁) (hu₂ : u.Contains x₂ r₂)
    (hv₁ : v.Contains x₁ r₁) (hv₂ : v.Contains x₂ r₂) : u = v := by
  have huDet : (u.H : ℤ) * (r₂ - r₁) = u.K * (x₂ - x₁) := by
    rw [GeometricLine.Contains] at hu₁ hu₂
    linarith
  have hvDet : (v.H : ℤ) * (r₂ - r₁) = v.K * (x₂ - x₁) := by
    rw [GeometricLine.Contains] at hv₁ hv₂
    linarith
  have hdx : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcross : u.K * (v.H : ℤ) = v.K * (u.H : ℤ) := by
    apply mul_right_cancel₀ hdx
    calc
      (u.K * (v.H : ℤ)) * (x₂ - x₁) =
          (v.H : ℤ) * (u.K * (x₂ - x₁)) := by ring
      _ = (v.H : ℤ) * ((u.H : ℤ) * (r₂ - r₁)) := by rw [← huDet]
      _ = (u.H : ℤ) * ((v.H : ℤ) * (r₂ - r₁)) := by ring
      _ = (u.H : ℤ) * (v.K * (x₂ - x₁)) := by rw [hvDet]
      _ = (v.K * (u.H : ℤ)) * (x₂ - x₁) := by ring
  have habs : u.K.natAbs * v.H = v.K.natAbs * u.H := by
    have := congrArg Int.natAbs hcross
    simpa [Int.natAbs_mul] using this
  have huCop : Nat.Coprime u.H u.K.natAbs := u.primitive
  have hvCop : Nat.Coprime v.H v.K.natAbs := v.primitive
  have huDvdMul : u.H ∣ u.K.natAbs * v.H := by
    refine ⟨v.K.natAbs, ?_⟩
    calc
      u.K.natAbs * v.H = v.K.natAbs * u.H := habs
      _ = u.H * v.K.natAbs := Nat.mul_comm _ _
  have hvDvdMul : v.H ∣ v.K.natAbs * u.H := by
    refine ⟨u.K.natAbs, ?_⟩
    calc
      v.K.natAbs * u.H = u.K.natAbs * v.H := habs.symm
      _ = v.H * u.K.natAbs := Nat.mul_comm _ _
  have huDvd : u.H ∣ v.H := (huCop.dvd_mul_left).mp huDvdMul
  have hvDvd : v.H ∣ u.H := (hvCop.dvd_mul_left).mp hvDvdMul
  have hH : u.H = v.H := Nat.dvd_antisymm huDvd hvDvd
  have hK : u.K = v.K := by
    rw [hH] at hcross
    exact mul_right_cancel₀ (by exact_mod_cast v.H_pos.ne') hcross
  have hintercept : u.intercept = v.intercept := by
    rw [GeometricLine.Contains] at hu₁ hv₁
    rw [hH, hK] at hu₁
    linarith
  cases u
  cases v
  simp_all

end GeometricLine

/-- The four slope regions used in the paper. -/
inductive SlopeRegion
  | interior
  | boundaryZero
  | boundaryOne
  | exterior
  deriving DecidableEq, Repr

/-- Exact classification of a rational normalized slope. -/
def classifySlope (μ : ℚ) : SlopeRegion :=
  if μ = 0 then .boundaryZero
  else if μ = 1 then .boundaryOne
  else if 0 < μ ∧ μ < 1 then .interior
  else .exterior

/-- Exact iterated shared-gap relation. -/
inductive SharedGapTrajectory (Q : ℕ) : AffineLine → GapWord → AffineLine → Prop
  | nil (line : AffineLine) : SharedGapTrajectory Q line [] line
  | cons (line next finish : AffineLine) (g : ℕ) (gs : GapWord)
      (hnext : next = line.transform Q g)
      (htail : SharedGapTrajectory Q next gs finish) :
      SharedGapTrajectory Q line (g :: gs) finish

/-- Applying two consecutive gap words is the same as applying their
concatenation.  This elementary identity belongs to the common affine layer:
both the interior and exterior branches use it. -/
theorem AffineLine.transformWord_append (Q : ℕ) (line : AffineLine)
    (u v : GapWord) :
    line.transformWord Q (u ++ v) =
      (line.transformWord Q u).transformWord Q v := by
  induction u generalizing line with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.cons_append, AffineLine.transformWord]
      exact ih (line.transform Q g)

/-- Exact normalized-slope recurrence for one shared gap. -/
theorem AffineLine.slope_transform (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (g : ℕ) :
    (line.transform Q g).slope Q =
      (2 : ℚ) ^ g * line.slope Q - 1 := by
  have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hH0 : (line.H : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt line.H_pos)
  simp only [AffineLine.slope, AffineLine.transform]
  push_cast
  field_simp [hQ0, hH0]

/-- Real-cast form of the exact one-gap slope recurrence. -/
theorem AffineLine.transform_slope_real (Q g : ℕ) (hQ : 0 < Q)
    (line : AffineLine) :
    ((line.transform Q g).slope Q : ℝ) =
      (2 : ℝ) ^ g * (line.slope Q : ℝ) - 1 := by
  exact_mod_cast AffineLine.slope_transform Q hQ line g

/-- Real slope after a word agrees with the elementary scalar recurrence. -/
theorem AffineLine.transformWord_slope_real (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) :
    ((line.transformWord Q word).slope Q : ℝ) =
      slopeAfter word (line.slope Q : ℝ) := by
  induction word generalizing line with
  | nil => rfl
  | cons g gs ih =>
      simp only [AffineLine.transformWord, slopeAfter]
      rw [ih, AffineLine.transform_slope_real Q g hQ line]

/-- Iterated shared-gap slope evolution depends only on the initial normalized
slope, not on the chosen parameter origin or a nonprimitive rescaling. -/
theorem AffineLine.transformWord_slope_eq_of_slope_eq (Q : ℕ) (hQ : 0 < Q)
    (left right : AffineLine) (word : GapWord)
    (hslope : left.slope Q = right.slope Q) :
    (left.transformWord Q word).slope Q =
      (right.transformWord Q word).slope Q := by
  induction word generalizing left right with
  | nil => exact hslope
  | cons g gs ih =>
      simp only [AffineLine.transformWord]
      apply ih
      rw [AffineLine.slope_transform Q hQ,
        AffineLine.slope_transform Q hQ, hslope]

/-- The inductive shared-gap trajectory has the deterministic endpoint given
by `transformWord`. -/
theorem sharedGapTrajectory_iff_transformWord (Q : ℕ) (line : AffineLine)
    (gaps : GapWord) (finish : AffineLine) :
    SharedGapTrajectory Q line gaps finish ↔
      finish = line.transformWord Q gaps := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons line next finish g gs hnext htail ih =>
        subst next
        exact ih
  · intro h
    subst finish
    induction gaps generalizing line with
    | nil => exact SharedGapTrajectory.nil line
    | cons g gs ih =>
        exact SharedGapTrajectory.cons line (line.transform Q g)
          ((line.transform Q g).transformWord Q gs) g gs rfl
          (ih (line.transform Q g))

/-- A slope is exterior precisely when it lies strictly outside `[0,1]`. -/
theorem classifySlope_eq_exterior_iff (μ : ℚ) :
    classifySlope μ = .exterior ↔ μ < 0 ∨ 1 < μ := by
  constructor
  · intro h
    by_cases hneg : μ < 0
    · exact Or.inl hneg
    by_cases hgt : 1 < μ
    · exact Or.inr hgt
    exfalso
    have hnonneg : 0 ≤ μ := le_of_not_gt hneg
    have hle : μ ≤ 1 := le_of_not_gt hgt
    by_cases h0 : μ = 0
    · subst μ
      simp [classifySlope] at h
    by_cases h1 : μ = 1
    · subst μ
      simp [classifySlope] at h
    have hi : 0 < μ ∧ μ < 1 :=
      ⟨lt_of_le_of_ne hnonneg (Ne.symm h0), lt_of_le_of_ne hle h1⟩
    simp [classifySlope, h0, h1, hi] at h
  · rintro (hneg | hgt)
    · have h0 : μ ≠ 0 := ne_of_lt hneg
      have h1 : μ ≠ 1 := by linarith
      have hi : ¬ (0 < μ ∧ μ < 1) := by
        rintro ⟨hpos, _⟩
        linarith
      simp [classifySlope, h0, h1, hi]
    · have h0 : μ ≠ 0 := by linarith
      have h1 : μ ≠ 1 := ne_of_gt hgt
      have hi : ¬ (0 < μ ∧ μ < 1) := by
        rintro ⟨_, hlt⟩
        linarith
      simp [classifySlope, h0, h1, hi]

/-- Exterior slope is forward invariant under a positive shared gap. -/
theorem classifySlope_transform_exterior (Q g : ℕ) (hQ : 0 < Q)
    (hg : 1 ≤ g) (line : AffineLine)
    (hline : classifySlope (line.slope Q) = .exterior) :
    classifySlope ((line.transform Q g).slope Q) = .exterior := by
  rw [AffineLine.slope_transform Q hQ]
  rw [classifySlope_eq_exterior_iff] at hline ⊢
  rcases hline with hneg | hgt
  · left
    have hpow : (0 : ℚ) < (2 : ℚ) ^ g := by positivity
    nlinarith [mul_neg_of_pos_of_neg hpow hneg]
  · right
    have hpow : (2 : ℚ) ≤ (2 : ℚ) ^ g := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hg)
    nlinarith [mul_le_mul_of_nonneg_left hgt.le (by positivity : (0 : ℚ) ≤ 2 ^ g)]

theorem classifySlope_transformWord_exterior (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hword : word.Positive)
    (hline : classifySlope (line.slope Q) = .exterior) :
    classifySlope ((line.transformWord Q word).slope Q) = .exterior := by
  induction word generalizing line with
  | nil => simpa only [AffineLine.transformWord] using hline
  | cons g gs ih =>
      have hg : 1 ≤ g := hword g (by simp)
      have hgs : GapWord.Positive gs := by
        intro x hx
        exact hword x (by simp [hx])
      exact ih (line.transform Q g) hgs
        (classifySlope_transform_exterior Q g hQ hg line hline)

/-- Every state produced by a gap prefix is interior. -/
def IsInteriorTrajectory (Q : ℕ) (line : AffineLine) (gaps : GapWord) : Prop :=
  ∀ r ≤ gaps.length, ∃ state : AffineLine,
    SharedGapTrajectory Q line (gaps.take r) state ∧
      classifySlope (state.slope Q) = .interior

/-- Every state produced by a nonempty gap prefix is exterior. -/
def IsExteriorTrajectory (Q : ℕ) (line : AffineLine) (gaps : GapWord) : Prop :=
  classifySlope (line.slope Q) = .exterior ∧
    ∀ r ≤ gaps.length, ∃ state : AffineLine,
      SharedGapTrajectory Q line (gaps.take r) state ∧
        classifySlope (state.slope Q) = .exterior

theorem isExteriorTrajectory_of_positive (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine) (word : GapWord) (hword : word.Positive)
    (hline : classifySlope (line.slope Q) = .exterior) :
    IsExteriorTrajectory Q line word := by
  refine ⟨hline, ?_⟩
  intro r hr
  refine ⟨line.transformWord Q (word.take r), ?_, ?_⟩
  · exact (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl
  · apply classifySlope_transformWord_exterior Q hQ line (word.take r)
    · intro g hg
      exact hword g (List.mem_of_mem_take hg)
    · exact hline

/-- Initial long prefix selected independently of the threshold. -/
def initialLongPrefix (W : WindowSystem) (k : ℕ) : GapWord :=
  (W.rawWindowGapWord k).firstPrefixAbove
    (Nat.floor (W.structural.Caff * W.L))

/-- Anchors that admit at least one large-excess threshold. -/
def highAnchors (W : WindowSystem) (Z0 : ℕ) : Finset ℕ :=
  by
    classical
    exact W.anchors.filter fun k =>
      ∃ T : ℝ, T ∈ W.thresholds ∧ W.m * Z0 < W.excess (k, T)

/-- Set of selected initial prefixes at one scale. -/
def initialPrefixes (W : WindowSystem) (Z0 : ℕ) : Finset GapWord :=
  (highAnchors W Z0).image (initialLongPrefix W)

/-- Anchor multiplicity of a selected prefix; thresholds are not counted. -/
def prefixMultiplicity (W : WindowSystem) (Z0 : ℕ) (p : GapWord) : ℕ :=
  ((highAnchors W Z0).filter fun k => initialLongPrefix W k = p).card

def frequencyCutoff (W : WindowSystem) : ℝ :=
  Real.rpow W.X (1 / 2 + W.structural.rho)

def IsFrequentPrefix (W : WindowSystem) (Z0 : ℕ) (p : GapWord) : Prop :=
  frequencyCutoff W ≤ prefixMultiplicity W Z0 p

def IsRarePrefix (W : WindowSystem) (Z0 : ℕ) (p : GapWord) : Prop :=
  (prefixMultiplicity W Z0 p : ℝ) < frequencyCutoff W

/-- Large-excess pairs with a rare selected prefix. -/
def rareLargePairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  W.largePairs Z0 ∩ {e | IsRarePrefix W Z0 (initialLongPrefix W e.1)}

theorem rareLargePairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    rareLargePairs W Z0 ⊆ W.pairSet := by
  intro e he
  exact he.1.1

/-- Certified real mass of the rare-prefix family. -/
def rareLargePairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (rareLargePairs W Z0)
    (rareLargePairs_subset_pairSet W Z0)

/-- Anchors occurring in the rare-prefix parent family. -/
def rareAnchors (W : WindowSystem) (Z0 : ℕ) : Finset ℕ :=
  by
    classical
    exact (highAnchors W Z0).filter fun k =>
      IsRarePrefix W Z0 (initialLongPrefix W k)

theorem rareLargePairs_subset_rareRectangle (W : WindowSystem) (Z0 : ℕ) :
    rareLargePairs W Z0 ⊆
      Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds := by
  classical
  intro e he
  refine ⟨?_, he.1.1.2⟩
  rw [Finset.mem_coe, rareAnchors, Finset.mem_filter]
  constructor
  · rw [highAnchors, Finset.mem_filter]
    refine ⟨he.1.1.1, e.2, he.1.1.2, ?_⟩
    exact he.1.2
  · exact he.2

theorem rareAnchors_card_le (W : WindowSystem) (Z0 : ℕ) :
    ((rareAnchors W Z0).card : ℝ) ≤
      ((initialPrefixes W Z0).card : ℝ) * frequencyCutoff W := by
  classical
  let rarePrefixes : Finset GapWord :=
    (initialPrefixes W Z0).filter fun p => IsRarePrefix W Z0 p
  let fibres : GapWord → Finset ℕ := fun p =>
    (highAnchors W Z0).filter fun k => initialLongPrefix W k = p
  have hsubset : rareAnchors W Z0 ⊆ rarePrefixes.biUnion fibres := by
    intro k hk
    rw [rareAnchors, Finset.mem_filter] at hk
    rw [Finset.mem_biUnion]
    refine ⟨initialLongPrefix W k, ?_, ?_⟩
    · change initialLongPrefix W k ∈
        (initialPrefixes W Z0).filter fun p => IsRarePrefix W Z0 p
      rw [Finset.mem_filter]
      constructor
      · rw [initialPrefixes, Finset.mem_image]
        exact ⟨k, hk.1, rfl⟩
      · exact hk.2
    · change k ∈ (highAnchors W Z0).filter fun j =>
        initialLongPrefix W j = initialLongPrefix W k
      rw [Finset.mem_filter]
      exact ⟨hk.1, rfl⟩
  have hcardNat : (rareAnchors W Z0).card ≤
      ∑ p ∈ rarePrefixes, (fibres p).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  have hcardReal : ((rareAnchors W Z0).card : ℝ) ≤
      ∑ p ∈ rarePrefixes, ((fibres p).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((rareAnchors W Z0).card : ℝ) ≤
        ∑ p ∈ rarePrefixes, ((fibres p).card : ℝ) := hcardReal
    _ ≤ ∑ _p ∈ rarePrefixes, frequencyCutoff W := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : p ∈ (initialPrefixes W Z0).filter fun q =>
          IsRarePrefix W Z0 q := hp
      rw [Finset.mem_filter] at hp'
      simpa only [fibres, prefixMultiplicity] using hp'.2.le
    _ = (rarePrefixes.card : ℝ) * frequencyCutoff W := by simp
    _ ≤ ((initialPrefixes W Z0).card : ℝ) * frequencyCutoff W := by
      have hcard : rarePrefixes.card ≤ (initialPrefixes W Z0).card := by
        apply Finset.card_le_card
        intro p hp
        have hp' : p ∈ (initialPrefixes W Z0).filter fun q =>
            IsRarePrefix W Z0 q := hp
        exact (Finset.mem_filter.mp hp').1
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      unfold frequencyCutoff
      exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le W.X) _

private theorem windowThresholdMeasure_rareRectangle
    (W : WindowSystem) (Z0 : ℕ) :
    windowThresholdMeasure
        (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) =
      ((rareAnchors W Z0).card : ℝ≥0∞) *
        ENNReal.ofReal (thresholdLength W) := by
  rw [windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) =
        Measure.count (rareAnchors W Z0 : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc, thresholdLength]
  congr 2
  ring

private theorem rareLargePairsMass_le (W : WindowSystem) (Z0 : ℕ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ e ∈ rareLargePairs W Z0, W.excess e ≤ M) :
    rareLargePairsMass W Z0 ≤
      M * (rareAnchors W Z0).card * thresholdLength W := by
  have hmass : mass (rareLargePairs W Z0) W.excess ≤
      ENNReal.ofReal M * windowThresholdMeasure
        (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) := by
    unfold mass
    calc
      (∫⁻ e in rareLargePairs W Z0, ENNReal.ofReal (W.excess e)
          ∂windowThresholdMeasure) ≤
          ∫⁻ _e in rareLargePairs W Z0, ENNReal.ofReal M
            ∂windowThresholdMeasure := by
        apply setLIntegral_mono measurable_const
        intro e he
        exact ENNReal.ofReal_le_ofReal (hbound e he)
      _ ≤ ∫⁻ _e in Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds,
          ENNReal.ofReal M ∂windowThresholdMeasure :=
        lintegral_mono_set (rareLargePairs_subset_rareRectangle W Z0)
      _ = ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) :=
        setLIntegral_const _ _
  have hleftTop : mass (rareLargePairs W Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (rareLargePairs W Z0)
      (rareLargePairs_subset_pairSet W Z0)).ne_top
  have hlength : 0 ≤ thresholdLength W :=
    mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrightTop :
      ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (rareAnchors W Z0 : Set ℕ) W.thresholds) ≠ ⊤ := by
    rw [windowThresholdMeasure_rareRectangle]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  have hto := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  change (mass (rareLargePairs W Z0) W.excess).toReal ≤ _
  rw [windowThresholdMeasure_rareRectangle] at hto
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlength, mul_assoc] using hto

/-- All occurrences of one selected prefix lie on this affine line. -/
def IsOccurrenceLine (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (line : AffineLine) : Prop :=
  ∀ k, k ∈ highAnchors W Z0 → initialLongPrefix W k = p →
    line.Contains
      (W.enumeration.a (k - W.s) + p.span : ℤ)
      (carryInt W.rational (W.enumeration.a (k - W.s) + p.span))

private theorem highAnchor_offset_le (W : WindowSystem) (Z0 k : ℕ)
    (hk : k ∈ highAnchors W Z0) : W.s ≤ k := by
  classical
  rw [highAnchors, Finset.mem_filter] at hk
  rcases hk.2 with ⟨T, hT, hlarge⟩
  by_contra hnot
  have hspan : W.rawWindowSpan k = 0 := by
    simp [WindowSystem.rawWindowSpan, hnot]
  have hTnonneg : 0 ≤ T := le_trans (by positivity) hT.1
  have hexcess : W.excess (k, T) = 0 := by
    rw [WindowSystem.excess, hspan]
    simp only [Nat.cast_zero, zero_sub]
    rw [max_eq_right]
    have heps : 0 ≤ W.epsilon * W.L :=
      mul_nonneg W.epsilon_nonneg (by positivity)
    linarith
  rw [hexcess] at hlarge
  have hnonneg : (0 : ℝ) ≤ W.m * Z0 := by positivity
  linarith

/-- Once a prefix has at least two occurrences, its geometric occurrence
line is canonical: every raw occurrence-line witness reduces to the same
primitive direction and intercept. -/
theorem occurrenceLines_canonical_eq_of_frequent
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (hcutoff : 1 < frequencyCutoff W)
    (hfrequent : IsFrequentPrefix W Z0 p)
    (u v : AffineLine)
    (hu : IsOccurrenceLine W Z0 p u)
    (hv : IsOccurrenceLine W Z0 p v) :
    u.canonicalGeometricLine = v.canonicalGeometricLine := by
  classical
  let fibre := (highAnchors W Z0).filter fun k => initialLongPrefix W k = p
  have hcardReal : (1 : ℝ) < (fibre.card : ℝ) :=
    lt_of_lt_of_le hcutoff hfrequent
  have hcard : 1 < fibre.card := by exact_mod_cast hcardReal
  obtain ⟨k₁, hk₁, k₂, hk₂, hkne⟩ := Finset.one_lt_card.mp hcard
  have hk₁' := Finset.mem_filter.mp hk₁
  have hk₂' := Finset.mem_filter.mp hk₂
  let x₁ : ℤ := W.enumeration.a (k₁ - W.s) + p.span
  let x₂ : ℤ := W.enumeration.a (k₂ - W.s) + p.span
  let r₁ : ℤ := carryInt W.rational
    (W.enumeration.a (k₁ - W.s) + p.span)
  let r₂ : ℤ := carryInt W.rational
    (W.enumeration.a (k₂ - W.s) + p.span)
  have hs₁ := highAnchor_offset_le W Z0 k₁ hk₁'.1
  have hs₂ := highAnchor_offset_le W Z0 k₂ hk₂'.1
  have hind : k₁ - W.s ≠ k₂ - W.s := by omega
  have hx : x₁ ≠ x₂ := by
    intro heq
    have henum : W.enumeration.a (k₁ - W.s) =
        W.enumeration.a (k₂ - W.s) := by
      have hsumInt :
          (W.enumeration.a (k₁ - W.s) : ℤ) + p.span =
            W.enumeration.a (k₂ - W.s) + p.span := by
        simpa only [x₁, x₂] using heq
      have hsumNat : W.enumeration.a (k₁ - W.s) + p.span =
          W.enumeration.a (k₂ - W.s) + p.span := by
        exact_mod_cast hsumInt
      exact Nat.add_right_cancel hsumNat
    exact hind (W.enumeration.strictMono.injective henum)
  have hu₁ : u.Contains x₁ r₁ := hu k₁ hk₁'.1 hk₁'.2
  have hu₂ : u.Contains x₂ r₂ := hu k₂ hk₂'.1 hk₂'.2
  have hv₁ : v.Contains x₁ r₁ := hv k₁ hk₁'.1 hk₁'.2
  have hv₂ : v.Contains x₂ r₂ := hv k₂ hk₂'.1 hk₂'.2
  apply GeometricLine.eq_of_two_common_points
    u.canonicalGeometricLine v.canonicalGeometricLine x₁ r₁ x₂ r₂ hx
  · exact u.contains_canonicalGeometricLine x₁ r₁ hu₁
  · exact u.contains_canonicalGeometricLine x₂ r₂ hu₂
  · exact v.contains_canonicalGeometricLine x₁ r₁ hv₁
  · exact v.contains_canonicalGeometricLine x₂ r₂ hv₂

/-- The actual suffix of an anchored gap window after its deterministic
initial long prefix. -/
def actualPostPrefixGaps (W : WindowSystem) (k : ℕ) : GapWord :=
  (W.rawWindowGapWord k).drop (initialLongPrefix W k).length

/-- Genuine anchored gap words consist only of positive support gaps. -/
theorem rawWindowGapWord_positive (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).Positive := by
  unfold WindowSystem.rawWindowGapWord
  split
  next hk =>
    change ∀ g, g ∈
      (List.range (W.s + 1)).map
        (fun j => supportGap W.enumeration (k - W.s + j)) → 0 < g
    intro g hg
    obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hg
    exact (supportGap_isSupportGap W.enumeration (k - W.s + j)).1
  next => simp [GapWord.Positive]

/-- An order-`m` anchored word contains at most `m` gaps. -/
theorem rawWindowGapWord_length_le (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).length ≤ W.m := by
  unfold WindowSystem.rawWindowGapWord
  split
  next hk => simp [WindowSystem.window, windowGapWord, WindowSystem.m]
  next => simp [WindowSystem.m]

theorem actualPostPrefixGaps_positive (W : WindowSystem) (k : ℕ) :
    (actualPostPrefixGaps W k).Positive := by
  intro g hg
  exact rawWindowGapWord_positive W k g (List.mem_of_mem_drop hg)

theorem actualPostPrefixGaps_length_le (W : WindowSystem) (k : ℕ) :
    (actualPostPrefixGaps W k).length ≤ W.m := by
  rw [actualPostPrefixGaps, List.length_drop]
  exact (Nat.sub_le _ _).trans (rawWindowGapWord_length_le W k)

theorem initialLongPrefix_append_actualPostPrefixGaps
    (W : WindowSystem) (k : ℕ) :
    initialLongPrefix W k ++ actualPostPrefixGaps W k =
      W.rawWindowGapWord k := by
  let w := W.rawWindowGapWord k
  let p := initialLongPrefix W k
  obtain ⟨tail, htail⟩ := GapWord.firstPrefixAbove_isPrefix
    (W.rawWindowGapWord k) (Nat.floor (W.structural.Caff * W.L))
  have hpw : p ++ tail = w := by
    simpa [p, w, initialLongPrefix] using htail
  change p ++ w.drop p.length = w
  have htake : w.take p.length = p := by
    rw [← hpw]
    simp
  simpa only [htake] using List.take_append_drop p.length w

theorem actualPostPrefixGaps_span (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).span =
      (initialLongPrefix W k).span + (actualPostPrefixGaps W k).span := by
  rw [← initialLongPrefix_append_actualPostPrefixGaps W k]
  exact List.sum_append

/-- A shared continuation beginning at the post-prefix occurrence line and
using an actual initial subword of the anchored suffix. -/
def IsActualInitialContinuation (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (line : AffineLine) (gaps : GapWord) : Prop :=
  IsOccurrenceLine W Z0 (initialLongPrefix W e.1) line ∧
    gaps.IsPrefix (actualPostPrefixGaps W e.1) ∧
    ∃ finish : AffineLine,
      SharedGapTrajectory W.rational.eta.den line gaps finish

/-- A shared continuation beginning later in the same actual anchored suffix.
The prefix trajectory determines the line at which `gaps` begins. -/
def IsActualContinuationAt (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (line : AffineLine) (gaps : GapWord) : Prop :=
  ∃ base finish : AffineLine, ∃ before after : GapWord,
    IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base ∧
      actualPostPrefixGaps W e.1 = before ++ gaps ++ after ∧
      SharedGapTrajectory W.rational.eta.den base before line ∧
      SharedGapTrajectory W.rational.eta.den line gaps finish

/-- A continuation beginning at the first exterior state of the actual
anchored suffix.  Every proper prefix of `before` is still non-exterior, and
the complete prefix reaches the exterior line at which `gaps` starts. -/
def IsActualFirstExteriorContinuation (W : WindowSystem) (Z0 : ℕ)
    (e : WindowThreshold) (line : AffineLine) (gaps : GapWord) : Prop :=
  ∃ base finish : AffineLine, ∃ before after : GapWord,
    IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base ∧
      actualPostPrefixGaps W e.1 = before ++ gaps ++ after ∧
      SharedGapTrajectory W.rational.eta.den base before line ∧
      (∀ r < before.length, ∀ state : AffineLine,
        SharedGapTrajectory W.rational.eta.den base (before.take r) state →
          classifySlope (state.slope W.rational.eta.den) ≠ .exterior) ∧
      classifySlope (line.slope W.rational.eta.den) = .exterior ∧
      SharedGapTrajectory W.rational.eta.den line gaps finish

/-- A pair has a long interior continuation in the genuine slope dynamics. -/
def LongInteriorPair (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold) : Prop :=
  e ∈ W.largePairs Z0 ∧ IsFrequentPrefix W Z0 (initialLongPrefix W e.1) ∧
    ∃ line : AffineLine, ∃ gaps : GapWord,
      IsActualInitialContinuation W Z0 e line gaps ∧
      IsInteriorTrajectory W.rational.eta.den line gaps ∧
      W.excess e / 8 ≤ gaps.span

/-- Complementary pair with a long exterior continuation. -/
def LongExteriorPair (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold) : Prop :=
  e ∈ W.largePairs Z0 ∧ IsFrequentPrefix W Z0 (initialLongPrefix W e.1) ∧
    ¬ LongInteriorPair W Z0 e ∧
    ∃ line : AffineLine, ∃ gaps : GapWord,
      IsActualFirstExteriorContinuation W Z0 e line gaps ∧
      IsExteriorTrajectory W.rational.eta.den line gaps ∧
      W.excess e / 4 ≤ gaps.span

def interiorPairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  {e | LongInteriorPair W Z0 e}

def exteriorPairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  {e | LongExteriorPair W Z0 e}

/-- Entropy exponent `Δ` used for initial prefixes. -/
def initialPrefixExponent (p : EntropyParams) : ℝ :=
  (p.structural.Caff + 1) *
    binaryEntropy (p.kappa / (p.structural.Caff + 1))

/-! The next few private lemmas provide the finite combinatorial model used
for the initial-prefix count.  A positive word is encoded by its strictly
increasing list of cumulative sums. -/

private def cumulativeSums : GapWord → List ℕ
  | [] => []
  | g :: gs => g :: (cumulativeSums gs).map (g + ·)

@[simp] private theorem cumulativeSums_nil : cumulativeSums [] = [] := rfl

@[simp] private theorem cumulativeSums_cons (g : ℕ) (gs : GapWord) :
    cumulativeSums (g :: gs) = g :: (cumulativeSums gs).map (g + ·) := rfl

private theorem cumulativeSums_length (w : GapWord) :
    (cumulativeSums w).length = w.length := by
  induction w with
  | nil => rfl
  | cons g gs ih => simp [cumulativeSums, ih]

private theorem cumulativeSums_pos {w : GapWord}
    (hpos : ∀ g ∈ w, 0 < g) :
    ∀ x ∈ cumulativeSums w, 0 < x := by
  induction w with
  | nil => simp
  | cons g gs ih =>
      have hg : 0 < g := hpos g (by simp)
      have htail : ∀ x ∈ gs, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      intro x hx
      simp only [cumulativeSums_cons, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact hg
      · exact Nat.add_pos_right g (ih htail y hy)

private theorem cumulativeSums_pairwise {w : GapWord}
    (hpos : ∀ g ∈ w, 0 < g) :
    (cumulativeSums w).Pairwise (· < ·) := by
  induction w with
  | nil => simp
  | cons g gs ih =>
      have hg : 0 < g := hpos g (by simp)
      have htail : ∀ x ∈ gs, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      rw [cumulativeSums_cons, List.pairwise_cons]
      constructor
      · intro x hx
        rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hypos := cumulativeSums_pos htail y hy
        omega
      · rw [List.pairwise_map]
        exact (ih htail).imp (by intro a b hab; omega)

private theorem cumulativeSums_le_span {w : GapWord}
    (hpos : ∀ g ∈ w, 0 < g) :
    ∀ x ∈ cumulativeSums w, x ≤ w.span := by
  induction w with
  | nil => simp
  | cons g gs ih =>
      have htail : ∀ x ∈ gs, 0 < x := by
        intro x hx
        exact hpos x (by simp [hx])
      intro x hx
      simp only [cumulativeSums_cons, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · simp [GapWord.span]
      · have hy_le : y ≤ gs.sum := by
          simpa only [GapWord.span] using ih htail y hy
        simp only [GapWord.span, List.sum_cons]
        omega

private theorem cumulativeSums_injective : Function.Injective cumulativeSums := by
  intro w
  induction w with
  | nil =>
      intro v hv
      cases v with
      | nil => rfl
      | cons g gs => simp at hv
  | cons g gs ih =>
      intro v hv
      cases v with
      | nil => simp at hv
      | cons h hs =>
          simp only [cumulativeSums_cons] at hv
          have hgh : g = h := (List.cons.inj hv).1
          subst h
          have htail : cumulativeSums gs = cumulativeSums hs := by
            have hm : (cumulativeSums gs).map (g + ·) =
                (cumulativeSums hs).map (g + ·) := by
              exact List.cons.inj hv |>.2
            exact Function.Injective.list_map
              (fun _ _ hab => Nat.add_left_cancel hab) hm
          exact congrArg (g :: ·) (ih htail)

private theorem perm_of_nodup_toFinset_eq {u v : List ℕ}
    (hu : u.Nodup) (hv : v.Nodup) (hset : u.toFinset = v.toFinset) :
    u.Perm v := by
  rw [List.perm_iff_count]
  intro x
  rw [hu.count, hv.count]
  have hmem : x ∈ u ↔ x ∈ v := by
    rw [← List.mem_toFinset, ← List.mem_toFinset, hset]
  simp only [hmem]

private theorem cumulativeEncoding_injective_on_positive :
    Set.InjOn (fun w : GapWord => (cumulativeSums w).toFinset)
      {w | ∀ g ∈ w, 0 < g} := by
  intro u hu v hv henc
  have hpu := cumulativeSums_pairwise hu
  have hpv := cumulativeSums_pairwise hv
  have hperm : (cumulativeSums u).Perm (cumulativeSums v) :=
    perm_of_nodup_toFinset_eq hpu.nodup hpv.nodup henc
  have heq : cumulativeSums u = cumulativeSums v :=
    hperm.eq_of_pairwise' hpu hpv
  exact cumulativeSums_injective heq

theorem positiveGapWords_card_le_compositions (words : Finset GapWord)
    (H rMax : ℕ)
    (hpositive : ∀ p ∈ words, ∀ g ∈ p, 0 < g)
    (hspan : ∀ p ∈ words, p.span ≤ H)
    (hlength : ∀ p ∈ words, p.length ≤ rMax) :
    words.card ≤
      ∑ r ∈ Finset.Icc 0 rMax,
        H.choose r := by
  classical
  let target : Finset (Finset ℕ) :=
    (Finset.Icc 0 rMax).biUnion fun r =>
      Finset.powersetCard r (Finset.Icc 1 H)
  have hmaps : Set.MapsTo
      (fun w : GapWord => (cumulativeSums w).toFinset)
      (words : Set GapWord) (target : Set (Finset ℕ)) := by
    intro p hp
    have hcard : (cumulativeSums p).toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup (cumulativeSums_pairwise
        (hpositive p hp)).nodup, cumulativeSums_length]
    have hsubset : (cumulativeSums p).toFinset ⊆ Finset.Icc 1 H := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_Icc]
      constructor
      · exact cumulativeSums_pos (hpositive p hp) x hx
      · exact (cumulativeSums_le_span (hpositive p hp) x hx).trans (hspan p hp)
    simp only [Finset.mem_coe, target, Finset.mem_biUnion]
    refine ⟨p.length, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hlength p hp⟩
    · exact Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩
  calc
    words.card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hmaps
        (cumulativeEncoding_injective_on_positive.mono (by
          intro p hp
          exact hpositive p hp))
    _ ≤ ∑ r ∈ Finset.Icc 0 rMax,
          (Finset.powersetCard r (Finset.Icc 1 H)).card :=
      Finset.card_biUnion_le
    _ = ∑ r ∈ Finset.Icc 0 rMax, H.choose r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.card_powersetCard, Nat.card_Icc]
      congr 1

/-- Positive gap words of bounded span and bounded length form a finite set.
This is the set-level companion to `positiveGapWords_card_le_compositions`. -/
theorem positiveGapWords_bounded_finite (H rMax : ℕ) :
    {w : GapWord |
      (∀ g ∈ w, 0 < g) ∧ w.span ≤ H ∧ w.length ≤ rMax}.Finite := by
  classical
  let E : Set GapWord :=
    {w : GapWord |
      (∀ g ∈ w, 0 < g) ∧ w.span ≤ H ∧ w.length ≤ rMax}
  let target : Finset (Finset ℕ) :=
    (Finset.Icc 0 rMax).biUnion fun r =>
      Finset.powersetCard r (Finset.Icc 1 H)
  let encode : GapWord → Finset ℕ :=
    fun w => (cumulativeSums w).toFinset
  have hmaps : Set.MapsTo encode E (target : Set (Finset ℕ)) := by
    intro w hw
    have hcard : (encode w).card = w.length := by
      dsimp [encode]
      rw [List.toFinset_card_of_nodup (cumulativeSums_pairwise hw.1).nodup,
        cumulativeSums_length]
    have hsubset : encode w ⊆ Finset.Icc 1 H := by
      intro x hx
      dsimp [encode] at hx
      rw [List.mem_toFinset] at hx
      exact Finset.mem_Icc.mpr ⟨cumulativeSums_pos hw.1 x hx,
        (cumulativeSums_le_span hw.1 x hx).trans hw.2.1⟩
    simp only [target, Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨w.length, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hw.2.2⟩,
      Finset.mem_powersetCard.mpr ⟨hsubset, hcard⟩⟩
  have himage : encode '' E ⊆ (target : Set (Finset ℕ)) := by
    rintro y ⟨w, hw, rfl⟩
    exact hmaps hw
  have hfiniteImage : (encode '' E).Finite := target.finite_toSet.subset himage
  have hinj : Set.InjOn encode E := by
    exact cumulativeEncoding_injective_on_positive.mono (by
      intro w hw
      exact hw.1)
  simpa only [E] using Set.Finite.of_finite_image hfiniteImage hinj

theorem sum_choose_Icc_zero_eq_shift (H m : ℕ) :
    (∑ r ∈ Finset.Icc 0 m, H.choose r) =
      ∑ q ∈ Finset.Icc 1 (m + 1), H.choose (q - 1) := by
  apply Finset.sum_bij (fun r _ => r + 1)
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  · intro r₁ hr₁ r₂ hr₂ h
    omega
  · intro q hq
    simp only [Finset.mem_Icc] at hq
    refine ⟨q - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro r hr
    simp

theorem tendsto_natFloor_affine_div (a c : ℝ)
    (ha : 0 < a) (hc : 0 ≤ c) :
    Tendsto
      (fun L : ℕ =>
        (Nat.floor (a * (L : ℝ) + c) : ℝ) / (L : ℝ))
      atTop (𝓝 a) := by
  have hlo : Tendsto
      (fun L : ℕ => a + (c - 1) / (L : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))
  have hhi : Tendsto
      (fun L : ℕ => a + c / (L : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hxlt := Nat.lt_floor_add_one (a * (L : ℝ) + c)
    have hnum : a * (L : ℝ) + c - 1 <
        (Nat.floor (a * (L : ℝ) + c) : ℝ) := by
      linarith
    have hdiv := (div_lt_div_iff_of_pos_right hLpos).2 hnum
    have heq : a + (c - 1) / (L : ℝ) =
        (a * (L : ℝ) + c - 1) / (L : ℝ) := by
      field_simp
      ring
    rw [heq]
    exact hdiv.le
  · filter_upwards [eventually_ge_atTop 1] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hxnonneg : 0 ≤ a * (L : ℝ) + c := by positivity
    have hnum := Nat.floor_le hxnonneg
    have hdiv := (div_le_div_iff_of_pos_right hLpos).2 hnum
    have heq : a + c / (L : ℝ) =
        (a * (L : ℝ) + c) / (L : ℝ) := by
      field_simp
    rw [heq]
    exact hdiv

theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  rw [show binaryEntropy = fun x => Real.binEntropy x / Real.log 2 by
    funext x
    rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, Real.logb]
    field_simp
    ring]
  exact Real.binEntropy_continuous.div_const _

private def initialCountSpanCap (context : FixedScaleContext) (CQ : ℝ) (L : ℕ) : ℕ :=
  Nat.floor
    ((context.structural.Caff + 1) * (L : ℝ) + CQ)

private def initialCountAlpha (context : FixedScaleContext) (CQ : ℝ) (L : ℕ) : ℝ :=
  ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
    ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)

private theorem binaryEntropy_half : binaryEntropy (1 / 2 : ℝ) = 1 := by
  rw [binaryEntropy]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hhalf]
  simp only [Real.logb, Real.log_inv]
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

private theorem initialCountAlpha_tendsto (context : FixedScaleContext)
    (CQ : ℝ) (hCQ : 0 ≤ CQ) :
    Tendsto (initialCountAlpha context CQ) atTop
      (𝓝 (context.entropy.kappa / (context.structural.Caff + 1))) := by
  let A : ℝ := context.structural.Caff + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith [context.structural.Caff_gt]
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have honeDiv : Tendsto (fun L : ℕ => (1 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hcapFloor : Tendsto
      (fun L : ℕ =>
        (initialCountSpanCap context CQ L : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    simpa only [initialCountSpanCap, A] using
      tendsto_natFloor_affine_div A CQ hA hCQ
  have hcap : Tendsto
      (fun L : ℕ =>
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    convert hcapFloor.add honeDiv using 1 <;> simp [Nat.cast_add, add_div]
  have hkFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    simpa using tendsto_natFloor_affine_div context.entropy.kappa 0
      context.entropy.kappa_pos (le_refl 0)
  have htwoDiv : Tendsto (fun L : ℕ => (2 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hnum : Tendsto
      (fun L : ℕ =>
        ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    convert hkFloor.add htwoDiv using 1 <;> simp [Nat.cast_add, add_div]
  have hquot := hnum.div hcap (ne_of_gt hA)
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  dsimp [initialCountAlpha]
  field_simp

private def initialCountError (context : FixedScaleContext) (CQ : ℝ) (L : ℕ) : ℝ :=
  if L = 0 then 0 else
    |(((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (initialCountAlpha context CQ L) -
        initialPrefixExponent context.entropy| +
      2 * Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
        ((L : ℝ) * Real.log 2)

private theorem initialCountError_tendsto_zero (context : FixedScaleContext)
    (CQ : ℝ) (hCQ : 0 ≤ CQ) :
    Tendsto (initialCountError context CQ) atTop (𝓝 0) := by
  let A : ℝ := context.structural.Caff + 1
  have hA : 0 < A := by
    dsimp [A]
    linarith [context.structural.Caff_gt]
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have honeDiv : Tendsto (fun L : ℕ => (1 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hcapFloor : Tendsto
      (fun L : ℕ =>
        (initialCountSpanCap context CQ L : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    simpa only [initialCountSpanCap, A] using
      tendsto_natFloor_affine_div A CQ hA hCQ
  have hcap : Tendsto
      (fun L : ℕ =>
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    convert hcapFloor.add honeDiv using 1 <;> simp [Nat.cast_add, add_div]
  have hkFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    simpa using tendsto_natFloor_affine_div context.entropy.kappa 0
      context.entropy.kappa_pos (le_refl 0)
  have htwoDiv : Tendsto (fun L : ℕ => (2 : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hnum : Tendsto
      (fun L : ℕ =>
        ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (L : ℝ))
      atTop (𝓝 context.entropy.kappa) := by
    convert hkFloor.add htwoDiv using 1 <;> simp [Nat.cast_add, add_div]
  have halpha : Tendsto (initialCountAlpha context CQ) atTop
      (𝓝 (context.entropy.kappa / A)) := by
    have hquot := hnum.div hcap hA0
    apply hquot.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [initialCountAlpha]
    field_simp
  have hentropy : Tendsto
      (fun L => binaryEntropy (initialCountAlpha context CQ L))
      atTop (𝓝 (binaryEntropy (context.entropy.kappa / A))) :=
    binaryEntropy_continuous.continuousAt.tendsto.comp halpha
  have hmain : Tendsto
      (fun L : ℕ =>
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ) *
          binaryEntropy (initialCountAlpha context CQ L))
      atTop (𝓝 (initialPrefixExponent context.entropy)) := by
    have := hcap.mul hentropy
    rw [initialPrefixExponent, context.entropy_structural]
    simpa only [A] using this
  have habs : Tendsto
      (fun L : ℕ =>
        |(((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L) -
          initialPrefixExponent context.entropy|)
      atTop (𝓝 0) := by
    have hconst : Tendsto
        (fun _ : ℕ => initialPrefixExponent context.entropy)
        atTop (𝓝 (initialPrefixExponent context.entropy)) := tendsto_const_nhds
    simpa using (hmain.sub hconst).abs
  have hxTop : Tendsto
      (fun L : ℕ => A * (L : ℝ) + CQ) atTop atTop := by
    have hmul : Tendsto (fun L : ℕ => A * (L : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hA hnatTop
    exact Filter.tendsto_atTop_mono
      (fun L => le_add_of_nonneg_right hCQ) hmul
  have hcapNatTop : Tendsto
      (fun L : ℕ => initialCountSpanCap context CQ L + 1) atTop atTop := by
    have hfloor : Tendsto
        (fun L : ℕ => initialCountSpanCap context CQ L) atTop atTop := by
      simpa only [initialCountSpanCap, A, Function.comp_def] using
        tendsto_nat_floor_atTop.comp hxTop
    exact Filter.tendsto_atTop_mono (fun L => Nat.le_succ _) hfloor
  have hcapRealTop : Tendsto
      (fun L : ℕ => ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ))
      atTop atTop := hnatTop.comp hcapNatTop
  have hlogOverCap : Tendsto
      (fun L : ℕ =>
        Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcapRealTop
  have hlogOverL : Tendsto
      (fun L : ℕ =>
        Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          (L : ℝ))
      atTop (𝓝 0) := by
    have hprod := hlogOverCap.mul hcap
    have hprod' : Tendsto
        (fun L : ℕ =>
          Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
              (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) *
            (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    have hcapPos : (0 : ℝ) <
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) := by positivity
    field_simp [hL0, ne_of_gt hcapPos]
  have hpoly : Tendsto
      (fun L : ℕ =>
        2 * Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hsimple : Tendsto
        (fun L : ℕ =>
          (2 * (Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
            (L : ℝ))) / Real.log 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hlogOverL).div_const (Real.log 2)
    apply hsimple.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    field_simp [hL0, hlog2]
  have hsum : Tendsto
      (fun L : ℕ =>
        |(((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L) -
          initialPrefixExponent context.entropy| +
        2 * Real.log (((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by simpa using habs.add hpoly
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [initialCountError, Nat.ne_of_gt hL, if_false]

private theorem initialPrefixes_card_le_compositions (W : WindowSystem)
    (Z0 H : ℕ)
    (hspan : ∀ p ∈ initialPrefixes W Z0, p.span ≤ H) :
    (initialPrefixes W Z0).card ≤
      ∑ r ∈ Finset.Icc 0 W.m,
        H.choose r := by
  have hpositive : ∀ p ∈ initialPrefixes W Z0, ∀ g ∈ p, 0 < g := by
    intro p hp g hg
    rw [initialPrefixes, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    have hpref := GapWord.firstPrefixAbove_isPrefix
      (W.rawWindowGapWord k)
      (Nat.floor (W.structural.Caff * W.L))
    have hgraw : g ∈ W.rawWindowGapWord k := hpref.subset hg
    unfold WindowSystem.rawWindowGapWord at hgraw
    split at hgraw
    next hsk =>
      simp only [WindowSystem.window, windowGapWord, List.mem_map,
        List.mem_range] at hgraw
      rcases hgraw with ⟨j, hj, rfl⟩
      exact (supportGap_isSupportGap W.enumeration _).1
    next hsk => simp at hgraw
  have hlength : ∀ p ∈ initialPrefixes W Z0, p.length ≤ W.m := by
    intro p hp
    rw [initialPrefixes, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    have hpref := GapWord.firstPrefixAbove_isPrefix
      (W.rawWindowGapWord k)
      (Nat.floor (W.structural.Caff * W.L))
    calc
      (initialLongPrefix W k).length ≤ (W.rawWindowGapWord k).length :=
        List.IsPrefix.length_le hpref
      _ ≤ W.m := by
        unfold WindowSystem.rawWindowGapWord
        split
        · simp [WindowSystem.window, windowGapWord, WindowSystem.m]
        · exact Nat.zero_le _
  exact positiveGapWords_card_le_compositions _ H W.m hpositive hspan hlength

/-- Every gap occurring in an anchored order-`m` word is eventually bounded
by `L + Cgap + 1`.  The finitely many support points below the uniform
starting point `x0` are absorbed into the family-dependent lower bound on
`L`; all later points use the denominator-uniform gap theorem. -/
theorem eventually_rawWindowGap_le (context : FixedScaleContext)
    (gap : GapParams context.Q) (F : ScaleFamily)
    (hF : F.MatchesContext context) :
    ∀ᶠ L : ℕ in atTop, ∀ k : ℕ, k ∈ (F.system L).anchors →
      ∀ g ∈ (F.system L).rawWindowGapWord k,
        g ≤ L + gap.Cgap + 1 := by
  let earlyBound :=
    (Finset.range gap.x0).sup fun i => supportGap F.enumeration i
  filter_upwards [eventually_ge_atTop earlyBound] with L hL
  intro k hk g hg
  have hkUpper : (F.system L).enumeration.a k ≤ 2 * (F.system L).X :=
    (Finset.mem_filter.mp hk).2.2
  unfold WindowSystem.rawWindowGapWord at hg
  split at hg
  next hsk =>
    simp only [WindowSystem.window, windowGapWord, List.mem_map,
      List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    let i := k - (F.system L).s + j
    have hi_le_k : i ≤ k := by
      dsimp [i]
      omega
    have hiIndex : i < F.enumeration.a i :=
      supportEnumeration_index_lt F.enumeration i
    have henum_i : (F.system L).enumeration.a i = F.enumeration.a i :=
      F.enumeration_eq L i
    have henum_k : (F.system L).enumeration.a k = F.enumeration.a k :=
      F.enumeration_eq L k
    have hsupportGap :
        supportGap (F.system L).enumeration i = supportGap F.enumeration i := by
      simp only [supportGap, F.enumeration_eq]
    rw [hsupportGap]
    by_cases hearly : F.enumeration.a i < gap.x0
    · have hiRange : i ∈ Finset.range gap.x0 := by
        simp only [Finset.mem_range]
        exact hiIndex.trans hearly
      have hgapEarly : supportGap F.enumeration i ≤ earlyBound := by
        exact Finset.le_sup (f := fun t => supportGap F.enumeration t) hiRange
      omega
    · have hx0 : gap.x0 ≤ F.enumeration.a i := Nat.le_of_not_gt hearly
      have hden : F.rational.eta.den = context.Q := hF.1
      have hgap := gap.bound F.rational hden (F.enumeration.a i) hx0
        (supportGap F.enumeration i)
        (supportGap_isSupportGap F.enumeration i)
      have hai_le_hak : F.enumeration.a i ≤ F.enumeration.a k :=
        F.enumeration.strictMono.monotone hi_le_k
      have hai_le_scale : F.enumeration.a i ≤ 2 * dyadicScale L := by
        calc
          F.enumeration.a i ≤ F.enumeration.a k := hai_le_hak
          _ = (F.system L).enumeration.a k := henum_k.symm
          _ ≤ 2 * (F.system L).X := hkUpper
          _ = 2 * dyadicScale L := by
            rw [WindowSystem.X, F.level_eq]
      have hlog : Nat.log 2 (F.enumeration.a i) ≤ L + 1 := by
        calc
          Nat.log 2 (F.enumeration.a i) ≤
              Nat.log 2 (2 * dyadicScale L) := Nat.log_mono_right hai_le_scale
          _ = L + 1 := by
            rw [dyadicScale, show 2 * 2 ^ L = 2 ^ (L + 1) by
              rw [pow_succ]
              omega]
            exact Nat.log_pow Nat.one_lt_two (L + 1)
      omega
  next hsk => simp at hg

private theorem rawWindowGapWord_span (W : WindowSystem) (k : ℕ) :
    (W.rawWindowGapWord k).span = W.rawWindowSpan k := by
  unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
  split <;> rfl

/-- Paper label: `lem:firstdeep-exists` (Section 5).  The overshoot constant
is selected from the denominator-level context before the cutoff, rational
numerator, or support family. -/
theorem lem_firstdeep_exists (context : FixedScaleContext) :
    ∃ CQ : ℝ, 0 ≤ CQ ∧ ∀ Z0 : ℕ,
      Nat.ceil
          (2 * context.structural.Caff / context.entropy.kappa) ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop,
          ∀ e : WindowThreshold, e ∈ (F.system L).largePairs Z0 →
            let p := initialLongPrefix (F.system L) e.1
            (F.system L).structural.Caff * (F.system L).L < p.span ∧
              (p.span : ℝ) ≤
                ((F.system L).structural.Caff + 1) *
                    (F.system L).L + CQ ∧
              (F.system L).excess e / 2 ≤
                (F.system L).rawWindowSpan e.1 - p.span := by
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  let CQ : ℝ := gap.Cgap + 1
  refine ⟨CQ, by positivity, ?_⟩
  intro Z0 hZ0 F hF
  filter_upwards [eventually_rawWindowGap_le context gap F hF,
    eventually_ge_atTop (gap.Cgap + 2)] with L hgap hL
  intro e he
  dsimp only
  let p := initialLongPrefix (F.system L) e.1
  have hstruct : (F.system L).structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hpEq : p =
      ((F.system L).rawWindowGapWord e.1).firstPrefixAbove
        (Nat.floor (context.structural.Caff * (L : ℝ))) := by
    dsimp [p, initialLongPrefix]
    rw [F.level_eq, hstruct]
  have hs : (F.system L).s =
      Nat.floor (context.entropy.kappa * (L : ℝ)) := by
    rw [F.offset_eq, hF.2.2.1]
  have hLposNat : 0 < L := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposNat
  have hCaffPos : 0 < context.structural.Caff :=
    lt_trans (by norm_num) context.structural.Caff_gt
  have hcutReal :
      2 * context.structural.Caff / context.entropy.kappa ≤ (Z0 : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hZ0)
  have hcoeff :
      2 * context.structural.Caff ≤ context.entropy.kappa * (Z0 : ℝ) := by
    have := (div_le_iff₀ context.entropy.kappa_pos).mp hcutReal
    simpa [mul_comm] using this
  have hZpos : (0 : ℝ) < Z0 := by
    have hquot : 0 <
        2 * context.structural.Caff / context.entropy.kappa :=
      div_pos (mul_pos (by norm_num) hCaffPos) context.entropy.kappa_pos
    exact hquot.trans_le hcutReal
  have hmLower :
      context.entropy.kappa * (L : ℝ) < ((F.system L).m : ℝ) := by
    rw [WindowSystem.m, hs]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (context.entropy.kappa * (L : ℝ)))
  have hmassLower :
      2 * context.structural.Caff * (L : ℝ) <
        ((F.system L).m : ℝ) * (Z0 : ℝ) := by
    have h₁ :
        2 * context.structural.Caff * (L : ℝ) ≤
          (context.entropy.kappa * (Z0 : ℝ)) * L := by
      exact mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg L)
    have h₂ :
        (context.entropy.kappa * (Z0 : ℝ)) * L <
          ((F.system L).m : ℝ) * Z0 := by
      have := mul_lt_mul_of_pos_right hmLower hZpos
      nlinarith
    exact h₁.trans_lt h₂
  have hlarge :
      ((F.system L).m : ℝ) * (Z0 : ℝ) < (F.system L).excess e := by
    simpa only [Set.mem_setOf_eq] using he.2
  have hexcessLower :
      2 * context.structural.Caff * (L : ℝ) <
        (F.system L).excess e := hmassLower.trans hlarge
  have hexcessPos : 0 < (F.system L).excess e := by
    have hbase : 0 < 2 * context.structural.Caff * (L : ℝ) := by positivity
    exact hbase.trans hexcessLower
  have hsk : (F.system L).s ≤ e.1 := by
    by_contra hnot
    have hraw : (F.system L).rawWindowSpan e.1 = 0 := by
      simp [WindowSystem.rawWindowSpan, hnot]
    have hupper := (F.system L).excess_le_rawWindowSpan e he.1
    rw [hraw, Nat.cast_zero] at hupper
    linarith
  have hrawUpper := (F.system L).excess_le_rawWindowSpan e he.1
  have hrawReal :
      context.structural.Caff * (L : ℝ) <
        ((F.system L).rawWindowSpan e.1 : ℝ) := by
    have hdouble :
        context.structural.Caff * (L : ℝ) <
          2 * context.structural.Caff * L := by nlinarith
    exact hdouble.trans (hexcessLower.trans_le hrawUpper)
  have hfloorNonneg :
      0 ≤ context.structural.Caff * (L : ℝ) := by positivity
  have hfloorCross :
      Nat.floor (context.structural.Caff * (L : ℝ)) <
        (F.system L).rawWindowSpan e.1 := by
    exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hfloorNonneg) hrawReal)
  have hwordCross :
      Nat.floor (context.structural.Caff * (L : ℝ)) <
        ((F.system L).rawWindowGapWord e.1).span := by
    simpa only [rawWindowGapWord_span] using hfloorCross
  have hpLowerNat :
      Nat.floor (context.structural.Caff * (L : ℝ)) < p.span := by
    rw [hpEq]
    exact GapWord.lt_span_firstPrefixAbove_of_lt_span _ _ hwordCross
  have hpLower :
      context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
    have hnext :=
      Nat.lt_floor_add_one (context.structural.Caff * (L : ℝ))
    have hsucc : Nat.floor (context.structural.Caff * (L : ℝ)) + 1 ≤ p.span :=
      Nat.succ_le_iff.mpr hpLowerNat
    exact hnext.trans_le (by exact_mod_cast hsucc)
  have hpCap : ∀ g ∈ (F.system L).rawWindowGapWord e.1,
      g ≤ L + gap.Cgap + 1 := hgap e.1 he.1.1
  have hpUpperNat : p.span ≤
      Nat.floor (context.structural.Caff * (L : ℝ)) +
        (L + gap.Cgap + 1) := by
    rw [hpEq]
    exact GapWord.span_firstPrefixAbove_le_add _ _ _ hpCap
  have hpUpper : (p.span : ℝ) ≤
      (context.structural.Caff + 1) * (L : ℝ) + CQ := by
    have hfloor := Nat.floor_le hfloorNonneg
    dsimp [CQ]
    have hpUpperCast : (p.span : ℝ) ≤
        (Nat.floor (context.structural.Caff * (L : ℝ)) : ℝ) +
          ((L : ℝ) + gap.Cgap + 1) := by exact_mod_cast hpUpperNat
    nlinarith
  have hpSpanLe : p.span ≤ (F.system L).rawWindowSpan e.1 := by
    rw [← rawWindowGapWord_span]
    rw [hpEq]
    exact GapWord.span_firstPrefixAbove_le_span _ _
  have hexcessEq :
      (F.system L).excess e =
        ((F.system L).rawWindowSpan e.1 : ℝ) - e.2 -
          (F.system L).epsilon * (F.system L).L := by
    unfold WindowSystem.excess
    apply max_eq_left
    by_contra hnot
    have hle :
        ((F.system L).rawWindowSpan e.1 : ℝ) - e.2 -
            (F.system L).epsilon * (F.system L).L ≤ 0 :=
      le_of_not_ge hnot
    have hpositive := hexcessPos
    rw [WindowSystem.excess, max_eq_right hle] at hpositive
    exact (lt_irrefl 0) hpositive
  have hthreshold :
      2 * ((F.system L).L : ℝ) + (F.system L).structural.C0 ≤ e.2 :=
    he.1.2.1
  have hepsilon :
      0 ≤ (F.system L).epsilon * ((F.system L).L : ℝ) :=
    mul_nonneg (F.system L).epsilon_nonneg (Nat.cast_nonneg _)
  have hCQltL : CQ < (L : ℝ) := by
    dsimp [CQ]
    exact_mod_cast (show gap.Cgap + 1 < L by omega)
  have hremainingReal :
      (F.system L).excess e / 2 ≤
        ((F.system L).rawWindowSpan e.1 : ℝ) - p.span := by
    rw [hexcessEq]
    rw [F.level_eq]
    rw [F.level_eq] at hthreshold hepsilon
    rw [hstruct] at hthreshold
    nlinarith
  have hcastSub :
      (((F.system L).rawWindowSpan e.1 - p.span : ℕ) : ℝ) =
        ((F.system L).rawWindowSpan e.1 : ℝ) - p.span := by
    exact Nat.cast_sub hpSpanLe
  constructor
  · rw [F.level_eq, hstruct]
    exact hpLower
  constructor
  · rw [F.level_eq, hstruct]
    exact hpUpper
  · change (F.system L).excess e / 2 ≤
      ((F.system L).rawWindowSpan e.1 : ℝ) - (p.span : ℝ)
    exact hremainingReal

/-- Paper label: `lem:firstdeep-count` (Section 5).  Once the cutoff is large
enough for the deterministic long prefix to exist, its subexponential error
is fixed uniformly over all compatible supports. -/
theorem lem_firstdeep_count (context : FixedScaleContext) :
    ∀ Z0 : ℕ,
      Nat.ceil
          (2 * context.structural.Caff / context.entropy.kappa) ≤ Z0 →
      ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop,
          ((initialPrefixes (F.system L) Z0).card : ℝ) ≤
            Real.rpow (F.system L).X
              (initialPrefixExponent (F.system L).entropy + error L) := by
  classical
  obtain ⟨CQ, hCQ, hfirst⟩ := lem_firstdeep_exists context
  intro Z0 hZ0
  refine ⟨initialCountError context CQ,
    initialCountError_tendsto_zero context CQ hCQ, ?_⟩
  have hkappaHalf :
      context.entropy.kappa / (context.structural.Caff + 1) ≤ 1 / 2 := by
    simpa only [context.entropy_structural] using
      context.entropy.kappa_initial_half
  have hkappaHalfStrict :
      context.entropy.kappa / (context.structural.Caff + 1) < 1 / 2 := by
    apply lt_of_le_of_ne hkappaHalf
    intro heq
    have hentropy :
        binaryEntropy
            (context.entropy.kappa / (context.structural.Caff + 1)) = 1 := by
      rw [heq]
      exact binaryEntropy_half
    have hmargin := context.entropy.initial_margin
    rw [context.entropy_structural, hentropy] at hmargin
    nlinarith [context.structural.Caff_gt, context.structural.rho_pos]
  intro F hF
  have halpha := initialCountAlpha_tendsto context CQ hCQ
  have halphaHalf : ∀ᶠ L : ℕ in atTop,
      initialCountAlpha context CQ L ≤ 1 / 2 :=
    ((tendsto_order.1 halpha).2 _ hkappaHalfStrict).mono fun _ h => h.le
  filter_upwards [hfirst Z0 hZ0 F hF, halphaHalf,
    eventually_ge_atTop 1] with L hfirstL halphaL hL
  let H := initialCountSpanCap context CQ L
  have hspan : ∀ p ∈ initialPrefixes (F.system L) Z0, p.span ≤ H := by
    intro p hp
    rw [initialPrefixes, Finset.mem_image] at hp
    rcases hp with ⟨k, hk, rfl⟩
    rw [highAnchors, Finset.mem_filter] at hk
    rcases hk.2 with ⟨T, hT, hlarge⟩
    have he : (k, T) ∈ (F.system L).largePairs Z0 :=
      ⟨⟨hk.1, hT⟩, hlarge⟩
    have hup := (hfirstL (k, T) he).2.1
    have hstruct : (F.system L).structural = context.structural :=
      (F.structural_eq L).trans hF.2.1
    rw [F.level_eq, hstruct] at hup
    exact Nat.le_floor hup
  have hcardNat :=
    initialPrefixes_card_le_compositions (F.system L) Z0 H hspan
  have hm : (F.system L).m =
      Nat.floor (context.entropy.kappa * (L : ℝ)) + 1 := by
    rw [WindowSystem.m, F.offset_eq, hF.2.2.1]
  have hH : 2 ≤ H + 1 := by
    have hreal : (1 : ℝ) ≤
        (context.structural.Caff + 1) * (L : ℝ) + CQ := by
      have hCaff : 2 < context.structural.Caff := context.structural.Caff_gt
      have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    have : 1 ≤ H := by
      apply Nat.le_floor
      norm_num only [Nat.cast_one]
      exact hreal
    omega
  have halphaPos : 0 < initialCountAlpha context CQ L := by
    dsimp [initialCountAlpha]
    positivity
  have hr : (((F.system L).m + 1 : ℕ) : ℝ) ≤
      initialCountAlpha context CQ L * ((H + 1 : ℕ) : ℝ) := by
    rw [hm]
    dsimp [initialCountAlpha, H]
    have hden : (0 : ℝ) <
        ((initialCountSpanCap context CQ L + 1 : ℕ) : ℝ) := by positivity
    field_simp
    norm_num
  have hcomposition := lem_composition_entropy (H + 1)
    ((F.system L).m + 1) (initialCountAlpha context CQ L)
    hH halphaPos halphaL hr
  have hcardReal : ((initialPrefixes (F.system L) Z0).card : ℝ) ≤
      (((H + 1 : ℕ) : ℝ) ^ 2) *
        Real.rpow 2
          (((H + 1 : ℕ) : ℝ) *
            binaryEntropy (initialCountAlpha context CQ L)) := by
    calc
      ((initialPrefixes (F.system L) Z0).card : ℝ) ≤
          ((∑ r ∈ Finset.Icc 0 (F.system L).m, H.choose r : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ = ((∑ q ∈ Finset.Icc 1 ((F.system L).m + 1),
          H.choose (q - 1) : ℕ) : ℝ) := by
        rw [sum_choose_Icc_zero_eq_shift]
      _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2) *
          Real.rpow 2
            (((H + 1 : ℕ) : ℝ) *
              binaryEntropy (initialCountAlpha context CQ L)) := by
        simpa only [Nat.add_sub_cancel] using hcomposition
  rw [F.entropy_eq, hF.2.2.1, WindowSystem.X, F.level_eq, dyadicScale]
  apply hcardReal.trans
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have hHreal : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
  have hbase : (0 : ℝ) < (((2 ^ L : ℕ) : ℝ)) := by positivity
  have hrpowTwo : Real.rpow 2
      (((H + 1 : ℕ) : ℝ) *
        binaryEntropy (initialCountAlpha context CQ L)) =
      Real.exp (Real.log 2 *
        (((H + 1 : ℕ) : ℝ) *
          binaryEntropy (initialCountAlpha context CQ L))) :=
    Real.rpow_def_of_pos (x := 2) (by norm_num) _
  have hrpowBase : Real.rpow (((2 ^ L : ℕ) : ℝ))
      (initialPrefixExponent context.entropy + initialCountError context CQ L) =
      Real.exp (Real.log (((2 ^ L : ℕ) : ℝ)) *
        (initialPrefixExponent context.entropy + initialCountError context CQ L)) :=
    Real.rpow_def_of_pos (x := (((2 ^ L : ℕ) : ℝ))) hbase _
  rw [hrpowTwo, hrpowBase]
  have hpolyExp : (((H + 1 : ℕ) : ℝ) ^ 2) =
      Real.exp (2 * Real.log (((H + 1 : ℕ) : ℝ))) := by
    calc
      (((H + 1 : ℕ) : ℝ) ^ 2) =
          Real.exp (Real.log (((H + 1 : ℕ) : ℝ) ^ 2)) :=
        (Real.exp_log (pow_pos hHreal 2)).symm
      _ = Real.exp (2 * Real.log (((H + 1 : ℕ) : ℝ))) := by
        rw [Real.log_pow]
        norm_num
  rw [hpolyExp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcastPow : (((2 ^ L : ℕ) : ℝ)) = (2 : ℝ) ^ L := by norm_num
  rw [hcastPow, Real.log_pow]
  have herror : initialCountError context CQ L =
      |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (initialCountAlpha context CQ L) -
        initialPrefixExponent context.entropy| +
        2 * Real.log (((H + 1 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2) := by
    simp only [initialCountError, Nat.ne_of_gt hL, if_false, H,
      initialCountSpanCap]
  rw [herror]
  have habs := le_abs_self
    ((((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
      binaryEntropy (initialCountAlpha context CQ L) -
      initialPrefixExponent context.entropy)
  have hmainLe :
      (((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (initialCountAlpha context CQ L) ≤
        initialPrefixExponent context.entropy +
          |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L) -
            initialPrefixExponent context.entropy| := by
    linarith
  have hscalePos : 0 < (L : ℝ) * Real.log 2 := mul_pos hLpos hlog2pos
  have hscaled := mul_le_mul_of_nonneg_left hmainLe hscalePos.le
  have hpolyCancel :
      ((L : ℝ) * Real.log 2) *
          (2 * Real.log (((H + 1 : ℕ) : ℝ)) /
            ((L : ℝ) * Real.log 2)) =
        2 * Real.log (((H + 1 : ℕ) : ℝ)) := by
    field_simp [hL0, hlog2]
  have hentropyScale :
      Real.log 2 *
          (((H + 1 : ℕ) : ℝ) *
            binaryEntropy (initialCountAlpha context CQ L)) =
        ((L : ℝ) * Real.log 2) *
          ((((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L)) := by
    field_simp [hL0]
  calc
    2 * Real.log (((H + 1 : ℕ) : ℝ)) +
        Real.log 2 *
          (((H + 1 : ℕ) : ℝ) *
            binaryEntropy (initialCountAlpha context CQ L)) =
      2 * Real.log (((H + 1 : ℕ) : ℝ)) +
        ((L : ℝ) * Real.log 2) *
          ((((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (initialCountAlpha context CQ L)) := by
      rw [hentropyScale]
    _ ≤ 2 * Real.log (((H + 1 : ℕ) : ℝ)) +
        ((L : ℝ) * Real.log 2) *
          (initialPrefixExponent context.entropy +
            |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
              binaryEntropy (initialCountAlpha context CQ L) -
              initialPrefixExponent context.entropy|) :=
      by simpa [add_comm] using
        add_le_add_left hscaled (2 * Real.log (((H + 1 : ℕ) : ℝ)))
    _ = ((L : ℝ) * Real.log 2) *
        (initialPrefixExponent context.entropy +
          (|(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
              binaryEntropy (initialCountAlpha context CQ L) -
              initialPrefixExponent context.entropy| +
            2 * Real.log (((H + 1 : ℕ) : ℝ)) /
              ((L : ℝ) * Real.log 2))) := by
      calc
        2 * Real.log (((H + 1 : ℕ) : ℝ)) +
            ((L : ℝ) * Real.log 2) *
              (initialPrefixExponent context.entropy +
                |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                  binaryEntropy (initialCountAlpha context CQ L) -
                  initialPrefixExponent context.entropy|) =
          ((L : ℝ) * Real.log 2) * initialPrefixExponent context.entropy +
            ((L : ℝ) * Real.log 2) *
              |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                binaryEntropy (initialCountAlpha context CQ L) -
                initialPrefixExponent context.entropy| +
            2 * Real.log (((H + 1 : ℕ) : ℝ)) := by ring
        _ = ((L : ℝ) * Real.log 2) * initialPrefixExponent context.entropy +
            ((L : ℝ) * Real.log 2) *
              |(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                binaryEntropy (initialCountAlpha context CQ L) -
                initialPrefixExponent context.entropy| +
            ((L : ℝ) * Real.log 2) *
              (2 * Real.log (((H + 1 : ℕ) : ℝ)) /
                ((L : ℝ) * Real.log 2)) := by rw [hpolyCancel]
        _ = ((L : ℝ) * Real.log 2) *
            (initialPrefixExponent context.entropy +
              (|(((H + 1 : ℕ) : ℝ) / (L : ℝ)) *
                  binaryEntropy (initialCountAlpha context CQ L) -
                  initialPrefixExponent context.entropy| +
                2 * Real.log (((H + 1 : ℕ) : ℝ)) /
                  ((L : ℝ) * Real.log 2))) := by ring

/-- Paper label: `prop:low-firstdeep` (Section 5).  The same cutoff condition
as in `lem_firstdeep_exists` is retained explicitly. -/
theorem prop_low_firstdeep (context : FixedScaleContext) :
    ∀ Z0 : ℕ,
      Nat.ceil
          (2 * context.structural.Caff / context.entropy.kappa) ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
      (fun L => rareLargePairsMass (F.system L) Z0) =o[atTop]
        (fun L =>
          ((F.system L).m : ℝ) * (F.system L).X *
            thresholdLength (F.system L)) := by
  classical
  intro Z0 hZ0 F hF
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨error, herrorZero, hcount⟩ :=
    lem_firstdeep_count context Z0 hZ0
  let Δ : ℝ := initialPrefixExponent context.entropy
  let δ : ℝ := 1 / 2 - context.structural.rho - Δ
  let d : ℝ := δ / 2
  have hΔ : Δ < 1 / 2 - 3 * context.structural.rho := by
    dsimp [Δ, initialPrefixExponent]
    simpa only [context.entropy_structural] using
      context.entropy.initial_margin
  have hδ : 0 < δ := by
    dsimp [δ]
    have hrho := context.structural.rho_pos
    linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have herrorSmall : ∀ᶠ L : ℕ in atTop, error L ≤ d :=
    ((tendsto_order.1 herrorZero).2 d hd).mono fun _ h => h.le
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  let b : ℝ := Real.log 2 * d
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) hd
  have hpolyExp :
      Tendsto (fun L : ℕ => (L : ℝ) / Real.exp (b * (L : ℝ)))
        atTop (𝓝 0) := by
    have hlittle :=
      (isLittleO_pow_exp_pos_mul_atTop 1 hb).comp_tendsto hnatTop
    simpa only [Function.comp_apply, pow_one] using
      hlittle.tendsto_div_nhds_zero
  have hexpTop : Tendsto (fun L : ℕ => Real.exp (b * (L : ℝ)))
      atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hb hnatTop)
  have hconstExp : Tendsto
      (fun L : ℕ => ((gap.Cgap : ℝ) + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hexpTop
  have hdecayExp : Tendsto
      (fun L : ℕ => ((L : ℝ) + gap.Cgap + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) := by
    simpa only [add_div, zero_add, add_assoc] using
      hpolyExp.add hconstExp
  have hrpowExp : ∀ L : ℕ,
      Real.rpow (dyadicScale L) d = Real.exp (b * (L : ℝ)) := by
    intro L
    have hdyadic : (0 : ℝ) < dyadicScale L := by
      rw [dyadicScale]
      positivity
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos
      (x := (dyadicScale L : ℝ)) (y := d) hdyadic]
    simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    dsimp [b]
    ring_nf
  have hdecay : Tendsto
      (fun L : ℕ => ((L : ℝ) + gap.Cgap + 1) /
        Real.rpow (dyadicScale L) d) atTop (𝓝 0) := by
    simpa only [hrpowExp] using hdecayExp
  apply IsLittleO.of_bound
  intro c hc
  have hdecayC : ∀ᶠ L : ℕ in atTop,
      ((L : ℝ) + gap.Cgap + 1) /
          Real.rpow (dyadicScale L) d ≤ c :=
    ((tendsto_order.1 hdecay).2 c hc).mono fun _ h => h.le
  filter_upwards [eventually_rawWindowGap_le context gap F hF,
    hcount F hF, herrorSmall, hdecayC, eventually_ge_atTop 1]
      with L hgap hprefixCount herrorL hdecayL hL
  let W := F.system L
  let G : ℕ := L + gap.Cgap + 1
  have hWstruct : W.structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hWentropy : W.entropy = context.entropy :=
    (F.entropy_eq L).trans hF.2.2.1
  have hlevel : W.L = L := F.level_eq L
  have hX : W.X = dyadicScale L := by rw [WindowSystem.X, hlevel]
  have hXpos : 0 < (W.X : ℝ) := by
    rw [hX, dyadicScale]
    positivity
  have hXone : (1 : ℝ) ≤ W.X := by
    rw [hX, dyadicScale]
    exact_mod_cast (Left.one_le_pow_of_le (by norm_num : (1 : ℕ) ≤ 2) L)
  have hGnonneg : (0 : ℝ) ≤ G := by positivity
  have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
  have hlengthNonneg : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrareBound : ∀ e ∈ rareLargePairs W Z0,
      W.excess e ≤ ((W.m : ℝ) * G) := by
    intro e he
    have hexcess := W.excess_le_rawWindowSpan e he.1.1
    have hsum : (W.rawWindowGapWord e.1).sum ≤
        (W.rawWindowGapWord e.1).length * G := by
      simpa [nsmul_eq_mul] using
        List.sum_le_card_nsmul (W.rawWindowGapWord e.1) G
          (hgap e.1 he.1.1.1)
    have hlen : (W.rawWindowGapWord e.1).length ≤ W.m := by
      unfold WindowSystem.rawWindowGapWord
      split
      · simp [windowGapWord, WindowSystem.window, WindowSystem.m]
      · exact Nat.zero_le _
    have hspan : W.rawWindowSpan e.1 ≤ W.m * G := by
      rw [← rawWindowGapWord_span]
      exact hsum.trans (Nat.mul_le_mul_right G hlen)
    exact hexcess.trans (by exact_mod_cast hspan)
  have hmass := rareLargePairsMass_le W Z0 ((W.m : ℝ) * G)
    (mul_nonneg hmnonneg hGnonneg) hrareBound
  have hanchors := rareAnchors_card_le W Z0
  have hcountW : ((initialPrefixes W Z0).card : ℝ) ≤
      Real.rpow W.X (Δ + error L) := by
    simpa only [W, hWentropy, Δ] using hprefixCount
  have hcutoff : frequencyCutoff W =
      Real.rpow W.X (1 / 2 + context.structural.rho) := by
    unfold frequencyCutoff
    rw [hWstruct]
  have hanchorEstimate : ((rareAnchors W Z0).card : ℝ) ≤
      Real.rpow W.X
        (Δ + error L + (1 / 2 + context.structural.rho)) := by
    calc
      ((rareAnchors W Z0).card : ℝ) ≤
          ((initialPrefixes W Z0).card : ℝ) * frequencyCutoff W := hanchors
      _ ≤ Real.rpow W.X (Δ + error L) * frequencyCutoff W := by
        exact mul_le_mul_of_nonneg_right hcountW
          (by unfold frequencyCutoff; exact Real.rpow_nonneg hXpos.le _)
      _ = Real.rpow W.X
          (Δ + error L + (1 / 2 + context.structural.rho)) := by
        rw [hcutoff]
        exact (Real.rpow_add hXpos _ _).symm
  have hexponent :
      Δ + error L + (1 / 2 + context.structural.rho) ≤ 1 - d := by
    dsimp [δ, d] at hδ hd herrorL ⊢
    linarith
  have hrpowExponent : Real.rpow W.X
      (Δ + error L + (1 / 2 + context.structural.rho)) ≤
      Real.rpow W.X (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hanchorFinal : ((rareAnchors W Z0).card : ℝ) ≤
      W.X / Real.rpow W.X d := by
    calc
      ((rareAnchors W Z0).card : ℝ) ≤
          Real.rpow W.X
            (Δ + error L + (1 / 2 + context.structural.rho)) :=
        hanchorEstimate
      _ ≤ Real.rpow W.X (1 - d) := hrpowExponent
      _ = W.X / Real.rpow W.X d := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_sub hXpos 1 d, Real.rpow_one]
  have hdecayW : (G : ℝ) / Real.rpow W.X d ≤ c := by
    rw [hX]
    simpa only [G, Nat.cast_add, Nat.cast_one] using hdecayL
  have hmassFinal : rareLargePairsMass W Z0 ≤
      c * ((W.m : ℝ) * W.X * thresholdLength W) := by
    calc
      rareLargePairsMass W Z0 ≤
          ((W.m : ℝ) * G) * (rareAnchors W Z0).card *
            thresholdLength W := hmass
      _ ≤ ((W.m : ℝ) * G) *
          (W.X / Real.rpow W.X d) * thresholdLength W := by
        gcongr
      _ = ((W.m : ℝ) * W.X * thresholdLength W) *
          ((G : ℝ) / Real.rpow W.X d) := by ring
      _ ≤ ((W.m : ℝ) * W.X * thresholdLength W) * c := by
        gcongr
      _ = c * ((W.m : ℝ) * W.X * thresholdLength W) := by ring
  have hmassNonneg : 0 ≤ rareLargePairsMass W Z0 := by
    unfold rareLargePairsMass finiteWindowMass FiniteMass.toReal
    exact ENNReal.toReal_nonneg
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmassNonneg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hmnonneg hXpos.le)
      hlengthNonneg), W] using hmassFinal

/-- The eventual denominator-uniform gap bound can be enlarged to cover the
finitely many possible starting positions below its uniform cutoff. -/
theorem exists_global_gap_bound (Q : ℕ) (hQ : 0 < Q) :
    ∃ Cgap : ℕ, ∀ R : RationalSupport, R.eta.den = Q →
      ∀ x g : ℕ, IsSupportGap R.S x g →
        g ≤ Nat.log 2 (x + 1) + Cgap := by
  obtain ⟨gap⟩ := gapParams_exists Q hQ
  obtain ⟨xexp, hexp⟩ := eventually_linear_lt_two_pow_pred Q
  let Bearly := max xexp (max gap.x0 1)
  refine ⟨max gap.Cgap Bearly, ?_⟩
  intro R hden x g hgap
  by_cases hx : gap.x0 ≤ x
  · have h := gap.bound R hden x hx g hgap
    have hlog : Nat.log 2 x ≤ Nat.log 2 (x + 1) :=
      Nat.log_mono_right (by omega)
    omega
  · have hgEarly : g < Bearly := by
      by_contra hnot
      have hB : Bearly ≤ g := Nat.le_of_not_gt hnot
      have hxg : x < g := by
        have hxx0 : x < gap.x0 := Nat.lt_of_not_ge hx
        exact hxx0.trans_le ((le_max_left gap.x0 1).trans
          ((le_max_right xexp (max gap.x0 1)).trans hB))
      have hg1 : 1 ≤ g :=
        (le_max_right gap.x0 1).trans
          ((le_max_right xexp (max gap.x0 1)).trans hB)
      have hlinear : Q * (x + g + 1) ≤ 3 * Q * g := by
        have hsum : x + g + 1 ≤ 3 * g := by omega
        nlinarith
      have hpower := gap_power_bound R x g hgap
      rw [hden] at hpower
      have hstrict := hexp g ((le_max_left xexp (max gap.x0 1)).trans hB)
      omega
    have hmax : Bearly ≤ max gap.Cgap Bearly := le_max_right _ _
    omega

def carryAlongWord (Q x : ℕ) (r : ℤ) : GapWord → ℤ
  | [] => r
  | g :: gs => carryAlongWord Q (x + g)
      ((2 : ℤ) ^ g * r - (Q : ℤ) * (x + g)) gs

private theorem wordMultiplier_cons (g : ℕ) (w : GapWord) :
    wordMultiplier (g :: w) = 2 ^ w.span + wordMultiplier w := by
  simp [wordMultiplier, List.range_succ_eq_map, GapWord.span,
    GapWord.prefixSpan, Function.comp_def, Nat.add_sub_add_left]

private theorem carryAlongWord_difference (Q x y : ℕ) (r s : ℤ)
    (w : GapWord) :
    carryAlongWord Q y s w - carryAlongWord Q x r w =
      (2 : ℤ) ^ w.span * (s - r) -
        (Q : ℤ) * wordMultiplier w * ((y : ℤ) - x) := by
  induction w generalizing x y r s with
  | nil => simp [carryAlongWord, GapWord.span, wordMultiplier]
  | cons g w ih =>
      simp only [carryAlongWord]
      rw [ih]
      rw [wordMultiplier_cons]
      simp only [GapWord.span, List.sum_cons, pow_add]
      push_cast
      ring

def enumerationGapWord {S : Set ℕ} (e : SupportEnumeration S)
    (i n : ℕ) : GapWord :=
  (List.range n).map fun j => supportGap e (i + j)

theorem enumerationGapWord_succ {S : Set ℕ}
    (e : SupportEnumeration S) (i n : ℕ) :
    enumerationGapWord e i (n + 1) =
      supportGap e i :: enumerationGapWord e (i + 1) n := by
  unfold enumerationGapWord
  rw [List.range_succ_eq_map]
  simp [Nat.add_comm, Nat.add_left_comm]

theorem enumerationGapWord_span {S : Set ℕ}
    (e : SupportEnumeration S) (i n : ℕ) :
    (enumerationGapWord e i n).span = e.a (i + n) - e.a i := by
  unfold enumerationGapWord GapWord.span
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have htel := sum_supportGap_Ico e i (i + n) (by omega)
  rw [Finset.sum_Ico_eq_sum_range] at htel
  simpa using htel

theorem carryAlong_enumeration (R : RationalSupport)
    (e : SupportEnumeration R.S) (i n : ℕ) :
    carryAlongWord R.eta.den (e.a i) (carryInt R (e.a i))
        (enumerationGapWord e i n) =
      carryInt R (e.a (i + n)) := by
  induction n generalizing i with
  | zero => simp [enumerationGapWord, carryAlongWord]
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, enumerationGapWord_succ]
      simp only [carryAlongWord]
      have hgap := supportGap_isSupportGap e i
      have hupdate :
          (2 : ℤ) ^ supportGap e i * carryInt R (e.a i) -
              (R.eta.den : ℤ) * (e.a i + supportGap e i) =
            carryInt R (e.a i + supportGap e i) := by
        exact (carryInt_across_supportGap R (e.a i)
          (supportGap e i) hgap).symm
      rw [hupdate]
      have hend : e.a i + supportGap e i = e.a (i + 1) := by
        simp only [supportGap]
        exact Nat.add_sub_of_le
          (e.strictMono (Nat.lt_succ_self i)).le
      rw [hend]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1)

theorem initialPrefix_eq_enumerationGapWord
    (W : WindowSystem) (Z0 k : ℕ) (p : GapWord)
    (hk : k ∈ highAnchors W Z0)
    (hp : initialLongPrefix W k = p) :
    p = enumerationGapWord W.enumeration (k - W.s) p.length := by
  have hsk : W.s ≤ k := highAnchor_offset_le W Z0 k hk
  have hprefix : p.IsPrefix (W.rawWindowGapWord k) := by
    rw [← hp]
    exact GapWord.firstPrefixAbove_isPrefix _ _
  rcases hprefix with ⟨tail, htail⟩
  have hlen : p.length ≤ W.s + 1 := by
    have hlength := congrArg List.length htail
    have hlength' : p.length + tail.length = W.s + 1 := by
      simpa [WindowSystem.rawWindowGapWord, hsk,
        WindowSystem.window, windowGapWord] using hlength
    omega
  have htake := congrArg (List.take p.length) htail
  rw [List.take_append_of_le_length (le_refl p.length)] at htake
  rw [WindowSystem.rawWindowGapWord, dif_pos hsk,
    WindowSystem.window, windowGapWord] at htake
  unfold enumerationGapWord
  simpa [← List.map_take, List.take_range, hlen] using htake

private theorem occurrenceCarry_difference
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (k₁ k₂ : ℕ) (hk₁ : k₁ ∈ highAnchors W Z0)
    (hk₂ : k₂ ∈ highAnchors W Z0)
    (hp₁ : initialLongPrefix W k₁ = p)
    (hp₂ : initialLongPrefix W k₂ = p) :
    let x₁ := W.enumeration.a (k₁ - W.s) + p.span
    let x₂ := W.enumeration.a (k₂ - W.s) + p.span
    carryInt W.rational x₂ - carryInt W.rational x₁ =
      (2 : ℤ) ^ p.span *
        (carryInt W.rational (W.enumeration.a (k₂ - W.s)) -
          carryInt W.rational (W.enumeration.a (k₁ - W.s))) -
      (W.rational.eta.den : ℤ) * wordMultiplier p *
        ((x₂ : ℤ) - x₁) := by
  dsimp only
  have hpword₁ := initialPrefix_eq_enumerationGapWord W Z0 k₁ p hk₁ hp₁
  have hpword₂ := initialPrefix_eq_enumerationGapWord W Z0 k₂ p hk₂ hp₂
  let i₁ := k₁ - W.s
  let i₂ := k₂ - W.s
  have hspan₁ := enumerationGapWord_span W.enumeration i₁ p.length
  have hspan₂ := enumerationGapWord_span W.enumeration i₂ p.length
  rw [← hpword₁] at hspan₁
  rw [← hpword₂] at hspan₂
  have hmono₁ : W.enumeration.a i₁ ≤ W.enumeration.a (i₁ + p.length) :=
    W.enumeration.strictMono.monotone (by omega)
  have hmono₂ : W.enumeration.a i₂ ≤ W.enumeration.a (i₂ + p.length) :=
    W.enumeration.strictMono.monotone (by omega)
  have hend₁ : W.enumeration.a i₁ + p.span =
      W.enumeration.a (i₁ + p.length) := by omega
  have hend₂ : W.enumeration.a i₂ + p.span =
      W.enumeration.a (i₂ + p.length) := by omega
  have hcarry₁ := carryAlong_enumeration W.rational W.enumeration i₁ p.length
  have hcarry₂ := carryAlong_enumeration W.rational W.enumeration i₂ p.length
  dsimp [i₁] at hpword₁ hspan₁ hmono₁ hend₁ hcarry₁
  dsimp [i₂] at hpword₂ hspan₂ hmono₂ hend₂ hcarry₂
  rw [← hpword₁, ← hend₁] at hcarry₁
  rw [← hpword₂, ← hend₂] at hcarry₂
  have hdiff := carryAlongWord_difference W.rational.eta.den
    (W.enumeration.a i₁) (W.enumeration.a i₂)
    (carryInt W.rational (W.enumeration.a i₁))
    (carryInt W.rational (W.enumeration.a i₂)) p
  rw [hcarry₁, hcarry₂] at hdiff
  dsimp [i₁, i₂] at hdiff ⊢
  convert hdiff using 1
  ring_nf

private def occurrenceX (W : WindowSystem) (p : GapWord) (k : ℕ) : ℤ :=
  W.enumeration.a (k - W.s) + p.span

private def occurrenceR (W : WindowSystem) (p : GapWord) (k : ℕ) : ℤ :=
  carryInt W.rational (W.enumeration.a (k - W.s) + p.span)

private theorem occurrenceDifference_mem_lattice
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord)
    (k₁ k₂ : ℕ) (hk₁ : k₁ ∈ highAnchors W Z0)
    (hk₂ : k₂ ∈ highAnchors W Z0)
    (hp₁ : initialLongPrefix W k₁ = p)
    (hp₂ : initialLongPrefix W k₂ = p) :
    (occurrenceX W p k₂ - occurrenceX W p k₁,
      occurrenceR W p k₂ - occurrenceR W p k₁) ∈
      congruenceLattice
        ((W.rational.eta.den : ℤ) * wordMultiplier p) (2 ^ p.span) := by
  have hdiff := occurrenceCarry_difference W Z0 p k₁ k₂
    hk₁ hk₂ hp₁ hp₂
  dsimp only at hdiff
  unfold congruenceLattice occurrenceX occurrenceR
  change Int.ModEq (2 ^ p.span : ℤ)
    ((W.rational.eta.den : ℤ) * wordMultiplier p *
        ((W.enumeration.a (k₂ - W.s) : ℤ) + p.span -
          ((W.enumeration.a (k₁ - W.s) : ℤ) + p.span)) +
      (carryInt W.rational (W.enumeration.a (k₂ - W.s) + p.span) -
        carryInt W.rational (W.enumeration.a (k₁ - W.s) + p.span))) 0
  rw [Int.modEq_zero_iff_dvd]
  refine ⟨carryInt W.rational (W.enumeration.a (k₂ - W.s)) -
    carryInt W.rational (W.enumeration.a (k₁ - W.s)), ?_⟩
  rw [hdiff]
  push_cast
  ring

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

private theorem occurrenceX_le
    (W : WindowSystem) (Z0 : ℕ) (p : GapWord) (Cgap : ℕ)
    (hglobal : ∀ R : RationalSupport,
      R.eta.den = W.rational.eta.den → ∀ x g : ℕ,
        IsSupportGap R.S x g → g ≤ Nat.log 2 (x + 1) + Cgap)
    (k : ℕ) (hk : k ∈ highAnchors W Z0)
    (hp : initialLongPrefix W k = p) :
    (occurrenceX W p k).natAbs ≤ (Cgap + 5) * W.X := by
  classical
  have hkAnchor : k ∈ W.anchors := by
    rw [highAnchors, Finset.mem_filter] at hk
    exact hk.1
  have hsk : W.s ≤ k := highAnchor_offset_le W Z0 k hk
  have hpPrefix : p.IsPrefix (W.rawWindowGapWord k) := by
    rw [← hp]
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hpSpan : p.span ≤ W.rawWindowSpan k := by
    rcases hpPrefix with ⟨tail, htail⟩
    have hspanEq : (W.rawWindowGapWord k).span = W.rawWindowSpan k := by
      unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
      split <;> rfl
    rw [← hspanEq]
    rw [← htail]
    simp only [GapWord.span, List.sum_append]
    omega
  have hkData := Finset.mem_filter.mp hkAnchor
  have hkUpper : W.enumeration.a k ≤ 2 * W.X := hkData.2.2
  have hgap := hglobal W.rational rfl (W.enumeration.a k)
    (supportGap W.enumeration k) (supportGap_isSupportGap W.enumeration k)
  have hXone : 1 ≤ W.X := by
    unfold WindowSystem.X dyadicScale
    exact Nat.one_le_two_pow
  have harg : W.enumeration.a k + 1 ≤ 4 * W.X := by omega
  have hlog : Nat.log 2 (W.enumeration.a k + 1) ≤ W.L + 2 := by
    calc
      Nat.log 2 (W.enumeration.a k + 1) ≤ Nat.log 2 (4 * W.X) :=
        Nat.log_mono_right harg
      _ = W.L + 2 := by
        rw [WindowSystem.X, dyadicScale,
          show 4 * 2 ^ W.L = 2 ^ (W.L + 2) by
            rw [pow_add]
            norm_num
            ring]
        exact Nat.log_pow Nat.one_lt_two (W.L + 2)
  have hnext : W.enumeration.a (k + 1) =
      W.enumeration.a k + supportGap W.enumeration k := by
    simp only [supportGap]
    exact (Nat.add_sub_of_le
      (W.enumeration.strictMono (Nat.lt_succ_self k)).le).symm
  have hendpoint : (occurrenceX W p k).natAbs ≤
      W.enumeration.a (k + 1) := by
    have hraw := rawWindowSpan_eq_sub W k hsk
    have hmono : W.enumeration.a (k - W.s) ≤ W.enumeration.a (k + 1) :=
      W.enumeration.strictMono.monotone (by omega)
    change W.enumeration.a (k - W.s) + p.span ≤ W.enumeration.a (k + 1)
    omega
  have hLpow : W.L ≤ W.X := by
    rw [WindowSystem.X, dyadicScale]
    exact nat_le_two_pow W.L
  have hboundNext : W.enumeration.a (k + 1) ≤ (Cgap + 5) * W.X := by
    rw [hnext]
    have hgap' : supportGap W.enumeration k ≤ W.L + 2 + Cgap :=
      hgap.trans (Nat.add_le_add_right hlog Cgap)
    nlinarith
  exact hendpoint.trans hboundNext

private theorem occurrenceR_bounds
    (W : WindowSystem) (p : GapWord) (Cx : ℕ) (k : ℕ)
    (_hx : 0 ≤ occurrenceX W p k)
    (hxle : occurrenceX W p k ≤ (Cx : ℤ) * W.X) :
    0 ≤ occurrenceR W p k ∧
      occurrenceR W p k ≤
        (W.rational.eta.den : ℤ) * (Cx + 2) * W.X := by
  have hcarry := prop_carry W.rational
  have hXone : (1 : ℤ) ≤ W.X := by
    unfold WindowSystem.X dyadicScale
    exact_mod_cast Nat.one_le_two_pow
  unfold occurrenceX at hxle
  unfold occurrenceR
  constructor
  · exact hcarry.2.1 _
  · have hup := hcarry.2.2.1
      (W.enumeration.a (k - W.s) + p.span)
    have hQnonneg : (0 : ℤ) ≤ W.rational.eta.den := by positivity
    calc
      carryInt W.rational (W.enumeration.a (k - W.s) + p.span) ≤
          (W.rational.eta.den : ℤ) *
            (W.enumeration.a (k - W.s) + p.span + 2) := hup
      _ ≤ (W.rational.eta.den : ℤ) * (Cx + 2) * W.X := by
        nlinarith

private theorem AffineLine.contains_of_direction_eq_of_primitive
    (line : AffineLine) (hprimitive : Int.gcd line.H line.K = 1)
    (x r : ℤ)
    (hdirection : line.H * (r - line.C) = line.K * (x - line.A)) :
    line.Contains x r := by
  have hdvdMul : line.H ∣ line.K * (x - line.A) := by
    exact ⟨r - line.C, hdirection.symm⟩
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

private theorem intDet_abs_le_of_box
    (Bx Br : ℤ) (hBx : 0 ≤ Bx) (hBr : 0 ≤ Br)
    (x₀ r₀ x₁ r₁ x₂ r₂ : ℤ)
    (hx₀ : 0 ≤ x₀) (hx₀' : x₀ ≤ Bx)
    (hx₁ : 0 ≤ x₁) (hx₁' : x₁ ≤ Bx)
    (hx₂ : 0 ≤ x₂) (hx₂' : x₂ ≤ Bx)
    (hr₀ : 0 ≤ r₀) (hr₀' : r₀ ≤ Br)
    (hr₁ : 0 ≤ r₁) (hr₁' : r₁ ≤ Br)
    (hr₂ : 0 ≤ r₂) (hr₂' : r₂ ≤ Br) :
    |intDet (x₁ - x₀, r₁ - r₀) (x₂ - x₀, r₂ - r₀)| ≤
      2 * Bx * Br := by
  have hdx₁ : |x₁ - x₀| ≤ Bx := by rw [abs_le]; constructor <;> linarith
  have hdx₂ : |x₂ - x₀| ≤ Bx := by rw [abs_le]; constructor <;> linarith
  have hdr₁ : |r₁ - r₀| ≤ Br := by rw [abs_le]; constructor <;> linarith
  have hdr₂ : |r₂ - r₀| ≤ Br := by rw [abs_le]; constructor <;> linarith
  unfold intDet
  calc
    |(x₁ - x₀) * (r₂ - r₀) - (r₁ - r₀) * (x₂ - x₀)| ≤
        |(x₁ - x₀) * (r₂ - r₀)| + |(r₁ - r₀) * (x₂ - x₀)| :=
      abs_sub _ _
    _ = |x₁ - x₀| * |r₂ - r₀| + |r₁ - r₀| * |x₂ - x₀| := by
      rw [abs_mul, abs_mul]
    _ ≤ Bx * Br + Br * Bx := by gcongr
    _ = 2 * Bx * Br := by ring

private theorem intDet_eq_zero_of_lattice_bounds
    (A : ℤ) (M D : ℕ) (hM : 1 ≤ M) (hlarge : D < M)
    (z₁ z₂ : ℤ × ℤ)
    (hz₁ : z₁ ∈ congruenceLattice A M)
    (hz₂ : z₂ ∈ congruenceLattice A M)
    (hdetBound : |intDet z₁ z₂| ≤ D) :
    intDet z₁ z₂ = 0 := by
  obtain ⟨q, hq⟩ := lem_lattice_det A M hM z₁ z₂ hz₁ hz₂
  by_contra hdet
  have hqne : q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hq
    exact hdet hq
  have hqabs : (1 : ℤ) ≤ |q| := Int.one_le_abs hqne
  have hMnonneg : (0 : ℤ) ≤ M := by positivity
  have hMle : (M : ℤ) ≤ |intDet z₁ z₂| := by
    rw [hq, abs_mul, abs_of_nonneg hMnonneg]
    nlinarith
  have hlargeInt : (D : ℤ) < M := by exact_mod_cast hlarge
  have hboundInt : |intDet z₁ z₂| ≤ (D : ℤ) := by exact_mod_cast hdetBound
  linarith

/-- Paper label: `lem:ap-locking` (Section 5).  Both the determinant slack
and the spacing constant are selected after the denominator and before the
window/support data. -/
theorem lem_ap_locking (Q : ℕ) (hQ : 0 < Q) :
    ∃ Cline : ℕ, ∃ Clock : ℝ, 0 < Clock ∧ ∀ W : WindowSystem,
      W.rational.eta.den = Q → ∀ Z0 : ℕ, ∀ p : GapWord,
      p ∈ initialPrefixes W Z0 →
      2 * W.L + Cline < p.span → IsFrequentPrefix W Z0 p →
      ∃ line : AffineLine,
        IsOccurrenceLine W Z0 p line ∧
        Int.gcd line.H line.K = 1 ∧
        (line.H : ℝ) ≤ Clock * W.X / frequencyCutoff W := by
  classical
  obtain ⟨Cgap, hglobal⟩ := exists_global_gap_bound Q hQ
  let Cx : ℕ := Cgap + 5
  let Cr : ℕ := Q * (Cx + 2)
  let D : ℕ := 2 * Cx * Cr
  have hpowTop : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, D < 2 ^ n :=
    hpowTop.eventually_gt_atTop D
  obtain ⟨Cline, hClineAll⟩ := eventually_atTop.1 hevent
  have hCline : D < 2 ^ Cline := hClineAll Cline le_rfl
  let Clock : ℝ := 2 * Cx + 1
  refine ⟨Cline, Clock, by dsimp [Clock]; positivity, ?_⟩
  intro W hden Z0 p hpSet hpLong hfrequent
  let fibre : Finset ℕ :=
    (highAnchors W Z0).filter fun k => initialLongPrefix W k = p
  have hfreqCard : frequencyCutoff W ≤ (fibre.card : ℝ) := by
    simpa only [IsFrequentPrefix, prefixMultiplicity, fibre] using hfrequent
  have hXposNat : 0 < W.X := by
    unfold WindowSystem.X dyadicScale
    positivity
  have hXpos : (0 : ℝ) < W.X := by exact_mod_cast hXposNat
  have hXoneNat : 1 ≤ W.X := Nat.one_le_iff_ne_zero.mpr hXposNat.ne'
  have hXone : (1 : ℝ) ≤ W.X := by exact_mod_cast hXoneNat
  have hfreqPos : 0 < frequencyCutoff W := by
    unfold frequencyCutoff
    exact Real.rpow_pos_of_pos hXpos _
  have hfreqLeX : frequencyCutoff W ≤ (W.X : ℝ) := by
    unfold frequencyCutoff
    calc
      Real.rpow W.X (1 / 2 + W.structural.rho) ≤ Real.rpow W.X 1 := by
        apply Real.rpow_le_rpow_of_exponent_le hXone
        nlinarith [W.structural.rho_lt]
      _ = W.X := by simp [Real.rpow_eq_pow]
  rw [initialPrefixes, Finset.mem_image] at hpSet
  rcases hpSet with ⟨kbase, hkbase, hpbase⟩
  have hkbaseF : kbase ∈ fibre := by
    change kbase ∈ (highAnchors W Z0).filter fun k =>
      initialLongPrefix W k = p
    rw [Finset.mem_filter]
    exact ⟨hkbase, hpbase⟩
  by_cases hcard : fibre.card ≤ 1
  · let x₀ := occurrenceX W p kbase
    let r₀ := occurrenceR W p kbase
    let line : AffineLine :=
      { A := x₀
        C := r₀
        H := 1
        K := 0
        H_pos := by norm_num }
    have hline : IsOccurrenceLine W Z0 p line := by
      intro k hk hpk
      have hkF : k ∈ fibre := by
        change k ∈ (highAnchors W Z0).filter fun j =>
          initialLongPrefix W j = p
        rw [Finset.mem_filter]
        exact ⟨hk, hpk⟩
      have hEq : k = kbase := by
        exact (Finset.card_le_one.mp hcard) k hkF kbase hkbaseF
      subst k
      refine ⟨0, ?_, ?_⟩ <;>
        simp [line, x₀, r₀, occurrenceX, occurrenceR]
    have hprimitive : Int.gcd line.H line.K = 1 := by
      simp [line, Int.gcd_def]
    have hfreqOne : frequencyCutoff W ≤ 1 :=
      hfreqCard.trans (by exact_mod_cast hcard)
    have hClockOne : (1 : ℝ) ≤ Clock := by
      dsimp [Clock, Cx]
      have : (0 : ℝ) ≤ Cgap := by positivity
      nlinarith
    have hbound : (line.H : ℝ) ≤
        Clock * W.X / frequencyCutoff W := by
      rw [le_div_iff₀ hfreqPos]
      dsimp [line]
      have hprod : (1 : ℝ) ≤ Clock * W.X := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hClockOne)
          (sub_nonneg.mpr hXone)]
      simpa using hfreqOne.trans hprod
    exact ⟨line, hline, hprimitive, hbound⟩
  · have hcardTwo : 1 < fibre.card := by omega
    obtain ⟨k₀, hk₀F, k₁, hk₁F, hkne⟩ :=
      Finset.one_lt_card.mp hcardTwo
    obtain ⟨ka, hkaF, kb, hkbF, hkab⟩ :
        ∃ ka ∈ fibre, ∃ kb ∈ fibre, ka < kb := by
      rcases lt_or_gt_of_ne hkne with hlt | hgt
      · exact ⟨k₀, hk₀F, k₁, hk₁F, hlt⟩
      · exact ⟨k₁, hk₁F, k₀, hk₀F, hgt⟩
    have hka := Finset.mem_filter.mp (show ka ∈
      (highAnchors W Z0).filter fun k => initialLongPrefix W k = p from hkaF)
    have hkb := Finset.mem_filter.mp (show kb ∈
      (highAnchors W Z0).filter fun k => initialLongPrefix W k = p from hkbF)
    let x₀ := occurrenceX W p ka
    let r₀ := occurrenceR W p ka
    let x₁ := occurrenceX W p kb
    let r₁ := occurrenceR W p kb
    have hsa := highAnchor_offset_le W Z0 ka hka.1
    have hsb := highAnchor_offset_le W Z0 kb hkb.1
    have hindex : ka - W.s < kb - W.s := by omega
    have hx01 : x₀ < x₁ := by
      dsimp [x₀, x₁, occurrenceX]
      have henum : (W.enumeration.a (ka - W.s) : ℤ) <
          W.enumeration.a (kb - W.s) := by
        exact_mod_cast W.enumeration.strictMono hindex
      linarith
    let raw : AffineLine :=
      { A := x₀
        C := r₀
        H := x₁ - x₀
        K := r₁ - r₀
        H_pos := sub_pos.mpr hx01 }
    let line : AffineLine :=
      { A := x₀
        C := r₀
        H := (raw.canonicalGeometricLine.H : ℤ)
        K := raw.canonicalGeometricLine.K
        H_pos := by exact_mod_cast raw.canonicalGeometricLine.H_pos }
    have hprimitive : Int.gcd line.H line.K = 1 := by
      simpa [line, Int.gcd_def] using raw.canonicalGeometricLine.primitive
    have pointBounds : ∀ k ∈ fibre,
        0 ≤ occurrenceX W p k ∧
        occurrenceX W p k ≤ (Cx : ℤ) * W.X ∧
        0 ≤ occurrenceR W p k ∧
        occurrenceR W p k ≤ (Cr : ℤ) * W.X := by
      intro k hkF
      have hk := Finset.mem_filter.mp (show k ∈
        (highAnchors W Z0).filter fun j => initialLongPrefix W j = p from hkF)
      have hxnonneg : 0 ≤ occurrenceX W p k := by
        unfold occurrenceX
        positivity
      have hxNat := occurrenceX_le W Z0 p Cgap
        (by simpa only [hden] using hglobal) k hk.1 hk.2
      have hxle : occurrenceX W p k ≤ (Cx : ℤ) * W.X := by
        change W.enumeration.a (k - W.s) + p.span ≤ Cx * W.X at hxNat
        unfold occurrenceX
        exact_mod_cast hxNat
      have hr := occurrenceR_bounds W p Cx k hxnonneg hxle
      refine ⟨hxnonneg, hxle, hr.1, ?_⟩
      dsimp [Cr]
      rw [← hden]
      simpa only [mul_assoc] using hr.2
    have hMlarge : D * W.X ^ 2 < 2 ^ p.span := by
      have hpPow : 2 ^ (2 * W.L + Cline) < 2 ^ p.span :=
        (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 hpLong
      have hfactor : 2 ^ (2 * W.L + Cline) = W.X ^ 2 * 2 ^ Cline := by
        rw [pow_add, WindowSystem.X, dyadicScale]
        congr 1
        rw [← pow_mul]
        congr 1
        omega
      calc
        D * W.X ^ 2 < 2 ^ Cline * W.X ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hCline (pow_pos hXposNat 2)
        _ = W.X ^ 2 * 2 ^ Cline := Nat.mul_comm _ _
        _ = 2 ^ (2 * W.L + Cline) := hfactor.symm
        _ < 2 ^ p.span := hpPow
    have hline : IsOccurrenceLine W Z0 p line := by
      intro k hk hpk
      have hkF : k ∈ fibre := by
        change k ∈ (highAnchors W Z0).filter fun j =>
          initialLongPrefix W j = p
        rw [Finset.mem_filter]
        exact ⟨hk, hpk⟩
      let x := occurrenceX W p k
      let r := occurrenceR W p k
      let z₁ : ℤ × ℤ := (x₁ - x₀, r₁ - r₀)
      let z : ℤ × ℤ := (x - x₀, r - r₀)
      have hz₁ := occurrenceDifference_mem_lattice W Z0 p ka kb
        hka.1 hkb.1 hka.2 hkb.2
      have hzk := occurrenceDifference_mem_lattice W Z0 p ka k
        hka.1 hk hka.2 hpk
      have hb₀ := pointBounds ka hkaF
      have hb₁ := pointBounds kb hkbF
      have hbk := pointBounds k hkF
      have hdetBoundInt := intDet_abs_le_of_box
        ((Cx : ℤ) * W.X) ((Cr : ℤ) * W.X)
        (by positivity) (by positivity)
        x₀ r₀ x₁ r₁ x r
        hb₀.1 hb₀.2.1 hb₁.1 hb₁.2.1 hbk.1 hbk.2.1
        hb₀.2.2.1 hb₀.2.2.2 hb₁.2.2.1 hb₁.2.2.2
        hbk.2.2.1 hbk.2.2.2
      have hdetBoundNat : |intDet z₁ z| ≤ D * W.X ^ 2 := by
        have hright :
            2 * ((Cx : ℤ) * W.X) * ((Cr : ℤ) * W.X) =
              ((D * W.X ^ 2 : ℕ) : ℤ) := by
          dsimp [D]
          ring
        rw [hright] at hdetBoundInt
        exact_mod_cast hdetBoundInt
      have hdet : intDet z₁ z = 0 :=
        intDet_eq_zero_of_lattice_bounds
          ((W.rational.eta.den : ℤ) * wordMultiplier p)
          (2 ^ p.span) (D * W.X ^ 2) Nat.one_le_two_pow hMlarge
          z₁ z (by simpa [z₁, x₀, r₀, x₁, r₁] using hz₁)
          (by simpa [z, x, r, x₀, r₀] using hzk) hdetBoundNat
      have hrawDirection :
          raw.H * (r - raw.C) = raw.K * (x - raw.A) := by
        dsimp [z₁, z, raw] at hdet ⊢
        simp only [intDet] at hdet
        linarith
      have hdne : (raw.directionGCD : ℤ) ≠ 0 := by
        exact_mod_cast raw.directionGCD_pos.ne'
      have hHfactor : raw.primitiveHorizontalInt *
          (raw.directionGCD : ℤ) = raw.H :=
        Int.ediv_mul_cancel (Int.gcd_dvd_left raw.H raw.K)
      have hKfactor : raw.primitiveVertical *
          (raw.directionGCD : ℤ) = raw.K :=
        Int.ediv_mul_cancel (Int.gcd_dvd_right raw.H raw.K)
      have hprimitiveDirection :
          line.H * (r - line.C) = line.K * (x - line.A) := by
        dsimp [line]
        rw [raw.canonicalGeometricLine_H_cast]
        change raw.primitiveHorizontalInt * (r - r₀) =
          raw.primitiveVertical * (x - x₀)
        apply mul_right_cancel₀ hdne
        calc
          (raw.primitiveHorizontalInt * (r - r₀)) *
              (raw.directionGCD : ℤ) = raw.H * (r - r₀) := by
                rw [← hHfactor]
                ring
          _ = raw.K * (x - x₀) := hrawDirection
          _ = (raw.primitiveVertical * (x - x₀)) *
              (raw.directionGCD : ℤ) := by
                rw [← hKfactor]
                ring
      have hcontains := line.contains_of_direction_eq_of_primitive
        hprimitive x r hprimitiveDirection
      simpa [x, r, occurrenceX, occurrenceR] using hcontains
    let param : {k // k ∈ fibre} → ℤ := fun k =>
      Classical.choose (hline k.1 (Finset.mem_filter.mp k.2).1
        (Finset.mem_filter.mp k.2).2)
    have hparamSpec (k : {k // k ∈ fibre}) :
        occurrenceX W p k.1 = line.A + line.H * param k ∧
        occurrenceR W p k.1 = line.C + line.K * param k :=
      Classical.choose_spec (hline k.1 (Finset.mem_filter.mp k.2).1
        (Finset.mem_filter.mp k.2).2)
    have hparamInjective : Function.Injective param := by
      intro a b hab
      have hxa := (hparamSpec a).1
      have hxb := (hparamSpec b).1
      rw [hab] at hxa
      have hxEq : occurrenceX W p a.1 = occurrenceX W p b.1 :=
        hxa.trans hxb.symm
      have haData := Finset.mem_filter.mp a.2
      have hbData := Finset.mem_filter.mp b.2
      have hsa' := highAnchor_offset_le W Z0 a.1 haData.1
      have hsb' := highAnchor_offset_le W Z0 b.1 hbData.1
      have hind : a.1 - W.s = b.1 - W.s := by
        apply W.enumeration.strictMono.injective
        have : W.enumeration.a (a.1 - W.s) + p.span =
            W.enumeration.a (b.1 - W.s) + p.span := by
          unfold occurrenceX at hxEq
          exact_mod_cast hxEq
        exact Nat.add_right_cancel this
      apply Subtype.ext
      omega
    let params : Finset ℤ := fibre.attach.image param
    have hparamsCard : params.card = fibre.card := by
      dsimp [params]
      rw [Finset.card_image_of_injective _ hparamInjective]
      simp
    let Bx : ℤ := (Cx : ℤ) * W.X
    let C : ℤ := Bx - line.A
    let J : ℤ := -line.H
    have hJ : J < 0 := by dsimp [J]; exact neg_lt_zero.mpr line.H_pos
    have hBx : 0 ≤ Bx := by dsimp [Bx]; positivity
    have hparamBound : ∀ t ∈ (params : Set ℤ),
        0 ≤ C + J * t ∧ C + J * t ≤ Bx := by
      intro t ht
      rw [Finset.mem_coe] at ht
      change t ∈ fibre.attach.image param at ht
      rw [Finset.mem_image] at ht
      rcases ht with ⟨k, hk, rfl⟩
      have hkF : k.1 ∈ fibre := k.2
      have hb := pointBounds k.1 hkF
      have hx := (hparamSpec k).1
      dsimp [C, J]
      constructor <;> linarith
    have hcount := integerAffineIntervalCount
      (params : Set ℤ) C J Bx hJ hBx hparamBound
    have hcountReal : (fibre.card : ℝ) ≤
        1 + (Bx : ℝ) / (line.H : ℝ) := by
      rw [← hparamsCard]
      simpa [J] using hcount.2
    have hcardReal : (2 : ℝ) ≤ fibre.card := by exact_mod_cast hcardTwo
    have hHreal : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
    have hspacing : ((fibre.card : ℝ) - 1) * line.H ≤ Bx := by
      have hmul := mul_le_mul_of_nonneg_right hcountReal hHreal.le
      field_simp at hmul
      nlinarith
    have hfreqTwice : frequencyCutoff W ≤
        2 * ((fibre.card : ℝ) - 1) := by
      calc
        frequencyCutoff W ≤ fibre.card := hfreqCard
        _ ≤ 2 * ((fibre.card : ℝ) - 1) := by linarith
    have hHfreq : (line.H : ℝ) * frequencyCutoff W ≤
        2 * (Cx : ℝ) * W.X := by
      have hmul := mul_le_mul_of_nonneg_left hfreqTwice hHreal.le
      have hBxCast : (Bx : ℝ) = (Cx : ℝ) * W.X := by
        dsimp [Bx]
        push_cast
        ring
      rw [hBxCast] at hspacing
      nlinarith
    have hClockCx : 2 * (Cx : ℝ) ≤ Clock := by
      dsimp [Clock]
      norm_num
    have hbound : (line.H : ℝ) ≤
        Clock * W.X / frequencyCutoff W := by
      rw [le_div_iff₀ hfreqPos]
      calc
        (line.H : ℝ) * frequencyCutoff W ≤
            2 * (Cx : ℝ) * W.X := hHfreq
        _ ≤ Clock * W.X := by gcongr
    exact ⟨line, hline, hprimitive, hbound⟩

/-- Paper label: `lem:strict-unique` (Section 5). -/
theorem lem_strict_unique (μ : ℝ) (hμ : μ ∈ Set.Ioo (0 : ℝ) 1) :
    Set.Subsingleton {g : ℕ | 1 ≤ g ∧ (2 : ℝ) ^ g * μ - 1 ∈ Set.Ioo (0 : ℝ) 1} := by
  rintro g ⟨hg, hgI⟩ h ⟨hh, hhI⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsucc : g + 1 ≤ h := Nat.succ_le_iff.mpr hlt
    have hpow : (2 : ℝ) ^ (g + 1) ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hsucc
    rw [pow_succ] at hpow
    have hmul := mul_le_mul_of_nonneg_right hpow hμ.1.le
    nlinarith [hgI.1, hhI.2]
  · have hsucc : h + 1 ≤ g := Nat.succ_le_iff.mpr hgt
    have hpow : (2 : ℝ) ^ (h + 1) ≤ (2 : ℝ) ^ g :=
      pow_le_pow_right₀ (by norm_num) hsucc
    rw [pow_succ] at hpow
    have hmul := mul_le_mul_of_nonneg_right hpow hμ.1.le
    nlinarith [hhI.1, hgI.2]

/-- Paper label: `lem:step-monotone` (Section 5). -/
theorem lem_step_monotone (Q g : ℕ) (line : AffineLine) :
    (line.transform Q g).primitiveHorizontalStep ∣ line.H.natAbs := by
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left line.H.natAbs
    (line.transform Q g).K.natAbs)

/-- A boundary-transition word: every proper post-entry state is a boundary
state and the final state is exterior, unless the word is empty. -/
def IsBoundaryTransition (Q : ℕ) (line : AffineLine) (gaps : GapWord) : Prop :=
  gaps = [] ∨
    (∀ r < gaps.length, ∃ state : AffineLine,
      SharedGapTrajectory Q line (gaps.take r) state ∧
        classifySlope (state.slope Q) ∈
          ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion)) ∧
    ∃ finish : AffineLine,
      SharedGapTrajectory Q line gaps finish ∧
        classifySlope (finish.slope Q) = .exterior

/-- Paper label: `lem:boundary-stretch` (Section 5). -/
theorem lem_boundary_stretch (Q m L Cgap : ℕ) (line : AffineLine)
    (gaps : GapWord) (htrans : IsBoundaryTransition Q line gaps)
    (hlen : gaps.length ≤ m)
    (hgap : ∀ g ∈ gaps, g ≤ L + Cgap) :
    gaps.span ≤ m + 2 * (L + Cgap) := by
  have trajectory_nil_eq (start finish : AffineLine)
      (h : SharedGapTrajectory Q start [] finish) : finish = start := by
    cases h
    rfl
  have trajectory_cons_iff (start finish : AffineLine) (g : ℕ) (gs : GapWord) :
      SharedGapTrajectory Q start (g :: gs) finish ↔
        SharedGapTrajectory Q (start.transform Q g) gs finish := by
    constructor
    · intro h
      cases h with
      | cons _ next _ _ _ hnext htail =>
          subst next
          exact htail
    · intro h
      exact SharedGapTrajectory.cons start (start.transform Q g) finish g gs rfl h
  have boundary_slope (μ : ℚ)
      (hμ : classifySlope μ ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion)) :
      μ = 0 ∨ μ = 1 := by
    by_cases hzero : μ = 0
    · exact Or.inl hzero
    by_cases hone : μ = 1
    · exact Or.inr hone
    simp [classifySlope, hzero, hone] at hμ
    split at hμ <;> simp_all
  have slope_transform (hQ : 0 < Q) (start : AffineLine) (g : ℕ) :
      (start.transform Q g).slope Q =
        (2 : ℚ) ^ g * start.slope Q - 1 := by
    have hQ0 : (Q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    have hH0 : (start.H : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt start.H_pos)
    simp only [AffineLine.slope, AffineLine.transform]
    push_cast
    field_simp [hQ0, hH0]
  have boundary_gap_le_one (hQ : 0 < Q) (start : AffineLine) (g : ℕ)
      (hstart : classifySlope (start.slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
      (hnext : classifySlope ((start.transform Q g).slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion)) :
      g ≤ 1 := by
    rcases boundary_slope (start.slope Q) hstart with hzero | hone
    · rcases boundary_slope ((start.transform Q g).slope Q) hnext with hnextzero | hnextone
      · rw [slope_transform hQ start g, hzero] at hnextzero
        norm_num at hnextzero
      · rw [slope_transform hQ start g, hzero] at hnextone
        norm_num at hnextone
    · rcases boundary_slope ((start.transform Q g).slope Q) hnext with hnextzero | hnextone
      · by_contra hg
        have hg2 : 2 ≤ g := by omega
        have hpow : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ g :=
          pow_le_pow_right₀ (by norm_num) hg2
        rw [slope_transform hQ start g, hone] at hnextzero
        norm_num at hnextzero
        nlinarith
      · by_contra hg
        have hg2 : 2 ≤ g := by omega
        have hpow : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ g :=
          pow_le_pow_right₀ (by norm_num) hg2
        rw [slope_transform hQ start g, hone] at hnextone
        norm_num at hnextone
        nlinarith
  have span_bound : ∀ (start : AffineLine) (word : GapWord),
      IsBoundaryTransition Q start word →
      (∀ g ∈ word, g ≤ L + Cgap) →
      word.span ≤ word.length + (L + Cgap) := by
    intro start word
    induction word generalizing start with
    | nil => simp [GapWord.span]
    | cons g gs ih =>
        intro htransition hword
        rcases htransition with hempty | ⟨hboundary, hfinish⟩
        · simp at hempty
        · by_cases hgs : gs = []
          · subst gs
            have hg := hword g (by simp)
            simp only [GapWord.span, List.sum_cons, List.sum_nil, List.length_cons,
              List.length_nil]
            omega
          · have hQ : 0 < Q := by
              by_contra hnot
              have hQzero : Q = 0 := Nat.eq_zero_of_not_pos hnot
              subst Q
              rcases hfinish with ⟨finish, _htrajectory, hexterior⟩
              simp [AffineLine.slope, classifySlope] at hexterior
            rcases hboundary 0 (by simp) with ⟨initial, hinitial, hinitialBoundary⟩
            have hinitial_eq : initial = start := by
              apply trajectory_nil_eq start initial
              simpa using hinitial
            subst initial
            have hgsLength : 0 < gs.length := List.length_pos_iff.mpr hgs
            rcases hboundary 1 (by simp; omega) with ⟨next, hnext, hnextBoundary⟩
            have hnextTail :
                SharedGapTrajectory Q (start.transform Q g) [] next :=
              (trajectory_cons_iff start next g []).mp (by simpa using hnext)
            have hnext_eq : next = start.transform Q g :=
              trajectory_nil_eq (start.transform Q g) next hnextTail
            subst next
            have hg : g ≤ 1 :=
              boundary_gap_le_one hQ start g hinitialBoundary hnextBoundary
            have htailTransition :
                IsBoundaryTransition Q (start.transform Q g) gs := by
              right
              constructor
              · intro r hr
                rcases hboundary (r + 1) (by simp; omega) with
                  ⟨state, hstate, hstateBoundary⟩
                refine ⟨state, ?_, hstateBoundary⟩
                apply (trajectory_cons_iff start state g (gs.take r)).mp
                simpa [List.take_succ_cons] using hstate
              · rcases hfinish with ⟨finish, htrajectory, hexterior⟩
                exact ⟨finish,
                  (trajectory_cons_iff start finish g gs).mp htrajectory,
                  hexterior⟩
            have htailGap : ∀ x ∈ gs, x ≤ L + Cgap := by
              intro x hx
              exact hword x (by simp [hx])
            have htail := ih (start.transform Q g) htailTransition htailGap
            have htail' : gs.sum ≤ gs.length + (L + Cgap) := by
              simpa only [GapWord.span] using htail
            simp only [GapWord.span, List.sum_cons, List.length_cons]
            omega
  have hspan := span_bound line gaps htrans hgap
  have hscale : L + Cgap ≤ 2 * (L + Cgap) := by omega
  omega

private theorem classifySlope_mem_boundary_iff (μ : ℚ) :
    classifySlope μ ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) ↔
      μ = 0 ∨ μ = 1 := by
  constructor
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · left
      unfold classifySlope at h
      by_cases h0 : μ = 0
      · exact h0
      rw [if_neg h0] at h
      split at h
      next h1 => simp_all
      next h1 =>
        split at h <;> simp_all
    · right
      unfold classifySlope at h
      by_cases h0 : μ = 0
      · simp [h0] at h
      rw [if_neg h0] at h
      by_cases h1 : μ = 1
      · exact h1
      rw [if_neg h1] at h
      split at h <;> simp_all
  · rintro (rfl | rfl) <;> simp [classifySlope]

private theorem boundary_transform_of_nonexterior (Q g : ℕ) (hQ : 0 < Q)
    (hg : 1 ≤ g) (line : AffineLine)
    (hline : classifySlope (line.slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
    (hnext : classifySlope ((line.transform Q g).slope Q) ≠ .exterior) :
    classifySlope ((line.transform Q g).slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
  rcases (classifySlope_mem_boundary_iff _).mp hline with hzero | hone
  · have hslope : (line.transform Q g).slope Q = -1 := by
      rw [AffineLine.slope_transform Q hQ, hzero]
      ring
    exfalso
    apply hnext
    rw [hslope, classifySlope_eq_exterior_iff]
    exact Or.inl (by norm_num)
  · by_cases hg1 : g = 1
    · subst g
      apply (classifySlope_mem_boundary_iff _).2
      right
      rw [AffineLine.slope_transform Q hQ, hone]
      norm_num
    · have hg2 : 2 ≤ g := by omega
      have hpow : (4 : ℚ) ≤ (2 : ℚ) ^ g := by
        have hpow' := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hg2
        norm_num at hpow' ⊢
        exact hpow'
      exfalso
      apply hnext
      rw [AffineLine.slope_transform Q hQ, hone,
        classifySlope_eq_exterior_iff]
      right
      nlinarith

private theorem boundary_before_first_exterior (Q : ℕ) (hQ : 0 < Q) :
    ∀ (line : AffineLine) (word : GapWord),
      word.Positive →
      classifySlope (line.slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) →
      (∀ r < word.length,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) ≠ .exterior) →
      ∀ r < word.length,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) ∈
          ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
  intro line word
  induction word generalizing line with
  | nil => simp
  | cons g gs ih =>
      intro hpos hline hbefore r hr
      cases r with
      | zero => simpa only [List.take_zero, AffineLine.transformWord] using hline
      | succ r =>
          have hrTail : r < gs.length := by simpa using hr
          have hgsNonempty : gs ≠ [] := List.ne_nil_of_length_pos
            (lt_of_le_of_lt (Nat.zero_le r) hrTail)
          have hg : 1 ≤ g := hpos g (by simp)
          have hnextNon :
              classifySlope ((line.transform Q g).slope Q) ≠ .exterior := by
            have := hbefore 1 (by simp; exact List.length_pos_iff.mpr hgsNonempty)
            simpa only [List.take_succ_cons, List.take_zero,
              AffineLine.transformWord] using this
          have hnextBoundary := boundary_transform_of_nonexterior Q g hQ hg
            line hline hnextNon
          have htailPos : GapWord.Positive gs := by
            intro x hx
            exact hpos x (by simp [hx])
          have htailBefore : ∀ q < gs.length,
              classifySlope
                (((line.transform Q g).transformWord Q (gs.take q)).slope Q) ≠
                  .exterior := by
            intro q hq
            have := hbefore (q + 1) (by simpa using Nat.succ_lt_succ hq)
            simpa only [List.take_succ_cons, AffineLine.transformWord] using this
          simpa only [List.take_succ_cons, AffineLine.transformWord] using
            ih (line.transform Q g) htailPos hnextBoundary htailBefore r hrTail

private theorem take_isPrefix (word : GapWord) (r : ℕ) :
    (word.take r).IsPrefix word := by
  exact ⟨word.drop r, List.take_append_drop r word⟩

private theorem exists_first_noninterior (Q : ℕ) (line : AffineLine)
    (word : GapWord) (hnot : ¬ IsInteriorTrajectory Q line word) :
    ∃ j ≤ word.length,
      classifySlope ((line.transformWord Q (word.take j)).slope Q) ≠ .interior ∧
      ∀ r < j,
        classifySlope ((line.transformWord Q (word.take r)).slope Q) = .interior := by
  have hexists : ∃ j : ℕ, j ≤ word.length ∧
      classifySlope ((line.transformWord Q (word.take j)).slope Q) ≠ .interior := by
    by_contra hnone
    apply hnot
    intro r hr
    refine ⟨line.transformWord Q (word.take r),
      (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl, ?_⟩
    by_contra hregion
    exact hnone ⟨r, hr, hregion⟩
  let j := Nat.find hexists
  have hj := Nat.find_spec hexists
  refine ⟨j, hj.1, hj.2, ?_⟩
  intro r hr
  by_contra hregion
  exact (Nat.find_min hexists hr) ⟨le_trans (Nat.le_of_lt hr) hj.1, hregion⟩

private theorem isBoundaryTransition_of_first_exterior
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (hpos : word.Positive)
    (hline : classifySlope (line.slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
    (hbefore : ∀ r < word.length,
      classifySlope ((line.transformWord Q (word.take r)).slope Q) ≠ .exterior)
    (hfinal : classifySlope ((line.transformWord Q word).slope Q) = .exterior) :
    IsBoundaryTransition Q line word := by
  by_cases hnil : word = []
  · exact Or.inl hnil
  right
  constructor
  · intro r hr
    refine ⟨line.transformWord Q (word.take r),
      (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl, ?_⟩
    exact boundary_before_first_exterior Q hQ line word hpos hline hbefore r hr
  · refine ⟨line.transformWord Q word,
      (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl, hfinal⟩

private theorem exists_virtual_boundary_transition
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (hpos : word.Positive)
    (hline : classifySlope (line.slope Q) ∈
      ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion))
    (hnone : ∀ r ≤ word.length,
      classifySlope ((line.transformWord Q (word.take r)).slope Q) ≠ .exterior) :
    ∃ exitGap : ℕ, 1 ≤ exitGap ∧ exitGap ≤ 2 ∧
      IsBoundaryTransition Q line (word ++ [exitGap]) := by
  have hproperDummy : ∀ r < (word ++ [1]).length,
      classifySlope ((line.transformWord Q ((word ++ [1]).take r)).slope Q) ≠
        .exterior := by
    intro r hr
    have hrle : r ≤ word.length := by simpa using hr
    rw [List.take_append_of_le_length hrle]
    exact hnone r hrle
  have hposDummy : (word ++ [1]).Positive := by
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hpos g hg
    · norm_num
  have hendBoundary :
      classifySlope ((line.transformWord Q word).slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
    have h := boundary_before_first_exterior Q hQ line (word ++ [1])
      hposDummy hline hproperDummy word.length (by simp)
    simpa [List.take_append_of_le_length (le_refl word.length)] using h
  rcases (classifySlope_mem_boundary_iff _).mp hendBoundary with hzero | hone
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    apply isBoundaryTransition_of_first_exterior Q hQ line (word ++ [1])
      hposDummy hline hproperDummy
    simp only [AffineLine.transformWord_append, AffineLine.transformWord]
    rw [AffineLine.slope_transform Q hQ, hzero]
    norm_num [classifySlope]
  · let extended := word ++ [2]
    have hproper : ∀ r < extended.length,
        classifySlope ((line.transformWord Q (extended.take r)).slope Q) ≠
          .exterior := by
      intro r hr
      have hrle : r ≤ word.length := by simpa [extended] using hr
      simp only [extended, List.take_append_of_le_length hrle]
      exact hnone r hrle
    have hposExtended : extended.Positive := by
      intro g hg
      simp only [extended, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hpos g hg
      · norm_num
    refine ⟨2, by norm_num, by norm_num, ?_⟩
    apply isBoundaryTransition_of_first_exterior Q hQ line extended
      hposExtended hline hproper
    simp only [extended, AffineLine.transformWord_append, AffineLine.transformWord]
    rw [AffineLine.slope_transform Q hQ, hone]
    norm_num [classifySlope]

theorem longExteriorSplit_of_no_longInterior
    (Q : ℕ) (hQ : 0 < Q) (line : AffineLine) (word : GapWord)
    (y : ℝ) (m cap : ℕ) (hy : 0 < y)
    (hpos : word.Positive) (hlen : word.length ≤ m)
    (hcapTwo : 2 ≤ cap) (hcap : ∀ g ∈ word, g ≤ cap)
    (hremaining : y / 2 ≤ (word.span : ℝ))
    (hno : ∀ u : GapWord, u.IsPrefix word →
      IsInteriorTrajectory Q line u → (u.span : ℝ) < y / 8)
    (hloss : ((m + 1 + 3 * cap : ℕ) : ℝ) ≤ y / 8) :
    ∃ before continuation : GapWord, ∃ exteriorLine : AffineLine,
      word = before ++ continuation ∧
      SharedGapTrajectory Q line before exteriorLine ∧
      (∀ r < before.length, ∀ state : AffineLine,
        SharedGapTrajectory Q line (before.take r) state →
          classifySlope (state.slope Q) ≠ .exterior) ∧
      classifySlope (exteriorLine.slope Q) = .exterior ∧
      IsExteriorTrajectory Q exteriorLine continuation ∧
      y / 4 ≤ (continuation.span : ℝ) := by
  have hnotFull : ¬ IsInteriorTrajectory Q line word := by
    intro hfull
    have hshort := hno word ⟨[], by simp⟩ hfull
    linarith
  obtain ⟨j, hjlen, hjnon, hjbefore⟩ :=
    exists_first_noninterior Q line word hnotFull
  let lineJ := line.transformWord Q (word.take j)
  have hprefixJ : (word.take j).IsPrefix word := take_isPrefix word j
  have hprefixJBound : (GapWord.span (word.take j) : ℝ) < y / 8 + cap := by
    cases j with
    | zero =>
        simp only [List.take_zero, GapWord.span, List.sum_nil, Nat.cast_zero]
        positivity
    | succ i =>
        have hiLen : i < word.length := lt_of_lt_of_le (Nat.lt_succ_self i) hjlen
        have hint : IsInteriorTrajectory Q line (word.take i) := by
          intro r hr
          have hriLe : r ≤ i := hr.trans (List.length_take_le i word)
          have hri : r < i + 1 := Nat.lt_succ_iff.mpr hriLe
          refine ⟨line.transformWord Q (word.take r), ?_, hjbefore r hri⟩
          have htake : (word.take i).take r = word.take r := by
            rw [List.take_take, min_eq_left hriLe]
          simpa only [htake] using
            (sharedGapTrajectory_iff_transformWord Q line (word.take r)
              (line.transformWord Q (word.take r))).2 rfl
        have hshort := hno (word.take i) (take_isPrefix word i) hint
        have hsum := List.sum_take_succ word i hiLen
        have helem : word[i] ≤ cap := hcap word[i] (List.getElem_mem hiLen)
        have hsumReal : ((word.take (i + 1)).sum : ℝ) =
            ((word.take i).sum : ℝ) + word[i] := by exact_mod_cast hsum
        have helemReal : (word[i] : ℝ) ≤ cap := by exact_mod_cast helem
        change ((word.take i).sum : ℝ) < y / 8 at hshort
        change ((word.take (i + 1)).sum : ℝ) < y / 8 + cap
        linarith
  have hcapLoss : (cap : ℝ) ≤ y / 8 := by
    have hnat : cap ≤ m + 1 + 3 * cap := by omega
    exact (by exact_mod_cast hnat : (cap : ℝ) ≤ (m + 1 + 3 * cap : ℕ)).trans hloss
  by_cases hjExterior : classifySlope (lineJ.slope Q) = .exterior
  · refine ⟨word.take j, word.drop j, lineJ, ?_, ?_, ?_, hjExterior, ?_, ?_⟩
    · exact (List.take_append_drop j word).symm
    · exact (sharedGapTrajectory_iff_transformWord Q line _ _).2 rfl
    · intro r hr state hstate
      have hrj : r < j := by simpa [List.length_take, hjlen] using hr
      have htake : (word.take j).take r = word.take r := by
        rw [List.take_take, min_eq_left (Nat.le_of_lt hrj)]
      have hstateEq :=
        (sharedGapTrajectory_iff_transformWord Q line _ state).1 hstate
      rw [htake] at hstateEq
      subst state
      rw [hjbefore r hrj]
      decide
    · apply isExteriorTrajectory_of_positive Q hQ lineJ (word.drop j)
      · intro g hg
        exact hpos g (List.mem_of_mem_drop hg)
      · exact hjExterior
    · have hsum : (word.span : ℝ) =
          (GapWord.span (word.take j) : ℝ) +
            (GapWord.span (word.drop j) : ℝ) := by
        have := congrArg (fun w : GapWord => (w.span : ℝ))
          (List.take_append_drop j word)
        simpa only [GapWord.span, List.sum_append, Nat.cast_add] using this.symm
      linarith
  · have hjnon' : classifySlope (lineJ.slope Q) ≠ .interior := by
      simpa only [lineJ] using hjnon
    have hjBoundary : classifySlope (lineJ.slope Q) ∈
        ({SlopeRegion.boundaryZero, SlopeRegion.boundaryOne} : Set SlopeRegion) := by
      cases hregion : classifySlope (lineJ.slope Q) with
      | interior => exact (hjnon' hregion).elim
      | boundaryZero => simp
      | boundaryOne => simp
      | exterior => exact (hjExterior hregion).elim
    let tail := word.drop j
    have htailPos : GapWord.Positive tail := by
      intro g hg
      exact hpos g (List.mem_of_mem_drop hg)
    have htailLen : tail.length ≤ m := by
      have htailWord : tail.length ≤ word.length := by
        dsimp [tail]
        rw [List.length_drop]
        omega
      exact htailWord.trans hlen
    have htailCap : ∀ g ∈ tail, g ≤ cap := by
      intro g hg
      exact hcap g (List.mem_of_mem_drop hg)
    by_cases hexists : ∃ t : ℕ, t ≤ tail.length ∧
        classifySlope ((lineJ.transformWord Q (tail.take t)).slope Q) = .exterior
    · let t := Nat.find hexists
      have ht := Nat.find_spec hexists
      have htBefore : ∀ r < t,
          classifySlope ((lineJ.transformWord Q (tail.take r)).slope Q) ≠
            .exterior := by
        intro r hr hext
        exact (Nat.find_min hexists hr) ⟨le_trans (Nat.le_of_lt hr) ht.1, hext⟩
      let transition := tail.take t
      let exteriorLine := lineJ.transformWord Q transition
      have htransitionLen : transition.length ≤ m := by
        dsimp [transition]
        rw [List.length_take_of_le ht.1]
        exact ht.1.trans htailLen
      have htransitionCap : ∀ g ∈ transition, g ≤ cap := by
        intro g hg
        exact htailCap g (List.mem_of_mem_take hg)
      have htransitionPos : GapWord.Positive transition := by
        intro g hg
        exact htailPos g (List.mem_of_mem_take hg)
      have htransitionBoundary : IsBoundaryTransition Q lineJ transition := by
        apply isBoundaryTransition_of_first_exterior Q hQ lineJ transition
          htransitionPos hjBoundary
        · intro r hr
          have htransitionLength : transition.length = t := by
            dsimp [transition]
            exact List.length_take_of_le ht.1
          have hr' : r < t := by simpa only [htransitionLength] using hr
          have htake : transition.take r = tail.take r := by
            simp [transition, List.take_take, min_eq_left (Nat.le_of_lt hr')]
          simpa only [htake] using htBefore r hr'
        · simpa only [transition, exteriorLine] using ht.2
      have htransitionSpan : GapWord.span transition ≤ m + 2 * cap := by
        exact lem_boundary_stretch Q m cap 0 lineJ transition htransitionBoundary
          htransitionLen (by simpa using htransitionCap)
      let before := word.take (j + t)
      let continuation := word.drop (j + t)
      have hjtLen : j + t ≤ word.length := by
        have htlen : t ≤ tail.length := ht.1
        dsimp [tail] at htlen
        rw [List.length_drop] at htlen
        omega
      have hbeforeSplit : before = word.take j ++ transition := by
        dsimp [before, transition, tail]
        exact List.take_add
      have hbeforeBound : (GapWord.span before : ℝ) < y / 4 := by
        have htransitionSpanReal : (GapWord.span transition : ℝ) ≤ m + 2 * cap := by
          exact_mod_cast htransitionSpan
        have hbeforeSpan : (GapWord.span before : ℝ) =
            (GapWord.span (word.take j) : ℝ) + GapWord.span transition := by
          have hnat : GapWord.span before =
              GapWord.span (word.take j) + GapWord.span transition := by
            change before.sum = (word.take j).sum + transition.sum
            rw [hbeforeSplit, List.sum_append]
          exact_mod_cast hnat
        have hloss' : ((m : ℝ) + 3 * cap) ≤ y / 8 := by
          have hnat : m + 3 * cap ≤ m + 1 + 3 * cap := by omega
          have hcast : ((m + 3 * cap : ℕ) : ℝ) ≤ y / 8 :=
            (by exact_mod_cast hnat :
              ((m + 3 * cap : ℕ) : ℝ) ≤ (m + 1 + 3 * cap : ℕ)).trans hloss
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcast
        rw [hbeforeSpan]
        nlinarith
      refine ⟨before, continuation, exteriorLine, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (List.take_append_drop (j + t) word).symm
      · rw [sharedGapTrajectory_iff_transformWord]
        dsimp [exteriorLine]
        rw [hbeforeSplit, AffineLine.transformWord_append]
      · intro r hr state hstate
        have hrjt : r < j + t := by
          simpa [before, List.length_take, hjtLen] using hr
        have htakeBefore : before.take r = word.take r := by
          dsimp [before]
          rw [List.take_take, min_eq_left (Nat.le_of_lt hrjt)]
        have hstateEq :=
          (sharedGapTrajectory_iff_transformWord Q line _ state).1 hstate
        rw [htakeBefore] at hstateEq
        subst state
        by_cases hrj : r < j
        · rw [hjbefore r hrj]
          decide
        · let q := r - j
          have hrEq : r = j + q := by dsimp [q]; omega
          have hqt : q < t := by dsimp [q]; omega
          have hstateRewrite :
              line.transformWord Q (word.take r) =
                lineJ.transformWord Q (tail.take q) := by
            rw [hrEq, List.take_add, AffineLine.transformWord_append]
          rw [hstateRewrite]
          exact htBefore q hqt
      · simpa only [exteriorLine, transition] using ht.2
      · apply isExteriorTrajectory_of_positive Q hQ exteriorLine continuation
        · intro g hg
          exact hpos g (List.mem_of_mem_drop hg)
        · simpa only [exteriorLine, transition] using ht.2
      · have hsum : (word.span : ℝ) =
            (GapWord.span before : ℝ) + (GapWord.span continuation : ℝ) := by
          have := congrArg (fun w : GapWord => (w.span : ℝ))
            (List.take_append_drop (j + t) word)
          simpa only [before, continuation, GapWord.span, List.sum_append,
            Nat.cast_add] using this.symm
        linarith
    · have hnone : ∀ t ≤ tail.length,
          classifySlope ((lineJ.transformWord Q (tail.take t)).slope Q) ≠
            .exterior := by
        intro t ht hext
        exact hexists ⟨t, ht, hext⟩
      obtain ⟨exitGap, hexitPos, hexitTwo, hvirtual⟩ :=
        exists_virtual_boundary_transition Q hQ lineJ tail htailPos hjBoundary hnone
      have hvirtualLen : (tail ++ [exitGap]).length ≤ m + 1 := by
        simpa using Nat.add_le_add_right htailLen 1
      have hvirtualCap : ∀ g ∈ tail ++ [exitGap], g ≤ cap := by
        intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact htailCap g hg
        · exact hexitTwo.trans hcapTwo
      have hvirtualSpan := lem_boundary_stretch Q (m + 1) cap 0 lineJ
        (tail ++ [exitGap]) hvirtual hvirtualLen (by simpa using hvirtualCap)
      have htailSpan : GapWord.span tail ≤ m + 1 + 2 * cap := by
        have hsum : GapWord.span (tail ++ [exitGap]) =
            GapWord.span tail + exitGap := by
          simp [GapWord.span]
        rw [hsum] at hvirtualSpan
        omega
      have hwordSum : (word.span : ℝ) =
          (GapWord.span (word.take j) : ℝ) + (GapWord.span tail : ℝ) := by
        have := congrArg (fun w : GapWord => (w.span : ℝ))
          (List.take_append_drop j word)
        simpa only [tail, GapWord.span, List.sum_append, Nat.cast_add] using this.symm
      have htailSpanReal : (GapWord.span tail : ℝ) ≤ m + 1 + 2 * cap := by
        exact_mod_cast htailSpan
      have hlossReal : (m : ℝ) + 1 + 3 * cap ≤ y / 8 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
          using hloss
      rw [hwordSum] at hremaining
      nlinarith

private theorem eventually_boundary_loss_le (κ : ℝ) (hκ : 0 < κ)
    (Cgap : ℕ) :
    ∃ Zloss : ℕ, ∀ Z0 : ℕ, Zloss ≤ Z0 →
      ∀ᶠ L : ℕ in atTop,
        let m := Nat.floor (κ * (L : ℝ)) + 1
        (((m + 1 + 3 * (L + Cgap + 1) : ℕ) : ℝ) ≤
          (m : ℝ) * Z0 / 8) := by
  let coeff : ℝ := 8 * (2 + 3 / κ)
  let Zloss := Nat.ceil coeff
  refine ⟨Zloss, ?_⟩
  intro Z0 hZ0
  let constant : ℕ := 1 + 3 * (Cgap + 1)
  let L0 : ℕ := Nat.ceil ((constant : ℝ) / κ)
  filter_upwards [eventually_ge_atTop L0] with L hL
  dsimp only
  let m := Nat.floor (κ * (L : ℝ)) + 1
  have hκLnonneg : 0 ≤ κ * (L : ℝ) :=
    mul_nonneg hκ.le (Nat.cast_nonneg L)
  have hmLower : κ * (L : ℝ) < (m : ℝ) := by
    dsimp [m]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (κ * (L : ℝ)))
  have hconstantDiv : (constant : ℝ) / κ ≤ (L : ℝ) := by
    calc
      (constant : ℝ) / κ ≤ Nat.ceil ((constant : ℝ) / κ) := Nat.le_ceil _
      _ = (L0 : ℕ) := rfl
      _ ≤ L := by exact_mod_cast hL
  have hconstant : (constant : ℝ) ≤ κ * (L : ℝ) := by
    have := (div_le_iff₀ hκ).mp hconstantDiv
    simpa [mul_comm] using this
  have hconstantM : (constant : ℝ) ≤ m := hconstant.trans hmLower.le
  have hLover : (L : ℝ) < (m : ℝ) / κ := by
    exact (lt_div_iff₀ hκ).2 (by simpa [mul_comm] using hmLower)
  have hcoeffZ : coeff ≤ (Z0 : ℝ) := by
    calc
      coeff ≤ Nat.ceil coeff := Nat.le_ceil coeff
      _ = (Zloss : ℕ) := rfl
      _ ≤ Z0 := by exact_mod_cast hZ0
  have hmPos : (0 : ℝ) < m := by positivity
  have hlossExpand :
      (((m + 1 + 3 * (L + Cgap + 1) : ℕ) : ℝ)) =
        (m : ℝ) + 3 * L + constant := by
    dsimp [constant]
    push_cast
    ring
  rw [hlossExpand]
  have hbound : (m : ℝ) + 3 * L + constant <
      (2 + 3 / κ) * m := by
    have hthree : 3 * (L : ℝ) < (3 / κ) * m := by
      have := mul_lt_mul_of_pos_left hLover (by norm_num : (0 : ℝ) < 3)
      field_simp at this ⊢
      nlinarith
    nlinarith
  have hcoeffMul : 8 * ((2 + 3 / κ) * m) ≤ (Z0 : ℝ) * m := by
    have := mul_le_mul_of_nonneg_right hcoeffZ hmPos.le
    simpa [coeff, mul_assoc, mul_comm, mul_left_comm] using this
  nlinarith

/-- Paper label: `lem:dichotomy` (Section 5).  The cutoff is selected before
the numerator/support family; only the eventual scale may depend on that
family.  The gap constant must carry the uniform theorem supplied by
`lem_gap`, rather than being an arbitrary natural number. -/
theorem lem_dichotomy (context : FixedScaleContext)
    (gap : GapParams context.Q) :
    ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop, ∀ e : WindowThreshold,
          e ∈ (F.system L).largePairs Z0 →
          IsFrequentPrefix (F.system L) Z0
            (initialLongPrefix (F.system L) e.1) →
          (LongInteriorPair (F.system L) Z0 e ∨
            LongExteriorPair (F.system L) Z0 e) ∧
          ¬ (LongInteriorPair (F.system L) Z0 e ∧
            LongExteriorPair (F.system L) Z0 e) := by
  classical
  obtain ⟨Cline, Clock, hClock, hlocking⟩ :=
    lem_ap_locking context.Q context.Q_pos
  obtain ⟨CQ, hCQ, hfirst⟩ := lem_firstdeep_exists context
  obtain ⟨Zloss, hZloss⟩ :=
    eventually_boundary_loss_le context.entropy.kappa
      context.entropy.kappa_pos gap.Cgap
  let Zfirst := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zmin := max Zfirst Zloss
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0 F hF
  have hZfirst : Zfirst ≤ Z0 := (le_max_left _ _).trans hZ0
  have hZlossBound : Zloss ≤ Z0 := (le_max_right _ _).trans hZ0
  have hdiff : 0 < context.structural.Caff - 2 := by
    linarith [context.structural.Caff_gt]
  let Lline := Nat.ceil (((Cline : ℝ) + 1) /
    (context.structural.Caff - 2))
  filter_upwards [hfirst Z0 (by simpa only [Zfirst] using hZfirst) F hF,
    eventually_rawWindowGap_le context gap F hF,
    hZloss Z0 hZlossBound,
    eventually_ge_atTop Lline,
    eventually_ge_atTop 1] with L hfirstL hgapL hlossL hLline hLone
  intro e he hfrequent
  let W := F.system L
  let p := initialLongPrefix W e.1
  let suffix := actualPostPrefixGaps W e.1
  have hlevel : W.L = L := F.level_eq L
  have hstruct : W.structural = context.structural :=
    (F.structural_eq L).trans hF.2.1
  have hentropy : W.entropy = context.entropy :=
    (F.entropy_eq L).trans hF.2.2.1
  have hden : W.rational.eta.den = context.Q := by
    change (F.system L).rational.eta.den = context.Q
    rw [F.rational_eq]
    exact hF.1
  have hWQpos : 0 < W.rational.eta.den := by
    rw [hden]
    exact context.Q_pos
  have hfirstE := hfirstL e he
  dsimp only at hfirstE
  have hpLower : context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
    have hlower := hfirstE.1
    change W.structural.Caff * (W.L : ℝ) < (p.span : ℝ) at hlower
    rw [hlevel, hstruct] at hlower
    exact hlower
  have hlineScale : (Cline : ℝ) <
      (context.structural.Caff - 2) * (L : ℝ) := by
    have hquot : ((Cline : ℝ) + 1) /
        (context.structural.Caff - 2) ≤ (L : ℝ) := by
      calc
        ((Cline : ℝ) + 1) / (context.structural.Caff - 2) ≤ Lline :=
          Nat.le_ceil _
        _ ≤ L := by exact_mod_cast hLline
    have hmul := (div_le_iff₀ hdiff).mp hquot
    nlinarith
  have hpLongReal : (2 * L + Cline : ℕ) < (p.span : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hpLong : 2 * W.L + Cline < p.span := by
    rw [hlevel]
    exact_mod_cast hpLongReal
  have heHigh : e.1 ∈ highAnchors W Z0 := by
    rw [highAnchors, Finset.mem_filter]
    exact ⟨he.1.1, e.2, he.1.2, he.2⟩
  have hpSet : p ∈ initialPrefixes W Z0 := by
    rw [initialPrefixes, Finset.mem_image]
    exact ⟨e.1, heHigh, rfl⟩
  obtain ⟨line, hline, hprimitive, hstep⟩ :=
    hlocking W hden Z0 p hpSet hpLong hfrequent
  have hdisjoint : ¬ (LongInteriorPair W Z0 e ∧
      LongExteriorPair W Z0 e) := by
    rintro ⟨hinterior, hexterior⟩
    exact hexterior.2.2.1 hinterior
  by_cases hinterior : LongInteriorPair W Z0 e
  · exact ⟨Or.inl hinterior, hdisjoint⟩
  · have hmEq : W.m =
        Nat.floor (context.entropy.kappa * (L : ℝ)) + 1 := by
      rw [WindowSystem.m]
      change (F.system L).s + 1 = _
      rw [F.offset_eq, hF.2.2.1]
    have hlossBase :
        (((W.m + 1 + 3 * (L + gap.Cgap + 1) : ℕ) : ℝ) ≤
          (W.m : ℝ) * Z0 / 8) := by
      simpa only [hmEq] using hlossL
    have hlarge : (W.m : ℝ) * (Z0 : ℝ) < W.excess e := by
      simpa only [Set.mem_setOf_eq, Nat.cast_mul] using he.2
    have hy : 0 < W.excess e := by
      have hnonneg : 0 ≤ (W.m : ℝ) * (Z0 : ℝ) := by positivity
      exact hnonneg.trans_lt hlarge
    have hlossExcess :
        (((W.m + 1 + 3 * (L + gap.Cgap + 1) : ℕ) : ℝ) ≤
          W.excess e / 8) := by
      exact hlossBase.trans (by nlinarith)
    have hsuffixNat : W.rawWindowSpan e.1 = p.span + suffix.span := by
      have hraw : (W.rawWindowGapWord e.1).span = W.rawWindowSpan e.1 := by
        unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
        split <;> rfl
      rw [← hraw]
      simpa only [p, suffix] using actualPostPrefixGaps_span W e.1
    have hsuffixEq :
        ((W.rawWindowSpan e.1 : ℝ) - (p.span : ℝ)) = suffix.span := by
      have hcast : (W.rawWindowSpan e.1 : ℝ) =
          (p.span : ℝ) + suffix.span := by exact_mod_cast hsuffixNat
      linarith
    have hsuffixRemaining : W.excess e / 2 ≤ (suffix.span : ℝ) := by
      rw [← hsuffixEq]
      simpa only [p] using hfirstE.2.2
    have hsuffixPos : suffix.Positive := actualPostPrefixGaps_positive W e.1
    have hsuffixLen : suffix.length ≤ W.m :=
      actualPostPrefixGaps_length_le W e.1
    let cap := L + gap.Cgap + 1
    have hcapTwo : 2 ≤ cap := by dsimp [cap]; omega
    have hsuffixCap : ∀ g ∈ suffix, g ≤ cap := by
      intro g hg
      exact hgapL e.1 he.1.1 g (List.mem_of_mem_drop hg)
    have hnoLong : ∀ u : GapWord, u.IsPrefix suffix →
        IsInteriorTrajectory W.rational.eta.den line u →
          (u.span : ℝ) < W.excess e / 8 := by
      intro u hu htrajectory
      by_contra hnot
      apply hinterior
      refine ⟨he, hfrequent, line, u, ?_, htrajectory, le_of_not_gt hnot⟩
      refine ⟨hline, hu, ?_⟩
      exact ⟨line.transformWord W.rational.eta.den u,
        (sharedGapTrajectory_iff_transformWord _ _ _ _).2 rfl⟩
    obtain ⟨before, continuation, exteriorLine, hsplit, hbeforeTrajectory,
        hfirstExterior, hexteriorSlope, hexteriorTrajectory, hcontinuationSpan⟩ :=
      longExteriorSplit_of_no_longInterior W.rational.eta.den hWQpos line
        suffix (W.excess e) W.m cap hy hsuffixPos hsuffixLen hcapTwo
        hsuffixCap hsuffixRemaining hnoLong (by simpa only [cap] using hlossExcess)
    have hactual : IsActualFirstExteriorContinuation W Z0 e
        exteriorLine continuation := by
      refine ⟨line, exteriorLine.transformWord W.rational.eta.den continuation,
        before, [], hline, ?_, hbeforeTrajectory, hfirstExterior,
        hexteriorSlope, ?_⟩
      · simpa only [suffix, List.append_nil] using hsplit
      · exact (sharedGapTrajectory_iff_transformWord _ _ _ _).2 rfl
    have hexteriorPair : LongExteriorPair W Z0 e := by
      refine ⟨he, hfrequent, hinterior, exteriorLine, continuation,
        hactual, hexteriorTrajectory, hcontinuationSpan⟩
    exact ⟨Or.inr hexteriorPair, hdisjoint⟩

end Erdos260
