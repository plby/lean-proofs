/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianBlockFactorization
import ErdosProblems.Erdos1165.ProfileListExponent

/-!
# Reindexing connected Gaussian blocks as constrained profiles

This file performs the finite change of variables used in HLOZ (A.12).
An independent family of killed Gaussian paths is read on its block
intervals; outside those intervals the deviation is zero.  Strictly ordered
blocks therefore give an injective family of genuine excursion profiles.
-/

open scoped BigOperators

namespace Erdos1165.GaussianMultiBlockProfile

noncomputable section

open AppendixFirstMoment GaussianSmallBall GaussianProfileReindex
  GaussianBlockFactorization ProfileA11Assembly ProfileTaylor

/-- The closed scale interval occupied by a Gaussian block. -/
def BlockContains (b : GaussianBlock) (l : ℕ) : Prop :=
  b.start ≤ l ∧ l ≤ b.start + b.steps

instance blockContainsDecidable (b : GaussianBlock) (l : ℕ) :
    Decidable (BlockContains b l) := by
  unfold BlockContains
  infer_instance

/-- The blocks occur in strictly increasing, disjoint scale intervals. -/
def StrictlyOrderedBlocks : List GaussianBlock → Prop
  | [] => True
  | b :: bs =>
      (∀ c ∈ bs, b.start + b.steps < c.start) ∧ StrictlyOrderedBlocks bs

/-- The centered integer deviation read from a family of killed block paths.
The value is zero at every scale not belonging to a block. -/
def independentBlockDeviation :
    {bs : List GaussianBlock} → IndependentGaussianBlockPaths bs → ℕ → ℤ
  | [], _p, _l => 0
  | b :: bs, p, l =>
      if h : BlockContains b l then
        gaussianBoxPathPosition p.1 ⟨l - b.start, by
          rw [BlockContains] at h
          omega⟩
      else independentBlockDeviation p.2 l

@[simp] lemma independentBlockDeviation_nil (p : Unit) (l : ℕ) :
    independentBlockDeviation (bs := []) p l = 0 := rfl

lemma independentBlockDeviation_cons_of_contains
    {b : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: bs)) {l : ℕ}
    (hl : BlockContains b l) :
    independentBlockDeviation p l =
      gaussianBoxPathPosition p.1 ⟨l - b.start, by
        rw [BlockContains] at hl
        omega⟩ := by
  rw [independentBlockDeviation, dif_pos hl]

lemma independentBlockDeviation_cons_of_not_contains
    {b : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: bs)) {l : ℕ}
    (hl : ¬BlockContains b l) :
    independentBlockDeviation p l = independentBlockDeviation p.2 l := by
  rw [independentBlockDeviation, dif_neg hl]

/-- Every nonzero deviation in the combined path family belongs to the box
of one of its blocks. -/
lemma independentBlockDeviation_eq_zero_or_mem
    {bs : List GaussianBlock} (p : IndependentGaussianBlockPaths bs) (l : ℕ) :
    independentBlockDeviation p l = 0 ∨
      ∃ b ∈ bs, BlockContains b l ∧
        independentBlockDeviation p l ∈ gaussianBox b.radius := by
  induction bs with
  | nil =>
      left
      change (0 : ℤ) = 0
      rfl
  | cons b bs ih =>
      by_cases hl : BlockContains b l
      · right
        refine ⟨b, by simp, hl, ?_⟩
        rw [independentBlockDeviation_cons_of_contains p hl]
        exact gaussianBoxPathPosition_mem p.1 _
      · rw [independentBlockDeviation_cons_of_not_contains p hl]
        rcases ih p.2 with hz | ⟨c, hc, hcl, hmem⟩
        · exact Or.inl hz
        · exact Or.inr ⟨c, by simp [hc], hcl, hmem⟩

@[simp] lemma centeredProfileValue_zero (l : ℕ) :
    centeredProfileValue l 0 = profileCenter l := by
  unfold centeredProfileValue
  simp

/-- The full profile obtained by filling all unoccupied scales with the
parabolic centre. -/
def embeddedMultiBlockProfile (n : ℕ) {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths bs) : Profile n :=
  fun i ↦ centeredProfileValue (scaleIndex i)
    (independentBlockDeviation p (scaleIndex i))

/-- Box and window bounds on every block imply that the combined profile is
in the exact HLOZ constrained-profile finset. -/
theorem embeddedMultiBlockProfile_mem_constrainedProfiles
    (n : ℕ) {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths bs) {delta : ℝ}
    (hcenter : ∀ b ∈ bs, ∀ l, BlockContains b l →
      b.radius ≤ profileCenter l)
    (hwidth : ∀ b ∈ bs, ∀ l, BlockContains b l →
      (b.radius : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    embeddedMultiBlockProfile n p ∈ constrainedProfiles n delta := by
  rw [mem_constrainedProfiles]
  intro i
  rcases independentBlockDeviation_eq_zero_or_mem p (scaleIndex i) with
    hz | ⟨b, hb, hbl, hmem⟩
  · rw [embeddedMultiBlockProfile, hz, centeredProfileValue_zero]
    unfold InProfileWindow
    simp only [Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, sub_self, abs_zero]
    exact Real.rpow_nonneg (by positivity) _
  · exact centeredProfileValue_in_window hmem
      (hcenter b hb (scaleIndex i) hbl)
      (hwidth b hb (scaleIndex i) hbl)

/-- Before the first block in a strictly ordered list, its combined
deviation is zero. -/
lemma independentBlockDeviation_eq_zero_of_lt_start
    {bs : List GaussianBlock} (p : IndependentGaussianBlockPaths bs)
    (l : ℕ) (hbefore : ∀ b ∈ bs, l < b.start) :
    independentBlockDeviation p l = 0 := by
  induction bs with
  | nil => cases p; rfl
  | cons b bs ih =>
      rw [independentBlockDeviation_cons_of_not_contains p (by
        intro hl
        exact (Nat.not_le_of_gt (hbefore b (by simp))) hl.1)]
      exact ih p.2 fun c hc ↦ hbefore c (by simp [hc])

/-- A block path can be read without interference from its strictly later
tail. -/
lemma independentBlockDeviation_head_position
    {b : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: bs))
    (j : Fin (b.steps + 1)) :
    independentBlockDeviation p (b.start + j.1) =
      gaussianBoxPathPosition p.1 j := by
  have hcontains : BlockContains b (b.start + j.1) :=
    ⟨by omega, by omega⟩
  rw [independentBlockDeviation, dif_pos hcontains]
  apply congrArg (gaussianBoxPathPosition p.1)
  apply Fin.ext
  change b.start + j.1 - b.start = j.1
  omega

@[simp] lemma gaussianBoxPathPosition_zero {R steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R steps x) :
    gaussianBoxPathPosition p (0 : Fin (steps + 1)) = x := by
  cases steps <;> rfl

lemma gaussianBoxPathPosition_one {R steps : ℕ} {x : ℤ}
    (p : GaussianBoxPath R (steps + 1) x) :
    gaussianBoxPathPosition p (1 : Fin (steps + 2)) = x + p.2.1.1 := by
  change gaussianBoxPathPosition p.2.2 0 = x + p.2.1.1
  exact gaussianBoxPathPosition_zero p.2.2

/-- Strict ordering makes the simultaneous block-to-profile map injective.
No path multiplicity is lost when the finite block sum is reindexed as a
sum over profiles. -/
theorem embeddedMultiBlockProfile_injective
    (n : ℕ) {bs : List GaussianBlock}
    (hordered : StrictlyOrderedBlocks bs)
    (hstart : ∀ b ∈ bs, 2 ≤ b.start)
    (hend : ∀ b ∈ bs, b.start + b.steps ≤ n)
    (hcenter : ∀ b ∈ bs, b.radius ≤ profileCenter b.start) :
    Function.Injective
      (embeddedMultiBlockProfile n (bs := bs)) := by
  induction bs with
  | nil =>
      intro p q _h
      cases p
      cases q
      rfl
  | cons b bs ih =>
      intro p q hpq
      have horderedHead : ∀ c ∈ bs,
          b.start + b.steps < c.start := hordered.1
      have horderedTail : StrictlyOrderedBlocks bs := hordered.2
      have hbstart : 2 ≤ b.start := hstart b (by simp)
      have hbend : b.start + b.steps ≤ n := hend b (by simp)
      have hbcenter : b.radius ≤ profileCenter b.start :=
        hcenter b (by simp)
      have hhead : p.1 = q.1 := by
        apply gaussianBoxPathValues_injective hbcenter
        apply List.ext_get
        · simp only [gaussianBoxPathValues_length]
        · intro k hkp hkq
          let j : Fin (b.steps + 1) :=
            ⟨k, by simpa [gaussianBoxPathValues_length] using hkp⟩
          rw [gaussianBoxPathValues_get b.start p.1 j,
            gaussianBoxPathValues_get b.start q.1 j]
          let i : Fin (n - 1) := ⟨b.start - 2 + j.1, by omega⟩
          have hscale : scaleIndex i = b.start + j.1 := by
            unfold scaleIndex
            dsimp only [i]
            omega
          have hentry := congrFun hpq i
          change centeredProfileValue (scaleIndex i)
              (independentBlockDeviation p (scaleIndex i)) =
            centeredProfileValue (scaleIndex i)
              (independentBlockDeviation q (scaleIndex i)) at hentry
          rw [hscale, independentBlockDeviation_head_position p j,
            independentBlockDeviation_head_position q j] at hentry
          exact hentry
      have htail : p.2 = q.2 := by
        apply ih horderedTail
          (fun c hc ↦ hstart c (by simp [hc]))
          (fun c hc ↦ hend c (by simp [hc]))
          (fun c hc ↦ hcenter c (by simp [hc]))
        funext i
        let l : ℕ := scaleIndex i
        by_cases hle : l ≤ b.start + b.steps
        · have hbefore : ∀ c ∈ bs, l < c.start := by
            intro c hc
            exact hle.trans_lt (horderedHead c hc)
          have hpzero := independentBlockDeviation_eq_zero_of_lt_start
            p.2 l hbefore
          have hqzero := independentBlockDeviation_eq_zero_of_lt_start
            q.2 l hbefore
          change centeredProfileValue l (independentBlockDeviation p.2 l) =
            centeredProfileValue l (independentBlockDeviation q.2 l)
          rw [hpzero, hqzero]
        · have hbnot : ¬BlockContains b l := by
            intro hl
            exact hle hl.2
          have hentry := congrFun hpq i
          change centeredProfileValue l
                (independentBlockDeviation p l) =
              centeredProfileValue l
                (independentBlockDeviation q l) at hentry
          rw [independentBlockDeviation_cons_of_not_contains p hbnot,
            independentBlockDeviation_cons_of_not_contains q hbnot] at hentry
          exact hentry
      apply Prod.ext
      · exact hhead
      · exact htail

/-! ## Exact Gaussian weight of the combined deviation profile -/

/-- The logarithm of the Gaussian normalizing denominator agrees with the
normalizer used in `ProfileA11Assembly`. -/
lemma log_gaussianStepDenominator {l : ℕ} (hl : 0 < l) :
    Real.log (2 * Real.sqrt (2 * Real.pi) * (l : ℝ)) =
      Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 := by
  let z : ℝ := 2 * Real.sqrt (2 * Real.pi) * (l : ℝ)
  have hzsq : z ^ 2 = 8 * Real.pi * (l : ℝ) ^ 2 := by
    dsimp only [z]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    ring
  calc
    Real.log z = (2 * Real.log z) / 2 := by ring
    _ = Real.log (z ^ 2) / 2 := by rw [Real.log_pow]; norm_num
    _ = Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 := by rw [hzsq]

lemma gaussianStepWeight_eq_exp_edgeLog {l : ℕ} (hl : 0 < l) (d : ℤ) :
    gaussianStepWeight l d =
      Real.exp (-((d : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2) -
        Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2) := by
  have hden : (0 : ℝ) < 2 * Real.sqrt (2 * Real.pi) * l := by positivity
  rw [Real.exp_sub, ← log_gaussianStepDenominator hl,
    Real.exp_log hden]
  rfl

/-- Product of all centered Gaussian edge weights of an integer deviation
profile. -/
def gaussianDeviationProduct (n : ℕ) (D : ℕ → ℤ) : ℝ :=
  ∏ l ∈ Finset.Ico 2 n,
    gaussianStepWeight l (D (l + 1) - D l)

/-- The finite product is exactly the exponential Gaussian energy appearing
in A.11, including every normalizer. -/
theorem gaussianDeviationProduct_eq_exp (n : ℕ) (D : ℕ → ℤ) :
    gaussianDeviationProduct n D =
      Real.exp (-gaussianEnergy n (fun l ↦ (D l : ℝ)) -
        gaussianNormalizerLogSum n) := by
  have hsum :
      -gaussianEnergy n (fun l ↦ (D l : ℝ)) -
          gaussianNormalizerLogSum n =
        ∑ l ∈ Finset.Ico 2 n,
          (-(((D (l + 1) - D l : ℤ) : ℝ) ^ 2) /
              (8 * (l : ℝ) ^ 2) -
            Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2) := by
    unfold gaussianEnergy gaussianNormalizerLogSum
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    push_cast
    ring
  rw [hsum, Real.exp_sum]
  unfold gaussianDeviationProduct
  apply Finset.prod_congr rfl
  intro l hl
  exact gaussianStepWeight_eq_exp_edgeLog (l := l)
    (lt_of_lt_of_le (by norm_num : 0 < 2) (Finset.mem_Ico.mp hl).1)
    (D (l + 1) - D l)

/-- Gaussian product on a consecutive scale segment. -/
def gaussianSegmentProduct (start : ℕ) : ℕ → (ℕ → ℤ) → ℝ
  | 0, _D => 1
  | steps + 1, D =>
      gaussianStepWeight start (D (start + 1) - D start) *
        gaussianSegmentProduct (start + 1) steps D

/-- A killed path has the segment product determined by its positions. -/
lemma gaussianBoxPathWeight_eq_segment_of_positions (l : ℕ)
    {R steps : ℕ} {x : ℤ} (p : GaussianBoxPath R steps x)
    (D : ℕ → ℤ)
    (hD : ∀ j : Fin (steps + 1),
      D (l + j.1) = gaussianBoxPathPosition p j) :
    gaussianBoxPathWeight l p = gaussianSegmentProduct l steps D := by
  induction steps generalizing l x with
  | zero => simp [gaussianBoxPathWeight, gaussianSegmentProduct]
  | succ steps ih =>
      change gaussianStepWeight l p.2.1.1 *
          gaussianBoxPathWeight (l + 1) p.2.2 =
        gaussianStepWeight l (D (l + 1) - D l) *
          gaussianSegmentProduct (l + 1) steps D
      have hzero := hD (0 : Fin (steps + 2))
      have hone := hD (1 : Fin (steps + 2))
      rw [gaussianBoxPathPosition_zero] at hzero
      rw [gaussianBoxPathPosition_one] at hone
      simp only [Nat.add_zero, Fin.val_zero, Fin.val_one] at hzero hone
      have hfirst : D (l + 1) - D l = p.2.1.1 := by omega
      rw [hfirst]
      congr 1
      apply ih (l := l + 1) p.2.2
      intro j
      have hsucc := hD j.succ
      change D (l + 1 + j.1) = gaussianBoxPathPosition p.2.2 j
      simpa [gaussianBoxPathPosition, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hsucc

lemma gaussianSegmentProduct_add (start a b : ℕ) (D : ℕ → ℤ) :
    gaussianSegmentProduct start (a + b) D =
      gaussianSegmentProduct start a D *
        gaussianSegmentProduct (start + a) b D := by
  induction a generalizing start with
  | zero => simp [gaussianSegmentProduct]
  | succ a ih =>
      rw [Nat.succ_add, gaussianSegmentProduct, gaussianSegmentProduct, ih]
      rw [show start + (a + 1) = start + 1 + a by omega]
      ring

lemma gaussianSegmentProduct_congr {start steps : ℕ} {D E : ℕ → ℤ}
    (h : ∀ l, start ≤ l → l ≤ start + steps → D l = E l) :
    gaussianSegmentProduct start steps D =
      gaussianSegmentProduct start steps E := by
  induction steps generalizing start with
  | zero => rfl
  | succ steps ih =>
      rw [gaussianSegmentProduct, gaussianSegmentProduct]
      have hstart := h start (by omega) (by omega)
      have hnext := h (start + 1) (by omega) (by omega)
      rw [hstart, hnext]
      congr 1
      apply ih
      intro l hl hupper
      exact h l (by omega) (by omega)

lemma gaussianSegmentProduct_eq_prod_Ico (start steps : ℕ) (D : ℕ → ℤ) :
    gaussianSegmentProduct start steps D =
      ∏ l ∈ Finset.Ico start (start + steps),
        gaussianStepWeight l (D (l + 1) - D l) := by
  induction steps generalizing start with
  | zero => simp [gaussianSegmentProduct]
  | succ steps ih =>
      rw [gaussianSegmentProduct, ih]
      have hsplit := Finset.prod_Ico_consecutive
        (fun l ↦ gaussianStepWeight l (D (l + 1) - D l))
        (show start ≤ start + 1 by omega)
        (show start + 1 ≤ start + (steps + 1) by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit

lemma gaussianDeviationProduct_eq_segment {n : ℕ} (hn : 2 ≤ n)
    (D : ℕ → ℤ) :
    gaussianDeviationProduct n D = gaussianSegmentProduct 2 (n - 2) D := by
  rw [gaussianSegmentProduct_eq_prod_Ico]
  unfold gaussianDeviationProduct
  rw [Nat.add_sub_of_le hn]

/-- Consecutive blocks leave exactly one reset edge between successive block
intervals. -/
def ConsecutiveBlocks : List GaussianBlock → Prop
  | [] => True
  | [_b] => True
  | b :: c :: bs =>
      c.start = b.start + b.steps + 1 ∧ ConsecutiveBlocks (c :: bs)

lemma consecutiveBlocks_strictlyOrdered : ∀ {bs : List GaussianBlock},
    ConsecutiveBlocks bs → StrictlyOrderedBlocks bs
  | [], _h => trivial
  | [_b], _h => ⟨by simp, trivial⟩
  | b :: c :: bs, h => by
      have htail := consecutiveBlocks_strictlyOrdered h.2
      have hnext : c.start = b.start + b.steps + 1 := h.1
      refine ⟨?_, htail⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · have hcd := htail.1 d hd
        have hcD : c.start < d.start :=
          (Nat.le_add_right c.start c.steps).trans_lt hcd
        exact (show b.start + b.steps < c.start by omega).trans hcD

/-- Terminal scale of the last block (zero for the empty list). -/
def gaussianBlocksEnd : List GaussianBlock → ℕ
  | [] => 0
  | [b] => b.start + b.steps
  | _b :: c :: bs => gaussianBlocksEnd (c :: bs)

lemma gaussianBlocksEnd_ge_start {b : GaussianBlock} {bs : List GaussianBlock}
    (h : ConsecutiveBlocks (b :: bs)) :
    b.start ≤ gaussianBlocksEnd (b :: bs) := by
  induction bs generalizing b with
  | nil => simp [gaussianBlocksEnd]
  | cons c bs ih =>
      dsimp only [gaussianBlocksEnd]
      have hnext := h.1
      exact (show b.start ≤ c.start by omega).trans (ih h.2)

lemma gaussianBlockEnd_le_blocksEnd_of_mem :
    ∀ {bs : List GaussianBlock}, ConsecutiveBlocks bs →
      ∀ {c : GaussianBlock}, c ∈ bs →
        c.start + c.steps ≤ gaussianBlocksEnd bs
  | [], _h, c, hc => by simp at hc
  | [b], _h, c, hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst c
      simp [gaussianBlocksEnd]
  | b :: d :: bs, h, c, hc => by
      dsimp only [gaussianBlocksEnd]
      rcases List.mem_cons.mp hc with rfl | hc
      · have hdEnd := gaussianBlocksEnd_ge_start h.2
        have hnext : d.start = c.start + c.steps + 1 := h.1
        omega
      · exact gaussianBlockEnd_le_blocksEnd_of_mem h.2 hc

lemma gaussianBoxPathWeight_eq_independentSegment
    {b : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: bs)) :
    gaussianBoxPathWeight b.start p.1 =
      gaussianSegmentProduct b.start b.steps
        (independentBlockDeviation p) := by
  apply gaussianBoxPathWeight_eq_segment_of_positions
  intro j
  exact independentBlockDeviation_head_position p j

lemma independentBlockDeviation_connector
    {b c : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: c :: bs))
    (hnext : c.start = b.start + b.steps + 1) :
    independentBlockDeviation p (b.start + b.steps + 1) -
        independentBlockDeviation p (b.start + b.steps) =
      -gaussianBoxPathEndpoint p.1 := by
  have hend := independentBlockDeviation_head_position p (Fin.last b.steps)
  have hbnot : ¬BlockContains b (b.start + b.steps + 1) := by
    intro h
    exact (Nat.not_succ_le_self _) h.2
  have htail : independentBlockDeviation p.2 c.start = 0 := by
    have h := independentBlockDeviation_head_position
      (p.2 : IndependentGaussianBlockPaths (c :: bs))
      (0 : Fin (c.steps + 1))
    rw [gaussianBoxPathPosition_zero] at h
    simpa using h
  have hend' : independentBlockDeviation p (b.start + b.steps) =
      gaussianBoxPathEndpoint p.1 := by
    simpa [gaussianBoxPathEndpoint] using hend
  rw [independentBlockDeviation_cons_of_not_contains p hbnot]
  rw [show b.start + b.steps + 1 = c.start by omega, htail, hend']
  exact Int.zero_sub _

/-- For consecutive blocks, the connected path weight is exactly the
Gaussian segment product from the first block start to the last block end. -/
theorem connectedGaussianBlockWeight_eq_segment
    {b : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: bs))
    (hconsecutive : ConsecutiveBlocks (b :: bs)) :
    connectedGaussianBlockWeight p =
      gaussianSegmentProduct b.start
        (gaussianBlocksEnd (b :: bs) - b.start)
        (independentBlockDeviation p) := by
  induction bs generalizing b with
  | nil =>
      rcases p with ⟨pb, u⟩
      cases u
      let p0 : IndependentGaussianBlockPaths [b] := ⟨pb, ()⟩
      have hpath := gaussianBoxPathWeight_eq_independentSegment p0
      simpa [p0, connectedGaussianBlockWeight, gaussianBlocksEnd] using hpath
  | cons c bs ih =>
      change gaussianBoxPathWeight b.start p.1 *
          gaussianStepWeight (b.start + b.steps)
            (-gaussianBoxPathEndpoint p.1) *
          connectedGaussianBlockWeight p.2 =
        gaussianSegmentProduct b.start
          (gaussianBlocksEnd (c :: bs) - b.start)
          (independentBlockDeviation p)
      have hnext := hconsecutive.1
      have htail := ih p.2 hconsecutive.2
      have hblock := gaussianBoxPathWeight_eq_independentSegment p
      have hconnector := independentBlockDeviation_connector p hnext
      let tailSteps := gaussianBlocksEnd (c :: bs) - c.start
      have htailSegment :
          gaussianSegmentProduct c.start tailSteps
              (independentBlockDeviation p.2) =
            gaussianSegmentProduct c.start tailSteps
              (independentBlockDeviation p) := by
        apply gaussianSegmentProduct_congr
        intro l hl _hupper
        symm
        apply independentBlockDeviation_cons_of_not_contains p
        intro hb
        rw [BlockContains] at hb
        have hcstart : b.start + b.steps < c.start := by omega
        omega
      rw [hblock, htail]
      change gaussianSegmentProduct b.start b.steps
            (independentBlockDeviation p) *
          gaussianStepWeight (b.start + b.steps)
            (-gaussianBoxPathEndpoint p.1) *
          gaussianSegmentProduct c.start tailSteps
            (independentBlockDeviation p.2) = _
      rw [htailSegment]
      rw [show gaussianStepWeight (b.start + b.steps)
            (-gaussianBoxPathEndpoint p.1) =
          gaussianSegmentProduct (b.start + b.steps) 1
            (independentBlockDeviation p) by
        simp [gaussianSegmentProduct, hconnector]]
      rw [← gaussianSegmentProduct_add]
      rw [show c.start = b.start + (b.steps + 1) by omega]
      rw [← gaussianSegmentProduct_add]
      congr 2
      have hcEnd : c.start ≤ gaussianBlocksEnd (c :: bs) :=
        gaussianBlocksEnd_ge_start hconsecutive.2
      dsimp only [tailSteps, gaussianBlocksEnd]
      omega

/-- The Gaussian normalizer product on the centered prefix before the first
block. -/
def gaussianCenteredPrefixProduct (start : ℕ) : ℝ :=
  gaussianSegmentProduct 2 (start - 2) (fun _ ↦ 0)

lemma gaussianSegmentProduct_nonneg (start steps : ℕ) (D : ℕ → ℤ) :
    0 ≤ gaussianSegmentProduct start steps D := by
  induction steps generalizing start with
  | zero => simp [gaussianSegmentProduct]
  | succ steps ih =>
      rw [gaussianSegmentProduct]
      exact mul_nonneg (gaussianStepWeight_nonneg _ _) (ih (start + 1))

lemma gaussianCenteredPrefixProduct_nonneg (start : ℕ) :
    0 ≤ gaussianCenteredPrefixProduct start :=
  gaussianSegmentProduct_nonneg _ _ _

lemma independentBlockDeviation_eq_zero_of_le_first_start
    {b : GaussianBlock} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths (b :: bs))
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    {l : ℕ} (hl : l ≤ b.start) :
    independentBlockDeviation p l = 0 := by
  rcases hl.eq_or_lt with rfl | hlt
  · have h := independentBlockDeviation_head_position p
      (0 : Fin (b.steps + 1))
    rw [gaussianBoxPathPosition_zero] at h
    simpa using h
  · apply independentBlockDeviation_eq_zero_of_lt_start p l
    have hstrict := consecutiveBlocks_strictlyOrdered hconsecutive
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hlt
    · have hbC : b.start < c.start :=
        (Nat.le_add_right b.start b.steps).trans_lt (hstrict.1 c hc)
      exact hlt.trans hbC

/-- The full Gaussian product factors into the centered prefix and the
connected multiblock path weight. -/
theorem gaussianDeviationProduct_eq_prefix_mul_connected
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hn : 2 ≤ n) (hbstart : 2 ≤ b.start)
    (p : IndependentGaussianBlockPaths (b :: bs))
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = n) :
    gaussianDeviationProduct n (independentBlockDeviation p) =
      gaussianCenteredPrefixProduct b.start *
        connectedGaussianBlockWeight p := by
  rw [gaussianDeviationProduct_eq_segment hn]
  have hbn : b.start ≤ n := by
    rw [← hend]
    exact gaussianBlocksEnd_ge_start hconsecutive
  have hlength : n - 2 = (b.start - 2) + (n - b.start) := by omega
  rw [hlength, gaussianSegmentProduct_add]
  have hprefix : gaussianSegmentProduct 2 (b.start - 2)
        (independentBlockDeviation p) = gaussianCenteredPrefixProduct b.start := by
    unfold gaussianCenteredPrefixProduct
    apply gaussianSegmentProduct_congr
    intro l _hl hupper
    have : l ≤ b.start := by omega
    rw [independentBlockDeviation_eq_zero_of_le_first_start p hconsecutive this]
  rw [hprefix, connectedGaussianBlockWeight_eq_segment p hconsecutive]
  rw [show 2 + (b.start - 2) = b.start by omega]
  congr 2
  rw [hend]

/-- **Finite multiblock Gaussian constrained-sum lower bound (A.12).**

The left side consists only of the centered-prefix factor and the explicit
spectral/connector cost.  The right side is the exact Gaussian energy sum of
the injective multiblock family. -/
theorem prefix_mul_exp_neg_totalCost_le_sum_gaussianDeviationProduct
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hn : 2 ≤ n) (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hend : gaussianBlocksEnd (b :: bs) = n)
    (hstart : ∀ c ∈ b :: bs, 0 < c.start)
    (hscale : ∀ c ∈ b :: bs,
      (2560 : ℝ) * (c.start + c.steps : ℕ) ^ 2 ≤
        (c.radius : ℝ) ^ 2) :
    gaussianCenteredPrefixProduct b.start *
        Real.exp (-gaussianBlockTotalCost (b :: bs)) ≤
      ∑ p : IndependentGaussianBlockPaths (b :: bs),
        gaussianDeviationProduct n (independentBlockDeviation p) := by
  have hmass := exp_neg_gaussianBlockTotalCost_le_sum_connected
    (b :: bs) hstart hscale
  calc
    gaussianCenteredPrefixProduct b.start *
          Real.exp (-gaussianBlockTotalCost (b :: bs)) ≤
        gaussianCenteredPrefixProduct b.start *
          ∑ p : IndependentGaussianBlockPaths (b :: bs),
            connectedGaussianBlockWeight p :=
      mul_le_mul_of_nonneg_left hmass
        (gaussianCenteredPrefixProduct_nonneg b.start)
    _ = ∑ p : IndependentGaussianBlockPaths (b :: bs),
          gaussianDeviationProduct n (independentBlockDeviation p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [gaussianDeviationProduct_eq_prefix_mul_connected hn hbstart p
        hconsecutive hend]

/-! ## Reindexing the Gaussian family inside the global profile sum -/

/-- Integer deviation of a genuine profile, extended by the parabolic centre
outside its natural scale range. -/
def profileIntegerDeviation {n : ℕ} (m : Profile n) (l : ℕ) : ℤ :=
  (ProfileListExponent.profileAtScale m l : ℤ) - profileCenter l

lemma independentBlockDeviation_lower
    {bs : List GaussianBlock} (p : IndependentGaussianBlockPaths bs)
    (hcenter : ∀ b ∈ bs, ∀ l, BlockContains b l →
      b.radius ≤ profileCenter l) (l : ℕ) :
    -(profileCenter l : ℤ) ≤ independentBlockDeviation p l := by
  rcases independentBlockDeviation_eq_zero_or_mem p l with
    hz | ⟨b, hb, hbl, hmem⟩
  · rw [hz]
    omega
  · have hbox := (mem_gaussianBox.mp hmem).1
    have hc := hcenter b hb l hbl
    omega

lemma profileIntegerDeviation_embeddedMultiBlockProfile
    {n : ℕ} {bs : List GaussianBlock}
    (p : IndependentGaussianBlockPaths bs)
    (hcenter : ∀ b ∈ bs, ∀ l, BlockContains b l →
      b.radius ≤ profileCenter l)
    {l : ℕ} (hlower : 2 ≤ l) (hupper : l ≤ n) :
    profileIntegerDeviation (embeddedMultiBlockProfile n p) l =
      independentBlockDeviation p l := by
  unfold profileIntegerDeviation ProfileListExponent.profileAtScale
  rw [dif_pos ⟨hlower, hupper⟩]
  let i : Fin (n - 1) := ⟨l - 2, by omega⟩
  change (embeddedMultiBlockProfile n p i : ℤ) - profileCenter l = _
  have hscale : scaleIndex i = l := by
    unfold scaleIndex
    dsimp only [i]
    omega
  unfold embeddedMultiBlockProfile
  rw [hscale]
  exact centeredProfileValue_sub_center
    (independentBlockDeviation_lower p hcenter l)

lemma gaussianDeviationProduct_embeddedMultiBlockProfile
    {n : ℕ} {bs : List GaussianBlock} (hn : 2 ≤ n)
    (p : IndependentGaussianBlockPaths bs)
    (hcenter : ∀ b ∈ bs, ∀ l, BlockContains b l →
      b.radius ≤ profileCenter l) :
    gaussianDeviationProduct n
        (profileIntegerDeviation (embeddedMultiBlockProfile n p)) =
      gaussianDeviationProduct n (independentBlockDeviation p) := by
  unfold gaussianDeviationProduct
  apply Finset.prod_congr rfl
  intro l hl
  have hlb := Finset.mem_Ico.mp hl
  rw [profileIntegerDeviation_embeddedMultiBlockProfile p hcenter hlb.1
      (Nat.le_of_lt hlb.2),
    profileIntegerDeviation_embeddedMultiBlockProfile p hcenter
      (by omega) hlb.2]

/-- Gaussian-energy sum over all exact constrained profiles. -/
def constrainedGaussianDeviationWeight (n : ℕ) (delta : ℝ) : ℝ :=
  ∑ m ∈ constrainedProfiles n delta,
    gaussianDeviationProduct n (profileIntegerDeviation m)

lemma constrainedGaussianDeviationWeight_nonneg (n : ℕ) (delta : ℝ) :
    0 ≤ constrainedGaussianDeviationWeight n delta := by
  unfold constrainedGaussianDeviationWeight
  exact Finset.sum_nonneg fun m _ ↦ by
    unfold gaussianDeviationProduct
    exact Finset.prod_nonneg fun l _ ↦ gaussianStepWeight_nonneg _ _

/-- The multiblock path family embeds injectively in the global constrained
Gaussian profile sum. -/
theorem sum_gaussianDeviationProduct_le_constrainedGaussianDeviationWeight
    (n : ℕ) {bs : List GaussianBlock} (hn : 2 ≤ n)
    {delta : ℝ}
    (hordered : StrictlyOrderedBlocks bs)
    (hstart : ∀ b ∈ bs, 2 ≤ b.start)
    (hend : ∀ b ∈ bs, b.start + b.steps ≤ n)
    (hcenter : ∀ b ∈ bs, ∀ l, BlockContains b l →
      b.radius ≤ profileCenter l)
    (hwidth : ∀ b ∈ bs, ∀ l, BlockContains b l →
      (b.radius : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    (∑ p : IndependentGaussianBlockPaths bs,
        gaussianDeviationProduct n (independentBlockDeviation p)) ≤
      constrainedGaussianDeviationWeight n delta := by
  let e : IndependentGaussianBlockPaths bs → Profile n :=
    embeddedMultiBlockProfile n
  have he : Function.Injective e :=
    embeddedMultiBlockProfile_injective n hordered hstart hend
      (fun b hb ↦ hcenter b hb b.start ⟨le_rfl, by omega⟩)
  have himage : Finset.image e Finset.univ ⊆ constrainedProfiles n delta := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨p, _hp, rfl⟩ := hm
    exact embeddedMultiBlockProfile_mem_constrainedProfiles n p hcenter hwidth
  calc
    (∑ p : IndependentGaussianBlockPaths bs,
        gaussianDeviationProduct n (independentBlockDeviation p)) =
      ∑ p : IndependentGaussianBlockPaths bs,
        gaussianDeviationProduct n (profileIntegerDeviation (e p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      symm
      exact gaussianDeviationProduct_embeddedMultiBlockProfile hn p hcenter
    _ = ∑ m ∈ Finset.image e Finset.univ,
        gaussianDeviationProduct n (profileIntegerDeviation m) := by
      symm
      exact Finset.sum_image he.injOn
    _ ≤ ∑ m ∈ constrainedProfiles n delta,
        gaussianDeviationProduct n (profileIntegerDeviation m) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun m _ _ ↦ by
          unfold gaussianDeviationProduct
          exact Finset.prod_nonneg fun l _ ↦ gaussianStepWeight_nonneg _ _)
    _ = constrainedGaussianDeviationWeight n delta := rfl

/-- Profile-level finite A.12: the explicit multiblock exponent lower-bounds
the complete constrained Gaussian-energy sum. -/
theorem prefix_mul_exp_neg_totalCost_le_constrainedGaussianDeviationWeight
    {n : ℕ} {b : GaussianBlock} {bs : List GaussianBlock}
    (hn : 2 ≤ n) (hbstart : 2 ≤ b.start)
    (hconsecutive : ConsecutiveBlocks (b :: bs))
    (hendLast : gaussianBlocksEnd (b :: bs) = n)
    (hstart : ∀ c ∈ b :: bs, 0 < c.start)
    (hscale : ∀ c ∈ b :: bs,
      (2560 : ℝ) * (c.start + c.steps : ℕ) ^ 2 ≤
        (c.radius : ℝ) ^ 2)
    {delta : ℝ}
    (hcenter : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      c.radius ≤ profileCenter l)
    (hwidth : ∀ c ∈ b :: bs, ∀ l, BlockContains c l →
      (c.radius : ℝ) ≤ (l : ℝ) ^ (1 + delta)) :
    gaussianCenteredPrefixProduct b.start *
        Real.exp (-gaussianBlockTotalCost (b :: bs)) ≤
      constrainedGaussianDeviationWeight n delta := by
  apply (prefix_mul_exp_neg_totalCost_le_sum_gaussianDeviationProduct
    hn hbstart hconsecutive hendLast hstart hscale).trans
  apply sum_gaussianDeviationProduct_le_constrainedGaussianDeviationWeight
    n hn (consecutiveBlocks_strictlyOrdered hconsecutive)
  · intro c hc
    exact hbstart.trans (by
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_rfl
      · have hlt := (consecutiveBlocks_strictlyOrdered hconsecutive).1 c hc
        omega)
  · intro c hc
    rw [← hendLast]
    exact gaussianBlockEnd_le_blocksEnd_of_mem hconsecutive hc
  · exact hcenter
  · exact hwidth

end

end Erdos1165.GaussianMultiBlockProfile
