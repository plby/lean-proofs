import ErdosProblems.Erdos260.Interior

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Long-exterior contribution

This module corresponds to Section 7 of the manuscript.
-/

noncomputable section

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators ENNReal List

namespace Erdos260

/-- Exact distance from a real number to `[0,1]`. -/
def distanceToUnitInterval (μ : ℝ) : ℝ :=
  if μ < 0 then -μ else if 1 < μ then μ - 1 else 0

-- The generated finite-enumeration proof needs full transparency in Lean 4.33.
set_option backward.isDefEq.respectTransparency false in
/-- The four first-exit tags. -/
inductive ExitTag
  | initialExterior
  | direct
  | boundaryZero
  | boundaryOne
  deriving DecidableEq, Repr, Fintype

/-- Deterministic first-exit record from Appendix B. -/
@[ext] structure FirstExitRecord where
  interiorGaps : ℕ
  tag : ExitTag
  boundaryOnes : ℕ
  exitGap : ℕ
  deriving DecidableEq, Repr

namespace FirstExitRecord

def initialExterior : FirstExitRecord := ⟨0, .initialExterior, 0, 0⟩

/-- Region immediately before the first exterior state, encoded with the four
tags used in Appendix B.  The exterior case is unreachable for a certified
first exit and is mapped to `direct` so that this helper remains total. -/
def tagOfPreExitRegion : SlopeRegion → ExitTag
  | .interior => .direct
  | .boundaryZero => .boundaryZero
  | .boundaryOne => .boundaryOne
  | .exterior => .direct

/-- The deterministic record extracted from a concrete initial trajectory.
`before` is the exact word from the post-prefix occurrence line up to the
first exterior state. -/
def ofFirstExit (Q : ℕ) (base : AffineLine) (before : GapWord) :
    FirstExitRecord :=
  if _h : before = [] then initialExterior else
    { interiorGaps :=
        ((List.range before.length).filter fun r =>
          classifySlope
            ((base.transformWord Q (before.take r)).slope Q) = .interior).length
      tag := tagOfPreExitRegion
        (classifySlope
          ((base.transformWord Q before.dropLast).slope Q))
      boundaryOnes :=
        ((List.range before.length).filter fun r =>
          classifySlope
            ((base.transformWord Q (before.take r)).slope Q) =
              .boundaryOne).length
      exitGap := before.getLastD 0 }

@[simp] theorem ofFirstExit_nil (Q : ℕ) (base : AffineLine) :
    ofFirstExit Q base [] = initialExterior := by
  simp [ofFirstExit]

def Valid (m L Cgap : ℕ) (record : FirstExitRecord) : Prop :=
  record.interiorGaps ≤ m ∧ record.boundaryOnes ≤ m ∧
    (record.tag = .initialExterior → record = initialExterior) ∧
    (record.tag ≠ .initialExterior →
      1 ≤ record.exitGap ∧ record.exitGap ≤ L + Cgap + 1) ∧
    (record.tag = .boundaryOne → 2 ≤ record.exitGap)

/-- A record describes the actual first exterior state of the anchored suffix.
The pre-exit word and all line states are tied to the same occurrence and the
record is definitionally the deterministic value returned by `ofFirstExit`. -/
def DescribesFirstExit (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold)
    (record : FirstExitRecord) (line : AffineLine)
    (continuation : GapWord) : Prop :=
  ∃ base finish : AffineLine, ∃ before after : GapWord,
    IsOccurrenceLine W Z0 (initialLongPrefix W e.1) base ∧
      actualPostPrefixGaps W e.1 = before ++ continuation ++ after ∧
      SharedGapTrajectory W.rational.eta.den base before line ∧
      SharedGapTrajectory W.rational.eta.den line continuation finish ∧
      classifySlope (line.slope W.rational.eta.den) = .exterior ∧
      (∀ r < before.length, ∃ state : AffineLine,
        SharedGapTrajectory W.rational.eta.den base (before.take r) state ∧
          classifySlope (state.slope W.rational.eta.den) ≠ .exterior) ∧
      record = ofFirstExit W.rational.eta.den base before

end FirstExitRecord

/-- Enlarged admissible carry corridor at one scale. -/
def InAdmissibleCarryRegion (Q X : ℕ) (x r : ℤ) : Prop :=
  -(X : ℤ) ≤ x ∧ x ≤ 3 * X ∧ 0 ≤ r ∧ r ≤ (Q : ℤ) * (x + 2)

/-- Original integer parameters whose points are admissible before and after a
fixed shared continuation.  No primitive reparameterization is performed. -/
def admissibleOriginalParameters (Q X : ℕ) (line : AffineLine)
    (word : GapWord) : Set ℤ :=
  {t |
    InAdmissibleCarryRegion Q X
      (line.A + line.H * t) (line.C + line.K * t) ∧
    let finish := line.transformWord Q word
    InAdmissibleCarryRegion Q X
      (finish.A + finish.H * t) (finish.C + finish.K * t)}

/-- Exterior-prefix exponent `δ_ext`. -/
def exteriorPrefixExponent (p : EntropyParams) : ℝ :=
  (p.structural.Gamma + 1) *
    binaryEntropy (p.kappa / (p.structural.Gamma + 1))

/-- Paper label: `lem:off-amplify` (Section 7). -/
theorem lem_off_amplify (μ : ℝ) (g : ℕ) (hg : 1 ≤ g)
    (hμ : μ ∉ Set.Icc (0 : ℝ) 1) :
    (2 : ℝ) ^ g * distanceToUnitInterval μ ≤
      distanceToUnitInterval ((2 : ℝ) ^ g * μ - 1) := by
  have hpow0 : 0 < (2 : ℝ) ^ g := pow_pos (by norm_num) _
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ g := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hg)
  by_cases hneg : μ < 0
  · have hnext : (2 : ℝ) ^ g * μ - 1 < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hpow0 hneg]
    rw [distanceToUnitInterval, if_pos hneg]
    rw [distanceToUnitInterval, if_pos hnext]
    linarith
  · have hnonneg : 0 ≤ μ := le_of_not_gt hneg
    have hgt : 1 < μ := by
      by_contra hnot
      exact hμ ⟨hnonneg, le_of_not_gt hnot⟩
    have hnext : 1 < (2 : ℝ) ^ g * μ - 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hpow2 hnonneg]
    rw [distanceToUnitInterval, if_neg hneg, if_pos hgt]
    rw [distanceToUnitInterval, if_neg (not_lt_of_ge (le_trans (by norm_num) hnext.le)),
      if_pos hnext]
    nlinarith

theorem classifySlope_exterior_not_mem (μ : ℚ)
    (h : classifySlope μ = .exterior) :
    (μ : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
  intro hmem
  have hmemQ : μ ∈ Set.Icc (0 : ℚ) 1 := by
    exact ⟨by exact_mod_cast hmem.1, by exact_mod_cast hmem.2⟩
  rcases hmemQ with ⟨hμ0, hμ1⟩
  unfold classifySlope at h
  by_cases h0 : μ = 0
  · simp [h0] at h
  by_cases h1 : μ = 1
  · simp [h1] at h
  have hinterior : 0 < μ ∧ μ < 1 :=
    ⟨lt_of_le_of_ne hμ0 (Ne.symm h0), lt_of_le_of_ne hμ1 h1⟩
  simp [h0, h1, hinterior] at h

/-- For a fixed transition word, changing the raw occurrence-line
parameterization without changing its normalized slope leaves the deterministic
first-exit record unchanged. -/
theorem FirstExitRecord.ofFirstExit_eq_of_slope_eq (Q : ℕ) (hQ : 0 < Q)
    (left right : AffineLine) (before : GapWord)
    (hslope : left.slope Q = right.slope Q) :
    FirstExitRecord.ofFirstExit Q left before =
      FirstExitRecord.ofFirstExit Q right before := by
  by_cases hnil : before = []
  · subst before
    simp [FirstExitRecord.ofFirstExit]
  · rw [FirstExitRecord.ofFirstExit, dif_neg hnil,
      FirstExitRecord.ofFirstExit, dif_neg hnil]
    have hstate (r : ℕ) :
        classifySlope ((left.transformWord Q (before.take r)).slope Q) =
          classifySlope ((right.transformWord Q (before.take r)).slope Q) :=
      congrArg classifySlope
        (AffineLine.transformWord_slope_eq_of_slope_eq Q hQ left right
          (before.take r) hslope)
    have hlast :
        classifySlope ((left.transformWord Q before.dropLast).slope Q) =
          classifySlope ((right.transformWord Q before.dropLast).slope Q) :=
      congrArg classifySlope
        (AffineLine.transformWord_slope_eq_of_slope_eq Q hQ left right
          before.dropLast hslope)
    simp_rw [hstate]
    rw [hlast]

/-- A shared-gap trajectory has no hidden choice: its terminal line is the
iterated affine transform of its initial line. -/
theorem sharedGapTrajectory_iff_eq_transformWord (Q : ℕ)
    (line finish : AffineLine) (word : GapWord) :
    SharedGapTrajectory Q line word finish ↔
      finish = line.transformWord Q word := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons line next finish g gs hnext htail ih =>
        subst next
        simpa only [AffineLine.transformWord] using ih
  · intro h
    subst finish
    induction word generalizing line with
    | nil => exact SharedGapTrajectory.nil line
    | cons g gs ih =>
        exact SharedGapTrajectory.cons line (line.transform Q g)
          ((line.transform Q g).transformWord Q gs) g gs rfl
          (ih (line.transform Q g))

/-! ### Deterministic reconstruction of the first-exit word

The polynomial first-exit record is useful in the exterior fibre count only
because, once the initial occurrence line is fixed, it reconstructs the
whole transition word.  The next lemmas make that assertion explicit rather
than treating it as an informal property of the record. -/

private def preExitRegionCount (Q : ℕ) (base : AffineLine)
    (word : GapWord) (region : SlopeRegion) : ℕ :=
  (List.range word.length).countP fun r =>
    classifySlope ((base.transformWord Q (word.take r)).slope Q) = region

private theorem countP_congr_of_mem {α : Type*} (l : List α)
    (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.countP_cons, List.countP_cons, h a (by simp)]
      exact congrArg (fun n => n + if q a = true then 1 else 0)
        (ih fun x hx => h x (by simp [hx]))

@[simp] private theorem preExitRegionCount_cons (Q g : ℕ)
    (base : AffineLine) (word : GapWord) (region : SlopeRegion) :
    preExitRegionCount Q base (g :: word) region =
      (if classifySlope (base.slope Q) = region then 1 else 0) +
        preExitRegionCount Q (base.transform Q g) word region := by
  unfold preExitRegionCount
  rw [List.length_cons, List.range_succ_eq_map, List.countP_cons,
    List.countP_map]
  have htail := countP_congr_of_mem (List.range word.length)
    ((fun r => decide
      (classifySlope
        ((base.transformWord Q ((g :: word).take r)).slope Q) = region)) ∘
      Nat.succ)
    (fun r => decide
      (classifySlope
        (((base.transform Q g).transformWord Q (word.take r)).slope Q) =
          region))
    (by
      intro r hr
      simp only [Function.comp_apply, List.take_succ_cons,
        AffineLine.transformWord])
  rw [htail]
  simp only [List.take_zero, AffineLine.transformWord, decide_eq_true_eq]
  omega

private def IsFirstExitWord (Q : ℕ) (base : AffineLine)
    (word : GapWord) : Prop :=
  word.Positive ∧
    (∀ r < word.length,
      classifySlope ((base.transformWord Q (word.take r)).slope Q) ≠
        .exterior) ∧
    classifySlope ((base.transformWord Q word).slope Q) = .exterior

private theorem classifySlope_interior_iff (μ : ℚ) :
    classifySlope μ = .interior ↔ 0 < μ ∧ μ < 1 := by
  unfold classifySlope
  by_cases h0 : μ = 0
  · simp [h0]
  by_cases h1 : μ = 1
  · simp [h1]
  simp [h0, h1]

private theorem classifySlope_boundaryZero_iff (μ : ℚ) :
    classifySlope μ = .boundaryZero ↔ μ = 0 := by
  constructor
  · intro h
    by_contra h0
    unfold classifySlope at h
    rw [if_neg h0] at h
    by_cases h1 : μ = 1
    · rw [if_pos h1] at h
      contradiction
    · rw [if_neg h1] at h
      by_cases hi : 0 < μ ∧ μ < 1
      · rw [if_pos hi] at h
        contradiction
      · rw [if_neg hi] at h
        contradiction
  · rintro rfl
    simp [classifySlope]

private theorem classifySlope_boundaryOne_iff (μ : ℚ) :
    classifySlope μ = .boundaryOne ↔ μ = 1 := by
  constructor
  · intro h
    by_contra h1
    unfold classifySlope at h
    by_cases h0 : μ = 0
    · simp [h0] at h
    simp only [h0, h1, if_false] at h
    split at h <;> contradiction
  · rintro rfl
    simp [classifySlope]

private theorem classifySlope_ne_exterior_iff (μ : ℚ) :
    classifySlope μ ≠ .exterior ↔ 0 ≤ μ ∧ μ ≤ 1 := by
  constructor
  · intro h
    cases hregion : classifySlope μ with
    | interior =>
        have hi := (classifySlope_interior_iff μ).mp hregion
        exact ⟨hi.1.le, hi.2.le⟩
    | boundaryZero =>
        rw [(classifySlope_boundaryZero_iff μ).mp hregion]
        norm_num
    | boundaryOne =>
        rw [(classifySlope_boundaryOne_iff μ).mp hregion]
        norm_num
    | exterior => exact (h hregion).elim
  · rintro ⟨h0, h1⟩ hext
    apply classifySlope_exterior_not_mem μ hext
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

private theorem IsFirstExitWord.tail {Q g : ℕ} {base : AffineLine}
    {word : GapWord} (h : IsFirstExitWord Q base (g :: word)) :
    IsFirstExitWord Q (base.transform Q g) word := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact h.1 x (by simp [hx])
  · intro r hr
    have hproper := h.2.1 (r + 1) (by simp; omega)
    simpa only [List.take_succ_cons, AffineLine.transformWord] using hproper
  · simpa only [AffineLine.transformWord] using h.2.2

private theorem IsFirstExitWord.base_nonexterior {Q : ℕ}
    {base : AffineLine} {word : GapWord} (hword : word ≠ [])
    (h : IsFirstExitWord Q base word) :
    classifySlope (base.slope Q) ≠ .exterior := by
  have hlen : 0 < word.length := List.length_pos_iff.mpr hword
  simpa only [List.take_zero, AffineLine.transformWord] using h.2.1 0 hlen

private theorem IsFirstExitWord.head_positive {Q g : ℕ}
    {base : AffineLine} {word : GapWord}
    (h : IsFirstExitWord Q base (g :: word)) : 1 ≤ g := by
  exact h.1 g (by simp)

private theorem transform_boundaryZero_exterior (Q g : ℕ) (hQ : 0 < Q)
    (base : AffineLine)
    (hbase : classifySlope (base.slope Q) = .boundaryZero) :
    classifySlope ((base.transform Q g).slope Q) = .exterior := by
  have hslope : base.slope Q = 0 :=
    (classifySlope_boundaryZero_iff _).mp hbase
  rw [AffineLine.slope_transform Q hQ, hslope]
  norm_num [classifySlope]

private theorem transform_boundaryOne_of_nonexterior (Q g : ℕ)
    (hQ : 0 < Q) (base : AffineLine) (hg : 1 ≤ g)
    (hbase : classifySlope (base.slope Q) = .boundaryOne)
    (hnext : classifySlope ((base.transform Q g).slope Q) ≠ .exterior) :
    g = 1 ∧
      classifySlope ((base.transform Q g).slope Q) = .boundaryOne := by
  have hslope : base.slope Q = 1 :=
    (classifySlope_boundaryOne_iff _).mp hbase
  have hbounds := (classifySlope_ne_exterior_iff _).mp hnext
  have hformula := AffineLine.slope_transform Q hQ base g
  have hg_one : g = 1 := by
    by_contra hne
    have hg_two : 2 ≤ g := by omega
    have hpow : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ g :=
      pow_le_pow_right₀ (by norm_num) hg_two
    rw [hslope] at hformula
    norm_num at hformula
    nlinarith
  subst g
  refine ⟨rfl, ?_⟩
  rw [AffineLine.slope_transform Q hQ, hslope]
  norm_num [classifySlope]

private theorem firstExit_boundaryZero_singleton (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (word : GapWord)
    (hbase : classifySlope (base.slope Q) = .boundaryZero)
    (hword : IsFirstExitWord Q base word) :
    ∃ g : ℕ, word = [g] := by
  cases word with
  | nil =>
      have := hword.2.2
      simp only [AffineLine.transformWord] at this
      rw [hbase] at this
      contradiction
  | cons g gs =>
      refine ⟨g, ?_⟩
      by_contra hne
      have hgs : gs ≠ [] := by
        intro hnil
        subst gs
        exact hne rfl
      have hproper :
          classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
        have hlt : 1 < (g :: gs).length := by
          simp only [List.length_cons]
          exact Nat.succ_lt_succ (List.length_pos_iff.mpr hgs)
        simpa only [List.take_succ_cons, List.take_zero,
          AffineLine.transformWord] using hword.2.1 1 hlt
      exact hproper (transform_boundaryZero_exterior Q g hQ base hbase)

private theorem firstExit_boundaryOne_all_states (Q : ℕ) (hQ : 0 < Q) :
    ∀ (base : AffineLine) (word : GapWord),
      classifySlope (base.slope Q) = .boundaryOne →
      IsFirstExitWord Q base word →
      ∀ r < word.length,
        classifySlope ((base.transformWord Q (word.take r)).slope Q) =
          .boundaryOne := by
  intro base word
  induction word generalizing base with
  | nil => simp
  | cons g gs ih =>
      intro hbase hword r hr
      cases r with
      | zero => simpa only [List.take_zero, AffineLine.transformWord] using hbase
      | succ r =>
          have hrTail : r < gs.length := by simpa using hr
          have hgs : gs ≠ [] := List.ne_nil_of_length_pos (lt_of_le_of_lt
            (Nat.zero_le r) hrTail)
          have hnextNonexterior :
              classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
            have hlt : 1 < (g :: gs).length := by
              simp only [List.length_cons]
              exact Nat.succ_lt_succ (List.length_pos_iff.mpr hgs)
            simpa only [List.take_succ_cons, List.take_zero,
              AffineLine.transformWord] using hword.2.1 1 hlt
          have hnext := transform_boundaryOne_of_nonexterior Q g hQ base
            hword.head_positive hbase hnextNonexterior
          simpa only [List.take_succ_cons, AffineLine.transformWord] using
            ih (base.transform Q g) hnext.2 hword.tail r hrTail

private theorem firstExit_boundaryOne_head_eq_one (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (g : ℕ) (tail : GapWord)
    (htail : tail ≠ [])
    (hbase : classifySlope (base.slope Q) = .boundaryOne)
    (hword : IsFirstExitWord Q base (g :: tail)) : g = 1 := by
  have hnextNonexterior :
      classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
    have hlt : 1 < (g :: tail).length := by
      simp only [List.length_cons]
      exact Nat.succ_lt_succ (List.length_pos_iff.mpr htail)
    simpa only [List.take_succ_cons, List.take_zero,
      AffineLine.transformWord] using hword.2.1 1 hlt
  exact (transform_boundaryOne_of_nonexterior Q g hQ base
    hword.head_positive hbase hnextNonexterior).1

private theorem preExitRegionCount_interior_eq_zero_of_boundary
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine) (word : GapWord)
    (hbase : classifySlope (base.slope Q) = .boundaryZero ∨
      classifySlope (base.slope Q) = .boundaryOne)
    (hword : IsFirstExitWord Q base word) :
    preExitRegionCount Q base word .interior = 0 := by
  have hall : ∀ r < word.length,
      classifySlope ((base.transformWord Q (word.take r)).slope Q) ≠
        .interior := by
    rcases hbase with hzero | hone
    · obtain ⟨g, rfl⟩ :=
        firstExit_boundaryZero_singleton Q hQ base word hzero hword
      intro r hr
      have hr0 : r = 0 := by simp at hr; omega
      subst r
      simp only [List.take_zero, AffineLine.transformWord]
      rw [hzero]
      decide
    · intro r hr
      rw [firstExit_boundaryOne_all_states Q hQ base word hone hword r hr]
      decide
  rw [preExitRegionCount, List.countP_eq_zero]
  intro r hr
  have hrlt : r < word.length := List.mem_range.mp hr
  simp only [decide_eq_true_eq]
  exact hall r hrlt

private theorem firstExit_boundary_tag (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (word : GapWord) (hwordNonempty : word ≠ [])
    (hword : IsFirstExitWord Q base word) :
    (classifySlope (base.slope Q) = .boundaryZero →
        (FirstExitRecord.ofFirstExit Q base word).tag = .boundaryZero) ∧
      (classifySlope (base.slope Q) = .boundaryOne →
        (FirstExitRecord.ofFirstExit Q base word).tag = .boundaryOne) := by
  constructor
  · intro hzero
    obtain ⟨g, rfl⟩ :=
      firstExit_boundaryZero_singleton Q hQ base word hzero hword
    rw [FirstExitRecord.ofFirstExit, dif_neg (by simp)]
    change FirstExitRecord.tagOfPreExitRegion
      (classifySlope ((base.transformWord Q [g].dropLast).slope Q)) =
        .boundaryZero
    simp only [List.dropLast, AffineLine.transformWord]
    rw [hzero]
    rfl
  · intro hone
    have hlastIndex : word.length - 1 < word.length := by
      exact Nat.sub_lt (List.length_pos_iff.mpr hwordNonempty) (by omega)
    have hlast := firstExit_boundaryOne_all_states Q hQ base word hone hword
      (word.length - 1) hlastIndex
    have hdrop : classifySlope
        ((base.transformWord Q word.dropLast).slope Q) = .boundaryOne := by
      simpa only [List.dropLast_eq_take] using hlast
    simp [FirstExitRecord.ofFirstExit, hwordNonempty,
      FirstExitRecord.tagOfPreExitRegion, hdrop]

private theorem FirstExitRecord.ofFirstExit_interiorGaps (Q : ℕ)
    (base : AffineLine) (word : GapWord) (hword : word ≠ []) :
    (FirstExitRecord.ofFirstExit Q base word).interiorGaps =
      preExitRegionCount Q base word .interior := by
  rw [FirstExitRecord.ofFirstExit, dif_neg hword]
  change (List.filter _ (List.range word.length)).length = _
  rw [← List.countP_eq_length_filter]
  rfl

private theorem FirstExitRecord.ofFirstExit_boundaryOnes (Q : ℕ)
    (base : AffineLine) (word : GapWord) (hword : word ≠ []) :
    (FirstExitRecord.ofFirstExit Q base word).boundaryOnes =
      preExitRegionCount Q base word .boundaryOne := by
  rw [FirstExitRecord.ofFirstExit, dif_neg hword]
  change (List.filter _ (List.range word.length)).length = _
  rw [← List.countP_eq_length_filter]
  rfl

private theorem FirstExitRecord.ofFirstExit_tag_cons (Q g : ℕ)
    (base : AffineLine) (tail : GapWord) (htail : tail ≠ []) :
    (FirstExitRecord.ofFirstExit Q base (g :: tail)).tag =
      (FirstExitRecord.ofFirstExit Q (base.transform Q g) tail).tag := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons x xs =>
      simp [FirstExitRecord.ofFirstExit, AffineLine.transformWord]

private theorem FirstExitRecord.ofFirstExit_exitGap_cons (Q g : ℕ)
    (base : AffineLine) (tail : GapWord) (htail : tail ≠ []) :
    (FirstExitRecord.ofFirstExit Q base (g :: tail)).exitGap =
      (FirstExitRecord.ofFirstExit Q (base.transform Q g) tail).exitGap := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons x xs => simp [FirstExitRecord.ofFirstExit]

private theorem FirstExitRecord.tail_eq_of_cons_record_eq (Q g : ℕ)
    (base : AffineLine) (left right : GapWord)
    (hleft : left ≠ []) (hright : right ≠ [])
    (hrecord : FirstExitRecord.ofFirstExit Q base (g :: left) =
      FirstExitRecord.ofFirstExit Q base (g :: right)) :
    FirstExitRecord.ofFirstExit Q (base.transform Q g) left =
      FirstExitRecord.ofFirstExit Q (base.transform Q g) right := by
  apply FirstExitRecord.ext
  · have hfield := congrArg FirstExitRecord.interiorGaps hrecord
    rw [FirstExitRecord.ofFirstExit_interiorGaps Q base _ (by simp),
      FirstExitRecord.ofFirstExit_interiorGaps Q base _ (by simp),
      preExitRegionCount_cons, preExitRegionCount_cons] at hfield
    rw [FirstExitRecord.ofFirstExit_interiorGaps Q (base.transform Q g) left
      hleft, FirstExitRecord.ofFirstExit_interiorGaps Q (base.transform Q g)
      right hright]
    omega
  · simpa only [FirstExitRecord.ofFirstExit_tag_cons Q g base left hleft,
      FirstExitRecord.ofFirstExit_tag_cons Q g base right hright] using
      congrArg FirstExitRecord.tag hrecord
  · have hfield := congrArg FirstExitRecord.boundaryOnes hrecord
    rw [FirstExitRecord.ofFirstExit_boundaryOnes Q base _ (by simp),
      FirstExitRecord.ofFirstExit_boundaryOnes Q base _ (by simp),
      preExitRegionCount_cons, preExitRegionCount_cons] at hfield
    rw [FirstExitRecord.ofFirstExit_boundaryOnes Q (base.transform Q g) left
      hleft, FirstExitRecord.ofFirstExit_boundaryOnes Q (base.transform Q g)
      right hright]
    omega
  · simpa only [FirstExitRecord.ofFirstExit_exitGap_cons Q g base left hleft,
      FirstExitRecord.ofFirstExit_exitGap_cons Q g base right hright] using
      congrArg FirstExitRecord.exitGap hrecord

private theorem positive_gap_eq_of_same_nonexterior_region
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine) (g h : ℕ)
    (hg : 1 ≤ g) (hh : 1 ≤ h)
    (hbase : classifySlope (base.slope Q) = .interior)
    (region : SlopeRegion) (hregion : region ≠ .exterior)
    (hgRegion : classifySlope ((base.transform Q g).slope Q) = region)
    (hhRegion : classifySlope ((base.transform Q h).slope Q) = region) :
    g = h := by
  have hbaseIrat := (classifySlope_interior_iff _).mp hbase
  have hbaseIreal : (base.slope Q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast hbaseIrat.1, by exact_mod_cast hbaseIrat.2⟩
  cases region with
  | interior =>
      apply lem_strict_unique (base.slope Q : ℝ) hbaseIreal
      · refine ⟨hg, ?_⟩
        have hnextRat := (classifySlope_interior_iff _).mp hgRegion
        have hnextReal :
            (((base.transform Q g).slope Q : ℚ) : ℝ) ∈ Set.Ioo 0 1 := by
          exact ⟨by exact_mod_cast hnextRat.1,
            by exact_mod_cast hnextRat.2⟩
        simpa only [AffineLine.transform_slope_real Q g hQ base] using hnextReal
      · refine ⟨hh, ?_⟩
        have hnextRat := (classifySlope_interior_iff _).mp hhRegion
        have hnextReal :
            (((base.transform Q h).slope Q : ℚ) : ℝ) ∈ Set.Ioo 0 1 := by
          exact ⟨by exact_mod_cast hnextRat.1,
            by exact_mod_cast hnextRat.2⟩
        simpa only [AffineLine.transform_slope_real Q h hQ base] using hnextReal
  | boundaryZero =>
      have hgSlope : (base.transform Q g).slope Q = 0 :=
        (classifySlope_boundaryZero_iff _).mp hgRegion
      have hhSlope : (base.transform Q h).slope Q = 0 :=
        (classifySlope_boundaryZero_iff _).mp hhRegion
      have hgFormula := AffineLine.slope_transform Q hQ base g
      have hhFormula := AffineLine.slope_transform Q hQ base h
      have hpows : (2 : ℚ) ^ g = (2 : ℚ) ^ h := by
        nlinarith [hbaseIrat.1]
      have hpowsNat : (2 : ℕ) ^ g = 2 ^ h := by exact_mod_cast hpows
      exact Nat.pow_right_injective (by norm_num) hpowsNat
  | boundaryOne =>
      have hgSlope : (base.transform Q g).slope Q = 1 :=
        (classifySlope_boundaryOne_iff _).mp hgRegion
      have hhSlope : (base.transform Q h).slope Q = 1 :=
        (classifySlope_boundaryOne_iff _).mp hhRegion
      have hgFormula := AffineLine.slope_transform Q hQ base g
      have hhFormula := AffineLine.slope_transform Q hQ base h
      have hpows : (2 : ℚ) ^ g = (2 : ℚ) ^ h := by
        nlinarith [hbaseIrat.1]
      have hpowsNat : (2 : ℕ) ^ g = 2 ^ h := by exact_mod_cast hpows
      exact Nat.pow_right_injective (by norm_num) hpowsNat
  | exterior => exact (hregion rfl).elim

private theorem preExitRegionCount_pos_of_base_region (Q : ℕ)
    (base : AffineLine) (word : GapWord) (region : SlopeRegion)
    (hword : word ≠ []) (hbase : classifySlope (base.slope Q) = region) :
    0 < preExitRegionCount Q base word region := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons g tail =>
      rw [preExitRegionCount_cons, hbase]
      simp

private theorem FirstExitRecord.ofFirstExit_tag_singleton (Q g : ℕ)
    (base : AffineLine) :
    (FirstExitRecord.ofFirstExit Q base [g]).tag =
      FirstExitRecord.tagOfPreExitRegion (classifySlope (base.slope Q)) := by
  rw [FirstExitRecord.ofFirstExit, dif_neg (by simp)]
  rfl

private theorem IsFirstExitWord.next_nonexterior {Q g : ℕ}
    {base : AffineLine} {tail : GapWord} (htail : tail ≠ [])
    (hword : IsFirstExitWord Q base (g :: tail)) :
    classifySlope ((base.transform Q g).slope Q) ≠ .exterior := by
  have hlt : 1 < (g :: tail).length := by
    simp only [List.length_cons]
    exact Nat.succ_lt_succ (List.length_pos_iff.mpr htail)
  simpa only [List.take_succ_cons, List.take_zero,
    AffineLine.transformWord] using hword.2.1 1 hlt

private theorem singleton_record_ne_long_firstExit (Q : ℕ) (hQ : 0 < Q)
    (base : AffineLine) (g h : ℕ) (tail : GapWord) (htail : tail ≠ [])
    (hsingle : IsFirstExitWord Q base [g])
    (hlong : IsFirstExitWord Q base (h :: tail)) :
    FirstExitRecord.ofFirstExit Q base [g] ≠
      FirstExitRecord.ofFirstExit Q base (h :: tail) := by
  intro hrecord
  have hbaseNon := hsingle.base_nonexterior (by simp)
  cases hbaseRegion : classifySlope (base.slope Q) with
  | exterior => exact hbaseNon hbaseRegion
  | boundaryZero =>
      obtain ⟨x, hshape⟩ := firstExit_boundaryZero_singleton Q hQ base
        (h :: tail) hbaseRegion hlong
      have : tail = [] := by simpa using congrArg List.tail hshape
      exact htail this
  | boundaryOne =>
      have hnext := transform_boundaryOne_of_nonexterior Q h hQ base
        hlong.head_positive hbaseRegion (hlong.next_nonexterior htail)
      have hleftCount :
          (FirstExitRecord.ofFirstExit Q base [g]).boundaryOnes = 1 := by
        rw [FirstExitRecord.ofFirstExit_boundaryOnes Q base [g] (by simp),
          preExitRegionCount_cons, hbaseRegion]
        simp [preExitRegionCount]
      have htailPositive : 0 < preExitRegionCount Q (base.transform Q h)
          tail .boundaryOne :=
        preExitRegionCount_pos_of_base_region Q (base.transform Q h) tail
          .boundaryOne htail hnext.2
      have hrightCount : 2 ≤
          (FirstExitRecord.ofFirstExit Q base (h :: tail)).boundaryOnes := by
        rw [FirstExitRecord.ofFirstExit_boundaryOnes Q base (h :: tail)
          (by simp), preExitRegionCount_cons, hbaseRegion]
        simpa [Nat.add_comm] using Nat.succ_le_succ htailPositive
      have hfield := congrArg FirstExitRecord.boundaryOnes hrecord
      omega
  | interior =>
      have hnextNon := hlong.next_nonexterior htail
      cases hnextRegion : classifySlope ((base.transform Q h).slope Q) with
      | exterior => exact hnextNon hnextRegion
      | interior =>
          have hleftCount :
              (FirstExitRecord.ofFirstExit Q base [g]).interiorGaps = 1 := by
            rw [FirstExitRecord.ofFirstExit_interiorGaps Q base [g] (by simp),
              preExitRegionCount_cons, hbaseRegion]
            simp [preExitRegionCount]
          have htailPositive : 0 < preExitRegionCount Q (base.transform Q h)
              tail .interior :=
            preExitRegionCount_pos_of_base_region Q (base.transform Q h) tail
              .interior htail hnextRegion
          have hrightCount : 2 ≤
              (FirstExitRecord.ofFirstExit Q base (h :: tail)).interiorGaps := by
            rw [FirstExitRecord.ofFirstExit_interiorGaps Q base (h :: tail)
              (by simp), preExitRegionCount_cons, hbaseRegion]
            simpa [Nat.add_comm] using Nat.succ_le_succ htailPositive
          have hfield := congrArg FirstExitRecord.interiorGaps hrecord
          omega
      | boundaryZero =>
          have hleftTag : (FirstExitRecord.ofFirstExit Q base [g]).tag =
              .direct := by
            rw [FirstExitRecord.ofFirstExit_tag_singleton, hbaseRegion]
            rfl
          have htailTag := (firstExit_boundary_tag Q hQ (base.transform Q h)
            tail htail hlong.tail).1 hnextRegion
          have hrightTag :
              (FirstExitRecord.ofFirstExit Q base (h :: tail)).tag =
                .boundaryZero := by
            rw [FirstExitRecord.ofFirstExit_tag_cons Q h base tail htail]
            exact htailTag
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [hleftTag, hrightTag] at hfield
          contradiction
      | boundaryOne =>
          have hleftTag : (FirstExitRecord.ofFirstExit Q base [g]).tag =
              .direct := by
            rw [FirstExitRecord.ofFirstExit_tag_singleton, hbaseRegion]
            rfl
          have htailTag := (firstExit_boundary_tag Q hQ (base.transform Q h)
            tail htail hlong.tail).2 hnextRegion
          have hrightTag :
              (FirstExitRecord.ofFirstExit Q base (h :: tail)).tag =
                .boundaryOne := by
            rw [FirstExitRecord.ofFirstExit_tag_cons Q h base tail htail]
            exact htailTag
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [hleftTag, hrightTag] at hfield
          contradiction

private theorem firstExit_next_region_eq_of_record_eq
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine) (g h : ℕ)
    (left right : GapWord) (hleft : left ≠ []) (hright : right ≠ [])
    (hbase : classifySlope (base.slope Q) = .interior)
    (hleftWord : IsFirstExitWord Q base (g :: left))
    (hrightWord : IsFirstExitWord Q base (h :: right))
    (hrecord : FirstExitRecord.ofFirstExit Q base (g :: left) =
      FirstExitRecord.ofFirstExit Q base (h :: right)) :
    classifySlope ((base.transform Q g).slope Q) =
      classifySlope ((base.transform Q h).slope Q) := by
  let leftRegion := classifySlope ((base.transform Q g).slope Q)
  let rightRegion := classifySlope ((base.transform Q h).slope Q)
  have hleftNon : leftRegion ≠ .exterior := hleftWord.next_nonexterior hleft
  have hrightNon : rightRegion ≠ .exterior := hrightWord.next_nonexterior hright
  have hcounts :
      preExitRegionCount Q (base.transform Q g) left .interior =
        preExitRegionCount Q (base.transform Q h) right .interior := by
    have hfield := congrArg FirstExitRecord.interiorGaps hrecord
    rw [FirstExitRecord.ofFirstExit_interiorGaps Q base (g :: left)
        (by simp),
      FirstExitRecord.ofFirstExit_interiorGaps Q base (h :: right)
        (by simp),
      preExitRegionCount_cons, preExitRegionCount_cons, hbase] at hfield
    omega
  by_cases hleftInterior : leftRegion = .interior
  · have hleftPos : 0 <
        preExitRegionCount Q (base.transform Q g) left .interior :=
      preExitRegionCount_pos_of_base_region Q (base.transform Q g) left
        .interior hleft hleftInterior
    by_contra hne
    have hrightBoundary : rightRegion = .boundaryZero ∨
        rightRegion = .boundaryOne := by
      cases hrightRegion : rightRegion with
      | interior => exact (hne (hleftInterior.trans hrightRegion.symm)).elim
      | boundaryZero => exact Or.inl rfl
      | boundaryOne => exact Or.inr rfl
      | exterior => exact (hrightNon hrightRegion).elim
    have hrightZero :
        preExitRegionCount Q (base.transform Q h) right .interior = 0 :=
      preExitRegionCount_interior_eq_zero_of_boundary Q hQ
        (base.transform Q h) right hrightBoundary hrightWord.tail
    omega
  · have hleftBoundary : leftRegion = .boundaryZero ∨
        leftRegion = .boundaryOne := by
      cases hleftRegion : leftRegion with
      | interior => exact (hleftInterior hleftRegion).elim
      | boundaryZero => exact Or.inl rfl
      | boundaryOne => exact Or.inr rfl
      | exterior => exact (hleftNon hleftRegion).elim
    by_cases hrightInterior : rightRegion = .interior
    · have hrightPos : 0 <
          preExitRegionCount Q (base.transform Q h) right .interior :=
        preExitRegionCount_pos_of_base_region Q (base.transform Q h) right
          .interior hright hrightInterior
      have hleftZero :
          preExitRegionCount Q (base.transform Q g) left .interior = 0 :=
        preExitRegionCount_interior_eq_zero_of_boundary Q hQ
          (base.transform Q g) left hleftBoundary hleftWord.tail
      omega
    · have hrightBoundary : rightRegion = .boundaryZero ∨
          rightRegion = .boundaryOne := by
        cases hrightRegion : rightRegion with
        | interior => exact (hrightInterior hrightRegion).elim
        | boundaryZero => exact Or.inl rfl
        | boundaryOne => exact Or.inr rfl
        | exterior => exact (hrightNon hrightRegion).elim
      rcases hleftBoundary with hleftZero | hleftOne
      · rcases hrightBoundary with hrightZero | hrightOne
        · exact hleftZero.trans hrightZero.symm
        · have hleftTag := (firstExit_boundary_tag Q hQ
            (base.transform Q g) left hleft hleftWord.tail).1 hleftZero
          have hrightTag := (firstExit_boundary_tag Q hQ
            (base.transform Q h) right hright hrightWord.tail).2 hrightOne
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [FirstExitRecord.ofFirstExit_tag_cons Q g base left hleft,
            FirstExitRecord.ofFirstExit_tag_cons Q h base right hright,
            hleftTag, hrightTag] at hfield
          contradiction
      · rcases hrightBoundary with hrightZero | hrightOne
        · have hleftTag := (firstExit_boundary_tag Q hQ
            (base.transform Q g) left hleft hleftWord.tail).2 hleftOne
          have hrightTag := (firstExit_boundary_tag Q hQ
            (base.transform Q h) right hright hrightWord.tail).1 hrightZero
          have hfield := congrArg FirstExitRecord.tag hrecord
          rw [FirstExitRecord.ofFirstExit_tag_cons Q g base left hleft,
            FirstExitRecord.ofFirstExit_tag_cons Q h base right hright,
            hleftTag, hrightTag] at hfield
          contradiction
        · exact hleftOne.trans hrightOne.symm

/-- Once the initial occurrence line is fixed, the polynomial first-exit
record reconstructs the complete positive transition word. -/
private theorem FirstExitRecord.ofFirstExit_injective_on_firstExit
    (Q : ℕ) (hQ : 0 < Q) (base : AffineLine)
    (left right : GapWord) (hleft : IsFirstExitWord Q base left)
    (hright : IsFirstExitWord Q base right)
    (hrecord : FirstExitRecord.ofFirstExit Q base left =
      FirstExitRecord.ofFirstExit Q base right) :
    left = right := by
  induction left generalizing base right with
  | nil =>
      cases right with
      | nil => rfl
      | cons h tail =>
          have hbaseExterior : classifySlope (base.slope Q) = .exterior := by
            simpa only [AffineLine.transformWord] using hleft.2.2
          have hbaseNon := hright.base_nonexterior (by simp)
          exact (hbaseNon hbaseExterior).elim
  | cons g left ih =>
      cases right with
      | nil =>
          have hbaseNon := hleft.base_nonexterior (by simp)
          have hbaseExterior : classifySlope (base.slope Q) = .exterior := by
            simpa only [AffineLine.transformWord] using hright.2.2
          exact (hbaseNon hbaseExterior).elim
      | cons h right =>
          by_cases hleftTail : left = []
          · subst left
            by_cases hrightTail : right = []
            · subst right
              have hfield := congrArg FirstExitRecord.exitGap hrecord
              have hgh : g = h := by
                simpa [FirstExitRecord.ofFirstExit] using hfield
              subst h
              rfl
            · exact (singleton_record_ne_long_firstExit Q hQ base g h right
                hrightTail hleft hright hrecord).elim
          · by_cases hrightTail : right = []
            · subst right
              exact (singleton_record_ne_long_firstExit Q hQ base h g left
                hleftTail hright hleft hrecord.symm).elim
            · have hbaseNon := hleft.base_nonexterior (by simp)
              have hhead : g = h := by
                cases hbaseRegion : classifySlope (base.slope Q) with
                | exterior => exact (hbaseNon hbaseRegion).elim
                | boundaryZero =>
                    obtain ⟨x, hshape⟩ := firstExit_boundaryZero_singleton Q
                      hQ base (g :: left) hbaseRegion hleft
                    have : left = [] := by simpa using congrArg List.tail hshape
                    exact (hleftTail this).elim
                | boundaryOne =>
                    have hg := firstExit_boundaryOne_head_eq_one Q hQ base g
                      left hleftTail hbaseRegion hleft
                    have hh := firstExit_boundaryOne_head_eq_one Q hQ base h
                      right hrightTail hbaseRegion hright
                    omega
                | interior =>
                    have hregion := firstExit_next_region_eq_of_record_eq Q hQ
                      base g h left right hleftTail hrightTail hbaseRegion
                      hleft hright hrecord
                    apply positive_gap_eq_of_same_nonexterior_region Q hQ base
                      g h hleft.head_positive hright.head_positive hbaseRegion
                      (classifySlope ((base.transform Q g).slope Q))
                      (hleft.next_nonexterior hleftTail)
                    · rfl
                    · exact hregion.symm ▸ rfl
              subst h
              have htailRecord :=
                FirstExitRecord.tail_eq_of_cons_record_eq Q g base left right
                  hleftTail hrightTail hrecord
              have htail := ih (base.transform Q g) right hleft.tail
                hright.tail htailRecord
              rw [htail]
/-- The stronger affine-locking witness produces the unique deterministic
record consumed by the exterior encoding. -/
theorem FirstExitRecord.exists_describes_of_actual
    (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold)
    (line : AffineLine) (continuation : GapWord)
    (hactual : IsActualFirstExteriorContinuation W Z0 e line continuation) :
    ∃ record : FirstExitRecord,
      FirstExitRecord.DescribesFirstExit W Z0 e record line continuation := by
  rcases hactual with
    ⟨base, finish, before, after, hbase, hsuffix, hbefore,
      hfirst, hexterior, hcontinuation⟩
  refine ⟨FirstExitRecord.ofFirstExit W.rational.eta.den base before, ?_⟩
  refine ⟨base, finish, before, after, hbase, hsuffix, hbefore,
    hcontinuation, hexterior, ?_, rfl⟩
  intro r hr
  let state := base.transformWord W.rational.eta.den (before.take r)
  have htrajectory : SharedGapTrajectory W.rational.eta.den base
      (before.take r) state :=
    (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).2 rfl
  exact ⟨state, htrajectory, hfirst r hr state htrajectory⟩

private theorem getLastD_mem_of_ne_nil {α : Type*} (word : List α)
    (default : α) (hword : word ≠ []) : word.getLastD default ∈ word := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons a tail =>
      simpa only [List.getLastD_cons] using
        (List.getLastD_mem_cons (l := tail) (a := a))

private theorem dropLast_append_getLastD {α : Type*} (word : List α)
    (default : α) (hword : word ≠ []) :
    word.dropLast ++ [word.getLastD default] = word := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons a tail =>
      have hcons : a :: tail ≠ [] := by simp
      rw [List.getLastD_cons, ← List.getLast_eq_getLastD hcons]
      exact List.dropLast_append_getLast hcons

/-- The deterministic first-exit record satisfies all finite ranges used in
the polynomial record count.  The `+1` is forced by the possible endpoint
`x = 2X`, for which `Nat.log 2 x = L + 1`. -/
theorem FirstExitRecord.ofFirstExit_valid
    (Q m L Cgap : ℕ) (hQ : 0 < Q) (base line : AffineLine)
    (before : GapWord)
    (htrajectory : SharedGapTrajectory Q base before line)
    (hexterior : classifySlope (line.slope Q) = .exterior)
    (hlength : before.length ≤ m) (hpositive : before.Positive)
    (hgap : ∀ g ∈ before, g ≤ L + Cgap + 1) :
    (FirstExitRecord.ofFirstExit Q base before).Valid m L Cgap := by
  by_cases hnil : before = []
  · subst before
    simp [FirstExitRecord.ofFirstExit, FirstExitRecord.initialExterior,
      FirstExitRecord.Valid]
  rw [FirstExitRecord.ofFirstExit, dif_neg hnil]
  have hinteriorCount :
      ((List.range before.length).filter fun r =>
        classifySlope ((base.transformWord Q (before.take r)).slope Q) =
          .interior).length ≤ m :=
    (List.length_filter_le _ _).trans (by simpa using hlength)
  have hboundaryCount :
      ((List.range before.length).filter fun r =>
        classifySlope ((base.transformWord Q (before.take r)).slope Q) =
          .boundaryOne).length ≤ m :=
    (List.length_filter_le _ _).trans (by simpa using hlength)
  have hlastMem : before.getLastD 0 ∈ before :=
    getLastD_mem_of_ne_nil before 0 hnil
  have hlastPos : 1 ≤ before.getLastD 0 :=
    hpositive _ hlastMem
  have hlastBound : before.getLastD 0 ≤ L + Cgap + 1 :=
    hgap _ hlastMem
  have htagNotInitial :
      FirstExitRecord.tagOfPreExitRegion
          (classifySlope ((base.transformWord Q before.dropLast).slope Q)) ≠
        .initialExterior := by
    cases classifySlope ((base.transformWord Q before.dropLast).slope Q) <;>
      simp [FirstExitRecord.tagOfPreExitRegion]
  have hboundaryExit :
      FirstExitRecord.tagOfPreExitRegion
            (classifySlope ((base.transformWord Q before.dropLast).slope Q)) =
          .boundaryOne →
        2 ≤ before.getLastD 0 := by
    intro htag
    have hpre :
        classifySlope ((base.transformWord Q before.dropLast).slope Q) =
          .boundaryOne := by
      cases hregion :
          classifySlope ((base.transformWord Q before.dropLast).slope Q) <;>
        simp [FirstExitRecord.tagOfPreExitRegion, hregion] at htag
      rfl
    by_contra hnot
    have hlast : before.getLastD 0 = 1 := by omega
    have hlineEq :
        line = (base.transformWord Q before.dropLast).transform Q
          (before.getLastD 0) := by
      have hterminal :=
        (sharedGapTrajectory_iff_eq_transformWord Q base line before).1
          htrajectory
      rw [← dropLast_append_getLastD before 0 hnil,
        AffineLine.transformWord_append] at hterminal
      simpa only [AffineLine.transformWord] using hterminal
    have hpreSlope :
        (base.transformWord Q before.dropLast).slope Q = 1 := by
      unfold classifySlope at hpre
      by_cases hzero :
          (base.transformWord Q before.dropLast).slope Q = 0
      · simp [hzero] at hpre
      rw [if_neg hzero] at hpre
      by_cases hone :
          (base.transformWord Q before.dropLast).slope Q = 1
      · exact hone
      rw [if_neg hone] at hpre
      split at hpre <;> contradiction
    have hnextSlope :
        ((base.transformWord Q before.dropLast).transform Q 1).slope Q = 1 := by
      rw [AffineLine.slope_transform Q hQ, hpreSlope]
      norm_num
    have hnextClass :
        classifySlope
            (((base.transformWord Q before.dropLast).transform Q 1).slope Q) =
          .boundaryOne := by
      simp [hnextSlope, classifySlope]
    rw [hlineEq, hlast, hnextClass] at hexterior
    contradiction
  refine ⟨hinteriorCount, hboundaryCount, ?_, ?_, hboundaryExit⟩
  · intro htag
    exact (htagNotInitial htag).elim
  · intro _htag
    exact ⟨hlastPos, hlastBound⟩

def validFirstExitRecords (m L Cgap : ℕ) : Set FirstExitRecord :=
  {record | record.Valid m L Cgap}

private def firstExitRecordCoordinates (record : FirstExitRecord) :
    ℕ × (ExitTag × (ℕ × ℕ)) :=
  (record.interiorGaps, (record.tag, (record.boundaryOnes, record.exitGap)))

private theorem firstExitRecordCoordinates_injective :
    Function.Injective firstExitRecordCoordinates := by
  intro a b h
  rcases a with ⟨ai, atag, ab, ae⟩
  rcases b with ⟨bi, bt, bb, be⟩
  simp only [firstExitRecordCoordinates] at h
  cases h
  rfl

/-- The first-exit records form a polynomial-size finite family. -/
theorem validFirstExitRecords_finite_and_ncard_le (m L Cgap : ℕ) :
    (validFirstExitRecords m L Cgap).Finite ∧
      (validFirstExitRecords m L Cgap).ncard ≤
        (m + 1) * 4 * (m + 1) * (L + Cgap + 2) := by
  let box : Set (ℕ × (ExitTag × (ℕ × ℕ))) :=
    Set.Iic m ×ˢ
      (Set.univ ×ˢ (Set.Iic m ×ˢ Set.Iic (L + Cgap + 1)))
  have hboxFinite : box.Finite := by
    exact (Set.finite_Iic m).prod
      (Set.finite_univ.prod
        ((Set.finite_Iic m).prod (Set.finite_Iic (L + Cgap + 1))))
  have hmaps : Set.MapsTo firstExitRecordCoordinates
      (validFirstExitRecords m L Cgap) box := by
    intro record hrecord
    change record.Valid m L Cgap at hrecord
    have hexit : record.exitGap ≤ L + Cgap + 1 := by
      by_cases hinitial : record.tag = .initialExterior
      · have hrecordEq := hrecord.2.2.1 hinitial
        rw [hrecordEq]
        simp [FirstExitRecord.initialExterior]
      · exact (hrecord.2.2.2.1 hinitial).2
    exact ⟨hrecord.1, Set.mem_univ _, hrecord.2.1, hexit⟩
  have himageFinite :
      (firstExitRecordCoordinates ''
        validFirstExitRecords m L Cgap).Finite := by
    apply hboxFinite.subset
    rintro _ ⟨record, hrecord, rfl⟩
    exact hmaps hrecord
  have hfinite : (validFirstExitRecords m L Cgap).Finite :=
    Set.Finite.of_finite_image himageFinite
      (firstExitRecordCoordinates_injective.injOn)
  refine ⟨hfinite, ?_⟩
  calc
    (validFirstExitRecords m L Cgap).ncard =
        (firstExitRecordCoordinates ''
          validFirstExitRecords m L Cgap).ncard := by
      symm
      exact Set.ncard_image_of_injective _ firstExitRecordCoordinates_injective
    _ ≤ box.ncard := by
      apply Set.ncard_le_ncard _ hboxFinite
      rintro _ ⟨record, hrecord, rfl⟩
      exact hmaps hrecord
    _ = (m + 1) * 4 * (m + 1) * (L + Cgap + 2) := by
      have hcardExit : Fintype.card ExitTag = 4 := by decide
      have hnatCardExit : Nat.card ExitTag = 4 := by
        simpa [Nat.card_eq_fintype_card] using hcardExit
      have hpair :
          (Set.Iic (m, L + Cgap + 1) : Set (ℕ × ℕ)).ncard =
            (m + 1) * (L + Cgap + 2) := by
        rw [show (Set.Iic (m, L + Cgap + 1) : Set (ℕ × ℕ)) =
            Set.Iic m ×ˢ Set.Iic (L + Cgap + 1) by rfl,
          Set.ncard_prod, Set.ncard_Iic_nat, Set.ncard_Iic_nat]
      dsimp [box]
      rw [Set.ncard_prod, Set.ncard_Iic_nat, Set.ncard_prod,
        Set.ncard_univ, hnatCardExit, hpair]
      ring

theorem distanceToUnitInterval_pos_of_not_mem (μ : ℝ)
    (hμ : μ ∉ Set.Icc (0 : ℝ) 1) :
    0 < distanceToUnitInterval μ := by
  by_cases hneg : μ < 0
  · rw [distanceToUnitInterval, if_pos hneg]
    linarith
  · have hnonneg : 0 ≤ μ := le_of_not_gt hneg
    have hgt : 1 < μ := by
      by_contra hnot
      exact hμ ⟨hnonneg, le_of_not_gt hnot⟩
    rw [distanceToUnitInterval, if_neg hneg, if_pos hgt]
    linarith

theorem not_mem_unitInterval_of_distance_pos (μ : ℝ)
    (hμ : 0 < distanceToUnitInterval μ) :
    μ ∉ Set.Icc (0 : ℝ) 1 := by
  intro hmem
  rw [distanceToUnitInterval, if_neg (not_lt_of_ge hmem.1),
    if_neg (not_lt_of_ge hmem.2)] at hμ
  linarith

theorem classifySlope_exterior_of_not_mem (μ : ℚ)
    (hμ : (μ : ℝ) ∉ Set.Icc (0 : ℝ) 1) :
    classifySlope μ = .exterior := by
  unfold classifySlope
  by_cases hzero : μ = 0
  · subst μ
    exact (hμ (by norm_num)).elim
  rw [if_neg hzero]
  by_cases hone : μ = 1
  · subst μ
    exact (hμ (by norm_num)).elim
  rw [if_neg hone]
  by_cases hinterior : 0 < μ ∧ μ < 1
  · exfalso
    apply hμ
    exact ⟨by exact_mod_cast hinterior.1.le,
      by exact_mod_cast hinterior.2.le⟩
  · simp [hinterior]

theorem distance_amplify_word (μ : ℝ) (word : GapWord)
    (hword : word.Positive) (hμ : μ ∉ Set.Icc (0 : ℝ) 1) :
    (2 : ℝ) ^ word.span * distanceToUnitInterval μ ≤
      distanceToUnitInterval (slopeAfter word μ) := by
  induction word generalizing μ with
  | nil => simp [GapWord.span, slopeAfter]
  | cons g gs ih =>
      have hg : 1 ≤ g := hword g (by simp)
      have hgs : GapWord.Positive gs := by
        intro x hx
        exact hword x (by simp [hx])
      let next := (2 : ℝ) ^ g * μ - 1
      have hstep :
          (2 : ℝ) ^ g * distanceToUnitInterval μ ≤
            distanceToUnitInterval next := by
        exact lem_off_amplify μ g hg hμ
      have hnextPos : 0 < distanceToUnitInterval next := by
        have hleft : 0 < (2 : ℝ) ^ g * distanceToUnitInterval μ :=
          mul_pos (by positivity) (distanceToUnitInterval_pos_of_not_mem μ hμ)
        exact lt_of_lt_of_le hleft hstep
      have hnext : next ∉ Set.Icc (0 : ℝ) 1 :=
        not_mem_unitInterval_of_distance_pos next hnextPos
      have htail := ih next hgs hnext
      calc
        (2 : ℝ) ^ GapWord.span (g :: gs) * distanceToUnitInterval μ =
            (2 : ℝ) ^ GapWord.span gs *
              ((2 : ℝ) ^ g * distanceToUnitInterval μ) := by
          simp only [GapWord.span, List.sum_cons, pow_add]
          ring
        _ ≤ (2 : ℝ) ^ GapWord.span gs * distanceToUnitInterval next := by
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
        _ ≤ distanceToUnitInterval (slopeAfter gs next) := htail
        _ = distanceToUnitInterval (slopeAfter (g :: gs) μ) := rfl

theorem exterior_rational_distance_lower (Q : ℕ) (hQ : 0 < Q)
    (line : AffineLine)
    (hexterior : classifySlope (line.slope Q) = .exterior) :
    (1 : ℝ) ≤ (Q : ℝ) * (line.H : ℝ) *
      distanceToUnitInterval (line.slope Q : ℝ) := by
  have hout := classifySlope_exterior_not_mem (line.slope Q) hexterior
  have hQrQ : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hHrQ : (0 : ℚ) < line.H := by exact_mod_cast line.H_pos
  have hdenQ : (0 : ℚ) < (Q : ℚ) * line.H := mul_pos hQrQ hHrQ
  have hQrR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHrR : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
  by_cases hneg : (line.slope Q : ℝ) < 0
  · have hnegQ : line.slope Q < 0 := by exact_mod_cast hneg
    have hKQ : (line.K : ℚ) < 0 := by
      rw [AffineLine.slope] at hnegQ
      rcases (div_neg_iff.mp hnegQ) with hbad | hgood
      · exact (not_lt_of_ge hdenQ.le hbad.2).elim
      · exact hgood.1
    have hKneg : line.K < 0 := by exact_mod_cast hKQ
    have hK : line.K ≤ -1 := by omega
    have hid :
        (Q : ℝ) * (line.H : ℝ) *
            distanceToUnitInterval (line.slope Q : ℝ) =
          -(line.K : ℝ) := by
      rw [distanceToUnitInterval, if_pos hneg, AffineLine.slope]
      push_cast
      field_simp [ne_of_gt hQrR, ne_of_gt hHrR]
    rw [hid]
    have hfinal : (1 : ℤ) ≤ -line.K := by omega
    exact_mod_cast hfinal
  · have hnonneg : (0 : ℝ) ≤ line.slope Q := le_of_not_gt hneg
    have hgt : (1 : ℝ) < line.slope Q := by
      by_contra hnot
      exact hout ⟨hnonneg, le_of_not_gt hnot⟩
    have hgtQ : (1 : ℚ) < line.slope Q := by exact_mod_cast hgt
    have hKQ : (Q : ℚ) * line.H < line.K := by
      rw [AffineLine.slope] at hgtQ
      simpa using (lt_div_iff₀ hdenQ).mp hgtQ
    have hK : (Q : ℤ) * line.H + 1 ≤ line.K := by exact_mod_cast hKQ
    have hid :
        (Q : ℝ) * (line.H : ℝ) *
            distanceToUnitInterval (line.slope Q : ℝ) =
          (line.K : ℝ) - (Q : ℝ) * line.H := by
      rw [distanceToUnitInterval, if_neg hneg, if_pos hgt,
        AffineLine.slope]
      push_cast
      field_simp [ne_of_gt hQrR, ne_of_gt hHrR]
    rw [hid]
    have hfinal : (1 : ℤ) ≤ line.K - (Q : ℤ) * line.H := by omega
    exact_mod_cast hfinal

/-- A finite set of integer parameters whose values under a decreasing affine
map lie in an interval of length `B` has the expected spacing bound. -/
private theorem affineIntegerParameterCount
    (S : Set ℤ) (C J B : ℤ) (hJ : J < 0) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ S, 0 ≤ C + J * t ∧ C + J * t ≤ B) :
    S.Finite ∧
      (S.ncard : ℝ) ≤ 1 + (B : ℝ) / (-(J : ℝ)) := by
  let f : ℤ → ℤ := fun t => C + J * t
  have himage : f '' S ⊆ Set.Icc 0 B := by
    rintro y ⟨t, ht, rfl⟩
    exact hbound t ht
  have hfimage : (f '' S).Finite :=
    (Set.finite_Icc 0 B).subset himage
  have hinj : Set.InjOn f S := by
    intro x _ y _ hxy
    dsimp [f] at hxy
    apply mul_left_cancel₀ (ne_of_lt hJ)
    exact add_left_cancel hxy
  have hfinite : S.Finite :=
    Set.Finite.of_finite_image hfimage hinj
  refine ⟨hfinite, ?_⟩
  by_cases hempty : S = ∅
  · rw [hempty, Set.ncard_empty]
    have hBreal : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hJreal : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hquot : (0 : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) := by
      exact div_nonneg hBreal hJreal.le
    norm_num
    linarith
  · have hnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    let s : Finset ℤ := hfinite.toFinset
    have hsne : s.Nonempty := by
      rcases hnonempty with ⟨t, ht⟩
      exact ⟨t, by simpa [s] using ht⟩
    let lo : ℤ := s.min' hsne
    let hi : ℤ := s.max' hsne
    have hlo_mem : lo ∈ s := by
      exact s.min'_mem hsne
    have hhi_mem : hi ∈ s := by
      exact s.max'_mem hsne
    have hlohi : lo ≤ hi := by
      exact s.min'_le hi hhi_mem
    have hsubset : s ⊆ Finset.Icc lo hi := by
      intro t ht
      simp only [Finset.mem_Icc]
      exact ⟨s.min'_le t ht, s.le_max' t ht⟩
    have hcard_nat : s.card ≤ (Finset.Icc lo hi).card :=
      Finset.card_le_card hsubset
    rw [Int.card_Icc] at hcard_nat
    have hnonneg : 0 ≤ hi + 1 - lo := by omega
    have hcard_int : (s.card : ℤ) ≤ hi + 1 - lo := by
      have hcast : (s.card : ℤ) ≤ ((hi + 1 - lo).toNat : ℤ) := by
        exact_mod_cast hcard_nat
      rwa [Int.toNat_of_nonneg hnonneg] at hcast
    have hncard_eq : S.ncard = s.card := by
      simpa [s] using Set.ncard_eq_toFinset_card S hfinite
    have hcard_real : (S.ncard : ℝ) ≤ ((hi + 1 - lo : ℤ) : ℝ) := by
      rw [hncard_eq]
      exact_mod_cast hcard_int
    have hloS : lo ∈ S := by
      simpa [s] using hlo_mem
    have hhiS : hi ∈ S := by
      simpa [s] using hhi_mem
    have hspan_int : (-J) * (hi - lo) ≤ B := by
      calc
        (-J) * (hi - lo) =
            (C + J * lo) - (C + J * hi) := by ring
        _ ≤ B := by
          linarith [(hbound lo hloS).2, (hbound hi hhiS).1]
    have hstep : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hspan_real₀ :
        (-(J : ℝ)) * ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hspan_int
    have hspan_real :
        ((hi - lo : ℤ) : ℝ) * (-(J : ℝ)) ≤ (B : ℝ) := by
      simpa [mul_comm] using hspan_real₀
    have hspan_div :
        ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) :=
      (le_div_iff₀ hstep).2 hspan_real
    push_cast at hcard_real hspan_div
    linarith

/-- Paper label: `lem:off-corridor` (Section 7). -/
theorem lem_off_corridor (Q : ℕ) (hQ : 0 < Q) :
    ∃ Ccorr : ℝ, 0 < Ccorr ∧ ∀ X : ℕ, ∀ line : AffineLine,
      (line.slope Q : ℝ) ∉ Set.Icc (0 : ℝ) 1 →
      {t : ℤ | InAdmissibleCarryRegion Q X
        (line.A + line.H * t) (line.C + line.K * t)}.Finite ∧
      ({t : ℤ | InAdmissibleCarryRegion Q X
        (line.A + line.H * t) (line.C + line.K * t)}.ncard : ℝ) ≤
        1 + Ccorr * X /
          ((line.H : ℝ) * distanceToUnitInterval (line.slope Q)) := by
  refine ⟨5, by norm_num, ?_⟩
  intro X line hslope
  let S : Set ℤ :=
    {t | InAdmissibleCarryRegion Q X
      (line.A + line.H * t) (line.C + line.K * t)}
  change S.Finite ∧
    (S.ncard : ℝ) ≤
      1 + 5 * X /
        ((line.H : ℝ) * distanceToUnitInterval (line.slope Q))
  by_cases hX : X = 0
  · subst X
    have hsub : S.Subsingleton := by
      intro t ht u hu
      change InAdmissibleCarryRegion Q 0
        (line.A + line.H * t) (line.C + line.K * t) at ht
      change InAdmissibleCarryRegion Q 0
        (line.A + line.H * u) (line.C + line.K * u) at hu
      rcases ht with ⟨hxt₀, hxt₁, _, _⟩
      rcases hu with ⟨hxu₀, hxu₁, _, _⟩
      have hxt : line.A + line.H * t = 0 := by omega
      have hxu : line.A + line.H * u = 0 := by omega
      apply mul_left_cancel₀ (ne_of_gt line.H_pos)
      linarith
    have hfinite : S.Finite := hsub.finite
    refine ⟨hfinite, ?_⟩
    have hcard : S.ncard ≤ 1 :=
      (Set.ncard_le_one hfinite).2 fun _ ht _ hu => hsub ht hu
    have hcard_real : (S.ncard : ℝ) ≤ 1 := by exact_mod_cast hcard
    simpa using hcard_real
  · have hXone : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hX
    have hQint : (0 : ℤ) ≤ (Q : ℤ) := by omega
    let B : ℤ := (Q : ℤ) * (3 * (X : ℤ) + 2)
    have hB : (0 : ℤ) ≤ B := by
      dsimp [B]
      positivity
    have hxwidth : 3 * (X : ℤ) + 2 ≤ 5 * X := by
      exact_mod_cast (show 3 * X + 2 ≤ 5 * X by omega)
    have hBfive : B ≤ 5 * (Q : ℤ) * X := by
      dsimp [B]
      calc
        (Q : ℤ) * (3 * (X : ℤ) + 2) ≤
            (Q : ℤ) * (5 * X) :=
          mul_le_mul_of_nonneg_left hxwidth hQint
        _ = 5 * (Q : ℤ) * X := by ring
    have hQrat : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
    have hHrat : (0 : ℚ) < (line.H : ℚ) := by
      exact_mod_cast line.H_pos
    have hdenQ : (0 : ℚ) < (Q : ℚ) * line.H :=
      mul_pos hQrat hHrat
    have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hHr : (line.H : ℝ) ≠ 0 := by
      exact_mod_cast line.H_pos.ne'
    by_cases hneg : (line.slope Q : ℝ) < 0
    · have hnegQ : line.slope Q < 0 := by exact_mod_cast hneg
      have hKQ : (line.K : ℚ) < 0 := by
        rw [AffineLine.slope] at hnegQ
        simpa using (div_lt_iff₀ hdenQ).mp hnegQ
      have hK : line.K < 0 := by exact_mod_cast hKQ
      have hcount := affineIntegerParameterCount
        S line.C line.K B hK hB (by
          intro t ht
          change InAdmissibleCarryRegion Q X
            (line.A + line.H * t) (line.C + line.K * t) at ht
          rcases ht with ⟨_, hxhi, hrlo, hrhi⟩
          have hxplus : line.A + line.H * t + 2 ≤
              3 * (X : ℤ) + 2 := by linarith
          have hprod := mul_le_mul_of_nonneg_left hxplus hQint
          exact ⟨hrlo, hrhi.trans (by simpa [B] using hprod)⟩)
      have hminusK : (0 : ℝ) < -(line.K : ℝ) := by
        exact_mod_cast (neg_pos.mpr hK)
      have hBfive_real : (B : ℝ) ≤
          5 * (Q : ℝ) * X := by exact_mod_cast hBfive
      have hden_id :
          (line.H : ℝ) * (-(line.slope Q : ℝ)) =
            -(line.K : ℝ) / (Q : ℝ) := by
        rw [AffineLine.slope]
        push_cast
        field_simp [hQr, hHr]
      have hratio : (B : ℝ) / (-(line.K : ℝ)) ≤
          5 * X /
            ((line.H : ℝ) * distanceToUnitInterval (line.slope Q)) := by
        rw [distanceToUnitInterval, if_pos hneg, hden_id]
        calc
          (B : ℝ) / (-(line.K : ℝ)) ≤
              (5 * (Q : ℝ) * X) / (-(line.K : ℝ)) :=
            (div_le_div_iff_of_pos_right hminusK).2 hBfive_real
          _ = 5 * X / (-(line.K : ℝ) / (Q : ℝ)) := by
            field_simp [hQr, ne_of_lt hminusK]
      refine ⟨hcount.1, ?_⟩
      nlinarith [hcount.2, hratio]
    · have hnonneg : (0 : ℝ) ≤ (line.slope Q : ℝ) :=
        le_of_not_gt hneg
      have hgt : (1 : ℝ) < line.slope Q := by
        by_contra hnot
        exact hslope ⟨hnonneg, le_of_not_gt hnot⟩
      have hgtQ : (1 : ℚ) < line.slope Q := by exact_mod_cast hgt
      have hKQ : (Q : ℚ) * line.H < line.K := by
        rw [AffineLine.slope] at hgtQ
        exact (one_lt_div hdenQ).mp hgtQ
      have hK : (Q : ℤ) * line.H < line.K := by exact_mod_cast hKQ
      let Ccomp : ℤ := (Q : ℤ) * (line.A + 2) - line.C
      let J : ℤ := (Q : ℤ) * line.H - line.K
      have hJ : J < 0 := by
        dsimp [J]
        omega
      have hcount := affineIntegerParameterCount
        S Ccomp J B hJ hB (by
          intro t ht
          change InAdmissibleCarryRegion Q X
            (line.A + line.H * t) (line.C + line.K * t) at ht
          rcases ht with ⟨_, hxhi, hrlo, hrhi⟩
          have hxplus : line.A + line.H * t + 2 ≤
              3 * (X : ℤ) + 2 := by linarith
          have hprod := mul_le_mul_of_nonneg_left hxplus hQint
          have hid : Ccomp + J * t =
              (Q : ℤ) * (line.A + line.H * t + 2) -
                (line.C + line.K * t) := by
            dsimp [Ccomp, J]
            ring
          rw [hid]
          exact ⟨sub_nonneg.mpr hrhi,
            (sub_le_self _ hrlo).trans (by simpa [B] using hprod)⟩)
      have hminusJ : (0 : ℝ) < -(J : ℝ) := by
        exact_mod_cast (neg_pos.mpr hJ)
      have hBfive_real : (B : ℝ) ≤
          5 * (Q : ℝ) * X := by exact_mod_cast hBfive
      have hden_id :
          (line.H : ℝ) * ((line.slope Q : ℝ) - 1) =
            -(J : ℝ) / (Q : ℝ) := by
        dsimp [J]
        rw [AffineLine.slope]
        push_cast
        field_simp [hQr, hHr]
        ring
      have hratio : (B : ℝ) / (-(J : ℝ)) ≤
          5 * X /
            ((line.H : ℝ) * distanceToUnitInterval (line.slope Q)) := by
        rw [distanceToUnitInterval, if_neg hneg, if_pos hgt, hden_id]
        calc
          (B : ℝ) / (-(J : ℝ)) ≤
              (5 * (Q : ℝ) * X) / (-(J : ℝ)) :=
            (div_le_div_iff_of_pos_right hminusJ).2 hBfive_real
          _ = 5 * X / (-(J : ℝ) / (Q : ℝ)) := by
            field_simp [hQr, ne_of_lt hminusJ]
      refine ⟨hcount.1, ?_⟩
      nlinarith [hcount.2, hratio]

/-- Paper label: `prop:fixed-off-word` (Section 7). -/
theorem prop_fixed_off_word (Q : ℕ) (hQ : 0 < Q) :
    ∃ Coff : ℝ, 0 < Coff ∧ ∀ X : ℕ, ∀ line : AffineLine,
      ∀ word : GapWord, word.Positive →
      classifySlope (line.slope Q) = .exterior →
      (admissibleOriginalParameters Q X line word).Finite ∧
        ((admissibleOriginalParameters Q X line word).ncard : ℝ) ≤
          1 + Coff * X * (2 : ℝ) ^ (-(word.span : ℤ)) := by
  rcases lem_off_corridor Q hQ with ⟨Ccorr, hCcorr, hcorr⟩
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨Ccorr * Q, mul_pos hCcorr hQr, ?_⟩
  intro X line word hword hexterior
  let finish := line.transformWord Q word
  have hinitialOutside := classifySlope_exterior_not_mem (line.slope Q) hexterior
  have hinitialDistance :
      (1 : ℝ) ≤ (Q : ℝ) * (line.H : ℝ) *
        distanceToUnitInterval (line.slope Q : ℝ) :=
    exterior_rational_distance_lower Q hQ line hexterior
  have hamplify :
      (2 : ℝ) ^ word.span * distanceToUnitInterval (line.slope Q : ℝ) ≤
        distanceToUnitInterval (finish.slope Q : ℝ) := by
    rw [AffineLine.transformWord_slope_real Q hQ line word]
    exact distance_amplify_word (line.slope Q : ℝ) word hword hinitialOutside
  have hfinishDistance : 0 < distanceToUnitInterval (finish.slope Q : ℝ) := by
    have hleft :
        0 < (2 : ℝ) ^ word.span *
          distanceToUnitInterval (line.slope Q : ℝ) :=
      mul_pos (by positivity)
        (distanceToUnitInterval_pos_of_not_mem (line.slope Q : ℝ) hinitialOutside)
    exact lt_of_lt_of_le hleft hamplify
  have hfinishOutside :
      (finish.slope Q : ℝ) ∉ Set.Icc (0 : ℝ) 1 :=
    not_mem_unitInterval_of_distance_pos (finish.slope Q : ℝ) hfinishDistance
  let corridor : Set ℤ :=
    {t | InAdmissibleCarryRegion Q X
      (finish.A + finish.H * t) (finish.C + finish.K * t)}
  have hsubset : admissibleOriginalParameters Q X line word ⊆ corridor := by
    intro t ht
    change InAdmissibleCarryRegion Q X
        (line.A + line.H * t) (line.C + line.K * t) ∧
      InAdmissibleCarryRegion Q X
        (finish.A + finish.H * t) (finish.C + finish.K * t) at ht
    exact ht.2
  have hcorridor : corridor.Finite ∧
      (corridor.ncard : ℝ) ≤
        1 + Ccorr * X /
          ((finish.H : ℝ) * distanceToUnitInterval (finish.slope Q)) := by
    simpa [corridor] using hcorr X finish hfinishOutside
  refine ⟨hcorridor.1.subset hsubset, ?_⟩
  have hncardNat := Set.ncard_le_ncard hsubset hcorridor.1
  have hncardReal :
      ((admissibleOriginalParameters Q X line word).ncard : ℝ) ≤
        (corridor.ncard : ℝ) := by exact_mod_cast hncardNat
  calc
    ((admissibleOriginalParameters Q X line word).ncard : ℝ) ≤
        (corridor.ncard : ℝ) := hncardReal
    _ ≤ 1 + Ccorr * X /
          ((finish.H : ℝ) * distanceToUnitInterval (finish.slope Q)) :=
      hcorridor.2
    _ ≤ 1 + (Ccorr * Q) * X * (2 : ℝ) ^ (-(word.span : ℤ)) := by
      have hH : (finish.H : ℝ) = line.H := by
        exact_mod_cast AffineLine.transformWord_H Q line word
      have hlineH : (0 : ℝ) < line.H := by exact_mod_cast line.H_pos
      have hden :
          0 < (finish.H : ℝ) * distanceToUnitInterval (finish.slope Q) :=
        mul_pos (by simpa [hH] using hlineH) hfinishDistance
      have hpow : (0 : ℝ) < (2 : ℝ) ^ word.span := by positivity
      have hdenprod :
          (2 : ℝ) ^ word.span ≤
            (Q : ℝ) * ((finish.H : ℝ) *
              distanceToUnitInterval (finish.slope Q)) := by
        rw [hH]
        calc
          (2 : ℝ) ^ word.span ≤
              (2 : ℝ) ^ word.span *
                ((Q : ℝ) * (line.H : ℝ) *
                  distanceToUnitInterval (line.slope Q : ℝ)) := by
            nlinarith [hinitialDistance]
          _ ≤ (Q : ℝ) * (line.H : ℝ) *
                distanceToUnitInterval (finish.slope Q : ℝ) := by
            have := mul_le_mul_of_nonneg_left hamplify
              (mul_nonneg hQr.le hlineH.le)
            nlinarith
          _ = (Q : ℝ) * ((line.H : ℝ) *
                distanceToUnitInterval (finish.slope Q : ℝ)) := by ring
      have hratio :
          Ccorr * X /
              ((finish.H : ℝ) * distanceToUnitInterval (finish.slope Q)) ≤
            (Ccorr * Q) * X / (2 : ℝ) ^ word.span := by
        rw [div_le_div_iff₀ hden hpow]
        have hnonneg : (0 : ℝ) ≤ Ccorr * X := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hdenprod hnonneg]
      have hzpow :
          (Ccorr * Q) * X / (2 : ℝ) ^ word.span =
            (Ccorr * Q) * X * (2 : ℝ) ^ (-(word.span : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
        ring
      rw [← hzpow]
      linarith

/-- The selected post-exit long prefix of a supplied exterior continuation. -/
def postExitLongPrefix (W : WindowSystem) (gaps : GapWord) : GapWord :=
  gaps.firstPrefixAbove (Nat.floor (W.structural.Gamma * W.L))

/-- Deterministic exterior counting data attached to an actual pair. -/
structure ExteriorSignature where
  record : FirstExitRecord
  word : GapWord
  deriving DecidableEq, Repr

def ValidExteriorSignature (W : WindowSystem) (Z0 Cgap : ℕ)
    (e : WindowThreshold) (signature : ExteriorSignature) : Prop :=
  signature.record.Valid W.m W.L Cgap ∧ signature.word.Positive ∧
    ∃ line : AffineLine, ∃ continuation : GapWord,
      FirstExitRecord.DescribesFirstExit W Z0 e signature.record line continuation ∧
      IsExteriorTrajectory W.rational.eta.den line continuation ∧
      signature.word = postExitLongPrefix W continuation

def exteriorSignatures (W : WindowSystem) (Z0 Cgap : ℕ) :
    Set ExteriorSignature :=
  {signature | ∃ e : WindowThreshold,
    LongExteriorPair W Z0 e ∧ ValidExteriorSignature W Z0 Cgap e signature}

/-- Uniform natural ceiling for a selected post-exit prefix. -/
def exteriorWordBound (W : WindowSystem) (Cgap : ℕ) : ℕ :=
  Nat.floor (W.structural.Gamma * W.L) + W.L + Cgap + 1

/-- Anchors supporting at least one long-exterior threshold.  Thresholds are
integrated only after the spatial parameter count. -/
def exteriorAnchors (W : WindowSystem) (Z0 : ℕ) : Finset ℕ := by
  classical
  exact W.anchors.filter fun k =>
    ∃ T : ℝ, LongExteriorPair W Z0 (k, T)

private def defaultAffineLine : AffineLine where
  A := 0
  C := 0
  H := 1
  K := 0
  H_pos := by norm_num

private def HasPrimitiveOccurrenceLine (W : WindowSystem) (Z0 : ℕ)
    (p : GapWord) : Prop :=
  ∃ line : AffineLine,
    IsOccurrenceLine W Z0 p line ∧ Int.gcd line.H line.K = 1

/-- A deterministic primitive raw parameterization is chosen for each
frequent locked prefix.  Prefixes outside the locked family receive a harmless
default; the exterior-source construction proves that this branch is never
used. -/
private noncomputable def chosenExteriorLine (W : WindowSystem) (Z0 : ℕ)
    (p : GapWord) : AffineLine := by
  classical
  exact if h : HasPrimitiveOccurrenceLine W Z0 p then Classical.choose h
    else defaultAffineLine

private theorem chosenExteriorLine_spec (W : WindowSystem) (Z0 : ℕ)
    (p : GapWord) (h : HasPrimitiveOccurrenceLine W Z0 p) :
    IsOccurrenceLine W Z0 p (chosenExteriorLine W Z0 p) ∧
      Int.gcd (chosenExteriorLine W Z0 p).H
        (chosenExteriorLine W Z0 p).K = 1 := by
  rw [chosenExteriorLine, dif_pos h]
  exact Classical.choose_spec h

/-- A genuine long-exterior source relative to one deterministic occurrence
line chosen for each initial prefix.  The record, continuation, raw integer
parameter, and admissibility certificate all refer to the same anchor.  No
injectivity or fibre-size assertion is stored as input data. -/
structure ExteriorSource (W : WindowSystem) (Z0 : ℕ)
    (lineFor : GapWord → AffineLine) where
  anchor : ℕ
  threshold : ℝ
  offset_le : W.s ≤ anchor
  pair : LongExteriorPair W Z0 (anchor, threshold)
  before : GapWord
  continuation : GapWord
  after : GapWord
  record : FirstExitRecord
  word : GapWord
  parameter : ℤ
  occurrence :
    IsOccurrenceLine W Z0 (initialLongPrefix W anchor)
      (lineFor (initialLongPrefix W anchor))
  suffix_eq :
    actualPostPrefixGaps W anchor = before ++ continuation ++ after
  first_nonexterior : ∀ r < before.length,
    classifySlope
      (((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den (before.take r)).slope W.rational.eta.den) ≠
      .exterior
  exit_exterior :
    classifySlope
      (((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den before).slope W.rational.eta.den) = .exterior
  continuation_exterior :
    IsExteriorTrajectory W.rational.eta.den
      ((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den before) continuation
  record_eq : record = FirstExitRecord.ofFirstExit W.rational.eta.den
    (lineFor (initialLongPrefix W anchor)) before
  word_eq : word = postExitLongPrefix W continuation
  initial_parameter :
    let p := initialLongPrefix W anchor
    let line := lineFor p
    ((W.enumeration.a (anchor - W.s) + p.span : ℕ) : ℤ) =
        line.A + line.H * parameter ∧
      carryInt W.rational (W.enumeration.a (anchor - W.s) + p.span) =
        line.C + line.K * parameter
  admissible : parameter ∈ admissibleOriginalParameters
    W.rational.eta.den W.X
      ((lineFor (initialLongPrefix W anchor)).transformWord
        W.rational.eta.den before) word

namespace ExteriorSource

def baseLine {W : WindowSystem} {Z0 : ℕ} {lineFor : GapWord → AffineLine}
    (source : ExteriorSource W Z0 lineFor) : AffineLine :=
  lineFor (initialLongPrefix W source.anchor)

def canonicalLine {W : WindowSystem} {Z0 : ℕ}
    {lineFor : GapWord → AffineLine} (source : ExteriorSource W Z0 lineFor) :
    GeometricLine := source.baseLine.canonicalGeometricLine

def exitLine {W : WindowSystem} {Z0 : ℕ} {lineFor : GapWord → AffineLine}
    (source : ExteriorSource W Z0 lineFor) : AffineLine :=
  source.baseLine.transformWord W.rational.eta.den source.before

/-- The source code deliberately contains no threshold coordinate.  Its raw
integer parameter is retained exactly as required by the exterior count. -/
def code {W : WindowSystem} {Z0 : ℕ} {lineFor : GapWord → AffineLine}
    (source : ExteriorSource W Z0 lineFor) :
    GapWord × FirstExitRecord × GapWord × ℤ :=
  (initialLongPrefix W source.anchor, source.record, source.word,
    source.parameter)

/-- One source code determines the anchor.  This is proved from the absolute
post-prefix coordinate and strict monotonicity; it is not an assumed field of
`ExteriorSource`. -/
theorem code_injective_on_anchor {W : WindowSystem} {Z0 : ℕ}
    {lineFor : GapWord → AffineLine}
    (left right : ExteriorSource W Z0 lineFor)
    (hcode : left.code = right.code) : left.anchor = right.anchor := by
  simp only [code, Prod.mk.injEq] at hcode
  rcases hcode with ⟨hprefix, _hrecord, _hword, hparameter⟩
  have hline :
      lineFor (initialLongPrefix W left.anchor) =
        lineFor (initialLongPrefix W right.anchor) := congrArg lineFor hprefix
  have hcoordinateInt :
      ((W.enumeration.a (left.anchor - W.s) +
          (initialLongPrefix W left.anchor).span : ℕ) : ℤ) =
        ((W.enumeration.a (right.anchor - W.s) +
          (initialLongPrefix W right.anchor).span : ℕ) : ℤ) := by
    calc
      ((W.enumeration.a (left.anchor - W.s) +
          (initialLongPrefix W left.anchor).span : ℕ) : ℤ) =
          (lineFor (initialLongPrefix W left.anchor)).A +
            (lineFor (initialLongPrefix W left.anchor)).H * left.parameter :=
        left.initial_parameter.1
      _ = (lineFor (initialLongPrefix W right.anchor)).A +
            (lineFor (initialLongPrefix W right.anchor)).H * right.parameter := by
        rw [hline, hparameter]
      _ = ((W.enumeration.a (right.anchor - W.s) +
          (initialLongPrefix W right.anchor).span : ℕ) : ℤ) :=
        right.initial_parameter.1.symm
  have hcoordinate :
      W.enumeration.a (left.anchor - W.s) +
          (initialLongPrefix W left.anchor).span =
        W.enumeration.a (right.anchor - W.s) +
          (initialLongPrefix W right.anchor).span := by
    exact_mod_cast hcoordinateInt
  have hvalues : W.enumeration.a (left.anchor - W.s) =
      W.enumeration.a (right.anchor - W.s) := by
    rw [hprefix] at hcoordinate
    omega
  have hindices : left.anchor - W.s = right.anchor - W.s :=
    W.enumeration.strictMono.injective hvalues
  have hleftOffset := left.offset_le
  have hrightOffset := right.offset_le
  omega

/-- For one fixed prefix line, the first-exit record determines the actual
pre-exit word.  This is the reconstruction fact needed to put every source
with the same `(prefix, record)` into one parameter fibre. -/
theorem before_eq_of_prefix_record {W : WindowSystem} {Z0 : ℕ}
    {lineFor : GapWord → AffineLine}
    (hQ : 0 < W.rational.eta.den)
    (left right : ExteriorSource W Z0 lineFor)
    (hprefix : initialLongPrefix W left.anchor =
      initialLongPrefix W right.anchor)
    (hrecord : left.record = right.record) :
    left.before = right.before := by
  have hline :
      lineFor (initialLongPrefix W left.anchor) =
        lineFor (initialLongPrefix W right.anchor) := congrArg lineFor hprefix
  have hleftPrefix : left.before.IsPrefix
      (actualPostPrefixGaps W left.anchor) :=
    ⟨left.continuation ++ left.after, by
      simpa only [List.append_assoc] using left.suffix_eq.symm⟩
  have hrightPrefix : right.before.IsPrefix
      (actualPostPrefixGaps W right.anchor) :=
    ⟨right.continuation ++ right.after, by
      simpa only [List.append_assoc] using right.suffix_eq.symm⟩
  have hleftWord : IsFirstExitWord W.rational.eta.den
      (lineFor (initialLongPrefix W left.anchor)) left.before := by
    refine ⟨?_, left.first_nonexterior, left.exit_exterior⟩
    intro g hg
    exact actualPostPrefixGaps_positive W left.anchor g
      (hleftPrefix.mem hg)
  have hrightWord : IsFirstExitWord W.rational.eta.den
      (lineFor (initialLongPrefix W right.anchor)) right.before := by
    refine ⟨?_, right.first_nonexterior, right.exit_exterior⟩
    intro g hg
    exact actualPostPrefixGaps_positive W right.anchor g
      (hrightPrefix.mem hg)
  have hrecordWords :
      FirstExitRecord.ofFirstExit W.rational.eta.den
          (lineFor (initialLongPrefix W left.anchor)) left.before =
        FirstExitRecord.ofFirstExit W.rational.eta.den
          (lineFor (initialLongPrefix W right.anchor)) right.before := by
    calc
      _ = left.record := left.record_eq.symm
      _ = right.record := hrecord
      _ = _ := right.record_eq
  rw [← hline] at hrightWord hrecordWords
  exact FirstExitRecord.ofFirstExit_injective_on_firstExit
    W.rational.eta.den hQ
    (lineFor (initialLongPrefix W left.anchor)) left.before right.before
    hleftWord hrightWord hrecordWords

end ExteriorSource

private theorem exteriorHighAnchor_offset_le (W : WindowSystem) (Z0 k : ℕ)
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

private theorem supportGap_anchor_mem_rawWindowGapWord (W : WindowSystem)
    (Z0 k : ℕ) (hk : k ∈ highAnchors W Z0) :
    supportGap W.enumeration k ∈ W.rawWindowGapWord k := by
  have hsk := exteriorHighAnchor_offset_le W Z0 k hk
  rw [rawWindowGapWord_eq_enumerationGapWord W k hsk]
  unfold enumerationGapWord
  rw [List.mem_map]
  refine ⟨W.s, ?_, ?_⟩
  · simp [WindowSystem.m]
  · congr 1
    omega

private theorem enumeration_anchor_succ_le_three_mul_X
    (W : WindowSystem) (Z0 k G : ℕ) (hk : k ∈ highAnchors W Z0)
    (hgap : ∀ g ∈ W.rawWindowGapWord k, g ≤ G) (hGX : G ≤ W.X) :
    W.enumeration.a (k + 1) ≤ 3 * W.X := by
  have hkAnchor : k ∈ W.anchors := by
    classical
    rw [highAnchors, Finset.mem_filter] at hk
    exact hk.1
  have hkUpper : W.enumeration.a k ≤ 2 * W.X := by
    classical
    simpa [WindowSystem.anchors] using (Finset.mem_filter.mp hkAnchor).2.2
  have hlast := hgap (supportGap W.enumeration k)
    (supportGap_anchor_mem_rawWindowGapWord W Z0 k hk)
  have hmono := W.enumeration.strictMono (Nat.lt_succ_self k)
  have hendpoint :
      W.enumeration.a k + supportGap W.enumeration k =
        W.enumeration.a (k + 1) := by
    simp only [supportGap]
    exact Nat.add_sub_of_le hmono.le
  omega

/-- Propagate the raw integer parameter of a primitive occurrence line through
two genuine prefixes of the same anchored suffix.  This is the point where
the exterior count keeps the original parameter rather than replacing it by
a primitive reparameterization. -/
private theorem occurrence_parameter_admissible_actual_prefix
    (W : WindowSystem) (Z0 k Cgap : ℕ)
    (hk : k ∈ highAnchors W Z0) (line : AffineLine)
    (hoccurrence : IsOccurrenceLine W Z0 (initialLongPrefix W k) line)
    (before word : GapWord)
    (hbefore : before.IsPrefix (actualPostPrefixGaps W k))
    (hcombined : (before ++ word).IsPrefix (actualPostPrefixGaps W k))
    (hgap : ∀ g ∈ W.rawWindowGapWord k,
      g ≤ W.L + Cgap + 1)
    (hgapScale : W.L + Cgap + 1 ≤ W.X) :
    ∃ t : ℤ,
      (((W.enumeration.a (k - W.s) +
          (initialLongPrefix W k).span : ℕ) : ℤ) =
          line.A + line.H * t ∧
        carryInt W.rational
            (W.enumeration.a (k - W.s) +
              (initialLongPrefix W k).span) =
          line.C + line.K * t) ∧
      t ∈ admissibleOriginalParameters W.rational.eta.den W.X
        (line.transformWord W.rational.eta.den before) word := by
  let p := initialLongPrefix W k
  let i := k - W.s
  let j := i + p.length
  have hsk := exteriorHighAnchor_offset_le W Z0 k hk
  have hpword : p = enumerationGapWord W.enumeration i p.length :=
    initialPrefix_eq_enumerationGapWord W Z0 k p hk rfl
  have hpspan := enumerationGapWord_span W.enumeration i p.length
  rw [← hpword] at hpspan
  have hstart : W.enumeration.a i + p.span = W.enumeration.a j := by
    have hmono := W.enumeration.strictMono.monotone
      (show i ≤ i + p.length by omega)
    dsimp [j]
    omega
  have hcontains := hoccurrence k hk rfl
  rcases hcontains with ⟨t, hx, hr⟩
  have hxStart : (W.enumeration.a j : ℤ) = line.A + line.H * t := by
    rw [← hstart]
    exact hx
  have hrStart : carryInt W.rational (W.enumeration.a j) =
      line.C + line.K * t := by
    rw [← hstart]
    exact hr
  have hbeforeWord : before = enumerationGapWord W.enumeration j before.length := by
    simpa [i, p, j] using
      prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
        before hbefore
  have hcombinedWord : before ++ word =
      enumerationGapWord W.enumeration j (before ++ word).length := by
    simpa [i, p, j] using
      prefix_actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
        (before ++ word) hcombined
  have hbeforeParameter :=
    line.transformWord_parameter_enumerationGapWord
      W.rational.eta.den W.rational rfl W.enumeration j before.length t
        hxStart hrStart
  rw [← hbeforeWord] at hbeforeParameter
  have hcombinedParameter :=
    line.transformWord_parameter_enumerationGapWord
      W.rational.eta.den W.rational rfl W.enumeration j
        (before ++ word).length t hxStart hrStart
  rw [← hcombinedWord] at hcombinedParameter
  have hpLength : p.length ≤ W.m := by
    exact (GapWord.firstPrefixAbove_length_le (W.rawWindowGapWord k) _).trans
      (rawWindowGapWord_length_le W k)
  have hactual : actualPostPrefixGaps W k =
      enumerationGapWord W.enumeration j (W.m - p.length) := by
    simpa [i, p, j] using
      actualPostPrefixGaps_eq_enumerationGapWord W Z0 k hsk hk
  have hbeforeLength : before.length ≤ W.m - p.length := by
    have h := hbefore.length_le
    rw [hactual] at h
    simpa [enumerationGapWord] using h
  have hcombinedLength : (before ++ word).length ≤ W.m - p.length := by
    have h := hcombined.length_le
    rw [hactual] at h
    simpa [enumerationGapWord] using h
  have hbeforeIndex : j + before.length ≤ k + 1 := by
    dsimp [i, j]
    rw [WindowSystem.m] at hpLength hbeforeLength
    omega
  have hcombinedIndex : j + (before ++ word).length ≤ k + 1 := by
    dsimp [i, j]
    rw [WindowSystem.m] at hpLength hcombinedLength
    omega
  have hanchorEnd : W.enumeration.a (k + 1) ≤ 3 * W.X :=
    enumeration_anchor_succ_le_three_mul_X W Z0 k
      (W.L + Cgap + 1) hk hgap hgapScale
  have hbeforeEnd : W.enumeration.a (j + before.length) ≤ 3 * W.X :=
    (W.enumeration.strictMono.monotone hbeforeIndex).trans hanchorEnd
  have hcombinedEnd :
      W.enumeration.a (j + (before ++ word).length) ≤ 3 * W.X :=
    (W.enumeration.strictMono.monotone hcombinedIndex).trans hanchorEnd
  have admissibleAt (n : ℕ)
      (hn : W.enumeration.a n ≤ 3 * W.X) :
      InAdmissibleCarryRegion W.rational.eta.den W.X
        (W.enumeration.a n) (carryInt W.rational (W.enumeration.a n)) := by
    refine ⟨?_, ?_, (prop_carry W.rational).2.1 _,
      (prop_carry W.rational).2.2.1 _⟩
    · have hx : (0 : ℤ) ≤ W.enumeration.a n := by positivity
      have hX : (0 : ℤ) ≤ W.X := by positivity
      omega
    · exact_mod_cast hn
  refine ⟨t, ?_, ?_⟩
  · simpa [p, i] using And.intro hx hr
  · change InAdmissibleCarryRegion W.rational.eta.den W.X
        ((line.transformWord W.rational.eta.den before).A +
          (line.transformWord W.rational.eta.den before).H * t)
        ((line.transformWord W.rational.eta.den before).C +
          (line.transformWord W.rational.eta.den before).K * t) ∧
      InAdmissibleCarryRegion W.rational.eta.den W.X
        (((line.transformWord W.rational.eta.den before).transformWord
          W.rational.eta.den word).A +
          ((line.transformWord W.rational.eta.den before).transformWord
            W.rational.eta.den word).H * t)
        (((line.transformWord W.rational.eta.den before).transformWord
          W.rational.eta.den word).C +
          ((line.transformWord W.rational.eta.den before).transformWord
            W.rational.eta.den word).K * t)
    constructor
    · rw [← hbeforeParameter.1, ← hbeforeParameter.2]
      exact admissibleAt _ hbeforeEnd
    · rw [← AffineLine.transformWord_append,
        ← hcombinedParameter.1, ← hcombinedParameter.2]
      exact admissibleAt _ hcombinedEnd

private theorem continuation_sublist_actualPostPrefix
    (W : WindowSystem) (Z0 : ℕ) (e : WindowThreshold)
    (record : FirstExitRecord) (line : AffineLine)
    (continuation : GapWord)
    (hdescribe : FirstExitRecord.DescribesFirstExit W Z0 e record line continuation) :
    continuation <+ actualPostPrefixGaps W e.1 := by
  rcases hdescribe with
    ⟨base, finish, before, after, _hbase, hsuffix, _hbefore,
      _hcontinuation, _hexterior, _hfirst, _hrecord⟩
  rw [hsuffix]
  exact (List.sublist_append_right before continuation).trans
    (List.sublist_append_left (before ++ continuation) after)

/-- Bind a valid exterior signature back to one genuine anchor, replacing the
raw occurrence line by the deterministic primitive line for its prefix.  The
canonical-line equality transfers the first-exit dynamics, while the actual
support run preserves one original integer parameter. -/
private theorem validExteriorSignature_has_source
    (W : WindowSystem) (Z0 Cgap : ℕ)
    (hQ : 0 < W.rational.eta.den)
    (hcutoff : 1 < frequencyCutoff W)
    (e : WindowThreshold) (he : LongExteriorPair W Z0 e)
    (signature : ExteriorSignature)
    (hvalid : ValidExteriorSignature W Z0 Cgap e signature)
    (hprimitive : HasPrimitiveOccurrenceLine W Z0
      (initialLongPrefix W e.1))
    (hgap : ∀ g ∈ W.rawWindowGapWord e.1,
      g ≤ W.L + Cgap + 1)
    (hgapScale : W.L + Cgap + 1 ≤ W.X) :
    ∃ source : ExteriorSource W Z0 (chosenExteriorLine W Z0),
      source.anchor = e.1 ∧ source.record = signature.record ∧
        source.word = signature.word := by
  rcases hvalid with
    ⟨_hrecordValid, hwordPositive, exitLine, continuation,
      hdescribe, _hexteriorTrajectory, hwordEq⟩
  rcases hdescribe with
    ⟨base, _finish, before, after, hbase, hsuffix, hbeforeTrajectory,
      _hcontinuationTrajectory, hexitExterior, hfirst, hrecordEq⟩
  let p := initialLongPrefix W e.1
  have hchosen := chosenExteriorLine_spec W Z0 p hprimitive
  have hcanonical :
      (chosenExteriorLine W Z0 p).canonicalGeometricLine =
        base.canonicalGeometricLine := by
    apply occurrenceLines_canonical_eq_of_frequent W Z0 p hcutoff he.2.1
    · exact hchosen.1
    · exact hbase
  have hslope : (chosenExteriorLine W Z0 p).slope W.rational.eta.den =
      base.slope W.rational.eta.den := by
    calc
      (chosenExteriorLine W Z0 p).slope W.rational.eta.den =
          (chosenExteriorLine W Z0 p).canonicalGeometricLine.slope
            W.rational.eta.den :=
        (AffineLine.canonicalGeometricLine_slope W.rational.eta.den hQ _).symm
      _ = base.canonicalGeometricLine.slope W.rational.eta.den := by
        rw [hcanonical]
      _ = base.slope W.rational.eta.den :=
        AffineLine.canonicalGeometricLine_slope W.rational.eta.den hQ _
  have hchosenFirst : ∀ r < before.length,
      classifySlope
        (((chosenExteriorLine W Z0 p).transformWord W.rational.eta.den
          (before.take r)).slope W.rational.eta.den) ≠ .exterior := by
    intro r hr
    rcases hfirst r hr with ⟨state, hstate, hbaseNon⟩
    have hstateEq : state =
        base.transformWord W.rational.eta.den (before.take r) :=
      (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).1 hstate
    subst state
    rw [AffineLine.transformWord_slope_eq_of_slope_eq
      W.rational.eta.den hQ (chosenExteriorLine W Z0 p) base
      (before.take r) hslope]
    exact hbaseNon
  have hexitEq : exitLine =
      base.transformWord W.rational.eta.den before :=
    (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).1 hbeforeTrajectory
  have hchosenExit :
      classifySlope
        (((chosenExteriorLine W Z0 p).transformWord W.rational.eta.den
          before).slope W.rational.eta.den) = .exterior := by
    rw [AffineLine.transformWord_slope_eq_of_slope_eq
      W.rational.eta.den hQ (chosenExteriorLine W Z0 p) base before hslope,
      ← hexitEq]
    exact hexitExterior
  have hbeforePrefix : before.IsPrefix (actualPostPrefixGaps W e.1) :=
    ⟨continuation ++ after, by
      simpa only [List.append_assoc] using hsuffix.symm⟩
  have hcontinuationSub : continuation <+ actualPostPrefixGaps W e.1 := by
    rw [hsuffix]
    exact (List.sublist_append_right before continuation).trans
      (List.sublist_append_left (before ++ continuation) after)
  have hcontinuationPositive : continuation.Positive := by
    intro g hg
    exact actualPostPrefixGaps_positive W e.1 g
      (hcontinuationSub.subset hg)
  have hchosenContinuation : IsExteriorTrajectory W.rational.eta.den
      ((chosenExteriorLine W Z0 p).transformWord W.rational.eta.den before)
      continuation :=
    isExteriorTrajectory_of_positive W.rational.eta.den hQ _ _
      hcontinuationPositive hchosenExit
  have hrecordChosen : signature.record =
      FirstExitRecord.ofFirstExit W.rational.eta.den
        (chosenExteriorLine W Z0 p) before := by
    calc
      signature.record = FirstExitRecord.ofFirstExit W.rational.eta.den
          base before := hrecordEq
      _ = FirstExitRecord.ofFirstExit W.rational.eta.den
          (chosenExteriorLine W Z0 p) before :=
        FirstExitRecord.ofFirstExit_eq_of_slope_eq W.rational.eta.den hQ
          base (chosenExteriorLine W Z0 p) before hslope.symm
  have hwordPrefix : signature.word.IsPrefix continuation := by
    rw [hwordEq]
    exact GapWord.firstPrefixAbove_isPrefix _ _
  have hcombinedPrefix : (before ++ signature.word).IsPrefix
      (actualPostPrefixGaps W e.1) := by
    rcases hwordPrefix with ⟨tail, htail⟩
    refine ⟨tail ++ after, ?_⟩
    calc
      (before ++ signature.word) ++ (tail ++ after) =
          before ++ (signature.word ++ tail) ++ after := by
        simp only [List.append_assoc]
      _ = before ++ continuation ++ after := by rw [htail]
      _ = actualPostPrefixGaps W e.1 := hsuffix.symm
  have hkHigh : e.1 ∈ highAnchors W Z0 := by
    classical
    rw [highAnchors, Finset.mem_filter]
    exact ⟨he.1.1.1, e.2, he.1.1.2, he.1.2⟩
  have hparameter := occurrence_parameter_admissible_actual_prefix
    W Z0 e.1 Cgap hkHigh (chosenExteriorLine W Z0 p) hchosen.1
      before signature.word hbeforePrefix hcombinedPrefix hgap hgapScale
  rcases hparameter with ⟨parameter, hinitial, hadmissible⟩
  let source : ExteriorSource W Z0 (chosenExteriorLine W Z0) :=
    { anchor := e.1
      threshold := e.2
      offset_le := exteriorHighAnchor_offset_le W Z0 e.1 hkHigh
      pair := he
      before := before
      continuation := continuation
      after := after
      record := signature.record
      word := signature.word
      parameter := parameter
      occurrence := by simpa only [p] using hchosen.1
      suffix_eq := hsuffix
      first_nonexterior := by simpa only [p] using hchosenFirst
      exit_exterior := by simpa only [p] using hchosenExit
      continuation_exterior := by simpa only [p] using hchosenContinuation
      record_eq := by simpa only [p] using hrecordChosen
      word_eq := hwordEq
      initial_parameter := by simpa only [p] using hinitial
      admissible := by simpa only [p] using hadmissible }
  exact ⟨source, rfl, rfl, rfl⟩

/-- A finite source family is counted by initial prefix, deterministic
first-exit signature, and the surviving original integer parameter.  The
last coordinate is genuinely injective on each fixed prefix/signature fibre. -/
private theorem exteriorAnchors_card_le_of_sources
    (W : WindowSystem) (Z0 Cgap : ℕ)
    (hQ : 0 < W.rational.eta.den) (Coff : ℝ) (_hCoff : 0 < Coff)
    (hfixed : ∀ X : ℕ, ∀ line : AffineLine, ∀ word : GapWord,
      word.Positive →
      classifySlope (line.slope W.rational.eta.den) = .exterior →
      (admissibleOriginalParameters W.rational.eta.den X line word).Finite ∧
        ((admissibleOriginalParameters W.rational.eta.den X line word).ncard : ℝ) ≤
          1 + Coff * X * (2 : ℝ) ^ (-(word.span : ℤ)))
    (hsignaturesFinite : (exteriorSignatures W Z0 Cgap).Finite)
    (sourceFor : {k // k ∈ exteriorAnchors W Z0} →
      ExteriorSource W Z0 (chosenExteriorLine W Z0))
    (signatureFor : {k // k ∈ exteriorAnchors W Z0} → ExteriorSignature)
    (hanchor : ∀ k, (sourceFor k).anchor = k.1)
    (hsignature : ∀ k, signatureFor k ∈ exteriorSignatures W Z0 Cgap)
    (hrecord : ∀ k, (sourceFor k).record = (signatureFor k).record)
    (hword : ∀ k, (sourceFor k).word = (signatureFor k).word)
    (hsmall : ∀ k,
      Coff * W.X * (2 : ℝ) ^ (-((sourceFor k).word.span : ℤ)) ≤ 1) :
    (exteriorAnchors W Z0).card ≤
      (initialPrefixes W Z0).card *
        (exteriorSignatures W Z0 Cgap).ncard * 2 := by
  classical
  let Anchor := {k // k ∈ exteriorAnchors W Z0}
  let signatures : Finset ExteriorSignature :=
    hsignaturesFinite.toFinset
  let codes : Finset (GapWord × ExteriorSignature) :=
    (initialPrefixes W Z0).product signatures
  let fibre : GapWord × ExteriorSignature → Finset Anchor := fun code =>
    Finset.univ.filter fun k =>
      (initialLongPrefix W k.1, signatureFor k) = code
  have highOfAnchor (k : Anchor) : k.1 ∈ highAnchors W Z0 := by
    have hpair := (sourceFor k).pair
    rw [hanchor k] at hpair
    rw [highAnchors, Finset.mem_filter]
    exact ⟨hpair.1.1.1, (sourceFor k).threshold,
      hpair.1.1.2, hpair.1.2⟩
  have hprefixMem (k : Anchor) :
      initialLongPrefix W k.1 ∈ initialPrefixes W Z0 := by
    rw [initialPrefixes, Finset.mem_image]
    exact ⟨k.1, highOfAnchor k, rfl⟩
  have hcodes (k : Anchor) :
      (initialLongPrefix W k.1, signatureFor k) ∈ codes := by
    change (initialLongPrefix W k.1, signatureFor k) ∈
      (initialPrefixes W Z0).product signatures
    exact Finset.mem_product.mpr ⟨hprefixMem k, by
      simpa only [signatures, Set.Finite.mem_toFinset] using hsignature k⟩
  have hcover : (Finset.univ : Finset Anchor) ⊆ codes.biUnion fibre := by
    intro k _hk
    rw [Finset.mem_biUnion]
    refine ⟨(initialLongPrefix W k.1, signatureFor k), hcodes k, ?_⟩
    change k ∈ (Finset.univ : Finset Anchor).filter fun j =>
      (initialLongPrefix W j.1, signatureFor j) =
        (initialLongPrefix W k.1, signatureFor k)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hfibreCard : ∀ code ∈ codes, (fibre code).card ≤ 2 := by
    intro code hcode
    by_cases hempty : fibre code = ∅
    · simp [hempty]
    · obtain ⟨baseAnchor, hbaseAnchor⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      let parameters : Finset ℤ :=
        (fibre code).image fun k => (sourceFor k).parameter
      have hparameterInjective : Set.InjOn
          (fun k : Anchor => (sourceFor k).parameter) (fibre code) := by
        intro left hleft right hright hparameter
        have hleftCode := (Finset.mem_filter.mp hleft).2
        have hrightCode := (Finset.mem_filter.mp hright).2
        have hprefixValues : initialLongPrefix W left.1 =
            initialLongPrefix W right.1 := by
          exact congrArg Prod.fst (hleftCode.trans hrightCode.symm)
        have hsignatureValues : signatureFor left = signatureFor right := by
          exact congrArg Prod.snd (hleftCode.trans hrightCode.symm)
        have hsourcePrefix : initialLongPrefix W (sourceFor left).anchor =
            initialLongPrefix W (sourceFor right).anchor := by
          rw [hanchor left, hanchor right]
          exact hprefixValues
        have hsourceRecord : (sourceFor left).record =
            (sourceFor right).record := by
          rw [hrecord left, hrecord right, hsignatureValues]
        have hsourceWord : (sourceFor left).word =
            (sourceFor right).word := by
          rw [hword left, hword right, hsignatureValues]
        have hsourceCode : (sourceFor left).code = (sourceFor right).code := by
          simp only [ExteriorSource.code, Prod.mk.injEq]
          exact ⟨hsourcePrefix, hsourceRecord, hsourceWord, hparameter⟩
        have hanchors :=
          ExteriorSource.code_injective_on_anchor
            (sourceFor left) (sourceFor right) hsourceCode
        apply Subtype.ext
        rw [← hanchor left, ← hanchor right]
        exact hanchors
      have hparametersCard : parameters.card = (fibre code).card := by
        exact Finset.card_image_of_injOn hparameterInjective
      have hbaseCode := (Finset.mem_filter.mp hbaseAnchor).2
      have hparametersSubset : (parameters : Set ℤ) ⊆
          admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor baseAnchor).exitLine (sourceFor baseAnchor).word := by
        intro t ht
        change t ∈ (fibre code).image
          (fun k => (sourceFor k).parameter) at ht
        rw [Finset.mem_image] at ht
        rcases ht with ⟨anchor, hanchorFibre, rfl⟩
        have hanchorCode := (Finset.mem_filter.mp hanchorFibre).2
        have hprefixValues : initialLongPrefix W anchor.1 =
            initialLongPrefix W baseAnchor.1 := by
          exact congrArg Prod.fst (hanchorCode.trans hbaseCode.symm)
        have hsignatureValues : signatureFor anchor = signatureFor baseAnchor := by
          exact congrArg Prod.snd (hanchorCode.trans hbaseCode.symm)
        have hsourcePrefix : initialLongPrefix W (sourceFor anchor).anchor =
            initialLongPrefix W (sourceFor baseAnchor).anchor := by
          rw [hanchor anchor, hanchor baseAnchor]
          exact hprefixValues
        have hsourceRecord : (sourceFor anchor).record =
            (sourceFor baseAnchor).record := by
          rw [hrecord anchor, hrecord baseAnchor, hsignatureValues]
        have hsourceBefore := ExteriorSource.before_eq_of_prefix_record hQ
          (sourceFor anchor) (sourceFor baseAnchor) hsourcePrefix hsourceRecord
        have hsourceWord : (sourceFor anchor).word =
            (sourceFor baseAnchor).word := by
          rw [hword anchor, hword baseAnchor, hsignatureValues]
        have hbaseLine : (sourceFor anchor).baseLine =
            (sourceFor baseAnchor).baseLine := by
          simpa only [ExteriorSource.baseLine] using
            congrArg (chosenExteriorLine W Z0) hsourcePrefix
        have hexitLine : (sourceFor anchor).exitLine =
            (sourceFor baseAnchor).exitLine := by
          simp only [ExteriorSource.exitLine]
          rw [hbaseLine, hsourceBefore]
        have hadmissible := (sourceFor anchor).admissible
        change (sourceFor anchor).parameter ∈
          admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor anchor).exitLine (sourceFor anchor).word at hadmissible
        rw [hexitLine, hsourceWord] at hadmissible
        exact hadmissible
      have hbaseWordPositive : (sourceFor baseAnchor).word.Positive := by
        have hmem := hsignature baseAnchor
        rcases hmem with ⟨_e, _he, hvalid⟩
        rw [hword baseAnchor]
        exact hvalid.2.1
      have hfixedBase := hfixed W.X (sourceFor baseAnchor).exitLine
        (sourceFor baseAnchor).word hbaseWordPositive
          (sourceFor baseAnchor).exit_exterior
      have hparameterBound :
          (admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor baseAnchor).exitLine
              (sourceFor baseAnchor).word).ncard ≤ 2 := by
        have hreal :
            ((admissibleOriginalParameters W.rational.eta.den W.X
              (sourceFor baseAnchor).exitLine
                (sourceFor baseAnchor).word).ncard : ℝ) ≤ 2 :=
          hfixedBase.2.trans (by nlinarith [hsmall baseAnchor])
        exact_mod_cast hreal
      have hparametersLe : parameters.card ≤
          (admissibleOriginalParameters W.rational.eta.den W.X
            (sourceFor baseAnchor).exitLine
              (sourceFor baseAnchor).word).ncard := by
        have hsubsetFinset : parameters ⊆ hfixedBase.1.toFinset := by
          intro t ht
          rw [Set.Finite.mem_toFinset]
          exact hparametersSubset ht
        simpa [Set.ncard_eq_toFinset_card _ hfixedBase.1] using
          Finset.card_le_card hsubsetFinset
      rw [← hparametersCard]
      exact hparametersLe.trans hparameterBound
  have hcardCover : (Finset.univ : Finset Anchor).card ≤
      ∑ code ∈ codes, (fibre code).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsumBound : (∑ code ∈ codes, (fibre code).card) ≤ codes.card * 2 := by
    calc
      (∑ code ∈ codes, (fibre code).card) ≤ ∑ _code ∈ codes, 2 := by
        exact Finset.sum_le_sum fun code hcode => hfibreCard code hcode
      _ = codes.card * 2 := by simp
  have hanchorCard : (exteriorAnchors W Z0).card =
      (Finset.univ : Finset Anchor).card := by
    simp [Anchor]
  have hcodesCard : codes.card =
      (initialPrefixes W Z0).card *
        (exteriorSignatures W Z0 Cgap).ncard := by
    dsimp [codes]
    rw [Finset.card_product]
    simp only [signatures, Set.ncard_eq_toFinset_card _ hsignaturesFinite]
  calc
    (exteriorAnchors W Z0).card =
        (Finset.univ : Finset Anchor).card := hanchorCard
    _ ≤ ∑ code ∈ codes, (fibre code).card := hcardCover
    _ ≤ codes.card * 2 := hsumBound
    _ = (initialPrefixes W Z0).card *
        (exteriorSignatures W Z0 Cgap).ncard * 2 := by rw [hcodesCard]

/-- Every signature is contained in a denominator-uniform finite record ×
word box. -/
theorem exteriorSignatures_finite_and_ncard_le
    (context : FixedScaleContext) (gap : GapParams context.Q)
    (F : ScaleFamily) (hF : F.MatchesContext context) (Z0 : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      (exteriorSignatures (F.system L) Z0 gap.Cgap).Finite ∧
      ((exteriorSignatures (F.system L) Z0 gap.Cgap).ncard : ℕ) ≤
        (((F.system L).m + 1) * 4 * ((F.system L).m + 1) *
            ((F.system L).L + gap.Cgap + 2)) *
          (∑ r ∈ Finset.Icc 0 (F.system L).m,
            (exteriorWordBound (F.system L) gap.Cgap).choose r) := by
  filter_upwards [eventually_rawWindowGap_le context gap F hF] with L hgap
  let W := F.system L
  let signatures := exteriorSignatures W Z0 gap.Cgap
  let words : Set GapWord :=
    {word | word.Positive ∧
      word.span ≤ exteriorWordBound W gap.Cgap ∧ word.length ≤ W.m}
  have hsignatureMaps : Set.MapsTo
      (fun signature : ExteriorSignature => (signature.record, signature.word))
      signatures (validFirstExitRecords W.m W.L gap.Cgap ×ˢ words) := by
    intro signature hsignature
    rcases hsignature with ⟨e, he, hvalid⟩
    rcases hvalid with
      ⟨hrecord, hwordPositive, line, continuation, hdescribe,
        _hexterior, hword⟩
    have heAnchor : e.1 ∈ W.anchors := he.1.1.1
    have hcontinuationSub : continuation <+ actualPostPrefixGaps W e.1 :=
      continuation_sublist_actualPostPrefix W Z0 e signature.record line
        continuation hdescribe
    have hwordPrefix : signature.word.IsPrefix continuation := by
      rw [hword]
      exact GapWord.firstPrefixAbove_isPrefix _ _
    have hwordSubActual : signature.word <+ actualPostPrefixGaps W e.1 :=
      hwordPrefix.sublist.trans hcontinuationSub
    have hlength : signature.word.length ≤ W.m :=
      hwordSubActual.length_le.trans (actualPostPrefixGaps_length_le W e.1)
    have hwordGap : ∀ g ∈ signature.word, g ≤ W.L + gap.Cgap + 1 := by
      intro g hg
      have hgActual : g ∈ actualPostPrefixGaps W e.1 :=
        hwordSubActual.subset hg
      have hgRaw : g ∈ W.rawWindowGapWord e.1 :=
        List.mem_of_mem_drop hgActual
      simpa [W, F.level_eq] using hgap e.1 heAnchor g hgRaw
    have hspan : signature.word.span ≤ exteriorWordBound W gap.Cgap := by
      rw [hword]
      simpa [postExitLongPrefix, exteriorWordBound, Nat.add_assoc] using
        GapWord.span_firstPrefixAbove_le_add continuation
          (Nat.floor (W.structural.Gamma * W.L))
          (W.L + gap.Cgap + 1) (by
            intro g hg
            have hgActual : g ∈ actualPostPrefixGaps W e.1 :=
              hcontinuationSub.subset hg
            have hgRaw : g ∈ W.rawWindowGapWord e.1 :=
              List.mem_of_mem_drop hgActual
            simpa [W, F.level_eq] using hgap e.1 heAnchor g hgRaw)
    exact ⟨hrecord, hwordPositive, hspan, hlength⟩
  have hrecordFinite :=
    (validFirstExitRecords_finite_and_ncard_le W.m W.L gap.Cgap).1
  have hwordsFinite : words.Finite := by
    apply (positiveGapWords_bounded_finite
      (exteriorWordBound W gap.Cgap) W.m).subset
    intro word hword
    exact hword
  have htargetFinite :
      (validFirstExitRecords W.m W.L gap.Cgap ×ˢ words).Finite :=
    hrecordFinite.prod hwordsFinite
  have hsignatureImageFinite :
      ((fun signature : ExteriorSignature =>
          (signature.record, signature.word)) '' signatures).Finite := by
    apply htargetFinite.subset
    rintro _ ⟨signature, hsignature, rfl⟩
    exact hsignatureMaps hsignature
  have hencodeInjective : Function.Injective
      (fun signature : ExteriorSignature =>
        (signature.record, signature.word)) := by
    intro a b h
    cases a
    cases b
    simp_all
  have hsignaturesFinite : signatures.Finite :=
    Set.Finite.of_finite_image hsignatureImageFinite hencodeInjective.injOn
  have hwordsCard : words.ncard ≤
      ∑ r ∈ Finset.Icc 0 W.m,
        (exteriorWordBound W gap.Cgap).choose r := by
    have hfinset := positiveGapWords_card_le_compositions
      hwordsFinite.toFinset (exteriorWordBound W gap.Cgap) W.m
      (by
        intro word hword g hg
        have hw : word ∈ words := by
          simpa only [Set.Finite.mem_toFinset] using hword
        exact hw.1 g hg)
      (by
        intro word hword
        have hw : word ∈ words := by
          simpa only [Set.Finite.mem_toFinset] using hword
        exact hw.2.1)
      (by
        intro word hword
        have hw : word ∈ words := by
          simpa only [Set.Finite.mem_toFinset] using hword
        exact hw.2.2)
    simpa [Set.ncard_eq_toFinset_card words hwordsFinite] using hfinset
  have hsignatureCard : signatures.ncard ≤
      (validFirstExitRecords W.m W.L gap.Cgap).ncard * words.ncard := by
    calc
      signatures.ncard =
          ((fun signature : ExteriorSignature =>
            (signature.record, signature.word)) '' signatures).ncard := by
        symm
        exact Set.ncard_image_of_injective _ hencodeInjective
      _ ≤ (validFirstExitRecords W.m W.L gap.Cgap ×ˢ words).ncard :=
        Set.ncard_le_ncard (by
          rintro _ ⟨signature, hsignature, rfl⟩
          exact hsignatureMaps hsignature) htargetFinite
      _ = (validFirstExitRecords W.m W.L gap.Cgap).ncard * words.ncard :=
        Set.ncard_prod
  refine ⟨hsignaturesFinite, ?_⟩
  calc
    signatures.ncard ≤
        (validFirstExitRecords W.m W.L gap.Cgap).ncard * words.ncard :=
      hsignatureCard
    _ ≤ (((W.m + 1) * 4 * (W.m + 1) * (W.L + gap.Cgap + 2))) *
          (∑ r ∈ Finset.Icc 0 W.m,
            (exteriorWordBound W gap.Cgap).choose r) := by
      exact Nat.mul_le_mul
        (validFirstExitRecords_finite_and_ncard_le W.m W.L gap.Cgap).2
        hwordsCard

private theorem longExteriorPair_has_signature
    (context : FixedScaleContext) (gap : GapParams context.Q)
    (F : ScaleFamily) (hF : F.MatchesContext context) (Z0 L : ℕ)
    (hcutoff : 4 * context.structural.Gamma / context.entropy.kappa < Z0)
    (hgap : ∀ k : ℕ, k ∈ (F.system L).anchors →
      ∀ g ∈ (F.system L).rawWindowGapWord k,
        g ≤ L + gap.Cgap + 1)
    (e : WindowThreshold) (he : LongExteriorPair (F.system L) Z0 e) :
    ∃ signature : ExteriorSignature,
      signature ∈ exteriorSignatures (F.system L) Z0 gap.Cgap ∧
      ValidExteriorSignature (F.system L) Z0 gap.Cgap e signature ∧
      (F.system L).structural.Gamma * L < signature.word.span ∧
      (signature.word.span : ℝ) ≤
        ((F.system L).structural.Gamma + 1) * L + (gap.Cgap + 1) ∧
      signature.word.length ≤ (F.system L).m := by
  let W := F.system L
  rcases he.2.2.2 with
    ⟨line, continuation, hactual, hexteriorTrajectory, hspanContinuation⟩
  rcases hactual with
    ⟨base, finish, before, after, hbase, hsuffix, hbefore, hfirst,
      hlineExterior, hcontinuation⟩
  let record := FirstExitRecord.ofFirstExit W.rational.eta.den base before
  let word := postExitLongPrefix W continuation
  let signature : ExteriorSignature := ⟨record, word⟩
  have heAnchor : e.1 ∈ W.anchors := he.1.1.1
  have hactualPositive := actualPostPrefixGaps_positive W e.1
  have hbeforePrefix : before.IsPrefix (actualPostPrefixGaps W e.1) := by
    exact ⟨continuation ++ after, by simpa [List.append_assoc] using hsuffix.symm⟩
  have hcontinuationSub : continuation <+ actualPostPrefixGaps W e.1 := by
    rw [hsuffix]
    exact (List.sublist_append_right before continuation).trans
      (List.sublist_append_left (before ++ continuation) after)
  have hbeforePositive : before.Positive := by
    intro g hg
    exact hactualPositive g (hbeforePrefix.mem hg)
  have hcontinuationPositive : continuation.Positive := by
    intro g hg
    exact hactualPositive g (hcontinuationSub.subset hg)
  have hbeforeLength : before.length ≤ W.m :=
    hbeforePrefix.length_le.trans (actualPostPrefixGaps_length_le W e.1)
  have hbeforeGap : ∀ g ∈ before, g ≤ W.L + gap.Cgap + 1 := by
    intro g hg
    simpa [W, F.level_eq] using hgap e.1 heAnchor g
      (List.mem_of_mem_drop (hbeforePrefix.subset hg))
  have hrecordValid : record.Valid W.m W.L gap.Cgap := by
    apply FirstExitRecord.ofFirstExit_valid W.rational.eta.den W.m W.L
      gap.Cgap
    · have hden : W.rational.eta.den = context.Q := by
        change (F.system L).rational.eta.den = context.Q
        rw [F.rational_eq, hF.1]
      simpa [hden] using context.Q_pos
    · exact hbefore
    · exact hlineExterior
    · exact hbeforeLength
    · exact hbeforePositive
    · exact hbeforeGap
  have hdescribe : FirstExitRecord.DescribesFirstExit W Z0 e record line continuation := by
    refine ⟨base, finish, before, after, hbase, hsuffix, hbefore,
      hcontinuation, hlineExterior, ?_, rfl⟩
    intro r hr
    let state := base.transformWord W.rational.eta.den (before.take r)
    have hstate : SharedGapTrajectory W.rational.eta.den base
        (before.take r) state :=
      (sharedGapTrajectory_iff_eq_transformWord _ _ _ _).2 rfl
    exact ⟨state, hstate, hfirst r hr state hstate⟩
  have hsignatureValid : ValidExteriorSignature W Z0 gap.Cgap e signature := by
    refine ⟨hrecordValid, ?_, line, continuation, hdescribe,
      hexteriorTrajectory, rfl⟩
    exact GapWord.firstPrefixAbove_positive continuation _ hcontinuationPositive
  have hmLower : context.entropy.kappa * (L : ℝ) < (W.m : ℝ) := by
    have hs : W.s = Nat.floor (context.entropy.kappa * (L : ℝ)) := by
      change (F.system L).s = _
      rw [F.offset_eq, hF.2.2.1]
    rw [WindowSystem.m, hs]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (context.entropy.kappa * (L : ℝ)))
  have hZpos : (0 : ℝ) < Z0 := by
    have hquotPos : 0 <
        4 * context.structural.Gamma / context.entropy.kappa := by
      have hGamma : 0 < context.structural.Gamma :=
        lt_trans (by norm_num) context.structural.Gamma_gt
      exact div_pos (mul_pos (by norm_num) hGamma) context.entropy.kappa_pos
    exact hquotPos.trans hcutoff
  have hcoefficient :
      4 * context.structural.Gamma < context.entropy.kappa * (Z0 : ℝ) := by
    have := (div_lt_iff₀ context.entropy.kappa_pos).mp hcutoff
    simpa [mul_comm] using this
  have hscale :
      4 * context.structural.Gamma * (L : ℝ) < (W.m : ℝ) * Z0 := by
    have hleft :
        4 * context.structural.Gamma * (L : ℝ) ≤
          (context.entropy.kappa * (Z0 : ℝ)) * L := by
      exact mul_le_mul_of_nonneg_right hcoefficient.le (Nat.cast_nonneg L)
    have hright :
        (context.entropy.kappa * (Z0 : ℝ)) * L <
          (W.m : ℝ) * Z0 := by
      have := mul_lt_mul_of_pos_right hmLower hZpos
      nlinarith
    exact hleft.trans_lt hright
  have hlarge : (W.m : ℝ) * Z0 < W.excess e := by
    simpa only [Set.mem_ofPred_eq] using he.1.2
  have hcontinuationCross :
      W.structural.Gamma * (L : ℝ) < (continuation.span : ℝ) := by
    have hstruct : W.structural = context.structural := by
      change (F.system L).structural = context.structural
      rw [F.structural_eq, hF.2.1]
    rw [hstruct]
    have hquarter :
        context.structural.Gamma * (L : ℝ) <
          (W.m : ℝ) * Z0 / 4 := by nlinarith
    have hdiv : (W.m : ℝ) * Z0 / 4 < W.excess e / 4 :=
      (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2 hlarge
    exact hquarter.trans (hdiv.trans_le hspanContinuation)
  have hfloorCross :
      Nat.floor (W.structural.Gamma * W.L) < continuation.span := by
    have hnonneg : 0 ≤ W.structural.Gamma * (W.L : ℝ) := by
      have hGamma : 0 < W.structural.Gamma :=
        lt_trans (by norm_num) W.structural.Gamma_gt
      positivity
    have hcross : W.structural.Gamma * (W.L : ℝ) <
        (continuation.span : ℝ) := by
      simpa [W, F.level_eq] using hcontinuationCross
    exact_mod_cast (lt_of_le_of_lt (Nat.floor_le hnonneg) hcross)
  have hwordLowerNat :
      Nat.floor (W.structural.Gamma * W.L) < word.span := by
    exact GapWord.lt_span_firstPrefixAbove_of_lt_span _ _ hfloorCross
  have hwordLower : W.structural.Gamma * (L : ℝ) < (word.span : ℝ) := by
    have hlevel : W.L = L := F.level_eq L
    rw [← hlevel]
    have hnext := Nat.lt_floor_add_one (W.structural.Gamma * (W.L : ℝ))
    have hsucc : Nat.floor (W.structural.Gamma * W.L) + 1 ≤ word.span :=
      Nat.succ_le_iff.mpr hwordLowerNat
    exact hnext.trans_le (by exact_mod_cast hsucc)
  have hcontinuationGap : ∀ g ∈ continuation, g ≤ W.L + gap.Cgap + 1 := by
    intro g hg
    simpa [W, F.level_eq] using hgap e.1 heAnchor g
      (List.mem_of_mem_drop (hcontinuationSub.subset hg))
  have hwordUpperNat : word.span ≤
      Nat.floor (W.structural.Gamma * W.L) + (W.L + gap.Cgap + 1) := by
    exact GapWord.span_firstPrefixAbove_le_add continuation _ _ hcontinuationGap
  have hwordUpper : (word.span : ℝ) ≤
      (W.structural.Gamma + 1) * L + (gap.Cgap + 1) := by
    have hGamma : 0 < W.structural.Gamma :=
      lt_trans (by norm_num) W.structural.Gamma_gt
    have hnonneg : 0 ≤ W.structural.Gamma * (W.L : ℝ) := by positivity
    have hfloor := Nat.floor_le hnonneg
    have hcast : (word.span : ℝ) ≤
        (Nat.floor (W.structural.Gamma * W.L) : ℝ) +
          ((W.L : ℝ) + gap.Cgap + 1) := by
      exact_mod_cast hwordUpperNat
    rw [F.level_eq] at hfloor hcast
    nlinarith
  have hwordLength : word.length ≤ W.m := by
    exact (GapWord.firstPrefixAbove_length_le continuation _).trans
      (hcontinuationSub.length_le.trans (actualPostPrefixGaps_length_le W e.1))
  refine ⟨signature, ⟨e, he, hsignatureValid⟩, hsignatureValid,
    ?_, hwordUpper, hwordLength⟩
  simpa [signature, W] using hwordLower

private def exteriorCountSpanCap (context : FixedScaleContext)
    (gap : GapParams context.Q) (L : ℕ) : ℕ :=
  Nat.floor (context.structural.Gamma * (L : ℝ)) + L + gap.Cgap + 1

private def exteriorCountAlpha (context : FixedScaleContext)
    (gap : GapParams context.Q) (L : ℕ) : ℝ :=
  ((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
    ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)

/-- The absolute entropy discrepancy and the degree-six polynomial loss,
both measured as exponents of `X = 2^L`. -/
private def exteriorCountError (context : FixedScaleContext)
    (gap : GapParams context.Q) (L : ℕ) : ℝ :=
  if L = 0 then 0 else
    |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
          binaryEntropy (exteriorCountAlpha context gap L) -
        exteriorPrefixExponent context.entropy| +
      6 * Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
        ((L : ℝ) * Real.log 2)

private theorem exteriorCountError_tendsto_zero
    (context : FixedScaleContext) (gap : GapParams context.Q) :
    Tendsto (exteriorCountError context gap) atTop (𝓝 0) := by
  let A : ℝ := context.structural.Gamma + 1
  have hGamma : 0 < context.structural.Gamma :=
    lt_trans (by norm_num) context.structural.Gamma_gt
  have hA : 0 < A := by dsimp [A]; linarith
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hgammaFloor : Tendsto
      (fun L : ℕ =>
        (Nat.floor (context.structural.Gamma * (L : ℝ)) : ℝ) / (L : ℝ))
      atTop (𝓝 context.structural.Gamma) := by
    simpa using tendsto_natFloor_affine_div context.structural.Gamma 0
      hGamma (le_refl 0)
  have hconstDiv : Tendsto
      (fun L : ℕ => ((gap.Cgap + 6 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnatTop
  have hcap : Tendsto
      (fun L : ℕ =>
        ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ))
      atTop (𝓝 A) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hsum : Tendsto
        (fun L : ℕ =>
          (Nat.floor (context.structural.Gamma * (L : ℝ)) : ℝ) /
              (L : ℝ) + 1 + ((gap.Cgap + 6 : ℕ) : ℝ) / (L : ℝ))
        atTop (𝓝 A) := by
      simpa [A] using (hgammaFloor.add hone).add hconstDiv
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [exteriorCountSpanCap, A]
    push_cast
    field_simp [hL0]
    ring
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
  have halpha : Tendsto (exteriorCountAlpha context gap) atTop
      (𝓝 (context.entropy.kappa / A)) := by
    have hquot := hnum.div hcap hA0
    apply hquot.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    dsimp [exteriorCountAlpha]
    field_simp
  have hentropy : Tendsto
      (fun L => binaryEntropy (exteriorCountAlpha context gap L))
      atTop (𝓝 (binaryEntropy (context.entropy.kappa / A))) :=
    binaryEntropy_continuous.continuousAt.tendsto.comp halpha
  have hmain : Tendsto
      (fun L : ℕ =>
        ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ) *
          binaryEntropy (exteriorCountAlpha context gap L))
      atTop (𝓝 (exteriorPrefixExponent context.entropy)) := by
    have := hcap.mul hentropy
    rw [exteriorPrefixExponent, context.entropy_structural]
    simpa only [A] using this
  have habs : Tendsto
      (fun L : ℕ =>
        |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy|)
      atTop (𝓝 0) := by
    have hconst : Tendsto
        (fun _ : ℕ => exteriorPrefixExponent context.entropy)
        atTop (𝓝 (exteriorPrefixExponent context.entropy)) :=
      tendsto_const_nhds
    simpa using (hmain.sub hconst).abs
  have hcapNatTop : Tendsto
      (fun L : ℕ => exteriorCountSpanCap context gap L + 5) atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun L => by dsimp [exteriorCountSpanCap]; omega)
      (tendsto_id : Tendsto (fun L : ℕ => L) atTop atTop)
  have hcapRealTop : Tendsto
      (fun L : ℕ => ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ))
      atTop atTop := hnatTop.comp hcapNatTop
  have hlogOverCap : Tendsto
      (fun L : ℕ =>
        Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcapRealTop
  have hlogOverL : Tendsto
      (fun L : ℕ =>
        Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          (L : ℝ))
      atTop (𝓝 0) := by
    have hprod := hlogOverCap.mul hcap
    have hprod' : Tendsto
        (fun L : ℕ =>
          Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
              (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) *
            (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    have hcapPos : (0 : ℝ) <
        ((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) := by positivity
    field_simp [hL0, ne_of_gt hcapPos]
  have hpoly : Tendsto
      (fun L : ℕ =>
        6 * Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hsimple : Tendsto
        (fun L : ℕ =>
          (6 * (Real.log
            (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
              (L : ℝ))) / Real.log 2)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hlogOverL).div_const (Real.log 2)
    apply hsimple.congr'
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    field_simp [hL0, hlog2]
  have hsum : Tendsto
      (fun L : ℕ =>
        |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy| +
        6 * Real.log (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
          ((L : ℝ) * Real.log 2))
      atTop (𝓝 0) := by simpa using habs.add hpoly
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  simp only [exteriorCountError, Nat.ne_of_gt hL, if_false]

/-- Paper label: `lem:seconddeep` (Section 7).  The fixed additive word
constant and a denominator-level cutoff are chosen before the support.  For
each larger cutoff the subexponential counting error is shared by every
compatible family. -/
theorem lem_seconddeep (context : FixedScaleContext)
    (gap : GapParams context.Q) :
    ∃ CQ : ℝ, 0 < CQ ∧ ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ F : ScaleFamily, F.MatchesContext context →
        ∀ᶠ L : ℕ in atTop,
            (exteriorSignatures (F.system L) Z0 gap.Cgap).Finite ∧
            ((exteriorSignatures (F.system L) Z0 gap.Cgap).ncard : ℝ) ≤
            Real.rpow (F.system L).X
              (exteriorPrefixExponent (F.system L).entropy + error L) ∧
          ∀ e : WindowThreshold,
            LongExteriorPair (F.system L) Z0 e →
            ∃ signature : ExteriorSignature,
                signature ∈ exteriorSignatures (F.system L) Z0 gap.Cgap ∧
              (F.system L).structural.Gamma * L < signature.word.span ∧
              (signature.word.span : ℝ) ≤
                ((F.system L).structural.Gamma + 1) * L + CQ ∧
              signature.word.length ≤ (F.system L).m := by
  classical
  let CQ : ℝ := gap.Cgap + 1
  let Zmin := Nat.ceil
    (4 * context.structural.Gamma / context.entropy.kappa) + 1
  refine ⟨CQ, by dsimp [CQ]; positivity, Zmin, ?_⟩
  intro Z0 hZ0
  refine ⟨exteriorCountError context gap,
    exteriorCountError_tendsto_zero context gap, ?_⟩
  intro F hF
  have hcutoff :
      4 * context.structural.Gamma / context.entropy.kappa < (Z0 : ℝ) := by
    have hceil :
        4 * context.structural.Gamma / context.entropy.kappa ≤
          (Nat.ceil (4 * context.structural.Gamma /
            context.entropy.kappa) : ℝ) :=
      Nat.le_ceil _
    have hZcast :
        Nat.ceil (4 * context.structural.Gamma / context.entropy.kappa) + 1 ≤
          Z0 := by simpa [Zmin] using hZ0
    exact hceil.trans_lt (by exact_mod_cast hZcast)
  filter_upwards [exteriorSignatures_finite_and_ncard_le context gap F hF Z0,
    eventually_rawWindowGap_le context gap F hF,
    eventually_ge_atTop 1] with L hsignatureCount hgap hL
  let W := F.system L
  let H := exteriorCountSpanCap context gap L
  let B := H + 5
  have hstruct : W.structural = context.structural := by
    change (F.system L).structural = context.structural
    rw [F.structural_eq, hF.2.1]
  have hentropy : W.entropy = context.entropy := by
    change (F.system L).entropy = context.entropy
    rw [F.entropy_eq, hF.2.2.1]
  have hlevel : W.L = L := F.level_eq L
  have hm : W.m =
      Nat.floor (context.entropy.kappa * (L : ℝ)) + 1 := by
    change (F.system L).s + 1 = _
    rw [F.offset_eq, hF.2.2.1]
  have hnumEq : W.m + 1 =
      Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 := by omega
  have hwordBound : exteriorWordBound W gap.Cgap = H := by
    simp only [exteriorWordBound, H, exteriorCountSpanCap, hstruct, hlevel]
  have hGamma : 0 < context.structural.Gamma :=
    lt_trans (by norm_num) context.structural.Gamma_gt
  have hkappaA :
      2 * context.entropy.kappa ≤ context.structural.Gamma + 1 := by
    have hh := context.entropy.kappa_exterior_half
    rw [context.entropy_structural] at hh
    have hA : 0 < context.structural.Gamma + 1 := by linarith
    have := (div_le_iff₀ hA).mp hh
    nlinarith
  have hkFloor :
      (Nat.floor (context.entropy.kappa * (L : ℝ)) : ℝ) ≤
        context.entropy.kappa * L := by
    exact Nat.floor_le
      (mul_nonneg context.entropy.kappa_pos.le (Nat.cast_nonneg L))
  have hGammaFloor :
      context.structural.Gamma * (L : ℝ) - 1 <
        (Nat.floor (context.structural.Gamma * (L : ℝ)) : ℝ) := by
    have := Nat.lt_floor_add_one (context.structural.Gamma * (L : ℝ))
    linarith
  have htwice : 2 * ((W.m + 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
    rw [hm]
    dsimp [B, H, exteriorCountSpanCap]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hkappaA (Nat.cast_nonneg L)]
  have hB : 2 ≤ B := by dsimp [B]; omega
  have halphaPos : 0 < exteriorCountAlpha context gap L := by
    dsimp [exteriorCountAlpha, B, H]
    positivity
  have halphaHalf : exteriorCountAlpha context gap L ≤ 1 / 2 := by
    have hBpos : (0 : ℝ) < B := by positivity
    change
      (((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
          (B : ℝ)) ≤ 1 / 2
    rw [← hnumEq]
    apply (div_le_iff₀ hBpos).2
    nlinarith
  have hr : ((W.m + 1 : ℕ) : ℝ) ≤
      exteriorCountAlpha context gap L * (B : ℝ) := by
    change ((W.m + 1 : ℕ) : ℝ) ≤
      ((((Nat.floor (context.entropy.kappa * (L : ℝ)) + 2 : ℕ) : ℝ) /
        (B : ℝ)) * (B : ℝ))
    rw [← hnumEq]
    have hB0 : (B : ℝ) ≠ 0 := by positivity
    field_simp [hB0]
    norm_num
  have hcomposition := lem_composition_entropy B (W.m + 1)
    (exteriorCountAlpha context gap L) hB halphaPos halphaHalf hr
  have hsumMono :
      (∑ r ∈ Finset.Icc 0 W.m,
          (exteriorWordBound W gap.Cgap).choose r) ≤
        ∑ r ∈ Finset.Icc 0 W.m, (B - 1).choose r := by
    apply Finset.sum_le_sum
    intro r hrmem
    apply Nat.choose_le_choose
    rw [hwordBound]
    dsimp [B]
    omega
  have hsumReal :
      ((∑ r ∈ Finset.Icc 0 W.m,
          (exteriorWordBound W gap.Cgap).choose r : ℕ) : ℝ) ≤
        (B : ℝ) ^ 2 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by
    calc
      ((∑ r ∈ Finset.Icc 0 W.m,
          (exteriorWordBound W gap.Cgap).choose r : ℕ) : ℝ) ≤
          ((∑ r ∈ Finset.Icc 0 W.m, (B - 1).choose r : ℕ) : ℝ) := by
        exact_mod_cast hsumMono
      _ = ((∑ q ∈ Finset.Icc 1 (W.m + 1),
          (B - 1).choose (q - 1) : ℕ) : ℝ) := by
        rw [sum_choose_Icc_zero_eq_shift]
      _ ≤ (B : ℝ) ^ 2 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by
        simpa only [Nat.add_sub_cancel] using hcomposition
  have hpolyNat :
      (W.m + 1) * 4 * (W.m + 1) * (W.L + gap.Cgap + 2) ≤
        B ^ 4 := by
    have hmBReal : ((W.m + 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
      nlinarith [htwice]
    have hmB : W.m + 1 ≤ B := by exact_mod_cast hmBReal
    have hLB : W.L + gap.Cgap + 2 ≤ B := by
      rw [hlevel]
      dsimp [B, H, exteriorCountSpanCap]
      omega
    have hfourB : 4 ≤ B := by dsimp [B]; omega
    nlinarith [Nat.mul_le_mul hmB hmB,
      Nat.mul_le_mul hfourB hLB]
  have hcardReal :
      ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
        (B : ℝ) ^ 6 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by
    have hcount := hsignatureCount.2
    change (exteriorSignatures W Z0 gap.Cgap).ncard ≤ _ at hcount
    have hcountReal : ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
        (((W.m + 1) * 4 * (W.m + 1) *
          (W.L + gap.Cgap + 2) : ℕ) : ℝ) *
          ((∑ r ∈ Finset.Icc 0 W.m,
            (exteriorWordBound W gap.Cgap).choose r : ℕ) : ℝ) := by
      exact_mod_cast hcount
    calc
      ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤ _ := hcountReal
      _ ≤ ((B : ℝ) ^ 4) *
          ((B : ℝ) ^ 2 * Real.rpow 2
            ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L))) := by
        exact mul_le_mul (by exact_mod_cast hpolyNat) hsumReal
          (by positivity) (by positivity)
      _ = (B : ℝ) ^ 6 * Real.rpow 2
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) := by ring
  have hcardTarget :
      ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
        Real.rpow W.X
          (exteriorPrefixExponent W.entropy + exteriorCountError context gap L) := by
    apply hcardReal.trans
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2 : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
    have hBreal : (0 : ℝ) < B := by positivity
    have hbase : (0 : ℝ) < (W.X : ℝ) := by simp [WindowSystem.X, dyadicScale]
    have hrpowTwo : Real.rpow 2
        ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L)) =
        Real.exp (Real.log 2 *
          ((B : ℝ) * binaryEntropy (exteriorCountAlpha context gap L))) :=
      Real.rpow_def_of_pos (x := 2) (by norm_num) _
    have hrpowBase : Real.rpow (W.X : ℝ)
        (exteriorPrefixExponent W.entropy + exteriorCountError context gap L) =
        Real.exp (Real.log (W.X : ℝ) *
          (exteriorPrefixExponent W.entropy +
            exteriorCountError context gap L)) :=
      Real.rpow_def_of_pos (x := (W.X : ℝ)) hbase _
    rw [hrpowTwo, hrpowBase]
    have hpolyExp : (B : ℝ) ^ 6 =
        Real.exp (6 * Real.log (B : ℝ)) := by
      calc
        (B : ℝ) ^ 6 = Real.exp (Real.log ((B : ℝ) ^ 6)) :=
          (Real.exp_log (pow_pos hBreal 6)).symm
        _ = Real.exp (6 * Real.log (B : ℝ)) := by
          rw [Real.log_pow]
          norm_num
    rw [hpolyExp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hXcast : (W.X : ℝ) = (2 : ℝ) ^ L := by
      simp [WindowSystem.X, dyadicScale, hlevel]
    rw [hXcast, Real.log_pow, hentropy]
    have herror : exteriorCountError context gap L =
        |((B : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy| +
          6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2) := by
      simpa [B, H] using
        (show exteriorCountError context gap L =
          |(((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ) / (L : ℝ)) *
              binaryEntropy (exteriorCountAlpha context gap L) -
            exteriorPrefixExponent context.entropy| +
            6 * Real.log
              (((exteriorCountSpanCap context gap L + 5 : ℕ) : ℝ)) /
              ((L : ℝ) * Real.log 2) by
            simp only [exteriorCountError, Nat.ne_of_gt hL, if_false])
    rw [herror]
    have hmainLe :
        ((B : ℝ) / (L : ℝ)) *
            binaryEntropy (exteriorCountAlpha context gap L) ≤
          exteriorPrefixExponent context.entropy +
            |((B : ℝ) / (L : ℝ)) *
              binaryEntropy (exteriorCountAlpha context gap L) -
              exteriorPrefixExponent context.entropy| := by
      linarith [le_abs_self
        (((B : ℝ) / (L : ℝ)) *
          binaryEntropy (exteriorCountAlpha context gap L) -
          exteriorPrefixExponent context.entropy)]
    have hscalePos : 0 < (L : ℝ) * Real.log 2 := mul_pos hLpos hlog2pos
    have hscaled := mul_le_mul_of_nonneg_left hmainLe hscalePos.le
    have hpolyCancel :
        ((L : ℝ) * Real.log 2) *
            (6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2)) =
          6 * Real.log (B : ℝ) := by field_simp [hL0, hlog2]
    have hentropyScale :
        Real.log 2 * ((B : ℝ) *
            binaryEntropy (exteriorCountAlpha context gap L)) =
          ((L : ℝ) * Real.log 2) *
            (((B : ℝ) / (L : ℝ)) *
              binaryEntropy (exteriorCountAlpha context gap L)) := by
      field_simp [hL0]
    calc
      6 * Real.log (B : ℝ) +
          Real.log 2 * ((B : ℝ) *
            binaryEntropy (exteriorCountAlpha context gap L)) =
          ((L : ℝ) * Real.log 2) *
              (((B : ℝ) / (L : ℝ)) *
                binaryEntropy (exteriorCountAlpha context gap L)) +
            ((L : ℝ) * Real.log 2) *
              (6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2)) := by
        rw [hentropyScale, hpolyCancel]
        ring
      _ ≤ ((L : ℝ) * Real.log 2) *
              (exteriorPrefixExponent context.entropy +
                |((B : ℝ) / (L : ℝ)) *
                    binaryEntropy (exteriorCountAlpha context gap L) -
                  exteriorPrefixExponent context.entropy|) +
            ((L : ℝ) * Real.log 2) *
              (6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2)) :=
        add_le_add hscaled le_rfl
      _ = ((L : ℝ) * Real.log 2) *
          (exteriorPrefixExponent context.entropy +
            (|((B : ℝ) / (L : ℝ)) *
                binaryEntropy (exteriorCountAlpha context gap L) -
              exteriorPrefixExponent context.entropy| +
              6 * Real.log (B : ℝ) / ((L : ℝ) * Real.log 2))) := by ring
  refine ⟨hsignatureCount.1, ?_, ?_⟩
  · simpa [W] using hcardTarget
  · intro e he
    obtain ⟨signature, hmem, _hvalid, hlower, hupper, hlength⟩ :=
      longExteriorPair_has_signature context gap F hF Z0 L hcutoff hgap e he
    exact ⟨signature, hmem, by simpa [W] using hlower,
      by simpa [W, CQ] using hupper, by simpa [W] using hlength⟩

theorem exteriorPairs_subset_pairSet (W : WindowSystem) (Z0 : ℕ) :
    exteriorPairs W Z0 ⊆ W.pairSet := by
  intro e he
  exact he.1.1

theorem exteriorPairs_subset_exteriorRectangle (W : WindowSystem) (Z0 : ℕ) :
    exteriorPairs W Z0 ⊆
      Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds := by
  classical
  intro e he
  refine ⟨?_, he.1.1.2⟩
  rw [Finset.mem_coe, exteriorAnchors, Finset.mem_filter]
  exact ⟨he.1.1.1, e.2, he⟩

private theorem windowThresholdMeasure_exteriorRectangle
    (W : WindowSystem) (Z0 : ℕ) :
    windowThresholdMeasure
        (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) =
      ((exteriorAnchors W Z0).card : ℝ≥0∞) *
        ENNReal.ofReal (thresholdLength W) := by
  rw [windowThresholdMeasure]
  have hprod :
      (Measure.count.prod volume)
          (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) =
        Measure.count (exteriorAnchors W Z0 : Set ℕ) * volume W.thresholds :=
    MeasureTheory.Measure.prod_prod _ _
  rw [hprod]
  simp only [Measure.count_apply_finset, WindowSystem.thresholds,
    thresholdInterval, Real.volume_Icc, thresholdLength]
  congr 2
  ring

/-- Certified real mass of the long-exterior parent family. -/
def exteriorPairsMass (W : WindowSystem) (Z0 : ℕ) : ℝ :=
  finiteWindowMass W (exteriorPairs W Z0)
    (exteriorPairs_subset_pairSet W Z0)

private theorem exteriorPairsMass_le (W : WindowSystem) (Z0 : ℕ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ e ∈ exteriorPairs W Z0, W.excess e ≤ M) :
    exteriorPairsMass W Z0 ≤
      M * (exteriorAnchors W Z0).card * thresholdLength W := by
  have hmass : mass (exteriorPairs W Z0) W.excess ≤
      ENNReal.ofReal M * windowThresholdMeasure
        (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) := by
    unfold mass
    calc
      (∫⁻ e in exteriorPairs W Z0, ENNReal.ofReal (W.excess e)
          ∂windowThresholdMeasure) ≤
          ∫⁻ _e in exteriorPairs W Z0, ENNReal.ofReal M
            ∂windowThresholdMeasure := by
        apply setLIntegral_mono measurable_const
        intro e he
        exact ENNReal.ofReal_le_ofReal (hbound e he)
      _ ≤ ∫⁻ _e in
          Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds,
          ENNReal.ofReal M ∂windowThresholdMeasure :=
        lintegral_mono_set (exteriorPairs_subset_exteriorRectangle W Z0)
      _ = ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) :=
        setLIntegral_const _ _
  have hleftTop : mass (exteriorPairs W Z0) W.excess ≠ ⊤ :=
    (finiteMassOfSubset W (exteriorPairs W Z0)
      (exteriorPairs_subset_pairSet W Z0)).ne_top
  have hlength : 0 ≤ thresholdLength W :=
    mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hrightTop :
      ENNReal.ofReal M * windowThresholdMeasure
          (Set.prod (exteriorAnchors W Z0 : Set ℕ) W.thresholds) ≠ ⊤ := by
    rw [windowThresholdMeasure_exteriorRectangle]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
  have hto := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hmass
  change (mass (exteriorPairs W Z0) W.excess).toReal ≤ _
  rw [windowThresholdMeasure_exteriorRectangle] at hto
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlength, mul_assoc] using hto

private theorem eventually_exterior_parameter_term_le_one
    (Gamma Coff : ℝ) (hGamma : 1 < Gamma) (hCoff : 0 < Coff) :
    ∀ᶠ L : ℕ in atTop, ∀ n : ℕ, Gamma * (L : ℝ) < n →
      Coff * dyadicScale L * (2 : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  let d : ℝ := Gamma - 1
  let b : ℝ := Real.log 2 * d
  have hd : 0 < d := by dsimp [d]; linarith
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) hd
  have hnatTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hexpTop : Tendsto (fun L : ℕ => Real.exp (b * (L : ℝ)))
      atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hb hnatTop)
  have hdecay : Tendsto
      (fun L : ℕ => Coff / Real.exp (b * (L : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hexpTop
  have hevent : ∀ᶠ L : ℕ in atTop,
      Coff / Real.exp (b * (L : ℝ)) ≤ 1 :=
    ((tendsto_order.1 hdecay).2 1 (by norm_num)).mono fun _ h => h.le
  filter_upwards [hevent] with L hL
  intro n hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnPower : Real.exp (Real.log 2 * (Gamma * (L : ℝ))) ≤
      (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn.le hlog2.le)
  have hdenom :
      Real.exp (b * (L : ℝ)) * (2 : ℝ) ^ L =
        Real.exp (Real.log 2 * (Gamma * (L : ℝ))) := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (x := (2 : ℝ)) (by norm_num),
      ← Real.exp_add]
    congr 1
    dsimp [b, d]
    ring
  have hdenomLe : Real.exp (b * (L : ℝ)) * (2 : ℝ) ^ L ≤
      (2 : ℝ) ^ n := by rw [hdenom]; exact hnPower
  have hpowL : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hfraction :
      Coff * (2 : ℝ) ^ L / (2 : ℝ) ^ n ≤
        Coff / Real.exp (b * (L : ℝ)) := by
    calc
      Coff * (2 : ℝ) ^ L / (2 : ℝ) ^ n ≤
          Coff * (2 : ℝ) ^ L /
            (Real.exp (b * (L : ℝ)) * (2 : ℝ) ^ L) :=
        div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Real.exp_pos _) hpowL) hdenomLe
      _ = Coff / Real.exp (b * (L : ℝ)) := by
        field_simp [ne_of_gt hpowL, ne_of_gt (Real.exp_pos _)]
  calc
    Coff * dyadicScale L * (2 : ℝ) ^ (-(n : ℤ)) =
        Coff * (2 : ℝ) ^ L / (2 : ℝ) ^ n := by
      rw [zpow_neg, zpow_natCast]
      simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
    _ ≤ Coff / Real.exp (b * (L : ℝ)) := hfraction
    _ ≤ 1 := hL

private theorem eventually_exteriorAnchors_card_le
    (context : FixedScaleContext) (gap : GapParams context.Q) :
    ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∃ initialError exteriorError : ℕ → ℝ,
        Tendsto initialError atTop (𝓝 0) ∧
        Tendsto exteriorError atTop (𝓝 0) ∧
        ∀ F : ScaleFamily, F.MatchesContext context →
          ∀ᶠ L : ℕ in atTop,
            ((exteriorAnchors (F.system L) Z0).card : ℝ) ≤
              Real.rpow (F.system L).X
                  (initialPrefixExponent (F.system L).entropy + initialError L) *
                Real.rpow (F.system L).X
                  (exteriorPrefixExponent (F.system L).entropy + exteriorError L) * 2 := by
  classical
  obtain ⟨Cline, Clock, hClock, hlocking⟩ :=
    lem_ap_locking context.Q context.Q_pos
  obtain ⟨Coff, hCoff, hfixed⟩ :=
    prop_fixed_off_word context.Q context.Q_pos
  obtain ⟨CQfirst, hCQfirst, hfirstExists⟩ := lem_firstdeep_exists context
  obtain ⟨CQexterior, hCQexterior, Zsecond, hsecond⟩ :=
    lem_seconddeep context gap
  let Zfirst := Nat.ceil
    (2 * context.structural.Caff / context.entropy.kappa)
  let Zexit := Nat.ceil
    (4 * context.structural.Gamma / context.entropy.kappa) + 1
  let Zmin := max Zsecond (max Zfirst Zexit)
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0
  have hZfirst : Zfirst ≤ Z0 :=
    (le_max_left Zfirst Zexit).trans
      ((le_max_right Zsecond (max Zfirst Zexit)).trans hZ0)
  have hZsecond : Zsecond ≤ Z0 :=
    (le_max_left Zsecond (max Zfirst Zexit)).trans hZ0
  have hZexit : Zexit ≤ Z0 :=
    (le_max_right Zfirst Zexit).trans
      ((le_max_right Zsecond (max Zfirst Zexit)).trans hZ0)
  have hcutoff :
      4 * context.structural.Gamma / context.entropy.kappa < (Z0 : ℝ) := by
    have hceil : 4 * context.structural.Gamma / context.entropy.kappa ≤
        (Nat.ceil (4 * context.structural.Gamma /
          context.entropy.kappa) : ℝ) := Nat.le_ceil _
    have hsucc : Nat.ceil
        (4 * context.structural.Gamma / context.entropy.kappa) + 1 ≤ Z0 := by
      simpa only [Zexit] using hZexit
    exact hceil.trans_lt (by exact_mod_cast hsucc)
  obtain ⟨initialError, hinitialError, hinitialCount⟩ :=
    lem_firstdeep_count context Z0 (by simpa only [Zfirst] using hZfirst)
  obtain ⟨exteriorError, hexteriorError, hexteriorCount⟩ :=
    hsecond Z0 hZsecond
  refine ⟨initialError, exteriorError, hinitialError, hexteriorError, ?_⟩
  intro F hF
  have hfirstEvent := hfirstExists Z0
    (by simpa only [Zfirst] using hZfirst) F hF
  have hinitialEvent := hinitialCount F hF
  have hexteriorEvent := hexteriorCount F hF
  have hgapEvent := eventually_rawWindowGap_le context gap F hF
  have hGamma : 1 < context.structural.Gamma := context.structural.Gamma_gt
  have hparameterEvent := eventually_exterior_parameter_term_le_one
    context.structural.Gamma Coff hGamma hCoff
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
  obtain ⟨Lpow, hpow⟩ := eventually_quadratic_lt_two_pow (gap.Cgap + 2)
  have hgapScaleEvent : ∀ᶠ L : ℕ in atTop,
      L + gap.Cgap + 1 ≤ dyadicScale L := by
    filter_upwards [eventually_ge_atTop (max Lpow 1)] with L hL
    have hLpow : Lpow ≤ L := (le_max_left Lpow 1).trans hL
    have hLone : 1 ≤ L := (le_max_right Lpow 1).trans hL
    have hlinear : L + gap.Cgap + 1 ≤ (gap.Cgap + 2) * L ^ 2 := by
      have hc : gap.Cgap + 1 ≤ (gap.Cgap + 1) * L :=
        by simpa using Nat.mul_le_mul_left (gap.Cgap + 1) hLone
      have hbase : L + gap.Cgap + 1 ≤ (gap.Cgap + 2) * L := by
        calc
          L + gap.Cgap + 1 = L + (gap.Cgap + 1) := by omega
          _ ≤ L + (gap.Cgap + 1) * L := Nat.add_le_add_left hc L
          _ = (gap.Cgap + 2) * L := by ring
      have hsq : L ≤ L ^ 2 := by
        calc
          L = L * 1 := by simp
          _ ≤ L * L := Nat.mul_le_mul_left L hLone
          _ = L ^ 2 := by ring
      exact hbase.trans (Nat.mul_le_mul_left (gap.Cgap + 2) hsq)
    exact hlinear.trans (hpow L hLpow).le
  filter_upwards [hfirstEvent, hinitialEvent, hexteriorEvent, hgapEvent,
    hparameterEvent, hlineEvent, hgapScaleEvent, eventually_ge_atTop 1]
      with L hfirstL hinitialL hexteriorL hgapL hparameterL hlineL
        hgapScale hL
  let W := F.system L
  have hden : W.rational.eta.den = context.Q := by
    change (F.system L).rational.eta.den = context.Q
    rw [F.rational_eq, hF.1]
  have hQW : 0 < W.rational.eta.den := by simpa [hden] using context.Q_pos
  have hstruct : W.structural = context.structural := by
    change (F.system L).structural = context.structural
    rw [F.structural_eq, hF.2.1]
  have hentropy : W.entropy = context.entropy := by
    change (F.system L).entropy = context.entropy
    rw [F.entropy_eq, hF.2.2.1]
  have hlevel : W.L = L := F.level_eq L
  have hfrequency : 1 < frequencyCutoff W := by
    unfold frequencyCutoff
    have hX : (1 : ℝ) < W.X := by
      rw [WindowSystem.X, hlevel, dyadicScale]
      exact_mod_cast (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ))
        (Nat.ne_of_gt hL))
    apply Real.one_lt_rpow hX
    rw [hstruct]
    linarith [context.structural.rho_pos]
  let Anchor := {k // k ∈ exteriorAnchors W Z0}
  have pairExists (k : Anchor) :
      ∃ T : ℝ, LongExteriorPair W Z0 (k.1, T) := by
    have hk := k.2
    change k.1 ∈ W.anchors.filter fun j =>
      ∃ T : ℝ, LongExteriorPair W Z0 (j, T) at hk
    rw [Finset.mem_filter] at hk
    exact hk.2
  let thresholdFor : Anchor → ℝ := fun k => Classical.choose (pairExists k)
  have thresholdSpec (k : Anchor) :
      LongExteriorPair W Z0 (k.1, thresholdFor k) :=
    Classical.choose_spec (pairExists k)
  have signatureExists (k : Anchor) :
      ∃ signature : ExteriorSignature,
        signature ∈ exteriorSignatures W Z0 gap.Cgap ∧
        ValidExteriorSignature W Z0 gap.Cgap (k.1, thresholdFor k) signature ∧
        W.structural.Gamma * L < signature.word.span ∧
        (signature.word.span : ℝ) ≤
          (W.structural.Gamma + 1) * L + (gap.Cgap + 1) ∧
        signature.word.length ≤ W.m := by
    simpa only [W] using longExteriorPair_has_signature context gap F hF Z0 L
      hcutoff hgapL (k.1, thresholdFor k) (thresholdSpec k)
  let signatureFor : Anchor → ExteriorSignature := fun k =>
    Classical.choose (signatureExists k)
  have signatureSpec (k : Anchor) :
      signatureFor k ∈ exteriorSignatures W Z0 gap.Cgap ∧
      ValidExteriorSignature W Z0 gap.Cgap (k.1, thresholdFor k)
        (signatureFor k) ∧
      W.structural.Gamma * L < (signatureFor k).word.span ∧
      ((signatureFor k).word.span : ℝ) ≤
        (W.structural.Gamma + 1) * L + (gap.Cgap + 1) ∧
      (signatureFor k).word.length ≤ W.m :=
    Classical.choose_spec (signatureExists k)
  have highOfAnchor (k : Anchor) : k.1 ∈ highAnchors W Z0 := by
    have hpair := thresholdSpec k
    rw [highAnchors, Finset.mem_filter]
    exact ⟨hpair.1.1.1, thresholdFor k, hpair.1.1.2, hpair.1.2⟩
  have primitiveAt (k : Anchor) :
      HasPrimitiveOccurrenceLine W Z0 (initialLongPrefix W k.1) := by
    let p := initialLongPrefix W k.1
    have hpMem : p ∈ initialPrefixes W Z0 := by
      rw [initialPrefixes, Finset.mem_image]
      exact ⟨k.1, highOfAnchor k, rfl⟩
    have hpLower := hfirstL (k.1, thresholdFor k) (thresholdSpec k).1
    dsimp only at hpLower
    have hpLong : 2 * W.L + Cline < p.span := by
      have hpReal : context.structural.Caff * (L : ℝ) < (p.span : ℝ) := by
        have hpReal' := hpLower.1
        change W.structural.Caff * (W.L : ℝ) < (p.span : ℝ) at hpReal'
        rw [hstruct, hlevel] at hpReal'
        exact hpReal'
      have htarget : ((2 * W.L + Cline : ℕ) : ℝ) < (p.span : ℝ) := by
        rw [hlevel]
        push_cast
        dsimp [lineSlack] at hlineL
        nlinarith
      exact_mod_cast htarget
    rcases hlocking W hden Z0 p hpMem hpLong (thresholdSpec k).2.1 with
      ⟨line, hoccurrence, hprimitive, _hheight⟩
    exact ⟨line, hoccurrence, hprimitive⟩
  have sourceExists (k : Anchor) :
      ∃ source : ExteriorSource W Z0 (chosenExteriorLine W Z0),
        source.anchor = k.1 ∧ source.record = (signatureFor k).record ∧
          source.word = (signatureFor k).word := by
    apply validExteriorSignature_has_source W Z0 gap.Cgap hQW hfrequency
      (k.1, thresholdFor k) (thresholdSpec k) (signatureFor k)
      (signatureSpec k).2.1 (primitiveAt k)
    · intro g hg
      simpa only [hlevel] using hgapL k.1 (thresholdSpec k).1.1.1 g hg
    · simpa [WindowSystem.X, hlevel] using hgapScale
  let sourceFor : Anchor → ExteriorSource W Z0 (chosenExteriorLine W Z0) :=
    fun k => Classical.choose (sourceExists k)
  have sourceSpec (k : Anchor) :
      (sourceFor k).anchor = k.1 ∧
      (sourceFor k).record = (signatureFor k).record ∧
      (sourceFor k).word = (signatureFor k).word :=
    Classical.choose_spec (sourceExists k)
  have hsourceSmall (k : Anchor) :
      Coff * W.X * (2 : ℝ) ^ (-((sourceFor k).word.span : ℤ)) ≤ 1 := by
    have hlower : context.structural.Gamma * (L : ℝ) <
        (sourceFor k).word.span := by
      rw [(sourceSpec k).2.2]
      simpa [hstruct] using (signatureSpec k).2.2.1
    have h := hparameterL (sourceFor k).word.span hlower
    simpa [WindowSystem.X, hlevel] using h
  have hanchorNat := exteriorAnchors_card_le_of_sources W Z0 gap.Cgap
    hQW Coff hCoff (by simpa [hden] using hfixed) hexteriorL.1
    sourceFor signatureFor
    (fun k => (sourceSpec k).1)
    (fun k => (signatureSpec k).1)
    (fun k => (sourceSpec k).2.1)
    (fun k => (sourceSpec k).2.2) hsourceSmall
  have hanchorReal : ((exteriorAnchors W Z0).card : ℝ) ≤
      ((initialPrefixes W Z0).card : ℝ) *
        ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) * 2 := by
    exact_mod_cast hanchorNat
  have hinitialW : ((initialPrefixes W Z0).card : ℝ) ≤
      Real.rpow W.X
        (initialPrefixExponent W.entropy + initialError L) := by
    simpa only [W] using hinitialL
  have hexteriorW : ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) ≤
      Real.rpow W.X
        (exteriorPrefixExponent W.entropy + exteriorError L) := by
    simpa only [W] using hexteriorL.2.1
  have hinitialNonneg : 0 ≤ Real.rpow W.X
      (initialPrefixExponent W.entropy + initialError L) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ((exteriorAnchors W Z0).card : ℝ) ≤
        ((initialPrefixes W Z0).card : ℝ) *
          ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) * 2 := hanchorReal
    _ ≤ Real.rpow W.X
          (initialPrefixExponent W.entropy + initialError L) *
        ((exteriorSignatures W Z0 gap.Cgap).ncard : ℝ) * 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinitialW (by positivity)) (by norm_num)
    _ ≤ Real.rpow W.X
          (initialPrefixExponent W.entropy + initialError L) *
        Real.rpow W.X
          (exteriorPrefixExponent W.entropy + exteriorError L) * 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexteriorW hinitialNonneg) (by norm_num)

/-- Paper label: `thm:off-mass` (Section 7).  The exterior estimate starts
after one denominator-level cutoff, as required by `lem_seconddeep`. -/
theorem thm_off_mass (context : FixedScaleContext) :
    ∃ Zmin : ℕ, ∀ Z0 : ℕ, Zmin ≤ Z0 →
      ∀ F : ScaleFamily, F.MatchesContext context →
      (fun L =>
        exteriorPairsMass (F.system L) Z0) =o[atTop]
        (fun L =>
          ((F.system L).m : ℝ) * (F.system L).X *
            thresholdLength (F.system L)) := by
  classical
  obtain ⟨gap⟩ := gapParams_exists context.Q context.Q_pos
  obtain ⟨Zmin, hanchors⟩ := eventually_exteriorAnchors_card_le context gap
  refine ⟨Zmin, ?_⟩
  intro Z0 hZ0 F hF
  obtain ⟨initialError, exteriorError, hinitialError, hexteriorError,
      hanchorCount⟩ := hanchors Z0 hZ0
  have hanchorEvent := hanchorCount F hF
  have hgapEvent := eventually_rawWindowGap_le context gap F hF
  let Δ : ℝ := initialPrefixExponent context.entropy
  let δext : ℝ := exteriorPrefixExponent context.entropy
  let margin : ℝ := 1 - 2 * context.structural.rho - (Δ + δext)
  let d : ℝ := margin / 2
  have htotal : Δ + δext < 1 - 2 * context.structural.rho := by
    dsimp [Δ, δext, initialPrefixExponent, exteriorPrefixExponent]
    simpa only [context.entropy_structural] using context.entropy.total_margin
  have hmargin : 0 < margin := by dsimp [margin]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have herrorZero : Tendsto (fun L => initialError L + exteriorError L)
      atTop (𝓝 0) := by simpa using hinitialError.add hexteriorError
  have herrorSmall : ∀ᶠ L : ℕ in atTop,
      initialError L + exteriorError L ≤ d :=
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
  have hbaseDecay : Tendsto
      (fun L : ℕ => ((L : ℝ) + gap.Cgap + 1) /
        Real.exp (b * (L : ℝ))) atTop (𝓝 0) := by
    simpa only [add_div, zero_add, add_assoc] using hpolyExp.add hconstExp
  have hdecayExp : Tendsto
      (fun L : ℕ => 2 * (((L : ℝ) + gap.Cgap + 1) /
        Real.exp (b * (L : ℝ)))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hbaseDecay
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
    congr 1
    ring
  have hdecay : Tendsto
      (fun L : ℕ => 2 * ((L : ℝ) + gap.Cgap + 1) /
        Real.rpow (dyadicScale L) d) atTop (𝓝 0) := by
    apply hdecayExp.congr'
    filter_upwards with L
    rw [hrpowExp]
    simp only [div_eq_mul_inv, mul_assoc]
  apply IsLittleO.of_bound
  intro c hc
  have hdecayC : ∀ᶠ L : ℕ in atTop,
      2 * ((L : ℝ) + gap.Cgap + 1) /
          Real.rpow (dyadicScale L) d ≤ c :=
    ((tendsto_order.1 hdecay).2 c hc).mono fun _ h => h.le
  filter_upwards [hanchorEvent, hgapEvent, herrorSmall, hdecayC,
    eventually_ge_atTop 1]
      with L hanchor hgap herrorL hdecayL hL
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
  have hmnonneg : (0 : ℝ) ≤ W.m := by positivity
  have hGnonneg : (0 : ℝ) ≤ G := by positivity
  have hlengthNonneg : 0 ≤ thresholdLength W := by
    unfold thresholdLength
    exact mul_nonneg W.structural.cI_pos.le (Nat.cast_nonneg _)
  have hexcessBound : ∀ e ∈ exteriorPairs W Z0,
      W.excess e ≤ (W.m : ℝ) * G := by
    intro e he
    have hexcess := W.excess_le_rawWindowSpan e he.1.1
    have hsum : (W.rawWindowGapWord e.1).sum ≤
        (W.rawWindowGapWord e.1).length * G := by
      simpa [nsmul_eq_mul] using
        List.sum_le_card_nsmul (W.rawWindowGapWord e.1) G
          (hgap e.1 he.1.1.1)
    have hlen : (W.rawWindowGapWord e.1).length ≤ W.m :=
      rawWindowGapWord_length_le W e.1
    have hspan : W.rawWindowSpan e.1 ≤ W.m * G := by
      have hspanEq : (W.rawWindowGapWord e.1).span =
          W.rawWindowSpan e.1 := by
        unfold WindowSystem.rawWindowGapWord WindowSystem.rawWindowSpan
        split <;> rfl
      rw [← hspanEq]
      exact hsum.trans (Nat.mul_le_mul_right G hlen)
    exact hexcess.trans (by exact_mod_cast hspan)
  have hmass := exteriorPairsMass_le W Z0 ((W.m : ℝ) * G)
    (mul_nonneg hmnonneg hGnonneg) hexcessBound
  have hanchorW : ((exteriorAnchors W Z0).card : ℝ) ≤
      Real.rpow W.X (Δ + initialError L) *
        Real.rpow W.X (δext + exteriorError L) * 2 := by
    simpa only [W, hWentropy, Δ, δext] using hanchor
  have hexponent :
      Δ + initialError L + (δext + exteriorError L) ≤ 1 - d := by
    dsimp [d, margin] at herrorL ⊢
    nlinarith [context.structural.rho_pos]
  have hrpowExponent : Real.rpow W.X
      (Δ + initialError L + (δext + exteriorError L)) ≤
      Real.rpow W.X (1 - d) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hanchorFinal : ((exteriorAnchors W Z0).card : ℝ) ≤
      2 * (W.X / Real.rpow W.X d) := by
    calc
      ((exteriorAnchors W Z0).card : ℝ) ≤
          Real.rpow W.X (Δ + initialError L) *
            Real.rpow W.X (δext + exteriorError L) * 2 := hanchorW
      _ = 2 * (Real.rpow W.X (Δ + initialError L) *
          Real.rpow W.X (δext + exteriorError L)) := by ring
      _ = 2 * Real.rpow W.X
          (Δ + initialError L + (δext + exteriorError L)) := by
        congr 1
        exact (Real.rpow_add hXpos _ _).symm
      _ ≤ 2 * Real.rpow W.X (1 - d) := by gcongr
      _ = 2 * (W.X / Real.rpow W.X d) := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_sub hXpos 1 d, Real.rpow_one]
  have hdecayW : 2 * (G : ℝ) / Real.rpow W.X d ≤ c := by
    rw [hX]
    simpa only [G, Nat.cast_add, Nat.cast_one] using hdecayL
  have hmassFinal : exteriorPairsMass W Z0 ≤
      c * ((W.m : ℝ) * W.X * thresholdLength W) := by
    calc
      exteriorPairsMass W Z0 ≤
          ((W.m : ℝ) * G) * (exteriorAnchors W Z0).card *
            thresholdLength W := hmass
      _ ≤ ((W.m : ℝ) * G) *
          (2 * (W.X / Real.rpow W.X d)) * thresholdLength W := by
        gcongr
      _ = ((W.m : ℝ) * W.X * thresholdLength W) *
          (2 * (G : ℝ) / Real.rpow W.X d) := by ring
      _ ≤ ((W.m : ℝ) * W.X * thresholdLength W) * c := by
        gcongr
      _ = c * ((W.m : ℝ) * W.X * thresholdLength W) := by ring
  have hmassNonneg : 0 ≤ exteriorPairsMass W Z0 := by
    unfold exteriorPairsMass finiteWindowMass FiniteMass.toReal
    exact ENNReal.toReal_nonneg
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmassNonneg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hmnonneg hXpos.le)
      hlengthNonneg), W] using hmassFinal

end Erdos260
