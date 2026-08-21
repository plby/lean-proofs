import ErdosProblems.Erdos228.OddSine

/-!
# Finite near-interval geometry for the odd kernel

This file packages the elementary one-dimensional geometry used when the
BBMST odd kernel is split into its interval contributions.  For a point
`theta`, the base intervals within one grid spacing `pi / n` form a finite
set.  If `theta` is in a base interval, separation makes that interval the
only near interval.  If `theta` is outside their union, at most one near
interval can lie on either side, hence there are at most two in total.
-/

namespace Erdos228.KernelNearGeometry

open scoped BigOperators
open Set

noncomputable section

open Erdos228.OddSine

/-- The (nonnegative) gap from `theta` to the closed interval represented by
`I`.  It is written explicitly rather than through `Metric.infDist`, so the
left/right endpoint selected by the kernel estimates is visible to Lean. -/
def intervalGap (theta : ℝ) (I : RealInterval) : ℝ :=
  max (I.1 - theta) (max (theta - I.2) 0)

theorem intervalGap_nonneg (theta : ℝ) (I : RealInterval) :
    0 ≤ intervalGap theta I := by
  exact le_max_of_le_right (le_max_right _ _)

theorem intervalGap_eq_zero_of_mem {theta : ℝ} {I : RealInterval}
    (htheta : InInterval I theta) :
    intervalGap theta I = 0 := by
  rw [InInterval, mem_Icc] at htheta
  simp only [intervalGap]
  rw [max_eq_right (sub_nonpos.mpr htheta.2)]
  rw [max_eq_right (sub_nonpos.mpr htheta.1)]

theorem intervalGap_eq_left {theta : ℝ} {I : RealInterval}
    (hI : I.1 ≤ I.2) (htheta : theta ≤ I.1) :
    intervalGap theta I = I.1 - theta := by
  have htheta' : theta ≤ I.2 := htheta.trans hI
  simp only [intervalGap]
  rw [max_eq_right (sub_nonpos.mpr htheta')]
  rw [max_eq_left (sub_nonneg.mpr htheta)]

theorem intervalGap_eq_right {theta : ℝ} {I : RealInterval}
    (hI : I.1 ≤ I.2) (htheta : I.2 ≤ theta) :
    intervalGap theta I = theta - I.2 := by
  have htheta' : I.1 ≤ theta := hI.trans htheta
  simp only [intervalGap]
  rw [max_eq_left (sub_nonneg.mpr htheta)]
  rw [max_eq_right]
  exact (sub_nonpos.mpr htheta').trans (sub_nonneg.mpr htheta)

/-- An interval is near `theta` when its closed-interval gap is strictly less
than one grid spacing. -/
def Near (n : ℕ) (theta : ℝ) (I : RealInterval) : Prop :=
  intervalGap theta I < Real.pi / n

/-- The finite collection of base intervals near `theta`. -/
noncomputable def nearIntervals {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (Near n theta) (Classical.decPred _) F.base

/-- The union-membership predicate for the base interval family. -/
def InBaseUnion {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) : Prop :=
  ∃ I ∈ F.base, InInterval I theta

/-- Near intervals strictly to the left of `theta`. -/
noncomputable def nearLeftIntervals {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (fun I ↦ Near n theta I ∧ I.2 < theta)
    (Classical.decPred _) F.base

/-- Near intervals strictly to the right of `theta`. -/
noncomputable def nearRightIntervals {n : ℕ} (F : SuitableIntervalFamily n) (theta : ℝ) :
    Finset RealInterval :=
  @Finset.filter _ (fun I ↦ Near n theta I ∧ theta < I.1)
    (Classical.decPred _) F.base

/-- The same near collection indexed by the subtype used by the odd-kernel
coefficients. -/
noncomputable def nearBaseIntervals {n : ℕ} (F : SuitableIntervalFamily n)
    (theta : ℝ) : Finset (↑F.base : Type) :=
  @Finset.filter (↑F.base : Type) (fun I ↦ Near n theta I.1)
    (Classical.decPred _) Finset.univ

/-- Forgetting subtype membership identifies the subtype-indexed and
endpoint-indexed near collections. -/
theorem nearIntervals_eq_image_nearBaseIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    nearIntervals F theta =
      (nearBaseIntervals F theta).image (fun I ↦ I.1) := by
  classical
  ext I
  simp [nearIntervals, nearBaseIntervals, and_comm]

/-- Two base intervals containing the same point are equal. -/
theorem eq_of_mem_intervals {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I J : RealInterval}
    (hI : I ∈ F.base) (hJ : J ∈ F.base)
    (hthetaI : InInterval I theta) (hthetaJ : InInterval J theta) :
    I = J := by
  by_contra hne
  have hsep := F.separated hI hJ hne theta hthetaI theta hthetaJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  exact (not_le_of_gt hpi) (by simpa using hsep)

/-- If `theta` belongs to `I`, every other base interval has gap at least one
grid spacing. -/
theorem intervalGap_ge_of_mem_of_ne {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I J : RealInterval}
    (hI : I ∈ F.base) (hJ : J ∈ F.base) (hne : I ≠ J)
    (htheta : InInterval I theta) :
    Real.pi / n ≤ intervalGap theta J := by
  have hnotJ : ¬InInterval J theta := by
    intro hthetaJ
    exact hne (eq_of_mem_intervals hn F hI hJ htheta hthetaJ)
  rw [InInterval, mem_Icc] at hnotJ
  rcases not_and_or.mp hnotJ with hleft | hright
  · have hleft' : theta < J.1 := lt_of_not_ge hleft
    rw [intervalGap_eq_left (F.ordered J hJ) hleft'.le]
    have hsep := F.separated hI hJ hne theta htheta J.1
      ⟨le_rfl, F.ordered J hJ⟩
    rw [abs_of_neg (sub_neg.mpr hleft')] at hsep
    linarith
  · have hright' : J.2 < theta := lt_of_not_ge hright
    rw [intervalGap_eq_right (F.ordered J hJ) hright'.le]
    have hsep := F.separated hI hJ hne theta htheta J.2
      ⟨F.ordered J hJ, le_rfl⟩
    rw [abs_of_pos (sub_pos.mpr hright')] at hsep
    exact hsep

/-- A point of a base interval has exactly that interval in its near set. -/
theorem nearIntervals_eq_singleton_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta) :
    nearIntervals F theta = {I} := by
  classical
  ext J
  simp only [nearIntervals, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hJ, hnear⟩
    by_contra hJI
    have hgap := intervalGap_ge_of_mem_of_ne hn F hI hJ
      (fun h ↦ hJI h.symm) htheta
    exact (not_lt_of_ge hgap) hnear
  · intro hJI
    subst J
    refine ⟨hI, ?_⟩
    rw [Near, intervalGap_eq_zero_of_mem htheta]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos Real.pi_pos hnR

/-- Subtype-indexed version of `nearIntervals_eq_singleton_of_mem`. -/
theorem nearBaseIntervals_eq_singleton_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta) :
    nearBaseIntervals F theta = {⟨I, hI⟩} := by
  classical
  ext J
  simp only [nearBaseIntervals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hnear
    apply Subtype.ext
    by_contra hne
    have hgap := intervalGap_ge_of_mem_of_ne hn F hI J.property
      (fun h ↦ hne h.symm) htheta
    exact (not_lt_of_ge hgap) hnear
  · intro hJI
    subst J
    rw [Near, intervalGap_eq_zero_of_mem htheta]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos Real.pi_pos hnR

/-- The endpoint and subtype versions have the same cardinality. -/
theorem card_nearBaseIntervals_eq_card_nearIntervals {n : ℕ}
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (nearBaseIntervals F theta).card = (nearIntervals F theta).card := by
  rw [nearIntervals_eq_image_nearBaseIntervals]
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-- Outside the union, every near interval is either strictly left or
strictly right of the point. -/
theorem nearIntervals_eq_left_union_right_of_not_inBaseUnion {n : ℕ}
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (hout : ¬InBaseUnion F theta) :
    nearIntervals F theta =
      nearLeftIntervals F theta ∪ nearRightIntervals F theta := by
  classical
  ext I
  simp only [nearIntervals, nearLeftIntervals, nearRightIntervals,
    Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hI, hnear⟩
    have hnot : ¬InInterval I theta := fun h ↦ hout ⟨I, hI, h⟩
    rw [InInterval, mem_Icc] at hnot
    rcases not_and_or.mp hnot with hright | hleft
    · exact Or.inr ⟨hI, hnear, lt_of_not_ge hright⟩
    · exact Or.inl ⟨hI, hnear, lt_of_not_ge hleft⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, hleft.2.1⟩
    · exact ⟨hright.1, hright.2.1⟩

/-- At most one near interval lies strictly to the left of a point. -/
theorem card_nearLeftIntervals_le_one {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (nearLeftIntervals F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  simp only [nearLeftIntervals, Finset.mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.2
    ⟨F.ordered I hI.1, le_rfl⟩ J.2 ⟨F.ordered J hJ.1, le_rfl⟩
  have hgapI : theta - I.2 < Real.pi / n := by
    rw [← intervalGap_eq_right (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : theta - J.2 < Real.pi / n := by
    rw [← intervalGap_eq_right (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.2 - J.2| < Real.pi / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs

/-- At most one near interval lies strictly to the right of a point. -/
theorem card_nearRightIntervals_le_one {n : ℕ} (_hn : 0 < n)
    (F : SuitableIntervalFamily n) (theta : ℝ) :
    (nearRightIntervals F theta).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro I hI J hJ
  simp only [nearRightIntervals, Finset.mem_filter] at hI hJ
  by_contra hne
  have hsep := F.separated hI.1 hJ.1 hne I.1
    ⟨le_rfl, F.ordered I hI.1⟩ J.1 ⟨le_rfl, F.ordered J hJ.1⟩
  have hgapI : I.1 - theta < Real.pi / n := by
    rw [← intervalGap_eq_left (F.ordered I hI.1) hI.2.2.le]
    exact hI.2.1
  have hgapJ : J.1 - theta < Real.pi / n := by
    rw [← intervalGap_eq_left (F.ordered J hJ.1) hJ.2.2.le]
    exact hJ.2.1
  have habs : |I.1 - J.1| < Real.pi / n := by
    rw [abs_lt]
    constructor <;> linarith [hI.2.2, hJ.2.2]
  exact (not_lt_of_ge hsep) habs

/-- Outside the base union, fewer than one grid spacing from `theta` can
hold for at most two base intervals. -/
theorem card_nearIntervals_le_two_of_not_inBaseUnion {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ}
    (hout : ¬InBaseUnion F theta) :
    (nearIntervals F theta).card ≤ 2 := by
  rw [nearIntervals_eq_left_union_right_of_not_inBaseUnion F hout]
  calc
    (nearLeftIntervals F theta ∪ nearRightIntervals F theta).card ≤
        (nearLeftIntervals F theta).card +
          (nearRightIntervals F theta).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (card_nearLeftIntervals_le_one hn F theta)
      (card_nearRightIntervals_le_one hn F theta)
    _ = 2 := rfl

/-- Subtype-indexed cardinality bound used directly in odd-kernel sums. -/
theorem card_nearBaseIntervals_le_two_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (hout : ¬InBaseUnion F theta) :
    (nearBaseIntervals F theta).card ≤ 2 := by
  rw [card_nearBaseIntervals_eq_card_nearIntervals]
  exact card_nearIntervals_le_two_of_not_inBaseUnion hn F hout

/-- In the first quadrant, the fourfold definition of `IsDangerous` reduces
to membership in one base interval.  Separation makes that interval unique. -/
theorem existsUnique_baseInterval_of_dangerous_firstQuadrant {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hdangerous : IsDangerous F theta) :
    ∃! I : RealInterval, I ∈ F.base ∧ InInterval I theta := by
  rcases hdangerous with ⟨I, hI, hmain | hneg | hreflect | htranslate⟩
  · refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact eq_of_mem_intervals hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InInterval, mem_Icc] at hneg
    have htheta0 : theta = 0 := by linarith [htheta.1, hquadI.1, hneg.1]
    have hmain : InInterval I theta := by
      rw [InInterval, mem_Icc]
      simpa [htheta0] using hneg
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact eq_of_mem_intervals hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InInterval, mem_Icc] at hreflect
    have hthetaMid : theta = Real.pi / 2 := by
      linarith [htheta.2, hquadI.2, hreflect.2]
    have harg : Real.pi - theta = theta := by
      rw [hthetaMid]
      ring
    have hmain : InInterval I theta := by
      rw [InInterval, mem_Icc, ← harg]
      exact hreflect
    refine ⟨I, ⟨hI, hmain⟩, ?_⟩
    rintro J ⟨hJ, hthetaJ⟩
    exact eq_of_mem_intervals hn F hJ hI hthetaJ hmain
  · have hquadI := F.in_first_quadrant I hI
    rw [InInterval, mem_Icc] at htranslate
    exfalso
    nlinarith [htheta.2, hquadI.1, htranslate.1, Real.pi_pos]

/-- Subtype-indexed unique interval for a dangerous first-quadrant point. -/
theorem existsUnique_baseSubtype_of_dangerous_firstQuadrant {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hdangerous : IsDangerous F theta) :
    ∃! I : (↑F.base : Type), InInterval I.1 theta := by
  obtain ⟨I, hI, hunique⟩ :=
    existsUnique_baseInterval_of_dangerous_firstQuadrant hn F htheta hdangerous
  refine ⟨⟨I, hI.1⟩, hI.2, ?_⟩
  intro J hthetaJ
  apply Subtype.ext
  exact hunique J.1 ⟨J.property, hthetaJ⟩

/-- Sum form of `nearIntervals_eq_singleton_of_mem`. -/
theorem sum_nearIntervals_eq_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta)
    (f : RealInterval → ℝ) :
    ∑ J ∈ nearIntervals F theta, f J = f I := by
  rw [nearIntervals_eq_singleton_of_mem hn F hI htheta]
  simp

/-- Subtype-indexed exact near-sum formula at a point of a base interval. -/
theorem sum_nearBaseIntervals_eq_of_mem {n : ℕ} (hn : 0 < n)
    (F : SuitableIntervalFamily n) {theta : ℝ} {I : RealInterval}
    (hI : I ∈ F.base) (htheta : InInterval I theta)
    (f : (↑F.base : Type) → ℝ) :
    ∑ J ∈ nearBaseIntervals F theta, f J = f ⟨I, hI⟩ := by
  rw [nearBaseIntervals_eq_singleton_of_mem hn F hI htheta]
  simp

/-- A sum over near intervals outside the union costs at most two copies of
a uniform pointwise bound. -/
theorem abs_sum_nearIntervals_le_two_mul_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta C : ℝ}
    (hout : ¬InBaseUnion F theta) (hC : 0 ≤ C)
    (f : RealInterval → ℝ)
    (hf : ∀ I ∈ nearIntervals F theta, |f I| ≤ C) :
    |∑ I ∈ nearIntervals F theta, f I| ≤ 2 * C := by
  classical
  have hcard := card_nearIntervals_le_two_of_not_inBaseUnion hn F hout
  calc
    |∑ I ∈ nearIntervals F theta, f I| ≤
        ∑ I ∈ nearIntervals F theta, |f I| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I ∈ nearIntervals F theta, C := by
      exact Finset.sum_le_sum fun I hI ↦ hf I hI
    _ = ((nearIntervals F theta).card : ℝ) * C := by simp
    _ ≤ 2 * C := by
      gcongr
      exact_mod_cast hcard

/-- Subtype-indexed two-term sum bound used by the kernel assembly. -/
theorem abs_sum_nearBaseIntervals_le_two_mul_of_not_inBaseUnion {n : ℕ}
    (hn : 0 < n) (F : SuitableIntervalFamily n) {theta C : ℝ}
    (hout : ¬InBaseUnion F theta) (hC : 0 ≤ C)
    (f : (↑F.base : Type) → ℝ)
    (hf : ∀ I ∈ nearBaseIntervals F theta, |f I| ≤ C) :
    |∑ I ∈ nearBaseIntervals F theta, f I| ≤ 2 * C := by
  classical
  have hcard := card_nearBaseIntervals_le_two_of_not_inBaseUnion hn F hout
  calc
    |∑ I ∈ nearBaseIntervals F theta, f I| ≤
        ∑ I ∈ nearBaseIntervals F theta, |f I| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _I ∈ nearBaseIntervals F theta, C := by
      exact Finset.sum_le_sum fun I hI ↦ hf I hI
    _ = ((nearBaseIntervals F theta).card : ℝ) * C := by simp
    _ ≤ 2 * C := by
      gcongr
      exact_mod_cast hcard

end

end Erdos228.KernelNearGeometry
