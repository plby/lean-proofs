import ErdosProblems.Erdos1002.GaussCylinderContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Measurable partitions by finite Gauss prefixes

Finite continued-fraction prefixes require an explicit endpoint convention.
We use the usual half-open tail `[0,1)`.  Thus a nonempty word gives exactly
the recursive cylinder obtained by intersecting a first-digit cylinder with
the pullback of the tail cylinder.  Distinct positive words of the same
length are genuinely disjoint.

Rationals whose expansion terminates before the requested length cannot have
a positive word of that length.  Rather than silently assign them a second
continued-fraction expansion, we isolate them in a measurable exceptional
set and prove that this set has both Gauss and Lebesgue measure zero.  This
gives the exact partition interface used by prefix-measurable approximation.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

/-! ## Positive words and half-open cylinders -/

/-- Positive digit words of one fixed length. -/
def PositiveDigitWord (b : ℕ) :=
  {qs : List ℕ // qs.length = b ∧ ∀ q ∈ qs, 0 < q}

instance (b : ℕ) : Countable (PositiveDigitWord b) := by
  unfold PositiveDigitWord
  infer_instance

/-- The all-one word supplies a canonical inhabitant at every length. -/
def defaultPositiveDigitWord (b : ℕ) : PositiveDigitWord b :=
  ⟨List.replicate b 1, by simp, by simp⟩

instance (b : ℕ) : Inhabited (PositiveDigitWord b) :=
  ⟨defaultPositiveDigitWord b⟩

/-- Recursive half-open prefix cylinder.  The empty tail is `[0,1)`, and a
new digit is imposed by the disjoint first-digit partition. -/
def gaussHalfOpenPrefixCylinder : List ℕ → Set ℝ
  | [] => Ico (0 : ℝ) 1
  | q :: qs => firstDigitCylinder q ∩
      gaussMap ⁻¹' gaussHalfOpenPrefixCylinder qs

theorem measurableSet_gaussHalfOpenPrefixCylinder (qs : List ℕ) :
    MeasurableSet (gaussHalfOpenPrefixCylinder qs) := by
  induction qs with
  | nil => exact measurableSet_Ico
  | cons q qs ih =>
      exact measurableSet_Ioc.inter
        (ih.preimage measurable_gaussMap)

theorem gaussHalfOpenPrefixCylinder_subset_closed
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q) :
    gaussHalfOpenPrefixCylinder qs ⊆ closedGaussPrefixCylinder qs := by
  induction qs with
  | nil =>
      intro x hx
      exact ⟨x, ⟨hx.1, hx.2.le⟩, by simp [gaussInverseWord]⟩
  | cons q qs ih =>
      intro x hx
      have hq : 0 < q := hpos q (by simp)
      have htail : ∀ r ∈ qs, 0 < r := by
        intro r hr
        exact hpos r (by simp [hr])
      obtain ⟨y, hy, hyeq⟩ := ih htail hx.2
      refine ⟨y, hy, ?_⟩
      change gaussInverseBranch q (gaussInverseWord qs y) = x
      rw [hyeq]
      exact gaussInverseBranch_gaussMap hq hx.1

/-- An inverse word sends an interior tail point to an interior unit point. -/
theorem gaussInverseWord_mem_Ioo
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    gaussInverseWord qs x ∈ Ioo (0 : ℝ) 1 := by
  induction qs with
  | nil => simpa [gaussInverseWord] using! hx
  | cons q qs ih =>
      have hq : 0 < q := hpos q (by simp)
      have htail : ∀ r ∈ qs, 0 < r := by
        intro r hr
        exact hpos r (by simp [hr])
      have hy := ih htail
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      change 0 < 1 / ((q : ℝ) + gaussInverseWord qs x) ∧
        1 / ((q : ℝ) + gaussInverseWord qs x) < 1
      constructor
      · exact one_div_pos.mpr (by linarith [hy.1])
      · apply (div_lt_one (by linarith [hy.1])).2
        linarith [hy.1, hqOne]

/-- The inverse-word image of zero is a representative which genuinely
belongs to the half-open cylinder. -/
def gaussPrefixRepresentative (qs : List ℕ) : ℝ :=
  gaussInverseWord qs (1 / 2)

theorem gaussPrefixRepresentative_mem
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q) :
    gaussPrefixRepresentative qs ∈ gaussHalfOpenPrefixCylinder qs := by
  induction qs with
  | nil => norm_num [gaussPrefixRepresentative, gaussHalfOpenPrefixCylinder,
      gaussInverseWord]
  | cons q qs ih =>
      have hq : 0 < q := hpos q (by simp)
      have htail : ∀ r ∈ qs, 0 < r := by
        intro r hr
        exact hpos r (by simp [hr])
      have htailmem := ih htail
      have htailIoo := gaussInverseWord_mem_Ioo htail
        (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
      have htailIco : gaussInverseWord qs (1 / 2) ∈ Ico (0 : ℝ) 1 :=
        ⟨htailIoo.1.le, htailIoo.2⟩
      constructor
      · exact gaussInverseBranch_mem_firstDigitCylinder htailIco q hq
      · change gaussMap
          (gaussInverseBranch q (gaussInverseWord qs (1 / 2))) ∈
            gaussHalfOpenPrefixCylinder qs
        rw [gaussMap_gaussInverseBranch htailIco q hq]
        exact htailmem

/-- Equal-length distinct positive words give disjoint half-open cylinders. -/
theorem disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
    {qs rs : List ℕ} (hlen : qs.length = rs.length)
    (hqpos : ∀ q ∈ qs, 0 < q) (hrpos : ∀ r ∈ rs, 0 < r)
    (hne : qs ≠ rs) :
    Disjoint (gaussHalfOpenPrefixCylinder qs)
      (gaussHalfOpenPrefixCylinder rs) := by
  induction qs generalizing rs with
  | nil =>
      cases rs with
      | nil => exact (hne rfl).elim
      | cons r rs => simp at hlen
  | cons q qs ih =>
      cases rs with
      | nil => simp at hlen
      | cons r rs =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          by_cases hqr : q = r
          · subst r
            have htailne : qs ≠ rs := by
              intro h
              exact hne (by simp [h])
            have htail := ih hlen
              (fun s hs ↦ hqpos s (by simp [hs]))
              (fun s hs ↦ hrpos s (by simp [hs])) htailne
            rw [Set.disjoint_left]
            intro x hxq hxr
            exact (Set.disjoint_left.mp htail hxq.2) hxr.2
          · rw [Set.disjoint_left]
            intro x hxq hxr
            have hqunit := firstDigitCylinder_subset_unit q
              (hqpos q (by simp)) hxq.1
            have hdq :=
              (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hqunit q
                (hqpos q (by simp))).2 hxq.1
            have hdru := firstDigitCylinder_subset_unit r
              (hrpos r (by simp)) hxr.1
            have hdr :=
              (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hdru r
                (hrpos r (by simp))).2 hxr.1
            have hcast : (q : ℤ) = (r : ℤ) := hdq.symm.trans hdr
            exact hqr (by exact_mod_cast hcast)

/-! ## The countable partition and its terminating exceptional set -/

def positivePrefixCylinder (b : ℕ) (w : PositiveDigitWord b) : Set ℝ :=
  gaussHalfOpenPrefixCylinder w.1

theorem measurableSet_positivePrefixCylinder
    (b : ℕ) (w : PositiveDigitWord b) :
    MeasurableSet (positivePrefixCylinder b w) :=
  measurableSet_gaussHalfOpenPrefixCylinder w.1

theorem pairwise_disjoint_positivePrefixCylinder (b : ℕ) :
    Pairwise fun w v : PositiveDigitWord b =>
      Disjoint (positivePrefixCylinder b w) (positivePrefixCylinder b v) := by
  intro w v hwv
  apply disjoint_gaussHalfOpenPrefixCylinder_of_sameLength
  · exact w.2.1.trans v.2.1.symm
  · exact w.2.2
  · exact v.2.2
  · intro h
    exact hwv (Subtype.ext h)

/-- Domain on which the first `b` positive digits exist. -/
def positivePrefixDomain (b : ℕ) : Set ℝ :=
  ⋃ w : PositiveDigitWord b, positivePrefixCylinder b w

theorem measurableSet_positivePrefixDomain (b : ℕ) :
    MeasurableSet (positivePrefixDomain b) := by
  exact MeasurableSet.iUnion fun w => measurableSet_positivePrefixCylinder b w

theorem existsUnique_mem_positivePrefixCylinder
    {b : ℕ} {x : ℝ} (hx : x ∈ positivePrefixDomain b) :
    ∃! w : PositiveDigitWord b, x ∈ positivePrefixCylinder b w := by
  rcases mem_iUnion.mp hx with ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  intro v hv
  by_contra hvw
  exact (Set.disjoint_left.mp
    (pairwise_disjoint_positivePrefixCylinder b hvw) hv) hw

/-- Points whose Gauss orbit reaches zero before digit `b`; these are exactly
the possible failures of a length-`b` positive prefix. -/
def gaussPrefixExceptional (b : ℕ) : Set ℝ :=
  (Ioc (0 : ℝ) 1 ∩
    ⋃ k : Fin b, (gaussMap^[k.1]) ⁻¹' ({0} : Set ℝ)) ∪ {1}

theorem measurableSet_gaussPrefixExceptional (b : ℕ) :
    MeasurableSet (gaussPrefixExceptional b) := by
  apply MeasurableSet.union
  · apply MeasurableSet.inter measurableSet_Ioc
    apply MeasurableSet.iUnion
    intro k
    exact (measurableSet_singleton 0).preimage
      (measurable_gaussMap.iterate k.1)
  · exact measurableSet_singleton 1

/-- Starting from a point in `[0,1)`, a nonterminating tail has a positive
word of every prescribed finite length. -/
theorem exists_positiveDigitWord_of_no_early_zero
    {b : ℕ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hzero : ∀ k < b, (gaussMap^[k]) x ≠ 0) :
    ∃ w : PositiveDigitWord b, x ∈ positivePrefixCylinder b w := by
  induction b generalizing x with
  | zero =>
      refine ⟨defaultPositiveDigitWord 0, ?_⟩
      simpa [positivePrefixCylinder, defaultPositiveDigitWord,
        gaussHalfOpenPrefixCylinder] using! hx
  | succ b ih =>
      have hx0 : x ≠ 0 := hzero 0 (by omega)
      have hxIoc : x ∈ Ioc (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2.le⟩
      have hxUnion : x ∈ ⋃ n : ℕ, firstDigitCylinder (n + 1) := by
        rw [iUnion_firstDigitCylinder]
        exact hxIoc
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxUnion
      let q := n + 1
      have hq : 0 < q := by omega
      have hyIco : gaussMap x ∈ Ico (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      have htailzero : ∀ k < b, (gaussMap^[k]) (gaussMap x) ≠ 0 := by
        intro k hk
        rw [← Function.iterate_succ_apply]
        exact hzero (k + 1) (by omega)
      obtain ⟨v, hv⟩ := ih hyIco htailzero
      let w : PositiveDigitWord (b + 1) :=
        ⟨q :: v.1, by simp [v.2.1], by
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hq
          · exact v.2.2 r hr⟩
      refine ⟨w, ?_⟩
      exact ⟨hn, hv⟩

theorem unit_diff_positivePrefixDomain_subset_exceptional (b : ℕ) :
    Ioc (0 : ℝ) 1 \ positivePrefixDomain b ⊆ gaussPrefixExceptional b := by
  intro x hx
  by_contra hnot
  have hxne1 : x ≠ 1 := by
    intro h
    apply hnot
    exact Or.inr h
  have hxIco : x ∈ Ico (0 : ℝ) 1 :=
    ⟨hx.1.1.le, lt_of_le_of_ne hx.1.2 hxne1⟩
  have hzero : ∀ k < b, (gaussMap^[k]) x ≠ 0 := by
    intro k hk heq
    apply hnot
    left
    refine ⟨hx.1, mem_iUnion.2 ⟨⟨k, hk⟩, ?_⟩⟩
    simpa only [mem_preimage, mem_singleton_iff] using! heq
  obtain ⟨w, hw⟩ := exists_positiveDigitWord_of_no_early_zero hxIco hzero
  exact hx.2 (mem_iUnion.2 ⟨w, hw⟩)

/-! ## The exceptional set is null -/

theorem map_gaussMap_iterate_gaussMeasure (k : ℕ) :
    Measure.map (gaussMap^[k]) gaussMeasure = gaussMeasure := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ]
      rw [← Measure.map_map (measurable_gaussMap.iterate k) measurable_gaussMap,
        map_gaussMap_gaussMeasure, ih]

theorem gaussMeasure_preimage_iterate_singleton_zero (k : ℕ) :
    gaussMeasure ((gaussMap^[k]) ⁻¹' ({0} : Set ℝ)) = 0 := by
  have h := congrArg (fun μ : Measure ℝ => μ ({0} : Set ℝ))
    (map_gaussMap_iterate_gaussMeasure k)
  change (Measure.map (gaussMap^[k]) gaussMeasure) ({0} : Set ℝ) =
    gaussMeasure ({0} : Set ℝ) at h
  rw [Measure.map_apply (measurable_gaussMap.iterate k)
    (measurableSet_singleton 0), gaussMeasure_singleton] at h
  exact h

theorem gaussMeasure_gaussPrefixExceptional (b : ℕ) :
    gaussMeasure (gaussPrefixExceptional b) = 0 := by
  apply MeasureTheory.measure_union_null
  · apply MeasureTheory.measure_mono_null inter_subset_right
    exact MeasureTheory.measure_iUnion_null fun k =>
      gaussMeasure_preimage_iterate_singleton_zero k.1
  · exact gaussMeasure_singleton 1

theorem volume_gaussPrefixExceptional (b : ℕ) :
    volume (gaussPrefixExceptional b) = 0 := by
  have hweighted :
      gaussMeasure.withDensity lebesgueOverGaussDensity
          (gaussPrefixExceptional b) = 0 :=
    (withDensity_absolutelyContinuous gaussMeasure
      lebesgueOverGaussDensity) (gaussMeasure_gaussPrefixExceptional b)
  rw [gaussMeasure_withDensity_lebesgueOverGaussDensity,
    Measure.restrict_apply (measurableSet_gaussPrefixExceptional b)] at hweighted
  have hsub : gaussPrefixExceptional b ⊆ Ioc (0 : ℝ) 1 := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · have hx1 : x = 1 := by simpa only [mem_singleton_iff] using! hx
      subst x
      norm_num
  simpa [inter_eq_left.mpr hsub] using! hweighted

theorem volume_unit_diff_positivePrefixDomain (b : ℕ) :
    volume (Ioc (0 : ℝ) 1 \ positivePrefixDomain b) = 0 :=
  MeasureTheory.measure_mono_null
    (unit_diff_positivePrefixDomain_subset_exceptional b)
    (volume_gaussPrefixExceptional b)

/-! ## An exact partition of `(0,1]` -/

/-- The extra `none` cell contains precisely the terminating endpoints which
do not possess a positive word of the requested length. -/
abbrev GaussPrefixPartitionIndex (b : ℕ) := Option (PositiveDigitWord b)

def gaussPrefixPartitionCell (b : ℕ) :
    GaussPrefixPartitionIndex b → Set ℝ
  | none => Ioc (0 : ℝ) 1 \ positivePrefixDomain b
  | some w => Ioc (0 : ℝ) 1 ∩ positivePrefixCylinder b w

theorem measurableSet_gaussPrefixPartitionCell
    (b : ℕ) (i : GaussPrefixPartitionIndex b) :
    MeasurableSet (gaussPrefixPartitionCell b i) := by
  cases i with
  | none =>
      exact measurableSet_Ioc.diff (measurableSet_positivePrefixDomain b)
  | some w =>
      exact measurableSet_Ioc.inter (measurableSet_positivePrefixCylinder b w)

theorem pairwise_disjoint_gaussPrefixPartitionCell (b : ℕ) :
    Pairwise fun i j : GaussPrefixPartitionIndex b =>
      Disjoint (gaussPrefixPartitionCell b i)
        (gaussPrefixPartitionCell b j) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some w =>
          rw [Set.disjoint_left]
          intro x hxnone hxw
          exact hxnone.2 (mem_iUnion.2 ⟨w, hxw.2⟩)
  | some v =>
      cases j with
      | none =>
          rw [Set.disjoint_left]
          intro x hxv hxnone
          exact hxnone.2 (mem_iUnion.2 ⟨v, hxv.2⟩)
      | some w =>
          have hvw : v ≠ w := by
            intro hvw
            exact hij (by simp [hvw])
          exact (pairwise_disjoint_positivePrefixCylinder b hvw).mono
            inter_subset_right inter_subset_right

/-- The word cells together with the terminating cell cover `(0,1]`
exactly, not merely almost everywhere. -/
theorem iUnion_gaussPrefixPartitionCell (b : ℕ) :
    (⋃ i : GaussPrefixPartitionIndex b, gaussPrefixPartitionCell b i) =
      Ioc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hi⟩
    cases i with
    | none => exact hi.1
    | some w => exact hi.1
  · intro hx
    by_cases hdom : x ∈ positivePrefixDomain b
    · obtain ⟨w, hw, _⟩ := existsUnique_mem_positivePrefixCylinder hdom
      exact mem_iUnion.2 ⟨some w, hx, hw⟩
    · exact mem_iUnion.2 ⟨none, hx, hdom⟩

theorem existsUnique_mem_gaussPrefixPartitionCell
    (b : ℕ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∃! i : GaussPrefixPartitionIndex b,
      x ∈ gaussPrefixPartitionCell b i := by
  have hcover : x ∈ ⋃ i : GaussPrefixPartitionIndex b,
      gaussPrefixPartitionCell b i := by
    rw [iUnion_gaussPrefixPartitionCell b]
    exact hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact (Set.disjoint_left.mp
    (pairwise_disjoint_gaussPrefixPartitionCell b hji) hj) hi

/-- The sole non-word cell in the exact partition is Lebesgue-null. -/
theorem volume_gaussPrefixPartitionCell_none (b : ℕ) :
    volume (gaussPrefixPartitionCell b none) = 0 :=
  volume_unit_diff_positivePrefixDomain b

/-! ## Countably piecewise prefix-weight approximation -/

theorem gaussPrefixRepresentative_mem_positivePrefixCylinder
    (b : ℕ) (w : PositiveDigitWord b) :
    gaussPrefixRepresentative w.1 ∈ positivePrefixCylinder b w :=
  gaussPrefixRepresentative_mem w.2.2

theorem prefixWeight_error_at_representative
    (b : ℕ) (w : PositiveDigitWord b) {x : ℝ}
    (hx : x ∈ positivePrefixCylinder b w) :
    |gaussLebesguePrefixWeight x -
        gaussLebesguePrefixWeight (gaussPrefixRepresentative w.1)| ≤
      Real.log 2 * (1 / 4 : ℝ) ^ (b / 2) := by
  have hxclosed := gaussHalfOpenPrefixCylinder_subset_closed w.2.2 hx
  have hcenter := gaussHalfOpenPrefixCylinder_subset_closed w.2.2
    (gaussPrefixRepresentative_mem w.2.2)
  simpa [w.2.1] using!
    abs_gaussLebesguePrefixWeight_sub_le_of_mem_closedCylinder
      w.2.2 hxclosed hcenter

/-- There is a globally measurable, countably piecewise-constant function
which takes the representative weight on every length-`b` cylinder. -/
theorem exists_measurable_gaussPrefixWeightApproximation (b : ℕ) :
    ∃ g : ℝ → ℝ, Measurable g ∧
      ∀ w : PositiveDigitWord b, ∀ x ∈ positivePrefixCylinder b w,
        g x = gaussLebesguePrefixWeight (gaussPrefixRepresentative w.1) := by
  let C : PositiveDigitWord b → Set ℝ := positivePrefixCylinder b
  let G : PositiveDigitWord b → ℝ → ℝ := fun w _ =>
    gaussLebesguePrefixWeight (gaussPrefixRepresentative w.1)
  obtain ⟨g, hg, hagree⟩ := exists_measurable_piecewise C
    (fun w => measurableSet_positivePrefixCylinder b w) G
    (fun _ => measurable_const) (by
      intro w v hwv x hx
      exact ((Set.disjoint_left.mp
        (pairwise_disjoint_positivePrefixCylinder b hwv)) hx.1 hx.2).elim)
  refine ⟨g, hg, ?_⟩
  intro w x hx
  exact hagree w hx

/-- A canonical choice of the preceding measurable approximation. -/
def gaussPrefixWeightApproximation (b : ℕ) : ℝ → ℝ :=
  Classical.choose (exists_measurable_gaussPrefixWeightApproximation b)

theorem measurable_gaussPrefixWeightApproximation (b : ℕ) :
    Measurable (gaussPrefixWeightApproximation b) :=
  (Classical.choose_spec (exists_measurable_gaussPrefixWeightApproximation b)).1

theorem gaussPrefixWeightApproximation_eq_on_cell
    (b : ℕ) (w : PositiveDigitWord b) {x : ℝ}
    (hx : x ∈ positivePrefixCylinder b w) :
    gaussPrefixWeightApproximation b x =
      gaussLebesguePrefixWeight (gaussPrefixRepresentative w.1) :=
  (Classical.choose_spec
    (exists_measurable_gaussPrefixWeightApproximation b)).2 w x hx

/-- Uniform pointwise error on the entire nonexceptional prefix domain. -/
theorem abs_gaussPrefixWeightApproximation_sub_le
    (b : ℕ) {x : ℝ} (hx : x ∈ positivePrefixDomain b) :
    |gaussPrefixWeightApproximation b x - gaussLebesguePrefixWeight x| ≤
      Real.log 2 * (1 / 4 : ℝ) ^ (b / 2) := by
  obtain ⟨w, hw, _⟩ := existsUnique_mem_positivePrefixCylinder hx
  rw [gaussPrefixWeightApproximation_eq_on_cell b w hw, abs_sub_comm]
  exact prefixWeight_error_at_representative b w hw

/-- Epsilon form of convergence of the uniform (equivalently, supremum)
error over every length-`b` prefix domain. -/
theorem eventually_uniform_gaussPrefixWeightApproximation
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ b : ℕ in atTop, ∀ x ∈ positivePrefixDomain b,
      |gaussPrefixWeightApproximation b x - gaussLebesguePrefixWeight x| < η := by
  have hevent : ∀ᶠ b : ℕ in atTop,
      Real.log 2 * (1 / 4 : ℝ) ^ (b / 2) < η :=
    (tendsto_order.1 tendsto_gaussPrefixCylinderWeightOscillation).2 _ hη
  filter_upwards [hevent] with b hb
  intro x hx
  exact (abs_gaussPrefixWeightApproximation_sub_le b hx).trans_lt hb

end

end Erdos1002
