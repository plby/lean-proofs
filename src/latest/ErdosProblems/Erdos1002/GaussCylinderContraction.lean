import ErdosProblems.Erdos1002.GaussDynamics
import ErdosProblems.Erdos1002.GaussPrefixApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform contraction of continued-fraction cylinders

Every regular continued-fraction digit is positive.  A single inverse Gauss
branch is nonexpanding on `[0,1]`, and every *pair* of inverse branches is
uniformly `1/4`-Lipschitz.  Iterating this elementary estimate gives an
explicit exponential diameter bound for every prefix cylinder.  This is the
quantitative input needed when the Lebesgue-to-Gauss density is replaced by a
function measurable with respect to a finite digit prefix.
-/

open Filter Set
open scoped Topology

namespace Erdos1002

noncomputable section

/-- Composition of the inverse branches encoded by a digit word.  The head
digit is the outermost inverse branch, as in the usual continued-fraction
cylinder parametrization. -/
def gaussInverseWord : List ℕ → ℝ → ℝ
  | [], x => x
  | q :: qs, x => gaussInverseBranch q (gaussInverseWord qs x)

/-- Number of disjoint adjacent pairs in a digit word.  Defining this
structurally avoids hiding any arithmetic in the induction below. -/
def gaussWordPairDepth : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | _ :: _ :: qs => gaussWordPairDepth qs + 1

theorem gaussWordPairDepth_eq_length_div_two (qs : List ℕ) :
    gaussWordPairDepth qs = qs.length / 2 := by
  induction qs using List.twoStepInduction with
  | nil => simp [gaussWordPairDepth]
  | singleton q => simp [gaussWordPairDepth]
  | cons_cons q r qs ih =>
      simp only [gaussWordPairDepth, List.length_cons, ih]
      omega

/-- Exact difference formula for one inverse branch. -/
theorem abs_gaussInverseBranch_sub
    (q : ℕ) (hq : 0 < q) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInverseBranch q x - gaussInverseBranch q y| =
      |x - y| / (((q : ℝ) + x) * ((q : ℝ) + y)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxden : 0 < (q : ℝ) + x := add_pos_of_pos_of_nonneg hqR hx
  have hyden : 0 < (q : ℝ) + y := add_pos_of_pos_of_nonneg hqR hy
  unfold gaussInverseBranch
  rw [show 1 / ((q : ℝ) + x) - 1 / ((q : ℝ) + y) =
      (y - x) / (((q : ℝ) + x) * ((q : ℝ) + y)) by
        field_simp
        ring,
    abs_div, abs_mul, abs_of_pos hxden, abs_of_pos hyden,
    abs_sub_comm]

/-- Every positive inverse branch preserves the closed unit interval. -/
theorem gaussInverseBranch_mem_Icc
    (q : ℕ) (hq : 0 < q) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    gaussInverseBranch q x ∈ Icc (0 : ℝ) 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold gaussInverseBranch
  constructor
  · exact (one_div_pos.mpr (add_pos_of_pos_of_nonneg hqR hx.1)).le
  · apply (div_le_one (add_pos_of_pos_of_nonneg hqR hx.1)).2
    exact hqOne.trans (le_add_of_nonneg_right hx.1)

/-- A single positive inverse branch is nonexpanding on `[0,1]`. -/
theorem dist_gaussInverseBranch_le
    (q : ℕ) (hq : 0 < q) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist (gaussInverseBranch q x) (gaussInverseBranch q y) ≤ dist x y := by
  rw [Real.dist_eq, Real.dist_eq,
    abs_gaussInverseBranch_sub q hq hx.1 hy.1]
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 1 ≤ ((q : ℝ) + x) * ((q : ℝ) + y) := by
    nlinarith [hx.1, hy.1]
  exact div_le_self (abs_nonneg _) hden

/-- Two adjacent positive inverse branches contract distances by at least a
factor `1/4`, uniformly in both digits. -/
theorem dist_gaussInverseBranch_pair_le
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist (gaussInverseBranch q (gaussInverseBranch r x))
        (gaussInverseBranch q (gaussInverseBranch r y)) ≤
      (1 / 4 : ℝ) * dist x y := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqx : 0 < (q : ℝ) * ((r : ℝ) + x) + 1 := by
    nlinarith [hx.1]
  have hqy : 0 < (q : ℝ) * ((r : ℝ) + y) + 1 := by
    nlinarith [hy.1]
  rw [Real.dist_eq, Real.dist_eq]
  unfold gaussInverseBranch
  rw [show 1 / ((q : ℝ) + 1 / ((r : ℝ) + x)) -
      1 / ((q : ℝ) + 1 / ((r : ℝ) + y)) =
      (x - y) /
        (((q : ℝ) * ((r : ℝ) + x) + 1) *
          ((q : ℝ) * ((r : ℝ) + y) + 1)) by
        have hxden : (r : ℝ) + x ≠ 0 := ne_of_gt (by nlinarith [hx.1])
        have hyden : (r : ℝ) + y ≠ 0 := ne_of_gt (by nlinarith [hy.1])
        field_simp
        ring,
    abs_div, abs_mul, abs_of_pos hqx, abs_of_pos hqy]
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden :
      4 ≤ ((q : ℝ) * ((r : ℝ) + x) + 1) *
        ((q : ℝ) * ((r : ℝ) + y) + 1) := by
    have hrx : (1 : ℝ) ≤ (r : ℝ) + x :=
      hrOne.trans (le_add_of_nonneg_right hx.1)
    have hry : (1 : ℝ) ≤ (r : ℝ) + y :=
      hrOne.trans (le_add_of_nonneg_right hy.1)
    have hfacx : (2 : ℝ) ≤ (q : ℝ) * ((r : ℝ) + x) + 1 := by
      have := one_le_mul_of_one_le_of_one_le hqOne hrx
      linarith
    have hfacy : (2 : ℝ) ≤ (q : ℝ) * ((r : ℝ) + y) + 1 := by
      have := one_le_mul_of_one_le_of_one_le hqOne hry
      linarith
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hfacx) (sub_nonneg.mpr hfacy)]
  have hnonneg : 0 ≤ |x - y| := abs_nonneg _
  calc
    |x - y| /
        (((q : ℝ) * ((r : ℝ) + x) + 1) *
          ((q : ℝ) * ((r : ℝ) + y) + 1))
        ≤ |x - y| / 4 := div_le_div_of_nonneg_left hnonneg (by positivity) hden
    _ = (1 / 4 : ℝ) * |x - y| := by ring

/-- A positive digit word maps the closed unit interval into itself. -/
theorem gaussInverseWord_mem_Icc
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    gaussInverseWord qs x ∈ Icc (0 : ℝ) 1 := by
  induction qs with
  | nil => simpa [gaussInverseWord] using! hx
  | cons q qs ih =>
      simp only [gaussInverseWord]
      apply gaussInverseBranch_mem_Icc q (hpos q (by simp))
      apply ih
      intro r hr
      exact hpos r (by simp [hr])

/-- Uniform exponential diameter bound for every positive digit word. -/
theorem dist_gaussInverseWord_le
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist (gaussInverseWord qs x) (gaussInverseWord qs y) ≤
      (1 / 4 : ℝ) ^ gaussWordPairDepth qs * dist x y := by
  induction qs using List.twoStepInduction generalizing x y with
  | nil => simp [gaussInverseWord, gaussWordPairDepth]
  | singleton q =>
      simpa [gaussInverseWord, gaussWordPairDepth] using!
        dist_gaussInverseBranch_le q (hpos q (by simp)) hx hy
  | cons_cons q r qs ih =>
      have hq : 0 < q := hpos q (by simp)
      have hr : 0 < r := hpos r (by simp)
      have htail : ∀ s ∈ qs, 0 < s := by
        intro s hs
        exact hpos s (by simp [hs])
      have hxi := gaussInverseWord_mem_Icc htail hx
      have hyi := gaussInverseWord_mem_Icc htail hy
      calc
        dist (gaussInverseWord (q :: r :: qs) x)
            (gaussInverseWord (q :: r :: qs) y)
            ≤ (1 / 4 : ℝ) *
                dist (gaussInverseWord qs x) (gaussInverseWord qs y) := by
              simpa only [gaussInverseWord] using!
                dist_gaussInverseBranch_pair_le q r hq hr hxi hyi
        _ ≤ (1 / 4 : ℝ) *
              ((1 / 4 : ℝ) ^ gaussWordPairDepth qs * dist x y) :=
            mul_le_mul_of_nonneg_left (ih htail hx hy) (by positivity)
        _ = (1 / 4 : ℝ) ^ gaussWordPairDepth (q :: r :: qs) * dist x y := by
            simp only [gaussWordPairDepth, pow_succ]
            ring

/-- Length form of the preceding estimate. -/
theorem dist_gaussInverseWord_le_length
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist (gaussInverseWord qs x) (gaussInverseWord qs y) ≤
      (1 / 4 : ℝ) ^ (qs.length / 2) * dist x y := by
  rw [← gaussWordPairDepth_eq_length_div_two]
  exact dist_gaussInverseWord_le hpos hx hy

/-- The affine Lebesgue-to-Gauss transfer weight therefore has an explicit
uniform error on every length-`b` prefix cylinder. -/
theorem abs_gaussLebesguePrefixWeight_gaussInverseWord_sub_le
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |gaussLebesguePrefixWeight (gaussInverseWord qs x) -
        gaussLebesguePrefixWeight (gaussInverseWord qs y)| ≤
      Real.log 2 * (1 / 4 : ℝ) ^ (qs.length / 2) := by
  apply abs_gaussLebesguePrefixWeight_sub_le_of_dist
  calc
    dist (gaussInverseWord qs x) (gaussInverseWord qs y)
        ≤ (1 / 4 : ℝ) ^ (qs.length / 2) * dist x y :=
      dist_gaussInverseWord_le_length hpos hx hy
    _ ≤ (1 / 4 : ℝ) ^ (qs.length / 2) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [Real.dist_eq]
        exact abs_sub_le_iff.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
      · positivity
    _ = (1 / 4 : ℝ) ^ (qs.length / 2) := mul_one _

/-- The closed cylinder parametrized by a positive digit word.  Endpoint
choices can later be changed on a finite set without altering Gauss or
Lebesgue measure. -/
def closedGaussPrefixCylinder (qs : List ℕ) : Set ℝ :=
  gaussInverseWord qs '' Icc (0 : ℝ) 1

theorem closedGaussPrefixCylinder_nonempty (qs : List ℕ) :
    (closedGaussPrefixCylinder qs).Nonempty := by
  refine ⟨gaussInverseWord qs 0, ?_⟩
  exact ⟨0, by simp, rfl⟩

theorem closedGaussPrefixCylinder_subset_unit
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q) :
    closedGaussPrefixCylinder qs ⊆ Icc (0 : ℝ) 1 := by
  rintro z ⟨x, hx, rfl⟩
  exact gaussInverseWord_mem_Icc hpos hx

/-- Fully explicit diameter statement: any two points in the same length-`b`
closed cylinder are at distance at most `4⁻⌊b/2⌋`. -/
theorem dist_le_of_mem_closedGaussPrefixCylinder
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {u v : ℝ} (hu : u ∈ closedGaussPrefixCylinder qs)
    (hv : v ∈ closedGaussPrefixCylinder qs) :
    dist u v ≤ (1 / 4 : ℝ) ^ (qs.length / 2) := by
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨y, hy, rfl⟩
  calc
    dist (gaussInverseWord qs x) (gaussInverseWord qs y)
        ≤ (1 / 4 : ℝ) ^ (qs.length / 2) * dist x y :=
      dist_gaussInverseWord_le_length hpos hx hy
    _ ≤ (1 / 4 : ℝ) ^ (qs.length / 2) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [Real.dist_eq]
        exact abs_sub_le_iff.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
      · positivity
    _ = (1 / 4 : ℝ) ^ (qs.length / 2) := mul_one _

/-- Corresponding oscillation estimate for the exact transfer density on a
closed prefix cylinder. -/
theorem abs_gaussLebesguePrefixWeight_sub_le_of_mem_closedCylinder
    {qs : List ℕ} (hpos : ∀ q ∈ qs, 0 < q)
    {u v : ℝ} (hu : u ∈ closedGaussPrefixCylinder qs)
    (hv : v ∈ closedGaussPrefixCylinder qs) :
    |gaussLebesguePrefixWeight u - gaussLebesguePrefixWeight v| ≤
      Real.log 2 * (1 / 4 : ℝ) ^ (qs.length / 2) := by
  exact abs_gaussLebesguePrefixWeight_sub_le_of_dist
    (dist_le_of_mem_closedGaussPrefixCylinder hpos hu hv)

/-- The explicit cylinder oscillation bound tends to zero with the prefix
length; no qualitative compactness argument is being hidden here. -/
theorem tendsto_gaussPrefixCylinderWeightOscillation :
    Tendsto
      (fun b : ℕ ↦ Real.log 2 * (1 / 4 : ℝ) ^ (b / 2))
      atTop (𝓝 0) := by
  have hdiv : Tendsto (fun b : ℕ ↦ b / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hpow : Tendsto (fun b : ℕ ↦ (1 / 4 : ℝ) ^ (b / 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)).comp hdiv
  simpa only [mul_zero] using! tendsto_const_nhds.mul hpow

/-- Sequence form used when the chosen prefix length depends on the main
asymptotic parameter. -/
theorem tendsto_gaussPrefixCylinderWeightOscillation_comp
    {b : ℕ → ℕ} (hb : Tendsto b atTop atTop) :
    Tendsto
      (fun N : ℕ ↦ Real.log 2 * (1 / 4 : ℝ) ^ (b N / 2))
      atTop (𝓝 0) :=
  tendsto_gaussPrefixCylinderWeightOscillation.comp hb

end

end Erdos1002
