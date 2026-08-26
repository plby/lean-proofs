import ErdosProblems.Erdos1038.SublevelBoundary
import ErdosProblems.Erdos1038.EmpiricalMeasure
import ErdosProblems.Erdos1038.MeanOrientation
import ErdosProblems.Erdos1038.TaoUpperTwoAtomTrial

/-!
# A closed target set for Tao's quantile rearrangement

Mathlib defines `Real.log 0 = 0`, whereas Tao's logarithmic potential is
extended-real valued and equals `+∞` at an empirical root.  For the upper
argument we therefore use the closed polynomial set `{x | |f x| ≤ 1}`.
It differs from the strict sublevel set only by the finite level set
`|f x| = 1`, has exactly the same volume, and away from the finite root set
is exactly the nonnegative empirical-potential set.
-/

open scoped ENNReal
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

private theorem one_lt_multiset_map_prod
    {α : Type*} (s : Multiset α) (g : α → ℝ)
    (hs : s ≠ 0) (hg : ∀ x ∈ s, 1 < g x) :
    1 < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => exact False.elim (hs rfl)
  | @cons x s ih =>
      have hx : 1 < g x := hg x (by simp)
      by_cases hsEmpty : s = 0
      · subst s
        simpa using! hx
      · rw [Multiset.map_cons, Multiset.prod_cons]
        apply one_lt_mul_of_lt_of_le hx
        exact (ih hsEmpty (fun y hy ↦ hg y (by simp [hy]))).le

def closedUnitSublevelSet (f : Polynomial ℝ) : Set ℝ :=
  {x | |f.eval x| ≤ 1}

theorem isClosed_closedUnitSublevelSet (f : Polynomial ℝ) :
    IsClosed (closedUnitSublevelSet f) := by
  exact isClosed_le f.continuous.abs continuous_const

theorem closedUnitSublevelSet_rootReflection (f : Polynomial ℝ) :
    closedUnitSublevelSet (rootReflection f) =
      (fun x : ℝ ↦ -x) ⁻¹' closedUnitSublevelSet f := by
  ext x
  simp only [closedUnitSublevelSet, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [abs_eval_rootReflection]

theorem sublevelSet_subset_closedUnitSublevelSet (f : Polynomial ℝ) :
    sublevelSet f ⊆ closedUnitSublevelSet f := by
  intro x hx
  change |f.eval x| < 1 at hx
  change |f.eval x| ≤ 1
  exact hx.le

theorem closedUnitSublevelSet_diff_sublevelSet_subset_levelSet
    (f : Polynomial ℝ) :
    closedUnitSublevelSet f \ sublevelSet f ⊆
      {x | |f.eval x| = 1} := by
  intro x hx
  exact le_antisymm hx.1 (le_of_not_gt hx.2)

theorem unitLevelSet_subset_rootSet_sq_sub_one
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    {x | |f.eval x| = 1} ⊆ rootSet (f ^ 2 - 1) := by
  intro x hx
  rw [mem_rootSet_iff, Polynomial.mem_roots (sq_sub_one_ne_zero hf)]
  change (f ^ 2 - 1).eval x = 0
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one]
  have hsquare : (f.eval x) ^ 2 = 1 := by
    rw [← sq_abs, hx]
    norm_num
  linarith

theorem volume_closedUnitSublevelSet_diff_sublevelSet
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    volume (closedUnitSublevelSet f \ sublevelSet f) = 0 := by
  apply measure_mono_null
    (closedUnitSublevelSet_diff_sublevelSet_subset_levelSet f |>.trans
      (unitLevelSet_subset_rootSet_sq_sub_one hf))
  exact volume_rootSet (f ^ 2 - 1)

/-- Passing from `< 1` to `≤ 1` does not change the sublevel volume. -/
theorem volume_closedUnitSublevelSet
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    volume (closedUnitSublevelSet f) = sublevelVolume f := by
  rw [sublevelVolume]
  exact (measure_eq_measure_of_null_diff
    (sublevelSet_subset_closedUnitSublevelSet f)
    (volume_closedUnitSublevelSet_diff_sublevelSet hf)).symm

theorem closedUnitSublevelSet_subset_Icc
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    closedUnitSublevelSet f ⊆ Icc (-2 : ℝ) 2 := by
  intro x hx
  have hroots : f.roots ≠ 0 := roots_ne_zero hf
  constructor
  · apply le_of_not_gt
    intro hxLeft
    have hfactor : ∀ r ∈ f.roots, (1 : ℝ) < |x - r| := by
      intro r hr
      have hrIcc := hf.root_mem_Icc hr
      rw [abs_of_nonpos (by linarith [hrIcc.1])]
      linarith [hrIcc.1]
    have hprod := one_lt_multiset_map_prod f.roots
      (fun r ↦ |x - r|) hroots hfactor
    have habs : 1 < |f.eval x| := by
      rw [hf.abs_eval_eq_prod_abs_roots]
      simpa using! hprod
    exact (not_lt_of_ge hx) habs
  · apply le_of_not_gt
    intro hxRight
    have hfactor : ∀ r ∈ f.roots, (1 : ℝ) < |x - r| := by
      intro r hr
      have hrIcc := hf.root_mem_Icc hr
      rw [abs_of_nonneg (by linarith [hrIcc.2])]
      linarith [hrIcc.2]
    have hprod := one_lt_multiset_map_prod f.roots
      (fun r ↦ |x - r|) hroots hfactor
    have habs : 1 < |f.eval x| := by
      rw [hf.abs_eval_eq_prod_abs_roots]
      simpa using! hprod
    exact (not_lt_of_ge hx) habs

theorem isCompact_closedUnitSublevelSet
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    IsCompact (closedUnitSublevelSet f) :=
  isCompact_Icc.of_isClosed_subset
    (isClosed_closedUnitSublevelSet f)
    (closedUnitSublevelSet_subset_Icc hf)

theorem closedUnitSublevelSet_nonempty
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    (closedUnitSublevelSet f).Nonempty := by
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero (roots_ne_zero hf)
  refine ⟨r, ?_⟩
  change |f.eval r| ≤ 1
  rw [(Polynomial.mem_roots hf.monic.ne_zero).mp hr]
  norm_num

/-- Leftmost point of the closed unit sublevel set. -/
def closedUnitSublevelLeft (f : Polynomial ℝ) (hf : IsAdmissible f) : ℝ :=
  Classical.choose ((isCompact_closedUnitSublevelSet hf).exists_isLeast
    (closedUnitSublevelSet_nonempty hf))

/-- Rightmost point of the closed unit sublevel set. -/
def closedUnitSublevelRight (f : Polynomial ℝ) (hf : IsAdmissible f) : ℝ :=
  Classical.choose ((isCompact_closedUnitSublevelSet hf).exists_isGreatest
    (closedUnitSublevelSet_nonempty hf))

theorem closedUnitSublevelLeft_isLeast
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    IsLeast (closedUnitSublevelSet f) (closedUnitSublevelLeft f hf) :=
  Classical.choose_spec ((isCompact_closedUnitSublevelSet hf).exists_isLeast
    (closedUnitSublevelSet_nonempty hf))

theorem closedUnitSublevelRight_isGreatest
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    IsGreatest (closedUnitSublevelSet f) (closedUnitSublevelRight f hf) :=
  Classical.choose_spec ((isCompact_closedUnitSublevelSet hf).exists_isGreatest
    (closedUnitSublevelSet_nonempty hf))

theorem closedUnitSublevelSet_subset_endpoints
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    closedUnitSublevelSet f ⊆
      Icc (closedUnitSublevelLeft f hf) (closedUnitSublevelRight f hf) := by
  intro x hx
  exact ⟨(closedUnitSublevelLeft_isLeast hf).2 hx,
    (closedUnitSublevelRight_isGreatest hf).2 hx⟩

theorem closedUnitSublevelLeft_rootReflection
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    closedUnitSublevelLeft (rootReflection f) hf.reflection =
      -closedUnitSublevelRight f hf := by
  have hleast : IsLeast (closedUnitSublevelSet (rootReflection f))
      (-closedUnitSublevelRight f hf) := by
    constructor
    · rw [closedUnitSublevelSet_rootReflection]
      change -(-closedUnitSublevelRight f hf) ∈ closedUnitSublevelSet f
      simpa using! (closedUnitSublevelRight_isGreatest hf).1
    · intro x hx
      rw [closedUnitSublevelSet_rootReflection] at hx
      change -x ∈ closedUnitSublevelSet f at hx
      have hmax := (closedUnitSublevelRight_isGreatest hf).2 hx
      linarith
  exact (closedUnitSublevelLeft_isLeast hf.reflection).unique hleast

theorem closedUnitSublevelRight_rootReflection
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    closedUnitSublevelRight (rootReflection f) hf.reflection =
      -closedUnitSublevelLeft f hf := by
  have hgreatest : IsGreatest (closedUnitSublevelSet (rootReflection f))
      (-closedUnitSublevelLeft f hf) := by
    constructor
    · rw [closedUnitSublevelSet_rootReflection]
      change -(-closedUnitSublevelLeft f hf) ∈ closedUnitSublevelSet f
      simpa using! (closedUnitSublevelLeft_isLeast hf).1
    · intro x hx
      rw [closedUnitSublevelSet_rootReflection] at hx
      change -x ∈ closedUnitSublevelSet f at hx
      have hmin := (closedUnitSublevelLeft_isLeast hf).2 hx
      linarith
  exact (closedUnitSublevelRight_isGreatest hf.reflection).unique hgreatest

theorem closedUnitSublevel_diameter_gt_of_volume_gt
    {f : Polynomial ℝ} (hf : IsAdmissible f) {c : ℝ}
    (hc : 0 ≤ c)
    (hvolume : ENNReal.ofReal c < sublevelVolume f) :
    c < closedUnitSublevelRight f hf - closedUnitSublevelLeft f hf := by
  rw [← volume_closedUnitSublevelSet hf] at hvolume
  have hmeasure := measure_mono (μ := volume)
    (closedUnitSublevelSet_subset_endpoints hf)
  rw [Real.volume_Icc] at hmeasure
  have hofReal :
      ENNReal.ofReal c < ENNReal.ofReal
        (closedUnitSublevelRight f hf - closedUnitSublevelLeft f hf) :=
    hvolume.trans_le hmeasure
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc).mp hofReal

/-- If the closed target has volume greater than `2√2`, one of its two
extreme points lies farther than `√2` from the root-interval center. -/
theorem closedUnitSublevel_extreme_dichotomy
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hvolume : ENNReal.ofReal (2 * Real.sqrt 2) < sublevelVolume f) :
    closedUnitSublevelLeft f hf < -Real.sqrt 2 ∨
      Real.sqrt 2 < closedUnitSublevelRight f hf := by
  have hdiam := closedUnitSublevel_diameter_gt_of_volume_gt hf
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hvolume
  by_cases hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2
  · exact Or.inl hleft
  · right
    have hleft' : -Real.sqrt 2 ≤ closedUnitSublevelLeft f hf :=
      le_of_not_gt hleft
    linarith

/-- Reflection chooses an orientation whose leftmost closed-target point is
strictly farther than `√2` to the left, without changing sublevel volume. -/
theorem exists_left_oriented_of_volume_gt
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hvolume : ENNReal.ofReal (2 * Real.sqrt 2) < sublevelVolume f) :
    ∃ g : Polynomial ℝ, ∃ hg : IsAdmissible g,
      sublevelVolume g = sublevelVolume f ∧
        closedUnitSublevelLeft g hg < -Real.sqrt 2 := by
  rcases closedUnitSublevel_extreme_dichotomy hf hvolume with
    hleft | hright
  · exact ⟨f, hf, rfl, hleft⟩
  · refine ⟨rootReflection f, hf.reflection,
      sublevelVolume_rootReflection f, ?_⟩
    rw [closedUnitSublevelLeft_rootReflection hf]
    linarith

def leftNormalizedClosedTarget
    (f : Polynomial ℝ) (hf : IsAdmissible f) : Set ℝ :=
  {x | x + closedUnitSublevelLeft f hf ∈ closedUnitSublevelSet f}

def taoNormalizedCenter (f : Polynomial ℝ) (hf : IsAdmissible f) : ℝ :=
  -closedUnitSublevelLeft f hf

def taoNormalizedSourceLeft
    (f : Polynomial ℝ) (hf : IsAdmissible f) : ℝ :=
  taoNormalizedCenter f hf - 1

def taoNormalizedRightTarget
    (f : Polynomial ℝ) (hf : IsAdmissible f) : Set ℝ :=
  leftNormalizedClosedTarget f hf ∩ Ici (taoNormalizedSourceLeft f hf)

theorem isClosed_leftNormalizedClosedTarget
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    IsClosed (leftNormalizedClosedTarget f hf) := by
  exact (isClosed_closedUnitSublevelSet f).preimage
    (continuous_id.add continuous_const)

theorem volume_leftNormalizedClosedTarget
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    volume (leftNormalizedClosedTarget f hf) = sublevelVolume f := by
  rw [leftNormalizedClosedTarget]
  change volume ((fun x : ℝ ↦ x + closedUnitSublevelLeft f hf) ⁻¹'
    closedUnitSublevelSet f) = _
  rw [measure_preimage_add_right]
  exact volume_closedUnitSublevelSet hf

theorem leftNormalizedClosedTarget_subset_Ici_zero
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    leftNormalizedClosedTarget f hf ⊆ Ici (0 : ℝ) := by
  intro x hx
  have hleast := (closedUnitSublevelLeft_isLeast hf).2 hx
  change 0 ≤ x
  linarith

theorem zero_mem_leftNormalizedClosedTarget
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    0 ∈ leftNormalizedClosedTarget f hf := by
  change 0 + closedUnitSublevelLeft f hf ∈ closedUnitSublevelSet f
  simpa only [zero_add] using!
    (closedUnitSublevelLeft_isLeast hf).1

theorem taoNormalizedCenter_gt_sqrt_two
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2) :
    Real.sqrt 2 < taoNormalizedCenter f hf := by
  unfold taoNormalizedCenter
  linarith

theorem taoNormalizedSourceLeft_pos
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2) :
    0 < taoNormalizedSourceLeft f hf := by
  unfold taoNormalizedSourceLeft taoNormalizedCenter
  linarith [one_lt_sqrt_two]

theorem taoNormalizedSourceLeft_lt_upperEdge
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    taoNormalizedSourceLeft f hf < taoUpperEdge := by
  have hleftMem := (closedUnitSublevelLeft_isLeast hf).1
  have hleftBound := (closedUnitSublevelSet_subset_Icc hf hleftMem).1
  unfold taoNormalizedSourceLeft taoNormalizedCenter taoUpperEdge
  linarith [one_lt_sqrt_two]

theorem taoNormalizedRightTarget_subset_Ici
    {f : Polynomial ℝ} (hf : IsAdmissible f) :
    taoNormalizedRightTarget f hf ⊆
      Ici (taoNormalizedSourceLeft f hf) :=
  inter_subset_right

/-- The strict volume excess leaves more than the required source-interval
mass to the right of the translated root interval's left endpoint. -/
theorem taoNormalizedRightTarget_mass
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hleft : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hvolume : ENNReal.ofReal taoUpperEdge < sublevelVolume f) :
    ENNReal.ofReal
        (taoUpperEdge - taoNormalizedSourceLeft f hf) <
      volume (taoNormalizedRightTarget f hf) := by
  let A := leftNormalizedClosedTarget f hf
  let l := taoNormalizedSourceLeft f hf
  let E := taoNormalizedRightTarget f hf
  have hl0 : 0 ≤ l := (taoNormalizedSourceLeft_pos hf hleft).le
  have hlM : l ≤ taoUpperEdge :=
    (taoNormalizedSourceLeft_lt_upperEdge hf).le
  have hAvolume : volume A = sublevelVolume f :=
    volume_leftNormalizedClosedTarget hf
  have hAsubset : A ⊆ Ici (0 : ℝ) :=
    leftNormalizedClosedTarget_subset_Ici_zero hf
  have hsplit : A = (A ∩ Iio l) ∪ E := by
    ext x
    constructor
    · intro hx
      by_cases hxl : x < l
      · exact Or.inl ⟨hx, hxl⟩
      · exact Or.inr ⟨hx, le_of_not_gt hxl⟩
    · rintro (hx | hx) <;> exact hx.1
  have hleftPart : volume (A ∩ Iio l) ≤ ENNReal.ofReal l := by
    calc
      volume (A ∩ Iio l) ≤ volume (Ico (0 : ℝ) l) := by
        apply measure_mono
        intro x hx
        exact ⟨hAsubset hx.1, hx.2⟩
      _ = ENNReal.ofReal l := by
        rw [Real.volume_Ico]
        simp
  by_contra hnot
  have hE : volume E ≤ ENNReal.ofReal (taoUpperEdge - l) :=
    le_of_not_gt hnot
  have hAle : volume A ≤ ENNReal.ofReal taoUpperEdge := by
    calc
      volume A = volume ((A ∩ Iio l) ∪ E) :=
        congrArg volume hsplit
      _ ≤ volume (A ∩ Iio l) + volume E :=
        measure_union_le (μ := (volume : Measure ℝ))
          (A ∩ Iio l) E
      _ ≤ ENNReal.ofReal l + ENNReal.ofReal (taoUpperEdge - l) :=
        add_le_add hleftPart hE
      _ = ENNReal.ofReal taoUpperEdge := by
        rw [← ENNReal.ofReal_add hl0 (sub_nonneg.mpr hlM)]
        congr 1
        ring
  rw [hAvolume] at hAle
  exact (not_le_of_gt hvolume) hAle

/-- Away from empirical roots, the closed polynomial target is exactly the
nonnegative real logarithmic-potential set. -/
theorem taoEmpiricalPotential_nonneg_iff_mem_closedUnitSublevelSet
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    {x : ℝ} (hx : x ∉ rootSet f) :
    0 ≤ taoEmpiricalPotential f hf x ↔
      x ∈ closedUnitSublevelSet f := by
  have hdegree : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hf.monic.natDegree_pos.mpr hf.ne_one
  have hinv : 0 < (f.natDegree : ℝ)⁻¹ := inv_pos.mpr hdegree
  rw [taoEmpiricalPotential_eq_neg_empiricalPotential,
    empiricalPotential, ← log_abs_eval_eq_sum_log_abs_roots hf hx]
  simp only [neg_nonneg]
  change (f.natDegree : ℝ)⁻¹ * Real.log |f.eval x| ≤ 0 ↔
    |f.eval x| ≤ 1
  constructor
  · intro hproduct
    apply (Real.log_nonpos_iff (abs_nonneg (f.eval x))).mp
    by_contra hlog
    have hlogPos : 0 < Real.log |f.eval x| := lt_of_not_ge hlog
    exact (not_lt_of_ge hproduct) (mul_pos hinv hlogPos)
  · intro habs
    exact mul_nonpos_of_nonneg_of_nonpos hinv.le
      ((Real.log_nonpos_iff (abs_nonneg (f.eval x))).mpr habs)

/-- Any measure that gives the finite root set mass zero sees nonnegative
empirical potential almost everywhere on the closed polynomial target. -/
theorem ae_taoEmpiricalPotential_nonneg_on_closedUnitSublevelSet
    {f : Polynomial ℝ} (hf : IsAdmissible f) (ν : Measure ℝ)
    (hroots : ν (rootSet f) = 0) :
    ∀ᵐ x ∂ν, x ∈ closedUnitSublevelSet f →
      0 ≤ taoEmpiricalPotential f hf x := by
  have hnotRoot : ∀ᵐ x ∂ν, x ∉ rootSet f := by
    apply ae_iff.mpr
    simpa only [not_not] using! hroots
  filter_upwards [hnotRoot] with x hx hclosed
  exact (taoEmpiricalPotential_nonneg_iff_mem_closedUnitSublevelSet
    hf hx).mpr hclosed

end

end Erdos1038
