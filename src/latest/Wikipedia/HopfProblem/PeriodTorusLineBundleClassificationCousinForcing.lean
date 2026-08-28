import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinCochain
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinDifferential
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCompactDbar

/-!
# The actual global closed forcing form of a holomorphic cocycle

The two antiholomorphic derivatives of the constructed smooth cochains
agree on overlaps. Their chart-selected values therefore glue to two actual
globally smooth functions. The local mixed-derivative identity proves the
closedness equation for this global pair.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

open PeriodTorusLineBundleClassification

namespace Cocycle

variable {ι : Type*} (C : Cocycle ι)

theorem dbarFirst_cochain_eq (i j : ι) {x : ℂ × ℂ}
    (hi : x ∈ C.domain i) (hj : x ∈ C.domain j) :
    dbarFirst (C.cochain i) x = dbarFirst (C.cochain j) x := by
  have h := (coordinate_dbar_zero_of_analyticAt
    (C.cochain_sub_analyticOnNhd i j x ⟨hi, hj⟩)).1
  rw [dbarFirst_sub ((C.cochain_contDiffAt hi).differentiableAt (by simp))
    ((C.cochain_contDiffAt hj).differentiableAt (by simp))] at h
  exact sub_eq_zero.mp h

theorem dbarSecond_cochain_eq (i j : ι) {x : ℂ × ℂ}
    (hi : x ∈ C.domain i) (hj : x ∈ C.domain j) :
    dbarSecond (C.cochain i) x = dbarSecond (C.cochain j) x := by
  have h := (coordinate_dbar_zero_of_analyticAt
    (C.cochain_sub_analyticOnNhd i j x ⟨hi, hj⟩)).2
  rw [dbarSecond_sub ((C.cochain_contDiffAt hi).differentiableAt (by simp))
    ((C.cochain_contDiffAt hj).differentiableAt (by simp))] at h
  exact sub_eq_zero.mp h

/-- The literal first antiholomorphic derivative of the selected local cochain. -/
def forcingFirst (x : ℂ × ℂ) : ℂ := dbarFirst (C.cochain (C.indexAt x)) x

/-- The literal second antiholomorphic derivative of the selected local cochain. -/
def forcingSecond (x : ℂ × ℂ) : ℂ := dbarSecond (C.cochain (C.indexAt x)) x

theorem forcingFirst_eq {i : ι} {x : ℂ × ℂ} (hx : x ∈ C.domain i) :
    C.forcingFirst x = dbarFirst (C.cochain i) x :=
  C.dbarFirst_cochain_eq (C.indexAt x) i (C.mem_domain_indexAt x) hx

theorem forcingSecond_eq {i : ι} {x : ℂ × ℂ} (hx : x ∈ C.domain i) :
    C.forcingSecond x = dbarSecond (C.cochain i) x :=
  C.dbarSecond_cochain_eq (C.indexAt x) i (C.mem_domain_indexAt x) hx

theorem forcingFirst_eventuallyEq {i : ι} {x : ℂ × ℂ} (hx : x ∈ C.domain i) :
    C.forcingFirst =ᶠ[𝓝 x] dbarFirst (C.cochain i) := by
  filter_upwards [(C.isOpen_domain i).mem_nhds hx] with y hy
  exact C.forcingFirst_eq hy

theorem forcingSecond_eventuallyEq {i : ι} {x : ℂ × ℂ} (hx : x ∈ C.domain i) :
    C.forcingSecond =ᶠ[𝓝 x] dbarSecond (C.cochain i) := by
  filter_upwards [(C.isOpen_domain i).mem_nhds hx] with y hy
  exact C.forcingSecond_eq hy

/-- The chart choice does not compromise actual global smoothness. -/
theorem forcingFirst_contDiff : ContDiff ℝ ∞ C.forcingFirst := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (contDiffAt_dbarFirst
    (C.cochain_contDiffAt (C.mem_domain_indexAt x))).congr_of_eventuallyEq
    (C.forcingFirst_eventuallyEq (C.mem_domain_indexAt x))

theorem forcingSecond_contDiff : ContDiff ℝ ∞ C.forcingSecond := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (contDiffAt_dbarSecond
    (C.cochain_contDiffAt (C.mem_domain_indexAt x))).congr_of_eventuallyEq
    (C.forcingSecond_eventuallyEq (C.mem_domain_indexAt x))

/-- Closedness is proved from local equality with the actual derivatives
of one smooth cochain and the real mixed-derivative theorem. -/
theorem forcing_isDbarClosed : IsDbarClosed C.forcingFirst C.forcingSecond := by
  intro x
  rw [dbarFirst_congr (C.forcingSecond_eventuallyEq (C.mem_domain_indexAt x)),
    dbarSecond_congr (C.forcingFirst_eventuallyEq (C.mem_domain_indexAt x))]
  exact dbarFirst_dbarSecond_of_contDiffAt (C.cochain_contDiffAt (C.mem_domain_indexAt x))

/-- The actual forcing construction, including all smoothness, transition,
derivative, and closedness conclusions, with no primitive assumed. -/
theorem exists_smooth_closed_forcing :
    ∃ (s : ι → ℂ × ℂ → ℂ) (f g : ℂ × ℂ → ℂ),
      (∀ i, ContDiffOn ℝ ∞ (s i) (C.domain i)) ∧
      (∀ i j x, x ∈ C.domain i → x ∈ C.domain j → s i x - s j x = C.transition i j x) ∧
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ IsDbarClosed f g ∧
      (∀ i x, x ∈ C.domain i → dbarFirst (s i) x = f x) ∧
      ∀ i x, x ∈ C.domain i → dbarSecond (s i) x = g x :=
  ⟨C.cochain, C.forcingFirst, C.forcingSecond, C.cochain_contDiffOn,
    fun i j _ hi hj => C.cochain_sub i j hi hj,
    C.forcingFirst_contDiff, C.forcingSecond_contDiff, C.forcing_isDbarClosed,
    fun _ _ hx => (C.forcingFirst_eq hx).symm, fun _ _ hx => (C.forcingSecond_eq hx).symm⟩

end Cocycle

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
