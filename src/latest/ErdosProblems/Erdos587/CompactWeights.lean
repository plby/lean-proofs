import ErdosProblems.Erdos587.FiberIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Fixed compactly supported Schwartz weights

The root plateau varies with the progression. A finite family of fixed
weights, not a changing Schwartz function with untracked constants, will
be used for the uniform analytic estimates.
-/

open scoped SchwartzMap

namespace Erdos587

noncomputable def intervalBump (a b η : ℝ) (hη : 0 < η) : ContDiffBump ((a + b) / 2) where
  rIn := |b - a| / 2 + η
  rOut := |b - a| / 2 + 2 * η
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def intervalSchwartz (a b η : ℝ) (hη : 0 < η) : 𝓢(ℝ, ℂ) :=
  ((intervalBump a b η hη).hasCompactSupport.toSchwartzMap
    (intervalBump a b η hη).contDiff).postcompCLM Complex.ofRealCLM

@[simp] lemma intervalSchwartz_apply (a b η : ℝ) (hη : 0 < η) (x : ℝ) :
    intervalSchwartz a b η hη x = ((intervalBump a b η hη x : ℝ) : ℂ) := rfl

lemma intervalSchwartz_real (a b η : ℝ) (hη : 0 < η) (x : ℝ) :
    (intervalSchwartz a b η hη x).im = 0 := rfl

lemma intervalSchwartz_nonneg (a b η : ℝ) (hη : 0 < η) (x : ℝ) :
    0 ≤ (intervalSchwartz a b η hη x).re := (intervalBump a b η hη).nonneg

lemma intervalSchwartz_le_one (a b η : ℝ) (hη : 0 < η) (x : ℝ) :
    (intervalSchwartz a b η hη x).re ≤ 1 := (intervalBump a b η hη).le_one

lemma intervalSchwartz_one_of_close {a b c d η : ℝ} (hη : 0 < η)
    (hac : |a - c| < η) (hbd : |b - d| < η) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    intervalSchwartz c d η hη x = 1 := by
  rw [intervalSchwartz_apply]
  have hh : intervalBump c d η hη x = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    dsimp [intervalBump]
    have hac' := abs_lt.mp hac
    have hbd' := abs_lt.mp hbd
    constructor <;> nlinarith [le_abs_self (d - c), neg_le_abs (d - c), hx.1, hx.2]
  simp only [hh, Complex.ofReal_one]

lemma intervalSchwartz_support_of_close {a b c d η : ℝ} (hη : 0 < η)
    (hab : a ≤ b) (hac : |a - c| < η) (hbd : |b - d| < η) {x : ℝ}
    (hx : intervalSchwartz c d η hη x ≠ 0) : a - 3 * η < x ∧ x < b + 3 * η := by
  have hx' : intervalBump c d η hη x ≠ 0 := by
    intro hh
    apply hx
    simp only [intervalSchwartz_apply, hh, Complex.ofReal_zero]
  have hmem : x ∈ Metric.ball ((c + d) / 2) (|d - c| / 2 + 2 * η) := by
    change x ∈ Metric.ball ((c + d) / 2) (intervalBump c d η hη).rOut
    rw [← (intervalBump c d η hη).support_eq]
    exact hx'
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
  have hac' := abs_lt.mp hac
  have hbd' := abs_lt.mp hbd
  rcases le_total c d with hcd | hdc
  · rw [abs_of_nonneg (sub_nonneg.mpr hcd)] at hmem
    constructor <;> linarith [hmem.1, hmem.2, hac'.1, hac'.2, hbd'.1, hbd'.2]
  · rw [abs_of_nonpos (sub_nonpos.mpr hdc)] at hmem
    constructor <;> linarith [hmem.1, hmem.2, hac'.1, hac'.2, hbd'.1, hbd'.2]

lemma intervalSchwartz_one {a b η : ℝ} (hη : 0 < η) {x : ℝ}
    (hx : x ∈ Set.Icc a b) : intervalSchwartz a b η hη x = 1 := by
  exact intervalSchwartz_one_of_close hη (by simpa) (by simpa) hx

lemma intervalSchwartz_support {a b η : ℝ} (hη : 0 < η) (hab : a ≤ b) {x : ℝ}
    (hx : intervalSchwartz a b η hη x ≠ 0) : a - 2 * η < x ∧ x < b + 2 * η := by
  have hx' : intervalBump a b η hη x ≠ 0 := by
    intro hh
    apply hx
    simp only [intervalSchwartz_apply, hh, Complex.ofReal_zero]
  have hmem : x ∈ Metric.ball ((a + b) / 2) (intervalBump a b η hη).rOut := by
    rw [← (intervalBump a b η hη).support_eq]
    exact hx'
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
  dsimp [intervalBump] at hmem
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hmem
  constructor <;> linarith [hmem.1, hmem.2]

noncomputable def physicalSquareWeight : 𝓢(ℝ, ℂ) :=
  intervalSchwartz (5 / 32) (7 / 32) (1 / 64) (by norm_num)

lemma physicalSquareWeight_real (x : ℝ) : (physicalSquareWeight x).im = 0 := rfl

lemma physicalSquareWeight_nonneg (x : ℝ) : 0 ≤ (physicalSquareWeight x).re :=
  intervalSchwartz_nonneg _ _ _ _ _

lemma physicalSquareWeight_plateau {x : ℝ} (hx : x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32)) :
    physicalSquareWeight x = 1 := intervalSchwartz_one (by norm_num) hx

lemma physicalSquareWeight_support {x : ℝ} (hx : physicalSquareWeight x ≠ 0) :
    (1 / 8 : ℝ) < x ∧ x < 1 / 4 := by
  have hh := intervalSchwartz_support (by norm_num : (0 : ℝ) < 1 / 64)
    (by norm_num : (5 / 32 : ℝ) ≤ 7 / 32) hx
  norm_num at hh
  exact hh

theorem exists_finite_interval_weights {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset 𝓢(ℝ, ℂ),
      (∀ f ∈ F, (∀ x : ℝ, (f x).im = 0) ∧ (∀ x : ℝ, 0 ≤ (f x).re) ∧
        (∀ x : ℝ, (f x).re ≤ 1)) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        ∃ f ∈ F, (∀ x ∈ Set.Icc a b, f x = 1) ∧
          (∀ x : ℝ, f x ≠ 0 → a - 3 * η < x ∧ x < b + 3 * η) := by
  classical
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨P, hcover⟩ := hK.elim_finite_subcover
    (fun p : ℝ × ℝ => Metric.ball p η) (fun _ => Metric.isOpen_ball)
    (fun p hp => Set.mem_iUnion.mpr ⟨p, Metric.mem_ball_self hη⟩)
  refine ⟨P.image (fun p => intervalSchwartz p.1 p.2 η hη), ?_, ?_⟩
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨intervalSchwartz_real _ _ _ _, intervalSchwartz_nonneg _ _ _ _,
      intervalSchwartz_le_one _ _ _ _⟩
  · intro a b ha hab hb
    have hp : (a, b) ∈ K := ⟨⟨ha, hab.trans hb⟩, ⟨ha.trans hab, hb⟩⟩
    obtain ⟨p, hpP, hpdist⟩ := Set.mem_iUnion₂.mp (hcover hp)
    have hdist : dist (a, b) p < η := hpdist
    rw [Prod.dist_eq, max_lt_iff] at hdist
    have hac : |a - p.1| < η := by
      rw [← Real.dist_eq]
      exact hdist.1
    have hbd : |b - p.2| < η := by
      rw [← Real.dist_eq]
      exact hdist.2
    refine ⟨intervalSchwartz p.1 p.2 η hη, Finset.mem_image.mpr ⟨p, hpP, rfl⟩, ?_, ?_⟩
    · intro x hx
      exact intervalSchwartz_one_of_close hη hac hbd hx
    · intro x hx
      exact intervalSchwartz_support_of_close hη hab hac hbd hx

end Erdos587
