import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.UrysohnsLemma

/-!
# Extending a chart family with a scalar cutoff

The chart-valued function only needs to be continuous on an open parameter
set. A scalar cutoff supported there gives a globally continuous vector-valued
family, still in the same ball and agreeing on any prescribed compact subset.
-/

open Set

namespace NoExoticSixSphere.ChartFamilyCutoff

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def weighted (F : X → E) (A : Set X) (hA : IsOpen A)
    (hF : ContinuousOn F A) (γ : C(X, ℝ)) (hγ : tsupport γ ⊆ A) : C(X, E) :=
  ⟨fun x ↦ γ x • F x,
    (γ.continuous.continuousOn.smul hF).continuous_of_tsupport_subset hA
      ((tsupport_smul_subset_left γ F).trans hγ)⟩

theorem weighted_eq (F : X → E) (A : Set X) (hA : IsOpen A)
    (hF : ContinuousOn F A) (γ : C(X, ℝ)) (hγ : tsupport γ ⊆ A)
    {x : X} (hx : γ x = 1) : weighted F A hA hF γ hγ x = F x := by
  change γ x • F x = F x
  rw [hx, one_smul]

theorem weighted_mem_ball (F : X → E) (A : Set X) (hA : IsOpen A)
    (hF : ContinuousOn F A) (γ : C(X, ℝ)) (hγ : tsupport γ ⊆ A)
    (hbound : ∀ x, γ x ∈ Icc (0 : ℝ) 1) (r : ℝ) (hr : 0 < r)
    (hball : ∀ x ∈ A, F x ∈ Metric.ball 0 r) (x : X) :
    weighted F A hA hF γ hγ x ∈ Metric.ball 0 r := by
  by_cases hx : x ∈ A
  · rw [Metric.mem_ball, dist_zero_right]
    change ‖γ x • F x‖ < r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
    have hh : ‖F x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hball x hx
    exact (mul_le_of_le_one_left (norm_nonneg _) (hbound x).2).trans_lt hh
  · have hzero : γ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hγ h))
    change γ x • F x ∈ Metric.ball 0 r
    rw [hzero, zero_smul]
    exact Metric.mem_ball_self hr

variable [CompactSpace X] [T2Space X]

theorem exists_extension (F : X → E) (A : Set X) (hA : IsOpen A)
    (hF : ContinuousOn F A) (K : Set X) (hK : IsClosed K) (hKA : K ⊆ A)
    (r : ℝ) (hr : 0 < r) (hball : ∀ x ∈ A, F x ∈ Metric.ball 0 r) :
    ∃ q : C(X, E), EqOn q F K ∧ ∀ x, q x ∈ Metric.ball 0 r := by
  obtain ⟨γ, hγ, hOne, hbound⟩ := exists_tsupport_one_of_isOpen_isClosed hA
    isClosed_closure.isCompact hK hKA
  exact ⟨weighted F A hA hF γ hγ,
    fun x hx ↦ weighted_eq F A hA hF γ hγ (hOne hx),
    weighted_mem_ball F A hA hF γ hγ hbound r hr hball⟩

end NoExoticSixSphere.ChartFamilyCutoff
