import Wikipedia.SmoothSixDPoincare.CompactFaceAvoidance
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# An open neighborhood of a compact whole face contains a larger product disk

Compactness of the sphere-times-closed-disk parameter space gives one radius
strictly larger than one inside any open neighborhood of the entire face.
This supplies the collar width needed to shrink a repeatedly transported face.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.SmoothSixDPoincare

theorem exists_larger_product_disk_in_open
    {X N : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {U : Set (X × N)} (hU : IsOpen U)
    (hface : (univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ U) :
    ∃ r : ℝ, 1 < r ∧ (univ : Set X) ×ˢ closedBall (0 : N) r ⊆ U := by
  let F : ℝ × (X × MorseHandle.UnitDisk N) → X × N :=
    fun q => (q.2.1, q.1 • q.2.2.val)
  have hF : Continuous F := (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.smul (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  have hpre : IsOpen {q : ℝ × (X × MorseHandle.UnitDisk N) | F q ∈ U} := hU.preimage hF
  have hnear : {t : ℝ | ∀ z : X × MorseHandle.UnitDisk N, F (t, z) ∈ U} ∈ 𝓝 (1 : ℝ) := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := (1 : ℝ)) (P := fun t (z : X × MorseHandle.UnitDisk N) => F (t, z) ∈ U)
      (fun z (_ : z ∈ univ) => hpre.mem_nhds (by
        have hz : (z.1, z.2.val) ∈ U := hface ⟨mem_univ z.1, z.2.property⟩
        change (z.1, (1 : ℝ) • z.2.val) ∈ U
        simpa only [one_smul] using hz))
    filter_upwards [h] with t ht
    exact fun z => ht z (mem_univ z)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := 1 + ε / 2
  have hr : 1 < r := by dsimp [r]; linarith
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hrball : r ∈ ball (1 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hr)]
    dsimp [r]
    linarith
  refine ⟨r, hr, ?_⟩
  rintro ⟨x, w⟩ ⟨_, hw⟩
  have hw' : r⁻¹ • w ∈ closedBall (0 : N) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₀)]
    exact (inv_mul_le_iff₀ hr₀).mpr (by simpa only [mul_one] using mem_closedBall_zero_iff.mp hw)
  have hh := hball hrball (x, ⟨r⁻¹ • w, hw'⟩)
  simpa only [F, smul_inv_smul₀ hr₀.ne'] using hh

end Wikipedia.SmoothSixDPoincare
