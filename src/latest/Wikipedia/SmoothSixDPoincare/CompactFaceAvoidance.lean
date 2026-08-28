import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Mathlib.Topology.Compactness.Compact

/-!
# Uniform avoidance on a thin disk bundle over a compact base

If the zero section of an actual continuous face misses a closed set, one
strictly positive normal radius works for every point of its compact base.
-/

noncomputable section

open Set Metric Filter Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

theorem exists_uniform_face_avoidance_radius
    {B W X : Type*} [TopologicalSpace B] [CompactSpace B]
    [NormedAddCommGroup W] [TopologicalSpace X]
    (F : C(B × MorseHandle.UnitDisk W, X)) {K : Set X} (hK : IsClosed K)
    (hcore : ∀ u, F (u, ⟨0, by simp⟩) ∉ K) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ u (w : MorseHandle.UnitDisk W), ‖w.val‖ ≤ a → F (u, w) ∉ K := by
  let zero : MorseHandle.UnitDisk W := ⟨0, by simp⟩
  have hU : IsOpen {z : MorseHandle.UnitDisk W × B | F (z.2, z.1) ∉ K} :=
    hK.isOpen_compl.preimage
      (F.continuous.comp (continuous_snd.prodMk continuous_fst))
  have hnear : {w : MorseHandle.UnitDisk W | ∀ u, F (u, w) ∉ K} ∈ 𝓝 zero := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := zero) (P := fun w u => F (u, w) ∉ K)
      (fun u (_ : u ∈ (univ : Set B)) => hU.mem_nhds (hcore u))
    filter_upwards [h] with w hw
    exact fun u => hw u (mem_univ u)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let a := min (ε / 2) 1
  have ha : 0 < a := lt_min (half_pos hε) zero_lt_one
  have haε : a < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨a, ha, min_le_right _ _, ?_⟩
  intro u w hw
  apply hball ?_ u
  change dist w zero < ε
  simpa only [Subtype.dist_eq, zero, dist_zero_right] using hw.trans_lt haε

end Wikipedia.SmoothSixDPoincare
