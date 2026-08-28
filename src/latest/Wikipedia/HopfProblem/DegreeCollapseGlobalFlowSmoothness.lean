import Wikipedia.HopfProblem.DegreeCollapseNativeFlowSmoothness
import Wikipedia.SmoothSixDPoincare.MorseCompactStability
import Mathlib.Topology.Connected.Clopen

/-!
# Global joint smoothness of the actual complete native flow

For each finite differentiability order, compactness gives a uniform
short-time interval. The flow action law and connectedness of the real
line extend that order to every time map, then to the joint flow. Taking
all finite orders gives smoothness. No common smooth neighborhood is
incorrectly inferred from an infinitely differentiable point germ.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare.MorsePerturbation

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Compactness gives a uniform short-time interval separately at each finite smoothness order. -/
theorem exists_uniform_smalltime_contMDiff (F : Flow ℝ M) (n : ℕ)
    (hzero : ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
      (fun q : M × ℝ => F q.2 q.1) (p, 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (-ε) ε, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F t) := by
  let U : Set (M × ℝ) := {q | ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
    (fun r : M × ℝ => F r.2 r.1) q}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    exact (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hq
  let T : Set ℝ := {t | ∀ p ∈ (univ : Set M), (t, p) ∈ Prod.swap ⁻¹' U}
  have hT : IsOpen T := isOpen_forall_mem_compact isCompact_univ (hU.preimage continuous_swap)
  have h0 : (0 : ℝ) ∈ T := fun p _ => hzero p
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨ε, hε, ?_⟩
  intro t ht p
  have htT : t ∈ T := hεsub (by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  have hj : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
      (fun q : M × ℝ => F q.2 q.1) (p, t) := htT p (mem_univ p)
  have hι : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) n
      (fun x : M => (x, t)) p := contMDiffAt_id.prodMk contMDiffAt_const
  have hh := hj.comp p hι
  exact hh

/-- The action law extends every finite smoothness order to all time maps. -/
theorem contMDiff_flow_time_of_zero (F : Flow ℝ M) (n : ℕ)
    (hzero : ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
      (fun q : M × ℝ => F q.2 q.1) (p, 0)) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_uniform_smalltime_contMDiff F n hzero
  let S : Set ℝ := {s | ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Ioo (-ε) ε := abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => F (u - s) (F s x)) = F u := by
      funext x
      rw [← F.map_add, sub_add_cancel]
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F u)
    rw [← heq]
    exact hc
  have hS : IsOpen S := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu h => hs (hstep h (by
      change dist u s < ε at hu
      rwa [dist_comm])))
  have h0 : (0 : ℝ) ∈ S := by
    have heq : F 0 = id := funext F.map_zero_apply
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (F 0)
    rw [heq]
    exact contMDiff_id
  have hSuniv : S = univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, h0⟩
  have ht : t ∈ S := by rw [hSuniv]; exact mem_univ t
  exact ht

/-- Fixed-time smoothness and the initial-slice germ give joint smoothness at every time. -/
theorem contMDiff_joint_flow_of_zero (F : Flow ℝ M) (n : ℕ)
    (hzero : ∀ p : M, ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
      (fun q : M × ℝ => F q.2 q.1) (p, 0)) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n (fun q : M × ℝ => F q.2 q.1) := by
  intro q
  let A (r : M × ℝ) := (F q.2 r.1, r.2 - q.2)
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) n A q :=
    ((contMDiff_flow_time_of_zero F n hzero q.2).contMDiffAt.comp q contMDiffAt_fst).prodMk
      (contMDiffAt_snd.sub contMDiffAt_const)
  have hG : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
      (fun r : M × ℝ => F r.2 r.1) (A q) := by
    simpa only [A, sub_self] using hzero (F q.2 q.1)
  have hc := hG.comp q hA
  have heq : ((fun r : M × ℝ => F r.2 r.1) ∘ A) = (fun r : M × ℝ => F r.2 r.1) := by
    funext r
    change F (r.2 - q.2) (F q.2 r.1) = F r.2 r.1
    rw [← F.map_add, sub_add_cancel]
  exact heq ▸ hc

variable [FiniteDimensional ℝ E]

/-- The actual complete native flow on a compact manifold is jointly smooth. -/
theorem contMDiff_native_flow
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (fun q : M × ℝ => F q.2 q.1) :=
  contMDiff_infty.mpr (fun n => contMDiff_joint_flow_of_zero F n
    (fun p => contMDiffAt_infty.mp (contMDiffAt_native_flow_zero hV F hcurve p) n))

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
