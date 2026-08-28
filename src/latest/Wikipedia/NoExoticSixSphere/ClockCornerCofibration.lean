import Wikipedia.NoExoticSixSphere.MetricPointCofibration
import Wikipedia.NoExoticSixSphere.SubspaceCofibration
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# A corner neighborhood deformation preserving the square boundary

The metric cutoff is one near the zero corner and zero on either
opposite edge. Scaling both clock coordinates by the remaining time
therefore contracts a neighborhood of the corner while preserving the
entire square boundary. This additional boundary condition is needed
when restricting product neighborhood data to an attaching sphere.
-/

noncomputable section

open Set
open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.ClockCorner

abbrev Square := Fin 2 → I

def cutoff : C(Square, I) :=
  ⟨fun t ↦ ⟨MetricPointCofibration.cutoff (0 : Square) t,
      MetricPointCofibration.cutoff_mem (0 : Square) t⟩,
    (MetricPointCofibration.cutoff (0 : Square)).continuous.subtype_mk _⟩

theorem cutoff_zero (t : Square) (ht : 1 ≤ dist t 0) : cutoff t = 0 :=
  Subtype.ext (MetricPointCofibration.cutoff_zero (0 : Square) t ht)

theorem cutoff_one (t : Square) (ht : dist t 0 ≤ 1 / 2) : cutoff t = 1 :=
  Subtype.ext (MetricPointCofibration.cutoff_one (0 : Square) t ht)

def motion : C(I × Square, Square) :=
  ⟨fun u i ↦ σ (u.1 * cutoff u.2) * u.2 i,
    continuous_pi (fun i ↦ (unitInterval.continuous_symm.comp
      (continuous_fst.mul (cutoff.continuous.comp continuous_snd))).mul
        ((continuous_apply i).comp continuous_snd))⟩

theorem motion_zero (t : Square) : motion (0, t) = t := by
  funext i
  change σ ((0 : I) * cutoff t) * t i = t i
  rw [zero_mul, unitInterval.symm_zero, one_mul]

theorem motion_fixed (s : I) : motion (s, (0 : Square)) = 0 := by
  funext i
  exact mul_zero _

theorem motion_far (s : I) (t : Square) (ht : 1 ≤ dist t 0) : motion (s, t) = t := by
  funext i
  change σ (s * cutoff t) * t i = t i
  rw [cutoff_zero t ht, mul_zero, unitInterval.symm_zero, one_mul]

theorem motion_terminal (t : Square) (ht : MetricPointCofibration.height (0 : Square) t < 1) :
    motion (1, t) = 0 := by
  have hc := cutoff_one t (MetricPointCofibration.height_lt_one (0 : Square) t ht).le
  funext i
  change σ ((1 : I) * cutoff t) * t i = 0
  rw [hc, one_mul, unitInterval.symm_one, zero_mul]

theorem motion_boundary (s : I) (t : Square) (ht : t ∈ Cube.boundary (Fin 2)) :
    motion (s, t) ∈ Cube.boundary (Fin 2) := by
  rcases ht with ⟨i, hi | hi⟩
  · refine ⟨i, Or.inl ?_⟩
    change σ (s * cutoff t) * t i = 0
    rw [hi, mul_zero]
  · have hd : 1 ≤ dist t (0 : Square) := by
      have he : dist (1 : I) (0 : I) = (1 : ℝ) := by norm_num [Subtype.dist_eq]
      simpa only [hi, Pi.zero_apply, he] using dist_le_pi_dist t (0 : Square) i
    rw [motion_far s t hd]
    exact ⟨i, Or.inr hi⟩

def data : NeighborhoodDeformation.Data (SubspaceCofibration.inclusion ({0} : Set Square)) where
  height := MetricPointCofibration.height (0 : Square)
  deformation := motion
  zero_iff t := by
    rw [MetricPointCofibration.height_zero_iff, SubspaceCofibration.mem_range]
    rfl
  bottom := motion_zero
  fixed s p := by
    have hp : p.val = 0 := p.property
    change motion (s, p.val) = p.val
    rw [hp, motion_fixed]
  terminal t ht := by
    rw [SubspaceCofibration.mem_range, motion_terminal t ht]
    exact Set.mem_singleton _

end NoExoticSixSphere.ClockCorner
