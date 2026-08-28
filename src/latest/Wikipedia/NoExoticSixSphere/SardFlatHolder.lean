import Wikipedia.NoExoticSixSphere.SardFlatEstimate
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Local Hölder estimates on the vanishing locus

Continuity of the next derivative gives a local bound. Taylor's integral
formula then makes the restriction to the high-order vanishing locus
Hölder with exponent one greater than the vanishing order.
-/

open scoped ContDiff NNReal ENNReal Topology
open Set Metric Filter

namespace NoExoticSixSphere.Sard

theorem holderOnWith_nat_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {s : Set X} {C : ℝ≥0} {k : ℕ}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ k) :
    HolderOnWith C (k : ℝ≥0) f s := by
  intro x hx y hy
  have he := ENNReal.ofReal_le_ofReal (h x hx y hy)
  simpa only [edist_dist, NNReal.coe_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_pow dist_nonneg] using he

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_holderOnWith_flatPoints {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) {x : E} (hx : x ∈ U) :
    ∃ L : ℝ≥0, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      HolderOnWith L ((k + 1 : ℕ) : ℝ≥0) f (ball x r ∩ flatPoints f k) := by
  let D := iteratedFDeriv ℝ (k + 1) f
  let C : ℝ≥0 := ‖D x‖₊ + 1
  have hD : ContinuousAt D x :=
    (hf.contDiffAt (hU.mem_nhds hx)).continuousAt_iteratedFDeriv (by
      exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤))
  have hxC : ‖D x‖ < (C : ℝ) := by simp [C]
  have hn : ∀ᶠ y in 𝓝 x, ‖D y‖ < (C : ℝ) := hD.norm.eventually (gt_mem_nhds hxC)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hn)
  let L : ℝ≥0 := ⟨(k.factorial : ℝ)⁻¹ * C, by positivity⟩
  refine ⟨L, r, hr, fun y hy ↦ (hball hy).1, ?_⟩
  apply holderOnWith_nat_of_dist_le
  intro y hy z hz
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (z - y) ∈ ball x r :=
    fun _ ht ↦ (convex_ball x r).add_smul_sub_mem hy.1 hz.1 ht
  have hb := norm_sub_le_of_flat
    (fun t ht ↦ hf.contDiffAt (hU.mem_nhds (hball (hseg t ht)).1)) hy.2 C
    (fun t ht ↦ (hball (hseg t ht)).2.le)
  change dist (f y) (f z) ≤ ((k.factorial : ℝ)⁻¹ * C) * dist y z ^ (k + 1)
  rw [dist_comm (f y) (f z), dist_comm y z, dist_eq_norm, dist_eq_norm]
  exact hb

theorem dimH_image_flatPoints_le [SecondCountableTopology E] {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) :
    dimH (f '' (U ∩ flatPoints f k)) ≤ dimH (U ∩ flatPoints f k) / (k + 1 : ℕ) := by
  apply dimH_image_le_of_locally_holder_on (r := ((k + 1 : ℕ) : ℝ≥0)) (by positivity)
  intro x hx
  obtain ⟨L, r, hr, _, hL⟩ := exists_holderOnWith_flatPoints hU hf k hx.1
  refine ⟨L, ball x r ∩ (U ∩ flatPoints f k), ?_, hL.mono ?_⟩
  · exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr)) self_mem_nhdsWithin
  · exact fun _ hy ↦ ⟨hy.1, hy.2.2⟩

end NoExoticSixSphere.Sard
