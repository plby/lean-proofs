import Wikipedia.SmoothSixDPoincare.BigonBallHomeomorph
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Move the whole cornered boundary strictly into the bigon interior

Contract about the actual interior point `(0,h/2)`, rather than the boundary
point `(0,0)`. A factor strictly between zero and one sends the whole disk
into its interior. Factors sufficiently close to one retain the boundary
inside any prescribed open boundary neighborhood.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- Affine contraction about the explicit interior point of the bigon. -/
def innerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - r) • (0, h / 2) + r • p

theorem innerBigonMap_one (h : ℝ) (p : ℝ × ℝ) : innerBigonMap h 1 p = p := by
  simp only [innerBigonMap, sub_self, zero_smul, one_smul, zero_add]

theorem contDiff_innerBigonMap (h : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => innerBigonMap h z.1 z.2) := by
  unfold innerBigonMap
  fun_prop

/-- The inward affine map is a genuine global diffeomorphism whenever its factor is nonzero. -/
def innerBigonDiffeomorph (h r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toEquiv := {
    toFun := innerBigonMap h r
    invFun := fun p => r⁻¹ • (p - (1 - r) • (0, h / 2))
    left_inv := by
      intro p
      simp only [innerBigonMap, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]
    right_inv := by
      intro p
      simp only [innerBigonMap, smul_smul, mul_inv_cancel₀ hr, one_smul]
      abel }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r)
    apply ContDiff.contMDiff
    unfold innerBigonMap
    fun_prop
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => r⁻¹ • (p - (1 - r) • (0, h / 2)))
    apply ContDiff.contMDiff
    fun_prop

/-- The actual native derivative of the inward affine map is bijective everywhere. -/
theorem bijective_mfderiv_innerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (innerBigonMap h r) p) :=
  PartialChart.bijective_mfderiv (innerBigonDiffeomorph h r hr).toPartialDiffeomorph
    (mem_univ p)

/-- Every point, including both arcs and both corners, moves into the open bigon. -/
theorem innerBigonMap_mem_interior {h r : ℝ} (hh : 0 < h) (hr : r ∈ Ioo (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ bigon h) : innerBigonMap h r p ∈ interior (bigon h) :=
  (convex_bigon hh.le).combo_interior_self_mem_interior (bigon_center_mem_interior hh)
    hp (sub_pos.mpr hr.2) hr.1.le (by ring)

/-- A small inward affine contraction keeps the entire original frontier in its open collar. -/
theorem exists_inner_bigon_boundary_in_open {h : ℝ} (hh : 0 < h)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hfrontU : frontier (bigon h) ⊆ U) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧
      MapsTo (innerBigonMap h r) (frontier (bigon h)) (U ∩ interior (bigon h)) := by
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  have hnear : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ frontier (bigon h), innerBigonMap h r p ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((contDiff_innerBigonMap h).continuous.continuousAt
      (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [innerBigonMap_one] using hfrontU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min ε 1 / 2
  have hδpos : 0 < δ := half_pos (lt_min hε zero_lt_one)
  have hδε : δ < ε := by
    dsimp [δ]
    have hm := min_le_left ε 1
    linarith
  have hδ1 : δ < 1 := by
    dsimp [δ]
    have hm := min_le_right ε 1
    linarith
  have hr : 1 - δ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hrball : 1 - δ ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : 1 - δ - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδpos]
    exact hδε
  refine ⟨1 - δ, hr, fun p hp => ⟨hball hrball p hp, ?_⟩⟩
  exact innerBigonMap_mem_interior hh hr ((mem_frontier_bigon_iff h p).mp hp).1

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
