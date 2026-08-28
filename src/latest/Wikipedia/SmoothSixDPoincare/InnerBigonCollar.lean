import Wikipedia.SmoothSixDPoincare.InnerBigon

/-!
# The actual collar left outside an inward affine bigon

The collar is compact and can be contained in any prescribed open neighborhood
of the original frontier. Its intersection with the inward disk is exactly
the inward disk's frontier. All sets are subsets of the original plane.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

/-- The collar includes both the original frontier and the shared inner frontier. -/
def innerBigonCollar (h r : ℝ) : Set (ℝ × ℝ) :=
  bigon h \ innerBigonMap h r '' interior (bigon h)

/-- The explicit inverse affine formula, also defined at zero factor for convenience. -/
def inverseInnerBigonMap (h r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  r⁻¹ • (p - (1 - r) • (0, h / 2))

theorem inverseInnerBigonMap_one (h : ℝ) (p : ℝ × ℝ) :
    inverseInnerBigonMap h 1 p = p := by
  simp only [inverseInnerBigonMap, inv_one, sub_self, zero_smul, sub_zero, one_smul]

theorem inner_inverseInnerBigonMap (h r : ℝ) (hr : r ≠ 0) (p : ℝ × ℝ) :
    innerBigonMap h r (inverseInnerBigonMap h r p) = p :=
  (innerBigonDiffeomorph h r hr).apply_symm_apply p

theorem continuousAt_inverseInnerBigonMap (h : ℝ) (p : ℝ × ℝ) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => inverseInnerBigonMap h z.1 z.2) (1, p) := by
  unfold inverseInnerBigonMap
  fun_prop (disch := norm_num)

theorem isCompact_innerBigonCollar {h r : ℝ} (hh : 0 < h) (hr : r ≠ 0) :
    IsCompact (innerBigonCollar h r) := by
  have ho : IsOpen (innerBigonMap h r '' interior (bigon h)) :=
    (innerBigonDiffeomorph h r hr).toHomeomorph.isOpenMap _ isOpen_interior
  exact (isCompact_bigon hh).inter_right ho.isClosed_compl

/-- A point of the inward disk belongs to the remaining collar exactly on the shared frontier. -/
theorem innerBigonMap_mem_collar_iff {h r : ℝ} (hh : 0 < h) (hr : r ∈ Ioo (0 : ℝ) 1)
    {p : ℝ × ℝ} (hp : p ∈ bigon h) :
    innerBigonMap h r p ∈ innerBigonCollar h r ↔ p ∈ frontier (bigon h) := by
  rw [frontier, (isClosed_bigon h).closure_eq]
  constructor
  · intro hx
    exact ⟨hp, fun hi => hx.2 (mem_image_of_mem _ hi)⟩
  · intro hx
    refine ⟨interior_subset (innerBigonMap_mem_interior hh hr hp), ?_⟩
    rintro ⟨q, hq, heq⟩
    have hqp : q = p := (innerBigonDiffeomorph h r hr.1.ne').injective heq
    exact hx.2 (hqp ▸ hq)

/-- A factor close enough to one makes the whole remaining collar, not just its inner edge,
lie inside the original open boundary neighborhood. -/
theorem exists_inner_bigon_collar_in_open {h : ℝ} (hh : 0 < h)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hfrontU : frontier (bigon h) ⊆ U) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧ innerBigonCollar h r ⊆ U ∧
      MapsTo (innerBigonMap h r) (frontier (bigon h)) (U ∩ interior (bigon h)) := by
  let bad : Set (ℝ × ℝ) := bigon h \ U
  have hbad : IsCompact bad := (isCompact_bigon hh).inter_right hU.isClosed_compl
  have hbadInterior : bad ⊆ interior (bigon h) := by
    intro p hp
    by_contra hi
    apply hp.2
    apply hfrontU
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hi⟩
  have hnearInv : ∀ᶠ r in 𝓝 (1 : ℝ),
      ∀ p ∈ bad, inverseInnerBigonMap h r p ∈ interior (bigon h) := by
    apply hbad.eventually_forall_of_forall_eventually
    intro p hp
    apply (continuousAt_inverseInnerBigonMap h p).preimage_mem_nhds
    apply isOpen_interior.mem_nhds
    simpa only [inverseInnerBigonMap_one] using hbadInterior hp
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  have hnearFront : ∀ᶠ r in 𝓝 (1 : ℝ),
      ∀ p ∈ frontier (bigon h), innerBigonMap h r p ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((contDiff_innerBigonMap h).continuous.continuousAt
      (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [innerBigonMap_one] using hfrontU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hnearInv.and hnearFront)
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
  have hretained := hball hrball
  refine ⟨1 - δ, hr, ?_, fun p hp => ⟨hretained.2 p hp, ?_⟩⟩
  · intro p hp
    by_contra hpU
    exact hp.2 ⟨inverseInnerBigonMap h (1 - δ) p, hretained.1 p ⟨hp.1, hpU⟩,
      inner_inverseInnerBigonMap h (1 - δ) hr.1.ne' p⟩
  · exact innerBigonMap_mem_interior hh hr ((mem_frontier_bigon_iff h p).mp hp).1

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
