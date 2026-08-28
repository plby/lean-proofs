import Wikipedia.SmoothSixDPoincare.WhitneyModelGeometry
import Mathlib.Analysis.Convex.Star

/-!
# The actual cornered planar region between the Whitney model sheets

The region `0 ≤ t ≤ h (1 - s²)` is compact and star-convex when `h > 0`.
Its two boundary arcs lie on the two different model sheets; their endpoints
are the two transverse intersections. The open region between them avoids
both sheets. The ambient parametrization is smooth and immersive even at
the corners; no smooth-circle parametrization of this cornered boundary is used.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def bigon (h : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h}

def bigonEmbedding : (ℝ × ℝ) → Space := fun p => (p, (0, 0))

theorem isClosed_bigon (h : ℝ) : IsClosed (bigon h) :=
  (isClosed_le continuous_const continuous_snd).inter
    (isClosed_le (show Continuous (fun p : ℝ × ℝ => h * p.1 ^ 2 + p.2) by fun_prop)
      continuous_const)

theorem zero_mem_bigon {h : ℝ} (hh : 0 ≤ h) : (0 : ℝ × ℝ) ∈ bigon h := by
  exact ⟨le_rfl, by simpa using hh⟩

theorem bigon_subset_rectangle {h : ℝ} (hh : 0 < h) :
    bigon h ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) h := by
  intro p hp
  rcases hp with ⟨ht, hupper⟩
  have hsq : p.1 ^ 2 ≤ 1 := by nlinarith
  have hheight : p.2 ≤ h := by nlinarith [sq_nonneg p.1]
  exact ⟨⟨by nlinarith, by nlinarith⟩, ht, hheight⟩

theorem isCompact_bigon {h : ℝ} (hh : 0 < h) : IsCompact (bigon h) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (isClosed_bigon h) (bigon_subset_rectangle hh)

/-- The ordinary ambient interior is exactly the region strictly between the arcs. -/
theorem mem_interior_bigon_iff (h : ℝ) (p : ℝ × ℝ) :
    p ∈ interior (bigon h) ↔ 0 < p.2 ∧ p.2 < h * (1 - p.1 ^ 2) := by
  constructor
  · intro hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    have hd (a : ℝ) : dist (p.1, p.2 + a) p = |a| := by
      simp [Prod.dist_eq]
    have hm : (p.1, p.2 + (-ε / 2)) ∈ Metric.ball p ε := by
      change dist (p.1, p.2 + (-ε / 2)) p < ε
      rw [hd, abs_of_neg (by linarith)]
      linarith
    have hp' : (p.1, p.2 + ε / 2) ∈ Metric.ball p ε := by
      change dist (p.1, p.2 + ε / 2) p < ε
      rw [hd, abs_of_pos (by linarith)]
      linarith
    have hlo := (hball hm).1
    have hhi := (hball hp').2
    change 0 ≤ p.2 + (-ε / 2) at hlo
    change h * p.1 ^ 2 + (p.2 + ε / 2) ≤ h at hhi
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    let U : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ h * q.1 ^ 2 + q.2 < h}
    have hU : IsOpen U := (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (show Continuous (fun q : ℝ × ℝ => h * q.1 ^ 2 + q.2) by fun_prop)
        continuous_const)
    have hpU : p ∈ U := ⟨hlo, by nlinarith⟩
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hU.mem_nhds hpU) (fun _ hq => ⟨hq.1.le, hq.2.le⟩))

/-- The complete frontier consists of the two arcs, with their common endpoints included. -/
theorem mem_frontier_bigon_iff (h : ℝ) (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔
      p ∈ bigon h ∧ (p.2 = 0 ∨ p.2 = h * (1 - p.1 ^ 2)) := by
  rw [frontier, (isClosed_bigon h).closure_eq, mem_sdiff, mem_interior_bigon_iff]
  constructor
  · rintro ⟨hp, hnot⟩
    refine ⟨hp, ?_⟩
    by_cases ht : p.2 = 0
    · exact Or.inl ht
    · right
      have hlo : 0 < p.2 := lt_of_le_of_ne hp.1 (Ne.symm ht)
      have hhi : ¬p.2 < h * (1 - p.1 ^ 2) := fun hlt => hnot ⟨hlo, hlt⟩
      have hupper := hp.2
      change h * p.1 ^ 2 + p.2 ≤ h at hupper
      nlinarith
  · rintro ⟨hp, ht | ht⟩
    · exact ⟨hp, fun hstrict => hstrict.1.ne' ht⟩
    · exact ⟨hp, fun hstrict => hstrict.2.ne ht⟩

/-- Radial contraction stays in the actual parabolic bigon, including the corners. -/
theorem starConvex_bigon {h : ℝ} (hh : 0 ≤ h) : StarConvex ℝ (0 : ℝ × ℝ) (bigon h) := by
  rw [starConvex_zero_iff]
  intro p hp a ha₀ ha₁
  rcases hp with ⟨ht, hupper⟩
  change 0 ≤ a * p.2 ∧ h * (a * p.1) ^ 2 + a * p.2 ≤ h
  refine ⟨mul_nonneg ha₀ ht, ?_⟩
  calc
    h * (a * p.1) ^ 2 + a * p.2 =
        a * (h * p.1 ^ 2 + p.2) - (a * (1 - a)) * (h * p.1 ^ 2) := by ring
    _ ≤ a * (h * p.1 ^ 2 + p.2) :=
      sub_le_self _ (mul_nonneg (mul_nonneg ha₀ (sub_nonneg.mpr ha₁))
        (mul_nonneg hh (sq_nonneg _)))
    _ ≤ a * h := mul_le_mul_of_nonneg_left hupper ha₀
    _ ≤ h := by nlinarith

theorem contDiff_bigonEmbedding : ContDiff ℝ ∞ bigonEmbedding := by
  unfold bigonEmbedding
  fun_prop

theorem isClosedEmbedding_bigonEmbedding : IsClosedEmbedding bigonEmbedding := by
  have hleft : LeftInverse Prod.fst bigonEmbedding := fun _ => rfl
  exact hleft.isClosedEmbedding continuous_fst contDiff_bigonEmbedding.continuous

theorem injective_fderiv_bigonEmbedding (p : ℝ × ℝ) :
    Injective (fderiv ℝ bigonEmbedding p) := by
  let L : (ℝ × ℝ) →L[ℝ] Space := (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0
  have hd : HasFDerivAt bigonEmbedding L p := L.hasFDerivAt
  rw [hd.fderiv]
  have hleft : LeftInverse Prod.fst L := fun _ => rfl
  exact hleft.injective

theorem bigonEmbedding_mem_firstSheet_iff (p : ℝ × ℝ) :
    bigonEmbedding p ∈ range firstSheet ↔ p.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun z : Space => z.1.2) hq).symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

theorem bigonEmbedding_mem_secondSheet_iff (h : ℝ) (p : ℝ × ℝ) :
    bigonEmbedding p ∈ range (secondSheet h) ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · rintro ⟨q, hq⟩
    have hs : q.1 = p.1 := congrArg (fun z : Space => z.1.1) hq
    have ht : h * (1 - q.1 ^ 2) = p.2 := congrArg (fun z : Space => z.1.2) hq
    rw [hs] at ht
    exact ht.symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

theorem lowerArc_mem_bigon {h s : ℝ} (hh : 0 ≤ h) (hs : |s| ≤ 1) :
    (s, 0) ∈ bigon h := by
  have habs := abs_le.mp hs
  refine ⟨le_rfl, ?_⟩
  change h * s ^ 2 + 0 ≤ h
  have hsq : s ^ 2 ≤ 1 := by nlinarith
  simpa only [mul_one, add_zero] using mul_le_mul_of_nonneg_left hsq hh

theorem upperArc_mem_bigon {h s : ℝ} (hh : 0 ≤ h) (hs : |s| ≤ 1) :
    (s, h * (1 - s ^ 2)) ∈ bigon h := by
  have habs := abs_le.mp hs
  refine ⟨mul_nonneg hh (by nlinarith), ?_⟩
  change h * s ^ 2 + h * (1 - s ^ 2) ≤ h
  nlinarith

theorem bigonEmbedding_lowerArc (s : ℝ) : bigonEmbedding (s, 0) = firstSheet (s, 0) := rfl

theorem bigonEmbedding_upperArc (h s : ℝ) :
    bigonEmbedding (s, h * (1 - s ^ 2)) = secondSheet h (s, 0) := rfl

/-- Points strictly between the two arcs miss both full sheet images. -/
theorem bigonEmbedding_avoids_sheets (h : ℝ) (p : ℝ × ℝ)
    (hlower : 0 < p.2) (hupper : p.2 < h * (1 - p.1 ^ 2)) :
    bigonEmbedding p ∉ range firstSheet ∪ range (secondSheet h) := by
  rintro (hp | hp)
  · exact hlower.ne' ((bigonEmbedding_mem_firstSheet_iff p).mp hp)
  · exact hupper.ne ((bigonEmbedding_mem_secondSheet_iff h p).mp hp)

/-- For small positive height, the complete bigon is in the cutoff plateau. -/
theorem cutoff_bigonEmbedding {h : ℝ} (hh : 0 < h) (hsmall : h ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ bigon h) : cutoff (bigonEmbedding p) = 1 := by
  obtain ⟨hs, ht⟩ := bigon_subset_rectangle hh hp
  have hsB : realBump p.1 = 1 := by
    apply realBump.one_of_mem_closedBall
    change dist p.1 0 ≤ 1
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_le, mem_Icc] using hs
  have htB : realBump p.2 = 1 := by
    apply realBump.one_of_mem_closedBall
    change dist p.2 0 ≤ 1
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2.trans hsmall
  have hp0 : planeBump 0 = 1 :=
    planeBump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  change (realBump p.1 * realBump p.2) * (planeBump 0 * planeBump 0) = 1
  rw [hsB, htB, hp0]
  norm_num

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
