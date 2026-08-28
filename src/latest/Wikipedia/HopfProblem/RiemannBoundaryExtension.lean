import Wikipedia.HopfProblem.RiemannBoundaryCircle
import Wikipedia.HopfProblem.RiemannBoundaryProper

/-!
# Local analytic extension of a Riemann map at a straight boundary

This file removes the boundedness and nonvanishing hypotheses from the
rectangle reflection theorem. Both follow locally from the unit-modulus
limit. In particular no boundary argument or continuous boundary extension
is assumed.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannBoundary

theorem dist_lt_two_mul_of_mem_centeredRectangle {x r : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle (x - r) (x + r) (-r) r) :
    dist z (x : ℂ) < 2 * r := by
  have hre : |(z - x).re| < r := by
    simp only [sub_re, ofReal_re]
    exact abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |(z - x).im| < r := by
    simpa only [sub_im, ofReal_im, sub_zero] using abs_lt.mpr hz.2
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (z - x)).trans_lt (by linarith)

theorem ball_subset_centeredRectangle (x r : ℝ) :
    ball (x : ℂ) r ⊆ openRectangle (x - r) (x + r) (-r) r := by
  intro z hz
  have hn : ‖z - x‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  have hre := abs_lt.mp ((abs_re_le_norm (z - x)).trans_lt hn)
  have him := abs_lt.mp ((abs_im_le_norm (z - x)).trans_lt hn)
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hre him
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩

/-- **Local unit-circle reflection from modulus limits.** A holomorphic
map on the upper part of an open neighborhood extends analytically across
each real boundary point when only its modulus tends to one there.
Neither a phase limit nor a preexisting continuous extension is required. -/
theorem exists_analytic_extension_of_modulus_one
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U)
    (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod : ∀ t : ℝ, (t : ℂ) ∈ U →
      Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1)) :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (x : ℂ) r) ∧
      EqOn H f (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (f (conj z)))⁻¹)
        (ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (x : ℂ) hx
  obtain ⟨δ, hδ, hδf⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hmod x hx)
    (1/2) (by norm_num)
  let r : ℝ := min ε δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : 2 * r < ε := by
    have hm := min_le_left ε δ
    dsimp [r]
    linarith
  have hrδ : 2 * r < δ := by
    have hm := min_le_right ε δ
    dsimp [r]
    linarith
  have hrectU : openRectangle (x - r) (x + r) (-r) r ⊆ U := by
    intro z hz
    apply hεU
    exact (dist_lt_two_mul_of_mem_centeredRectangle hz).trans hrε
  have hu : openRectangle (x - r) (x + r) 0 r ⊆ U ∩ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ⟨hrectU ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩, hz.2.1⟩
  have hsize : ∀ z ∈ openRectangle (x - r) (x + r) 0 r,
      1/2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 := by
    intro z hz
    have hzR : z ∈ openRectangle (x - r) (x + r) (-r) r :=
      ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    have he := hδf hz.2.1 ((dist_lt_two_mul_of_mem_centeredRectangle hzR).trans hrδ)
    rw [Real.dist_eq, abs_lt] at he
    constructor <;> linarith [he.1, he.2]
  have hmodR : ∀ t ∈ Ioo (x - r) (x + r),
      Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1) := by
    intro t ht
    apply hmod
    apply hrectU
    simpa only [openRectangle, mem_ofPred_eq, ofReal_re, ofReal_im] using
      And.intro ht (show (0 : ℝ) ∈ Ioo (-r) r by constructor <;> linarith)
  obtain ⟨H, hH, hHe, hHl, hHcircle⟩ :=
    exists_analytic_extension_of_modulus_one_bounded (by linarith) hr
      (show (0 : ℝ) < 1/2 by norm_num) (hf.mono hu)
      (fun z hz => (hsize z hz).2) (fun z hz => (hsize z hz).1) hmodR
  refine ⟨r, hr, H, hH.mono (ball_subset_centeredRectangle x r), ?_, ?_, ?_⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHe ⟨hzR.1, hz.2, hzR.2.2⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHl ⟨hzR.1, hzR.2.1, hz.2⟩
  · intro t ht
    have htR := ball_subset_centeredRectangle x r ht
    exact hHcircle t (by simpa only [ofReal_re] using htR.1)

/-- The properness norm limit at a point outside the domain, for an
arbitrary ambient representative of a genuine disc homeomorphism. -/
theorem tendsto_norm_discHomeomorph_nhdsWithin_of_notMem
    {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {a : ℂ} (ha : a ∉ D) :
    Tendsto (fun z => ‖f z‖) (𝓝[D] a) (𝓝 1) := by
  have hz : Tendsto (Subtype.val : D → ℂ)
      (comap (Subtype.val : D → ℂ) (𝓝[D] a)) (𝓝 a) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have ht := RiemannMapping.tendsto_norm_discHomeomorph_of_notMem e ha hz
  apply (tendsto_comap'_iff (i := (Subtype.val : D → ℂ)) ?_).mp
  · simpa only [Function.comp_def, he] using ht
  · simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : D ∈ 𝓝[D] a)

/-- Properness supplies the modulus limit in a straight boundary
coordinate. Only actual chart-side membership and continuity are needed. -/
theorem tendsto_norm_discHomeomorph_in_boundary_chart
    {D U : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f φ : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hφ : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    {x : ℝ} (hx : (x : ℂ) ∈ U) (hout : φ (x : ℂ) ∉ D) :
    Tendsto (fun z => ‖f (φ z)‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1) := by
  apply (tendsto_norm_discHomeomorph_nhdsWithin_of_notMem e he hout).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc := hφ (x : ℂ) ⟨hx, by simp⟩
    apply hc.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_id.mono_right nhdsWithin_le_nhds
    · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
      exact ⟨hz, le_of_lt hu⟩
  · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
    exact hside ⟨hz, hu⟩

/-- **Analytic extension of a genuine disc uniformization at a straight
boundary chart.** The unit-modulus limit is proved by properness, not
assumed. The original uniformization may have no specified boundary values. -/
theorem exists_analytic_extension_discHomeomorph_in_boundary_chart
    {D U : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f φ : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f D) (hφ : DifferentiableOn ℂ φ U)
    (hside : MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ U → φ (t : ℂ) ∉ D)
    {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (x : ℂ) r) ∧
      EqOn H (f ∘ φ) (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (f (φ (conj z))))⁻¹)
        (ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1 := by
  apply exists_analytic_extension_of_modulus_one hU hx
    (hf.comp (hφ.mono inter_subset_left) hside)
  intro t ht
  exact tendsto_norm_discHomeomorph_in_boundary_chart e he hU
    (hφ.continuousOn.mono inter_subset_left) hside ht (hout t ht)

/-- Version for a boundary coordinate holomorphic only in the upper
half-neighborhood and continuous on its closure. This includes inverse
power coordinates at analytic corners. -/
theorem exists_analytic_extension_discHomeomorph_in_half_chart
    {D U : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f φ : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f D)
    (hφ : DifferentiableOn ℂ φ (U ∩ {z : ℂ | 0 < z.im}))
    (hφc : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ U → φ (t : ℂ) ∉ D)
    {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (x : ℂ) r) ∧
      EqOn H (f ∘ φ) (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (f (φ (conj z))))⁻¹)
        (ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1 := by
  apply exists_analytic_extension_of_modulus_one hU hx (hf.comp hφ hside)
  intro t ht
  exact tendsto_norm_discHomeomorph_in_boundary_chart e he hU hφc hside ht (hout t ht)

end Wikipedia.HopfProblem.RiemannBoundary
