import Wikipedia.HopfProblem.HolomorphicCousinUniqueness

/-!
# Analytic gluing and uniqueness on arbitrary open covers

Compatible holomorphic functions on an arbitrary open cover of the complex
plane glue to an actual entire function.  If one member of the cover contains
a neighborhood of infinity and agrees there with a holomorphic function in
the reciprocal coordinate, Liouville's theorem proves that all local functions
are constant.  The same argument proves vanishing for negative twists.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicCousin

variable {ι : Type*}

/-- Choose a cover member at each point and evaluate its local function.
Compatibility is used to prove independence of the choice and analyticity. -/
def openCoverGlue (U : ι → Set ℂ) (hcover : ∀ z : ℂ, ∃ i, z ∈ U i)
    (f : ι → ℂ → ℂ) (z : ℂ) : ℂ := f (hcover z).choose z

/-- The chosen function agrees exactly with every representative on its domain. -/
theorem openCoverGlue_eq {U : ι → Set ℂ} {hcover : ∀ z : ℂ, ∃ i, z ∈ U i}
    {f : ι → ℂ → ℂ}
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) {i : ι} {z : ℂ}
    (hz : z ∈ U i) : openCoverGlue U hcover f z = f i z :=
  hfg (hcover z).choose i ⟨(hcover z).choose_spec, hz⟩

/-- Local agreement holds throughout a neighborhood inside the chosen domain. -/
theorem openCoverGlue_eventuallyEq {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {hcover : ∀ z : ℂ, ∃ i, z ∈ U i}
    {f : ι → ℂ → ℂ}
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) {i : ι} {z : ℂ}
    (hz : z ∈ U i) : openCoverGlue U hcover f =ᶠ[𝓝 z] f i := by
  filter_upwards [(hU i).mem_nhds hz] with w hw
  exact openCoverGlue_eq hfg hw

/-- The glued function is analytic at every point of the complex plane. -/
theorem openCoverGlue_analyticAt {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {hcover : ∀ z : ℂ, ∃ i, z ∈ U i}
    {f : ι → ℂ → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) (z : ℂ) :
    AnalyticAt ℂ (openCoverGlue U hcover f) z := by
  obtain ⟨i, hi⟩ := hcover z
  exact (hf i z hi).congr (openCoverGlue_eventuallyEq hU hfg hi).symm

/-- An analytic reciprocal-coordinate representative supplies the actual
limit of the globally glued function at infinity. -/
theorem openCoverGlue_tendsto_cocompact {U : ι → Set ℂ}
    {hcover : ∀ z : ℂ, ∃ i, z ∈ U i} {f : ι → ℂ → ℂ}
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) {i₀ : ι} {R : ℝ}
    (hR : 0 < R) (htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 R⁻¹))
    (hinfty : ∀ z : ℂ, R < ‖z‖ → f i₀ z = G z⁻¹) :
    Tendsto (openCoverGlue U hcover f) (cocompact ℂ) (𝓝 (G 0)) := by
  have hG0 : ContinuousAt G 0 :=
    (hG 0 (by simpa only [mem_ball, dist_self] using inv_pos.mpr hR)).continuousAt
  have hlim : Tendsto (fun z : ℂ => G z⁻¹) (Bornology.cobounded ℂ) (𝓝 (G 0)) :=
    hG0.tendsto.comp tendsto_inv₀_cobounded
  rw [← Metric.cobounded_eq_cocompact]
  apply hlim.congr'
  filter_upwards [eventually_cobounded_le_norm (R + 1)] with z hz
  have hzR : R < ‖z‖ := (lt_add_one R).trans_le hz
  exact ((openCoverGlue_eq hfg (htail z hzR)).trans (hinfty z hzR)).symm

/-- The entire function constructed by analytic gluing is constant when it
extends holomorphically across infinity. -/
theorem openCoverGlue_eq_const {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {hcover : ∀ z : ℂ, ∃ i, z ∈ U i}
    {f : ι → ℂ → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) {i₀ : ι} {R : ℝ}
    (hR : 0 < R) (htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 R⁻¹))
    (hinfty : ∀ z : ℂ, R < ‖z‖ → f i₀ z = G z⁻¹) (z : ℂ) :
    openCoverGlue U hcover f z = G 0 := by
  have hd : Differentiable ℂ (openCoverGlue U hcover f) :=
    fun w => (openCoverGlue_analyticAt hU hf hfg w).differentiableAt
  exact hd.apply_eq_of_tendsto_cocompact z
    (openCoverGlue_tendsto_cocompact hfg hR htail hG hinfty)

/-- **Global analytic uniqueness on an arbitrary cover.** Compatible local
holomorphic functions which extend across infinity are all constant. -/
theorem eq_const_of_open_cover_agreement {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z : ℂ, ∃ i, z ∈ U i)
    {f : ι → ℂ → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) {i₀ : ι} {R : ℝ}
    (hR : 0 < R) (htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 R⁻¹))
    (hinfty : ∀ z : ℂ, R < ‖z‖ → f i₀ z = G z⁻¹) :
    (∀ i, EqOn (f i) (fun _ => G 0) (U i)) ∧
      EqOn G (fun _ => G 0) (ball 0 R⁻¹) := by
  have hc (z : ℂ) : openCoverGlue U hcover f z = G 0 :=
    openCoverGlue_eq_const hU hf hfg hR htail hG hinfty z
  have hlocal (i : ι) : EqOn (f i) (fun _ => G 0) (U i) := by
    intro z hz
    exact (openCoverGlue_eq hfg hz).symm.trans (hc z)
  refine ⟨hlocal, ?_⟩
  intro u hu
  by_cases hu0 : u = 0
  · simp only [hu0]
  · have hu' : ‖u‖ < R⁻¹ := by
      simpa only [mem_ball, dist_zero_right] using hu
    have hRu : R < ‖u⁻¹‖ := by
      rw [norm_inv]
      exact (lt_inv_comm₀ hR (norm_pos_iff.mpr hu0)).mpr hu'
    simpa only [inv_inv] using
      (hinfty u⁻¹ hRu).symm.trans (hlocal i₀ (htail u⁻¹ hRu))

/-- A compatible section of a negative-degree transition function on an
arbitrary open cover vanishes on every member and on the reciprocal chart. -/
theorem negative_twist_eq_zero_of_open_cover {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z : ℂ, ∃ i, z ∈ U i)
    {f : ι → ℂ → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hfg : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) {i₀ : ι} {R : ℝ}
    (hR : 0 < R) (htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀)
    {m : ℕ} (hm : 0 < m) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 R⁻¹))
    (hinfty : ∀ z : ℂ, R < ‖z‖ → f i₀ z = z⁻¹ ^ m * G z⁻¹) :
    (∀ i, EqOn (f i) (fun _ => 0) (U i)) ∧ EqOn G (fun _ => 0) (ball 0 R⁻¹) := by
  have hH : AnalyticOnNhd ℂ (fun u => u ^ m * G u) (ball 0 R⁻¹) :=
    fun u hu => (analyticAt_id.pow m).mul (hG u hu)
  obtain ⟨hfconst, hHconst⟩ :=
    eq_const_of_open_cover_agreement hU hcover hf hfg hR htail hH hinfty
  have hfinite : ∀ i, EqOn (f i) (fun _ => 0) (U i) := by
    simpa only [zero_pow hm.ne', zero_mul] using hfconst
  have hGoff (u : ℂ) (hu : u ∈ ball (0 : ℂ) R⁻¹) (hu0 : u ≠ 0) : G u = 0 := by
    have he : u ^ m * G u = 0 := by
      simpa only [zero_pow hm.ne', zero_mul] using hHconst hu
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero m hu0)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R⁻¹ := by
    simpa only [mem_ball, dist_self] using inv_pos.mpr hR
  have hlim : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) :=
    (hG 0 h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : G =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds h0)] with u hu0 hu
    exact hGoff u hu hu0
  have hG0 : G 0 = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero.symm)
  refine ⟨hfinite, fun u hu => ?_⟩
  by_cases hu0 : u = 0
  · simpa only [hu0] using hG0
  · exact hGoff u hu hu0

end Wikipedia.HopfProblem.HolomorphicCousin
