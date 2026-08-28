import Wikipedia.NoExoticSixSphere.ResidualLink

/-!
# The residual-coordinate link bounds an actual embedded local ball

The inverse-coordinate map on the closed unit four-ball is smooth and
injective, hence a closed embedding. Its restriction to the unit sphere is
the actual link, and its center is the original residual-zero point.
-/

noncomputable section

open Set Function Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne

theorem scaledVector_mem_closedBall {ε : ℝ} (hε : 0 < ε) {z : Vector 4}
    (hz : z ∈ closedBall (0 : Vector 4) 1) :
    ε • WhitneyCusp.residualCoordinates z ∈ closedBall (0 : Vector 4) ε := by
  have hn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε,
    WhitneyCusp.residualCoordinates.norm_map]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hε.le

variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {D : X → BlockMap E (Vector 4)}

def Data.ballMap (d : Data D) (ε : ℝ) (z : Vector 4) : X :=
  d.coord.symm (ε • WhitneyCusp.residualCoordinates z)

theorem Data.ballMap_link (d : Data D) (ε : ℝ) (q : Sphere 3) :
    d.ballMap ε q.val = d.link ε q := rfl

theorem Data.ballMap_zero (d : Data D) (ε : ℝ) {x : X} (hx : x ∈ d.coord.source)
    (hz : residual (D x) = 0) : d.ballMap ε 0 = x := by
  rw [Data.ballMap, map_zero, smul_zero]
  exact d.inverse_zero hx hz

theorem Data.ballMap_mem_source (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target)
    {z : Vector 4} (hz : z ∈ closedBall (0 : Vector 4) 1) :
    d.ballMap ε z ∈ d.coord.source :=
  d.coord.toOpenPartialHomeomorph.map_target (hball (scaledVector_mem_closedBall hε hz))

theorem Data.residual_ballMap (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target)
    {z : Vector 4} (hz : z ∈ closedBall (0 : Vector 4) 1) :
    residual (D (d.ballMap ε z)) = ε • WhitneyCusp.residualCoordinates z :=
  d.residual_inverse (hball (scaledVector_mem_closedBall hε hz))

theorem Data.singular_ballMap_iff (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target)
    {z : Vector 4} (hz : z ∈ closedBall (0 : Vector 4) 1) :
    ¬ Injective (D (d.ballMap ε z)) ↔ z = 0 := by
  rw [singular_iff_residual_zero (d.source_chart _ (d.ballMap_mem_source hε hball hz)),
    d.residual_ballMap hε hball hz]
  constructor
  · intro he
    apply WhitneyCusp.residualCoordinates.injective
    have hi := congrArg (fun v : Vector 4 ↦ ε⁻¹ • v) he
    simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul, smul_zero, map_zero] using hi
  · rintro rfl
    rw [map_zero, smul_zero]

theorem Data.contDiffOn_ballMap (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    ContDiffOn ℝ ∞ (d.ballMap ε) (closedBall (0 : Vector 4) 1) := by
  have hs : ContDiff ℝ ∞ (fun z : Vector 4 ↦ ε • WhitneyCusp.residualCoordinates z) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Vector 4 ↦ ε)).smul
      WhitneyCusp.residualCoordinates.contDiff
  exact d.coord.contMDiffOn_invFun.contDiffOn.comp hs.contDiffOn
    (fun _ hz ↦ hball (scaledVector_mem_closedBall hε hz))

theorem Data.ballMap_injOn (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    InjOn (d.ballMap ε) (closedBall (0 : Vector 4) 1) := by
  intro z hz w hw he
  apply WhitneyCusp.residualCoordinates.injective
  have hr := congrArg (fun x ↦ residual (D x)) he
  rw [d.residual_ballMap hε hball hz, d.residual_ballMap hε hball hw] at hr
  have hi := congrArg (fun v : Vector 4 ↦ ε⁻¹ • v) hr
  simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] using hi

theorem Data.ballMap_isClosedEmbedding (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) :
    IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ d.ballMap ε z.val) := by
  have hc := (d.contDiffOn_ballMap hε hball).continuousOn.domRestrict
  apply hc.isClosedEmbedding
  intro z w he
  exact Subtype.ext (d.ballMap_injOn hε hball z.property w.property he)

theorem Data.link_injective (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) : Injective (d.link ε) := by
  intro q r he
  apply Subtype.ext
  apply WhitneyCusp.residualCoordinates.injective
  have hr := congrArg (fun x ↦ residual (D x)) he
  rw [d.residual_link hε hball q, d.residual_link hε hball r] at hr
  change ε • WhitneyCusp.residualCoordinates q.val =
    ε • WhitneyCusp.residualCoordinates r.val at hr
  have hi := congrArg (fun v : Vector 4 ↦ ε⁻¹ • v) hr
  simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] using hi

theorem Data.link_isClosedEmbedding (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target) : IsClosedEmbedding (d.link ε) :=
  (d.continuous_link hε hball).isClosedEmbedding (d.link_injective hε hball)

theorem Data.link_ne_center (d : Data D) {ε : ℝ} (hε : 0 < ε)
    (hball : closedBall (0 : Vector 4) ε ⊆ d.coord.target)
    {x : X} (hz : residual (D x) = 0) (q : Sphere 3) : d.link ε q ≠ x := by
  intro he
  have hr := congrArg (fun y ↦ residual (D y)) he
  rw [d.residual_link hε hball q, hz] at hr
  exact scaledParameter_ne_zero hε q hr

end NoExoticSixSphere.ResidualCoordinates
