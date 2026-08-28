import Wikipedia.NoExoticSixSphere.WhitneyCuspTransverseDoublePoint
import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff

/-!
# A compactly supported cusp modification of an actual embedded model

Only the last coordinate of the negative-parameter Whitney cusp changes.
The cutoff is one on the radius-two ball and supported in the radius-three
ball. Thus the born crossing remains in the exact polynomial model while
the entire family agrees with the original embedding outside a compact set.
-/

noncomputable section

open Set Function Filter Topology Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

structure Cutoff where
  value : Vector 3 → ℝ
  smooth : ContDiff ℝ ∞ value
  compact : HasCompactSupport value
  support : tsupport value ⊆ ball 0 3
  one : ∀ x, ‖x‖ ≤ 2 → value x = 1
  bounds : ∀ x, value x ∈ Icc (0 : ℝ) 1

theorem nonempty_cutoff : Nonempty Cutoff := by
  have hsub : closedBall (0 : Vector 3) 2 ⊆ ball 0 3 := by
    intro x hx
    change dist x 0 ≤ 2 at hx
    change dist x 0 < 3
    exact lt_of_le_of_lt hx (by norm_num)
  obtain ⟨β, hβ, hc, hs, hone, hb⟩ :=
    exists_compact_smooth_cutoff (isCompact_closedBall (0 : Vector 3) 2) isOpen_ball hsub
  refine ⟨⟨β, hβ, hc, hs, ?_, hb⟩⟩
  intro x hx
  exact hone.self_of_nhdsSet x (by simpa only [mem_closedBall, dist_zero_right] using hx)

def map (β : Vector 3 → ℝ) (t : ℝ) (x : Vector 3) : Vector 6 :=
  WithLp.toLp 2 ![x 0, x 1, x 2 ^ 2, x 0 * x 2, x 1 * x 2,
    x 2 ^ 3 + x 2 - (t + 1) * β x * x 2]

theorem contDiff_map {β : Vector 3 → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (uncurry (map β)) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × Vector 3 ↦ q.2 i) :=
    (contDiff_piLp_apply 2).comp contDiff_snd
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact (hc 2).pow 2
  · exact (hc 0).mul (hc 2)
  · exact (hc 1).mul (hc 2)
  · exact (((hc 2).pow 3).add (hc 2)).sub
      (((contDiff_fst.add contDiff_const).mul (hβ.comp contDiff_snd)).mul (hc 2))

theorem map_neg_one (β : Vector 3 → ℝ) (x : Vector 3) :
    map β (-1) x = WhitneyCusp.map (-1) x := by
  ext i
  fin_cases i <;> simp [map, WhitneyCusp.map]

theorem map_eq_cusp_of_one {β : Vector 3 → ℝ} (t : ℝ) {x : Vector 3} (hx : β x = 1) :
    map β t x = WhitneyCusp.map t x := by
  ext i
  fin_cases i <;> simp [map, WhitneyCusp.map, hx]
  ring

theorem map_eq_cusp_near (β : Cutoff) (t : ℝ) {x : Vector 3} (hx : ‖x‖ < 2) :
    map β.value t =ᶠ[𝓝 x] WhitneyCusp.map t := by
  have hx' : x ∈ ball (0 : Vector 3) 2 := by simpa only [mem_ball, dist_zero_right] using hx
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  apply map_eq_cusp_of_one
  apply β.one y
  exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy)

theorem map_eq_base_off_support (β : Vector 3 → ℝ) (t : ℝ) {x : Vector 3}
    (hx : x ∉ tsupport β) : map β t x = WhitneyCusp.map (-1) x := by
  have hβ : β x = 0 := image_eq_zero_of_notMem_tsupport hx
  ext i
  fin_cases i <;> simp [map, WhitneyCusp.map, hβ]

theorem norm_axis (z : ℝ) : ‖WhitneyCusp.axis z‖ = |z| := by
  rw [EuclideanSpace.norm_eq]
  simp [WhitneyCusp.axis, Fin.sum_univ_succ, Real.sqrt_sq_eq_abs]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
