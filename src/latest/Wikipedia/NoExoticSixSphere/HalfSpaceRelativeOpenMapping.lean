import Wikipedia.NoExoticSixSphere.ConvexLocalHomeomorphExtension
import Wikipedia.NoExoticSixSphere.HalfSpaceHomeomorphNeighborhood

/-!
# Relative openness at a regular boundary point

A continuously differentiable map on the closed half-space with invertible
derivative has a relatively open image near a boundary point if it sends
the boundary to the boundary and the positive side to the positive side.
The argument uses a proved topological extension, not a smooth extension.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology ContDiff

namespace NoExoticSixSphere.ProductHalfSpace

variable {B C : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]

theorem exists_halfSpace_image_neighborhood {f : (ℝ × B) → ℝ × C} {x : ℝ × B}
    (hx : x.1 = 0) (hf : ContDiffWithinAt ℝ 1 f {z | 0 ≤ z.1} x)
    (L : (ℝ × B) ≃L[ℝ] (ℝ × C))
    (hL : fderivWithin ℝ f {z | 0 ≤ z.1} x = L.toContinuousLinearMap)
    {U : Set (ℝ × B)} (hU : IsOpen U) (hxU : x ∈ U)
    (hz : ∀ z ∈ U, z.1 = 0 → (f z).1 = 0)
    (hp : ∀ z ∈ U, 0 < z.1 → 0 < (f z).1)
    {t : Set (ℝ × B)} (ht : t ∈ 𝓝[{z | 0 ≤ z.1}] x) :
    ∃ r : ℝ, 0 < r ∧ ball (f x) r ∩ {y | 0 ≤ y.1} ⊆ f '' t := by
  have hc : Convex ℝ {z : ℝ × B | 0 ≤ z.1} :=
    (convex_Ici (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ B)
  have hu : UniqueDiffOn ℝ {z : ℝ × B | 0 ≤ z.1} := by
    simpa only [model_range] using (model B).uniqueDiffOn
  obtain ⟨q, G, hq, hG⟩ := exists_homeomorph_nhdsWithin_of_convex_contDiffWithinAt
    hc hu (le_of_eq hx.symm) hf L hL
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp (inter_mem ht hq)
  let V := U ∩ ball x δ
  have hV : IsOpen V := hU.inter isOpen_ball
  have hxV : x ∈ V := ⟨hxU, mem_ball_self hδ⟩
  have hEq : ∀ z ∈ V, 0 ≤ z.1 → f z = G z :=
    fun z hzV hz0 ↦ hG (hsmall ⟨hzV.2, hz0⟩).2
  have hzero : ∀ z ∈ V, z.1 = 0 → (G z).1 = 0 := by
    intro z hzV hz0
    rw [← hEq z hzV (le_of_eq hz0.symm)]
    exact hz z hzV.1 hz0
  have hpos : ∀ z ∈ V, 0 < z.1 → 0 < (G z).1 := by
    intro z hzV hz0
    rw [← hEq z hzV hz0.le]
    exact hp z hzV.1 hz0
  obtain ⟨r, hr, hinv⟩ := exists_inverse_halfSpace_neighborhood G hx hV hxV hzero hpos
  have hxG : f x = G x := hEq x hxV (le_of_eq hx.symm)
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hyball : y ∈ ball (G x) r := by simpa only [← hxG] using hy.1
  obtain ⟨hyV, hy0⟩ := hinv y hyball hy.2
  refine ⟨G.symm y, (hsmall ⟨hyV.2, hy0⟩).1, ?_⟩
  rw [hEq (G.symm y) hyV hy0, G.apply_symm_apply]

theorem image_mem_nhdsWithin_halfSpace {f : (ℝ × B) → ℝ × C} {x : ℝ × B}
    (hx : x.1 = 0) (hf : ContDiffWithinAt ℝ 1 f {z | 0 ≤ z.1} x)
    (L : (ℝ × B) ≃L[ℝ] (ℝ × C))
    (hL : fderivWithin ℝ f {z | 0 ≤ z.1} x = L.toContinuousLinearMap)
    {U : Set (ℝ × B)} (hU : IsOpen U) (hxU : x ∈ U)
    (hz : ∀ z ∈ U, z.1 = 0 → (f z).1 = 0)
    (hp : ∀ z ∈ U, 0 < z.1 → 0 < (f z).1)
    {t : Set (ℝ × B)} (ht : t ∈ 𝓝[{z | 0 ≤ z.1}] x) :
    f '' t ∈ 𝓝[{y | 0 ≤ y.1}] (f x) :=
  Metric.mem_nhdsWithin_iff.mpr
    (exists_halfSpace_image_neighborhood hx hf L hL hU hxU hz hp ht)

end NoExoticSixSphere.ProductHalfSpace
