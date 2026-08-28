import Wikipedia.HopfProblem.DegreeCollapseIntegralPrimitiveDirection
import Wikipedia.HopfProblem.DegreeCollapseIntegralLocalAssembly
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedHomology

/-!
# Local constancy of the integral coordinates of an original top class

On a compact chart neighborhood, subtract the appropriate integer
multiple of its constructed chart class from the original restricted
absolute class. The actual local boundary witness makes this difference
vanish on a smaller neighborhood. Thus the original local coordinates
are constant there. Primitive direction is independent of the chart.
-/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralLocalNormalization

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

theorem evaluate_fromAbsolute (K : Set M) (x : M) (hx : x ∈ K) (d : ℕ)
    (a : SingularHomology M d) :
    evaluate (ModuleCat.of ℤ ℤ) K x hx d (fromAbsolute (ModuleCat.of ℤ ℤ) K d a) =
      fromAbsolute (ModuleCat.of ℤ ℤ) {x} d a :=
  LinearMap.congr_fun (restrict_fromAbsolute (ModuleCat.of ℤ ℤ)
    (Set.singleton_subset_iff.mpr hx) d) a

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]
  [T2Space M] [ChartedSpace E M]

/-- The original chart marking with the actual coefficient-object source type explicit. -/
def chartMark (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    Homology (ModuleCat.of ℤ ℤ) {x} (n + 2) ≃ₗ[ℤ] ℤ :=
  RelativeSingularHomology.chartLocalTopEquiv n e x hx

def direction (a : SingularHomology M (n + 2)) : IntegralLocalAssembly.Values M (n + 2) :=
  fun x => IntegralPrimitiveDirection.normalize
    (chartMark n (chartAt E x) x (mem_chart_source E x))
    (fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a)

theorem direction_in_chart (a : SingularHomology M (n + 2))
    (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    direction (E := E) n a x = IntegralPrimitiveDirection.normalize (chartMark n e x hx)
      (fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a) :=
  IntegralPrimitiveDirection.normalize_independent
    (chartMark n (chartAt E x) x (mem_chart_source E x)) (chartMark n e x hx) _

omit [ChartedSpace E M] in
/-- The original absolute class has locally constant coordinates in any supplied actual chart. -/
theorem exists_local_coefficient_in_chart (a : SingularHomology M (n + 2))
    (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hUs : U ⊆ e.source, ∃ k : ℤ, ∀ (y : M) (hy : y ∈ U),
        fromAbsolute (ModuleCat.of ℤ ℤ) {y} (n + 2) a = k • (chartMark n e y (hUs hy)).symm 1 := by
  obtain ⟨R, hR, hRtarget, _⟩ := ChartClosedBall.exists_support_subset e x hx univ univ_mem
  let B := ChartClosedBall.support e (e x) R
  have hB : IsCompact B := ChartClosedBall.support_isCompact e (e x) R hRtarget
  have hBs : B ⊆ e.source := ChartClosedBall.support_subset_source e (e x) R hRtarget
  have hxint : x ∈ interior B := mem_interior_iff_mem_nhds.mpr
    (ChartClosedBall.support_mem_nhds e x hx R hR hRtarget)
  have hxB : x ∈ B := interior_subset hxint
  let b := IntegralChartOrientation.fundamentalClass n e B hB hBs
  let k : ℤ := chartMark n e x hx (fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a)
  have hax : fromAbsolute (ModuleCat.of ℤ ℤ) {x} (n + 2) a = k • (chartMark n e x hx).symm 1 := by
    apply (chartMark n e x hx).injective
    rw [map_zsmul, LinearEquiv.apply_symm_apply]
    change k = (k : ℤ) • (1 : ℤ)
    simp only [zsmul_eq_mul, Int.cast_id, mul_one]
  have hbx : evaluate (ModuleCat.of ℤ ℤ) B x hxB (n + 2) b = (chartMark n e x hx).symm 1 :=
    IntegralChartOrientation.fundamentalClass_evaluate n e B hB hBs x hxB
  let c : Homology (ModuleCat.of ℤ ℤ) B (n + 2) :=
    fromAbsolute (ModuleCat.of ℤ ℤ) B (n + 2) a - k • b
  have hc : evaluate (ModuleCat.of ℤ ℤ) B x hxB (n + 2) c = 0 := by
    change evaluate (ModuleCat.of ℤ ℤ) B x hxB (n + 2)
      (fromAbsolute (ModuleCat.of ℤ ℤ) B (n + 2) a - k • b) = 0
    rw [map_sub, map_zsmul, evaluate_fromAbsolute B x hxB (n + 2) a, hbx]
    exact sub_eq_zero.mpr hax
  obtain ⟨V, hV, hxV, hzero⟩ := exists_zero_restriction_neighborhood (ModuleCat.of ℤ ℤ)
    B (n + 2) c x hxB hc
  let U := V ∩ interior B
  have hUs : U ⊆ e.source := fun y hy => hBs (interior_subset hy.2)
  refine ⟨U, hV.inter isOpen_interior, ⟨hxV, hxint⟩, hUs, k, ?_⟩
  intro y hy
  have hyB : y ∈ B := interior_subset hy.2
  have hz := hzero {y} (Set.singleton_subset_iff.mpr hyB) (Set.singleton_subset_iff.mpr hy.1)
  change evaluate (ModuleCat.of ℤ ℤ) B y hyB (n + 2)
    (fromAbsolute (ModuleCat.of ℤ ℤ) B (n + 2) a - k • b) = 0 at hz
  have hby : evaluate (ModuleCat.of ℤ ℤ) B y hyB (n + 2) b =
      (chartMark n e y (hUs hy)).symm 1 :=
    IntegralChartOrientation.fundamentalClass_evaluate n e B hB hBs y hyB
  rw [map_sub, map_zsmul, evaluate_fromAbsolute B y hyB (n + 2) a, hby] at hz
  exact sub_eq_zero.mp hz

/-- The original absolute class has one fixed integral coordinate on a genuine neighborhood. -/
theorem exists_local_coefficient (a : SingularHomology M (n + 2)) (x : M) :
    ∃ (e : OpenPartialHomeomorph M E) (U : Set M), IsOpen U ∧ x ∈ U ∧
      ∃ hUs : U ⊆ e.source, ∃ k : ℤ, ∀ (y : M) (hy : y ∈ U),
        fromAbsolute (ModuleCat.of ℤ ℤ) {y} (n + 2) a = k • (chartMark n e y (hUs hy)).symm 1 := by
  obtain ⟨U, hU, hxU, hUs, k, hk⟩ := exists_local_coefficient_in_chart n a
    (chartAt E x) x (mem_chart_source E x)
  exact ⟨chartAt E x, U, hU, hxU, hUs, k, hk⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralLocalNormalization
