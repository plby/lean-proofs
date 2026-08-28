import Wikipedia.HopfProblem.OrbitPairAmbientPointParameters
import Wikipedia.HopfProblem.OrbitPairLocalProjectedCollisionFiber
import Wikipedia.HopfProblem.OrbitPairNativeCenteredChart
import Wikipedia.HopfProblem.OrbitPairAmbientClockStability
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Globally exact projected fibers at a selected ordinary collision

Construct a clock supported in the interval where the old projected fiber
is exactly the two collision sources. A generic ambient parameter leaves
only old coincidences with equal clock weight. At the selected value the
target bump and clock equal one, forcing every surviving preimage into
that interval. The new projected fiber is therefore globally the intended
pair, with no preimages at remote times.

All synchronized collisions are retained exactly, all collision-source
full derivatives remain injective, and no new projected coincidences are
created with any of the finitely many old collision sources. The last
condition permits finite iteration without losing previously prepared
global fibers.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open ClockVelocity AmbientPointParameters

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_global_projected_fiber_at_collision
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hiF : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hrF : SynchronizedPairs.RegularOn (I := I) (J := J) F {q | q.2.1 ≠ q.2.2})
    (hfinite : (FamilyDoublePoints.doublePoints F).Finite)
    (hno : FamilyDoublePoints.triplePoints F = ∅)
    (hfull : ∀ q ∈ FamilyDoublePoints.collisionSources F,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F q))
    (hdim : Module.finrank ℝ (ℝ × E) < Module.finrank ℝ G)
    {p : ℝ × (M × M)} (hp : p ∈ FamilyDoublePoints.doublePoints F)
    {U : Set ℝ} (hU : IsOpen U) (hpU : p.1 ∈ U) :
    ∃ F' : ℝ × M → N, ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F' ∧
      FamilyDoublePoints.doublePoints F' = FamilyDoublePoints.doublePoints F ∧
      (∀ t x, Injective (mfderiv I J (fun y => F' (t, y)) x)) ∧
      SynchronizedPairs.RegularOn (I := I) (J := J) F' {q | q.2.1 ≠ q.2.2} ∧
      (FamilyDoublePoints.doublePoints F').Finite ∧ FamilyDoublePoints.triplePoints F' = ∅ ∧
      (∀ q ∈ FamilyDoublePoints.collisionSources F',
        Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F' q)) ∧
      (∀ t x, t ∉ U → F' (t, x) = F (t, x)) ∧
      (∀ q ∈ FamilyDoublePoints.collisionSources F, ∀ z,
        F' q = F' z → F q = F z) ∧
      (∀ z : ℝ × M, F' z = F' (SynchronizedPairs.first p) ↔
        z = SynchronizedPairs.first p ∨ z = SynchronizedPairs.second p) := by
  obtain ⟨a, b, hab, habU⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hpU)
  obtain ⟨l, r, hplr, hlrab, hlocal⟩ :=
    exists_local_projected_fiber_of_ordinary_collision hF hno hfull hp hab.1 hab.2
  let q₀ := SynchronizedPairs.first p
  let Φ := NativeCenteredChart.chart (I := J) (F q₀)
  have hzero : (0 : G) ∈ Φ.source := NativeCenteredChart.zero_mem_source (F q₀)
  have hΦzero : Φ 0 = F q₀ := NativeCenteredChart.chart_zero (F q₀)
  have hqtarget : F q₀ ∈ Φ.target := hΦzero ▸ Φ.map_source' hzero
  have hqcoord : Φ.symm (F q₀) = 0 :=
    (congrArg Φ.symm hΦzero).symm.trans (Φ.left_inv' hzero)
  obtain ⟨β, hβsupport, hβcompact, hβ, -, hβone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (Φ.open_source.mem_nhds hzero)
  obtain ⟨κ, hκsupport, -, hκ, hκrange, hκone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (isOpen_Ioo.mem_nhds hplr)
  have hbound : ∀ t, ‖κ t‖ ≤ 1 := by
    intro t
    have hκt := hκrange (mem_range_self t)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hκt.1] using hκt.2
  obtain ⟨ρ, hρ, hall⟩ := exists_radius_clock_changed_family Φ hβ hβcompact hβsupport
    hκ hbound hF hiF hrF
  have hC := FamilyDoublePoints.finite_collisionSources hfinite
  have hkeep := eventually_clock_preserves_full_immersion Φ hβ hβcompact hβsupport
    hκ hbound hF hC.isCompact hfull
  have hsmall : ∀ᶠ v : G in 𝓝 0, ‖v‖ < ρ :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by
      change ‖(0 : G)‖ < ρ
      simpa only [norm_zero] using hρ)
  obtain ⟨v, -, hv, hpoints⟩ := exists_small_clock_no_new_finite_point_coincidences
    Φ F β κ hF hβ hβcompact hβsupport hκ hbound hC hdim (hsmall.and hkeep)
      (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨hF', hD, hiF', hrF', hfixed⟩ := hall v hv.1
  let F' := family Φ F β κ v
  change FamilyDoublePoints.doublePoints F' = FamilyDoublePoints.doublePoints F at hD
  have hsourceEq := FamilyDoublePoints.collisionSources_eq_of_doublePoints_eq hD
  have hp₀ : q₀ ∈ FamilyDoublePoints.collisionSources F := Or.inl ⟨p, hp, rfl⟩
  refine ⟨F', hF', hD, hiF', hrF', hD.symm ▸ hfinite, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FamilyDoublePoints.triplePoints_eq_of_doublePoints_eq hD]
    exact hno
  · intro q hq
    rw [hsourceEq] at hq
    exact hv.2 q hq
  · intro t x ht
    apply hfixed t x
    left
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => ht (habU (hlrab (hκsupport h)))
  · exact fun q hq z hz => (hpoints q hq z hz).1
  · intro z
    constructor
    · intro hz
      obtain ⟨hold, hweights⟩ := hpoints q₀ hp₀ z hz.symm
      have hw := hweights hqtarget
      change β (Φ.symm (F q₀)) * κ p.1 = β (Φ.symm (F z)) * κ z.1 at hw
      rw [← hold, hqcoord, hβone, hκone, one_mul, one_mul] at hw
      have hκz : κ z.1 ≠ 0 := by rw [← hw]; exact one_ne_zero
      have hztime : z.1 ∈ Ioo l r := hκsupport (subset_tsupport κ hκz)
      exact (hlocal z hztime).mp hold.symm
    · rintro (rfl | rfl)
      · rfl
      · have hp' : p ∈ FamilyDoublePoints.doublePoints F' := hD.symm ▸ hp
        exact hp'.2.symm

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
