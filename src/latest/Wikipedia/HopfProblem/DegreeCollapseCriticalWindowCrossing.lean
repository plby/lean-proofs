import Wikipedia.HopfProblem.DegreeCollapseFiniteFamilyLevelTransport

/-!
# Excluding the central endpoint forces actual passage through the old window

The modified flow need not use the original window radii. The unchanged
height and critical values still show that an upper-level orbit whose
forward limit is not the one central critical point reaches the original
lower level. The proved level-holonomy basin formula supplies that exclusion.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.reaches_lower_of_excluded_critical_limit
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (p : M) (hwindow : ∀ q ∈ criticalPoints E f, f q ∈ Icc a b → q = p)
    (x : {y : M // f y = b})
    (hexcluded : ¬Tendsto (fun t => S.flow t x.val) atTop (𝓝 p)) :
    x.val ∈ FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct x.val
  have hregular := hb x.val x.property
  have hbelow : f r < a := by
    by_contra h
    have hrb : f r < b := by simpa only [x.property] using (hheights hregular).1
    have heq := hwindow r hr ⟨le_of_not_gt h, hrb.le⟩
    exact hexcluded (heq ▸ hforward)
  have habove : a < f q := by
    have hbq : b < f q := by simpa only [x.property] using (hheights hregular).2
    exact hab.trans hbq
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward habove hbelow

theorem AdaptedSurgeryWindows.reaches_old_lower_of_belt_avoidance
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (D : (S.data p).UpperLevel → (S.data p).UpperLevel)
    (hforward : ∀ x : (S.data p).UpperLevel, ∀ q : M,
      Tendsto (fun t => T.flow t x.val) atTop (𝓝 q) ↔
        Tendsto (fun t => S.flow t (D x).val) atTop (𝓝 q))
    (x : (S.data p).UpperLevel) (hx : D x ∉ range (S.data p).surgery.beltSphere) :
    x.val ∈ FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
  apply T.reaches_lower_of_excluded_critical_limit hf
    ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
    (S.data p).upper_regular p.val (S.isolated p) x
  intro h
  exact hx ((S.belt_basin_iff hf p (D x)).mp ((hforward x p.val).mp h))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
