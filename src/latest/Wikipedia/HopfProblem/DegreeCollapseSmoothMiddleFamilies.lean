import Wikipedia.HopfProblem.DegreeCollapseMiddleSphereSmoothing

/-!
# Constructed smooth middle sphere families with the exact native core germs

Both finite families are smoothed relatively to the same fixed pole cap.
The literal pointwise intersection table is unchanged. Each sphere retains
its actual continuous capped class and its original inverse-Morse-chart germ.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

abbrev MiddleLabel := {p : criticalPoints E D.function // nativeMorseIndex E D.function p = 3}

instance middleLabel_finite : Finite D.MiddleLabel := by
  let _ : Finite (criticalPoints E D.function) := D.windows.toSurgeryWindows.finite.to_subtype
  infer_instance

structure SmoothMiddleFamilies where
  descending : D.MiddleLabel → C(Hemisphere.Sphere 3, M)
  ascending : D.MiddleLabel → C(Hemisphere.Sphere 3, M)
  descending_smooth : ∀ p, ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ (descending p)
  ascending_smooth : ∀ p, ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ (ascending p)
  descending_relative : ∀ p, (D.descendingSphere p.val p.property).HomotopicRel
    (descending p) fixedPoleCap
  ascending_relative : ∀ p, (D.ascendingSphere p.val p.property).HomotopicRel
    (ascending p) fixedPoleCap
  pair_iff : ∀ p q x y, descending p x = ascending q y ↔
    x = middlePole ∧ y = middlePole ∧ p = q

theorem nonempty_smoothMiddleFamilies : Nonempty D.SmoothMiddleFamilies := by
  obtain ⟨f, g, hf, hg, hrelf, hrelg, heq⟩ := exists_smooth_opposite_families
    (fun p : D.MiddleLabel => D.descendingSphere p.val p.property)
    (fun p : D.MiddleLabel => D.ascendingSphere p.val p.property)
    (fun p => D.descendingSphere_smooth_negative p.val p.property)
    (fun p => D.ascendingSphere_smooth_negative p.val p.property)
    (fun p q x y h => by
      obtain ⟨hx, hy, -⟩ := (D.closed_middle_pair_iff p.val q.val p.property q.property x y).mp h
      exact ⟨hx, hy⟩)
  refine ⟨⟨f, g, hf, hg, hrelf, hrelg, ?_⟩⟩
  intro p q x y
  constructor
  · intro h
    obtain ⟨hx, hy, hpq⟩ :=
      (D.closed_middle_pair_iff p.val q.val p.property q.property x y).mp
        ((heq p q x y).mp h)
    exact ⟨hx, hy, Subtype.ext hpq⟩
  · rintro ⟨hx, hy, hpq⟩
    apply (heq p q x y).mpr
    exact (D.closed_middle_pair_iff p.val q.val p.property q.property x y).mpr
      ⟨hx, hy, congrArg Subtype.val hpq⟩

namespace SmoothMiddleFamilies

variable {D} (F : D.SmoothMiddleFamilies)

theorem descending_pole (p : D.MiddleLabel) : F.descending p middlePole = p.val.val :=
  ((F.descending_relative p).fst_eq_snd
    (innerPoleCap_subset_fixed middlePole_mem_inner)).symm.trans
      (D.descendingSphere_pole p.val p.property)

theorem ascending_pole (p : D.MiddleLabel) : F.ascending p middlePole = p.val.val :=
  ((F.ascending_relative p).fst_eq_snd
    (innerPoleCap_subset_fixed middlePole_mem_inner)).symm.trans
      (D.ascendingSphere_pole p.val p.property)

theorem descending_core_germ (p : D.MiddleLabel) :
    F.descending p =ᶠ[𝓝 middlePole] (fun x =>
      CoreDisks.negativeFun (D.windows.data p.val)
        (D.negativeLinear p.val p.property (Hemisphere.tail x))) := by
  filter_upwards [fixedPoleCap_mem_nhds] with x hx
  exact ((F.descending_relative p).fst_eq_snd hx).symm.trans
    (D.descendingSphere_negative_formula p.val p.property x (fixedPoleCap_subset_negative hx))

theorem ascending_core_germ (p : D.MiddleLabel) :
    F.ascending p =ᶠ[𝓝 middlePole] (fun x =>
      CoreDisks.positiveFun (D.windows.data p.val)
        (D.positiveLinear p.val p.property (Hemisphere.tail x))) := by
  filter_upwards [fixedPoleCap_mem_nhds] with x hx
  exact ((F.ascending_relative p).fst_eq_snd hx).symm.trans
    (D.ascendingSphere_negative_formula p.val p.property x (fixedPoleCap_subset_negative hx))

end SmoothMiddleFamilies

open SingularMayerVietoris in
theorem exists_smooth_middle_families [SimplyConnectedSpace M]
    [Subsingleton (SingularHomology M 2)] (hdim : Module.finrank ℝ E = 6) :
    ∃ D : SeparatedSystem E M, Nonempty D.SmoothMiddleFamilies := by
  obtain ⟨D⟩ := nonempty_separatedSystem E M hdim
  exact ⟨D, D.nonempty_smoothMiddleFamilies⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
