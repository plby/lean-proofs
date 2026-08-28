import Wikipedia.HopfProblem.DegreeCollapseEmbeddedCircleThroughArc
import Wikipedia.HopfProblem.DegreeCollapseBeltArcClosingPath
import Wikipedia.HopfProblem.DegreeCollapseBeltArcTransversality

/-!
# An embedded circle with exactly one original belt intersection

When both branches of an index-one critical point reach the same minimum,
the constructed local transverse arc closes through that minimum's basin.
The resulting circle is smooth and immersed in the actual upper-level atlas.
Its only belt intersection is the prescribed point, and it retains the
entire local arc parametrization near the crossing.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap TopologicalSpace
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_single_belt_intersection_circle
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {d : ℕ} (hlow : ∀ a : criticalPoints E f, f a ≤ S.toSurgeryWindows.upper q →
      nativeMorseIndex E f a ≤ d) (hcut : 1 + d < Module.finrank ℝ E)
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
      (∀ s ∈ Icc (-r) r, γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) =
        nativeBeltLevelArc S q u v s) ∧
      ∀ z w, γ z = (S.data q).surgery.beltSphere w ↔
        z = Circle.exp (2 * Real.pi / (2 * r + 1) * r) ∧ v = w := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  obtain ⟨r, hr, hr1, hbasin, hpath⟩ :=
    S.exists_belt_arc_closing_path hf p q hp hq u v hbranches hlow hcut
  let α := nativeBeltLevelArc S q u v
  let U : Opens (S.data q).UpperLevel :=
    ⟨{z | Tendsto (fun t => S.flow t z.val) atTop (𝓝 p.val)},
      (S.isOpen_minimum_forward_basin hf p hp).preimage continuous_subtype_val⟩
  have hpr : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1.le
  have hmr : |-r| ≤ 1 := by rw [abs_neg]; exact hpr
  have hplus : α r ∈ U := by
    change Tendsto (fun t => S.flow t (α r).val) atTop (𝓝 p.val)
    rw [nativeBeltLevelArc_coe S q u v hpr]
    exact hbasin r (by simpa only [abs_of_pos hr] using hr) (by rw [abs_of_pos hr])
  have hminus : α (-r) ∈ U := by
    change Tendsto (fun t => S.flow t (α (-r)).val) atTop (𝓝 p.val)
    rw [nativeBeltLevelArc_coe S q u v hmr]
    exact hbasin (-r) (by simpa only [abs_neg, abs_of_pos hr] using hr)
      (by rw [abs_neg, abs_of_pos hr])
  let η : Path (⟨α r, hplus⟩ : U) (⟨α (-r), hminus⟩ : U) := {
    toFun := fun t => ⟨⟨hpath.somePath t, (hpath.somePath_mem t).1⟩,
      (hpath.somePath_mem t).2.1⟩
    continuous_toFun := (hpath.somePath.continuous.subtype_mk _).subtype_mk _
    source' := Subtype.ext (Subtype.ext (hpath.somePath.source.trans
      (nativeBeltLevelArc_coe S q u v hpr).symm))
    target' := Subtype.ext (Subtype.ext (hpath.somePath.target.trans
      (nativeBeltLevelArc_coe S q u v hmr).symm)) }
  have hαi : InjOn α (Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    apply nativeBeltArc_injOn S q u v hx hy
    have hh := congrArg Subtype.val hxy
    rw [nativeBeltLevelArc_coe S q u v (abs_le.mpr hx),
      nativeBeltLevelArc_coe S q u v (abs_le.mpr hy)] at hh
    exact hh
  have hdimL : 3 ≤ Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    omega
  obtain ⟨γ, hγ, hγi, hγd, hshort, himage⟩ := exists_embedded_circle_through_arc U hr hr1
    (nativeBeltLevelArc_contMDiffOn S hf q u v) hαi
    (fun _ hs => nativeBeltLevelArc_derivative_injective S hf q u v hs)
    hplus hminus η hdimL
  let z₀ := Circle.exp (2 * Real.pi / (2 * r + 1) * r)
  have hzero : γ z₀ = (S.data q).surgery.beltSphere v := by
    have hh := hshort 0 ⟨by linarith, hr.le⟩
    rw [zero_add] at hh
    apply Subtype.ext
    exact (congrArg Subtype.val hh).trans
      ((nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans
        (nativeBeltArc_zero S q u v))
  have hpq : p ≠ q := by
    intro heq
    have hh := hp
    rw [heq, hq] at hh
    exact Nat.one_ne_zero hh
  refine ⟨r, hr, hr1, γ, hγ, hγi, hγd, hshort, ?_⟩
  intro z w
  constructor
  · intro hzw
    rcases himage (mem_range_self z) with hshortz | hUz
    · obtain ⟨s, hs, hsz⟩ := hshortz
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsw : nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val := by
        rw [← nativeBeltLevelArc_coe S q u v hs1]
        exact congrArg Subtype.val (hsz.trans hzw)
      obtain ⟨-, hvw⟩ := (nativeBeltArc_belt_eq_iff S q u v w hs1).mp hsw
      refine ⟨hγi ?_, hvw⟩
      exact hzw.trans ((congrArg (S.data q).surgery.beltSphere hvw).symm.trans hzero.symm)
    · have hqz := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩
      change Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 p.val) at hUz
      rw [hzw] at hUz
      exact False.elim (hpq (Subtype.ext (tendsto_nhds_unique hUz hqz)))
  · rintro ⟨rfl, rfl⟩
    exact hzero

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
