import Wikipedia.HopfProblem.DegreeCollapseBeltArcReachingPath

/-!
# Closing the belt circle while retaining an additional open condition

The additional condition concerns points of the original ambient manifold.
Both the prescribed short arc and the return path satisfy it. Relative
circle construction inside its intersection with the minimum basin keeps
the entire resulting circle there, without changing its unique belt crossing.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap TopologicalSpace
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem single_belt_intersection_of_arc_and_minimum_range
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : p ≠ q)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    {X : Type*} {γ : X → (S.data q).UpperLevel} (hγi : Injective γ) {z₀ : X}
    (hzero : γ z₀ = (S.data q).surgery.beltSphere v) {r : ℝ} (hr1 : r ≤ 1)
    (himage : ∀ z, γ z ∈ nativeBeltLevelArc S q u v '' Icc (-r) r ∨
      Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 p.val)) :
    ∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w := by
  intro z w
  constructor
  · intro hzw
    rcases himage z with hshort | hmin
    · obtain ⟨s, hs, hsz⟩ := hshort
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hsw : nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val := by
        rw [← nativeBeltLevelArc_coe S q u v hs1]
        exact congrArg Subtype.val (hsz.trans hzw)
      obtain ⟨-, hvw⟩ := (nativeBeltArc_belt_eq_iff S q u v w hs1).mp hsw
      refine ⟨hγi ?_, hvw⟩
      exact hzw.trans ((congrArg (S.data q).surgery.beltSphere hvw).symm.trans hzero.symm)
    · have hqz := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩
      rw [hzw] at hmin
      exact False.elim (hpq (Subtype.ext (tendsto_nhds_unique hmin hqz)))
  · rintro ⟨rfl, rfl⟩
    exact hzero

open Classical in
theorem AdaptedSurgeryWindows.exists_single_belt_circle_in_open_with_image
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0) (hpq : p ≠ q)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (O : Opens M) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hshortO : ∀ s ∈ Icc (-r) r, nativeBeltArc S q u v s ∈ O)
    (hpath : JoinedIn {z : M | f z = S.toSurgeryWindows.upper q ∧
      Tendsto (fun t => S.flow t z) atTop (𝓝 p.val) ∧ z ∈ O}
      (nativeBeltArc S q u v r) (nativeBeltArc S q u v (-r)))
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
      (∀ z, (γ z).val ∈ O) ∧
      (∀ s ∈ Icc (-r) r, γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) =
        nativeBeltLevelArc S q u v s) ∧
      (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔
        z = Circle.exp (2 * Real.pi / (2 * r + 1) * r) ∧ v = w) ∧
      ∀ z, γ z ∈ nativeBeltLevelArc S q u v '' Icc (-r) r ∨
        Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let α := nativeBeltLevelArc S q u v
  let U : Opens (S.data q).UpperLevel :=
    ⟨{z | Tendsto (fun t => S.flow t z.val) atTop (𝓝 p.val) ∧ z.val ∈ O},
      ((S.isOpen_minimum_forward_basin hf p hp).inter O.isOpen).preimage continuous_subtype_val⟩
  have hpr : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1.le
  have hmr : |-r| ≤ 1 := by rw [abs_neg]; exact hpr
  have hplus : α r ∈ U := by
    change Tendsto (fun t => S.flow t (α r).val) atTop (𝓝 p.val) ∧ (α r).val ∈ O
    rw [nativeBeltLevelArc_coe S q u v hpr]
    exact hpath.source_mem.2
  have hminus : α (-r) ∈ U := by
    change Tendsto (fun t => S.flow t (α (-r)).val) atTop (𝓝 p.val) ∧ (α (-r)).val ∈ O
    rw [nativeBeltLevelArc_coe S q u v hmr]
    exact hpath.target_mem.2
  let η : Path (⟨α r, hplus⟩ : U) (⟨α (-r), hminus⟩ : U) := {
    toFun := fun t => ⟨⟨hpath.somePath t, (hpath.somePath_mem t).1⟩, (hpath.somePath_mem t).2⟩
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
    (fun _ hs => nativeBeltLevelArc_derivative_injective S hf q u v hs) hplus hminus η hdimL
  let z₀ := Circle.exp (2 * Real.pi / (2 * r + 1) * r)
  have hzero : γ z₀ = (S.data q).surgery.beltSphere v := by
    have hh := hshort 0 ⟨by linarith, hr.le⟩
    rw [zero_add] at hh
    apply Subtype.ext
    exact (congrArg Subtype.val hh).trans
      ((nativeBeltLevelArc_coe S q u v (s := 0) (by simp)).trans (nativeBeltArc_zero S q u v))
  have himage' (z : Circle) : γ z ∈ nativeBeltLevelArc S q u v '' Icc (-r) r ∨
      Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 p.val) := by
    rcases himage (mem_range_self z) with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1
  refine ⟨γ, hγ, hγi, hγd, ?_, hshort, ?_, himage'⟩
  · intro z
    rcases himage (mem_range_self z) with hz | hz
    · obtain ⟨s, hs, hsz⟩ := hz
      rw [← hsz, nativeBeltLevelArc_coe S q u v
        (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
      exact hshortO s hs
    · exact hz.2
  · apply single_belt_intersection_of_arc_and_minimum_range S hf p q hpq u v hγi hzero hr1.le
    exact himage'

open Classical in
theorem AdaptedSurgeryWindows.exists_single_belt_circle_in_open
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0) (hpq : p ≠ q)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (O : Opens M) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hshortO : ∀ s ∈ Icc (-r) r, nativeBeltArc S q u v s ∈ O)
    (hpath : JoinedIn {z : M | f z = S.toSurgeryWindows.upper q ∧
      Tendsto (fun t => S.flow t z) atTop (𝓝 p.val) ∧ z ∈ O}
      (nativeBeltArc S q u v r) (nativeBeltArc S q u v (-r)))
    (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ γ : C(Circle, (S.data q).UpperLevel),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
      (∀ z, (γ z).val ∈ O) ∧
      (∀ s ∈ Icc (-r) r, γ (Circle.exp (2 * Real.pi / (2 * r + 1) * (s + r))) =
        nativeBeltLevelArc S q u v s) ∧
      ∀ z w, γ z = (S.data q).surgery.beltSphere w ↔
        z = Circle.exp (2 * Real.pi / (2 * r + 1) * r) ∧ v = w := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  obtain ⟨γ, hγ, hi, hd, hO, hs, hb, -⟩ := S.exists_single_belt_circle_in_open_with_image
    hf p q hp hpq u v O hr hr1 hshortO hpath hdim
  exact ⟨γ, hγ, hi, hd, hO, hs, hb⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
