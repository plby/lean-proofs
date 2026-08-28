import Wikipedia.HopfProblem.DegreeCollapseBeltBranchesAcrossCut
import Wikipedia.HopfProblem.DegreeCollapsePositiveBeltPointCrossing
import Wikipedia.HopfProblem.DegreeCollapseBeltCircleReachingLevel

/-!
# A transverse belt circle between the original two cuts

Close the prescribed short belt arc inside the lower-boundary crossing
basin, retaining the higher-level crossing condition. This open set is
disjoint from the whole belt, since every belt point has the original
positive critical point as its forward limit. The constructed embedded
circle therefore has exactly the original single transverse belt crossing.
Every other part of the circle crosses the original lower boundary.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_single_belt_circle_crossing_lower_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) {c : ℝ} (hcq : c < f q)
    (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (O : Opens M) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hshortO : ∀ s ∈ Icc (-r) r, nativeBeltArc S q u v s ∈ O)
    (hpath : JoinedIn {z : M | f z = S.toSurgeryWindows.upper q ∧
      z ∈ FlowCancellation.levelBasin S.flow f c ∧ z ∈ O}
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
        (γ z).val ∈ FlowCancellation.levelBasin S.flow f c := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let α := nativeBeltLevelArc S q u v
  have hB : IsOpen (FlowCancellation.levelBasin S.flow f c) :=
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (hc z hz))).1
  let U : Opens (S.data q).UpperLevel :=
    ⟨{z | z.val ∈ FlowCancellation.levelBasin S.flow f c ∧ z.val ∈ O},
      (hB.inter O.isOpen).preimage continuous_subtype_val⟩
  have hpr : |r| ≤ 1 := by rw [abs_of_pos hr]; exact hr1.le
  have hmr : |-r| ≤ 1 := by rw [abs_neg]; exact hpr
  have hplus : α r ∈ U := by
    change (α r).val ∈ FlowCancellation.levelBasin S.flow f c ∧ (α r).val ∈ O
    rw [nativeBeltLevelArc_coe S q u v hpr]
    exact hpath.source_mem.2
  have hminus : α (-r) ∈ U := by
    change (α (-r)).val ∈ FlowCancellation.levelBasin S.flow f c ∧ (α (-r)).val ∈ O
    rw [nativeBeltLevelArc_coe S q u v hmr]
    exact hpath.target_mem.2
  let η : Path (⟨α r, hplus⟩ : U) (⟨α (-r), hminus⟩ : U) := {
    toFun t := ⟨⟨hpath.somePath t, (hpath.somePath_mem t).1⟩, (hpath.somePath_mem t).2⟩
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
      (γ z).val ∈ FlowCancellation.levelBasin S.flow f c := by
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
  · intro z w
    constructor
    · intro hzw
      rcases himage' z with hshortz | hcross
      · obtain ⟨s, hs, hsz⟩ := hshortz
        have hs1 : |s| ≤ 1 := (abs_le.mpr hs).trans hr1.le
        have hsw : nativeBeltArc S q u v s = ((S.data q).surgery.beltSphere w).val := by
          rw [← nativeBeltLevelArc_coe S q u v hs1]
          exact congrArg Subtype.val (hsz.trans hzw)
        obtain ⟨_, hvw⟩ := (nativeBeltArc_belt_eq_iff S q u v w hs1).mp hsw
        refine ⟨hγi ?_, hvw⟩
        exact hzw.trans ((congrArg (S.data q).surgery.beltSphere hvw).symm.trans hzero.symm)
      · have hbad : ((S.data q).surgery.beltSphere w).val ∈
            (FlowCancellation.levelBasin S.flow f c)ᶜ := by
          rw [levelBasin_compl_eq_endpoint_obstruction S hf hc]
          exact Or.inl ⟨q, hcq.le,
            (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩⟩
        rw [hzw] at hcross
        exact (hbad hcross).elim
    · rintro ⟨rfl, rfl⟩
      exact hzero

theorem AdaptedSurgeryWindows.exists_transverse_belt_circle_between_cuts
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    {c a : ℝ} (hcq : c < f q) (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    [PathConnectedSpace {y : M // f y = c}]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      ((S.data q).surgery.attachingSphere w).val ∈ FlowCancellation.levelBasin S.flow f c)
    (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {d : ℕ} (hlow : ∀ z : criticalPoints E f, c < f z → f z ≤ a → nativeMorseIndex E f z ≤ d)
    (hdn : d < n) (hcut : 1 + d < Module.finrank ℝ E) (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ∃ γ : C(Circle, (S.data q).UpperLevel),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
        (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
        (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f a) ∧
        ∃ z₀ : Circle,
          (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
          (Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z₀ :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
              (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v))) ∧
          ∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f c ∨
            Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  have hqa : f q < a := (S.toSurgeryWindows.value_lt_upper q).trans_le hba
  obtain ⟨v, hv⟩ := S.exists_belt_point_reaching_level_above_cut hf q n hcq hqa hlow hdn
  obtain ⟨r, hr, hr1, hreach, hlower, hpath⟩ :=
    S.exists_belt_arc_closing_path_between_cuts hf q hcq hc u v hbranches hba ha hv hlow hcut
  let O : Opens M := ⟨FlowCancellation.levelBasin S.flow f a,
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (ha z hz))).1⟩
  obtain ⟨γ, hγ, hγi, hγd, hγreach, hshort, hsingle, himage⟩ :=
    S.exists_single_belt_circle_crossing_lower_cut hf q hcq hc u v O hr hr1
      (fun s hs => hreach s (abs_le.mpr hs)) hpath hdim
  let ψ : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / (2 * r + 1) * (t + r))
  have hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ :=
    contMDiff_circleExp.comp (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff
  have heq : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] nativeBeltLevelArc S q u v := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
    exact hshort t ⟨ht.1.le, ht.2.le⟩
  have hendpoints (z : Circle) : (γ z).val ∈ FlowCancellation.levelBasin S.flow f c ∨
      Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 q.val) := by
    rcases himage z with hshortz | hzlower
    · obtain ⟨s, hs, hsz⟩ := hshortz
      have hsr : |s| ≤ r := abs_le.mpr hs
      have hs1 : |s| ≤ 1 := hsr.trans hr1.le
      by_cases hs0 : s = 0
      · right
        have hz : (γ z).val = ((S.data q).surgery.beltSphere v).val := by
          rw [← hsz, nativeBeltLevelArc_coe S q u v hs1, hs0, nativeBeltArc_zero]
        rw [hz]
        exact (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
      · left
        rw [← hsz, nativeBeltLevelArc_coe S q u v hs1]
        exact hlower s (abs_pos.mpr hs0) hsr
    · exact Or.inl hzlower
  refine ⟨v, γ, hγ, hγi, hγd, hγreach,
    Circle.exp (2 * Real.pi / (2 * r + 1) * r), hsingle, ?_, hendpoints⟩
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v
  have hαtrans : Surjective ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E)
      (nativeBeltLevelArc S q u v) 0 : ℝ →L[ℝ] RegularLevel.Model E).coprod B) :=
    nativeBeltLevelArc_transverse S hf q hq n u v
  have ht : Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ (ψ 0) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod B) :=
    transverse_circle_of_arc_germ (D := EuclideanSpace ℝ (Fin n))
      (J := 𝓘(ℝ, RegularLevel.Model E)) (α := nativeBeltLevelArc S q u v)
      (γ := γ) (ψ := ψ) hγ hψ heq B hαtrans
  have hp0 : ψ 0 = Circle.exp (2 * Real.pi / (2 * r + 1) * r) := by
    dsimp [ψ]
    rw [zero_add]
  rw [hp0] at ht
  exact ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
