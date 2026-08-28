import Wikipedia.HopfProblem.DegreeCollapseBeltCircleInOpen

/-!
# A transverse belt circle whose entire image reaches the higher level

All geometric inputs are constructed from the given Morse system: a belt
point outside the low-backward obstruction, a short arc in the open crossing
basin, a return path that retains that condition, and a native embedded
circle with the original unique transverse belt intersection.
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
theorem AdaptedSurgeryWindows.exists_transverse_belt_circle_reaching_level_with_endpoints
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {d : ℕ} (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ d)
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
          ∀ z, Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 p.val) ∨
            Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  have hqa : f q < a := (S.toSurgeryWindows.value_lt_upper q).trans_le hba
  obtain ⟨v, hv⟩ := S.exists_belt_point_reaching_level hf q n hqa hlow hdn
  obtain ⟨r, hr, hr1, hreach, hmin, hpath⟩ :=
    S.exists_belt_arc_closing_path_reaching_level hf p q hp u v hbranches hba ha hv hlow hcut
  let O : Opens M := ⟨FlowCancellation.levelBasin S.flow f a,
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (ha z hz))).1⟩
  have hpq : p ≠ q := by
    intro heq
    have hh := hp
    rw [heq, hq] at hh
    exact Nat.one_ne_zero hh
  obtain ⟨γ, hγ, hγi, hγd, hγreach, hshort, hsingle, himage⟩ :=
    S.exists_single_belt_circle_in_open_with_image hf p q hp hpq u v O hr hr1
      (fun s hs => hreach s (abs_le.mpr hs)) hpath hdim
  let ψ : ℝ → Circle := fun t => Circle.exp (2 * Real.pi / (2 * r + 1) * (t + r))
  have hψ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ ψ :=
    contMDiff_circleExp.comp (contDiff_const.mul (contDiff_id.add contDiff_const)).contMDiff
  have heq : γ ∘ ψ =ᶠ[𝓝 (0 : ℝ)] nativeBeltLevelArc S q u v := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
    exact hshort t ⟨ht.1.le, ht.2.le⟩
  have hendpoints (z : Circle) : Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 p.val) ∨
      Tendsto (fun t => S.flow t (γ z).val) atTop (𝓝 q.val) := by
    rcases himage z with hshortz | hzmin
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
        exact hmin s (abs_pos.mpr hs0) hsr
    · exact Or.inl hzmin
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

open Classical in
theorem AdaptedSurgeryWindows.exists_transverse_belt_circle_reaching_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {d : ℕ} (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ d)
    (hdn : d < n) (hcut : 1 + d < Module.finrank ℝ E) (hdim : 4 ≤ Module.finrank ℝ E) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∃ v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ∃ γ : C(Circle, (S.data q).UpperLevel),
        ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧ Injective γ ∧
        (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z)) ∧
        (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f a) ∧
        ∃ z₀ : Circle,
          (∀ z w, γ z = (S.data q).surgery.beltSphere w ↔ z = z₀ ∧ v = w) ∧
          Surjective ((mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) γ z₀ :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] RegularLevel.Model E).coprod
              (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) (S.data q).surgery.beltSphere v)) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  obtain ⟨v, γ, hγ, hi, hd, hreach, z₀, hsingle, htrans, -⟩ :=
    S.exists_transverse_belt_circle_reaching_level_with_endpoints hf p q hp hq n u hbranches
      hba ha hlow hdn hcut hdim
  exact ⟨v, γ, hγ, hi, hd, hreach, z₀, hsingle, htrans⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
