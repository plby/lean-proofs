import Wikipedia.HopfProblem.DegreeCollapseSmoothSignedTime
import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMaps

/-!
# The actual level basin is a native smooth flow cylinder

The original flow gives the forward map from the actual regular level
times real time. The proved smooth signed hitting time constructs its
inverse. Both directions use the original native manifold structures.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Construct the full native flow cylinder over a nonempty strictly crossed regular level. -/
theorem exists_native_level_flow_cylinder {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (z : {x : M // f x = c}) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ Φ : PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({x : M // f x = c} × ℝ) M ∞,
      Φ.source = univ ∧ Φ.target = levelBasin F f c ∧
      (∀ p, Φ p = F p.2 p.1) ∧
      ∀ x ∈ Φ.target, (Φ.symm x).2 = -signedLevelTime F f c x := by
  classical
  let _ := RegularLevel.chartedSpace hf hreg
  let L := {x : M // f x = c}
  let B := levelBasin F f c
  let θ := signedLevelTime F f c
  obtain ⟨hB, hθ, htranslate⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  let r : M → L := fun x => if hx : x ∈ B then
    ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ else z
  let φ : L × ℝ → M := fun p => F p.2 p.1
  let ψ : M → L × ℝ := fun x => (r x, -θ x)
  have hflow := SmoothODE.contMDiff_native_flow hV F hcurve
  have hφ : ContMDiff (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ φ :=
    hflow.comp (((RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst).prodMk
      contMDiff_snd)
  have hψ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) ∞ ψ B := by
    intro x hx
    have hθx := (hθ x hx).contMDiffAt (hB.mem_nhds hx)
    have hr : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, RegularLevel.Model E) ∞ r x := by
      apply (RegularLevel.contMDiffAt_iff_inclusion hf hreg 𝓘(ℝ, E) r x).mpr
      apply (hflow.contMDiffAt.comp x (contMDiffAt_id.prodMk hθx)).congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hx] with y hy
      change (r y : M) = F (θ y) y
      have hyB : y ∈ B := hy
      simp only [r, dif_pos hyB]
    exact (hr.prodMk hθx.neg).contMDiffWithinAt
  have hD : Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) :=
    (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) := FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hlevel (x : L) : (x : M) ∈ B := ⟨0, by simpa only [F.map_zero_apply] using x.property⟩
  have hφB (p : L × ℝ) : φ p ∈ B := (levelBasin_flow_iff F f c p.2 p.1).mpr (hlevel p.1)
  have hclock (p : L × ℝ) : θ (φ p) = -p.2 := by
    have hh := htranslate p.1 (hlevel p.1) p.2
    rw [signedLevelTime_eq_zero F hf.continuous hD hder hboundary p.1.property, zero_sub] at hh
    exact hh
  have hleft (p : L × ℝ) : ψ (φ p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change (r (φ p) : M) = p.1
      rw [show r (φ p) = ⟨F (θ (φ p)) (φ p), signedLevelTime_hits F f c (hφB p)⟩ by
        simp only [r, dif_pos (hφB p)]]
      change F (θ (φ p)) (F p.2 p.1) = p.1
      rw [hclock, ← F.map_add, neg_add_cancel, F.map_zero_apply]
    · change -θ (φ p) = p.2
      rw [hclock, neg_neg]
  have hright (x : M) (hx : x ∈ B) : φ (ψ x) = x := by
    change F (-θ x) (r x) = x
    rw [show r x = ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ by simp only [r, dif_pos hx]]
    change F (-θ x) (F (θ x) x) = x
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  let Φ : PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (L × ℝ) M ∞ := {
    toFun := φ
    invFun := ψ
    source := univ
    target := B
    map_source' := fun p _ => hφB p
    map_target' := fun _ _ => mem_univ _
    left_inv' := fun p _ => hleft p
    right_inv' := hright
    open_source := isOpen_univ
    open_target := hB
    contMDiffOn_toFun := hφ.contMDiffOn
    contMDiffOn_invFun := hψ }
  exact ⟨Φ, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
