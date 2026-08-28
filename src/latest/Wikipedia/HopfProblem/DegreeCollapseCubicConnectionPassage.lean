import Wikipedia.HopfProblem.DegreeCollapseNativeCubicPassage
import Wikipedia.HopfProblem.DegreeCollapseNativeCubicOrbit
import Wikipedia.HopfProblem.DegreeCollapseNativeNoReturn
import Wikipedia.HopfProblem.DegreeCollapseNativeBandCrossing

/-!
# Finite passage from a native cubic field chart and a unique connection

The model chart constructs the entire connecting orbit. A compact outer
region is chosen inside both the original chart and the open critical
band. Endpoint convergence and uniqueness construct the inner no-return
neighborhood. The resulting supported field modification removes the two
zeros and has a uniform finite residence bound for the whole closed band.
-/

noncomputable section

open Set Function Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Construct compact supported zero cancellation and finite passage from the unique connection. -/
theorem exists_cubic_connection_finite_passage {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ ManifoldMorse.criticalPoints E f)
    (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair : ∀ x ∈ ManifoldMorse.criticalPoints E f,
      f x ∈ Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique : ∀ x ∉ ManifoldMorse.criticalPoints E f,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 (Φ (-a, 0))) →
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 (Φ (a, 0))) →
        ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧ K ⊆ Φ.target ∩ f ⁻¹' Ioo c d ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
      (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
      (∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' →
        ∃ t ∈ Icc (0 : ℝ) T, f (γ t) ∉ Icc c d) ∧
      ∃ G : Flow ℝ M, (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
        (∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (G T x) < c) ∧
          ∀ x, c ≤ f x → d < f (G (-T) x)) ∧
        ContinuousOn (FlowConstruction.entryTime G {x | f x ≤ c}) {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  obtain ⟨hrange, htop, hbot⟩ := native_cubic_axis_orbit σ ha Φ haxis hV₁ hmodel F hcurve
  have hclosed := native_cubic_closed_axis σ ha Φ haxis hV₁ hmodel F hcurve
  have hmono := FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc (Φ (0, 0))
  have hztop := hf.continuous.continuousAt.tendsto.comp htop
  have hzbot := hf.continuous.continuousAt.tendsto.comp hbot
  have hzband (t : ℝ) : f (F t (Φ (0, 0))) ∈ Icc (f (Φ (a, 0))) (f (Φ (-a, 0))) :=
    ⟨hmono.le_of_tendsto hztop t, hmono.ge_of_tendsto hzbot t⟩
  let A := Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}
  have hAband : Φ '' A ⊆ f ⁻¹' Ioo c d := by
    intro x hx
    rw [hclosed] at hx
    rcases hx with hx | hx | ⟨t, ht⟩
    · rw [hx]
      exact ⟨hc, lt_trans hpq hd⟩
    · rw [hx]
      exact ⟨lt_trans hc hpq, hd⟩
    · rw [← ht]
      exact ⟨lt_of_lt_of_le hc (hzband t).1, lt_of_le_of_lt (hzband t).2 hd⟩
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' (f ⁻¹' Ioo c d)) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_Ioo.preimage hf.continuous)
  have hAsub : A ⊆ Φ.source ∩ Φ ⁻¹' (f ⁻¹' Ioo c d) :=
    fun x hx => ⟨haxis hx, hAband ⟨x, hx, rfl⟩⟩
  obtain ⟨C, hC, hAC, hCsub⟩ := exists_compact_between
    (show IsCompact A from isCompact_Icc.prod isCompact_singleton) hopen hAsub
  have hCΦ : C ⊆ Φ.source := fun x hx => (hCsub hx).1
  let U := Φ '' interior C
  have hU : IsOpen U := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    isOpen_interior (fun x hx => hCΦ (interior_subset hx))
  have hAU : Φ '' A ⊆ U := image_mono hAC
  have hpU : Φ (a, (0 : Fin m → ℝ)) ∈ U :=
    hAU ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩
  have hqU : Φ (-a, (0 : Fin m → ℝ)) ∈ U :=
    hAU ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
  have hzU (t : ℝ) : F t (Φ (0, 0)) ∈ U := by
    apply hAU
    rw [hclosed]
    exact Or.inr (Or.inr ⟨t, rfl⟩)
  obtain ⟨N, hN, hNU, hpN, hqN, hzN, hnoreturn⟩ :=
    FlowCancellation.exists_native_connection_no_return hf hV F hcurve hzero hdesc hinj
      hp hq hpq (fun x hx hh => hpair x hx ⟨le_trans hc.le hh.1, le_trans hh.2 hd.le⟩)
      hzband hunique hU hpU hqU hzU
  have haxisN (s : ℝ) (hs : s ∈ Icc (-a) a) : Φ (s, (0 : Fin m → ℝ)) ∈ N := by
    have hh : Φ (s, (0 : Fin m → ℝ)) ∈ Φ '' A := ⟨(s, 0), ⟨hs, rfl⟩, rfl⟩
    rw [hclosed] at hh
    rcases hh with hh | hh | ⟨t, ht⟩
    · exact hh ▸ hpN
    · exact hh ▸ hqN
    · exact ht ▸ hzN t
  have hneg (x : M) (hx : f x ∈ Icc c d) (hout : x ∉ N) :
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    apply hdesc x
    intro hcrit
    rcases hpair x hcrit hx with he | he
    · exact hout (he ▸ hpN)
    · exact hout (he ▸ hqN)
  obtain ⟨K, V', hK, hKN, hV', hzeros, hkeep, hpass⟩ :=
    exists_native_cubic_field_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve
      hN hNU haxisN hC hCΦ (image_mono interior_subset) hneg hnoreturn
  have hKsub : K ⊆ Φ.target ∩ f ⁻¹' Ioo c d := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hNU (hKN hx)
    exact ⟨Φ.map_source' (hCΦ (interior_subset hz)), (hCsub (interior_subset hz)).2⟩
  have hcd : c ≤ d := by linarith
  have hboundary (x : M) (hx : f x = c ∨ f x = d) :
      mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd⟩
        · exact ⟨hcd, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  refine ⟨K, V', hK, hKsub, hV', hzeros, hkeep, hpass, ?_⟩
  exact FlowCancellation.exists_native_flow_band_crossing hf hV'
    (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hpass

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
