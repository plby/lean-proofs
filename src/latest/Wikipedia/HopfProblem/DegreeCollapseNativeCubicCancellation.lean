import Wikipedia.HopfProblem.DegreeCollapseLocalFunctionReplacement
import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationSupport

/-!
# Exact removal of a cubic critical pair on the original manifold

A genuine partial smooth chart and its compactly supported cubic model
give an actual smooth replacement function. The native critical set loses
exactly the two specified points and every exterior germ is unchanged.
Existence of a cubic chart for a selected pair of handles remains a separate
geometric obligation; it is not assumed from homotopy equivalence alone.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.NativeCubicCancellation

open LocalFunctionReplacement MorseCancellation

variable {E B H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- Model data remove exactly the two corresponding native critical points. -/
theorem remove_chart_pair (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E} {p q : E}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hb₀ : ContDiff ℝ ∞ b₀) (hb₁ : ContDiff ℝ ∞ b₁)
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x)
    (hp : p ∈ Φ.source) (hq : q ∈ Φ.source)
    (hcrit : ∀ x, fderiv ℝ b₀ x = 0 ↔ x = p ∨ x = q)
    (hreg : ∀ x, fderiv ℝ b₁ x ≠ 0) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ y, mfderiv I 𝓘(ℝ, ℝ) g y = 0 ↔
        mfderiv I 𝓘(ℝ, ℝ) f y = 0 ∧ y ≠ Φ p ∧ y ≠ Φ q) ∧
      (∀ y, y ∉ Φ '' K → g =ᶠ[𝓝 y] f) := by
  let g := replace Φ f b₁
  refine ⟨g, contMDiff_replace Φ hf hb₁ hK hKΦ hmodel hfix, ?_, ?_⟩
  · intro y
    rw [critical_points_after_replacement Φ hb₁ hK hKΦ hmodel hfix (fun x _ => hreg x)]
    constructor
    · rintro ⟨hycrit, hy⟩
      refine ⟨hycrit, ?_, ?_⟩
      · intro he
        exact hy (he ▸ Φ.map_source' hp)
      · intro he
        exact hy (he ▸ Φ.map_source' hq)
    · rintro ⟨hycrit, hyp, hyq⟩
      refine ⟨hycrit, ?_⟩
      intro hy
      have heq := replace_critical_iff Φ f hb₀ hy
      rw [replace_self Φ hmodel] at heq
      have hc := (hcrit _).mp (heq.mp hycrit)
      rcases hc with h | h
      · exact hyp ((Φ.right_inv' hy).symm.trans (congrArg Φ h))
      · exact hyq ((Φ.right_inv' hy).symm.trans (congrArg Φ h))
  · intro y hy
    exact replace_germ_off_support Φ hK hKΦ hmodel hfix hy

variable {m : ℕ} (σ : Fin m → ℝ)

/-- A nonzero critical point of a localized cubic must lie in its actual support. -/
theorem critical_mem_support (hσ : ∀ i, σ i ≠ 0) {φ : Model m → ℝ}
    {t : ℝ} {p : Model m} (hp : p ≠ 0)
    (hcrit : fderiv ℝ (localized σ φ t) p = 0) : p ∈ tsupport φ := by
  by_contra h
  rw [(localized_germ_outside σ φ t h).fderiv_eq] at hcrit
  exact hp ((cubic_zero_unique_critical σ hσ p).mp hcrit)

/-- The actual supported family supplies both models; only its placement in
the manifold is a premise of the resulting replacement. -/
theorem exists_native_cubic_cancellation
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) I (Model m) M ∞)
    (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφΦ : tsupport φ ⊆ Φ.source)
    {U : Set (Model m)} (hU : IsOpen U) (h0 : (0 : Model m) ∈ U)
    (hφU : EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ, 0 < a ∧ (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
      ∀ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f →
        (∀ x ∈ Φ.source, f (Φ x) = localized σ φ (-(a ^ 2)) x) →
        ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
          (∀ y, mfderiv I 𝓘(ℝ, ℝ) g y = 0 ↔
            mfderiv I 𝓘(ℝ, ℝ) f y = 0 ∧ y ≠ Φ (a, 0) ∧ y ≠ Φ (-a, 0)) ∧
          (∀ y, y ∉ Φ '' tsupport φ → g =ᶠ[𝓝 y] f) := by
  obtain ⟨a, ha, hcrit, hreg, _, hfix⟩ :=
    exists_supported_cancellation σ hσ hφ hc hU h0 hφU
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    apply hφΦ
    apply critical_mem_support σ hσ
    · intro he
      exact ha.ne' (congrArg Prod.fst he)
    · exact (hcrit _).mpr (Or.inl rfl)
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    apply hφΦ
    apply critical_mem_support σ hσ
    · intro he
      have he' := congrArg Prod.fst he
      exact ha.ne' (neg_eq_zero.mp he')
    · exact (hcrit _).mpr (Or.inr rfl)
  refine ⟨a, ha, hp, hq, ?_⟩
  intro f hf hmodel
  have hs (t : ℝ) : ContDiff ℝ ∞ (localized σ φ t) :=
    (contDiff_localized_family σ hφ).comp (contDiff_const.prodMk contDiff_id)
  exact remove_chart_pair Φ hf (hs _) (hs _) hc hφΦ hmodel
    (fun x hx => (hfix _ x hx).trans (hfix _ x hx).symm) hp hq hcrit hreg

/-- The cutoff and its full unit plateau are constructed inside any prescribed open neighborhood. -/
theorem exists_cutoff {V : Set (Model m)} (hV : IsOpen V) (h0 : (0 : Model m) ∈ V) :
    ∃ φ : Model m → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ V ∧
      ∃ U : Set (Model m), IsOpen U ∧ (0 : Model m) ∈ U ∧ EqOn φ (fun _ => 1) U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let φ : ContDiffBump (0 : Model m) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, Metric.ball 0 (r / 4),
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  · rw [φ.tsupport_eq]
    intro p hp
    apply hball
    exact lt_of_le_of_lt hp (by change r / 2 < r; linarith)
  · intro p hp
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hp)

/-- Apart from an actual cubic coordinate expression for `f`, all the local
cancellation data are constructed from the chart and the transverse signs. -/
theorem exists_cancellation_at_chart_origin
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) I (Model m) M ∞)
    (hσ : ∀ i, σ i ≠ 0) (h0 : (0 : Model m) ∈ Φ.source) :
    ∃ (φ : Model m → ℝ) (a : ℝ), 0 < a ∧
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Φ.source ∧
      (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
      ∀ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f →
        (∀ x ∈ Φ.source, f (Φ x) = localized σ φ (-(a ^ 2)) x) →
        ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
          (∀ y, mfderiv I 𝓘(ℝ, ℝ) g y = 0 ↔
            mfderiv I 𝓘(ℝ, ℝ) f y = 0 ∧ y ≠ Φ (a, 0) ∧ y ≠ Φ (-a, 0)) ∧
          (∀ y, y ∉ Φ '' tsupport φ → g =ᶠ[𝓝 y] f) := by
  obtain ⟨φ, hφ, hc, hs, U, hU, hU0, hφU⟩ := exists_cutoff Φ.open_source h0
  obtain ⟨a, ha, hp, hq, hreplace⟩ :=
    exists_native_cubic_cancellation σ Φ hσ hφ hc hs hU hU0 hφU
  exact ⟨φ, a, ha, hφ, hc, hs, hp, hq, hreplace⟩

end Wikipedia.HopfProblem.DegreeCollapse.NativeCubicCancellation
