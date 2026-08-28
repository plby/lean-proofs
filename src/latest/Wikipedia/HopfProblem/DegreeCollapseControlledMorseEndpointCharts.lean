import Wikipedia.HopfProblem.DegreeCollapseAlignedMorseFieldCharts

/-!
# Domain-controlled aligned endpoint charts

Restrict the actual endpoint chart to a constructed open neighborhood on
which its rational coordinate denominator is positive and the transformed
Morse coordinate lies in the original Morse chart target. This gives the
exact forward coordinate equation, including all domain conditions needed
to recover the scalar axis from actual orbit points.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- The correct sign of the rational endpoint coordinate selects the
interior axis, once its actual denominator domain is retained. -/
theorem endpointFieldCoordinate_mem_open_axis {a : ℝ} (ha : 0 < a)
    {e : ℝ} (he : e ^ 2 = 1) {s : ℝ} (hs : s ∈ endpointFieldDomain a e)
    (hdir : 0 < -e * endpointFieldCoordinate a e s) : s ∈ Ioo (-a) a := by
  rcases sq_eq_one_iff.mp he with h | h
  · subst e
    have hd : 0 < a + s := by simpa [endpointFieldDomain] using hs
    have hy : (s - a) / (a + s) < 0 := by
      simpa [endpointFieldCoordinate] using hdir
    have hn : s - a < 0 := by simpa using (div_lt_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩
  · subst e
    have hd : 0 < a - s := by simpa [endpointFieldDomain] using hs
    have hy : 0 < (s + a) / (a - s) := by
      simpa [endpointFieldCoordinate, sub_eq_add_neg] using hdir
    have hn : 0 < s + a := by simpa using (lt_div_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

open ManifoldMorse

open Classical in
/-- The aligned chart is restricted to a constructed neighborhood with an
actual Morse-coordinate equation and the positive rational denominator. -/
theorem exists_controlled_morse_field_endpoint (c : SignedMorseChart (E := E) f x)
    {m : ℕ} (σ : Fin m → ℝ) {e : ℝ} (he : e ^ 2 = 1)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) = x ∧
      Φ.target ⊆ c.splitChart.source ∧
      (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
      ∀ p ∈ Φ.source, p.1 ∈ endpointFieldDomain (1 / 2) e ∧
        c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p) := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_original_field_endpoint_with_alignment c σ he L hL V heq
  let q : Model m := (e / 2, 0)
  have hq : q.1 ∈ endpointFieldDomain (1 / 2) e := by
    simpa only [q, mul_one_div] using
      endpointField_mem_domain (by norm_num : 0 < (1 / 2 : ℝ)) he
  have hd : ContinuousAt (endpointFieldCoordinate (1 / 2) e) q.1 :=
    ((contDiffOn_endpointFieldCoordinate (1 / 2) e).contDiffAt
      ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)).continuousAt
  have hprod : ContinuousAt (endpointFieldProduct (m := m) (1 / 2) e) q :=
    (hd.comp continuousAt_fst).prodMk continuousAt_snd
  have hzero : L (endpointFieldProduct (1 / 2) e q) = 0 := by
    have hq' : q = (e * (1 / 2), (0 : Fin m → ℝ)) := by
      apply Prod.ext
      · dsimp [q]
        ring
      · rfl
    rw [hq']
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  have hct : ContinuousAt (fun p : Model m => L (endpointFieldProduct (1 / 2) e p)) q :=
    L.continuous.continuousAt.comp hprod
  have htarget0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have htarget : ∀ᶠ p in 𝓝 q, L (endpointFieldProduct (1 / 2) e p) ∈ c.splitChart.target := by
    have hn : ∀ᶠ z in 𝓝 (L (endpointFieldProduct (1 / 2) e q)), z ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (hzero.symm ▸ htarget0)
    exact hct.eventually hn
  have hdomain : ∀ᶠ p in 𝓝 q, p.1 ∈ endpointFieldDomain (1 / 2) e :=
    continuousAt_fst.eventually ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)
  obtain ⟨U, hUsub, hU, hqU⟩ := mem_nhds_iff.mp (hdomain.and htarget)
  let Ψ := PartialChart.restrictSource Φ hU
  have hpΨ : q ∈ Ψ.source := ⟨hp, hqU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, ?_⟩
  · intro y hy
    exact hf y hy.1
  · intro p hp
    obtain ⟨hpd, hpt⟩ := hUsub hp.2
    refine ⟨hpd, ?_⟩
    change c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p)
    rw [hmap]
    exact c.splitChart.right_inv' hpt

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
