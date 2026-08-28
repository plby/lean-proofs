import Wikipedia.HopfProblem.DegreeCollapseMorseLinearCoordinates
import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationPreservation

/-!
# Insert a supported Morse pair in an original regular chart

The replacement is an actual function on the unchanged manifold. The native
critical set gains exactly the two chart points, every old critical germ is
retained, and the total finite critical count increases by exactly two.
The input model is required to be Morse; its construction is separate.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open LocalFunctionReplacement MorseCancellationPreservation

variable {E D M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem insert_morse_chart_pair
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (L : E ≃L[ℝ] D)
    {f : M → ℝ} {b₀ b₁ : D → ℝ} {K : Set D} {p q : D}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hb₀ : ContDiff ℝ ∞ b₀) (hb₁ : ContDiff ℝ ∞ b₁)
    (hmb₁ : MorsePerturbation.IsMorse b₁)
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x)
    (hp : p ∈ Φ.source) (hq : q ∈ Φ.source) (hpq : p ≠ q)
    (hreg : ∀ x, fderiv ℝ b₀ x ≠ 0)
    (hcrit : ∀ x, fderiv ℝ b₁ x = 0 ↔ x = p ∨ x = q) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard = (criticalPoints E f).ncard + 2 ∧
      (∀ y, y ∈ criticalPoints E g ↔ y ∈ criticalPoints E f ∨ y = Φ p ∨ y = Φ q) ∧
      (∀ y, y ∉ Φ '' K → g =ᶠ[𝓝 y] f) ∧
      (∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
      ∀ z ∈ Φ.source, g (Φ z) = b₁ z := by
  let g := replace Φ f b₁
  have hg := contMDiff_replace Φ hf hb₁ hK hKΦ hmodel hfix
  have houtside (y : M) (hy : y ∉ Φ '' K) : g =ᶠ[𝓝 y] f :=
    replace_germ_off_support Φ hK hKΦ hmodel hfix hy
  have hnot (y : M) (hy : y ∈ Φ.target) : y ∉ criticalPoints E f := by
    intro hc
    have he := replace_critical_iff Φ f hb₀ hy
    rw [replace_self Φ hmodel] at he
    exact hreg (Φ.symm y) (he.mp hc)
  have hcritg (y : M) : y ∈ criticalPoints E g ↔
      y ∈ criticalPoints E f ∨ y = Φ p ∨ y = Φ q := by
    by_cases hy : y ∈ Φ.target
    · have he := replace_critical_iff Φ f hb₁ hy
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
      rw [he, hcrit]
      constructor
      · rintro (h | h)
        · exact Or.inr (Or.inl ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
        · exact Or.inr (Or.inr ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
      · rintro (hc | rfl | rfl)
        · exact False.elim (hnot y hy hc)
        · exact Or.inl (Φ.left_inv' hp)
        · exact Or.inr (Φ.left_inv' hq)
    · have hyK : y ∉ Φ '' K := by
        rintro ⟨z, hz, rfl⟩
        exact hy (Φ.map_source' (hKΦ hz))
      have hyp : y ≠ Φ p := fun h => hy (h.symm ▸ Φ.map_source' hp)
      have hyq : y ≠ Φ q := fun h => hy (h.symm ▸ Φ.map_source' hq)
      have he : y ∈ criticalPoints E g ↔ y ∈ criticalPoints E f := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
        rw [(houtside y hyK).mfderiv_eq]
        rfl
      simpa only [hyp, hyq, or_false] using he
  have hmg : IsMorse E g := by
    intro y
    by_cases hy : y ∈ Φ.target
    · have hx := Φ.map_target' hy
      have hmodelg : g ∘ Φ =ᶠ[𝓝 (Φ.symm y)] b₁ := by
        filter_upwards [Φ.open_source.mem_nhds hx] with z hz
        exact replace_chart Φ f b₁ hz
      have hh := isMorseAt_of_native_model_germ Φ L hx hb₁ hmb₁ hmodelg
      have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
      exact hright ▸ hh
    · apply isMorseAt_of_same_germ (hm y)
      apply houtside y
      rintro ⟨z, hz, rfl⟩
      exact hy (Φ.map_source' (hKΦ hz))
  have hneq : Φ p ≠ Φ q := fun h => hpq (Φ.toOpenPartialHomeomorph.injOn hp hq h)
  have hpnot := hnot (Φ p) (Φ.map_source' hp)
  have hqnot := hnot (Φ q) (Φ.map_source' hq)
  have heq : criticalPoints E g = insert (Φ p) (insert (Φ q) (criticalPoints E f)) := by
    ext y
    rw [hcritg]
    simp only [mem_insert_iff]
    tauto
  refine ⟨g, hg, hmg, ?_, hcritg, houtside, ?_, fun z hz => replace_chart Φ f b₁ hz⟩
  · rw [heq, ncard_insert_of_notMem
      (by simp only [mem_insert_iff, hneq, hpnot, or_self, not_false_eq_true])
      ((finite_criticalPoints hf hm).insert (Φ q)),
      ncard_insert_of_notMem hqnot (finite_criticalPoints hf hm)]
  · intro y hy
    apply houtside y
    rintro ⟨z, hz, rfl⟩
    exact hnot (Φ z) (Φ.map_source' (hKΦ hz)) hy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
