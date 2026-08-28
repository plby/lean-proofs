import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Closed-axis injectivity from a genuine regular chart and its two ends

The regular axis is injective because it lies in an actual partial
diffeomorphism. Two distinct endpoints outside that chart's target
cannot collide with its interior or with each other. Thus the closed
axis is injective without assuming a separate global embedding theorem.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing

variable {Z E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem injective_closed_axis_of_regular_chart
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞)
    {l r : ℝ} (γ : ℝ → M)
    (hsource : ∀ s ∈ Ioo l r, (s, (0 : Z)) ∈ Φ.source)
    (hregular : ∀ s ∈ Ioo l r, γ s = Φ (s, 0))
    (hleft : γ l ∉ Φ.target) (hright : γ r ∉ Φ.target) (hne : γ l ≠ γ r) :
    InjOn γ (Icc l r) := by
  have htarget (s : ℝ) (hs : s ∈ Ioo l r) : γ s ∈ Φ.target := by
    rw [hregular s hs]
    exact Φ.map_source' (hsource s hs)
  have hleftOnly (s : ℝ) (hs : s ∈ Icc l r) (heq : γ s = γ l) : s = l := by
    by_cases hsl : s = l
    · exact hsl
    by_cases hsr : s = r
    · subst s
      exact (hne heq.symm).elim
    have hi : s ∈ Ioo l r :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hleft (heq ▸ htarget s hi)).elim
  have hrightOnly (s : ℝ) (hs : s ∈ Icc l r) (heq : γ s = γ r) : s = r := by
    by_cases hsr : s = r
    · exact hsr
    by_cases hsl : s = l
    · subst s
      exact (hne heq).elim
    have hi : s ∈ Ioo l r :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hright (heq ▸ htarget s hi)).elim
  intro s hs t ht heq
  by_cases hsl : s = l
  · subst s
    exact (hleftOnly t ht heq.symm).symm
  by_cases hsr : s = r
  · subst s
    exact (hrightOnly t ht heq.symm).symm
  by_cases htl : t = l
  · subst t
    exact hleftOnly s hs heq
  by_cases htr : t = r
  · subst t
    exact hrightOnly s hs heq
  have hs' : s ∈ Ioo l r :=
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
  have ht' : t ∈ Ioo l r :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
  rw [hregular s hs', hregular t ht'] at heq
  exact congrArg Prod.fst
    (Φ.toOpenPartialHomeomorph.injOn (hsource s hs') (hsource t ht') heq)

end Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing
