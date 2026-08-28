import Wikipedia.HopfProblem.DegreeCollapseRegularTimeMorseBand
import Wikipedia.HopfProblem.DegreeCollapseRelativeMorseApproximation

/-!
# A genuine Morse function with exactly the original zero fiber and halves

Relative uniform approximation is applied outside a smaller protected
regular band. Exact equality in that band and uniform smallness elsewhere
preserve all three signs. At every original zero the two functions agree
on a neighborhood, so their native derivatives and regularity agree too.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare ManifoldMorse

theorem same_sign_of_near_equal (a b δ : ℝ) (hδ : 0 < δ)
    (heq : |a| ≤ δ → b = a) (hclose : |b - a| < δ) :
    (b = 0 ↔ a = 0) ∧ (0 ≤ b ↔ 0 ≤ a) ∧ (0 < b ↔ 0 < a) := by
  by_cases ha : |a| ≤ δ
  · rw [heq ha]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  · have hlarge : δ < |a| := lt_of_not_ge ha
    have hbounds := abs_lt.mp hclose
    by_cases ha0 : 0 ≤ a
    · rw [abs_of_nonneg ha0] at hlarge
      have ha' : 0 < a := hδ.trans hlarge
      have hb : 0 < b := by linarith [hbounds.1]
      exact ⟨iff_of_false (ne_of_gt hb) (ne_of_gt ha'),
        iff_of_true hb.le ha0, iff_of_true hb ha'⟩
    · have ha' : a < 0 := lt_of_not_ge ha0
      rw [abs_of_neg ha'] at hlarge
      have hb : b < 0 := by linarith [hbounds.2]
      exact ⟨iff_of_false (ne_of_lt hb) (ne_of_lt ha'),
        iff_of_false (not_le.mpr hb) ha0,
        iff_of_false (not_lt.mpr hb.le) (not_lt.mpr ha'.le)⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ}

theorem exists_morse_preserving_band (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      ∃ δ : ℝ, 0 < δ ∧ EqOn g f {p : M | |f p| ≤ δ} ∧
        ∀ p : M, |g p - f p| < δ := by
  obtain ⟨r, hr, hm⟩ := exists_morse_zero_band hf hreg
  let K : Set M := {p | |f p| ≤ r}
  let O : Set M := {p | r / 2 < |f p|}
  have hK : IsCompact K := (isClosed_le hf.continuous.abs continuous_const).isCompact
  have hO : IsOpen O := isOpen_lt continuous_const hf.continuous.abs
  have hcover : (interior K)ᶜ ⊆ O := by
    intro p hp
    have hpr : ¬ |f p| < r := by
      intro hlt
      apply hp
      apply mem_interior_iff_mem_nhds.mpr
      exact mem_of_superset ((isOpen_lt hf.continuous.abs continuous_const).mem_nhds hlt)
        (fun q hq ↦ (show q ∈ K from (show |f q| < r from hq).le))
    exact (half_lt_self hr).trans_le (le_of_not_gt hpr)
  obtain ⟨g, hg, hmg, hclose, hfixed⟩ :=
    exists_relative_morse_close hf K O hK hm hO hcover (r / 2) (half_pos hr)
  refine ⟨g, hg, hmg, r / 2, half_pos hr, ?_, hclose⟩
  intro p hp
  apply hfixed
  change ¬ r / 2 < |f p|
  exact not_lt.mpr (show |f p| ≤ r / 2 from hp)

theorem exists_morse_preserving_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ p, f p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (∀ p, f p = 0 → g =ᶠ[𝓝 p] f) ∧
      (∀ p, g p = 0 ↔ f p = 0) ∧ (∀ p, 0 ≤ g p ↔ 0 ≤ f p) ∧
      (∀ p, 0 < g p ↔ 0 < f p) ∧
      ∀ p, g p = 0 → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p) := by
  obtain ⟨g, hg, hm, δ, hδ, hfixed, hclose⟩ := exists_morse_preserving_band hf hreg
  have hsign (p : M) : (g p = 0 ↔ f p = 0) ∧
      (0 ≤ g p ↔ 0 ≤ f p) ∧ (0 < g p ↔ 0 < f p) :=
    same_sign_of_near_equal (f p) (g p) δ hδ (fun hp ↦ hfixed hp) (hclose p)
  have hgerm (p : M) (hp : f p = 0) : g =ᶠ[𝓝 p] f := by
    have hmem : p ∈ {x : M | |f x| < δ} := by simpa [hp] using hδ
    filter_upwards [(isOpen_lt hf.continuous.abs continuous_const).mem_nhds hmem] with x hx
    exact hfixed hx.le
  refine ⟨g, hg, hm, hgerm, fun p ↦ (hsign p).1,
    fun p ↦ (hsign p).2.1, fun p ↦ (hsign p).2.2, ?_⟩
  intro p hp
  have hfp := (hsign p).1.mp hp
  rw [(hgerm p hfp).mfderiv_eq]
  exact hreg p hfp

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse
