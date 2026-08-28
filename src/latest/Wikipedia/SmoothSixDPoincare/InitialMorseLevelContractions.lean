import Wikipedia.SmoothSixDPoincare.MorseDiskPropagation
import Wikipedia.SmoothSixDPoincare.ManifoldFermat
import Wikipedia.SmoothSixDPoincare.IsolatedMorseBand
import Wikipedia.NoExoticSixSphere.SphereConnectivity

/-!
# Circle contractions in the initial regular Morse level

Distinct critical values make the compact manifold's global minimum unique.
The actual small sublevel disk and its boundary homeomorphism then supply the
initial level's circle contractions. No sphere-recognition theorem for the
whole manifold is used.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

namespace SublevelDisk

variable {M : Type*} [TopologicalSpace M] [T2Space M] {f : M → ℝ} {a : ℝ} {n : ℕ}

/-- The boundary of an actual sublevel disk of dimension at least three has circle contractions. -/
theorem circle_nullhomotopies (d : SublevelDisk (n + 1) f a) (hn : 1 < n) :
    ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = a}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let e : Hemisphere.Sphere n ≃ₜ {x : M // f x = a} := d.boundaryHomeomorph
  let forward : C(Hemisphere.Sphere n, {x : M // f x = a}) := ⟨e, e.continuous⟩
  let backward : C({x : M // f x = a}, Hemisphere.Sphere n) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := NoExoticSixSphere.sphere_sphere_nullhomotopic hn (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

end SublevelDisk

namespace ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- All levels between a unique minimum and the next critical value have circle contractions. -/
theorem SignedMorseChart.circle_nullhomotopies_before_next_critical
    {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b)
    (hregular : ∀ x, f p < f x → f x ≤ b → x ∉ criticalPoints E f)
    {n : ℕ} (hdim : Module.finrank ℝ E = n + 1) (hn : 1 < n) :
    ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = b}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  obtain ⟨d⟩ := c.nonempty_sublevelDisk_before_next_critical hf hunique hb hregular
  have d' : SublevelDisk (n + 1) f b := hdim ▸ d
  exact d'.circle_nullhomotopies hn

variable [Nonempty M]

/-- Supply the initial regular level and its contractions from an original excellent
Morse function. -/
theorem exists_initial_level_circle_nullhomotopies {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) (hdim : Module.finrank ℝ E = 6) :
    ∃ p ∈ criticalPoints E f, (∀ x, f x ≤ f p → x = p) ∧
      ∃ a > f p, (∀ x, f p < f x → f x ≤ a → x ∉ criticalPoints E f) ∧
        (∀ g : C(Hemisphere.Sphere 1, {x : M // f x = a}),
          ∃ q, g.Homotopic (ContinuousMap.const _ q)) := by
  obtain ⟨p, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
  have hglobal : ∀ x, f p ≤ f x := fun x => hmin (mem_univ x)
  have hp : p ∈ criticalPoints E f :=
    mem_criticalPoints_of_localMin hf (Eventually.of_forall hglobal)
  have hunique : ∀ x, f x ≤ f p → x = p := by
    intro x hx
    have hxcrit : x ∈ criticalPoints E f := mem_criticalPoints_of_localMin hf
      (Eventually.of_forall (fun y => hx.trans (hglobal y)))
    exact hinj hxcrit hp (le_antisymm hx (hglobal x))
  obtain ⟨ρ, hρ, -, hband⟩ := exists_isolating_radius (finite_criticalPoints hf hm) p
    (fun x hx hval => hinj hx hp hval) zero_lt_one
  let a := f p + ρ ^ 2
  have ha : f p < a := by dsimp [a]; linarith [sq_pos_of_pos hρ]
  have hregular : ∀ x, f p < f x → f x ≤ a → x ∉ criticalPoints E f := by
    intro x hxlo hxhi hxcrit
    have hxp := hband x hxcrit ⟨by linarith [sq_nonneg ρ], hxhi⟩
    rw [hxp] at hxlo
    exact lt_irrefl _ hxlo
  obtain ⟨c⟩ := nonempty_signedMorseChart hf hm p hp
  exact ⟨p, hp, hunique, a, ha, hregular,
    c.circle_nullhomotopies_before_next_critical hf hunique ha hregular hdim (by norm_num)⟩

end ManifoldMorse

end Wikipedia.SmoothSixDPoincare
