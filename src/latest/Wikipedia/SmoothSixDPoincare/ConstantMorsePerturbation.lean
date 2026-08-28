import Wikipedia.SmoothSixDPoincare.ManifoldRegularStability

/-!
# Small locally constant perturbations preserve the actual critical set

Adding a small multiple of a smooth cutoff that is locally constant near
every critical point preserves the native critical set exactly. The Morse
condition is also preserved. The cutoff may have different constants at
different critical points, so their values can be varied independently.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def constantPerturb (f ψ : M → ℝ) (a : ℝ) (x : M) : ℝ := f x + a * ψ x

theorem contMDiff_constantPerturb {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry (constantPerturb f ψ)) :=
  (hf.comp contMDiff_snd).add (contMDiff_fst.smul (hψ.comp contMDiff_snd))

/-- On a constant plateau, the actual native derivative is unchanged for every parameter. -/
theorem mfderiv_constantPerturb_of_locally_constant {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {x : M} {b : ℝ} (hψ : ψ =ᶠ[𝓝 x] fun _ => b) (a : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : constantPerturb f ψ a =ᶠ[𝓝 x] (fun y => f y + a * b) := by
    filter_upwards [hψ] with y hy
    simp only [constantPerturb, hy]
  rw [heq.mfderiv_eq]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (f + fun _ => a * b) x = _
  rw [mfderiv_add (hf.mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const]
  exact add_zero _

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- For all sufficiently small parameters, the Morse condition and the entire native critical set
are preserved, not merely the critical points already known to exist. -/
theorem eventually_constantPerturb_morse_criticalPoints {f ψ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ)
    (hconstant : ∀ p ∈ criticalPoints E f, ∃ b : ℝ, ψ =ᶠ[𝓝 p] fun _ => b) :
    ∀ᶠ a in 𝓝 (0 : ℝ), IsMorse E (constantPerturb f ψ a) ∧
      criticalPoints E (constantPerturb f ψ a) = criticalPoints E f := by
  have hfamily := contMDiff_constantPerturb hf hψ
  have hzero : constantPerturb f ψ 0 = f := by funext x; simp [constantPerturb]
  have hm₀ : IsMorseOn E (constantPerturb f ψ 0) univ := by
    rw [hzero]
    exact fun x _ => hm x
  have hmor := (isOpen_isMorseOn hfamily isCompact_univ).mem_nhds hm₀
  let U := ⋃ b : ℝ, interior {x : M | ψ x = b}
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_interior)
  have hcover : criticalPoints E (constantPerturb f ψ 0) ⊆ U := by
    rw [hzero]
    intro p hp
    obtain ⟨b, hb⟩ := hconstant p hp
    exact mem_iUnion.mpr ⟨b, mem_interior_iff_mem_nhds.mpr hb⟩
  have hfixed : ∀ a x, x ∈ U →
      (x ∈ criticalPoints E (constantPerturb f ψ a) ↔
        x ∈ criticalPoints E (constantPerturb f ψ 0)) := by
    intro a x hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hx
    have hlocal : ψ =ᶠ[𝓝 x] fun _ => b := mem_interior_iff_mem_nhds.mp hb
    rw [hzero]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (constantPerturb f ψ a) x = 0 ↔
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_constantPerturb_of_locally_constant hf hlocal a]
    rfl
  have hcrit := eventually_criticalPoints_eq hfamily 0 hU hcover hfixed
  rw [hzero] at hcrit
  filter_upwards [hmor, hcrit] with a ha hc
  exact ⟨fun x => ha x (mem_univ x), hc⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
