import Wikipedia.HopfProblem.HolomorphicDifferentialFormsPullback

/-!
# Functoriality and detection of genuine holomorphic forms

The chain rule proves functoriality for the actual derivative pullback.
Surjective submersions detect forms, and forms pulled back from a quotient
are invariant under actual holomorphic deck transformations.
-/

noncomputable section

open Function Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]
  {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ, F) ω N] {p : ℕ}

@[simp] theorem pullback_id (θ : Form E M p) :
    pullback id contMDiff_id θ = θ := by
  apply ContMDiffSection.ext
  intro x
  ext v
  simp [pullback_apply]

theorem pullback_congr {f g : M → N} (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω g) (hfg : f = g) :
    (pullback f hf : Form F N p →ₗ[ℂ] Form E M p) = pullback g hg := by
  subst g
  rfl

variable {G P : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ G] [TopologicalSpace P] [ChartedSpace G P]
  [IsManifold 𝓘(ℂ, G) ω P]

/-- The actual chain rule gives contravariant functoriality on forms. -/
theorem pullback_comp (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (g : N → P) (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ω g) (θ : Form G P p) :
    pullback (g ∘ f) (hg.comp hf) θ = pullback f hf (pullback g hg θ) := by
  apply ContMDiffSection.ext
  intro x
  rw [pullback_apply, pullback_apply, pullback_apply,
    mfderiv_comp x (hg.mdifferentiable (by simp) (f x)) (hf.mdifferentiable (by simp) x)]
  rfl

/-- Actual deck invariance follows from equality of the actual maps. -/
theorem pullback_deck (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (g : M → M) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω g)
    (hfg : f ∘ g = f) (θ : Form F N p) :
    pullback g hg (pullback f hf θ) = pullback f hf θ := by
  rw [← pullback_comp]
  rw [pullback_congr (hf.comp hg) hf hfg]

/-- A surjective submersion detects zero on the full alternating
cotangent spaces, in every degree. -/
theorem pullback_eq_zero_iff (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f) (hsurj : Surjective f)
    (hderiv : ∀ x, Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (θ : Form F N p) : pullback f hf θ = 0 ↔ θ = 0 := by
  constructor
  · intro h
    apply ContMDiffSection.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    ext v
    choose w hw using fun i : Fin p => hderiv x (v i)
    have hx := congrArg (fun η : Form E M p => η x) h
    change (θ (f x)).compContinuousLinearMap (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x) = 0 at hx
    have hv := DFunLike.congr_fun hx w
    have hvec : (fun i => mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x (w i)) = v := funext hw
    change θ (f x) (fun i => mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x (w i)) = 0 at hv
    rw [hvec] at hv
    exact hv
  · rintro rfl
    exact map_zero _

/-- Vanishing on a dense set detects an actual holomorphic form, by
continuity of its actual covector in every native trivialization. -/
theorem eq_zero_of_dense {s : Set M} (hs : Dense s)
    (θ : Form E M p) (hθ : ∀ x ∈ s, θ x = 0) : θ = 0 := by
  apply ContMDiffSection.ext
  intro x
  have hx : x ∈ closure s := by rw [hs.closure_eq]; trivial
  have hfreq := (mem_closure_iff_frequently.mp hx).mono (fun y hy => show
      inCoordinates E M θ x y = 0 from by
    ext v
    rw [inCoordinates_apply, hθ y hy]
    rfl)
  have heq := tendsto_nhds_unique_of_frequently_eq
    (inCoordinates_holomorphicAt E M θ x).continuousAt tendsto_const_nhds hfreq
  ext v
  have hv := congrArg (fun a : E [⋀^Fin p]→L[ℂ] ℂ => a v) heq
  have hz : inCoordinates E M θ x x v = (0 : ℂ) := hv.trans rfl
  calc
    θ x v = inCoordinates E M θ x x v := by rw [inCoordinates_self]; rfl
    _ = 0 := hz
    _ = (0 : Form E M p) x v := rfl

end Wikipedia.HopfProblem.HolomorphicDifferentialForms
