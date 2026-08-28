import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyLimit
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyNormalization

/-!
# Finite-dimensional holomorphic normal families

Bounded holomorphic coordinate maps have actual compact closure for
compact convergence, and every point of that closure is holomorphic.
The sequential form produces a strictly increasing subsequence, a
holomorphic limit, and locally uniform convergence of the Fréchet
derivatives. Compact normalizations survive the limiting process.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E]

section CompleteTarget

variable [CompleteSpace F]

/-- Every compact-convergence closure point of a holomorphic family is
holomorphic, for the genuine functions on the given open domain. -/
theorem differentiableOn_of_mem_closure {U : Set E} (hU : IsOpen U)
    {s : Set (FunctionSpace U F)}
    (hs : ∀ f ∈ s, DifferentiableOn ℂ (evaluation f) U)
    {f : FunctionSpace U F} (hf : f ∈ closure s) :
    DifferentiableOn ℂ (evaluation f) U := by
  let : (𝓝[s] f).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hf
  exact tendstoLocallyUniformlyOn_differentiableOn
    (evaluation_tendstoLocallyUniformlyOn hU)
    (eventually_mem_nhdsWithin.mono fun g hg => hs g hg) hU

/-- Holomorphicity is closed in the actual compact-convergence topology. -/
theorem isClosed_holomorphic {U : Set E} (hU : IsOpen U) :
    IsClosed {f : FunctionSpace U F | DifferentiableOn ℂ (evaluation f) U} := by
  apply closure_subset_iff_isClosed.mp
  intro f hf
  exact differentiableOn_of_mem_closure hU (fun _ hg => hg) hf

end CompleteTarget

variable [FiniteDimensional ℂ F]

/-- The bounded holomorphic maps, as a subset of the actual function space. -/
def boundedHolomorphicFamily (U : Set E) (C : ℝ) : Set (FunctionSpace U F) :=
  {f | DifferentiableOn ℂ (evaluation f) U ∧ ∀ z ∈ U, ‖evaluation f z‖ ≤ C}

/-- The family with a fixed bound is itself compact: its closure does not
introduce nonholomorphic functions or lose the bound. -/
theorem isCompact_boundedHolomorphicFamily {U : Set E} (hU : IsOpen U) (C : ℝ) :
    IsCompact (boundedHolomorphicFamily (F := F) U C) := by
  have hclosed : IsClosed (boundedHolomorphicFamily (F := F) U C) := by
    apply closure_subset_iff_isClosed.mp
    intro f hf
    exact ⟨differentiableOn_of_mem_closure hU (fun _ hg => hg.1) hf,
      norm_le_of_mem_closure hU (fun _ hg => hg.2) hf⟩
  have hc := isCompact_closure_of_bounded_holomorphic hU
    (s := boundedHolomorphicFamily (F := F) U C) (fun _ hf => hf.1)
    ⟨C, fun _ hf => hf.2⟩
  rwa [hclosed.closure_eq] at hc

/-- The normal-family subsequence theorem in arbitrary finite-dimensional
complex coordinates. All holomorphicity and bound properties of the limit
are conclusions, not additional assumptions. -/
theorem exists_subseq_tendstoLocallyUniformlyOn {U : Set E} (hU : IsOpen U)
    (f : ℕ → E → F) (hfd : ∀ n, DifferentiableOn ℂ (f n) U) {C : ℝ}
    (hfb : ∀ n, ∀ z ∈ U, ‖f n z‖ ≤ C) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U ∧
      ∀ z ∈ U, ‖g z‖ ≤ C := by
  obtain ⟨g, φ, hφ, hconv, hbound⟩ := exists_subseq_compact_convergence hU f hfd hfb
  exact ⟨g, φ, hφ, tendstoLocallyUniformlyOn_differentiableOn hconv
    (Eventually.of_forall fun n => hfd (φ n)) hU, hconv, hbound⟩

/-- The same subsequence also converges locally uniformly after taking the
actual complex Fréchet derivative. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_fderiv {U : Set E} (hU : IsOpen U)
    (f : ℕ → E → F) (hfd : ∀ n, DifferentiableOn ℂ (f n) U) {C : ℝ}
    (hfb : ∀ n, ∀ z ∈ U, ‖f n z‖ ≤ C) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℂ (f (φ n))) (fderiv ℂ g) atTop U ∧
      ∀ z ∈ U, ‖g z‖ ≤ C := by
  obtain ⟨g, φ, hφ, hg, hconv, hbound⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn hU f hfd hfb
  exact ⟨g, φ, hφ, hg, hconv, tendstoLocallyUniformlyOn_fderiv hconv
    (Eventually.of_forall fun n => hfd (φ n)) hU, hbound⟩

/-- A compactly attained normalization survives in the holomorphic normal
limit, so normalized displacements cannot converge to zero everywhere. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_normalized {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : ℕ → E → F) (hfd : ∀ n, DifferentiableOn ℂ (f n) U) {C r : ℝ}
    (hfb : ∀ n, ∀ z ∈ U, ‖f n z‖ ≤ C)
    (hnorm : ∀ n, ∃ x ∈ K, ‖f n x‖ = r) :
    ∃ (g : E → F) (φ : ℕ → ℕ), StrictMono φ ∧ DifferentiableOn ℂ g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U ∧
      (∀ z ∈ U, ‖g z‖ ≤ C) ∧ ∃ z ∈ K, ‖g z‖ = r := by
  obtain ⟨g, φ, hφ, hg, hconv, hbound⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn hU f hfd hfb
  exact ⟨g, φ, hφ, hg, hconv, hbound,
    exists_point_norm_eq_of_compact hU hK hKU hconv
      (fun n => hfd (φ n)) (fun n => hnorm (φ n))⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily
