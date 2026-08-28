import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

/-!
# Simultaneous normal limits in a finite family of native charts

The product of the actual compact bounded-holomorphic families gives one
subsequence for every chart. No compatibility or analyticity property of
the limits is postulated: holomorphicity follows from the proved
multivariable Weierstrass theorem.
-/

noncomputable section

open Set Filter
open scoped Topology Uniformity

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismFiniteNormalFamily

open HolomorphicAutomorphismNormalFamily

theorem exists_simultaneous_subseq
    {ι E F : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (f : ℕ → ι → E → F) (hfd : ∀ n i, DifferentiableOn ℂ (f n i) (U i))
    (C : ι → ℝ) (hfb : ∀ n i, ∀ z ∈ U i, ‖f n i z‖ ≤ C i) :
    ∃ (g : ι → E → F) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, DifferentiableOn ℂ (g i) (U i)) ∧
      (∀ i, TendstoLocallyUniformlyOn (fun n => f (φ n) i) (g i) atTop (U i)) ∧
      ∀ i, ∀ z ∈ U i, ‖g i z‖ ≤ C i := by
  let := Fintype.ofFinite ι
  let : ∀ i, (𝓤 (FunctionSpace (U i) F)).IsCountablyGenerated :=
    fun i => uniformity_isCountablyGenerated (F := F) (hU i)
  let P := ∀ i, FunctionSpace (U i) F
  let S : Set P := Set.pi univ (fun i => boundedHolomorphicFamily (F := F) (U i) (C i))
  have hS : IsCompact S := by
    simpa only [S, Set.pi, mem_univ, forall_true_left] using
      (isCompact_pi_infinite fun i => isCompact_boundedHolomorphicFamily (hU i) (C i))
  let f' : ℕ → P := fun n i => UniformOnFun.ofFun (compactSubsets (U i)) (f n i)
  have hf' : ∀ n, f' n ∈ S := fun n i _ => ⟨hfd n i, hfb n i⟩
  obtain ⟨g, hg, φ, hφ, hconv⟩ := hS.tendsto_subseq hf'
  refine ⟨fun i => evaluation (g i), φ, hφ,
    fun i => (hg i (mem_univ i)).1, ?_, fun i => (hg i (mem_univ i)).2⟩
  intro i
  have hi : Tendsto (fun n => f' (φ n) i) atTop (𝓝 (g i)) :=
    ((continuous_apply i).tendsto g).comp hconv
  exact (tendsto_iff_tendstoLocallyUniformlyOn (hU i)).mp hi

end Wikipedia.HopfProblem.HolomorphicAutomorphismFiniteNormalFamily
