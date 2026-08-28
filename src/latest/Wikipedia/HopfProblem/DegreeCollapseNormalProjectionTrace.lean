import Wikipedia.HopfProblem.DegreeCollapseCenteredSheetPassage

/-!
# Normal projections detect the actual transverse trace

A surjective native normal derivative annihilating the belt tangent turns
native transversality into a bijective normal trace derivative. The fixed
terminal chart supplies its common normal factor by actual differentiation.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M U H X V H' Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [TopologicalSpace H] {I : ModelWithCorners ℝ U H}
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'}
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

theorem bijective_trace_normal_of_native_transverse
    {f : X → M} {g : Y → M} {n : M → N} {x : X} {y : Y}
    (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y))
    (hpoint : g y = f x)
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) f g x y)
    (hsurj : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp
      (mfderiv I' 𝓘(ℝ, E) g y) = 0)
    (hdim : Module.finrank ℝ U = Module.finrank ℝ N) :
    Bijective (mfderiv I 𝓘(ℝ, N) (n ∘ f) x) := by
  let Q : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)
  let B : V →L[ℝ] E := mfderiv I' 𝓘(ℝ, E) g y
  let A : U →L[ℝ] E := mfderiv I 𝓘(ℝ, E) f x
  have hbij : Bijective (Q.comp A) :=
    TransverseCoordinates.bijective_normal_comp Q B A hsurj
      (TransverseCoordinates.surjective_coprod_swap A B (htrans hpoint)) hzero hdim
  have hn' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (f x) := hpoint ▸ hn
  have hder : (mfderiv I 𝓘(ℝ, N) (n ∘ f) x : U →L[ℝ] N) = Q.comp A := by
    rw [mfderiv_comp x hn' hf, ← hpoint]
    rfl
  rw [hder]
  exact hbij

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ N] in
theorem hasFDerivAt_terminal_normal_factor
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞)
    (hΦ : ((1 : ℝ), (0 : U × V)) ∈ Φ.source)
    {n : M → N} (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (1, 0))) :
    HasFDerivAt (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0))))
      (fderiv ℝ (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0)))) 0) 0 := by
  let Q : (ℝ × U) → ℝ × (U × V) := fun z => (1 + z.1, (z.2, 0))
  have hQ : ContDiff ℝ ∞ Q :=
    (contDiff_const.add contDiff_fst).prodMk (contDiff_snd.prodMk contDiff_const)
  have hQ0 : Q 0 = (1, 0) := by
    change ((1 : ℝ) + 0, ((0 : U), (0 : V))) = (1, 0)
    rw [add_zero]
    rfl
  have hΦ' : ContMDiffAt 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) ∞ Φ (Q 0) := by
    rw [hQ0]
    exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hΦ)
  have hn' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (Q 0)) := by rw [hQ0]; exact hn
  have hs : ContDiffAt ℝ ∞ (fun z : ℝ × U => n (Φ (Q z))) 0 :=
    (ContMDiffAt.comp (g := n) (f := fun z : ℝ × U => Φ (Q z))
      0 hn' (hΦ'.comp 0 hQ.contMDiff.contMDiffAt)).contDiffAt
  exact (hs.differentiableAt (by simp)).hasFDerivAt

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
