import Wikipedia.HopfProblem.OrbitPairCoincidenceDifferential

/-!
# The native synchronized pair domain of a surface family

Both evaluations use the same original time. Its model has dimension five
when the surface model has dimension two. Transversality means that the
native difference differential on this domain is surjective at a collision.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SynchronizedPairs

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

def first (q : ℝ × (M × M)) : ℝ × M := (q.1, q.2.1)

def second (q : ℝ × (M × M)) : ℝ × M := (q.1, q.2.2)

theorem first_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (I.prod I)) (𝓘(ℝ, ℝ).prod I) ∞ (first (M := M)) :=
  contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)

theorem second_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod (I.prod I)) (𝓘(ℝ, ℝ).prod I) ∞ (second (M := M)) :=
  contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)

def RegularOn (f : ℝ × M → N) (S : Set (ℝ × (M × M))) : Prop :=
  ∀ q ∈ S, f (first q) = f (second q) →
    Coincidence.TransverseAt (I := 𝓘(ℝ, ℝ).prod (I.prod I)) (J := J)
      (f ∘ first) (f ∘ second) q

theorem model_dimension [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2) :
    Module.finrank ℝ (ℝ × (E × E)) = 5 := by
  simp only [Module.finrank_prod, Module.finrank_self, hdim]

end Wikipedia.HopfProblem.OrbitPair.SynchronizedPairs
