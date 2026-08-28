import Wikipedia.HopfProblem.HolomorphicMeromorphicDescentGluing

/-!
# Genuine local meromorphic descent on a specified open target domain

The local fractions may be presented on different original target
neighborhoods. Their actual pullbacks prove compatibility, and their
germs glue to a section of the original meromorphic sheaf on the
specified open set. The domain is not replaced by a new manifold.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold I ω M] [J.Boundaryless] [IsManifold J ω N]

/-- Local genuine descents glue uniquely on any original open target
domain, with compatibility derived from the actual surjective map. -/
theorem existsUnique_descent_on_open (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (hsurj : _root_.Function.Surjective f) (g : Function I M) (W : Opens N)
    (hlocal : ∀ y : W, ∃ (U : Opens N) (_hy : y.val ∈ U) (s : Section J N U),
      pullbackSection I J f hf U s =
        restrict I M (le_top : pullbackOpen I J f U ≤ ⊤) g) :
    ∃! s : Section J N W, pullbackSection I J f hf W s =
      restrict I M (le_top : pullbackOpen I J f W ≤ ⊤) g := by
  classical
  have hlocal' : ∀ y : W, ∃ (U : Opens N) (_hUW : U ≤ W) (_hy : y.val ∈ U)
      (s : Section J N U), pullbackSection I J f hf U s =
        restrict I M (le_top : pullbackOpen I J f U ≤ ⊤) g := by
    intro y
    obtain ⟨U, hy, s, hs⟩ := hlocal y
    refine ⟨U ⊓ W, inf_le_right, ⟨hy, y.property⟩,
      restrict J N (inf_le_left : U ⊓ W ≤ U) s, ?_⟩
    apply section_ext
    intro x
    exact congrArg (fun a : Section I M (pullbackOpen I J f U) =>
      a ⟨x.val, x.property.1⟩) hs
  choose U hUW hU s hs using hlocal'
  let a : (y : W) → Germ J N y.val := fun y => s y ⟨y.val, hU y⟩
  have ha (y : W) (z : U y) : a ⟨z.val, hUW y z.property⟩ = s y z := by
    exact local_descent_germs_eq I J f hf hsurj g
      (s ⟨z.val, hUW y z.property⟩) (s y)
      (hs ⟨z.val, hUW y z.property⟩) (hs y) z.val
      (hU ⟨z.val, hUW y z.property⟩) z.property
  let b : Section J N W := ⟨a, by
    intro y
    obtain ⟨V, hVU, hyV, p, q, hq, hrep⟩ :=
      local_representation J N (s y) ⟨y.val, hU y⟩
    refine ⟨V, hyV, homOfLE (hVU.trans (hUW y)), p, q, hq, ?_⟩
    intro z
    exact (ha y (Set.inclusion hVU z)).trans (hrep z)⟩
  have hb : pullbackSection I J f hf W b =
      restrict I M (le_top : pullbackOpen I J f W ≤ ⊤) g := by
    apply section_ext
    intro x
    change germPullback I J f hf x.val
      (s ⟨f x.val, x.property⟩ ⟨f x.val, hU ⟨f x.val, x.property⟩⟩) = g ⟨x.val, by trivial⟩
    exact congrArg (fun t : Section I M (pullbackOpen I J f (U ⟨f x.val, x.property⟩)) =>
      t ⟨x.val, hU ⟨f x.val, x.property⟩⟩) (hs ⟨f x.val, x.property⟩)
  refine ⟨b, hb, ?_⟩
  intro t ht
  exact pullbackRingHom_injective I J f hf hsurj W (ht.trans hb.symm)

end Wikipedia.HopfProblem.HolomorphicMeromorphic
