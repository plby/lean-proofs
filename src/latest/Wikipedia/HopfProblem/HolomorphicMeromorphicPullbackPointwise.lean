import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor

/-!
# Pointwise functoriality for actual local meromorphic sections

These identities keep the original section domains and base-point
germs explicit, avoiding any extension of local meromorphic functions
outside their domains.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]
  [J.Boundaryless] [IsManifold J ω N]

/-- Equal actual holomorphic maps give equal pulled-back germs of any
genuine local section on its original domain. -/
theorem germPullback_section_congr (f g : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (hg : IsOpenMap g) (hfg : ∀ x, f x = g x)
    (U : Opens N) (s : Section J N U) (x : M) (hx : f x ∈ U) (hx' : g x ∈ U) :
    germPullback I J f hf x (s ⟨f x, hx⟩) = germPullback I J g hg x (s ⟨g x, hx'⟩) := by
  have heq : f = g := ContMDiffMap.ext hfg
  cases heq
  rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic
