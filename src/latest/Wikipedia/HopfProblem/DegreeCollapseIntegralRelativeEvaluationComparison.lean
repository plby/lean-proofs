import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapNaturality
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocal
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainsFree

/-!
# The original relative cohomology pullback from the original homology map

With vanishing preceding relative homology, canonical integral evaluation
identifies the original pullback with precomposition by the original
homology map. This proves bijectivity, retaining the actual cochain map.
-/

noncomputable section

open Function CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open SingularCohomologyFree NoExoticSixSphere

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V) (n : ℕ)
  [Subsingleton (RelativeSingularHomology.Homology U n)]

theorem cohomologyPullback_succ_bijective
    (hn : Surjective (RelativeSingularHomology.map f hf n))
    (hs : Bijective (RelativeSingularHomology.map f hf (n + 1))) :
    Bijective (cohomologyPullback f hf (n + 1)) := by
  let K := RelativeSingularHomology.complex U
  let L := RelativeSingularHomology.complex V
  let (j : ℕ) : Module.Free ℤ (K.X j) := RelativeSingularHomology.chains_free U j
  let (j : ℕ) : Module.Free ℤ (L.X j) := RelativeSingularHomology.chains_free V j
  let : Subsingleton (L.homology n) := hn.subsingleton
  let : Module.Free ℤ (K.homology n) := Module.Free.of_subsingleton ℤ _
  let : Module.Free ℤ (L.homology n) := Module.Free.of_subsingleton ℤ _
  let e := LinearEquiv.ofBijective (RelativeSingularHomology.map f hf (n + 1)) hs
  have hnat (a : Cohomology V (n + 1)) (x : K.homology (n + 1)) :
      cohomologyEvaluation K (n + 1) (cohomologyPullback f hf (n + 1) a) x =
        cohomologyEvaluation L (n + 1) a (e x) :=
    cohomologyEvaluation_naturality (RelativeSingularHomology.mapChain f hf) (n + 1) a x
  constructor
  · intro a b hab
    apply LocalEvaluation.cohomologyEvaluation_succ_injective L n
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hnat, ← hnat, hab]
  · intro a
    let F := (cohomologyEvaluation K (n + 1) a).comp e.symm.toLinearMap
    obtain ⟨b, hb⟩ := LocalEvaluation.cohomologyEvaluation_surjective L (n + 1) F
    refine ⟨b, LocalEvaluation.cohomologyEvaluation_succ_injective K n ?_⟩
    ext x
    rw [hnat, hb]
    change cohomologyEvaluation K (n + 1) a (e.symm (e x)) =
      cohomologyEvaluation K (n + 1) a x
    rw [LinearEquiv.symm_apply_apply]

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
