import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCocycleLift
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Original cochains and relative cycles for the range of an embedding

An embedding identifies the source with its actual range. Strict
vanishing on source chains therefore gives strict vanishing on range
subspace chains. An original bounding chain gives an actual relative
cycle, with the original connecting map equal to its original boundary
class transported into that range.
-/

noncomputable section

open CategoryTheory Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralEmbeddingRange

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def rangeMap (f : C(X, Y)) : C(X, Set.range f) :=
  ⟨fun x ↦ ⟨f x, ⟨x, rfl⟩⟩, f.continuous.subtype_mk _⟩

theorem inclusion_rangeMap (f : C(X, Y)) :
    (subtypeInclusion (Set.range f)).comp (rangeMap f) = f := rfl

theorem quotientMap_inducedChain (f : C(X, Y)) (n : ℕ) (c : Chains X n) :
    quotientMap (Set.range f) n (inducedChain f n c) = 0 := by
  have he : (quotientMap (Set.range f) n).comp (inducedChain f n) = 0 := by
    apply chainMap_ext X n
    intro σ
    have hz := congrArg (fun g ↦ (g.f n).hom
      (simplexChain (Set.range f) n ((rangeMap f).comp σ))) (inclusion_projection (Set.range f))
    change quotientMap (Set.range f) n
      (inducedChain (subtypeInclusion (Set.range f)) n
        (simplexChain (Set.range f) n ((rangeMap f).comp σ))) = 0 at hz
    rw [inducedChain_simplex] at hz
    rw [LinearMap.comp_apply, inducedChain_simplex]
    exact hz
  exact LinearMap.congr_fun he c

theorem restriction_range_zero (f : C(X, Y)) (hf : IsEmbedding f) (n : ℕ)
    (c : SingularCohomologyCup.Cochain Y n) (hc : c.comp (inducedChain f n) = 0) :
    c.comp (inducedChain (subtypeInclusion (Set.range f)) n) = 0 := by
  let e : X ≃ₜ Set.range f := hf.toHomeomorph
  let r : C(Set.range f, X) := ⟨e.symm, e.symm.continuous⟩
  apply chainMap_ext (Set.range f) n
  intro σ
  have hs : f.comp (r.comp σ) =
      (subtypeInclusion (Set.range f)).comp σ := by
    apply ContinuousMap.ext
    intro t
    exact congrArg (fun y : Set.range f ↦ y.val) (e.apply_symm_apply (σ t))
  have he := LinearMap.congr_fun hc (simplexChain X n (r.comp σ))
  change c (inducedChain f n (simplexChain X n (r.comp σ))) = 0 at he
  rw [inducedChain_simplex, hs] at he
  rw [LinearMap.comp_apply, inducedChain_simplex]
  exact he

def rangeCycle (f : C(X, Y)) (n : ℕ) (z : ModuleHomology.Cycle (singularComplex X) n)
    (B : Chains Y (n + 1))
    (hB : ((singularComplex Y).d (n + 1) n).hom B = inducedChain f n z.val) :
    ModuleHomology.Cycle (complex (Set.range f)) (n + 1) :=
  ModuleHomology.mkCycle (complex (Set.range f)) (n + 1) (quotientMap (Set.range f) (n + 1) B)
    (by
      change ((complex (Set.range f)).d (n + 1) n).hom
        (quotientMap (Set.range f) (n + 1) B) = 0
      rw [boundary_quotientMap, hB, quotientMap_inducedChain])

theorem rangeCycle_val (f : C(X, Y)) (n : ℕ) (z : ModuleHomology.Cycle (singularComplex X) n)
    (B : Chains Y (n + 1))
    (hB : ((singularComplex Y).d (n + 1) n).hom B = inducedChain f n z.val) :
    (rangeCycle f n z B hB).val = quotientMap (Set.range f) (n + 1) B := rfl

theorem connecting_rangeCycle (f : C(X, Y)) (n : ℕ)
    (z : ModuleHomology.Cycle (singularComplex X) n) (B : Chains Y (n + 1))
    (hB : ((singularComplex Y).d (n + 1) n).hom B = inducedChain f n z.val) :
    connecting (Set.range f) n
      (ModuleHomology.cycleClass (complex (Set.range f)) (n + 1) (rangeCycle f n z B hB)) =
    singularHomologyMap (rangeMap f) n (ModuleHomology.cycleClass (singularComplex X) n z) := by
  let z₁ := ModuleHomology.mapCycles (singularChainMap (rangeMap f)) n z
  have hz₁ : inducedChain (subtypeInclusion (Set.range f)) n z₁.val =
      ((singularComplex Y).d (n + 1) n).hom B := by
    change inducedChain (subtypeInclusion (Set.range f)) n
      (ModuleHomology.mapCycles (singularChainMap (rangeMap f)) n z).val = _
    rw [ModuleHomology.mapCycles_val]
    change ((inducedChain (subtypeInclusion (Set.range f)) n).comp
      (inducedChain (rangeMap f) n)) z.val = _
    rw [← inducedChain_comp, inclusion_rangeMap]
    exact hB.symm
  have he := PeriodTorusHigherHomology.connectingMap_cycleClass
    (sequence_shortExact (Set.range f)) n
    (rangeCycle f n z B hB) B rfl z₁ hz₁
  exact he.trans (ModuleHomology.homologyMap_cycleClass (singularChainMap (rangeMap f)) n z).symm

end Wikipedia.HopfProblem.DegreeCollapse.IntegralEmbeddingRange
