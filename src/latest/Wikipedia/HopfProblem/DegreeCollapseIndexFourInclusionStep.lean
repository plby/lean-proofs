import Wikipedia.HopfProblem.DegreeCollapseRegularInclusionHomology
import Wikipedia.HopfProblem.DegreeCollapseIndexFourInclusion

/-!
# One index-four handle adjoins its actual common-cut three-sphere class

Across the real regular band, the literal sublevel inclusion is an
isomorphism. The native four-handle kills exactly its original attaching
class. Exact flow transport supplies the prescribed lift on the common
cut, so the enlarged kernel is the old kernel plus this actual sphere.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.index_four_inclusion_step
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 4)
    {a b : ℝ} (hab : a ≤ b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hbp : b < S.toSurgeryWindows.lower p)
    (hband : ∀ y, f y ∈ Icc b (S.toSurgeryWindows.lower p) → y ∉ criticalPoints E f)
    (γ : C(S₃, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ,
      S.flow t (nativeIndexFourAttachingSphere S p hp x).val = (γ x).val)
    (hsurj : Surjective (singularHomologyMap (sublevelMap f hab) 3)) :
    let hau := (hab.trans hbp.le).trans
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le
    Surjective (singularHomologyMap (sublevelMap f hau) 3) ∧
      LinearMap.ker (singularHomologyMap (sublevelMap f hau) 3) =
        LinearMap.ker (singularHomologyMap (sublevelMap f hab) 3) ⊔
          Submodule.span ℤ {threeSectionClass γ} := by
  let hl := (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  let P := singularHomologyMap (sublevelMap f hab) 3
  let J := singularHomologyMap (sublevelMap f hbp.le) 3
  let Q := singularHomologyMap (sublevelMap f hl.le) 3
  have hJ : Bijective J := regular_sublevel_inclusion_bijective hf hbp.le hband 3
  obtain ⟨hQ, hkerQ⟩ := S.native_index_four_inclusion_relation hf p hp
  have hclass := S.native_index_four_attaching_class_of_flow_section hf p hp ha
    (hab.trans_lt hbp) γ horbit
  have hcomp : J.comp P = singularHomologyMap (sublevelMap f (hab.trans hbp.le)) 3 :=
    sublevelHomologyMap_comp f hab hbp.le 3
  have htotal : Q.comp (J.comp P) =
      singularHomologyMap (sublevelMap f ((hab.trans hbp.le).trans hl.le)) 3 := by
    rw [hcomp]
    exact sublevelHomologyMap_comp f (hab.trans hbp.le) hl.le 3
  have hkerJ : LinearMap.ker (J.comp P) = LinearMap.ker P := by
    ext v
    change J (P v) = 0 ↔ P v = 0
    exact ⟨fun h => hJ.injective (h.trans (map_zero J).symm), fun h => by rw [h, map_zero]⟩
  have hker : LinearMap.ker Q = Submodule.span ℤ {(J.comp P) (threeSectionClass γ)} := by
    rw [hcomp, hclass]
    exact hkerQ
  constructor
  · rw [← htotal]
    exact hQ.comp (hJ.surjective.comp hsurj)
  · rw [← htotal, HomologyTransport.ker_comp_span_singleton (J.comp P) Q
      (threeSectionClass γ) hker, hkerJ]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
