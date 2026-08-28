import Wikipedia.HopfProblem.DegreeCollapseRegularInclusionHomology

/-!
# One native middle handle adjoins the actual common-cut sphere class

The regular band is an isomorphism for literal inclusions. The critical
window kills exactly the native attaching class, and the actual flow
section supplies its specified lift at the common cut. Thus the new
kernel is precisely the old kernel plus that actual section class.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.middle_inclusion_step
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    {a b : ℝ} (hab : a ≤ b) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hbp : b < S.toSurgeryWindows.lower p)
    (hband : ∀ y, f y ∈ Icc b (S.toSurgeryWindows.lower p) → y ∉ criticalPoints E f)
    (γ : C(S₂, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ,
      S.flow t (nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val)
    (hsurj : Surjective (singularHomologyMap (sublevelMap f hab) 2)) :
    let hau := (hab.trans hbp.le).trans
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le
    Surjective (singularHomologyMap (sublevelMap f hau) 2) ∧
      LinearMap.ker (singularHomologyMap (sublevelMap f hau) 2) =
        LinearMap.ker (singularHomologyMap (sublevelMap f hab) 2) ⊔
          Submodule.span ℤ {middleSectionClass γ} := by
  let hl := (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  let P := singularHomologyMap (sublevelMap f hab) 2
  let J := singularHomologyMap (sublevelMap f hbp.le) 2
  let Q := singularHomologyMap (sublevelMap f hl.le) 2
  have hJ : Bijective J := regular_sublevel_inclusion_bijective hf hbp.le hband 2
  obtain ⟨hQ, hkerQ⟩ := S.native_index_three_inclusion_relation hf p hp
  have hclass := S.native_attaching_class_of_flow_section hf p hp ha (hab.trans_lt hbp) γ horbit
  have hcomp : J.comp P = singularHomologyMap (sublevelMap f (hab.trans hbp.le)) 2 :=
    sublevelHomologyMap_comp f hab hbp.le 2
  have htotal : Q.comp (J.comp P) =
      singularHomologyMap (sublevelMap f ((hab.trans hbp.le).trans hl.le)) 2 := by
    rw [hcomp]
    exact sublevelHomologyMap_comp f (hab.trans hbp.le) hl.le 2
  have hkerJ : LinearMap.ker (J.comp P) = LinearMap.ker P := by
    ext v
    change J (P v) = 0 ↔ P v = 0
    exact ⟨fun h => hJ.injective (h.trans (map_zero J).symm), fun h => by rw [h, map_zero]⟩
  have hker : LinearMap.ker Q = Submodule.span ℤ {(J.comp P) (middleSectionClass γ)} := by
    rw [hcomp, hclass]
    exact hkerQ
  constructor
  · rw [← htotal]
    exact hQ.comp (hJ.surjective.comp hsurj)
  · rw [← htotal, HomologyTransport.ker_comp_span_singleton (J.comp P) Q
      (middleSectionClass γ) hker, hkerJ]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
