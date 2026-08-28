import Wikipedia.HopfProblem.DegreeCollapseIntegralSmallCohomologySequence
import Wikipedia.HopfProblem.DegreeCollapseIntegralCochainBiproduct

/-!
# Mayer--Vietoris for the original integral relative cohomology groups

Transport the proved small-cochain sequence by the original open-union
comparison and the canonical integral biproduct coordinates. The
connecting map and all three exactness identities refer to these actual
relative cohomology groups and their original chain-induced maps.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (U V : Set X)

def middleEquiv (n : ℕ) : MiddleCohomology U V n ≃ₗ[ℤ] (Cohomology U n × Cohomology V n) :=
  IntegralCochainBiproduct.cohomologyBiprodEquiv
    (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U)
    (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V) n

def differenceMap (n : ℕ) : (Cohomology U n × Cohomology V n) →ₗ[ℤ] Cohomology (U ∩ V) n :=
  (secondMap U V n).comp (middleEquiv U V n).symm.toLinearMap

variable (hU : IsOpen U) (hV : IsOpen V)

def firstMap (n : ℕ) : Cohomology (U ∪ V) n →ₗ[ℤ] (Cohomology U n × Cohomology V n) :=
  (middleEquiv U V n).toLinearMap.comp
    ((smallFirstMap U V n).comp (smallUnionEquiv U V hU hV n).toLinearMap)

/-- The actual connecting homomorphism transported through original integral excision. -/
def connecting (n : ℕ) : Cohomology (U ∩ V) n →ₗ[ℤ] Cohomology (U ∪ V) (n + 1) :=
  (smallUnionEquiv U V hU hV (n + 1)).symm.toLinearMap.comp (smallConnecting U V n)

theorem firstMap_eq (n : ℕ) :
    firstMap U V hU hV n = (middleEquiv U V n).toLinearMap.comp
      (HomologicalComplex.homologyMap
        (dualMap (RelativeMayerVietoris.rightMap (ModuleCat.of ℤ ℤ) U V)) n).hom := by
  rw [← RelativeMayerVietoris.smallRightMap_quotient, dualMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

theorem exact_left (n : ℕ) :
    LinearMap.range (connecting U V hU hV n) = LinearMap.ker (firstMap U V hU hV (n + 1)) := by
  let E := smallUnionEquiv U V hU hV (n + 1)
  let M := middleEquiv U V (n + 1)
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨c, rfl⟩
    change M (smallFirstMap U V (n + 1) (E (E.symm (smallConnecting U V n c)))) = 0
    rw [LinearEquiv.apply_symm_apply]
    have hc : smallFirstMap U V (n + 1) (smallConnecting U V n c) = 0 :=
      (small_exact_left U V n).le ⟨c, rfl⟩
    exact (congrArg M hc).trans M.map_zero
  · intro ha
    change M (smallFirstMap U V (n + 1) (E a)) = 0 at ha
    have ha' : E a ∈ LinearMap.ker (smallFirstMap U V (n + 1)) :=
      M.injective (ha.trans M.map_zero.symm)
    obtain ⟨c, hc⟩ := (small_exact_left U V n).ge ha'
    refine ⟨c, E.injective ?_⟩
    exact (E.apply_symm_apply (smallConnecting U V n c)).trans hc

theorem exact_middle (n : ℕ) :
    LinearMap.range (firstMap U V hU hV n) = LinearMap.ker (differenceMap U V n) := by
  let E := smallUnionEquiv U V hU hV n
  let M := middleEquiv U V n
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    change secondMap U V n (M.symm (M (smallFirstMap U V n (E b)))) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact (small_exact_middle U V n).le ⟨E b, rfl⟩
  · intro ha
    change M.symm a ∈ LinearMap.ker (secondMap U V n) at ha
    obtain ⟨b, hb⟩ := (small_exact_middle U V n).ge ha
    refine ⟨E.symm b, ?_⟩
    change M (smallFirstMap U V n (E (E.symm b))) = a
    rw [LinearEquiv.apply_symm_apply, hb, LinearEquiv.apply_symm_apply]

theorem exact_right (n : ℕ) :
    LinearMap.range (differenceMap U V n) = LinearMap.ker (connecting U V hU hV n) := by
  let E := smallUnionEquiv U V hU hV (n + 1)
  let M := middleEquiv U V n
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    change E.symm (smallConnecting U V n (secondMap U V n (M.symm b))) = 0
    have hb : smallConnecting U V n (secondMap U V n (M.symm b)) = 0 :=
      (small_exact_right U V n).le ⟨M.symm b, rfl⟩
    exact (congrArg E.symm hb).trans E.symm.map_zero
  · intro ha
    change E.symm (smallConnecting U V n a) = 0 at ha
    have ha' : a ∈ LinearMap.ker (smallConnecting U V n) :=
      E.symm.injective (ha.trans E.symm.map_zero.symm)
    obtain ⟨b, hb⟩ := (small_exact_right U V n).ge ha'
    refine ⟨M b, ?_⟩
    change secondMap U V n (M.symm (M b)) = a
    rw [LinearEquiv.symm_apply_apply]
    exact hb

/-- Degree zero retains injectivity because the original cochain row has no incoming term. -/
theorem firstMap_zero_injective : Function.Injective (firstMap U V hU hV 0) := by
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (smallSequence U V)).mp (smallSequence_shortExact U V) 0
  let : Mono (((smallSequence U V).f).f 0) := hd.mono_f
  let : Mono (HomologicalComplex.homologyMap (smallSequence U V).f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (smallSequence U V).f 0
      (by intro i; simp)
  have hi : Function.Injective (smallFirstMap U V 0) :=
    (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap (smallSequence U V).f 0)).mp
      inferInstance
  intro a b hab
  apply (smallUnionEquiv U V hU hV 0).injective
  apply hi
  exact (middleEquiv U V 0).injective hab

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
