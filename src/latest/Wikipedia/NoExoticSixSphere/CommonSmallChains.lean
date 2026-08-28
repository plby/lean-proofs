import Wikipedia.NoExoticSixSphere.SingularChainRangeIntersection
import Wikipedia.NoExoticSixSphere.SingularSmallChainComparison

/-!
# Chains simultaneously small for two actual open covers

The intersection of two small singular subcomplexes has the same native
integral homology as the ambient singular set. A common subdivision
stage gives representatives, and support preservation of the original
subdivision homotopy gives injectivity. Native coefficient reduction
then proves the same statement with finite-cyclic coefficients.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- Simplices lying in a member of each of the two specified covers. -/
abbrev commonSmall : (singular X).Subcomplex :=
  (support U ⊔ support A) ⊓ (support V ⊔ support B)

/-- The original inclusion of the common small singular subcomplex. -/
abbrev commonSmallInclusion : (commonSmall U A V B : SSet) ⟶ singular X :=
  (commonSmall U A V B).ι

/-- The native common-small chain map, with the specified coefficient object. -/
abbrev commonSmallChainInclusion (R : ModuleCat.{0} ℤ) :=
  (SimplicialCoefficients.chains R).map (commonSmallInclusion U A V B)

/-- Common-small chains have precisely the intersection of the two original small-chain images. -/
theorem commonSmallInclusion_range (R : ModuleCat.{0} ℤ) (n : ℕ) :
    LinearMap.range ((commonSmallChainInclusion U A V B R).f n).hom =
      LinearMap.range
        (((SimplicialCoefficients.chains R).map (smallInclusion U A)).f n).hom ⊓
      LinearMap.range
        (((SimplicialCoefficients.chains R).map (smallInclusion V B)).f n).hom :=
  SimplicialCoefficients.chainImage_inf R (support U ⊔ support A) (support V ⊔ support B) n

/-- Integral native small-chain images equal the original simplex-support submodules. -/
theorem smallInclusion_integral_range (n : ℕ) :
    LinearMap.range
        (((SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (smallInclusion U A)).f n).hom =
      SingularMayerVietoris.smallChainSubmodule U A n := by
  have h := smallInclusion_range (ModuleCat.of ℤ ℤ) U A n
  change _ = LinearMap.range (inducedChain (SingularMayerVietoris.subtypeInclusion U) n) ⊔
    LinearMap.range (inducedChain (SingularMayerVietoris.subtypeInclusion A) n) at h
  exact h.trans (congrArg₂ (fun P Q => P ⊔ Q)
    (SingularMayerVietoris.subtypeInclusion_chain_range U n)
    (SingularMayerVietoris.subtypeInclusion_chain_range A n))

theorem commonSmallInclusion_integral_range (n : ℕ) :
    LinearMap.range ((commonSmallChainInclusion U A V B (ModuleCat.of ℤ ℤ)).f n).hom =
      SingularMayerVietoris.smallChainSubmodule U A n ⊓
        SingularMayerVietoris.smallChainSubmodule V B n :=
  (commonSmallInclusion_range U A V B (ModuleCat.of ℤ ℤ) n).trans
    (congrArg₂ (fun P Q => P ⊓ Q)
      (smallInclusion_integral_range U A n) (smallInclusion_integral_range V B n))

/-- One subdivision stage makes every later subdivision small for both covers. -/
theorem eventually_subdivision_commonSmall
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ)
    (n : ℕ) (c : Chains X n) :
    ∃ N : ℕ, ∀ k ≥ N, SingularMayerVietoris.subdivision X k n c ∈
      LinearMap.range ((commonSmallChainInclusion U A V B (ModuleCat.of ℤ ℤ)).f n).hom := by
  obtain ⟨N, hN⟩ :=
    SingularMayerVietoris.eventually_subdivision_mem_small U A hU hA hUA n c
  obtain ⟨M, hM⟩ :=
    SingularMayerVietoris.eventually_subdivision_mem_small V B hV hB hVB n c
  refine ⟨max N M, fun k hk => ?_⟩
  rw [commonSmallInclusion_integral_range]
  exact ⟨hN k ((le_max_left N M).trans hk), hM k ((le_max_right N M).trans hk)⟩

/-- The actual subdivision homotopy preserves simultaneous smallness. -/
theorem subdivisionHomotopy_mem_commonSmall (k n : ℕ) (c : Chains X n)
    (hc : c ∈
      LinearMap.range ((commonSmallChainInclusion U A V B (ModuleCat.of ℤ ℤ)).f n).hom) :
    SingularMayerVietoris.subdivisionHomotopy X k n c ∈
      LinearMap.range
        ((commonSmallChainInclusion U A V B (ModuleCat.of ℤ ℤ)).f (n + 1)).hom := by
  rw [commonSmallInclusion_integral_range] at hc ⊢
  exact ⟨SingularMayerVietoris.subdivisionHomotopy_mem_small U A k n c hc.1,
    SingularMayerVietoris.subdivisionHomotopy_mem_small V B k n c hc.2⟩

/-- The original common-small integral inclusion is a quasi-isomorphism. -/
theorem commonSmallInclusion_integral_quasiIso
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ) :
    QuasiIso (commonSmallChainInclusion U A V B (ModuleCat.of ℤ ℤ)) := by
  let f := commonSmallChainInclusion U A V B (ModuleCat.of ℤ ℤ)
  have hf (n : ℕ) : Function.Injective (f.f n).hom :=
    (ModuleCat.mono_iff_injective (f.f n)).mp inferInstance
  apply SingularMayerVietoris.ModuleHomology.quasiIso_of_injective_chain_conditions f hf
  · intro n c hc
    obtain ⟨k, hk⟩ := eventually_subdivision_commonSmall U A V B hU hA hUA hV hB hVB n c
    obtain ⟨z, hz⟩ := hk k le_rfl
    refine ⟨z, SingularMayerVietoris.subdivisionHomotopy X k n c, ?_⟩
    rw [hz]
    exact SingularMayerVietoris.subdivisionHomotopy_boundary_of_cycle k n c hc
  · intro n c hc b hb
    have hfc : ((singularComplex X).d n (n - 1)).hom ((f.f n).hom c) = 0 :=
      (congrArg (fun m => m.hom c) (f.comm n (n - 1))).trans
        ((congrArg (f.f (n - 1)).hom hc).trans ((f.f (n - 1)).hom.map_zero))
    obtain ⟨k, hk⟩ :=
      eventually_subdivision_commonSmall U A V B hU hA hUA hV hB hVB (n + 1) b
    obtain ⟨z, hz⟩ := hk k le_rfl
    obtain ⟨w, hw⟩ := subdivisionHomotopy_mem_commonSmall U A V B k n
      ((f.f n).hom c) ⟨c, rfl⟩
    refine ⟨z + w, hf n ?_⟩
    calc
      (f.f n).hom ((((commonSmall U A V B : SSet).chainComplex
          (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom (z + w)) =
          ((singularComplex X).d (n + 1) n).hom ((f.f (n + 1)).hom (z + w)) :=
        (congrArg (fun m => m.hom (z + w)) (f.comm (n + 1) n)).symm
      _ = ((singularComplex X).d (n + 1) n).hom
          (SingularMayerVietoris.subdivision X k (n + 1) b +
            SingularMayerVietoris.subdivisionHomotopy X k n ((f.f n).hom c)) := by
        rw [map_add, hz, hw]
      _ = (f.f n).hom c := by
        rw [map_add, SingularMayerVietoris.subdivision_boundary, hb,
          SingularMayerVietoris.subdivisionHomotopy_boundary_of_cycle k n _ hfc]
        abel

/-- The same original common-small inclusion is a quasi-isomorphism with finite coefficients. -/
theorem commonSmallInclusion_mod_quasiIso (p : ℕ) (hp : p ≠ 0)
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ) :
    QuasiIso (commonSmallChainInclusion U A V B (ModuleCat.of ℤ (ZMod p))) :=
  SimplicialCoefficients.map_mod_quasiIso_of_integral p hp (commonSmallInclusion U A V B)
    (commonSmallInclusion_integral_quasiIso U A V B hU hA hUA hV hB hVB)

end NoExoticSixSphere.SingularSubcomplex
