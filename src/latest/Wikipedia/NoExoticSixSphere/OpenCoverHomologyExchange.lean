import Wikipedia.HopfProblem.SingularMayerVietorisSmallEquivalence
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceAlgebra
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Cut-and-paste of actual maps on an open two-set cover

Four maps share their first pieces in pairs and exchange their second
pieces. On every small singular simplex their two diagonal sums agree.
The proved small-chain comparison transports this identity to actual
singular homology in every degree. No homology relation is assumed.
-/

noncomputable section

open Set Function CategoryTheory

namespace NoExoticSixSphere.OpenCoverExchange

open Wikipedia.HopfProblem.FirstHurewicz
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem inducedChain_eq_of_supported (f g : C(X, Y)) (U : Set X) (hfg : EqOn f g U)
    (n : ℕ) (c : Chains X n) (hc : c ∈ supportedChainSubmodule U n) :
    inducedChain f n c = inducedChain g n c := by
  have hle : supportedChainSubmodule U n ≤
      LinearMap.ker (inducedChain f n - inducedChain g n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change inducedChain f n (simplexChain X n σ) -
      inducedChain g n (simplexChain X n σ) = 0
    rw [inducedChain_simplex, inducedChain_simplex]
    have he : f.comp σ = g.comp σ := by
      apply ContinuousMap.ext
      intro x
      exact hfg (hσ ⟨x, rfl⟩)
    rw [he, sub_self]
  exact sub_eq_zero.mp (hle hc)

variable (f₀₀ f₀₁ f₁₀ f₁₁ : C(X, Y)) (U V : Set X)
  (hU₀ : EqOn f₀₀ f₀₁ U) (hU₁ : EqOn f₁₀ f₁₁ U)
  (hV₀ : EqOn f₀₀ f₁₀ V) (hV₁ : EqOn f₀₁ f₁₁ V)

include hU₀ hU₁ hV₀ hV₁

theorem inducedChain_exchange_of_small (n : ℕ) (c : Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) :
    inducedChain f₀₀ n c + inducedChain f₁₁ n c =
      inducedChain f₀₁ n c + inducedChain f₁₀ n c := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hc
  simp only [map_add]
  rw [inducedChain_eq_of_supported f₀₀ f₀₁ U hU₀ n u hu,
    inducedChain_eq_of_supported f₁₀ f₁₁ U hU₁ n u hu,
    inducedChain_eq_of_supported f₀₀ f₁₀ V hV₀ n v hv,
    inducedChain_eq_of_supported f₀₁ f₁₁ V hV₁ n v hv]
  abel

theorem smallChainMap_exchange :
    smallInclusion U V ≫ singularChainMap f₀₀ + smallInclusion U V ≫ singularChainMap f₁₁ =
      smallInclusion U V ≫ singularChainMap f₀₁ + smallInclusion U V ≫ singularChainMap f₁₀ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change inducedChain f₀₀ n c.val + inducedChain f₁₁ n c.val =
    inducedChain f₀₁ n c.val + inducedChain f₁₀ n c.val
  exact inducedChain_exchange_of_small f₀₀ f₀₁ f₁₀ f₁₁ U V hU₀ hU₁ hV₀ hV₁ n c.val c.property

theorem homologyMap_exchange (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (n : ℕ) :
    singularHomologyMap f₀₀ n + singularHomologyMap f₁₁ n =
      singularHomologyMap f₀₁ n + singularHomologyMap f₁₀ n := by
  have h := congrArg (fun F ↦ homologyLinearMap F n)
    (smallChainMap_exchange f₀₀ f₀₁ f₁₀ f₁₁ U V hU₀ hU₁ hV₀ hV₁)
  simp only [homologyLinearMap_add, homologyLinearMap_comp] at h
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (smallHomologyEquiv U V hU hV hcover n).surjective a
  have he := LinearMap.congr_fun h b
  change singularHomologyMap f₀₀ n (smallHomologyEquiv U V hU hV hcover n b) +
      singularHomologyMap f₁₁ n (smallHomologyEquiv U V hU hV hcover n b) =
    singularHomologyMap f₀₁ n (smallHomologyEquiv U V hU hV hcover n b) +
      singularHomologyMap f₁₀ n (smallHomologyEquiv U V hU hV hcover n b) at he
  simpa only [hb, LinearMap.add_apply] using he

end NoExoticSixSphere.OpenCoverExchange
