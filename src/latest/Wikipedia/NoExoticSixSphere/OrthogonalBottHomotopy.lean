import Wikipedia.NoExoticSixSphere.OrthogonalBottCubeComparison
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# The first Bott comparison on native higher homotopy classes

The map is induced by the actual minimum-exponential loop map, not a chosen
abstract bijection. Surjectivity and injectivity have the respective checked
parameter-dimension bounds. This is only the first comparison, not the full
orthogonal homotopy computation.
-/

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization

variable {n : ℕ}

noncomputable def bottHomotopyMap (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) :
    HomotopyGroup (Fin d) (OrthogonalComplexStructures.Space n) J₀ →
      HomotopyGroup (Fin d) (Path a a) (Path.refl a) :=
  HigherHomotopy.map (bottLoopMap a b hanti J₀) (bottLoopMap_base a b hanti J₀)

theorem bottHomotopyMap_surjective (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 2 < n) :
    Function.Surjective (bottHomotopyMap d a b hanti J₀) :=
  HigherHomotopy.map_surjective _ _ (bottLoopMap_injective a b hanti J₀)
    (exists_cube_bottLoopMap_representative d a b hanti J₀ hd)

theorem bottHomotopyMap_injective (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 3 < n) :
    Function.Injective (bottHomotopyMap d a b hanti J₀) :=
  HigherHomotopy.map_injective _ _ (fun f g S h ↦
    (cube_bottLoopMap_homotopicRel_iff d a b hanti J₀ hd f g S).mpr h)

noncomputable def bottHomotopyEquiv (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 3 < n) :
    HomotopyGroup (Fin d) (OrthogonalComplexStructures.Space n) J₀ ≃
      HomotopyGroup (Fin d) (Path a a) (Path.refl a) :=
  Equiv.ofBijective (bottHomotopyMap d a b hanti J₀)
    ⟨bottHomotopyMap_injective d a b hanti J₀ hd,
      bottHomotopyMap_surjective d a b hanti J₀ (by omega)⟩

noncomputable def bottHomotopyMulEquiv (d : ℕ) [NeZero d] (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 3 < n) :
    HomotopyGroup (Fin d) (OrthogonalComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin d) (Path a a) (Path.refl a) :=
  MulEquiv.ofBijective
    (HigherHomotopy.mapMonoidHom (bottLoopMap a b hanti J₀) (bottLoopMap_base a b hanti J₀))
    ⟨bottHomotopyMap_injective d a b hanti J₀ hd,
      bottHomotopyMap_surjective d a b hanti J₀ (by omega)⟩

end NoExoticSixSphere.OrthogonalPolygon
