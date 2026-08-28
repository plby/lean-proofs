import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation

/-!
# Original coefficient change on actual simplex summands

The native coefficient functor applies the given coefficient map to
each original coproduct summand. In particular, reduction sends the
original integral simplex generator to the same native simplex with
coefficient one.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients

namespace NoExoticSixSphere.CoefficientChains

variable {A B : ModuleCat.{0} ℤ} {X : Type} [TopologicalSpace X]

/-- Native coefficient change retains the actual simplex and changes only its coefficient. -/
theorem coefficientMap_simplex (f : A ⟶ B) (n : ℕ) (σ : SingularSimplex X n) (a : A) :
    ((coefficientComplexMap f X).f n).hom (simplex A X n σ a) =
      simplex B X n σ (f.hom a) := by
  have he := Sigma.ι_map
    (fun _ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ => f) (simplexIndex X n σ)
  exact congrArg (fun g => g.hom a) he

/-- Integral simplex generators reduce to their original native coefficient summands. -/
theorem reduction_simplex (p n : ℕ) (σ : SingularSimplex X n) :
    ((reductionChainMap p X).f n).hom (simplexChain X n σ) =
      simplex (ModuleCat.of ℤ (ZMod p)) X n σ 1 := by
  have he := coefficientMap_simplex (reductionCoefficient p) n σ 1
  have hone : (reductionCoefficient p).hom (1 : ℤ) = (1 : ZMod p) := by
    change ((1 : ℤ) : ZMod p) = 1
    exact Int.cast_one
  exact he.trans (congrArg (simplex (ModuleCat.of ℤ (ZMod p)) X n σ) hone)

end NoExoticSixSphere.CoefficientChains
