import Wikipedia.NoExoticSixSphere.ModTwoCochainComplex

/-!
# Mod-two cochains on an original integer chain complex

This is the integer enrichment of the existing additive dual complex.
It applies in particular to the actual relative singular complexes; no
cohomology group is replaced by a prescribed algebraic model.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.ModTwoDualComplex

local notation "CSC" => ConstantSheafSingularComparison.dualComplex

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The actual additive dual, equipped with its compatible integer scalars. -/
def complex : CochainComplex (ModuleCat.{0} ℤ) ℕ where
  X n := ModuleCat.of ℤ (K.X n →+ ZMod 2)
  d i j := ModuleCat.ofHom (ConstantSheafSingularComparison.addHomToIntLinearMap
    (ConstantSheafSingularComparison.dualDifferential K (AddCommGrpCat.of (ZMod 2)) i j))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply AddMonoidHom.ext
    intro c
    change α ((K.d j i).hom c) = 0
    rw [K.shape j i hij]
    exact α.map_zero
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply AddMonoidHom.ext
    intro c
    change α ((K.d j i).hom ((K.d k j).hom c)) = 0
    have he := congrArg (fun f : K.X k ⟶ K.X i => f.hom c) (K.d_comp_d k j i)
    exact (congrArg α he).trans α.map_zero

/-- Forgetting scalars recovers the original additive dual definitionally. -/
theorem forget_complex :
    ((forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (complex K) = CSC K (AddCommGrpCat.of (ZMod 2)) := rfl

/-- Specializing to singular chains gives the cap product's original cochains. -/
theorem complex_singular (X : Type) [TopologicalSpace X] :
    complex (singularComplex X) = ModTwoCapProduct.cochainComplex X := rfl

variable {K} {L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Literal precomposition by an original chain map. -/
def map (f : K ⟶ L) : complex L ⟶ complex K where
  f n := ModuleCat.ofHom (ConstantSheafSingularComparison.addHomToIntLinearMap
    ((ConstantSheafSingularComparison.dualMap (AddCommGrpCat.of (ZMod 2)) f).f n).hom)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change L.X i →+ ZMod 2 at α
    apply AddMonoidHom.ext
    intro c
    change α ((f.f i).hom ((K.d j i).hom c)) =
      α ((L.d j i).hom ((f.f j).hom c))
    exact congrArg α (congrArg (fun g : K.X j ⟶ L.X i => g.hom c) (f.comm j i).symm)

theorem map_apply (f : K ⟶ L) (n : ℕ) (α : L.X n →+ ZMod 2) :
    ((map f).f n).hom α = α.comp (f.f n).hom.toAddMonoidHom := rfl

end NoExoticSixSphere.ModTwoDualComplex
