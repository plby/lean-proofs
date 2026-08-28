import Wikipedia.HopfProblem.SingularMayerVietorisSmallChains
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Chain maps into the actual small-chain subcomplex

An ambient chain map whose values are small factors through the genuine
small-chain subcomplex. Its factorization is unique because the inclusion
is degreewise the inclusion of a submodule.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] (U V : Set X)

instance smallInclusion_mono : Mono (smallInclusion U V) :=
  HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).mpr (smallInclusion_f_injective U V n))

/-- Factor an actual ambient chain map through the actual small-chain subcomplex. -/
def liftToSmall {K : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ singularComplex X)
    (hf : ∀ n (c : K.X n), (f.f n).hom c ∈ smallChainSubmodule U V n) :
    K ⟶ smallComplex U V where
  f n := ModuleCat.ofHom ((f.f n).hom.codRestrict _ (hf n))
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun g : K.X i ⟶ Chains X j => g.hom c) (f.comm i j)

@[simp] theorem liftToSmall_f_val {K : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K ⟶ singularComplex X)
    (hf : ∀ n (c : K.X n), (f.f n).hom c ∈ smallChainSubmodule U V n)
    (n : ℕ) (c : K.X n) : ((liftToSmall U V f hf).f n c).1 = (f.f n).hom c := rfl

@[simp] theorem liftToSmall_inclusion {K : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K ⟶ singularComplex X)
    (hf : ∀ n (c : K.X n), (f.f n).hom c ∈ smallChainSubmodule U V n) :
    liftToSmall U V f hf ≫ smallInclusion U V = f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  rfl

theorem liftToSmall_unique {K : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K ⟶ singularComplex X)
    (hf : ∀ n (c : K.X n), (f.f n).hom c ∈ smallChainSubmodule U V n)
    (g : K ⟶ smallComplex U V) (hg : g ≫ smallInclusion U V = f) :
    g = liftToSmall U V f hf := by
  apply (cancel_mono (smallInclusion U V)).mp
  rw [hg, liftToSmall_inclusion]

end Wikipedia.HopfProblem.SingularMayerVietoris
