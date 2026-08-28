import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsMaps
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsInclusions

/-!
# The two maps into small singular chains

The actual singular-chain maps of the two subtype inclusions factor through
the small-chain subcomplex. Their images jointly generate that subcomplex.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] (U V : Set X)

theorem subtypeInclusion_chain_mem (n : ℕ) (c : Chains U n) :
    inducedChain (subtypeInclusion U) n c ∈ supportedChainSubmodule U n := by
  rw [← subtypeInclusion_chain_range U n]
  exact ⟨c, rfl⟩

/-- The actual map from the left subspace into the small-chain complex. -/
def toSmallLeft : singularComplex U ⟶ smallComplex U V :=
  liftToSmall U V (singularChainMap (subtypeInclusion U)) (fun n c =>
    (show supportedChainSubmodule U n ≤ smallChainSubmodule U V n from le_sup_left)
      (subtypeInclusion_chain_mem U n c))

/-- The actual map from the right subspace into the small-chain complex. -/
def toSmallRight : singularComplex V ⟶ smallComplex U V :=
  liftToSmall U V (singularChainMap (subtypeInclusion V)) (fun n c =>
    (show supportedChainSubmodule V n ≤ smallChainSubmodule U V n from le_sup_right)
      (subtypeInclusion_chain_mem V n c))

@[simp] theorem toSmallLeft_f_val (n : ℕ) (c : Chains U n) :
    ((toSmallLeft U V).f n c).1 = inducedChain (subtypeInclusion U) n c := rfl

@[simp] theorem toSmallRight_f_val (n : ℕ) (c : Chains V n) :
    ((toSmallRight U V).f n c).1 = inducedChain (subtypeInclusion V) n c := rfl

@[simp] theorem toSmallLeft_inclusion :
    toSmallLeft U V ≫ smallInclusion U V = singularChainMap (subtypeInclusion U) :=
  liftToSmall_inclusion U V _ _

@[simp] theorem toSmallRight_inclusion :
    toSmallRight U V ≫ smallInclusion U V = singularChainMap (subtypeInclusion V) :=
  liftToSmall_inclusion U V _ _

/-- Every small chain is a sum of chains from the two actual subspaces. -/
theorem toSmall_jointly_surjective (n : ℕ) (s : (smallComplex U V).X n) :
    ∃ x : Chains U n, ∃ y : Chains V n,
      ((toSmallLeft U V).f n).hom x + ((toSmallRight U V).f n).hom y = s := by
  obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp s.2
  rw [← subtypeInclusion_chain_range U n] at hc
  rw [← subtypeInclusion_chain_range V n] at hd
  obtain ⟨x, hx⟩ := hc
  obtain ⟨y, hy⟩ := hd
  refine ⟨x, y, ?_⟩
  apply Subtype.ext
  change inducedChain (subtypeInclusion U) n x +
    inducedChain (subtypeInclusion V) n y = s.1
  rw [hx, hy]
  exact hcd

end Wikipedia.HopfProblem.SingularMayerVietoris
