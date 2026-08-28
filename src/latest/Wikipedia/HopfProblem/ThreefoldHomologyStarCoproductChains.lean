import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Actual singular chains of a finite disjoint union

Every singular simplex in a topological coproduct lies in one component.
The resulting simplex decomposition gives mutually inverse chain maps
between the actual singular complex and the finite categorical biproduct
of the component complexes. The map from the biproduct is literally the
map induced by the continuous component inclusions.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

open FirstHurewicz SingularMayerVietoris

local instance singularChainsFiniteBiproducts :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {ι : Type} (X : ι → Type) [∀ i, TopologicalSpace (X i)]

/-- The actual continuous inclusion of one component in the topological coproduct. -/
def sigmaInclusion (i : ι) : C(X i, Σ i, X i) :=
  ⟨Sigma.mk i, continuous_sigmaMk⟩

@[simp] theorem sigmaInclusion_apply (i : ι) (x : X i) :
    sigmaInclusion X i x = Sigma.mk i x := rfl

/-- A genuine singular simplex of a disjoint union lies in one summand. -/
theorem singularSimplex_sigma_split (n : ℕ) (σ : SingularSimplex (Σ i, X i) n) :
    ∃ (i : ι) (τ : SingularSimplex (X i) n), σ = (sigmaInclusion X i).comp τ := by
  obtain ⟨i, g, hg, heq⟩ := σ.continuous.exists_lift_sigma
  exact ⟨i, ⟨g, hg⟩, ContinuousMap.ext (congrFun heq)⟩

/-- Include a simplex of a component into the topological coproduct. -/
def sigmaSimplexMap (n : ℕ) :
    (Σ i, SingularSimplex (X i) n) → SingularSimplex (Σ i, X i) n :=
  fun σ => (sigmaInclusion X σ.1).comp σ.2

theorem sigmaSimplexMap_injective (n : ℕ) :
    Function.Injective (sigmaSimplexMap X n) := by
  classical
  let z : stdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  rintro ⟨i, σ⟩ ⟨j, τ⟩ h
  have hij : i = j := congrArg (fun f => (f z).1) h
  subst j
  congr 1
  exact ContinuousMap.ext fun t => sigma_mk_injective (congrArg (fun f => f t) h)

theorem sigmaSimplexMap_surjective (n : ℕ) :
    Function.Surjective (sigmaSimplexMap X n) := by
  intro σ
  obtain ⟨i, τ, hτ⟩ := singularSimplex_sigma_split X n σ
  exact ⟨⟨i, τ⟩, hτ.symm⟩

/-- The actual simplex set of a coproduct is the coproduct of the simplex sets. -/
def sigmaSimplexEquiv (n : ℕ) :
    (Σ i, SingularSimplex (X i) n) ≃ SingularSimplex (Σ i, X i) n :=
  Equiv.ofBijective (sigmaSimplexMap X n)
    ⟨sigmaSimplexMap_injective X n, sigmaSimplexMap_surjective X n⟩

@[simp] theorem sigmaSimplexEquiv_mk (n : ℕ) (i : ι)
    (σ : SingularSimplex (X i) n) :
    sigmaSimplexEquiv X n ⟨i, σ⟩ = (sigmaInclusion X i).comp σ := rfl

@[simp] theorem sigmaSimplexEquiv_symm_inclusion (n : ℕ) (i : ι)
    (σ : SingularSimplex (X i) n) :
    (sigmaSimplexEquiv X n).symm ((sigmaInclusion X i).comp σ) = ⟨i, σ⟩ :=
  (sigmaSimplexEquiv X n).symm_apply_apply ⟨i, σ⟩

/-- Actual component chain inclusions jointly detect maps out of coproduct chains. -/
theorem sigmaChains_hom_ext (n : ℕ) {M : ModuleCat ℤ}
    (f g : Chains (Σ i, X i) n ⟶ M)
    (h : ∀ i, (singularChainMap (sigmaInclusion X i)).f n ≫ f =
      (singularChainMap (sigmaInclusion X i)).f n ≫ g) : f = g := by
  apply ModuleCat.hom_ext
  apply chainMap_ext (Σ i, X i) n
  intro σ
  obtain ⟨i, τ, rfl⟩ := singularSimplex_sigma_split X n σ
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, inducedChain_simplex]
    using congrArg (fun k => k.hom (simplexChain (X i) n τ)) (h i)

variable [Fintype ι]

/-- The chain map given by all the actual continuous component inclusions. -/
def sigmaChainComplexMap :
    (⨁ fun i => singularComplex (X i)) ⟶ singularComplex (Σ i, X i) :=
  biproduct.desc fun i => singularChainMap (sigmaInclusion X i)

@[simp] theorem sigmaChainComplexMap_inclusion (i : ι) :
    biproduct.ι (fun i => singularComplex (X i)) i ≫ sigmaChainComplexMap X =
      singularChainMap (sigmaInclusion X i) :=
  biproduct.ι_desc _ i

private def sigmaChainInverseDegree (n : ℕ) :
    Chains (Σ i, X i) n →ₗ[ℤ] (⨁ fun i => singularComplex (X i)).X n :=
  chainLift (Σ i, X i) n fun σ =>
    let τ := (sigmaSimplexEquiv X n).symm σ
    ((biproduct.ι (fun i => singularComplex (X i)) τ.1).f n).hom
      (simplexChain (X τ.1) n τ.2)

private theorem sigmaChainInverseDegree_inclusion (n : ℕ) (i : ι)
    (σ : SingularSimplex (X i) n) :
    sigmaChainInverseDegree X n
        (simplexChain (Σ i, X i) n ((sigmaInclusion X i).comp σ)) =
      ((biproduct.ι (fun i => singularComplex (X i)) i).f n).hom
        (simplexChain (X i) n σ) := by
  simpa only [sigmaChainInverseDegree, chainLift_simplex] using
    congrArg (fun τ : Σ i, SingularSimplex (X i) n =>
      ((biproduct.ι (fun i => singularComplex (X i)) τ.1).f n).hom
        (simplexChain (X τ.1) n τ.2)) (sigmaSimplexEquiv_symm_inclusion X n i σ)

private theorem sigmaChainInverseDegree_comp_inclusion (n : ℕ) (i : ι) :
    (singularChainMap (sigmaInclusion X i)).f n ≫
        ModuleCat.ofHom (sigmaChainInverseDegree X n) =
      (biproduct.ι (fun i => singularComplex (X i)) i).f n := by
  apply ModuleCat.hom_ext
  apply chainMap_ext (X i) n
  intro σ
  change sigmaChainInverseDegree X n
    (inducedChain (sigmaInclusion X i) n (simplexChain (X i) n σ)) = _
  rw [inducedChain_simplex, sigmaChainInverseDegree_inclusion]

/-- The genuine chain inverse, obtained by locating each simplex in its component. -/
def sigmaChainComplexInverse :
    singularComplex (Σ i, X i) ⟶ (⨁ fun i => singularComplex (X i)) where
  f n := ModuleCat.ofHom (sigmaChainInverseDegree X n)
  comm' n m _ := by
    apply sigmaChains_hom_ext X n
    intro i
    calc
      _ = ((singularChainMap (sigmaInclusion X i)).f n ≫
          ModuleCat.ofHom (sigmaChainInverseDegree X n)) ≫
            (⨁ fun i => singularComplex (X i)).d n m := (Category.assoc _ _ _).symm
      _ = (biproduct.ι (fun i => singularComplex (X i)) i).f n ≫
          (⨁ fun i => singularComplex (X i)).d n m :=
        congrArg (fun f : Chains (X i) n ⟶ (⨁ fun i => singularComplex (X i)).X n =>
          f ≫ (⨁ fun i => singularComplex (X i)).d n m)
          (sigmaChainInverseDegree_comp_inclusion X n i)
      _ = (singularComplex (X i)).d n m ≫
          (biproduct.ι (fun i => singularComplex (X i)) i).f m :=
        (biproduct.ι (fun i => singularComplex (X i)) i).comm n m
      _ = (singularComplex (X i)).d n m ≫
          ((singularChainMap (sigmaInclusion X i)).f m ≫
            ModuleCat.ofHom (sigmaChainInverseDegree X m)) :=
        (congrArg (fun f : Chains (X i) m ⟶ (⨁ fun i => singularComplex (X i)).X m =>
          (singularComplex (X i)).d n m ≫ f)
          (sigmaChainInverseDegree_comp_inclusion X m i)).symm
      _ = ((singularComplex (X i)).d n m ≫
          (singularChainMap (sigmaInclusion X i)).f m) ≫
            ModuleCat.ofHom (sigmaChainInverseDegree X m) := (Category.assoc _ _ _).symm
      _ = ((singularChainMap (sigmaInclusion X i)).f n ≫
          (singularComplex (Σ i, X i)).d n m) ≫
            ModuleCat.ofHom (sigmaChainInverseDegree X m) :=
        congrArg (fun f : Chains (X i) n ⟶ Chains (Σ i, X i) m =>
          f ≫ ModuleCat.ofHom (sigmaChainInverseDegree X m))
          ((singularChainMap (sigmaInclusion X i)).comm n m).symm
      _ = _ := Category.assoc _ _ _

@[simp] theorem sigmaChainComplexInverse_inclusion (i : ι) :
    singularChainMap (sigmaInclusion X i) ≫ sigmaChainComplexInverse X =
      biproduct.ι (fun i => singularComplex (X i)) i := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact sigmaChainInverseDegree_comp_inclusion X n i

theorem sigmaChainComplexMap_comp_inverse :
    sigmaChainComplexMap X ≫ sigmaChainComplexInverse X =
      𝟙 (⨁ fun i => singularComplex (X i)) := by
  apply biproduct.hom_ext'
  intro i
  rw [← Category.assoc, sigmaChainComplexMap_inclusion,
    sigmaChainComplexInverse_inclusion, Category.comp_id]

theorem sigmaChainComplexInverse_comp_map :
    sigmaChainComplexInverse X ≫ sigmaChainComplexMap X =
      𝟙 (singularComplex (Σ i, X i)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply sigmaChains_hom_ext X n
  intro i
  have h : singularChainMap (sigmaInclusion X i) ≫
      (sigmaChainComplexInverse X ≫ sigmaChainComplexMap X) =
        singularChainMap (sigmaInclusion X i) := by
    rw [← Category.assoc, sigmaChainComplexInverse_inclusion,
      sigmaChainComplexMap_inclusion]
  exact (congrArg (fun f => f.f n) h).trans (Category.comp_id _).symm

/-- The actual singular chain complex of a finite disjoint union. -/
def sigmaChainComplexIso :
    (⨁ fun i => singularComplex (X i)) ≅ singularComplex (Σ i, X i) where
  hom := sigmaChainComplexMap X
  inv := sigmaChainComplexInverse X
  hom_inv_id := sigmaChainComplexMap_comp_inverse X
  inv_hom_id := sigmaChainComplexInverse_comp_map X

@[simp] theorem sigmaChainComplexIso_hom :
    (sigmaChainComplexIso X).hom = sigmaChainComplexMap X := rfl

@[simp] theorem sigmaChainComplexIso_inv :
    (sigmaChainComplexIso X).inv = sigmaChainComplexInverse X := rfl

end Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct
