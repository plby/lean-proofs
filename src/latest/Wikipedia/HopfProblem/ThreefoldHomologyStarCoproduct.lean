import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproductChains
import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproductBiproduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# All-degree integral singular homology of a finite topological coproduct

The equivalence below is induced by the actual chain decomposition. Its
inverse is the finite sum of the actual continuous component inclusions.
Consequently it identifies each inclusion with its coordinate single and
identifies every map out of the coproduct with the sum of its restrictions.
These formulas also prove naturality for componentwise continuous maps.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

local instance singularHomologyFiniteBiproducts :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {ι : Type} [Fintype ι]
variable (X : ι → Type) [∀ i, TopologicalSpace (X i)]

/-- The actual all-degree integral singular homology of a finite disjoint union. -/
def sigmaHomologyEquiv (n : ℕ) :
    SingularHomology (Σ i, X i) n ≃ₗ[ℤ] (∀ i, SingularHomology (X i) n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (sigmaChainComplexIso X)).symm.toLinearEquiv.trans
      (homologyBiproductEquiv (fun i => singularComplex (X i)) n)

/-- The inverse is the sum of the homology maps of the literal inclusions. -/
theorem sigmaHomologyEquiv_symm_apply (n : ℕ) (a : ∀ i, SingularHomology (X i) n) :
    (sigmaHomologyEquiv X n).symm a =
      ∑ i, singularHomologyMap (sigmaInclusion X i) n (a i) := by
  change (HomologicalComplex.homologyMap (sigmaChainComplexMap X) n).hom
    ((homologyBiproductEquiv (fun i => singularComplex (X i)) n).symm a) = _
  exact homologyBiproductEquiv_desc n
    (fun i => singularChainMap (sigmaInclusion X i)) a

@[simp] theorem sigmaHomologyEquiv_symm_single [DecidableEq ι]
    (n : ℕ) (i : ι) (a : SingularHomology (X i) n) :
    (sigmaHomologyEquiv X n).symm (Pi.single i a) =
      singularHomologyMap (sigmaInclusion X i) n a := by
  rw [sigmaHomologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/-- Each actual continuous component inclusion is its standard coordinate single. -/
@[simp] theorem sigmaHomologyEquiv_inclusion [DecidableEq ι]
    (n : ℕ) (i : ι) (a : SingularHomology (X i) n) :
    sigmaHomologyEquiv X n (singularHomologyMap (sigmaInclusion X i) n a) =
      Pi.single i a := by
  apply (sigmaHomologyEquiv X n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sigmaHomologyEquiv_symm_single]

/-- Every class is the sum of its actual component classes. -/
theorem sigmaHomologyEquiv_decomposition (n : ℕ) (a : SingularHomology (Σ i, X i) n) :
    a = ∑ i, singularHomologyMap (sigmaInclusion X i) n (sigmaHomologyEquiv X n a i) := by
  have h := sigmaHomologyEquiv_symm_apply X n (sigmaHomologyEquiv X n a)
  rwa [LinearEquiv.symm_apply_apply] at h

variable {X} {Z : Type} [TopologicalSpace Z]

/-- Every actual map out of the coproduct is the sum of its restrictions on homology. -/
theorem sigmaHomologyEquiv_map_out_symm (f : C((Σ i, X i), Z)) (n : ℕ)
    (a : ∀ i, SingularHomology (X i) n) :
    singularHomologyMap f n ((sigmaHomologyEquiv X n).symm a) =
      ∑ i, singularHomologyMap (f.comp (sigmaInclusion X i)) n (a i) := by
  rw [sigmaHomologyEquiv_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (LinearMap.congr_fun (singularHomologyMap_comp (sigmaInclusion X i) f n)
    (a i)).symm

/-- The same formula on an arbitrary genuine homology class. -/
theorem sigmaHomologyEquiv_map_out (f : C((Σ i, X i), Z)) (n : ℕ)
    (a : SingularHomology (Σ i, X i) n) :
    singularHomologyMap f n a =
      ∑ i, singularHomologyMap (f.comp (sigmaInclusion X i)) n
        (sigmaHomologyEquiv X n a i) := by
  have h := sigmaHomologyEquiv_map_out_symm f n (sigmaHomologyEquiv X n a)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- The literal continuous map descended from the component maps. -/
def sigmaElimMap (f : ∀ i, C(X i, Z)) : C((Σ i, X i), Z) :=
  ContinuousMap.sigma f

omit [Fintype ι] in
@[simp] theorem sigmaElimMap_apply (f : ∀ i, C(X i, Z)) (i : ι) (x : X i) :
    sigmaElimMap f ⟨i, x⟩ = f i x := rfl

omit [Fintype ι] in
@[simp] theorem sigmaElimMap_comp_inclusion (f : ∀ i, C(X i, Z)) (i : ι) :
    (sigmaElimMap f).comp (sigmaInclusion X i) = f i := rfl

/-- Descent from actual continuous component maps gives their finite sum in homology. -/
theorem sigmaHomologyEquiv_sigmaElim_symm (f : ∀ i, C(X i, Z)) (n : ℕ)
    (a : ∀ i, SingularHomology (X i) n) :
    singularHomologyMap (sigmaElimMap f) n ((sigmaHomologyEquiv X n).symm a) =
      ∑ i, singularHomologyMap (f i) n (a i) := by
  simpa only [sigmaElimMap_comp_inclusion] using
    sigmaHomologyEquiv_map_out_symm (sigmaElimMap f) n a

theorem sigmaHomologyEquiv_sigmaElim (f : ∀ i, C(X i, Z)) (n : ℕ)
    (a : SingularHomology (Σ i, X i) n) :
    singularHomologyMap (sigmaElimMap f) n a =
      ∑ i, singularHomologyMap (f i) n (sigmaHomologyEquiv X n a i) := by
  simpa only [sigmaElimMap_comp_inclusion] using
    sigmaHomologyEquiv_map_out (sigmaElimMap f) n a

variable {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]

/-- The genuine continuous map of topological coproducts, acting componentwise. -/
def sigmaMap (f : ∀ i, C(X i, Y i)) : C((Σ i, X i), Σ i, Y i) :=
  sigmaElimMap fun i => (sigmaInclusion Y i).comp (f i)

omit [Fintype ι] in
@[simp] theorem sigmaMap_apply (f : ∀ i, C(X i, Y i)) (i : ι) (x : X i) :
    sigmaMap f ⟨i, x⟩ = ⟨i, f i x⟩ := rfl

omit [Fintype ι] in
@[simp] theorem sigmaMap_comp_inclusion (f : ∀ i, C(X i, Y i)) (i : ι) :
    (sigmaMap f).comp (sigmaInclusion X i) =
      (sigmaInclusion Y i).comp (f i) := rfl

/-- The disjoint-union homology coordinates are natural for actual component maps. -/
theorem sigmaHomologyEquiv_sigmaMap_symm (f : ∀ i, C(X i, Y i)) (n : ℕ)
    (a : ∀ i, SingularHomology (X i) n) :
    sigmaHomologyEquiv Y n
      (singularHomologyMap (sigmaMap f) n ((sigmaHomologyEquiv X n).symm a)) =
      fun i => singularHomologyMap (f i) n (a i) := by
  apply (sigmaHomologyEquiv Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sigmaHomologyEquiv_map_out_symm,
    sigmaHomologyEquiv_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.congr_fun (singularHomologyMap_comp (f i) (sigmaInclusion Y i) n)
    (a i)

theorem sigmaHomologyEquiv_sigmaMap (f : ∀ i, C(X i, Y i)) (n : ℕ)
    (a : SingularHomology (Σ i, X i) n) :
    sigmaHomologyEquiv Y n (singularHomologyMap (sigmaMap f) n a) =
      fun i => singularHomologyMap (f i) n (sigmaHomologyEquiv X n a i) := by
  have h := sigmaHomologyEquiv_sigmaMap_symm f n (sigmaHomologyEquiv X n a)
  rwa [LinearEquiv.symm_apply_apply] at h

omit [Fintype ι] in
/-- Actual component inclusions jointly detect linear maps out of coproduct homology. -/
theorem sigmaHomology_hom_ext [Finite ι] (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f g : SingularHomology (Σ i, X i) n →ₗ[ℤ] M)
    (h : ∀ i, f.comp (singularHomologyMap (sigmaInclusion X i) n) =
      g.comp (singularHomologyMap (sigmaInclusion X i) n)) : f = g := by
  let := Fintype.ofFinite ι
  apply LinearMap.ext
  intro a
  rw [sigmaHomologyEquiv_decomposition X n a, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.congr_fun (h i) (sigmaHomologyEquiv X n a i)

end Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct
