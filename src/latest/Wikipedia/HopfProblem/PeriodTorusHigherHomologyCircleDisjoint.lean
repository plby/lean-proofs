import Wikipedia.HopfProblem.SingularMayerVietorisSequence
import Mathlib.Topology.Connected.Clopen

/-!
# Integral singular homology of a disjoint union

A singular simplex in a topological sum lies in exactly one summand, because
the standard simplex is connected and nonempty. Consequently the actual
chain map induced by the two inclusions is an isomorphism from the biproduct
of the actual singular chain complexes. Applying homology gives the
all-degree disjoint-union equivalence, with its actual inclusion maps.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual left inclusion into a topological sum. -/
def sumInlMap : C(X, X ⊕ Y) := ⟨Sum.inl, continuous_inl⟩

/-- The actual right inclusion into a topological sum. -/
def sumInrMap : C(Y, X ⊕ Y) := ⟨Sum.inr, continuous_inr⟩

/-- The universal continuous map out of a topological sum. -/
def sumElimMap {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Z)) (g : C(Y, Z)) : C(X ⊕ Y, Z) :=
  ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩

/-- Every singular simplex of a sum lies in one of its two summands. -/
theorem singularSimplex_sum_split (n : ℕ) (σ : SingularSimplex (X ⊕ Y) n) :
    (∃ τ : SingularSimplex X n, σ = (sumInlMap X Y).comp τ) ∨
      (∃ τ : SingularSimplex Y n, σ = (sumInrMap X Y).comp τ) := by
  rcases Sum.isConnected_iff.mp (isConnected_range σ.continuous) with
    ⟨s, _, hs⟩ | ⟨s, _, hs⟩
  · have hr : Set.range σ ⊆ Set.range (Sum.inl : X → X ⊕ Y) :=
      hs.trans_subset (Set.image_subset_range _ _)
    obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.mp hr
    have hc : Continuous g :=
      Topology.IsEmbedding.inl.continuous_iff.mpr (hg ▸ σ.continuous)
    exact Or.inl ⟨⟨g, hc⟩, ContinuousMap.ext (congrFun hg)⟩
  · have hr : Set.range σ ⊆ Set.range (Sum.inr : Y → X ⊕ Y) :=
      hs.trans_subset (Set.image_subset_range _ _)
    obtain ⟨g, hg⟩ := Set.range_subset_range_iff_exists_comp.mp hr
    have hc : Continuous g :=
      Topology.IsEmbedding.inr.continuous_iff.mpr (hg ▸ σ.continuous)
    exact Or.inr ⟨⟨g, hc⟩, ContinuousMap.ext (congrFun hg)⟩

/-- Map each simplex of a summand into the topological sum. -/
def sumSimplexMap (n : ℕ) :
    SingularSimplex X n ⊕ SingularSimplex Y n → SingularSimplex (X ⊕ Y) n :=
  Sum.elim ((sumInlMap X Y).comp) ((sumInrMap X Y).comp)

theorem sumSimplexMap_injective (n : ℕ) :
    Function.Injective (sumSimplexMap X Y n) := by
  classical
  let z : stdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  intro σ τ h
  cases σ with
  | inl σ =>
    cases τ with
    | inl τ =>
      congr 1
      exact ContinuousMap.ext fun t => Sum.inl.inj (congrArg (fun f => f t) h)
    | inr τ =>
      exact False.elim (Sum.inl_ne_inr (congrArg (fun f => f z) h))
  | inr σ =>
    cases τ with
    | inl τ =>
      exact False.elim (Sum.inr_ne_inl (congrArg (fun f => f z) h))
    | inr τ =>
      congr 1
      exact ContinuousMap.ext fun t => Sum.inr.inj (congrArg (fun f => f t) h)

theorem sumSimplexMap_surjective (n : ℕ) :
    Function.Surjective (sumSimplexMap X Y n) := by
  intro σ
  rcases singularSimplex_sum_split X Y n σ with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
  · exact ⟨Sum.inl τ, hτ.symm⟩
  · exact ⟨Sum.inr τ, hτ.symm⟩

/-- The genuine simplex set of a disjoint union is the sum of the two simplex sets. -/
def sumSimplexEquiv (n : ℕ) :
    SingularSimplex X n ⊕ SingularSimplex Y n ≃ SingularSimplex (X ⊕ Y) n :=
  Equiv.ofBijective (sumSimplexMap X Y n)
    ⟨sumSimplexMap_injective X Y n, sumSimplexMap_surjective X Y n⟩

@[simp] theorem sumSimplexEquiv_inl (n : ℕ) (σ : SingularSimplex X n) :
    sumSimplexEquiv X Y n (Sum.inl σ) = (sumInlMap X Y).comp σ := rfl

@[simp] theorem sumSimplexEquiv_inr (n : ℕ) (σ : SingularSimplex Y n) :
    sumSimplexEquiv X Y n (Sum.inr σ) = (sumInrMap X Y).comp σ := rfl

@[simp] theorem sumSimplexEquiv_symm_inl (n : ℕ) (σ : SingularSimplex X n) :
    (sumSimplexEquiv X Y n).symm ((sumInlMap X Y).comp σ) = Sum.inl σ :=
  (sumSimplexEquiv X Y n).symm_apply_apply (Sum.inl σ)

@[simp] theorem sumSimplexEquiv_symm_inr (n : ℕ) (σ : SingularSimplex Y n) :
    (sumSimplexEquiv X Y n).symm ((sumInrMap X Y).comp σ) = Sum.inr σ :=
  (sumSimplexEquiv X Y n).symm_apply_apply (Sum.inr σ)

/-- The actual chain map given by the two topological-sum inclusions. -/
def sumChainComplexMap :
    singularComplex X ⊞ singularComplex Y ⟶ singularComplex (X ⊕ Y) :=
  biprod.desc (singularChainMap (sumInlMap X Y)) (singularChainMap (sumInrMap X Y))

private def sumChainInverseDegree (n : ℕ) :
    Chains (X ⊕ Y) n →ₗ[ℤ] (singularComplex X ⊞ singularComplex Y).X n :=
  chainLift (X ⊕ Y) n fun σ =>
    Sum.elim
      (fun τ => (biprod.inl : singularComplex X ⟶
        singularComplex X ⊞ singularComplex Y).f n |>.hom (simplexChain X n τ))
      (fun τ => (biprod.inr : singularComplex Y ⟶
        singularComplex X ⊞ singularComplex Y).f n |>.hom (simplexChain Y n τ))
      ((sumSimplexEquiv X Y n).symm σ)

private theorem sumChainInverseDegree_inl (n : ℕ) (σ : SingularSimplex X n) :
    sumChainInverseDegree X Y n
        (simplexChain (X ⊕ Y) n ((sumInlMap X Y).comp σ)) =
      ((biprod.inl : singularComplex X ⟶
        singularComplex X ⊞ singularComplex Y).f n).hom (simplexChain X n σ) := by
  simp only [sumChainInverseDegree, chainLift_simplex, sumSimplexEquiv_symm_inl,
    Sum.elim_inl]

private theorem sumChainInverseDegree_inr (n : ℕ) (σ : SingularSimplex Y n) :
    sumChainInverseDegree X Y n
        (simplexChain (X ⊕ Y) n ((sumInrMap X Y).comp σ)) =
      ((biprod.inr : singularComplex Y ⟶
        singularComplex X ⊞ singularComplex Y).f n).hom (simplexChain Y n σ) := by
  simp only [sumChainInverseDegree, chainLift_simplex, sumSimplexEquiv_symm_inr,
    Sum.elim_inr]

private theorem sumChainComplexMap_comp_inverse (n : ℕ) :
    (sumChainComplexMap X Y).f n ≫ ModuleCat.ofHom (sumChainInverseDegree X Y n) =
      𝟙 ((singularComplex X ⊞ singularComplex Y).X n) := by
  apply HomologicalComplex.biprodX_ext_from
  · calc
      _ = ((biprod.inl : singularComplex X ⟶ singularComplex X ⊞
          singularComplex Y).f n ≫ (sumChainComplexMap X Y).f n) ≫
            ModuleCat.ofHom (sumChainInverseDegree X Y n) := (Category.assoc _ _ _).symm
      _ = (singularChainMap (sumInlMap X Y)).f n ≫
          ModuleCat.ofHom (sumChainInverseDegree X Y n) :=
        congrArg (fun f : Chains X n ⟶ Chains (X ⊕ Y) n =>
          f ≫ ModuleCat.ofHom (sumChainInverseDegree X Y n))
          (HomologicalComplex.biprod_inl_desc_f
            (singularChainMap (sumInlMap X Y)) (singularChainMap (sumInrMap X Y)) n)
      _ = _ := by
        apply ModuleCat.hom_ext
        apply chainMap_ext X n
        intro σ
        change sumChainInverseDegree X Y n
          (inducedChain (sumInlMap X Y) n (simplexChain X n σ)) = _
        rw [inducedChain_simplex, sumChainInverseDegree_inl, Category.comp_id]
  · calc
      _ = ((biprod.inr : singularComplex Y ⟶ singularComplex X ⊞
          singularComplex Y).f n ≫ (sumChainComplexMap X Y).f n) ≫
            ModuleCat.ofHom (sumChainInverseDegree X Y n) := (Category.assoc _ _ _).symm
      _ = (singularChainMap (sumInrMap X Y)).f n ≫
          ModuleCat.ofHom (sumChainInverseDegree X Y n) :=
        congrArg (fun f : Chains Y n ⟶ Chains (X ⊕ Y) n =>
          f ≫ ModuleCat.ofHom (sumChainInverseDegree X Y n))
          (HomologicalComplex.biprod_inr_desc_f
            (singularChainMap (sumInlMap X Y)) (singularChainMap (sumInrMap X Y)) n)
      _ = _ := by
        apply ModuleCat.hom_ext
        apply chainMap_ext Y n
        intro σ
        change sumChainInverseDegree X Y n
          (inducedChain (sumInrMap X Y) n (simplexChain Y n σ)) = _
        rw [inducedChain_simplex, sumChainInverseDegree_inr, Category.comp_id]

private theorem sumChainInverse_comp_map (n : ℕ) :
    ModuleCat.ofHom (sumChainInverseDegree X Y n) ≫ (sumChainComplexMap X Y).f n =
      𝟙 (Chains (X ⊕ Y) n) := by
  apply ModuleCat.hom_ext
  apply chainMap_ext (X ⊕ Y) n
  intro σ
  rcases singularSimplex_sum_split X Y n σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · change ((sumChainComplexMap X Y).f n).hom
      (sumChainInverseDegree X Y n
        (simplexChain (X ⊕ Y) n ((sumInlMap X Y).comp τ))) = _
    rw [sumChainInverseDegree_inl]
    exact (congrArg (fun f => f.hom (simplexChain X n τ))
      (HomologicalComplex.biprod_inl_desc_f
        (singularChainMap (sumInlMap X Y))
        (singularChainMap (sumInrMap X Y)) n)).trans
      (inducedChain_simplex (sumInlMap X Y) n τ)
  · change ((sumChainComplexMap X Y).f n).hom
      (sumChainInverseDegree X Y n
        (simplexChain (X ⊕ Y) n ((sumInrMap X Y).comp τ))) = _
    rw [sumChainInverseDegree_inr]
    exact (congrArg (fun f => f.hom (simplexChain Y n τ))
      (HomologicalComplex.biprod_inr_desc_f
        (singularChainMap (sumInlMap X Y))
        (singularChainMap (sumInrMap X Y)) n)).trans
      (inducedChain_simplex (sumInrMap X Y) n τ)

private theorem sumChainComplexMap_component_isIso (n : ℕ) :
    IsIso ((sumChainComplexMap X Y).f n) :=
  ⟨⟨ModuleCat.ofHom (sumChainInverseDegree X Y n),
    sumChainComplexMap_comp_inverse X Y n, sumChainInverse_comp_map X Y n⟩⟩

/-- Actual singular chains preserve a binary topological disjoint union. -/
def sumChainComplexIso :
    singularComplex X ⊞ singularComplex Y ≅ singularComplex (X ⊕ Y) := by
  letI (n : ℕ) : IsIso ((sumChainComplexMap X Y).f n) :=
    sumChainComplexMap_component_isIso X Y n
  letI : IsIso (sumChainComplexMap X Y) :=
    HomologicalComplex.Hom.isIso_of_components (sumChainComplexMap X Y)
  exact asIso (sumChainComplexMap X Y)

@[simp] theorem sumChainComplexIso_hom :
    (sumChainComplexIso X Y).hom = sumChainComplexMap X Y := rfl

/-- The actual all-degree integral singular homology of a disjoint union. -/
def sumHomologyEquiv (n : ℕ) :
    SingularHomology (X ⊕ Y) n ≃ₗ[ℤ] (SingularHomology X n × SingularHomology Y n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (sumChainComplexIso X Y)).symm.toLinearEquiv.trans
      (homologyBiprodEquiv (singularComplex X) (singularComplex Y) n)

/-- The inverse is the sum of the actual maps induced by the two inclusions. -/
theorem sumHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology X n × SingularHomology Y n) :
    (sumHomologyEquiv X Y n).symm a =
      singularHomologyMap (sumInlMap X Y) n a.1 +
        singularHomologyMap (sumInrMap X Y) n a.2 := by
  change (HomologicalComplex.homologyMap (sumChainComplexMap X Y) n).hom
    ((homologyBiprodEquiv (singularComplex X) (singularComplex Y) n).symm a) = _
  exact homologyBiprodEquiv_desc n
    (singularChainMap (sumInlMap X Y)) (singularChainMap (sumInrMap X Y)) a

@[simp] theorem sumHomologyEquiv_inl (n : ℕ) (a : SingularHomology X n) :
    sumHomologyEquiv X Y n (singularHomologyMap (sumInlMap X Y) n a) = (a, 0) := by
  apply (sumHomologyEquiv X Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sumHomologyEquiv_symm_apply, map_zero, add_zero]

@[simp] theorem sumHomologyEquiv_inr (n : ℕ) (a : SingularHomology Y n) :
    sumHomologyEquiv X Y n (singularHomologyMap (sumInrMap X Y) n a) = (0, a) := by
  apply (sumHomologyEquiv X Y n).symm.injective
  rw [LinearEquiv.symm_apply_apply, sumHomologyEquiv_symm_apply, map_zero, zero_add]

@[simp] theorem sumHomologyEquiv_symm_inl (n : ℕ) (a : SingularHomology X n) :
    (sumHomologyEquiv X Y n).symm (a, 0) =
      singularHomologyMap (sumInlMap X Y) n a := by
  rw [sumHomologyEquiv_symm_apply, map_zero, add_zero]

@[simp] theorem sumHomologyEquiv_symm_inr (n : ℕ) (a : SingularHomology Y n) :
    (sumHomologyEquiv X Y n).symm (0, a) =
      singularHomologyMap (sumInrMap X Y) n a := by
  rw [sumHomologyEquiv_symm_apply, map_zero, zero_add]

variable {X Y} {Z : Type} [TopologicalSpace Z]

private theorem sumElim_homology_inl (f : C(X, Z)) (g : C(Y, Z))
    (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap (sumElimMap f g) n
      (singularHomologyMap (sumInlMap X Y) n a) = singularHomologyMap f n a := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom (sumInlMap X Y))
      (TopCat.ofHom (sumElimMap f g))
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a).symm

private theorem sumElim_homology_inr (f : C(X, Z)) (g : C(Y, Z))
    (n : ℕ) (a : SingularHomology Y n) :
    singularHomologyMap (sumElimMap f g) n
      (singularHomologyMap (sumInrMap X Y) n a) = singularHomologyMap g n a := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom (sumInrMap X Y))
      (TopCat.ofHom (sumElimMap f g))
  exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a).symm

private theorem disjointHomology_id_apply (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap (ContinuousMap.id X) n a = a := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map_id (TopCat.of X)
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) a

/-- Any actual map from a disjoint union acts by the sum of its two induced maps. -/
theorem sumHomologyEquiv_sumElim_symm (f : C(X, Z)) (g : C(Y, Z)) (n : ℕ)
    (a : SingularHomology X n × SingularHomology Y n) :
    singularHomologyMap (sumElimMap f g) n ((sumHomologyEquiv X Y n).symm a) =
      singularHomologyMap f n a.1 + singularHomologyMap g n a.2 := by
  rw [sumHomologyEquiv_symm_apply, map_add, sumElim_homology_inl, sumElim_homology_inr]

/-- The universal map out of a topological sum, expressed in actual homology coordinates. -/
theorem sumHomologyEquiv_sumElim (f : C(X, Z)) (g : C(Y, Z)) (n : ℕ)
    (a : SingularHomology (X ⊕ Y) n) :
    singularHomologyMap (sumElimMap f g) n a =
      singularHomologyMap f n (sumHomologyEquiv X Y n a).1 +
        singularHomologyMap g n (sumHomologyEquiv X Y n a).2 := by
  have h := sumHomologyEquiv_sumElim_symm f g n (sumHomologyEquiv X Y n a)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- The actual fold map adds the two homology coordinates. -/
theorem sumHomologyEquiv_fold (n : ℕ) (a : SingularHomology (X ⊕ X) n) :
    singularHomologyMap (sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)) n a =
      (sumHomologyEquiv X X n a).1 + (sumHomologyEquiv X X n a).2 := by
  rw [sumHomologyEquiv_sumElim, disjointHomology_id_apply, disjointHomology_id_apply]

/-- The fold formula applied to the inverse disjoint-union homology equivalence. -/
theorem sumHomologyEquiv_fold_symm (n : ℕ)
    (a : SingularHomology X n × SingularHomology X n) :
    singularHomologyMap (sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)) n
      ((sumHomologyEquiv X X n).symm a) = a.1 + a.2 := by
  rw [sumHomologyEquiv_sumElim_symm, disjointHomology_id_apply, disjointHomology_id_apply]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
