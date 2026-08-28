import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapNaturality
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedHomology

/-!
# Extension and forgetting of original integral cohomology supports

The groups are integral cohomology of the genuine relative chain quotients
by the support complements. The maps are actual pair-map precomposition.
Their cap compatibility retains the original integral homology restriction.
The whole-space equivalence uses the proved empty-subspace chain isomorphism.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedCohomology

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X]

abbrev complex (K : Set X) :=
  dualComplex (SupportedRelativeHomology.Complex (ModuleCat.of ℤ ℤ) K)

abbrev Cohomology (K : Set X) (p : ℕ) := (complex K).homology p

/-- Growing the support is the original contravariant map of relative complexes. -/
def extendCochain {K L : Set X} (h : K ⊆ L) : complex K ⟶ complex L :=
  dualMap (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ ℤ) h)

theorem extendCochain_refl (K : Set X) :
    extendCochain (Set.Subset.refl K) = 𝟙 (complex K) := by
  unfold extendCochain
  rw [SupportedRelativeHomology.restrictChain_refl, dualMap_id]

theorem extendCochain_trans {K L N : Set X} (hKL : K ⊆ L) (hLN : L ⊆ N) :
    extendCochain (hKL.trans hLN) = extendCochain hKL ≫ extendCochain hLN := by
  unfold extendCochain
  rw [SupportedRelativeHomology.restrictChain_trans, dualMap_comp]

abbrev extend {K L : Set X} (h : K ⊆ L) (p : ℕ) : Cohomology K p →ₗ[ℤ] Cohomology L p :=
  (HomologicalComplex.homologyMap (extendCochain h) p).hom

theorem extend_refl (K : Set X) (p : ℕ) :
    extend (Set.Subset.refl K) p = LinearMap.id := by
  change (HomologicalComplex.homologyMap (extendCochain (Set.Subset.refl K)) p).hom = _
  rw [extendCochain_refl, HomologicalComplex.homologyMap_id]
  rfl

theorem extend_trans {K L N : Set X} (hKL : K ⊆ L) (hLN : L ⊆ N) (p : ℕ) :
    extend (hKL.trans hLN) p = (extend hLN p).comp (extend hKL p) := by
  change (HomologicalComplex.homologyMap (extendCochain (hKL.trans hLN)) p).hom = _
  rw [extendCochain_trans, HomologicalComplex.homologyMap_comp]
  rfl

theorem extend_eq_pullback {K L : Set X} (h : K ⊆ L) (p : ℕ) :
    extend h p = RelativeIntegralCap.cohomologyPullback (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hx hy => hx (h hy)) p := rfl

/-- The original quotient projection forgets support. -/
abbrev toAbsolute (K : Set X) (p : ℕ) : Cohomology K p →ₗ[ℤ] SingularCohomology X p :=
  (HomologicalComplex.homologyMap (RelativeIntegralCap.toAbsoluteMap Kᶜ) p).hom

theorem extendCochain_toAbsolute {K L : Set X} (h : K ⊆ L) :
    extendCochain h ≫ RelativeIntegralCap.toAbsoluteMap Lᶜ =
      RelativeIntegralCap.toAbsoluteMap Kᶜ := by
  have he := RelativeCoefficients.projection_mapChain (ModuleCat.of ℤ ℤ)
    (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hx hy => hx (h hy))
  rw [RelativeCoefficients.spaceMap_id, Category.id_comp] at he
  exact (dualMap_comp
    (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) Lᶜ)
    (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ ℤ) h)).symm.trans
      (congrArg dualMap he)

theorem toAbsolute_extend {K L : Set X} (h : K ⊆ L) (p : ℕ) (a : Cohomology K p) :
    toAbsolute L p (extend h p a) = toAbsolute K p a := by
  have he := congrArg (fun f : complex K ⟶ singularCochainComplex X =>
    (HomologicalComplex.homologyMap f p).hom) (extendCochain_toAbsolute h)
  have hc := congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_comp
    (extendCochain h) (RelativeIntegralCap.toAbsoluteMap Lᶜ) p)
  exact LinearMap.congr_fun (hc.symm.trans he) a

/-- The actual whole-support map is an equivalence, before any duality theorem. -/
def absoluteEquiv (p : ℕ) :
    Cohomology (Set.univ : Set X) p ≃ₗ[ℤ] SingularCohomology X p := by
  have : IsIso (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ)
      ((Set.univ : Set X)ᶜ)) := by
    rw [Set.compl_univ]
    exact RelativeCoefficients.projection_empty_isIso (ModuleCat.of ℤ ℤ)
  let e := dualFunctor.mapIso
    (asIso (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) ((Set.univ : Set X)ᶜ))).op
  exact ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) p).mapIso
    e).toLinearEquiv

theorem absoluteEquiv_toLinearMap (p : ℕ) :
    (absoluteEquiv (X := X) p).toLinearMap = toAbsolute Set.univ p := rfl

/-- Extending a cohomology support is adjoint to the actual integral homology restriction. -/
theorem cap_extend {K L : Set X} (hKL : K ⊆ L) {p q d : ℕ} (h : p + q = d)
    (a : Cohomology K p) (c : SupportedRelativeHomology.Homology (ModuleCat.of ℤ ℤ) L d) :
    RelativeIntegralCap.capProductInDegree Lᶜ h (extend hKL p a) c =
      RelativeIntegralCap.capProductInDegree Kᶜ h a
        (SupportedRelativeHomology.restrict (ModuleCat.of ℤ ℤ) hKL d c) := by
  have he := RelativeIntegralCap.capProductInDegree_naturality (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hx hy => hx (hKL hy)) h a c
  rw [RelativeSingularHomology.chainMap_id, HomologicalComplex.homologyMap_id] at he
  exact he

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedCohomology
