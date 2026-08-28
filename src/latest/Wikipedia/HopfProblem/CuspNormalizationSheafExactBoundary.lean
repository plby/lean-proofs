import Wikipedia.HopfProblem.CuspNormalizationSheafExactNormalization
import Wikipedia.HopfProblem.CuspNormalizationSheafBoundaryAugmentation

/-!
# Exactness at the actual double-curve direct sum

The actual last-map kernel has zero oriented augmentation in its actual
axis-germ coordinates. The proved analytic-germ exactness supplies branch
germs, which the actual normalization-stalk equivalence transports back
to a preimage under the actual global boundary arrow. This proves exactness
on every actual stalk and hence exactness of the actual sheaves.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace ToricFan
open CuspQuotient.NormalizationLocalCoordinates
open SheafNormalizationStalk SheafBoundaryStalk SheafBoundaryAugmentation

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual alternating evaluation arrow evaluated on actual stalks. -/
def deltaOneStalkMap (x : CentralSpace C ε) :
    (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x →+
      (tripleSheaf C ε hε).presheaf.stalk x :=
  ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
    (deltaOne C ε hε hε1 hC hR)).hom

/-- The genuine global complex identity remains the actual zero
composite under the actual stalk functor. -/
theorem deltaOneStalkMap_deltaZero (x : CentralSpace C ε)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) :
    deltaOneStalkMap C ε hε hε1 hC hR x
      (deltaZeroStalkMap C ε hε hε1 hC hR x φ) = 0 := by
  let F := SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x
  have hz : F.map (deltaZero C ε hε hε1 hC hR) ≫
      F.map (deltaOne C ε hε hε1 hC hR) = 0 :=
    (F.map_comp _ _).symm.trans
      ((congrArg F.map (deltaZero_deltaOne C ε hε hε1 hC hR)).trans (F.map_zero _ _))
  exact ConcreteCategory.congr_hom hz φ

/-- Every genuine adapted chart proves exactness of the actual second
and third stalk maps. All local analytic lifting has been constructed. -/
theorem boundaryStalkMaps_exact (a : Tube (disc ε)) (s : Triangle)
    (x : CentralSpace C ε)
    (hx : x.val ∈ (normalizationChart C ε hε hε1 hC hR a s).source) :
    Function.Exact (deltaZeroStalkMap C ε hε hε1 hC hR x)
      (deltaOneStalkMap C ε hε hε1 hC hR x) := by
  let b := normalizationChart C ε hε hε1 hC hR a s x.val
  let e₁ := normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx
  let e₂ := boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx
  intro β
  constructor
  · intro hβ
    obtain ⟨φ, hφ⟩ := exists_orientedDifference_preimage_of_deltaOne_eq_zero
      C ε hε hε1 hC hR a s x hx β hβ
    refine ⟨e₁.symm φ, ?_⟩
    apply e₂.injective
    change boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx
      (deltaZeroStalkMap C ε hε hε1 hC hR x (e₁.symm φ)) = e₂ β
    rw [deltaZeroStalkMap_conjugacy]
    change orientedDifference s (Germs.activeBranches b) (e₁ (e₁.symm φ)) = e₂ β
    rw [e₁.apply_symm_apply]
    exact hφ
  · rintro ⟨φ, rfl⟩
    exact deltaOneStalkMap_deltaZero C ε hε hε1 hC hR x φ

/-- Categorical exactness of the actual middle stalk complex. -/
theorem boundaryComplex_stalk_exact (a : Tube (disc ε)) (s : Triangle)
    (x : CentralSpace C ε)
    (hx : x.val ∈ (normalizationChart C ε hε hε1 hC hR a s).source) :
    ((boundaryComplex C ε hε hε1 hC hR).map
      (SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x)).Exact :=
  (ShortComplex.ab_exact_iff_function_exact _).mpr
    (boundaryStalkMaps_exact C ε hε hε1 hC hR a s x hx)

/-- The kernel of the actual alternating evaluation consists exactly
of actual differences of holomorphic germs on the normalization. -/
theorem boundaryComplex_exact : (boundaryComplex C ε hε hε1 hC hR).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (boundaryComplex C ε hε hε1 hC hR)).mpr
  intro x
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  obtain ⟨a, s, _, hx, _⟩ :=
    componentProjection_local_coordinate_normalization C ε hε hε1 hC hR x.val
  exact boundaryComplex_stalk_exact C ε hε hε1 hC hR a s x hx

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
