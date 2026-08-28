import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphere

/-!
# Actual higher acyclicity of the cusp double-curve terms

Each source-ordered double curve has the constructed analytic sphere
parametrization. Its genuine holomorphic sheaf therefore has the proved
sphere cohomology, via actual biholomorphic section pullback and actual
finite closed pushforward. The three actual curve inclusions have the
same genuine cohomology as their sources. Additivity of the actual Ext
cohomology functor then proves higher acyclicity of the actual boundary
term of the normalization resolution.

No rational-curve or direct-image acyclicity is assumed, and this file
does not assert higher acyclicity of the normalization surface.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The genuine curve holomorphic sheaf with exactly its constructed
atlas, made explicit so no arbitrary charted structure is generalized. -/
abbrev actualCurveHolomorphicSheaf (k : Fin 3) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (sourceDoubleCurve C ε hε k)) :=
  @HolomorphicFunctionSheaf.additiveSheaf ℂ ℂ _ _ _ 𝓘(ℂ)
    (sourceDoubleCurve C ε hε k) _
    (curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k))

/-- The actual curve sphere parametrization induces a genuine
cohomology equivalence in every degree. -/
def actualCurveSphereCohomologyEquiv (k : Fin 3) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (actualCurveHolomorphicSheaf C ε hε hε1 hC hR k) n ≃+
      CategoryTheory.Sheaf.H.{0}
        HolomorphicSheafCohomology.SphereDolbeault.holomorphicSheaf n := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact HolomorphicSheafCohomology.Biholomorph.cohomologyEquiv
    (curveBiholomorph C ε hε hε1 hC hR (sourceEdgeIndex k)) n

/-- Every positive genuine holomorphic cohomology group of each
actual source-ordered double curve is zero. -/
theorem actualCurveHolomorphic_higher_subsingleton (k : Fin 3) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (actualCurveHolomorphicSheaf C ε hε hε1 hC hR k) (n + 1)) := by
  let e := actualCurveSphereCohomologyEquiv C ε hε hε1 hC hR k (n + 1)
  refine ⟨fun a b => e.injective ?_⟩
  have hh := HolomorphicSheafCohomology.SphereDolbeault.holomorphic_higher_subsingleton n
  exact hh.elim (e a) (e b)

/-- The actual double-curve resolution term, including its actual
closed inclusion, has the genuine sphere cohomology. -/
def curveDirectImageSphereCohomologyEquiv (k : Fin 3) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (curveSheaf C ε hε hε1 hC hR k) n ≃+
      CategoryTheory.Sheaf.H.{0}
        HolomorphicSheafCohomology.SphereDolbeault.holomorphicSheaf n := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  exact (curveHolomorphicCohomologyEquiv C ε hε hε1 hC hR k n).trans
    (actualCurveSphereCohomologyEquiv C ε hε hε1 hC hR k n)

/-- Actual finite closed pushforward preserves the proved higher
vanishing for each actual double-curve resolution term. -/
theorem curveSheaf_higher_subsingleton (k : Fin 3) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (curveSheaf C ε hε hε1 hC hR k) (n + 1)) := by
  let e := curveDirectImageSphereCohomologyEquiv C ε hε hε1 hC hR k (n + 1)
  refine ⟨fun a b => e.injective ?_⟩
  have hh := HolomorphicSheafCohomology.SphereDolbeault.holomorphic_higher_subsingleton n
  exact hh.elim (e a) (e b)

/-- The actual three-curve boundary term of the normalization
resolution is acyclic in every positive genuine Ext degree. -/
theorem boundarySheaf_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (boundarySheaf C ε hε hε1 hC hR) (n + 1)) := by
  let K : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) ⥤ AddCommGrpCat :=
    CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of (CentralSpace C ε))) (n + 1)
  have : K.Additive := by
    change (CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of (CentralSpace C ε))) (n + 1)).Additive
    infer_instance
  let A : Fin 3 → TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)) :=
    curveSheaf C ε hε hε1 hC hR
  let ei := K.mapBiproduct A ≪≫ AddCommGrpCat.biproductIsoPi (K.obj ∘ A)
  let e := ei.addCommGroupIsoToAddEquiv
  refine ⟨fun a b => e.injective ?_⟩
  funext k
  exact (curveSheaf_higher_subsingleton C ε hε hε1 hC hR k n).elim ((e a) k) ((e b) k)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
