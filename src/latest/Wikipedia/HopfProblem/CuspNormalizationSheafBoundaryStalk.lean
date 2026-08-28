import Wikipedia.HopfProblem.CuspNormalizationSheafCurveStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspSums

/-!
# The actual boundary sheaf stalk as the product of incident axis germs

The direct-sum stalk is first compared with the actual product of all
three curve stalks. The stalks of nonincident closed curves are zero;
the remaining factors are identified with actual one-variable analytic
germs using the actual centered axis charts. Thus no inactive factor or
local analytic identification is an assumption of the comparison.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryStalk

open CuspQuotient ToricCharts ToricSpace ToricFan
open CuspQuotient.NormalizationLocalCoordinates SheafResolution SheafCurveStalk

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- The actual source-ordered double curves incident to the chart point. -/
abbrev ActiveCurves (s : Triangle) (b : CoordinateSpace 3) :=
  {k : Fin 3 // sourcePair s k ⊆ Germs.activeBranches b}

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- Discard the genuinely zero nonincident stalks and use the actual
analytic axis-stalk equivalence in every remaining factor. -/
def curveProductEquiv (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    (∀ k : Fin 3, (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x) ≃+
      (ActiveCurves s ((e) x.val) → SheafGermComplex.AxisGerm) := by
  classical
  refine
    { toFun := fun φ k => curveStalkEquivAt C ε hε hε1 hC hR a s x hx k.val k.property (φ k)
      invFun := fun ψ k => if hk : sourcePair s k ⊆ Germs.activeBranches ((e) x.val) then
        (curveStalkEquivAt C ε hε hε1 hC hR a s x hx k hk).symm (ψ ⟨k, hk⟩) else 0
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro φ
    funext k
    by_cases hk : sourcePair s k ⊆ Germs.activeBranches ((e) x.val)
    · simp only [dif_pos hk, AddEquiv.symm_apply_apply]
    · simp only [dif_neg hk]
      let := AddCommGrpCat.subsingleton_of_isZero
        (curveStalk_isZeroAt C ε hε hε1 hC hR a s x hx k hk)
      exact Subsingleton.elim _ _
  · intro ψ
    funext k
    simp only [dif_pos k.property, AddEquiv.apply_symm_apply]
  · intro φ ψ
    funext k
    exact map_add (curveStalkEquivAt C ε hε hε1 hC hR a s x hx k.val k.property) (φ k) (ψ k)

@[simp] theorem curveProductEquiv_apply (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (φ : ∀ k : Fin 3, (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x)
    (k : ActiveCurves s ((e) x.val)) :
    curveProductEquiv C ε hε hε1 hC hR a s x hx φ k =
      curveStalkEquivAt C ε hε hε1 hC hR a s x hx k.val k.property (φ k) := rfl

/-- The genuine direct-sum boundary stalk is the product of the actual
analytic axis germs of the actual incident double curves. -/
def boundaryStalkEquivAt (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x ≃+
      (ActiveCurves s ((e) x.val) → SheafGermComplex.AxisGerm) :=
  (SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε))
    (curveSheaf C ε hε hε1 hC hR) x).trans
      (curveProductEquiv C ε hε hε1 hC hR a s x hx)

/-- Each coordinate is the actual stalk of the actual direct-sum
projection, followed by the actual centered axis comparison. -/
@[simp] theorem boundaryStalkEquivAt_apply (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (φ : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk x)
    (k : ActiveCurves s ((e) x.val)) :
    boundaryStalkEquivAt C ε hε hε1 hC hR a s x hx φ k =
      curveStalkEquivAt C ε hε hε1 hC hR a s x hx k.val k.property
        ((SheafBiproduct.stalkFunctor (TopCat.of (CentralSpace C ε)) x).map
          (biproduct.π (curveSheaf C ε hε hε1 hC hR) k.val) φ) := by
  change curveStalkEquivAt C ε hε hε1 hC hR a s x hx k.val k.property
      (SheafBiproduct.finiteStalkEquiv (TopCat.of (CentralSpace C ε))
        (curveSheaf C ε hε hε1 hC hR) x φ k.val) = _
  rw [SheafBiproduct.finiteStalkEquiv_apply]

end Wikipedia.HopfProblem.CuspNormalization.SheafBoundaryStalk
