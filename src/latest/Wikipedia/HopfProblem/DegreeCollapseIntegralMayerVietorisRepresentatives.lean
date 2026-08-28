import Wikipedia.HopfProblem.DegreeCollapseSmallIntegralCap
import Wikipedia.NoExoticSixSphere.SingularSmallChainComparison
import Wikipedia.NoExoticSixSphere.ChainConnectingRepresentatives

/-!
# Original integral Mayer--Vietoris on native small-cycle representatives

The canonical isomorphism between the two small-chain constructions
preserves the piece maps and the ambient inclusion. The lift--boundary
formula below therefore computes the original integral connecting
homomorphism, with its original sign, on native small-chain cycles.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralMayerVietoris

open NoExoticSixSphere FirstHurewicz SingularMayerVietoris
open IntegralCap (Coefficient)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev smallSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (SingularSubcomplex.smallChainSquare U V Coefficient).shortComplex

abbrev smallInclusion : (smallSequence U V).X₃ ⟶ singularComplex X :=
  (SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.smallInclusion U V)

theorem smallSequence_shortExact : (smallSequence U V).ShortExact :=
  SingularSubcomplex.smallChainSequence_shortExact U V Coefficient

theorem first_eq : (smallSequence U V).f = (chainSequence U V).f := rfl

/-- The canonical comparison retains the actual sum map from the two pieces. -/
theorem second_comparison :
    (smallSequence U V).g ≫ (SingularSubcomplex.integralSmallIso U V).hom =
      (chainSequence U V).g := by
  change biprod.desc
    ((SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.toSmallLeft U V))
    ((SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.toSmallRight U V)) ≫
      (SingularSubcomplex.integralSmallIso U V).hom =
    biprod.desc (SingularMayerVietoris.toSmallLeft U V) (SingularMayerVietoris.toSmallRight U V)
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, SingularSubcomplex.toSmallLeft_integralSmallIso]
    exact (biprod.inl_desc _ _).symm
  · simp only [biprod.inr_desc_assoc, SingularSubcomplex.toSmallRight_integralSmallIso]
    exact (biprod.inr_desc _ _).symm

/-- The original small-chain sum followed by inclusion is the actual ambient sum. -/
theorem second_inclusion : (smallSequence U V).g ≫ smallInclusion U V =
    biprod.desc (RelativeCoefficients.inclusion Coefficient U)
      (RelativeCoefficients.inclusion Coefficient V) := by
  change biprod.desc
    ((SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.toSmallLeft U V))
    ((SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.toSmallRight U V)) ≫ _ = _
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, SingularSubcomplex.chainToSmallLeft_inclusion]
    exact (biprod.inl_desc _ _).symm
  · simp only [biprod.inr_desc_assoc, SingularSubcomplex.chainToSmallRight_inclusion]
    exact (biprod.inr_desc _ _).symm

/-- The original integral connecting map retains the actual native lift and boundary. -/
theorem connecting_cycleClass (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : ModuleHomology.Cycle (smallSequence U V).X₃ (n + 1))
    (b : (smallSequence U V).X₂.X (n + 1))
    (hb : ((smallSequence U V).g.f (n + 1)).hom b = a.val)
    (c : ModuleHomology.Cycle (singularComplex (U ∩ V : Set X)) n)
    (hc : ((smallSequence U V).f.f n).hom c.val =
      ((smallSequence U V).X₂.d (n + 1) n).hom b) :
    connectingHomomorphism U V hU hV hcover n
        (ModuleHomology.cycleClass (singularComplex X) (n + 1)
          (ModuleHomology.mapCycles (smallInclusion U V) (n + 1) a)) =
      ModuleHomology.cycleClass (singularComplex (U ∩ V : Set X)) n c := by
  let z := ModuleHomology.mapCycles (SingularSubcomplex.integralSmallIso U V).hom (n + 1) a
  have hb' : ((chainSequence U V).g.f (n + 1)).hom b = z.val :=
    (congrArg (fun m => (m.f (n + 1)).hom b) (second_comparison U V)).symm.trans
      ((congrArg ((SingularSubcomplex.integralSmallIso U V).hom.f (n + 1)).hom hb).trans
        (ModuleHomology.mapCycles_val _ _ a).symm)
  have hz : ModuleHomology.mapCycles (SingularMayerVietoris.smallInclusion U V) (n + 1) z =
      ModuleHomology.mapCycles (smallInclusion U V) (n + 1) a := by
    apply Subtype.ext
    exact (ModuleHomology.mapCycles_val _ _ z).trans
      ((congrArg ((SingularMayerVietoris.smallInclusion U V).f (n + 1)).hom
        (ModuleHomology.mapCycles_val (SingularSubcomplex.integralSmallIso U V).hom
          (n + 1) a)).trans
        ((congrArg (fun m => (m.f (n + 1)).hom a.val)
          (SingularSubcomplex.integralSmallIso_inclusion U V)).trans
            (ModuleHomology.mapCycles_val (smallInclusion U V) (n + 1) a).symm))
  have hclass : smallHomologyComparison U V (n + 1)
      (ModuleHomology.cycleClass (smallComplex U V) (n + 1) z) =
      ModuleHomology.cycleClass (singularComplex X) (n + 1)
        (ModuleHomology.mapCycles (smallInclusion U V) (n + 1) a) :=
    (ModuleHomology.homologyMap_cycleClass
      (SingularMayerVietoris.smallInclusion U V) (n + 1) z).trans
        (congrArg (ModuleHomology.cycleClass (singularComplex X) (n + 1)) hz)
  exact (congrArg (connectingHomomorphism U V hU hV hcover n) hclass.symm).trans
    ((connectingHomomorphism_comparison U V hU hV hcover n _).trans
      (ChainConnecting.connecting_cycleClass (chainSequence_shortExact U V) n z b hb' c hc))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralMayerVietoris
