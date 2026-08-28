import Wikipedia.NoExoticSixSphere.SingularSmallChainComparison
import Wikipedia.NoExoticSixSphere.ChainConnectingRepresentatives

/-!
# The native mod-two Mayer--Vietoris connecting map

The original small-chain short exact row and the proved subdivision
comparison define the connecting map on the actual ambient homology.
Its representative formula keeps the original small-cycle inclusion.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev Coefficient := ModuleCat.of ℤ (ZMod 2)

abbrev smallSequence := (SingularSubcomplex.smallChainSquare U V Coefficient).shortComplex

theorem smallSequence_shortExact : (smallSequence U V).ShortExact :=
  SingularSubcomplex.smallChainSequence_shortExact U V Coefficient

abbrev smallInclusion :=
  (SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.smallInclusion U V)

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

/-- The actual inclusion-induced homology equivalence proved by subdivision. -/
def smallEquiv (n : ℕ) : (smallSequence U V).X₃.homology n ≃ₗ[ℤ] ModHomology 2 X n := by
  let := SingularSubcomplex.smallInclusion_mod_quasiIso U V 2 (by decide) hU hV hcover
  exact (isoOfQuasiIsoAt (smallInclusion U V) n).toLinearEquiv

/-- The genuine connecting map on the original ambient mod-two homology. -/
def connecting (n : ℕ) : ModHomology 2 X (n + 1) →ₗ[ℤ] ModHomology 2 (U ∩ V : Set X) n :=
  (connectingMap (smallSequence_shortExact U V) n).comp
    (smallEquiv U V hU hV hcover (n + 1)).symm.toLinearMap

theorem connecting_comparison (n : ℕ) (a : (smallSequence U V).X₃.homology (n + 1)) :
    connecting U V hU hV hcover n (homologyLinearMap (smallInclusion U V) (n + 1) a) =
      connectingMap (smallSequence_shortExact U V) n a :=
  congrArg (connectingMap (smallSequence_shortExact U V) n)
    ((smallEquiv U V hU hV hcover (n + 1)).symm_apply_apply a)

/-- Original small cycle representatives give the native lift--boundary connecting formula. -/
theorem connecting_cycleClass (n : ℕ) (a : ModuleHomology.Cycle (smallSequence U V).X₃ (n + 1))
    (b : (smallSequence U V).X₂.X (n + 1))
    (hb : ((smallSequence U V).g.f (n + 1)).hom b = a.val)
    (c : ModuleHomology.Cycle (modComplex 2 (U ∩ V : Set X)) n)
    (hc : ((smallSequence U V).f.f n).hom c.val =
      ((smallSequence U V).X₂.d (n + 1) n).hom b) :
    connecting U V hU hV hcover n (ModuleHomology.cycleClass (modComplex 2 X) (n + 1)
        (ModuleHomology.mapCycles (smallInclusion U V) (n + 1) a)) =
      ModuleHomology.cycleClass (modComplex 2 (U ∩ V : Set X)) n c := by
  exact (congrArg (connecting U V hU hV hcover n)
    (ModuleHomology.homologyMap_cycleClass (smallInclusion U V) (n + 1) a).symm).trans
      ((connecting_comparison U V hU hV hcover n _).trans
        (ChainConnecting.connecting_cycleClass (smallSequence_shortExact U V) n a b hb c hc))

end NoExoticSixSphere.ModTwoMayerVietoris
