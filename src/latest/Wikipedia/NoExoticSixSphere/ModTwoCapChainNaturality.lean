import Wikipedia.NoExoticSixSphere.ModTwoCochainPullback

/-!
# Naturality of the original front/back cap chain

Mapping an actual capped chain agrees with capping the mapped chain by
the target cochain, after pulling that cochain back along the original
continuous map. The proof uses the literal maps of singular simplices.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients SingularCohomologyCup

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Naturality as an equality of the original coefficient-chain linear maps. -/
theorem spaceMap_cap_map (f : C(X, Y)) (p q : ℕ) (α : Cochain Y p) :
    (((RelativeCoefficients.spaceMap Coefficient f).f q).hom).comp
        (cap (q := q) (pullback f p α)) =
      (cap (q := q) α).comp ((RelativeCoefficients.spaceMap Coefficient f).f (p + q)).hom := by
  apply CoefficientChains.map_ext Coefficient X (p + q)
  intro σ a
  have hleft := congrArg ((RelativeCoefficients.spaceMap Coefficient f).f q).hom
    (cap_simplex (q := q) (pullback f p α) σ a)
  have hright := congrArg (cap (q := q) α)
    (CoefficientChains.spaceMap_simplex Coefficient (p + q) f σ a)
  apply hleft.trans
  apply (CoefficientChains.spaceMap_simplex Coefficient q f _ _).trans
  apply Eq.trans _ (hright.trans (cap_simplex (q := q) α (f.comp σ) a)).symm
  rw [pullback_simplex]
  simp only [ContinuousMap.comp_assoc]

/-- The naturality formula on every original chain. -/
theorem spaceMap_cap (f : C(X, Y)) (p q : ℕ) (α : Cochain Y p)
    (c : ModTwoChains.Chains X (p + q)) :
    ((RelativeCoefficients.spaceMap Coefficient f).f q).hom
        (cap (q := q) (pullback f p α) c) =
      cap (q := q) α (((RelativeCoefficients.spaceMap Coefficient f).f (p + q)).hom c) :=
  LinearMap.congr_fun (spaceMap_cap_map f p q α) c

end NoExoticSixSphere.ModTwoCapProduct
