import Wikipedia.NoExoticSixSphere.ModTwoCapChainNaturality
import Wikipedia.NoExoticSixSphere.ModTwoCapCohomology

/-!
# Naturality of the descended mod-two cap product

The original chain-level equality passes through actual cycle maps and
the actual categorical homology and cohomology maps. Thus this naturality
statement concerns the constructed cap product itself and the original
continuous-map actions, not an abstractly transported pairing.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Mapping capped original cycles agrees with capping their original images. -/
theorem mapCycles_cap (f : C(X, Y)) (p q : ℕ) (α : Cocycle Y p)
    (c : ModuleHomology.Cycle (modComplex 2 X) (p + q)) :
    ModuleHomology.mapCycles (RelativeCoefficients.spaceMap Coefficient f) q
        (capCycles p q (SingularCohomologyFree.mapCocycles (cochainPullback f) p α).val
          (cocycle_coboundary_zero X p
            (SingularCohomologyFree.mapCocycles (cochainPullback f) p α)) c) =
      capCycles p q α.val (cocycle_coboundary_zero Y p α)
        (ModuleHomology.mapCycles (RelativeCoefficients.spaceMap Coefficient f) (p + q) c) := by
  apply Subtype.ext
  let β := SingularCohomologyFree.mapCocycles (cochainPullback f) p α
  have hβ : β.val = pullback f p α.val :=
    SingularCohomologyFree.mapCocycles_val (cochainPullback f) p α
  have hleft := ModuleHomology.mapCycles_val (RelativeCoefficients.spaceMap Coefficient f) q
    (capCycles p q β.val (cocycle_coboundary_zero X p β) c)
  have hright := capCycles_val p q α.val (cocycle_coboundary_zero Y p α)
    (ModuleHomology.mapCycles (RelativeCoefficients.spaceMap Coefficient f) (p + q) c)
  apply hleft.trans
  apply (congrArg ((RelativeCoefficients.spaceMap Coefficient f).f q).hom
    (capCycles_val p q β.val (cocycle_coboundary_zero X p β) c)).trans
  apply (congrArg (fun γ : Cochain X p =>
    ((RelativeCoefficients.spaceMap Coefficient f).f q).hom (cap (q := q) γ c.val)) hβ).trans
  apply (spaceMap_cap f p q α.val c.val).trans
  exact (hright.trans (congrArg (cap (q := q) α.val)
    (ModuleHomology.mapCycles_val (RelativeCoefficients.spaceMap Coefficient f) (p + q) c))).symm

/-- The original native homology action sends each cycle to its actual mapped cycle. -/
theorem modHomologyMap_cycleClass (f : C(X, Y)) (n : ℕ)
    (c : ModuleHomology.Cycle (modComplex 2 X) n) :
    modHomologyMap 2 f n (ModuleHomology.cycleClass (modComplex 2 X) n c) =
      ModuleHomology.cycleClass (modComplex 2 Y) n
        (ModuleHomology.mapCycles (RelativeCoefficients.spaceMap Coefficient f) n c) :=
  ModuleHomology.homologyMap_cycleClass (RelativeCoefficients.spaceMap Coefficient f) n c

/-- Naturality for arbitrary actual cohomology and homology classes. -/
theorem capProduct_naturality (f : C(X, Y)) (p q : ℕ)
    (a : Cohomology Y p) (c : ModHomology 2 X (p + q)) :
    modHomologyMap 2 f q (capProduct X p q (cohomologyPullback f p a) c) =
      capProduct Y p q a (modHomologyMap 2 f (p + q) c) := by
  obtain ⟨α, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective (cochainComplex Y) p a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (modComplex 2 X) (p + q) c
  rw [cohomologyPullback_cocycleClass, capProduct_cocycle_cycle,
    modHomologyMap_cycleClass, modHomologyMap_cycleClass, capProduct_cocycle_cycle]
  exact congrArg (ModuleHomology.cycleClass (modComplex 2 Y) q) (mapCycles_cap f p q α z)

end NoExoticSixSphere.ModTwoCapProduct
