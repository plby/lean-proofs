import Wikipedia.NoExoticSixSphere.RelativeCoefficientConnecting
import Wikipedia.NoExoticSixSphere.SupportedRelativeCycleClass

/-!
# Lifting through the original relative map for nested subspaces

If the connecting class for `(X,V)` vanishes after projection to
`(V,U)`, subtracting an actual chain in `V` corrects its ambient lift
to a cycle for `(X,U)`. The image of the corrected class under the
original identity map of pairs is exactly the given class.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

theorem quotient_cycle_is_cycle (U : Set X) (n : ℕ)
    (w : ModuleHomology.Cycle (coefficientComplex A X) n) :
    ((complex A U).d n (n - 1)).hom (quotientMap A U n w.val) = 0 := by
  rw [boundary_quotientMap, ModuleHomology.cycle_condition, map_zero]

theorem projection_cycleClass (U : Set X) (n : ℕ)
    (w : ModuleHomology.Cycle (coefficientComplex A X) n) :
    homologyLinearMap (projection A U) n
        (ModuleHomology.cycleClass (coefficientComplex A X) n w) =
      relativeClass A U n w.val (quotient_cycle_is_cycle A U n w) := by
  rw [ModuleHomology.homologyMap_cycleClass, relativeClass]
  apply congrArg (ModuleHomology.cycleClass (complex A U) n)
  apply Subtype.ext
  exact ModuleHomology.mapCycles_val (projection A U) n w

theorem corrected_boundary_quotient (U V : Set X) (n : ℕ)
    (c : CoefficientChains.Chains A X (n + 1)) (w : CoefficientChains.Chains A V n)
    (v : CoefficientChains.Chains A V (n + 1))
    (hw : ((inclusion A V).f n).hom w = ((coefficientComplex A X).d (n + 1) n).hom c)
    (hv : quotientMap A (RelativeSingularHomology.overlapIn V U) n
      (w - ((coefficientComplex A V).d (n + 1) n).hom v) = 0) :
    quotientMap A U n (((coefficientComplex A X).d (n + 1) n).hom
      (c - ((inclusion A V).f (n + 1)).hom v)) = 0 := by
  obtain ⟨e, he⟩ := (quotientMap_eq_zero_iff A (RelativeSingularHomology.overlapIn V U) n _).mp hv
  let f : C(RelativeSingularHomology.overlapIn V U, U) :=
    ⟨fun r ↦ ⟨r.val.val, r.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hcomp : spaceMap A f ≫ inclusion A U =
      inclusion A (RelativeSingularHomology.overlapIn V U) ≫ inclusion A V := by
    change spaceMap A f ≫ spaceMap A (subtypeInclusion U) =
      spaceMap A (subtypeInclusion (RelativeSingularHomology.overlapIn V U)) ≫
        spaceMap A (subtypeInclusion V)
    rw [← spaceMap_comp, ← spaceMap_comp]
    rfl
  have hd : ((coefficientComplex A X).d (n + 1) n).hom
      (((inclusion A V).f (n + 1)).hom v) =
        ((inclusion A V).f n).hom (((coefficientComplex A V).d (n + 1) n).hom v) :=
    congrArg (fun m ↦ m.hom v) ((inclusion A V).comm (n + 1) n)
  have hb : ((coefficientComplex A X).d (n + 1) n).hom
      (c - ((inclusion A V).f (n + 1)).hom v) =
        ((inclusion A V).f n).hom (w - ((coefficientComplex A V).d (n + 1) n).hom v) := by
    rw [map_sub, hd, ← hw, map_sub]
  apply (quotientMap_eq_zero_iff A U n _).mpr
  refine ⟨((spaceMap A f).f n).hom e, ?_⟩
  exact (congrArg (fun m ↦ (m.f n).hom e) hcomp).trans
    ((congrArg ((inclusion A V).f n).hom he).trans hb.symm)

theorem corrected_quotient (V : Set X) (n : ℕ) (c : CoefficientChains.Chains A X n)
    (v : CoefficientChains.Chains A V n) :
    quotientMap A V n (c - ((inclusion A V).f n).hom v) = quotientMap A V n c := by
  have hv : quotientMap A V n (((inclusion A V).f n).hom v) = 0 :=
    (quotientMap_eq_zero_iff A V n _).mpr ⟨v, rfl⟩
  rw [map_sub, hv, sub_zero]

theorem exists_lift_of_connecting_projection_zero {U V : Set X} (hUV : U ⊆ V) (n : ℕ)
    (F : (complex A V).homology (n + 1))
    (hF : homologyLinearMap (projection A (RelativeSingularHomology.overlapIn V U)) n
      (connecting A V n F) = 0) :
    ∃ G : (complex A U).homology (n + 1),
      homologyLinearMap (mapChain A (ContinuousMap.id X)
        (show Set.MapsTo (ContinuousMap.id X) U V from hUV)) (n + 1) G = F := by
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (complex A V) (n + 1) F
  obtain ⟨c, hc, w, hw, hconnect⟩ := exists_connecting_lift A V n z
  rw [hconnect, projection_cycleClass] at hF
  obtain ⟨v, hv⟩ := (relativeClass_eq_zero_iff A
    (RelativeSingularHomology.overlapIn V U) n w.val
    (quotient_cycle_is_cycle A (RelativeSingularHomology.overlapIn V U) n w)).mp hF
  let c' := c - ((inclusion A V).f (n + 1)).hom v
  have hcycle : ((complex A U).d (n + 1) n).hom (quotientMap A U (n + 1) c') = 0 :=
    (boundary_quotientMap A U (n + 1) n c').trans
      (corrected_boundary_quotient A U V n c w.val v hw hv)
  have hcycle' : ((complex A U).d (n + 1) ((n + 1) - 1)).hom
      (quotientMap A U (n + 1) c') = 0 :=
    (congrArg (fun j ↦ ((complex A U).d (n + 1) j).hom
      (quotientMap A U (n + 1) c') = 0) (Nat.add_sub_cancel n 1)).mpr hcycle
  let z' := ModuleHomology.mkCycle (complex A U) (n + 1)
    (quotientMap A U (n + 1) c') hcycle'
  refine ⟨ModuleHomology.cycleClass (complex A U) (n + 1) z', ?_⟩
  rw [ModuleHomology.homologyMap_cycleClass]
  apply congrArg (ModuleHomology.cycleClass (complex A V) (n + 1))
  apply Subtype.ext
  have hp := projection_mapChain A (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) U V from hUV)
  rw [spaceMap_id, Category.id_comp] at hp
  exact (ModuleHomology.mapCycles_val (mapChain A (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) U V from hUV)) (n + 1) z').trans
      ((congrArg (fun m ↦ (m.f (n + 1)).hom c') hp).trans
        ((corrected_quotient A V (n + 1) c v).trans hc))

end NoExoticSixSphere.RelativeCoefficients
