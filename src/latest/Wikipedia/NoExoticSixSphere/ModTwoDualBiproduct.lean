import Wikipedia.NoExoticSixSphere.ModTwoDualHomotopy
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual cohomology of the mod-two dual of a chain biproduct

Contravariant duality and the homology functor are additive. Their
canonical biproduct comparisons therefore identify this actual
cohomology object with the product of the two actual cohomology groups.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace NoExoticSixSphere.ModTwoDualComplex

/-- The original mod-two cochain constructions form an additive contravariant functor. -/
def cochainDualFunctor : (ChainComplex (ModuleCat.{0} ℤ) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{0} ℤ) ℕ where
  obj K := complex K.unop
  map f := map f.unop
  map_id _ := map_id _
  map_comp f g := map_comp g.unop f.unop

instance cochainDualFunctor_additive : cochainDualFunctor.Additive where
  map_add := by
    intro K L f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change K.unop.X n →+ ZMod 2 at α
    apply AddMonoidHom.ext
    intro c
    exact α.map_add ((f.unop.f n).hom c) ((g.unop.f n).hom c)

/-- The canonical product marking retains the actual contravariant maps. -/
def cohomologyBiprodEquiv (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (complex (K ⊞ L)).homology n ≃ₗ[ℤ]
      ((complex K).homology n × (complex L).homology n) := by
  let F := cochainDualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n
  let : F.Additive := inferInstanceAs ((cochainDualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).Additive)
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  let e := (F.mapIso (biprod.opIso K L) ≪≫ Functor.mapBiprod F (op K) (op L) ≪≫
    ModuleCat.biprodIsoProd (F.obj (op K)) (F.obj (op L))).toLinearEquiv
  let ea : (complex (K ⊞ L)).homology n ≃+
      ((complex K).homology n × (complex L).homology n) :=
    { toEquiv := e.toEquiv
      map_add' := fun x y => e.map_add x y }
  exact ea.toIntLinearEquiv

/-- The first product coordinate is the pullback induced by the original chain injection. -/
theorem cohomologyBiprodEquiv_fst (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : (complex (K ⊞ L)).homology n) :
    (cohomologyBiprodEquiv K L n a).1 =
      (HomologicalComplex.homologyMap (map (biprod.inl : K ⟶ K ⊞ L)) n).hom a := by
  let F := cochainDualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n
  let : F.Additive := inferInstanceAs ((cochainDualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).Additive)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  let I := F.mapIso (biprod.opIso K L) ≪≫ Functor.mapBiprod F (op K) (op L) ≪≫
    ModuleCat.biprodIsoProd (F.obj (op K)) (F.obj (op L))
  have he : I.hom ≫
      ((ModuleCat.biprodIsoProd (F.obj (op K)) (F.obj (op L))).inv ≫ biprod.fst) =
      F.map (biprod.inl : K ⟶ K ⊞ L).op := by
    simp only [I, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Functor.mapBiprod_hom, biprod.lift_fst]
    rw [← F.map_comp, biprod.opIso_hom_fst]
  have hp := congrArg (fun f => f.hom (I.hom.hom a))
    (ModuleCat.biprodIsoProd_inv_comp_fst (F.obj (op K)) (F.obj (op L)))
  exact hp.symm.trans (congrArg (fun f => f.hom a) he)

/-- The second product coordinate is the pullback induced by the original chain injection. -/
theorem cohomologyBiprodEquiv_snd (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : (complex (K ⊞ L)).homology n) :
    (cohomologyBiprodEquiv K L n a).2 =
      (HomologicalComplex.homologyMap (map (biprod.inr : L ⟶ K ⊞ L)) n).hom a := by
  let F := cochainDualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n
  let : F.Additive := inferInstanceAs ((cochainDualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).Additive)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  let I := F.mapIso (biprod.opIso K L) ≪≫ Functor.mapBiprod F (op K) (op L) ≪≫
    ModuleCat.biprodIsoProd (F.obj (op K)) (F.obj (op L))
  have he : I.hom ≫
      ((ModuleCat.biprodIsoProd (F.obj (op K)) (F.obj (op L))).inv ≫ biprod.snd) =
      F.map (biprod.inr : L ⟶ K ⊞ L).op := by
    simp only [I, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.hom_inv_id_assoc, Functor.mapBiprod_hom, biprod.lift_snd]
    rw [← F.map_comp, biprod.opIso_hom_snd]
  have hp := congrArg (fun f => f.hom (I.hom.hom a))
    (ModuleCat.biprodIsoProd_inv_comp_snd (F.obj (op K)) (F.obj (op L)))
  exact hp.symm.trans (congrArg (fun f => f.hom a) he)

end NoExoticSixSphere.ModTwoDualComplex
