import Wikipedia.HopfProblem.DegreeCollapseIntegralDualSequence
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Original integral cohomology in canonical biproduct coordinates

The actual integral cochain dual and the homology functor are additive.
Their canonical biproduct comparisons give product coordinates whose
maps are the original integral pullbacks by the two chain injections.
Dual sum and diagonal maps retain their original coordinate formulas.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCochainBiproduct

open SingularCohomologyFree

/-- The canonical comparison with the two original integral cohomology groups. -/
def cohomologyBiprodEquiv (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    (dualComplex (K ⊞ L)).homology n ≃ₗ[ℤ]
      ((dualComplex K).homology n × (dualComplex L).homology n) := by
  let F := dualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n
  let : F.Additive := inferInstanceAs ((dualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).Additive)
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  let e := (F.mapIso (biprod.opIso K L) ≪≫ Functor.mapBiprod F (op K) (op L) ≪≫
    ModuleCat.biprodIsoProd (F.obj (op K)) (F.obj (op L))).toLinearEquiv
  let ea : (dualComplex (K ⊞ L)).homology n ≃+
      ((dualComplex K).homology n × (dualComplex L).homology n) :=
    { toEquiv := e.toEquiv
      map_add' := fun x y => e.map_add x y }
  exact ea.toIntLinearEquiv

theorem cohomologyBiprodEquiv_fst (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : (dualComplex (K ⊞ L)).homology n) :
    (cohomologyBiprodEquiv K L n a).1 =
      (HomologicalComplex.homologyMap (dualMap (biprod.inl : K ⟶ K ⊞ L)) n).hom a := by
  let F := dualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n
  let : F.Additive := inferInstanceAs ((dualFunctor ⋙
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

theorem cohomologyBiprodEquiv_snd (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : (dualComplex (K ⊞ L)).homology n) :
    (cohomologyBiprodEquiv K L n a).2 =
      (HomologicalComplex.homologyMap (dualMap (biprod.inr : L ⟶ K ⊞ L)) n).hom a := by
  let F := dualFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n
  let : F.Additive := inferInstanceAs ((dualFunctor ⋙
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

variable {K L N : ChainComplex (ModuleCat.{0} ℤ) ℕ}

theorem dualMap_neg (f : K ⟶ L) : dualMap (-f) = -dualMap f :=
  dualFunctor.map_neg (f := f.op)

/-- A genuine dual sum map gives exactly the two original integral pullbacks. -/
theorem cohomologyBiprodEquiv_map_desc (f : K ⟶ N) (g : L ⟶ N) (n : ℕ)
    (a : (dualComplex N).homology n) :
    cohomologyBiprodEquiv K L n
        ((HomologicalComplex.homologyMap (dualMap (biprod.desc f g)) n).hom a) =
      ((HomologicalComplex.homologyMap (dualMap f) n).hom a,
        (HomologicalComplex.homologyMap (dualMap g) n).hom a) := by
  apply Prod.ext
  · rw [cohomologyBiprodEquiv_fst]
    have he := HomologicalComplex.homologyMap_comp (dualMap (biprod.desc f g))
      (dualMap (biprod.inl : K ⟶ K ⊞ L)) n
    rw [← dualMap_comp, biprod.inl_desc] at he
    exact (congrArg (fun h => h.hom a) he).symm
  · rw [cohomologyBiprodEquiv_snd]
    have he := HomologicalComplex.homologyMap_comp (dualMap (biprod.desc f g))
      (dualMap (biprod.inr : L ⟶ K ⊞ L)) n
    rw [← dualMap_comp, biprod.inr_desc] at he
    exact (congrArg (fun h => h.hom a) he).symm

/-- Original integral diagonal pullback is the sum of the actual coordinate pullbacks. -/
theorem cohomologyBiprodEquiv_map_lift (f : N ⟶ K) (g : N ⟶ L) (n : ℕ)
    (a : (dualComplex (K ⊞ L)).homology n) :
    (HomologicalComplex.homologyMap (dualMap (biprod.lift f g)) n).hom a =
      (HomologicalComplex.homologyMap (dualMap f) n).hom (cohomologyBiprodEquiv K L n a).1 +
        (HomologicalComplex.homologyMap (dualMap g) n).hom (cohomologyBiprodEquiv K L n a).2 := by
  have hl : biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have he := congrArg (fun h => HomologicalComplex.homologyMap (dualMap h) n) hl
  rw [dualMap_add, dualMap_comp, dualMap_comp, HomologicalComplex.homologyMap_add,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  rw [cohomologyBiprodEquiv_fst, cohomologyBiprodEquiv_snd]
  exact congrArg (fun h => h.hom a) he

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCochainBiproduct
