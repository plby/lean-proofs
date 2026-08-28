import Wikipedia.NoExoticSixSphere.FamilyDoublePointSymmetry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual double points of a single map as a zero-parameter family

The added parameter is a genuine zero-dimensional vector space. Projection
and insertion of its sole point give inverse homeomorphisms of the actual
double-point closures, commuting with the source swap.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.MapDoublePoints

variable {V Y : Type*} [TopologicalSpace V] (g : V → Y)

def points : Set (V × V) := {p | p.1 ≠ p.2 ∧ g p.1 = g p.2}

theorem swap_mem_closure {p : V × V} (hp : p ∈ closure (points g)) :
    Prod.swap p ∈ closure (points g) :=
  (show MapsTo Prod.swap (points g) (points g) from
    fun _ hq ↦ ⟨hq.1.symm, hq.2.symm⟩).closure continuous_swap hp

def swapClosure : closure (points g) ≃ₜ closure (points g) where
  toFun p := ⟨Prod.swap p.val, swap_mem_closure g p.property⟩
  invFun p := ⟨Prod.swap p.val, swap_mem_closure g p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _

abbrev ZeroParameter := EuclideanSpace ℝ (Fin 0)

def asFamily : ZeroParameter → V → Y := fun _ ↦ g

theorem insert_mem_closure {p : V × V} (hp : p ∈ closure (points g)) :
    ((0 : ZeroParameter), p) ∈ closure (FamilyEmbedding.doublePoints (asFamily g)) :=
  (show MapsTo (fun q : V × V ↦ ((0 : ZeroParameter), q)) (points g)
    (FamilyEmbedding.doublePoints (asFamily g)) from fun _ hq ↦ hq).closure
      (continuous_const.prodMk continuous_id) hp

theorem project_mem_closure {p : ZeroParameter × (V × V)}
    (hp : p ∈ closure (FamilyEmbedding.doublePoints (asFamily g))) :
    p.2 ∈ closure (points g) :=
  (show MapsTo Prod.snd (FamilyEmbedding.doublePoints (asFamily g)) (points g) from
    fun _ hq ↦ hq).closure continuous_snd hp

def familyCoordinates : closure (points g) ≃ₜ
    closure (FamilyEmbedding.doublePoints (asFamily g)) where
  toFun p := ⟨(0, p.val), insert_mem_closure g p.property⟩
  invFun p := ⟨p.val.2, project_mem_closure g p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _p := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  continuous_toFun :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _

theorem familyCoordinates_swap (p : closure (points g)) :
    familyCoordinates g (swapClosure g p) =
      FamilyEmbedding.swapClosure (asFamily g) (familyCoordinates g p) :=
  Subtype.ext rfl

end NoExoticSixSphere.MapDoublePoints
