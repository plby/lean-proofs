import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual additive Čech one-cocycles

A cocycle is a family of actual sections on the pairwise intersections
of an arbitrary open cover. Its identity is an equality after literal
restriction to each triple intersection. Solvability means that this
family is the difference of restrictions of actual local sections.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- Actual sections of an additive sheaf on an actual open set. -/
abbrev Section (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U : Opens X) :=
  F.obj.obj (op U)

/-- Literal restriction, with its actual additive-group homomorphism. -/
def res (F : TopCat.Sheaf AddCommGrpCat.{0} X) {U V : Opens X} (h : V ≤ U) :
    Section F U →+ Section F V :=
  (F.obj.map (homOfLE h).op).hom

@[simp] theorem res_refl (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (U : Opens X) (s : Section F U) : res F le_rfl s = s := by
  change F.obj.map (𝟙 (op U)) s = s
  exact congrArg (fun k => k s) (F.obj.map_id (op U))

/-- Successive actual restrictions are the restriction to the smaller open set. -/
theorem res_trans (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) (s : Section F U) :
    res F hWV (res F hVU s) = res F (hWV.trans hVU) s := by
  change F.obj.map (homOfLE hWV).op (F.obj.map (homOfLE hVU).op s) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A morphism of sheaves commutes with the literal restrictions. -/
theorem res_map {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    {U V : Opens X} (h : V ≤ U) (s : Section F U) :
    res G h (f.hom.app (op U) s) = f.hom.app (op V) (res F h s) := by
  exact congrArg (fun k => k s) (f.hom.naturality (homOfLE h).op).symm

/-- A Čech one-cocycle of actual additive sheaf sections. -/
structure CechOneCocycle (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {ι : Type} (U : ι → Opens X) where
  value : ∀ i j : ι, Section F (U i ⊓ U j)
  condition : ∀ i j k : ι,
    res F (V := (U i ⊓ U j) ⊓ U k) inf_le_left (value i j) +
      res F (V := (U i ⊓ U j) ⊓ U k)
        (inf_le_inf inf_le_right le_rfl) (value j k) =
      res F (V := (U i ⊓ U j) ⊓ U k)
        (inf_le_inf inf_le_left le_rfl) (value i k)

/-- An actual cocycle is solvable when it is the difference of actual
sections on the members of its open cover. -/
def CechOneCocycle.Solvable {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U) : Prop :=
  ∃ b : ∀ i : ι, Section F (U i), ∀ i j : ι,
    res F inf_le_left (b i) - res F inf_le_right (b j) = c.value i j

/-- Solvability on every actual open cover. This property is a concrete
input to the subsequent comparison with genuine sheaf cohomology. -/
def CechOneVanishing (F : TopCat.Sheaf AddCommGrpCat.{0} X) : Prop :=
  ∀ (ι : Type) (U : ι → Opens X), (∀ x : X, ∃ i : ι, x ∈ U i) →
    ∀ c : CechOneCocycle F U, c.Solvable

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
