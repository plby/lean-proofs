import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech
import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersBasic

/-!
# The concrete presheaf attached to an additive Čech cocycle

Over `V`, a section consists of an integer `n` and sections `b i` on
`V ⊓ U i` whose differences are `n • c i j`. The integer is universe
lifted so its native constant sheaf is literally the source used by
mathlib's sheaf-cohomology definition. No cocycle solution is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- The cocycle identity after restriction to any actual common open set. -/
theorem cocycle_condition_restrict (i j k : ι) {V : Opens X}
    (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) :
    res F (le_inf hi hj) (c.value i j) + res F (le_inf hj hk) (c.value j k) =
      res F (le_inf hi hk) (c.value i k) := by
  have h := congrArg (res F (le_inf (le_inf hi hj) hk)) (c.condition i j k)
  simpa only [map_add, res_trans] using h

/-- The actual additive subgroup of integer-plus-local-section data. -/
def sectionSubgroup (V : Opens X) :
    AddSubgroup (ULift.{0} ℤ × ∀ i : ι, Section F (V ⊓ U i)) where
  carrier := {s | ∀ i j : ι,
    res F (inf_le_inf_left V inf_le_left) (s.2 i) -
      res F (inf_le_inf_left V inf_le_right) (s.2 j) =
        s.1.down • res F inf_le_right (c.value i j)}
  zero_mem' := by
    intro i j
    simp
  add_mem' := by
    intro a b ha hb i j
    change res F _ (a.2 i + b.2 i) - res F _ (a.2 j + b.2 j) =
      (a.1.down + b.1.down) • res F _ (c.value i j)
    rw [map_add, map_add, add_zsmul]
    calc
      _ = (res F _ (a.2 i) - res F _ (a.2 j)) +
          (res F _ (b.2 i) - res F _ (b.2 j)) := by abel
      _ = _ := by rw [ha i j, hb i j]
  neg_mem' := by
    intro a ha i j
    change res F _ (-a.2 i) - res F _ (-a.2 j) =
      (-a.1.down) • res F _ (c.value i j)
    rw [map_neg, map_neg, neg_zsmul]
    calc
      _ = -(res F _ (a.2 i) - res F _ (a.2 j)) := by abel
      _ = _ := by rw [ha i j]

/-- Actual sections of the extension presheaf. -/
abbrev ExtensionSection (V : Opens X) := ↥(sectionSubgroup c V)

@[ext] theorem extensionSection_ext {V : Opens X}
    {s t : ExtensionSection c V} (hn : s.1.1 = t.1.1)
    (hb : ∀ i : ι, s.1.2 i = t.1.2 i) : s = t :=
  Subtype.ext (Prod.ext hn (funext hb))

/-- Projection to the actual lifted integer coordinate. -/
def degreeHom (V : Opens X) : ExtensionSection c V →+ ULift.{0} ℤ where
  toFun s := s.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation at one local section coordinate. -/
def coordinateHom (V : Opens X) (i : ι) :
    ExtensionSection c V →+ Section F (V ⊓ U i) where
  toFun s := s.1.2 i
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem degreeHom_apply (V : Opens X) (s : ExtensionSection c V) :
    degreeHom c V s = s.1.1 := rfl

@[simp] theorem coordinateHom_apply (V : Opens X) (i : ι) (s : ExtensionSection c V) :
    coordinateHom c V i s = s.1.2 i := rfl

/-- Literal restriction of the local coordinates, preserving the degree. -/
def restrict {V W : Opens X} (hWV : W ≤ V) :
    ExtensionSection c V →+ ExtensionSection c W where
  toFun s := ⟨⟨s.1.1, fun i => res F (inf_le_inf_right (U i) hWV) (s.1.2 i)⟩, by
    intro i j
    have h := congrArg (res F (inf_le_inf_right (U i ⊓ U j) hWV)) (s.2 i j)
    simpa only [map_sub, map_zsmul, res_trans] using h⟩
  map_zero' := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact map_zero _
  map_add' s t := by
    apply extensionSection_ext
    · rfl
    · intro i
      exact map_add _ _ _

@[simp] theorem restrict_degree {V W : Opens X} (hWV : W ≤ V)
    (s : ExtensionSection c V) :
    degreeHom c W (restrict c hWV s) = degreeHom c V s := rfl

@[simp] theorem restrict_coordinate {V W : Opens X} (hWV : W ≤ V)
    (s : ExtensionSection c V) (i : ι) :
    coordinateHom c W i (restrict c hWV s) =
      res F (inf_le_inf_right (U i) hWV) (coordinateHom c V i s) := rfl

@[simp] theorem restrict_refl (V : Opens X) (s : ExtensionSection c V) :
    restrict c le_rfl s = s := by
  apply extensionSection_ext
  · rfl
  · intro i
    exact res_refl F (V ⊓ U i) (s.1.2 i)

theorem restrict_trans {V W T : Opens X} (hWV : W ≤ V) (hTW : T ≤ W)
    (s : ExtensionSection c V) :
    restrict c hTW (restrict c hWV s) = restrict c (hTW.trans hWV) s := by
  apply extensionSection_ext
  · rfl
  · intro i
    exact res_trans F _ _ _

/-- The genuine presheaf of cocycle-compatible integer and local data. -/
def presheaf : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj V := AddCommGrpCat.of (ExtensionSection c V.unop)
  map h := AddCommGrpCat.ofHom (restrict c (leOfHom h.unop))
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro s
    exact restrict_refl c V.unop s
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (restrict_trans c (leOfHom f.unop) (leOfHom g.unop) s).symm

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
