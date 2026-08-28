import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The full native holomorphic automorphism group

Every analytic diffeomorphism of the original complex manifold is an
element. Multiplication is ordinary composition: the right factor acts
first. No subgroup generation or additional regularity condition is used.
-/

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]

/-- All native complex analytic self-diffeomorphisms, with a dedicated
type on which to put the usual automorphism-group topology. -/
structure HolomorphicAutomorphism (I : ModelWithCorners ℂ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] where
  toDiffeomorph : Diffeomorph I I M M ω

namespace HolomorphicAutomorphism

variable {I : ModelWithCorners ℂ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]

noncomputable instance : FunLike (HolomorphicAutomorphism I M) M M where
  coe f := f.toDiffeomorph
  coe_injective := by
    intro f g h
    cases f with
    | mk f =>
      cases g with
      | mk g =>
        have he : f = g := Diffeomorph.coeFn_injective h
        cases he
        rfl

@[ext] theorem ext {f g : HolomorphicAutomorphism I M} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Every native analytic diffeomorphism gives an automorphism. -/
def ofDiffeomorph (f : Diffeomorph I I M M ω) : HolomorphicAutomorphism I M := ⟨f⟩

@[simp] theorem toDiffeomorph_ofDiffeomorph (f : Diffeomorph I I M M ω) :
    (ofDiffeomorph f).toDiffeomorph = f := rfl

@[simp] theorem ofDiffeomorph_toDiffeomorph (f : HolomorphicAutomorphism I M) :
    ofDiffeomorph f.toDiffeomorph = f := rfl

@[simp] theorem ofDiffeomorph_apply (f : Diffeomorph I I M M ω) (x : M) :
    ofDiffeomorph f x = f x := rfl

@[simp] theorem toDiffeomorph_apply (f : HolomorphicAutomorphism I M) (x : M) :
    f.toDiffeomorph x = f x := rfl

/-- The wrapper is equivalent to the complete native diffeomorphism type. -/
def equivDiffeomorph : HolomorphicAutomorphism I M ≃ Diffeomorph I I M M ω where
  toFun := toDiffeomorph
  invFun := ofDiffeomorph
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Group (HolomorphicAutomorphism I M) where
  one := ofDiffeomorph (Diffeomorph.refl I M ω)
  mul f g := ofDiffeomorph (g.toDiffeomorph.trans f.toDiffeomorph)
  inv f := ofDiffeomorph f.toDiffeomorph.symm
  mul_assoc f g h := ext fun _ => rfl
  one_mul f := ext fun _ => rfl
  mul_one f := ext fun _ => rfl
  inv_mul_cancel f := ext fun x => f.toDiffeomorph.symm_apply_apply x

@[simp] theorem one_apply (x : M) : (1 : HolomorphicAutomorphism I M) x = x := rfl

@[simp] theorem mul_apply (f g : HolomorphicAutomorphism I M) (x : M) :
    (f * g) x = f (g x) := rfl

@[simp] theorem inv_apply (f : HolomorphicAutomorphism I M) (x : M) :
    f⁻¹ x = f.toDiffeomorph.symm x := rfl

@[simp] theorem inv_apply_apply (f : HolomorphicAutomorphism I M) (x : M) :
    f⁻¹ (f x) = x := f.toDiffeomorph.symm_apply_apply x

@[simp] theorem apply_inv_apply (f : HolomorphicAutomorphism I M) (x : M) :
    f (f⁻¹ x) = x := f.toDiffeomorph.apply_symm_apply x

@[simp] theorem toDiffeomorph_mul (f g : HolomorphicAutomorphism I M) :
    (f * g).toDiffeomorph = g.toDiffeomorph.trans f.toDiffeomorph := rfl

@[simp] theorem toDiffeomorph_inv (f : HolomorphicAutomorphism I M) :
    (f⁻¹).toDiffeomorph = f.toDiffeomorph.symm := rfl

theorem holomorphic (f : HolomorphicAutomorphism I M) : ContMDiff I I ω f :=
  f.toDiffeomorph.contMDiff

theorem continuous (f : HolomorphicAutomorphism I M) : Continuous f :=
  f.toDiffeomorph.continuous

/-- The underlying native homeomorphism. -/
noncomputable def toHomeomorph (f : HolomorphicAutomorphism I M) : M ≃ₜ M :=
  f.toDiffeomorph.toHomeomorph

@[simp] theorem toHomeomorph_apply (f : HolomorphicAutomorphism I M) (x : M) :
    f.toHomeomorph x = f x := rfl

/-- The ordinary continuous map, used with its compact-open topology. -/
noncomputable def toContinuousMap (f : HolomorphicAutomorphism I M) : C(M, M) :=
  ⟨f, f.continuous⟩

@[simp] theorem toContinuousMap_apply (f : HolomorphicAutomorphism I M) (x : M) :
    f.toContinuousMap x = f x := rfl

@[simp] theorem toContinuousMap_one :
    (1 : HolomorphicAutomorphism I M).toContinuousMap = ContinuousMap.id M := rfl

@[simp] theorem toContinuousMap_mul (f g : HolomorphicAutomorphism I M) :
    (f * g).toContinuousMap = f.toContinuousMap.comp g.toContinuousMap := rfl

theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : HolomorphicAutomorphism I M → C(M, M)) := by
  intro f g h
  exact ext fun x => congrArg (fun u : C(M, M) => u x) h

/-- The map and its inverse, both as ordinary continuous maps. -/
noncomputable def toPair (f : HolomorphicAutomorphism I M) : C(M, M) × C(M, M) :=
  (f.toContinuousMap, (f⁻¹).toContinuousMap)

@[simp] theorem toPair_fst (f : HolomorphicAutomorphism I M) :
    f.toPair.1 = f.toContinuousMap := rfl

@[simp] theorem toPair_snd (f : HolomorphicAutomorphism I M) :
    f.toPair.2 = (f⁻¹).toContinuousMap := rfl

theorem toPair_injective :
    Function.Injective (toPair : HolomorphicAutomorphism I M → C(M, M) × C(M, M)) := by
  intro f g h
  exact toContinuousMap_injective (congrArg Prod.fst h)

/-- The full automorphism group acts on the unchanged underlying manifold. -/
noncomputable instance : MulAction (HolomorphicAutomorphism I M) M where
  smul f x := f x
  one_smul := one_apply
  mul_smul := mul_apply

@[simp] theorem smul_def (f : HolomorphicAutomorphism I M) (x : M) : f • x = f x := rfl

end HolomorphicAutomorphism

end Wikipedia.HopfProblem
