import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Actual smooth multipliers and complex scalar sheaf endomorphisms

Every global smooth complex-valued function acts on the actual additive
smooth-function sheaf by pointwise multiplication.  These morphisms
commute with literal restriction and form a ring homomorphism into the
endomorphism ring.  In particular, complex constants give the actual
complex scalar action needed for cohomology.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Actual bundled global smooth complex-valued functions. -/
abbrev GlobalFunction := ContMDiffMap I 𝓘(ℝ, ℂ) M ℂ ∞

/-- Literal restriction of a genuine global smooth function. -/
def globalRestriction (g : GlobalFunction I M) (U : Opens M) : Section I M U :=
  ⟨fun x => g x, fun x => contMDiffAt_subtype_iff.mpr (g.contMDiff x)⟩

@[simp] theorem globalRestriction_apply (g : GlobalFunction I M) (U : Opens M) (x : U) :
    globalRestriction I M g U x = g x := rfl

/-- Pointwise extensionality for actual additive smooth sheaf endomorphisms. -/
theorem sheafEnd_ext {f g : additiveSheaf I M ⟶ additiveSheaf I M}
    (h : ∀ (U : Opens M) (s : Section I M U) (x : U),
      (f.hom.app (op U) s : Section I M U) x =
        (g.hom.app (op U) s : Section I M U) x) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact ContMDiffMap.ext (h U.unop s)

/-- Multiplication by an actual smooth global function on every open set. -/
def multiplier (g : GlobalFunction I M) : additiveSheaf I M ⟶ additiveSheaf I M where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        ({ toFun := fun f => globalRestriction I M g U.unop * f
           map_zero' := mul_zero _
           map_add' := mul_add _ } : Section I M U.unop →+ Section I M U.unop)
      naturality := fun U V h => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro f
        apply ContMDiffMap.ext
        intro x
        rfl }

@[simp] theorem multiplier_apply (g : GlobalFunction I M) (U : Opens M)
    (f : Section I M U) (x : U) :
    ((multiplier I M g).hom.app (op U) f : Section I M U) x = g x * f x := rfl

/-- Actual smooth multiplication is a ring homomorphism into the sheaf
endomorphism ring, whose multiplication is composition. -/
def multiplierRingHom : GlobalFunction I M →+* End (additiveSheaf I M) where
  toFun := multiplier I M
  map_zero' := by
    apply sheafEnd_ext I M
    intro U s x
    exact zero_mul (s x)
  map_one' := by
    apply sheafEnd_ext I M
    intro U s x
    exact one_mul (s x)
  map_add' f g := by
    apply sheafEnd_ext I M
    intro U s x
    exact add_mul (f x) (g x) (s x)
  map_mul' f g := by
    apply sheafEnd_ext I M
    intro U s x
    exact mul_assoc (f x) (g x) (s x)

/-- Complex constants as actual global smooth functions. -/
def constantGlobalRingHom : ℂ →+* GlobalFunction I M where
  toFun c := ⟨fun _ => c, contMDiff_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual complex scalar action on the smooth-function sheaf. -/
def scalarEnd : ℂ →+* End (additiveSheaf I M) :=
  (multiplierRingHom I M).comp (constantGlobalRingHom I M)

/-- The scalar sheaf endomorphism acts by literal complex multiplication. -/
@[simp] theorem scalarEnd_apply (c : ℂ) (U : Opens M) (f : Section I M U) (x : U) :
    ((scalarEnd I M c).asHom.hom.app (op U) f : Section I M U) x = c * f x := rfl

/-- This action agrees with the pointwise complex module on sections. -/
theorem scalarEnd_eq_smul (c : ℂ) (U : Opens M) (f : Section I M U) :
    (scalarEnd I M c).asHom.hom.app (op U) f = c • f := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions
