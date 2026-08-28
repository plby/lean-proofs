import Wikipedia.HopfProblem.CuspNormalizationSheafReducedPredicate
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reduced rings of actual locally ambient-holomorphic functions

Each section ring is literally a subring of the ring of actual complex
functions on its relative open domain. In particular it is reduced.
Evaluation, constants, complex scalars and restriction all have their
ordinary pointwise formulas.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- The actual subring of functions that locally extend holomorphically
to the ambient complex-charted space. -/
def sectionSubring (U : Opens S) : Subring (U → ℂ) where
  carrier := {f | IsLocallyAmbient I S U f}
  zero_mem' := IsLocallyAmbient.const I S U 0
  one_mem' := IsLocallyAmbient.const I S U 1
  add_mem' := IsLocallyAmbient.add I S
  mul_mem' := IsLocallyAmbient.mul I S
  neg_mem' := IsLocallyAmbient.neg I S

/-- A reduced holomorphic section is an actual function with proved
local ambient holomorphic extensions. -/
abbrev Section (U : Opens S) := ↥(sectionSubring I S U)

instance sectionCoeFun (U : Opens S) : CoeFun (Section I S U) (fun _ => U → ℂ) where
  coe f := f.val

@[ext] theorem Section.ext {U : Opens S} {f g : Section I S U}
    (h : ∀ x : U, f x = g x) : f = g := Subtype.ext (funext h)

theorem Section.locallyAmbient {U : Opens S} (f : Section I S U) :
    IsLocallyAmbient I S U (fun x => f x) := f.property

/-- Pointwise complex functions have no nonzero nilpotents, and the
literal subring inherits this property. -/
instance section_isReduced (U : Opens S) : IsReduced (Section I S U) :=
  isReduced_of_injective (sectionSubring I S U).subtype Subtype.val_injective

/-- Literal restriction of actual sections. -/
def restriction {U V : Opens S} (h : U ≤ V) : Section I S V →+* Section I S U where
  toFun f := ⟨fun x => f (Set.inclusion h x), IsLocallyAmbient.restrict I S h f.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem restriction_apply {U V : Opens S} (h : U ≤ V)
    (f : Section I S V) (x : U) :
    restriction I S h f x = f (Set.inclusion h x) := rfl

@[simp] theorem restriction_refl (U : Opens S) (f : Section I S U) :
    restriction I S le_rfl f = f := rfl

theorem restriction_trans {U V W : Opens S} (hUV : U ≤ V) (hVW : V ≤ W)
    (f : Section I S W) :
    restriction I S hUV (restriction I S hVW f) = restriction I S (hUV.trans hVW) f := rfl

/-- Evaluation is the actual evaluation of the underlying function. -/
def eval (U : Opens S) (x : U) : Section I S U →+* ℂ :=
  (Pi.evalRingHom _ x).comp (sectionSubring I S U).subtype

@[simp] theorem eval_apply (U : Opens S) (x : U) (f : Section I S U) :
    eval I S U x f = f x := rfl

/-- The actual constant section with a prescribed complex value. -/
def constant (U : Opens S) : ℂ →+* Section I S U where
  toFun c := ⟨fun _ => c, IsLocallyAmbient.const I S U c⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem constant_apply (U : Opens S) (c : ℂ) (x : U) :
    constant I S U c x = c := rfl

@[simp] theorem eval_constant (U : Opens S) (x : U) (c : ℂ) :
    eval I S U x (constant I S U c) = c := rfl

theorem eval_surjective (U : Opens S) (x : U) : Function.Surjective (eval I S U x) :=
  fun c => ⟨constant I S U c, rfl⟩

theorem constant_injective (U : Opens S) (x : U) : Function.Injective (constant I S U) :=
  Function.LeftInverse.injective (g := eval I S U x) (fun _ => rfl)

@[simp] theorem restriction_constant {U V : Opens S} (h : U ≤ V) (c : ℂ) :
    restriction I S h (constant I S V c) = constant I S U c := rfl

/-- The complex algebra structure is the pointwise constant scalar map. -/
instance section_algebra (U : Opens S) : Algebra ℂ (Section I S U) :=
  (constant I S U).toAlgebra

@[simp] theorem algebraMap_apply (U : Opens S) (c : ℂ) (x : U) :
    algebraMap ℂ (Section I S U) c x = c := rfl

@[simp] theorem smul_apply (U : Opens S) (c : ℂ) (f : Section I S U) (x : U) :
    (c • f) x = c * f x := rfl

/-- Actual restriction is complex-linear as well as a ring map. -/
def restrictionAlgHom {U V : Opens S} (h : U ≤ V) :
    Section I S V →ₐ[ℂ] Section I S U where
  __ := restriction I S h
  commutes' _ := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
