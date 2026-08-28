import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic

/-!
# The actual sheaf of smooth complex-valued functions

The sections are bundled real `C^∞` maps into `ℂ`, on the actual open
submanifolds.  Restriction is literal restriction of functions, and the
sheaf condition is supplied by the proved local-invariant-property sheaf
construction.  This is a real smooth-function sheaf, not the holomorphic
function sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions

/-- Complex multiplication is smooth in the underlying real charts. -/
instance complex_contMDiffRing (n : ℕ∞ω) : ContMDiffRing 𝓘(ℝ, ℂ) n ℂ :=
  { instNormedSpaceLieAddGroup with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps, chartAt_self_eq]
      rw [contDiffOn_univ]
      exact contDiff_mul }

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The genuine smooth complex-valued functions on an actual open set. -/
abbrev Section (U : Opens M) := ContMDiffMap I 𝓘(ℝ, ℂ) U ℂ ∞

/-- The sheaf of actual smooth functions, initially valued in types. -/
def typeSheaf : TopCat.Sheaf (Type) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := I) (I' := 𝓘(ℝ, ℂ)) ∞).sheaf M ℂ

/-- Its sections are definitionally the actual bundled smooth maps. -/
theorem typeSheaf_obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (typeSheaf I M).presheaf.obj U = Section I M U.unop := rfl

/-- Pointwise ring operations and literal smooth restriction maps. -/
def presheaf : TopCat.Presheaf CommRingCat (TopCat.of M) where
  obj U := CommRingCat.of (Section I M U.unop)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom I 𝓘(ℝ, ℂ) ℂ (CategoryTheory.leOfHom h.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((presheaf I M).obj U) (fun _ => U.unop → ℂ) where
  coe f := f.1

/-- The actual ring-valued smooth-function sheaf. -/
def sheaf : TopCat.Sheaf CommRingCat (TopCat.of M) where
  obj := presheaf I M
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (typeSheaf I M).property

instance sheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((sheaf I M).presheaf.obj U) (fun _ => U.unop → ℂ) where
  coe f := f.1

/-- Forgetting the ring operations recovers the proved local smooth-map
sheaf, with no extra gluing hypothesis. -/
theorem forget_sheaf :
    (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat)).obj (sheaf I M) =
      typeSheaf I M := rfl

/-- The actual additive smooth-function sheaf. -/
def additiveSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
    (sheaf I M)

instance additiveSheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((additiveSheaf I M).presheaf.obj U) (fun _ => U.unop → ℂ) where
  coe f := f.1

/-- Complex constants define genuine smooth sections on every open set. -/
def constantSectionRingHom (U : Opens M) : ℂ →+* Section I M U where
  toFun c := ⟨fun _ => c, contMDiff_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Actual complex scalar multiplication on smooth complex-valued
sections, despite differentiability being over the real field. -/
instance section_algebra (U : Opens M) : Algebra ℂ (Section I M U) :=
  (constantSectionRingHom I M U).toAlgebra

@[simp] theorem constantSectionRingHom_apply (U : Opens M) (c : ℂ) (x : U) :
    constantSectionRingHom I M U c x = c := rfl

@[simp] theorem smul_apply (U : Opens M) (c : ℂ) (f : Section I M U) (x : U) :
    (c • f) x = c * f x := rfl

instance additiveSheaf_obj_module (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ℂ ((additiveSheaf I M).presheaf.obj U) :=
  inferInstanceAs (Module ℂ (Section I M U.unop))

@[simp] theorem restriction_apply {U V : Opens M} (h : U ≤ V)
    (f : Section I M V) (x : U) :
    (presheaf I M).map (homOfLE h).op f x = f ⟨x, h x.property⟩ := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SmoothFunctions
