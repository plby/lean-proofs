import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionEvaluation
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionExact
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingLocal

/-!
# Actual extension evaluations on opens contained in a cover member

On `V ≤ U i`, the coordinate morphism followed by literal restriction
gives an additive map from the actual extension sections on `V` to
the original sheaf sections on `V`. It is the identity on the included
original sheaf. For any actual degree-`n` extension section, the
difference of two such evaluations is `n` times the original cocycle.
The proof uses the actual kernel of the extension, not an assumed
representative or injectivity of the constant-sheaf unit.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- The actual coordinate on an open contained in `U i`, with target
the literal section group on that same open. -/
def localEvaluationHom (i : ι) {V : Opens X} (hi : V ≤ U i) :
    Section (extensionSheaf c) V →+ Section F V :=
  (res F (le_inf le_rfl hi)).comp ((evaluation c i).hom.app (op V)).hom

theorem localEvaluationHom_apply (i : ι) {V : Opens X} (hi : V ≤ U i)
    (e : Section (extensionSheaf c) V) :
    localEvaluationHom c i hi e =
      res F (le_inf le_rfl hi) ((evaluation c i).hom.app (op V) e) := rfl

/-- Each actual local evaluation is the identity on the included
original section group. -/
@[simp] theorem localEvaluationHom_inclusion (i : ι) {V : Opens X} (hi : V ≤ U i)
    (a : Section F V) :
    localEvaluationHom c i hi ((inclusion c).hom.app (op V) a) = a := by
  rw [localEvaluationHom_apply, evaluation_app_inclusion, res_trans, res_refl]

/-- On an actual presheaf-unit section, local evaluation is the
literal coordinate restricted back to `V`. -/
@[simp] theorem localEvaluationHom_app_unit (i : ι) {V : Opens X} (hi : V ≤ U i)
    (s : ExtensionSection c V) :
    localEvaluationHom c i hi ((unit c).app (op V) s) =
      res F (le_inf le_rfl hi) (coordinateHom c V i s) := by
  rw [localEvaluationHom_apply, evaluation_app_unit]

/-- The actual raw cocycle condition gives the difference formula
on all presheaf-unit sections, with the original positive sign. -/
theorem localEvaluationHom_app_unit_difference (V : Opens X) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : ExtensionSection c V) :
    localEvaluationHom c i hi ((unit c).app (op V) s) -
      localEvaluationHom c j hj ((unit c).app (op V) s) =
        (degreeHom c V s).down • res F (le_inf hi hj) (c.value i j) := by
  rw [localEvaluationHom_app_unit, localEvaluationHom_app_unit]
  change res F (le_inf le_rfl hi) (s.1.2 i) - res F (le_inf le_rfl hj) (s.1.2 j) =
    s.1.1.down • res F (le_inf hi hj) (c.value i j)
  have h := congrArg (res F (le_inf le_rfl (le_inf hi hj))) (s.2 i j)
  simpa only [map_sub, map_zsmul, res_trans] using h

/-- Every actual extension-sheaf section whose projection is the
integer representative `n` has evaluation difference `n • c i j`.
Kernel exactness supplies the comparison with a constructed local lift. -/
theorem localEvaluationHom_difference
    (hU : ∀ x : X, ∃ i : ι, x ∈ U i) (V : Opens X) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) (n : ULift.{0} ℤ)
    (e : Section (extensionSheaf c) V)
    (hp : (projection c).hom.app (op V) e = (degreeUnit X).app (op V) n) :
    localEvaluationHom c i hi e - localEvaluationHom c j hj e =
      n.down • res F (le_inf hi hj) (c.value i j) := by
  let t : ExtensionSection c V := localLiftHom c i hi n
  have hker : (projection c).hom.app (op V) (e - (unit c).app (op V) t) = 0 := by
    rw [map_sub, hp, projection_app_unit]
    change (degreeUnit X).app (op V) n - (degreeUnit X).app (op V) n = 0
    exact sub_self _
  obtain ⟨a, ha⟩ : ∃ a : Section F V,
      (inclusion c).hom.app (op V) a = e - (unit c).app (op V) t :=
    section_kernel_lift (complex_shortExact c hU) (e - (unit c).app (op V) t) hker
  have he : e = (inclusion c).hom.app (op V) a + (unit c).app (op V) t :=
    (eq_sub_iff_add_eq.mp ha).symm
  calc
    localEvaluationHom c i hi e - localEvaluationHom c j hj e =
        localEvaluationHom c i hi ((unit c).app (op V) t) -
        localEvaluationHom c j hj ((unit c).app (op V) t) := by
      rw [he, map_add, map_add, localEvaluationHom_inclusion c i hi a,
        localEvaluationHom_inclusion c j hj a]
      abel
    _ = n.down • res F (le_inf hi hj) (c.value i j) := by
      simpa only [t, localLiftHom_degree] using
        localEvaluationHom_app_unit_difference c V i j hi hj t

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
