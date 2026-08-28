import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Evaluation on the genuine categorical holomorphic stalk

Evaluation at a point is a compatible family of ring homomorphisms on
the open-neighbourhood diagram. Its colimit map is therefore a ring
homomorphism from the actual sheaf stalk to the complex numbers.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Evaluation of genuine holomorphic sections on the actual
open-neighbourhood diagram of the point. -/
def stalkEvalCocone (x : M) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of M) x).op ⋙ presheaf I M) where
  pt := CommRingCat.of ℂ
  ι :=
    { app := fun U => CommRingCat.ofHom
        (ContMDiffMap.evalRingHom ⟨x, U.unop.2⟩)
      naturality := by
        intro U V i
        ext f
        rfl }

/-- The colimit-induced evaluation morphism of commutative rings. -/
def stalkEvalHom (x : M) : (presheaf I M).stalk x ⟶ CommRingCat.of ℂ :=
  colimit.desc _ (stalkEvalCocone I M x)

/-- Evaluation of an actual categorical holomorphic-function germ. -/
def stalkEval (x : M) : (presheaf I M).stalk x →+* ℂ :=
  (stalkEvalHom I M x).hom

/-- Every representative of a categorical germ gives the same value. -/
@[simp] theorem stalkEval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : Section I M U) :
    stalkEval I M x ((presheaf I M).germ U x hx f) = f ⟨x, hx⟩ := by
  exact congrArg (fun h => h f)
    (colimit.ι_desc (stalkEvalCocone I M x) (op ⟨U, hx⟩))

/-- Constants show that evaluation on the genuine stalk is surjective. -/
theorem stalkEval_surjective (x : M) : Function.Surjective (stalkEval I M x) := by
  intro c
  let f : Section I M ⊤ := ⟨fun _ => c, contMDiff_const⟩
  refine ⟨(presheaf I M).germ ⊤ x (by trivial) f, ?_⟩
  exact stalkEval_germ I M ⊤ x (by trivial) f

/-- A stalk at an actual point is nontrivial, since its evaluation maps
onto the nontrivial field of complex numbers. -/
instance stalk_nontrivial (x : M) : Nontrivial ((presheaf I M).stalk x) :=
  (stalkEval_surjective I M x).nontrivial

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
