import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSplittingLocal
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionExact
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingLocal

/-!
# Genuine splitting is equivalent to actual Čech solvability

A global degree-one section is compared with the constructed local
degree-one sections. The actual kernel exactness gives local sections
of the original sheaf, and its actual monic inclusion proves their
differences equal the original cocycle. Conversely, an actual Čech
solution furnishes the constructed sheaf splitting. No local lifting,
kernel, or constant-unit injectivity premise is assumed.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- Any actual global degree-one section of the extension supplies
an actual solution of the given Čech cocycle. -/
theorem solvable_of_global_degreeOne
    (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (s : Section (extensionSheaf c) (⊤ : Opens X))
    (hs : (projection c).hom.app (op (⊤ : Opens X)) s =
      (degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))) : c.Solvable := by
  classical
  have hS := complex_shortExact c hU
  have hb (i : ι) : ∃ b : Section F (U i),
      (inclusion c).hom.app (op (U i)) b =
        res (extensionSheaf c) le_top s - localDegreeOneSection c i :=
    section_kernel_lift hS _ (projection_globalSection_sub_localDegreeOne c s hs i)
  choose b hb using hb
  refine ⟨b, ?_⟩
  intro i j
  apply section_f_injective hS (U i ⊓ U j)
  have hbi : (inclusion c).hom.app (op (U i ⊓ U j)) (res F inf_le_left (b i)) =
      res (extensionSheaf c) inf_le_left
        (res (extensionSheaf c) le_top s - localDegreeOneSection c i) :=
    (res_map (inclusion c) inf_le_left (b i)).symm.trans
      (congrArg (res (extensionSheaf c) inf_le_left) (hb i))
  have hbj : (inclusion c).hom.app (op (U i ⊓ U j)) (res F inf_le_right (b j)) =
      res (extensionSheaf c) inf_le_right
        (res (extensionSheaf c) le_top s - localDegreeOneSection c j) :=
    (res_map (inclusion c) inf_le_right (b j)).symm.trans
      (congrArg (res (extensionSheaf c) inf_le_right) (hb j))
  calc
    (inclusion c).hom.app (op (U i ⊓ U j))
        (res F inf_le_left (b i) - res F inf_le_right (b j)) =
        res (extensionSheaf c) inf_le_left
          (res (extensionSheaf c) le_top s - localDegreeOneSection c i) -
        res (extensionSheaf c) inf_le_right
          (res (extensionSheaf c) le_top s - localDegreeOneSection c j) := by
      rw [map_sub, hbi, hbj]
    _ = res (extensionSheaf c) inf_le_right (localDegreeOneSection c j) -
        res (extensionSheaf c) inf_le_left (localDegreeOneSection c i) := by
      rw [map_sub, map_sub, res_trans, res_trans]
      abel
    _ = (inclusion c).hom.app (op (U i ⊓ U j)) (c.value i j) :=
      localDegreeOneSection_difference c i j

/-- A genuine right inverse of the actual degree projection gives a
global degree-one section and hence an actual Čech solution. -/
theorem solvable_of_splitting (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
    (σ : degreeSheaf X ⟶ extensionSheaf c)
    (hσ : σ ≫ projection c = 𝟙 (degreeSheaf X)) : c.Solvable := by
  let n : Section (degreeSheaf X) (⊤ : Opens X) :=
    (degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))
  apply solvable_of_global_degreeOne c hU (σ.hom.app (op (⊤ : Opens X)) n)
  exact congrArg (fun f : degreeSheaf X ⟶ degreeSheaf X =>
    f.hom.app (op (⊤ : Opens X)) n) hσ

/-- The genuine extension splits precisely when its original actual
Čech cocycle is a coboundary. -/
theorem exists_splitting_iff_solvable (hU : ∀ x : X, ∃ i : ι, x ∈ U i) :
    (∃ σ : degreeSheaf X ⟶ extensionSheaf c,
      σ ≫ projection c = 𝟙 (degreeSheaf X)) ↔ c.Solvable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact solvable_of_splitting c hU σ hσ
  · exact exists_splitting_of_solvable c

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
