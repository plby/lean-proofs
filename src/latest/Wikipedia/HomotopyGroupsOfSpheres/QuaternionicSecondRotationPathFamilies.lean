import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumFamilies
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonFamilyPaths

/-! # Continuous minimum-rotation path families and their exact polygon samples -/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.UniformTimePartition

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

def rotationPathFamily {a : ComplexStructures.Space n}
    (P : C(X, AnticommutingStructures.Space a)) : C(unitInterval × X, ComplexStructures.Space n) :=
  let R : C(ℝ × AnticommutingStructures.Space a, ComplexStructures.Space n) :=
    ⟨fun z ↦ AnticommutingStructures.rotation z.2 z.1,
      AnticommutingStructures.continuous_rotation a⟩
  R.comp ⟨fun z ↦ ((z.1 : ℝ) * Real.pi, P z.2),
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
      (P.continuous.comp continuous_snd)⟩

def minimumPathParameters (F : C(unitInterval × X, ComplexStructures.Space n))
    (a : ComplexStructures.Space n) : Set X :=
  {x | ∃ P : AnticommutingStructures.Space a,
    ∀ u : unitInterval, F (u, x) = AnticommutingStructures.rotation P ((u : ℝ) * Real.pi)}

theorem rotation_eq_of_paths {a : ComplexStructures.Space n}
    (P Q : AnticommutingStructures.Space a)
    (h : ∀ u : unitInterval, AnticommutingStructures.rotation P ((u : ℝ) * Real.pi) =
      AnticommutingStructures.rotation Q ((u : ℝ) * Real.pi)) : P = Q := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have he := h half
  have hcoef : (half : ℝ) * Real.pi = Real.pi / 2 := by dsimp only [half]; ring
  rw [hcoef, AnticommutingStructures.rotation_half_pi,
    AnticommutingStructures.rotation_half_pi] at he
  exact Subtype.ext he

theorem realizedFamily_rotation (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (hzero : τ 0 = 0)
    (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ P : AnticommutingStructures.Space a, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)
    (P : C(X, AnticommutingStructures.Space a))
    (hp : ∀ x, rotationFamilyVertices τ P x ∈ admissible a b m) :
    realizedFamily a b τ hτ (rotationFamilyVertices τ P) hp = rotationPathFamily P := by
  apply ContinuousMap.ext
  intro z
  exact path_rotationVertices a b τ hzero hone hanti (P z.2) (hsmall (P z.2))
    hτ (t := (z.1 : ℝ)) z.1.property

theorem uniform_vertices_eq_rotation_of_path (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (P : AnticommutingStructures.Space a)
    (hpath : ∀ u : unitInterval, path a b (time m) (strictMono_time m) v hv (u : ℝ) =
      AnticommutingStructures.rotation P ((u : ℝ) * Real.pi)) :
    v = rotationVertices (time m) P := by
  funext i
  have he := hpath (unitTime m i.castSucc.succ)
  change path a b (time m) (strictMono_time m) v hv (time m i.castSucc.succ) =
    AnticommutingStructures.rotation P (time m i.castSucc.succ * Real.pi) at he
  rw [path_vertex, vertices_interior] at he
  exact he

theorem uniform_mem_minimumSet_of_path (a b : ComplexStructures.Space n)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ P : AnticommutingStructures.Space a, ∀ i : Fin (m + 1),
      ‖(time m i.succ - time m i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (P : AnticommutingStructures.Space a)
    (hpath : ∀ u : unitInterval, path a b (time m) (strictMono_time m) v hv (u : ℝ) =
      AnticommutingStructures.rotation P ((u : ℝ) * Real.pi)) :
    v ∈ minimumSet a b (time m) := by
  rw [uniform_vertices_eq_rotation_of_path a b v hv P hpath]
  exact rotationVertices_mem_minimumSet a b (time m) (strictMono_time m)
    (time_zero m) (time_last m) hanti hsmall P

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
