import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Splitting off the first coordinate of the native parameter cube
-/

namespace NoExoticSixSphere.CubeFirstCoordinate

noncomputable def split (d : ℕ) :
    C((Fin (d + 1) → unitInterval), unitInterval × (Fin d → unitInterval)) where
  toFun t := (t 0, Fin.tail t)
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun i ↦ continuous_apply i.succ))

noncomputable def join (d : ℕ) :
    C(unitInterval × (Fin d → unitInterval), (Fin (d + 1) → unitInterval)) where
  toFun t := Fin.cons t.1 t.2
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd

theorem join_split (d : ℕ) (t : Fin (d + 1) → unitInterval) : join d (split d t) = t :=
  Fin.cons_self_tail t

theorem split_join (d : ℕ) (t : unitInterval × (Fin d → unitInterval)) :
    split d (join d t) = t := by
  rcases t with ⟨s, t⟩
  rfl

theorem boundary_split_iff (d : ℕ) (t : Fin (d + 1) → unitInterval) :
    t ∈ Cube.boundary (Fin (d + 1)) ↔
      (split d t).1 = 0 ∨ (split d t).1 = 1 ∨ (split d t).2 ∈ Cube.boundary (Fin d) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
    | succ i => exact Or.inr (Or.inr ⟨i, hi⟩)
  · rintro (h | h | ⟨i, hi⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · exact ⟨i.succ, hi⟩

theorem boundary_join_iff (d : ℕ) (t : unitInterval × (Fin d → unitInterval)) :
    join d t ∈ Cube.boundary (Fin (d + 1)) ↔
      t.1 = 0 ∨ t.1 = 1 ∨ t.2 ∈ Cube.boundary (Fin d) := by
  rw [boundary_split_iff, split_join]

end NoExoticSixSphere.CubeFirstCoordinate
