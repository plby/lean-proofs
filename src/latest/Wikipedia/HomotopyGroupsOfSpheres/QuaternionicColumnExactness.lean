import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnConnecting
import Wikipedia.HomotopyGroupsOfSpheres.Basic

/-!
# Exactness at the fiber of every quaternionic column projection

The image of the constructed connecting map consists exactly of the
homotopy classes in the fiber that become null-homotopic in the total quaternionic matrix group.
This is proved by lifting and projecting genuine relative cube homotopies.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.CubeFirstCoordinate
open HopfProblem.SecondHurewicz

variable {N : Type} [Fintype N] [DecidableEq N] {j : N}
variable {n : ℕ}

/-- The inclusion of the actual fiber subgroup into the total space. -/
def inclusion : C((axisSubgroup j), (SpGroup N)) := ⟨Subtype.val, continuous_subtype_val⟩

def inclusionMap (n : ℕ) [NeZero n] :
    HomotopyGroup (Fin n) (axisSubgroup j) 1 →* HomotopyGroup (Fin n) (SpGroup N) 1 :=
  map inclusion 1

theorem endpoint_inclusion_nullhomotopic
    {p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)} (L : CubeLift p) :
    GenLoop.Homotopic (mapGenLoop inclusion 1 L.endpoint) GenLoop.const := by
  let H : (GenLoop.const : GenLoop (Fin n) (SpGroup N) 1).val.HomotopyRel
      (mapGenLoop inclusion 1 L.endpoint).val (Cube.boundary (Fin n)) := {
    toContinuousMap := L.map
    map_zero_left := L.initial
    map_one_left := fun _ => rfl
    prop' := fun t u hu => L.boundary t u hu }
  exact ⟨H.symm⟩

theorem inclusionMap_connecting [NeZero n]
    (a : HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j)) :
    inclusionMap n (connecting n a) = 1 := by
  refine Quotient.inductionOn a fun p => ?_
  exact Quotient.sound (endpoint_inclusion_nullhomotopic (chosenLift p))

/-- A null-homotopy in the total space projects to a cube whose boundary is the original class. -/
theorem exists_connecting_of_nullhomotopic (q : GenLoop (Fin n) (axisSubgroup j) 1)
    (hq : GenLoop.Homotopic (mapGenLoop inclusion 1 q) GenLoop.const) :
    ∃ p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j),
      connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j)) =
        (⟦q⟧ : HomotopyGroup (Fin n) (axisSubgroup j) 1) := by
  obtain ⟨H⟩ := hq
  let F := H.symm
  let p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j) :=
    ⟨(column j).comp (F.toContinuousMap.comp (split n)), by
      intro u hu
      change (column j) (F (split n u)) = (axisColumn j)
      rcases (boundary_split_iff n u).mp hu with h₀ | h₁ | hb
      · change (column j) (F ((split n u).1, (split n u).2)) = (axisColumn j)
        rw [h₀]
        exact (congrArg (column j) (F.map_zero_left _)).trans (column_one j)
      · change (column j) (F ((split n u).1, (split n u).2)) = (axisColumn j)
        rw [h₁]
        exact (congrArg (column j) (F.map_one_left _)).trans (q ((split n u).2)).property
      · rw [show F (split n u) = 1 from F.eq_fst (split n u).1 hb]
        exact (column_one j)⟩
  let L : CubeLift p := {
    map := F.toContinuousMap
    initial := F.map_zero_left
    project := fun t u => by
      change (column j) (F (t, u)) = (column j) (F (split n (join n (t, u))))
      rw [split_join]
    boundary := fun t u hu => F.eq_fst t hu }
  have he : L.endpoint = q := by
    apply GenLoop.ext
    intro u
    apply Subtype.ext
    exact F.map_one_left u
  exact ⟨p, (connecting_eq_endpoint p L).trans (congrArg Quotient.mk' he)⟩

/-- Exactness at the native homotopy group of the fiber. -/
theorem connecting_range_eq_kernel [NeZero n]
    (a : HomotopyGroup (Fin n) (axisSubgroup j) 1) :
    (∃ b : HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j), connecting n b = a) ↔
      inclusionMap n a = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact inclusionMap_connecting b
  · refine Quotient.inductionOn a fun q hq => ?_
    obtain ⟨p, hp⟩ := exists_connecting_of_nullhomotopic q (Quotient.exact hq)
    exact ⟨⟦p⟧, hp⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
