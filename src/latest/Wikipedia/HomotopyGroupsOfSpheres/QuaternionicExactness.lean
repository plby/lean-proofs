import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicConnecting
import Wikipedia.HomotopyGroupsOfSpheres.Basic

/-!
# Exactness at the fiber for `S³ → Sp(2) → S⁷`

The image of the constructed connecting map consists exactly of the
homotopy classes in the fiber that become null-homotopic in `Sp(2)`.
This is proved by lifting and projecting genuine relative cube homotopies.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open NoExoticSixSphere.CubeFirstCoordinate
open HopfProblem.SecondHurewicz

variable {n : ℕ}

/-- The inclusion of the actual fiber subgroup into the total space. -/
def inclusion : C(northSubgroup, SpTwo) := ⟨Subtype.val, continuous_subtype_val⟩

def inclusionMap (n : ℕ) [NeZero n] :
    HomotopyGroup (Fin n) northSubgroup 1 →* HomotopyGroup (Fin n) SpTwo 1 :=
  map inclusion 1

theorem endpoint_inclusion_nullhomotopic
    {p : GenLoop (Fin (n + 1)) BaseSphere north} (L : CubeLift p) :
    GenLoop.Homotopic (mapGenLoop inclusion 1 L.endpoint) GenLoop.const := by
  let H : (GenLoop.const : GenLoop (Fin n) SpTwo 1).val.HomotopyRel
      (mapGenLoop inclusion 1 L.endpoint).val (Cube.boundary (Fin n)) := {
    toContinuousMap := L.map
    map_zero_left := L.initial
    map_one_left := fun _ => rfl
    prop' := fun t u hu => L.boundary t u hu }
  exact ⟨H.symm⟩

theorem inclusionMap_connecting [NeZero n]
    (a : HomotopyGroup (Fin (n + 1)) BaseSphere north) :
    inclusionMap n (connecting n a) = 1 := by
  refine Quotient.inductionOn a fun p => ?_
  exact Quotient.sound (endpoint_inclusion_nullhomotopic (chosenLift p))

/-- A null-homotopy in the total space projects to a cube whose boundary is the original class. -/
theorem exists_connecting_of_nullhomotopic (q : GenLoop (Fin n) northSubgroup 1)
    (hq : GenLoop.Homotopic (mapGenLoop inclusion 1 q) GenLoop.const) :
    ∃ p : GenLoop (Fin (n + 1)) BaseSphere north,
      connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) BaseSphere north) =
        (⟦q⟧ : HomotopyGroup (Fin n) northSubgroup 1) := by
  obtain ⟨H⟩ := hq
  let F := H.symm
  let p : GenLoop (Fin (n + 1)) BaseSphere north :=
    ⟨projection.comp (F.toContinuousMap.comp (split n)), by
      intro u hu
      change projection (F (split n u)) = north
      rcases (boundary_split_iff n u).mp hu with h₀ | h₁ | hb
      · change projection (F ((split n u).1, (split n u).2)) = north
        rw [h₀]
        exact (congrArg projection (F.map_zero_left _)).trans projection_one
      · change projection (F ((split n u).1, (split n u).2)) = north
        rw [h₁]
        exact (congrArg projection (F.map_one_left _)).trans (q ((split n u).2)).property
      · rw [show F (split n u) = 1 from F.eq_fst (split n u).1 hb]
        exact projection_one⟩
  let L : CubeLift p := {
    map := F.toContinuousMap
    initial := F.map_zero_left
    project := fun t u => by
      change projection (F (t, u)) = projection (F (split n (join n (t, u))))
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
    (a : HomotopyGroup (Fin n) northSubgroup 1) :
    (∃ b : HomotopyGroup (Fin (n + 1)) BaseSphere north, connecting n b = a) ↔
      inclusionMap n a = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact inclusionMap_connecting b
  · refine Quotient.inductionOn a fun q hq => ?_
    obtain ⟨p, hp⟩ := exists_connecting_of_nullhomotopic q (Quotient.exact hq)
    exact ⟨⟦p⟧, hp⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
