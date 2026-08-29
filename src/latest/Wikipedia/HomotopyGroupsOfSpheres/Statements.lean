import Wikipedia.HomotopyGroupsOfSpheres.All

/-! # Proposition-valued statements of the main sphere homotopy-group calculations -/

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

theorem pi1_sphere_one (x : Sphere 1) :
    Nonempty (π_ 1 (Sphere 1) x ≃* Multiplicative ℤ) :=
  ⟨pi1_sphere_one_mulEquiv x⟩

theorem pi2_sphere_one (x : Sphere 1) : Nonempty (π_ 2 (Sphere 1) x ≃* PUnit) :=
  ⟨pi2_sphere_one_mulEquiv x⟩

theorem pi1_sphere_two (x : Sphere 2) : Nonempty (π_ 1 (Sphere 2) x ≃* PUnit) :=
  ⟨pi1_sphere_two_mulEquiv x⟩

theorem pi2_sphere_two (x : Sphere 2) :
    Nonempty (π_ 2 (Sphere 2) x ≃* Multiplicative ℤ) :=
  ⟨pi2_sphere_two_mulEquiv x⟩

theorem pi3_sphere_two (x : Sphere 2) :
    Nonempty (π_ 3 (Sphere 2) x ≃* Multiplicative ℤ) :=
  ⟨pi3_sphere_two_mulEquiv x⟩

theorem pi6_sphere_two (x : Sphere 2) :
    Nonempty (π_ 6 (Sphere 2) x ≃* Multiplicative (ZMod 12)) :=
  ⟨pi6_sphere_two_mulEquiv x⟩

theorem pi3_sphere_three (x : Sphere 3) :
    Nonempty (π_ 3 (Sphere 3) x ≃* Multiplicative ℤ) :=
  ⟨pi3_sphere_three_mulEquiv x⟩

theorem pi6_sphere_three (x : Sphere 3) :
    Nonempty (π_ 6 (Sphere 3) x ≃* Multiplicative (ZMod 12)) :=
  ⟨pi6_sphere_three_mulEquiv x⟩

theorem pi7_sphere_seven (x : Sphere 7) :
    Nonempty (π_ 7 (Sphere 7) x ≃* Multiplicative ℤ) :=
  ⟨pi7_sphere_seven_mulEquiv x⟩

end Wikipedia.HomotopyGroupsOfSpheres
