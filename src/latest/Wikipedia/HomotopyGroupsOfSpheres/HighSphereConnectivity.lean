import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenConnectivity
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Iso

/-! # Vanishing through degree seven for spheres of dimension at least eight -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.SphereHomology

instance highSphere_piTwo_subsingleton (n : ℕ) (x : Sphere (n + 8)) :
    Subsingleton (π_ 2 (Sphere (n + 8)) x) :=
  unitSphere_piTwo_subsingleton (n + 5) x

instance highSphere_piThree_subsingleton (n : ℕ) (x : Sphere (n + 8)) :
    Subsingleton (π_ 3 (Sphere (n + 8)) x) := by
  let := unitSphere_homology_subsingleton (n + 7) 3 (by decide) (by omega)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

instance highSphere_piFour_subsingleton (n : ℕ) (x : Sphere (n + 8)) :
    Subsingleton (π_ 4 (Sphere (n + 8)) x) := by
  let := unitSphere_homology_subsingleton (n + 7) 4 (by decide) (by omega)
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

instance highSphere_piFive_subsingleton (n : ℕ) (x : Sphere (n + 8)) :
    Subsingleton (π_ 5 (Sphere (n + 8)) x) := by
  let := unitSphere_homology_subsingleton (n + 7) 5 (by decide) (by omega)
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

instance highSphere_piSix_subsingleton (n : ℕ) (x : Sphere (n + 8)) :
    Subsingleton (π_ 6 (Sphere (n + 8)) x) := by
  let := unitSphere_homology_subsingleton (n + 7) 6 (by decide) (by omega)
  exact (SixthHurewicz.hurewiczPi6Equiv x).injective.subsingleton

instance highSphere_piSeven_subsingleton (n : ℕ) (x : Sphere (n + 8)) :
    Subsingleton (π_ 7 (Sphere (n + 8)) x) := by
  let := unitSphere_homology_subsingleton (n + 7) 7 (by decide) (by omega)
  exact (SeventhHurewicz.hurewiczPi7Equiv x).injective.subsingleton

theorem sphere_piSix_subsingleton (n : ℕ) (hn : 8 ≤ n) (x : Sphere n) :
    Subsingleton (π_ 6 (Sphere n) x) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have he : n = m + 8 := by omega
  clear hm
  subst n
  infer_instance

theorem sphere_piSeven_subsingleton (n : ℕ) (hn : 8 ≤ n) (x : Sphere n) :
    Subsingleton (π_ 7 (Sphere n) x) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have he : n = m + 8 := by omega
  clear hm
  subst n
  infer_instance

end Wikipedia.HomotopyGroupsOfSpheres
