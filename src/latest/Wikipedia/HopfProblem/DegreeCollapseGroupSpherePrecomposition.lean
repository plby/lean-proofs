import Wikipedia.HopfProblem.DegreeCollapseSphereLiftFamily
import Wikipedia.HopfProblem.HomotopyGroupPowerMap
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyPrecomposition

/-!
# Precomposition preserves powers for maps into an actual topological group

Pointwise powers represent the original native homotopy-group powers.
Based sphere homotopies remain based after precomposition. Consequently,
if one sphere map represents a power of another, their induced native
maps have the same power relation in every positive degree.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.GroupSpherePrecomposition

open NoExoticSixSphere SmoothCube SphereLiftFamily

theorem compose_class_congr {X : Type*} [TopologicalSpace X] {x : X}
    {m n : ℕ} [NeZero m] [NeZero n] {f h : BasedMap n X x}
    (heq : sphereClass f = sphereClass h) (g : SphereComposition.Based m n) :
    sphereClass (compose f g) = sphereClass (compose h g) := by
  obtain ⟨H⟩ := (sphereClass_eq_iff (Nat.pos_of_neZero n) f h).mp heq
  apply (sphereClass_eq_iff (Nat.pos_of_neZero m) _ _).mpr
  exact ⟨Wikipedia.HomotopyGroupsOfSpheres.pointedHomotopyPrecomp
    H g.val (spherePole m) g.property⟩

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable {m n : ℕ} [NeZero m] [NeZero n]

def power (f : BasedMap n G 1) (k : ℤ) : BasedMap n G 1 :=
  ⟨f.val ^ k, by simp only [ContinuousMap.zpow_apply, f.property, one_zpow]⟩

theorem power_nat_class (f : BasedMap n G 1) (k : ℕ) :
    sphereClass (power f k) = sphereClass f ^ k := by
  have h : toGenLoop (power f k) = HomotopyGroupPowerMap.powLoop (toGenLoop f) k := by
    apply GenLoop.ext
    intro u
    change f.val (quotient n u) ^ (k : ℤ) = f.val (quotient n u) ^ k
    exact zpow_natCast _ _
  exact (congrArg (fun p : GenLoop (Fin n) G 1 ↦ (⟦p⟧ : π_ n G 1)) h).trans
    (HomotopyGroupPowerMap.class_powLoop (toGenLoop f) k)

omit [NeZero n] in
theorem power_mul_inverse (f : BasedMap n G 1) (k : ℕ) :
    HomotopyGroupPowerMap.mulLoop (toGenLoop (power f (-(k : ℤ))))
      (toGenLoop (power f k)) = GenLoop.const := by
  apply GenLoop.ext
  intro u
  change f.val (quotient n u) ^ (-(k : ℤ)) *
    f.val (quotient n u) ^ (k : ℤ) = 1
  simp only [zpow_neg, inv_mul_cancel]

theorem power_class (f : BasedMap n G 1) (k : ℤ) :
    sphereClass (power f k) = sphereClass f ^ k := by
  cases k with
  | ofNat k => exact power_nat_class f k
  | negSucc k =>
    have h : sphereClass (power f (-((k + 1 : ℕ) : ℤ))) *
        sphereClass (power f (k + 1 : ℕ)) = 1 := by
      have hloop := HomotopyGroupPowerMap.class_mulLoop
        (toGenLoop (power f (-((k + 1 : ℕ) : ℤ))))
        (toGenLoop (power f (k + 1 : ℕ)))
      rw [power_mul_inverse] at hloop
      exact hloop.symm
    have hi := eq_inv_of_mul_eq_one_left h
    rw [power_nat_class] at hi
    change sphereClass (power f (-((k + 1 : ℕ) : ℤ))) =
      sphereClass f ^ (-((k + 1 : ℕ) : ℤ))
    simpa only [zpow_neg, zpow_natCast] using hi

theorem compose_power {f h : BasedMap n G 1} (k : ℤ)
    (heq : sphereClass h = sphereClass f ^ k) (g : SphereComposition.Based m n) :
    sphereClass (compose h g) = sphereClass (compose f g) ^ k := by
  have hclass : sphereClass h = sphereClass (power f k) :=
    heq.trans (power_class f k).symm
  exact (compose_class_congr hclass g).trans (power_class (compose f g) k)

theorem native_map_power {f h : BasedMap n G 1} (k : ℤ)
    (heq : sphereClass h = sphereClass f ^ k)
    (c : π_ m (Sphere n) (spherePole n)) :
    HigherHomotopy.map (N := Fin m) h.val h.property c =
      HigherHomotopy.map (N := Fin m) f.val f.property c ^ k := by
  obtain ⟨g, rfl⟩ := sphereClass_surjective (Nat.pos_of_neZero m) c
  exact compose_power k heq g

theorem injective_of_generates {f h : BasedMap n G 1}
    (hf : Function.Surjective (fun k : ℤ ↦ sphereClass f ^ k))
    (hh : Function.Injective (HigherHomotopy.map (N := Fin m) h.val h.property)) :
    Function.Injective (HigherHomotopy.map (N := Fin m) f.val f.property) := by
  obtain ⟨k, hk⟩ := hf (sphereClass h)
  change sphereClass f ^ k = sphereClass h at hk
  intro a b hab
  apply hh
  rw [native_map_power k hk.symm a, native_map_power k hk.symm b, hab]

end Wikipedia.HopfProblem.DegreeCollapse.GroupSpherePrecomposition
