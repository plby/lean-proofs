import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnExactness

/-!
# Homotopy comparison with the quaternionic column fiber

If the two adjacent homotopy groups of the base vanish, inclusion of the
actual fiber induces an isomorphism. Surjectivity is proved by lifting a
null-homotopy of the projected cube; injectivity uses the connecting map.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.CubeFirstCoordinate HopfProblem.SecondHurewicz

variable {N : Type} [Fintype N] [DecidableEq N] {j : N} {n : ℕ}

theorem connecting_const :
    connecting n (⟦GenLoop.const⟧ : HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j)) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) (axisSubgroup j) 1) := by
  let L : CubeLift (GenLoop.const : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)) := {
    map := ContinuousMap.const _ 1
    initial := fun _ => rfl
    project := fun _ _ => column_one j
    boundary := fun _ _ _ => rfl }
  have hL : L.endpoint = GenLoop.const := by
    apply GenLoop.ext
    intro u
    apply Subtype.ext
    rfl
  exact (connecting_eq_endpoint _ L).trans (congrArg Quotient.mk' hL)

theorem inclusionMap_injective [NeZero n]
    [Subsingleton (HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j))] :
    Function.Injective (inclusionMap (j := j) n) := by
  apply (injective_iff_map_eq_one (inclusionMap (j := j) n)).mpr
  intro a ha
  obtain ⟨b, hb⟩ := (connecting_range_eq_kernel a).mpr ha
  have he : b = (⟦GenLoop.const⟧ :
      HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j)) := Subsingleton.elim _ _
  rw [← hb, he]
  exact connecting_const

/-- A cube in the total space can be moved into the actual fiber when its projection is null. -/
theorem exists_fiber_representative
    [Subsingleton (HomotopyGroup (Fin n) (UnitColumn N) (axisColumn j))]
    (q : GenLoop (Fin n) (SpGroup N) 1) :
    ∃ r : GenLoop (Fin n) (axisSubgroup j) 1,
      GenLoop.Homotopic (mapGenLoop inclusion 1 r) q := by
  let p : GenLoop (Fin n) (UnitColumn N) (axisColumn j) :=
    ⟨(column j).comp q.val, fun u hu =>
      (congrArg (column j) (q.property u hu)).trans (column_one j)⟩
  have hp : (⟦p⟧ : HomotopyGroup (Fin n) (UnitColumn N) (axisColumn j)) =
      ⟦GenLoop.const⟧ := @Subsingleton.elim
        (HomotopyGroup (Fin n) (UnitColumn N) (axisColumn j)) inferInstance _ _
  obtain ⟨H⟩ := Quotient.exact hp
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift j H.toContinuousMap q.val
    (fun u => (H.map_zero_left u).symm)
  have hLb (t : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
      L (t, u) = q u :=
    hLfix u (fun s => (H.eq_fst s hu).trans (H.map_zero_left u).symm) t
  have hE (u : Fin n → I) : L (1, u) ∈ axisSubgroup j :=
    (hLp 1 u).trans (H.map_one_left u)
  let r : GenLoop (Fin n) (axisSubgroup j) 1 :=
    ⟨⟨fun u => ⟨L (1, u), hE u⟩,
      (L.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩,
      fun u hu => Subtype.ext ((hLb 1 u hu).trans (q.property u hu))⟩
  let F : q.val.HomotopyRel (mapGenLoop inclusion 1 r).val (Cube.boundary (Fin n)) := {
    toContinuousMap := L
    map_zero_left := hL₀
    map_one_left := fun _ => rfl
    prop' := hLb }
  exact ⟨r, ⟨F.symm⟩⟩

theorem inclusionMap_surjective [NeZero n]
    [Subsingleton (HomotopyGroup (Fin n) (UnitColumn N) (axisColumn j))] :
    Function.Surjective (inclusionMap (j := j) n) := by
  intro a
  refine Quotient.inductionOn a fun q => ?_
  obtain ⟨r, hr⟩ := exists_fiber_representative (j := j) q
  exact ⟨⟦r⟧, Quotient.sound hr⟩

/-- The comparison is induced by the original fiber inclusion. -/
def inclusionMulEquiv (j : N) (n : ℕ) [NeZero n]
    [Subsingleton (HomotopyGroup (Fin n) (UnitColumn N) (axisColumn j))]
    [Subsingleton (HomotopyGroup (Fin (n + 1)) (UnitColumn N) (axisColumn j))] :
    HomotopyGroup (Fin n) (axisSubgroup j) 1 ≃* HomotopyGroup (Fin n) (SpGroup N) 1 :=
  MulEquiv.ofBijective (inclusionMap n) ⟨inclusionMap_injective, inclusionMap_surjective⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
