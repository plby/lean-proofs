import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# Sphere contractions on a cubical cylinder, relative to its entire boundary

The time coordinate and the cube coordinates are exactly the coordinates of
a successor-dimensional cube. Both time ends and every side face are fixed.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.CubeCylinder

def boundary (m : ℕ) : Set (unitInterval × (Fin m → unitInterval)) :=
  {z | (z.1 = 0 ∨ z.1 = 1) ∨ z.2 ∈ Cube.boundary (Fin m)}

def insert (m : ℕ) :
    C(unitInterval × (Fin m → unitInterval), Fin (m + 1) → unitInterval) :=
  ⟨fun z ↦ Fin.cons z.1 z.2, by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd⟩

def split (m : ℕ) :
    C((Fin (m + 1) → unitInterval), unitInterval × (Fin m → unitInterval)) :=
  ⟨fun x ↦ (x 0, fun i ↦ x i.succ),
    (continuous_apply 0).prodMk (continuous_pi (fun i ↦ continuous_apply i.succ))⟩

theorem split_insert (m : ℕ) (z : unitInterval × (Fin m → unitInterval)) :
    split m (insert m z) = z := by
  apply Prod.ext
  · rfl
  · rfl

theorem insert_split (m : ℕ) (x : Fin (m + 1) → unitInterval) :
    insert m (split m x) = x := by
  funext i
  cases i using Fin.cases <;> rfl

theorem insert_boundary (m : ℕ) (z : unitInterval × (Fin m → unitInterval))
    (hz : z ∈ boundary m) : insert m z ∈ Cube.boundary (Fin (m + 1)) := by
  rcases hz with ht | ⟨i, hi⟩
  · exact ⟨0, ht⟩
  · exact ⟨i.succ, hi⟩

theorem split_boundary (m : ℕ) (x : Fin (m + 1) → unitInterval)
    (hx : x ∈ Cube.boundary (Fin (m + 1))) : split m x ∈ boundary m := by
  obtain ⟨i, hi⟩ := hx
  cases i using Fin.cases with
  | zero => exact Or.inl hi
  | succ i => exact Or.inr ⟨i, hi⟩

theorem sphere_nullhomotopicRel {m n : ℕ} (hmn : m + 1 < n)
    (H : C(unitInterval × (Fin m → unitInterval), Sphere n)) (c : Sphere n)
    (hbd : ∀ z ∈ boundary m, H z = c) :
    Nonempty (H.HomotopyRel (ContinuousMap.const _ c) (boundary m)) := by
  let p : GenLoop (Fin (m + 1)) (Sphere n) c :=
    ⟨H.comp (split m), fun x hx ↦ hbd _ (split_boundary m x hx)⟩
  obtain ⟨G⟩ := genLoop_homotopic_const_of_homeomorph_sphere hmn
    (Homeomorph.refl (Sphere n)) c p
  refine ⟨{
    toFun := fun z ↦ G (z.1, insert m z.2)
    continuous_toFun := G.continuous.comp
      (continuous_fst.prodMk ((insert m).continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    rw [G.apply_zero]
    change H (split m (insert m z)) = H z
    rw [split_insert]
  · intro z
    exact G.apply_one (insert m z)
  · intro t z hz
    change G (t, insert m z) = H z
    rw [G.eq_fst t (insert_boundary m z hz)]
    change H (split m (insert m z)) = H z
    rw [split_insert]

end NoExoticSixSphere.CubeCylinder
