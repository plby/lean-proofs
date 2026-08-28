import Wikipedia.NoExoticSixSphere.PartialFrameRelativeReduction
import Wikipedia.NoExoticSixSphere.CubeCylinderConnectivity

/-!
# Native homotopy stability for adding a column

The actual reconstruction map is surjective on cubical homotopy classes
below the base sphere dimension. It is injective one degree further below:
contract the first column of a homotopy on its entire cubical cylinder,
lift that contraction relative to all faces, and extract the remaining frame.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

variable {m n r : ℕ}
variable (v : UnitSphere (Vector (r + 1))) (c : UnitSphere (Vector (n + 1)))

theorem exists_genLoop_reconstruction (hmn : m < n) (a : Space n r)
    (p : GenLoop (Fin m) (Space (n + 1) (r + 1)) (ColumnFiber.reconstruct v c a)) :
    ∃ q : GenLoop (Fin m) (Space n r) a,
      GenLoop.Homotopic p
        (HigherHomotopy.genLoopMap (ColumnFiber.reconstructionMap v c) rfl q) := by
  let cp : GenLoop (Fin m) (Sphere n) c :=
    ⟨(column v).comp p.val, fun x hx ↦
      (congrArg (column v) (p.property x hx)).trans
        (Subtype.ext (ColumnFiber.reconstruct_column v c a))⟩
  obtain ⟨H⟩ := genLoop_homotopic_const_of_homeomorph_sphere hmn
    (Homeomorph.refl (Sphere n)) c cp
  obtain ⟨q, ⟨G⟩⟩ := exists_rankReductionRel_of_column_homotopy v c p.val H
  have hq (x : Fin m → unitInterval) (hx : x ∈ Cube.boundary (Fin m)) : q x = a := by
    apply reconstruction_injective v c
    exact (G.fst_eq_snd hx).symm.trans (p.property x hx)
  exact ⟨⟨q, hq⟩, ⟨G⟩⟩

theorem reconstruction_homotopyMap_surjective (hmn : m < n) (a : Space n r) :
    Function.Surjective (HigherHomotopy.map (N := Fin m) (y := a)
      (ColumnFiber.reconstructionMap v c) rfl) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro p
  obtain ⟨q, hq⟩ := exists_genLoop_reconstruction v c hmn a p
  exact ⟨Quotient.mk' q, Quotient.sound hq.symm⟩

theorem reconstruction_homotopyRel_reflect (hmn : m + 1 < n)
    (p q : C((Fin m → unitInterval), Space n r))
    (H : ((ColumnFiber.reconstructionMap v c).comp p).HomotopyRel
      ((ColumnFiber.reconstructionMap v c).comp q) (Cube.boundary (Fin m))) :
    Nonempty (p.HomotopyRel q (Cube.boundary (Fin m))) := by
  let Hc : C(unitInterval × (Fin m → unitInterval), Sphere n) :=
    (column v).comp H.toHomotopy.toContinuousMap
  have hcol (z : unitInterval × (Fin m → unitInterval))
      (hz : z ∈ CubeCylinder.boundary m) : Hc z = c := by
    rcases z with ⟨t, x⟩
    change column v (H (t, x)) = c
    rcases hz with (ht | ht) | hx
    · change t = 0 at ht
      subst t
      rw [H.apply_zero]
      exact Subtype.ext (ColumnFiber.reconstruct_column v c (p x))
    · change t = 1 at ht
      subst t
      rw [H.apply_one]
      exact Subtype.ext (ColumnFiber.reconstruct_column v c (q x))
    · rw [H.eq_fst t hx]
      exact Subtype.ext (ColumnFiber.reconstruct_column v c (p x))
  obtain ⟨K⟩ := CubeCylinder.sphere_nullhomotopicRel hmn Hc c hcol
  obtain ⟨Q, ⟨G⟩⟩ := exists_rankReductionRel_of_column_homotopy v c
    H.toHomotopy.toContinuousMap K
  refine ⟨{
    toContinuousMap := Q
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    apply reconstruction_injective v c
    exact (G.fst_eq_snd (show (0, x) ∈ CubeCylinder.boundary m from
      Or.inl (Or.inl rfl))).symm.trans (H.apply_zero x)
  · intro x
    apply reconstruction_injective v c
    exact (G.fst_eq_snd (show (1, x) ∈ CubeCylinder.boundary m from
      Or.inl (Or.inr rfl))).symm.trans (H.apply_one x)
  · intro t x hx
    apply reconstruction_injective v c
    exact (G.fst_eq_snd (show (t, x) ∈ CubeCylinder.boundary m from
      Or.inr hx)).symm.trans (H.eq_fst t hx)

theorem reconstruction_homotopyMap_injective (hmn : m + 1 < n) (a : Space n r) :
    Function.Injective (HigherHomotopy.map (N := Fin m) (y := a)
      (ColumnFiber.reconstructionMap v c) rfl) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q hpq
  obtain ⟨H⟩ := Quotient.exact hpq
  exact Quotient.sound (reconstruction_homotopyRel_reflect v c hmn p.val q.val H)

def reconstruction_homotopyEquiv (hmn : m + 1 < n) (a : Space n r) :
    HomotopyGroup (Fin m) (Space n r) a ≃
      HomotopyGroup (Fin m) (Space (n + 1) (r + 1)) (ColumnFiber.reconstruct v c a) :=
  Equiv.ofBijective (HigherHomotopy.map (ColumnFiber.reconstructionMap v c) rfl)
    ⟨reconstruction_homotopyMap_injective v c hmn a,
      reconstruction_homotopyMap_surjective v c (by omega) a⟩

def reconstruction_homotopyMulEquiv [Nonempty (Fin m)] (hmn : m + 1 < n)
    (a : Space n r) :
    HomotopyGroup (Fin m) (Space n r) a ≃*
      HomotopyGroup (Fin m) (Space (n + 1) (r + 1)) (ColumnFiber.reconstruct v c a) :=
  MulEquiv.ofBijective (HigherHomotopy.mapMonoidHom (ColumnFiber.reconstructionMap v c) rfl)
    ⟨reconstruction_homotopyMap_injective v c hmn a,
      reconstruction_homotopyMap_surjective v c (by omega) a⟩

end NoExoticSixSphere.Stiefel
