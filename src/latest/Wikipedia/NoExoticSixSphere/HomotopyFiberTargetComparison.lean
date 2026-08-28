import Wikipedia.NoExoticSixSphere.HomotopyFiberTargetMap

/-!
# Native comparison of fibers under a target map

The actual fiber exact sequences and the literal naturality identities
give injectivity and surjectivity of the target-change fiber map. The
source of the original map is unchanged. The proof is a group-level
diagram argument and does not assume a homotopy-excision theorem.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.HomotopyFiberTargetMap

open HomotopyFiber

variable {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  (f : C(A, B)) (g : C(B, C)) (a : A)

theorem hom_injective (d : ℕ) [NeZero d]
    (hg : Function.Injective (HigherHomotopy.map (N := Fin (d + 1)) g (y := f a) rfl)) :
    Function.Injective (hom f g a d) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro c hc
  change hom f g a d c = 1 at hc
  change c = 1
  have hp : HigherHomotopy.mapMonoidHom (N := Fin d) (projection f (f a))
      (projection_basepoint f a) c = 1 :=
    (projection_hom f g a d c).symm.trans
      ((congrArg (HigherHomotopy.mapMonoidHom (N := Fin d)
        (projection (g.comp f) ((g.comp f) a)) (projection_basepoint (g.comp f) a)) hc).trans
          (map_one _))
  obtain ⟨b, hb⟩ := (projection_eq_const_iff_exists_boundary_class d f a c).mp hp
  change boundaryHom d f a b = c at hb
  have hgb : boundaryHom d (g.comp f) a
      (HigherHomotopy.map (N := Fin (d + 1)) g (y := f a) rfl b) = 1 := by
    rw [← boundary_hom f g a d b, hb, hc]
  obtain ⟨u, hu⟩ := (boundary_eq_const_iff_exists_source_class d (g.comp f) a _).mp hgb
  rw [source_map_factor f g a (d + 1) u] at hu
  exact hb.symm.trans ((boundary_eq_const_iff_exists_source_class d f a b).mpr ⟨u, hg hu⟩)

theorem hom_surjective (d : ℕ) [NeZero d]
    (hgd : Function.Injective (HigherHomotopy.map (N := Fin d) g (y := f a) rfl))
    (hg : Function.Surjective (HigherHomotopy.map (N := Fin (d + 1)) g (y := f a) rfl)) :
    Function.Surjective (hom f g a d) := by
  intro x
  let p : π_ d A a := HigherHomotopy.mapMonoidHom (N := Fin d)
    (projection (g.comp f) ((g.comp f) a)) (projection_basepoint (g.comp f) a) x
  have hp : HigherHomotopy.map (N := Fin d) f (y := a) rfl p = 1 := by
    apply hgd
    have he : HigherHomotopy.map (N := Fin d) (g.comp f) (y := a) rfl p = 1 :=
      (map_eq_const_iff_exists_fiber_class (g.comp f) a p).mpr ⟨x, rfl⟩
    rw [source_map_factor f g a d p] at he
    exact he.trans (map_one
      (HigherHomotopy.mapMonoidHom (N := Fin d) g (y := f a) rfl)).symm
  obtain ⟨y, hy⟩ := (map_eq_const_iff_exists_fiber_class f a p).mp hp
  have hy' : HigherHomotopy.map (N := Fin d) (projection f (f a))
      (projection_basepoint f a) y = p := hy
  let z := x * (hom f g a d y)⁻¹
  have hz : HigherHomotopy.mapMonoidHom (N := Fin d)
      (projection (g.comp f) ((g.comp f) a)) (projection_basepoint (g.comp f) a) z = 1 := by
    change HigherHomotopy.mapMonoidHom (N := Fin d)
      (projection (g.comp f) ((g.comp f) a)) (projection_basepoint (g.comp f) a)
        (x * (hom f g a d y)⁻¹) = 1
    rw [map_mul, map_inv, projection_hom f g a d y]
    change p * (HigherHomotopy.map (N := Fin d) (projection f (f a))
      (projection_basepoint f a) y)⁻¹ = 1
    rw [hy', mul_inv_cancel]
  obtain ⟨b, hb⟩ := (projection_eq_const_iff_exists_boundary_class d (g.comp f) a z).mp hz
  change boundaryHom d (g.comp f) a b = z at hb
  obtain ⟨c, hc⟩ := hg b
  refine ⟨boundaryHom d f a c * y, ?_⟩
  rw [map_mul, boundary_hom f g a d c, hc, hb]
  change (x * (hom f g a d y)⁻¹) * hom f g a d y = x
  simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem hom_bijective (d : ℕ) [NeZero d]
    (hgd : Function.Injective (HigherHomotopy.map (N := Fin d) g (y := f a) rfl))
    (hg : Function.Bijective (HigherHomotopy.map (N := Fin (d + 1)) g (y := f a) rfl)) :
    Function.Bijective (hom f g a d) :=
  ⟨hom_injective f g a d hg.injective, hom_surjective f g a d hgd hg.surjective⟩

end NoExoticSixSphere.HomotopyFiberTargetMap
