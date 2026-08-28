import Wikipedia.NoExoticSixSphere.IteratedSphereHomotopyEquivalence

/-!
# Coordinate changes retain nullity at every finite suspension stage

An exact square of actual continuous maps and actual homeomorphisms induces
a sphere homotopy-equivalence square. Both inverse homotopies are retained
by suspension, so the comparison holds after any specified finite number
of suspensions, not just at the initial stage.
-/

noncomputable section

namespace NoExoticSixSphere.SphereRepresentative

variable {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y'] {m n m' n' : ℕ}

def map (s : X ≃ₜ Sphere m) (t : Y ≃ₜ Sphere n) (f : C(X, Y)) :
    C(Sphere m, Sphere n) :=
  t.toHomotopyEquiv.toFun.comp (f.comp s.symm.toHomotopyEquiv.toFun)

theorem iterate_nullhomotopic_iff (s : X ≃ₜ Sphere m) (t : Y ≃ₜ Sphere n)
    (s' : X' ≃ₜ Sphere m') (t' : Y' ≃ₜ Sphere n')
    (e : X ≃ₜ X') (E : Y ≃ₜ Y') (f : C(X, Y)) (g : C(X', Y'))
    (h : ∀ x, E (f x) = g (e x)) (r : ℕ) :
    (SphereMapSuspension.iterate (map s t f) r).Nullhomotopic ↔
      (SphereMapSuspension.iterate (map s' t' g) r).Nullhomotopic := by
  let S := (s.symm.trans e).trans s'
  let T := (t.symm.trans E).trans t'
  apply SphereMapSuspension.iterate_nullhomotopic_iff_of_equiv_square
    S.toHomotopyEquiv T.toHomotopyEquiv
  have he : T.toHomotopyEquiv.toFun.comp (map s t f) =
      (map s' t' g).comp S.toHomotopyEquiv.toFun := by
    apply ContinuousMap.ext
    intro x
    change t' (E (t.symm (t (f (s.symm x))))) = t' (g (s'.symm (s' (e (s.symm x)))))
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply, h]
  rw [he]

end NoExoticSixSphere.SphereRepresentative
