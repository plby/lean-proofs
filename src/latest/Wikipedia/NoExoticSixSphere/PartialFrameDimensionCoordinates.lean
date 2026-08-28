import Wikipedia.NoExoticSixSphere.SphereDiskExtension

/-!
# Exact dimension transport for partial frames and their disk extensions

Only proved equalities of natural-number dimensions are transported. This
does not change the underlying frame or assume any geometric comparison.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization DiskBoundary

def dimensionHomeomorph {N n N' n' : ℕ} (hN : N = N') (hn : n = n') :
    Space N n ≃ₜ Space N' n' := by
  subst N'
  subst n'
  exact Homeomorph.refl _

theorem extends_dimensionHomeomorph_iff {N n N' n' : ℕ}
    (hN : N = N') (hn : n = n') (f : C(Sphere 3, Space N n)) :
    Extends ((dimensionHomeomorph hN hn : C(Space N n, Space N' n')).comp f) ↔ Extends f := by
  subst N'
  subst n'
  rfl

theorem homotopic_dimensionHomeomorph_iff {X : Type*} [TopologicalSpace X] {N n N' n' : ℕ}
    (hN : N = N') (hn : n = n') (f g : C(X, Space N n)) :
    ((dimensionHomeomorph hN hn : C(Space N n, Space N' n')).comp f).Homotopic
      ((dimensionHomeomorph hN hn : C(Space N n, Space N' n')).comp g) ↔ f.Homotopic g := by
  subst N'
  subst n'
  rfl

end NoExoticSixSphere.Stiefel
