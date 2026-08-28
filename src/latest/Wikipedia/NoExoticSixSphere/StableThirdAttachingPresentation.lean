import Wikipedia.NoExoticSixSphere.SphereFiveEighthPresentation

/-!
# The actual attaching presentation is unchanged by further suspension

Starting with the native pi_8(S5), every subsequent native suspension in
the third stem lies in the proved bijectivity range. The recursive
equivalences below use exactly those suspension homomorphisms. Thus the
single geometric attaching relation presents every such stable stage,
and detects the kernel of every iterated suspension from pi_7(S4).
No numerical coordinates of that relation are asserted.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.StableThirdAttaching

abbrev Stage (k : ℕ) := π_ (k + 8) (Sphere (k + 5)) (spherePole (k + 5))

def stepHom (k : ℕ) : Stage k →* Stage (k + 1) :=
  CubicalSphereSuspension.hom (k + 8) (k + 5)

theorem stepHom_bijective (k : ℕ) : Function.Bijective (stepHom k) :=
  CubicalSphereSuspension.hom_bijective (by omega)

def stepEquiv (k : ℕ) : Stage k ≃* Stage (k + 1) :=
  MulEquiv.ofBijective (stepHom k) (stepHom_bijective k)

def fromFirst : (k : ℕ) → Stage 0 ≃* Stage k
  | 0 => MulEquiv.refl _
  | k + 1 => (fromFirst k).trans (stepEquiv k)

theorem fromFirst_zero (x : Stage 0) : fromFirst 0 x = x := rfl

theorem fromFirst_succ (k : ℕ) (x : Stage 0) :
    fromFirst (k + 1) x = stepHom k (fromFirst k x) := rfl

def suspension (k : ℕ) : π_ 7 (Sphere 4) (spherePole 4) →* Stage k :=
  (fromFirst k).toMonoidHom.comp SphereFourAttaching.suspension

theorem suspension_zero (x : π_ 7 (Sphere 4) (spherePole 4)) :
    suspension 0 x = SphereFourAttaching.suspension x := rfl

theorem suspension_succ (k : ℕ) (x : π_ 7 (Sphere 4) (spherePole 4)) :
    suspension (k + 1) x = stepHom k (suspension k x) := rfl

theorem suspension_eq_one_iff (k : ℕ) (x : π_ 7 (Sphere 4) (spherePole 4)) :
    suspension k x = 1 ↔ ∃ a : ℤ, SphereFourAttaching.attachingClass ^ a = x := by
  have h : suspension k x = 1 ↔ SphereFourAttaching.suspension x = 1 := by
    constructor
    · intro hx
      exact (fromFirst k).injective (hx.trans (map_one (fromFirst k)).symm)
    · intro hx
      change fromFirst k (SphereFourAttaching.suspension x) = 1
      rw [hx, map_one]
  exact h.trans (SphereFourAttaching.suspension_eq_one_iff x)

def projection (k : ℕ) : SphereFiveEighth.Coordinates →* Stage k :=
  (fromFirst k).toMonoidHom.comp SphereFiveEighth.projection

def presentationEquiv (k : ℕ) :
    (SphereFiveEighth.Coordinates ⧸ Subgroup.zpowers SphereFiveEighth.relation) ≃* Stage k :=
  SphereFiveEighth.presentationEquiv.trans (fromFirst k)

theorem presentationEquiv_mk (k : ℕ) (x : SphereFiveEighth.Coordinates) :
    presentationEquiv k (QuotientGroup.mk x) = projection k x := rfl

theorem projection_coordinates (k : ℕ) (x : π_ 7 (Sphere 4) (spherePole 4)) :
    projection k (SphereFourSeventh.groupEquiv x) = suspension k x :=
  congrArg (fromFirst k) (SphereFiveEighth.projection_coordinates x)

theorem projection_eq_one_iff_coordinates (k : ℕ) (x : SphereFiveEighth.Coordinates) :
    projection k x = 1 ↔ ∃ a : ℤ,
      a * SphereFiveEighth.relation.1.toAdd = x.1.toAdd ∧
        a • SphereFiveEighth.relation.2.toAdd = x.2.toAdd := by
  have h : projection k x = 1 ↔ SphereFiveEighth.projection x = 1 := by
    constructor
    · intro hx
      exact (fromFirst k).injective (hx.trans (map_one (fromFirst k)).symm)
    · intro hx
      change fromFirst k (SphereFiveEighth.projection x) = 1
      rw [hx, map_one]
  exact h.trans (SphereFiveEighth.projection_eq_one_iff_coordinates x)

end NoExoticSixSphere.StableThirdAttaching
