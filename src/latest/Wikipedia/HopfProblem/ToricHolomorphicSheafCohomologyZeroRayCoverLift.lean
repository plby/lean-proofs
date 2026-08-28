import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverCoordinates

/-!
# Actual inverse-blowdown coordinate maps on open domains

These maps compose the literal projective affine parametrization with
the proved inverse of the actual punctured blowdown. The inverse map is
the literal projective coordinate of blowdown, not a transported atlas.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

open ToricCharts ToricComponent

variable (k : Fin 3) (Ω : Opens (ℂ × ℂ))
  (hΩ : ∀ q ∈ Ω, standardProjectiveMap k q ∈ ProjectivePlane.puncturedSpace)

def projectiveLift (q : Ω) : ProjectivePlane.puncturedSpace :=
  ⟨standardProjectiveMap k q, hΩ q q.property⟩

theorem projectiveLift_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω (projectiveLift k Ω hΩ) := by
  intro q
  have he : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω
      (fun p : Ω => (projectiveLift k Ω hΩ p : ProjectivePlane.Space)) q ↔
    ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω (projectiveLift k Ω hΩ) q :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((standardProjectiveMap_holomorphic k).comp contMDiff_subtype_val) q)

/-- The actual inverse punctured blowdown, in the specified actual affine coordinates. -/
def liftMap (q : Ω) : component :=
  puncturedBlowdownBiholomorph.symm (projectiveLift k Ω hΩ q)

theorem liftMap_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω (liftMap k Ω hΩ) :=
  contMDiff_subtype_val.comp
    (puncturedBlowdownBiholomorph.symm.contMDiff.comp (projectiveLift_holomorphic k Ω hΩ))

@[simp] theorem blowdown_liftMap (q : Ω) :
    blowdown (liftMap k Ω hΩ q) = standardProjectiveMap k q :=
  congrArg Subtype.val
    (puncturedBlowdownBiholomorph.apply_symm_apply (projectiveLift k Ω hΩ q))

theorem liftMap_mem_punctured (q : Ω) : liftMap k Ω hΩ q ∈ blowdownPuncturedSpace :=
  (puncturedBlowdownBiholomorph.symm (projectiveLift k Ω hΩ q)).property

@[simp] theorem coordinates_liftMap (q : Ω) : coordinates k (liftMap k Ω hΩ q) = q := by
  change standardProjectiveCoords k (blowdown (liftMap k Ω hΩ q)) = q
  rw [blowdown_liftMap, standardProjectiveCoords_map]

theorem liftMap_mem_cover_iff (j : Fin 3) (q : Ω) :
    liftMap k Ω hΩ q ∈ cover j ↔ standardProjectiveMap k q ∈ ProjectivePlane.affineTarget j := by
  rw [← blowdown_mem_affineTarget_iff, blowdown_liftMap]

theorem liftMap_coordinates (x : component) (hx : x ∈ cover k)
    (hxΩ : coordinates k x ∈ Ω) :
    liftMap k Ω hΩ ⟨coordinates k x, hxΩ⟩ = x := by
  apply puncturedBlowdown_inverse_eq_of_blowdown
  exact (standardProjectiveMap_coordinates k x hx).symm

variable (W : Opens component) (hW : W ≤ cover k)
  (hLift : ∀ q : Ω, liftMap k Ω hΩ q ∈ W)
  (hCoords : ∀ x : W, coordinates k x ∈ Ω)

/-- A genuine biholomorphism whose forward map is the actual inverse blowdown
and whose inverse is the actual projective coordinate of blowdown. -/
def coordinateBiholomorph : Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) Ω W ω where
  toEquiv :=
    { toFun q := ⟨liftMap k Ω hΩ q, hLift q⟩
      invFun x := ⟨coordinates k x, hCoords x⟩
      left_inv q := Subtype.ext (coordinates_liftMap k Ω hΩ q)
      right_inv x := Subtype.ext (liftMap_coordinates k Ω hΩ x (hW x.property) (hCoords x)) }
  contMDiff_toFun := by
    intro q
    have he : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω
        (liftMap k Ω hΩ) q ↔
      ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω
        (fun p : Ω => (⟨liftMap k Ω hΩ p, hLift p⟩ : W)) q :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (fun p : Ω => (⟨liftMap k Ω hΩ p, hLift p⟩ : W)) univ q
    exact he.mp (liftMap_holomorphic k Ω hΩ q)
  contMDiff_invFun := by
    intro x
    have he : ContMDiffAt 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ × ℂ) ω
        (fun y : W => coordinates k y) x ↔
      ContMDiffAt 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ × ℂ) ω
        (fun y : W => (⟨coordinates k y, hCoords y⟩ : Ω)) x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (fun y : W => (⟨coordinates k y, hCoords y⟩ : Ω)) univ x
    apply he.mp
    exact ((coordinates_holomorphicOn k).contMDiffAt
      ((cover k).isOpen.mem_nhds (hW x.property))).comp _ contMDiff_subtype_val.contMDiffAt

@[simp] theorem coordinateBiholomorph_apply (q : Ω) :
    (coordinateBiholomorph k Ω hΩ W hW hLift hCoords q : component) = liftMap k Ω hΩ q := rfl

@[simp] theorem coordinateBiholomorph_symm_apply (x : W) :
    ((coordinateBiholomorph k Ω hΩ W hW hLift hCoords).symm x : ℂ × ℂ) = coordinates k x := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
