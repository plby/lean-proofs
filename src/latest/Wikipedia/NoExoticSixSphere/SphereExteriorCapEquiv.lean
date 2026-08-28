import Wikipedia.NoExoticSixSphere.SphereExteriorCapImage

/-!
# Actual exterior-cap bijections with the retained original source

Each exterior cap, including its pole, parametrizes the complement of the
open reference disk. Reflection gives the southern bijection. The two cap
domains partition the complement of the neck region.
-/

noncomputable section

open Set Function Metric Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def northExterior : Set (Sphere 3) := {x | 0 < x.val 0 ∧ x ∉ neckRegion}

def southExterior : Set (Sphere 3) := {x | x.val 0 < 0 ∧ x ∉ neckRegion}

def northExteriorCap (ε : ℝ) (hε : 0 < ε) : northExterior → ↥((removedSourceDisk ε)ᶜ) :=
  fun x ↦ ⟨sphereCap ε x.val, fun h ↦ x.property.2
    ((sphereCap_mem_removed_iff hε x.property.1).mp h)⟩

theorem northExteriorCap_bijective (ε : ℝ) (hε : 0 < ε) :
    Bijective (northExteriorCap ε hε) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact sphereCap_injOn hε.ne' x.property.1 y.property.1 (congrArg Subtype.val he)
  · intro z
    have hz : z.val ≠ sourceChart 0 := by
      intro he
      exact z.property (he ▸ sourceChart_zero_mem_removed hε)
    have ht : z.val ∈ (sphereCapCoordinates ε hε.ne').target := by
      rwa [sphereCapCoordinates_target]
    let x := (sphereCapCoordinates ε hε.ne').symm z.val
    have hx : 0 < x.val 0 := by
      have hs := (sphereCapCoordinates ε hε.ne').map_target ht
      rwa [sphereCapCoordinates_source] at hs
    have he : sphereCap ε x = z.val := (sphereCapCoordinates ε hε.ne').right_inv ht
    have hn : x ∉ neckRegion := by
      intro hxn
      apply z.property
      rw [← he]
      exact (sphereCap_mem_removed_iff hε hx).mpr hxn
    exact ⟨⟨x, hx, hn⟩, Subtype.ext he⟩

def northExteriorEquiv (ε : ℝ) (hε : 0 < ε) : northExterior ≃ ↥((removedSourceDisk ε)ᶜ) :=
  Equiv.ofBijective (northExteriorCap ε hε) (northExteriorCap_bijective ε hε)

theorem northExteriorEquiv_val (ε : ℝ) (hε : 0 < ε) (x : northExterior) :
    (northExteriorEquiv ε hε x).val = sphereCap ε x.val := rfl

def exteriorReflection : southExterior ≃ northExterior where
  toFun x := ⟨reflectHead x.val, by
    constructor
    · rw [reflectHead_head]
      exact neg_pos.mpr x.property.1
    · exact fun h ↦ x.property.2 ((reflectHead_mem_neckRegion_iff x.val).mp h)⟩
  invFun x := ⟨reflectHead x.val, by
    constructor
    · rw [reflectHead_head]
      exact neg_neg_of_pos x.property.1
    · exact fun h ↦ x.property.2 ((reflectHead_mem_neckRegion_iff x.val).mp h)⟩
  left_inv x := Subtype.ext (reflectHead_involutive x.val)
  right_inv x := Subtype.ext (reflectHead_involutive x.val)

def southExteriorEquiv (ε : ℝ) (hε : 0 < ε) : southExterior ≃ ↥((removedSourceDisk ε)ᶜ) :=
  exteriorReflection.trans (northExteriorEquiv ε hε)

theorem southExteriorEquiv_val (ε : ℝ) (hε : 0 < ε) (x : southExterior) :
    (southExteriorEquiv ε hε x).val = sphereCap ε (reflectHead x.val) := rfl

theorem exterior_cover {x : Sphere 3} (hx : x ∉ neckRegion) :
    x ∈ northExterior ∨ x ∈ southExterior := by
  rcases (sourceRegion_cover x).resolve_left hx with hn | hs
  · exact Or.inl ⟨northRegion_head_pos hn, hx⟩
  · exact Or.inr ⟨southRegion_head_neg hs, hx⟩

theorem disjoint_exterior : Disjoint northExterior southExterior := by
  apply disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_gt hx.1) hy.1

theorem northExterior_mem_northRegion {x : Sphere 3} (hx : x ∈ northExterior) :
    x ∈ northRegion := by
  rcases (sourceRegion_cover x).resolve_left hx.2 with hn | hs
  · exact hn
  · exact ((not_lt_of_gt hx.1) (southRegion_head_neg hs)).elim

theorem southExterior_mem_southRegion {x : Sphere 3} (hx : x ∈ southExterior) :
    x ∈ southRegion := by
  rcases (sourceRegion_cover x).resolve_left hx.2 with hn | hs
  · exact ((not_lt_of_gt (northRegion_head_pos hn)) hx.1).elim
  · exact hs

end NoExoticSixSphere.SphereSumNeck
