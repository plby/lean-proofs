import Wikipedia.NoExoticSixSphere.JamesSpherePunctureDilation

/-!
# The actual sphere-cover overlap retracts onto the James middle slice

Conjugating the explicit antipodal-pole deformation by finite coordinate
dilation gives a strong deformation on the original cover overlap. The
retract is the literal middle-slice embedding, not a replacement sphere.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.JamesSphere.Overlap

theorem equator_mem (n : ℕ) (x : Equator (equatorPole n)) : x.val ∈ overlap n :=
  (dilation_mem_punctured_iff n x.val).mp
    (SphereEquatorRetraction.equator_mem (equatorPole n) (equatorDilation n x))

def inclusion (n : ℕ) : C(Equator (equatorPole n), overlap n) :=
  ⟨fun x ↦ ⟨x.val, equator_mem n x⟩, continuous_subtype_val.subtype_mk _⟩

theorem equator_square (n : ℕ) (x : Equator (equatorPole n)) :
    overlapHomeomorph n (inclusion n x) =
      SphereEquatorRetraction.inclusion (equatorPole n) (equatorDilation n x) := rfl

theorem inverse_equator (n : ℕ) (x : Equator (equatorPole n)) :
    (overlapHomeomorph n).symm (SphereEquatorRetraction.inclusion (equatorPole n) x) =
      inclusion n ((equatorDilation n).symm x) := by
  apply (overlapHomeomorph n).injective
  rw [Homeomorph.apply_symm_apply, equator_square, Homeomorph.apply_symm_apply]

def retraction (n : ℕ) : C(overlap n, Equator (equatorPole n)) :=
  ⟨fun y ↦ (equatorDilation n).symm
    (SphereEquatorRetraction.retraction (equatorPole n) (overlapHomeomorph n y)),
    (equatorDilation n).symm.continuous.comp
      ((SphereEquatorRetraction.retraction (equatorPole n)).continuous.comp
        (overlapHomeomorph n).continuous)⟩

theorem retraction_inclusion (n : ℕ) (x : Equator (equatorPole n)) :
    retraction n (inclusion n x) = x := by
  change (equatorDilation n).symm
    (SphereEquatorRetraction.retraction (equatorPole n)
      (overlapHomeomorph n (inclusion n x))) = x
  rw [equator_square, SphereEquatorRetraction.retraction_inclusion, Homeomorph.symm_apply_apply]

def point (n : ℕ) (s : I) (y : overlap n) : overlap n :=
  (overlapHomeomorph n).symm
    (SphereEquatorRetraction.point (equatorPole n) s (overlapHomeomorph n y))

theorem continuous_point (n : ℕ) : Continuous (fun p : I × overlap n ↦ point n p.1 p.2) := by
  have hp : Continuous (fun p : I × overlap n ↦ (p.1, overlapHomeomorph n p.2)) :=
    continuous_fst.prodMk ((overlapHomeomorph n).continuous.comp continuous_snd)
  have hq : Continuous (fun p : I × overlap n ↦
      SphereEquatorRetraction.point (equatorPole n) p.1 (overlapHomeomorph n p.2)) :=
    (SphereEquatorRetraction.continuous_point (E := V (n + 2)) (equatorPole n)).comp
      (f := fun p : I × overlap n ↦ (p.1, overlapHomeomorph n p.2)) hp
  exact (overlapHomeomorph n).symm.continuous.comp hq

theorem point_zero (n : ℕ) (y : overlap n) : point n 0 y = y := by
  rw [point, SphereEquatorRetraction.point_zero, Homeomorph.symm_apply_apply]

theorem point_one (n : ℕ) (y : overlap n) : point n 1 y = inclusion n (retraction n y) := by
  rw [point, SphereEquatorRetraction.point_one, inverse_equator]
  rfl

theorem point_inclusion (n : ℕ) (s : I) (x : Equator (equatorPole n)) :
    point n s (inclusion n x) = inclusion n x := by
  rw [point, equator_square, SphereEquatorRetraction.point_inclusion, inverse_equator,
    Homeomorph.symm_apply_apply]

def deformation (n : ℕ) : (ContinuousMap.id (overlap n)).HomotopyRel
    ((inclusion n).comp (retraction n)) (Set.range (inclusion n)) where
  toFun p := point n p.1 p.2
  continuous_toFun := continuous_point n
  map_zero_left := point_zero n
  map_one_left := point_one n
  prop' s y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact point_inclusion n s x

def middleHomeomorph (n : ℕ) : Sphere n ≃ₜ Equator (equatorPole n) :=
  (middle_isClosedEmbedding n).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (middle_range_eq_equator n))

def middleInclusion (n : ℕ) : C(Sphere n, overlap n) :=
  (inclusion n).comp (middleHomeomorph n : C(Sphere n, Equator (equatorPole n)))

theorem middleInclusion_val (n : ℕ) (x : Sphere n) : (middleInclusion n x).val = middle n x := rfl

def middleRetraction (n : ℕ) : C(overlap n, Sphere n) :=
  ((middleHomeomorph n).symm : C(Equator (equatorPole n), Sphere n)).comp (retraction n)

theorem middleRetraction_inclusion (n : ℕ) (x : Sphere n) :
    middleRetraction n (middleInclusion n x) = x := by
  change (middleHomeomorph n).symm (retraction n (inclusion n (middleHomeomorph n x))) = x
  rw [retraction_inclusion, Homeomorph.symm_apply_apply]

def middleDeformation (n : ℕ) : (ContinuousMap.id (overlap n)).HomotopyRel
    ((middleInclusion n).comp (middleRetraction n)) (Set.range (middleInclusion n)) where
  toFun p := point n p.1 p.2
  continuous_toFun := continuous_point n
  map_zero_left := point_zero n
  map_one_left y := by
    rw [point_one]
    change inclusion n (retraction n y) =
      inclusion n (middleHomeomorph n ((middleHomeomorph n).symm (retraction n y)))
    rw [Homeomorph.apply_symm_apply]
  prop' s y hy := by
    obtain ⟨x, rfl⟩ := hy
    exact point_inclusion n s (middleHomeomorph n x)

end NoExoticSixSphere.JamesSphere.Overlap
