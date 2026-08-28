import Wikipedia.NoExoticSixSphere.SphereCylinderPoles

/-!
# Actual finite punctures under the sphere-cylinder compactification

Add the two genuine poles to the images of the selected cylinder points.
The complement is homeomorphic to the original cylinder with precisely those
selected points removed. No arbitrary equivalence of underlying types is used.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

def punctures (n : ℕ) (S : Set (ℝ × Sphere n)) : Set (Sphere (n + 1)) :=
  {endPole n false, endPole n true} ∪ point n '' S

theorem finite_punctures (n : ℕ) {S : Set (ℝ × Sphere n)} (hS : S.Finite) :
    (punctures n S).Finite :=
  ((finite_singleton (endPole n true)).insert (endPole n false)).union (hS.image (point n))

theorem isOpen_compl_punctures (n : ℕ) {S : Set (ℝ × Sphere n)} (hS : S.Finite) :
    IsOpen (punctures n S)ᶜ := (finite_punctures n hS).isClosed.isOpen_compl

theorem point_mem_punctures_iff (n : ℕ) (S : Set (ℝ × Sphere n)) (p : ℝ × Sphere n) :
    point n p ∈ punctures n S ↔ p ∈ S := by
  constructor
  · rintro (hpole | himage)
    · have hb : point n p ∈ band n := tail_point_ne_zero n p
      rcases hpole with he | he
      · exact False.elim (endPole_not_mem_band n false (he ▸ hb))
      · exact False.elim (endPole_not_mem_band n true (he ▸ hb))
    · obtain ⟨q, hq, he⟩ := himage
      exact injective_point n he ▸ hq
  · intro hp
    exact Or.inr ⟨p, hp, rfl⟩

theorem compl_punctures_subset_band (n : ℕ) (S : Set (ℝ × Sphere n)) :
    (punctures n S)ᶜ ⊆ band n := by
  intro y hy
  by_contra hb
  exact hy (Or.inl ((not_mem_band_iff n y).mp hb))

def puncturedHomeomorph (n : ℕ) (S : Set (ℝ × Sphere n)) :
    ((punctures n S)ᶜ : Set (Sphere (n + 1))) ≃ₜ (Sᶜ : Set (ℝ × Sphere n)) where
  toFun y := ⟨inverse n y.val, fun hs ↦ y.property
    (Or.inr ⟨inverse n y.val, hs,
      point_inverse n y.val (compl_punctures_subset_band n S y.property)⟩)⟩
  invFun p := ⟨point n p.val, (point_mem_punctures_iff n S p.val).not.mpr p.property⟩
  left_inv y := Subtype.ext
    (point_inverse n y.val (compl_punctures_subset_band n S y.property))
  right_inv p := Subtype.ext (inverse_point n p.val)
  continuous_toFun := by
    have hc : ContinuousOn (inverse n) (punctures n S)ᶜ :=
      (chart n).contMDiffOn_invFun.continuousOn.mono (compl_punctures_subset_band n S)
    exact hc.domRestrict.subtype_mk _
  continuous_invFun := ((point n).continuous.comp continuous_subtype_val).subtype_mk _

theorem puncturedHomeomorph_apply (n : ℕ) (S : Set (ℝ × Sphere n))
    (y : ((punctures n S)ᶜ : Set (Sphere (n + 1)))) :
    (puncturedHomeomorph n S y).val = inverse n y.val := rfl

theorem puncturedHomeomorph_symm_apply (n : ℕ) (S : Set (ℝ × Sphere n))
    (p : (Sᶜ : Set (ℝ × Sphere n))) :
    ((puncturedHomeomorph n S).symm p).val = point n p.val := rfl

end NoExoticSixSphere.SphereCylinder
