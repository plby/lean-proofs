import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.Support
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.NormalForm.Conjugation
import StackExchange.Puzzling139335.N4MiddleInvolutions.Remainder

/-!
# The actual middle pair satisfies the unit-base support dichotomy

An actual placement of the bottom piece normalizes one middle piece.  The
reflection is conjugated through that placement, and the actual common arc
of the middle pieces supplies the two distinct common points.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

theorem image_symm_of_image_eq {P Q : Set Plane}
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' P = Q) : f.symm '' Q = P := by
  rw [← hf, image_image]
  change (fun p => f.symm (f p)) '' P = P
  simp only [f.symm_apply_apply, image_id']

/-- The common-base alternative is an equality of actual sets. In the other
alternative the whole middle union is on the inward side of an actual
unit base transported from the bottom piece. -/
theorem middle_base_reflection_or_support {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 2 = d.piece 3)
    (c : ℂ) (u : Circle)
    (hform : ∀ p, PlaneIsometries.complexEquiv (e p) =
      c + (u : ℂ) * starRingEnd ℂ ((PlaneIsometries.complexEquiv p - c) / (u : ℂ)))
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' d.piece 0 = d.piece 2) :
    ((∀ x, e (f x) = f (!₂[x 0, -x 1] : Plane)) ∧
      d.piece 2 ∩ d.piece 3 = segment ℝ (f (corner 0)) (f (corner 1))) ∨
      ∀ z ∈ d.piece 2 ∪ d.piece 3, 0 ≤ (f.symm z) 1 := by
  let Q : Set Plane := f.symm '' d.piece 3
  let g : Plane ≃ᵃⁱ[ℝ] Plane := (f.trans e).trans f.symm
  have hback : f.symm '' d.piece 2 = d.piece 0 := image_symm_of_image_eq f hf
  have hforward : f '' Q = d.piece 3 := by
    dsimp only [Q]
    rw [image_image]
    change (fun p => f (f.symm p)) '' d.piece 3 = d.piece 3
    simp only [f.apply_symm_apply, image_id']
  have hg : g '' d.piece 0 = Q := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨e (f p), ?_, rfl⟩
      rw [← he]
      exact mem_image_of_mem e (hf ▸ mem_image_of_mem f hp)
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq, rfl⟩ := he.symm ▸ hp
      obtain ⟨r, hr, rfl⟩ := hf.symm ▸ hq
      exact ⟨r, hr, rfl⟩
  have hdis : Disjoint (interior (d.piece 0)) (interior Q) := by
    have hdisImage := RectangularHull.disjoint_interiors_image_homeomorph
      (d.disjoint_interiors (by decide : (2 : Fin 4) ≠ 3)) f.symm.toHomeomorph
    change Disjoint (interior (f.symm '' d.piece 2)) (interior Q) at hdisImage
    simpa only [hback] using hdisImage
  have hstrip : ∀ x ∈ d.piece 0, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 := by
    intro x hx
    have hxS := d.piece_subset 0 hx
    exact ⟨hxS.1.1, hxS.1.2, hxS.2.1⟩
  have hbase : segment ℝ (corner 0) (corner 1) ⊆ d.piece 0 := h.bottom_side hc
  have hcommon : (d.piece 0 ∩ Q).Nontrivial := by
    obtain ⟨p, hp, q, hq, hpq⟩ := middle_inter_nontrivial_of_involution h hc e
      (involutive_of_axis_form e c u hform) he
    refine ⟨f.symm p, ?_, f.symm q, ?_, ?_⟩
    · exact ⟨hback ▸ mem_image_of_mem f.symm hp.1, mem_image_of_mem f.symm hp.2⟩
    · exact ⟨hback ▸ mem_image_of_mem f.symm hq.1, mem_image_of_mem f.symm hq.2⟩
    · exact fun heq => hpq (f.symm.injective heq)
  obtain ⟨ν, k, hν, hgform⟩ :=
    exists_unit_normal_form_conjugate_of_axis_form e f c u hform
  rcases normal_reflection_unit_base_dichotomy (d.jordan 0) g hg hdis hν hgform
      hstrip hbase hcommon with hbaseMirror | hsupport
  · left
    refine ⟨?_, ?_⟩
    · intro x
      apply f.symm.injective
      change g x = f.symm (f (!₂[x 0, -x 1] : Plane))
      rw [f.symm_apply_apply]
      exact hbaseMirror x
    have hcommonBase := inter_eq_base_of_base_reflection g hg hstrip hbase hbaseMirror
    have himage : f '' (d.piece 0 ∩ Q) = d.piece 2 ∩ d.piece 3 := by
      rw [image_inter f.injective, hf, hforward]
    rw [← himage, hcommonBase]
    exact image_segment ℝ f.toAffineEquiv.toAffineMap _ _
  · right
    intro z hz
    apply hsupport (f.symm z)
    rcases hz with hz | hz
    · exact Or.inl (hback ▸ mem_image_of_mem f.symm hz)
    · exact Or.inr (mem_image_of_mem f.symm hz)

/-- The set-level projection of the stronger base-reflection alternative. -/
theorem middle_common_base_or_support {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 2 = d.piece 3)
    (c : ℂ) (u : Circle)
    (hform : ∀ p, PlaneIsometries.complexEquiv (e p) =
      c + (u : ℂ) * starRingEnd ℂ ((PlaneIsometries.complexEquiv p - c) / (u : ℂ)))
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' d.piece 0 = d.piece 2) :
    d.piece 2 ∩ d.piece 3 = segment ℝ (f (corner 0)) (f (corner 1)) ∨
      ∀ z ∈ d.piece 2 ∪ d.piece 3, 0 ≤ (f.symm z) 1 := by
  rcases middle_base_reflection_or_support h hc e he c u hform f hf with
    ⟨_, hcommon⟩ | hsupport
  · exact Or.inl hcommon
  · exact Or.inr hsupport

end Puzzling139335.N4MiddleInvolutions.Reflection
