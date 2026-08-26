import ErdosProblems.Erdos633.LocalConeMeasure

/-!
# The local cone and sector constructions are intrinsic

Cone membership is characterized by a positive point on the ray lying in
the triangle. This removes the coordinate chart from affine transport, and
isometries preserve the unit-sector areas used for local angle accounting.
-/

namespace Erdos633

open MeasureTheory

theorem Triangle.mem_localConeAt_iff_exists_lineMap (P : Triangle) (z x : ℂ)
    (hz : z ∈ P.carrier) : x ∈ P.localConeAt z ↔
      ∃ t : ℝ, 0 < t ∧ AffineMap.lineMap z x t ∈ P.carrier := by
  constructor
  · intro hx
    obtain ⟨ε, hε, hmodel⟩ := P.exists_local_cone_radius z hz
    obtain ⟨t, ht, hnear⟩ := exists_positive_lineMap_mem_ball z x ε hε
    exact ⟨t, ht, (hmodel _ hnear).1.mpr ((P.localConeAt_lineMap_iff z x t ht).mpr hx)⟩
  · rintro ⟨t, ht, hy⟩
    apply (P.localConeAt_lineMap_iff z x t ht).mp
    intro i _
    exact (P.mem_carrier_iff_barycentric _).mp hy i

theorem Triangle.localConeAt_mapAffineEquiv (P : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ)
    (z : ℂ) (hz : z ∈ P.carrier) :
    (P.mapAffineEquiv e).localConeAt (e z) = e '' P.localConeAt z := by
  have hez : e z ∈ (P.mapAffineEquiv e).carrier := by
    rw [Triangle.mapAffineEquiv_carrier]
    exact ⟨z, hz, rfl⟩
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image, P.mem_localConeAt_iff_exists_lineMap z x hz,
    (P.mapAffineEquiv e).mem_localConeAt_iff_exists_lineMap (e z) (e x) hez]
  constructor
  · rintro ⟨t, ht, hy⟩
    refine ⟨t, ht, ?_⟩
    have heline : e (AffineMap.lineMap z x t) = AffineMap.lineMap (e z) (e x) t :=
      e.toAffineMap.apply_lineMap z x t
    rw [Triangle.mapAffineEquiv_carrier, ← heline] at hy
    exact e.injective.mem_set_image.mp hy
  · rintro ⟨t, ht, hy⟩
    refine ⟨t, ht, ?_⟩
    have heline : e (AffineMap.lineMap z x t) = AffineMap.lineMap (e z) (e x) t :=
      e.toAffineMap.apply_lineMap z x t
    rw [Triangle.mapAffineEquiv_carrier, ← heline]
    exact ⟨AffineMap.lineMap z x t, hy, rfl⟩

theorem Triangle.localConeAt_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ)
    (z : ℂ) (hz : z ∈ P.carrier) :
    (P.mapIsometry e).localConeAt (e z) = e '' P.localConeAt z :=
  P.localConeAt_mapAffineEquiv e.toRealAffineIsometryEquiv.toAffineEquiv z hz

theorem Triangle.localSector_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ)
    (z : ℂ) (hz : z ∈ P.carrier) :
    (P.mapIsometry e).localSector (e z) = e '' P.localSector z := by
  rw [Triangle.localSector, P.localConeAt_mapIsometry e z hz, ← e.image_ball z 1,
    ← Set.image_inter e.injective]
  rfl

theorem Triangle.localSectorArea_mapIsometry (P : Triangle) (e : ℂ ≃ᵢ ℂ)
    (z : ℂ) (hz : z ∈ P.carrier) :
    (P.mapIsometry e).localSectorArea (e z) = P.localSectorArea z := by
  unfold Triangle.localSectorArea
  rw [P.localSector_mapIsometry e z hz, isometry_volume_image]

theorem Triangle.localConeAt_eq_of_carrier_eq (P Q : Triangle)
    (h : P.carrier = Q.carrier) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localConeAt z = Q.localConeAt z := by
  ext x
  rw [P.mem_localConeAt_iff_exists_lineMap z x hz,
    Q.mem_localConeAt_iff_exists_lineMap z x (h ▸ hz), h]

theorem Triangle.localSector_eq_of_carrier_eq (P Q : Triangle)
    (h : P.carrier = Q.carrier) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localSector z = Q.localSector z := by
  rw [Triangle.localSector, Triangle.localSector,
    P.localConeAt_eq_of_carrier_eq Q h z hz]

theorem Triangle.localSectorArea_eq_of_carrier_eq (P Q : Triangle)
    (h : P.carrier = Q.carrier) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localSectorArea z = Q.localSectorArea z := by
  unfold Triangle.localSectorArea
  rw [P.localSector_eq_of_carrier_eq Q h z hz]

end Erdos633
