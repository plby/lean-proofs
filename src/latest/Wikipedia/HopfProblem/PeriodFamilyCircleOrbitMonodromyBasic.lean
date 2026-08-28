import Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-!
# Transporting the genuine circle quotients

A homeomorphism between original period tori that intertwines their actual
delta-circle actions induces a homeomorphism of their original orbit
quotients.  Conjugation by the proved fixed-period comparisons then gives
the corresponding map of the marked lattice or mapping-torus models.
The concrete period changes are supplied in the following files.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

local notation "Circle" => AddCircle (1 : ℝ)

variable {p q : PeriodDomain} (e : p.Torus ≃ₜ q.Torus)
  (he : ∀ (t : Circle) (x : p.Torus),
    e (circleFlow p t x) = circleFlow q t (e x))

include he

theorem circleOrbitProjection_congr_eq_iff (x y : p.Torus) :
    circleOrbitProjection p x = circleOrbitProjection p y ↔
      circleOrbitProjection q (e x) = circleOrbitProjection q (e y) := by
  rw [circleOrbitProjection_eq_iff, circleOrbitProjection_eq_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (he t y).symm.trans (congrArg e ht)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, e.injective ((he t y).trans ht)⟩

/-- The homeomorphism induced on the actual delta-circle orbit quotients. -/
def circleOrbitCongr : CircleOrbit p ≃ₜ CircleOrbit q :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph
    (circleOrbitProjection p) (fun x => circleOrbitProjection q (e x))
    (circleOrbitProjection_isOpenQuotientMap p).isQuotientMap
    ((circleOrbitProjection_isOpenQuotientMap q).isQuotientMap.comp e.isQuotientMap)
    (circleOrbitProjection_congr_eq_iff e he)

@[simp] theorem circleOrbitCongr_projection (x : p.Torus) :
    circleOrbitCongr e he (circleOrbitProjection p x) = circleOrbitProjection q (e x) :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_apply _ _ _ _ _ x

@[simp] theorem circleOrbitCongr_symm_projection (y : q.Torus) :
    (circleOrbitCongr e he).symm (circleOrbitProjection q y) =
      circleOrbitProjection p (e.symm y) := by
  apply (circleOrbitCongr e he).injective
  rw [Homeomorph.apply_symm_apply, circleOrbitCongr_projection, Homeomorph.apply_symm_apply]

/-- The induced transport in the literal three-period lattice models. -/
def orbitModelCongr : OrbitModel p ≃ₜ OrbitModel q :=
  ((orbitModelHomeomorph p).symm.trans (circleOrbitCongr e he)).trans
    (orbitModelHomeomorph q)

@[simp] theorem orbitModelCongr_projection (x : p.Torus) :
    orbitModelCongr e he (torusProjection p x) = torusProjection q (e x) := by
  change orbitModelHomeomorph q
    (circleOrbitCongr e he ((orbitModelHomeomorph p).symm (torusProjection p x))) = _
  rw [← orbitModelHomeomorph_projection, Homeomorph.symm_apply_apply,
    circleOrbitCongr_projection, orbitModelHomeomorph_projection]

/-- The same original transport in the genuine elliptic mapping-torus models. -/
def mappingTorusCongr : MappingTorusModel p ≃ₜ MappingTorusModel q :=
  ((circleMappingTorusHomeomorph p).symm.trans (circleOrbitCongr e he)).trans
    (circleMappingTorusHomeomorph q)

@[simp] theorem mappingTorusCongr_projection (x : p.Torus) :
    mappingTorusCongr e he
      (circleMappingTorusHomeomorph p (circleOrbitProjection p x)) =
      circleMappingTorusHomeomorph q (circleOrbitProjection q (e x)) := by
  change circleMappingTorusHomeomorph q
    (circleOrbitCongr e he ((circleMappingTorusHomeomorph p).symm
      (circleMappingTorusHomeomorph p (circleOrbitProjection p x)))) = _
  rw [Homeomorph.symm_apply_apply, circleOrbitCongr_projection]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
