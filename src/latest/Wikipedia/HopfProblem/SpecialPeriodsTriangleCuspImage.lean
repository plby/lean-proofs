import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspCompactification
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspBall

/-!
# The exponential chart on the actual full quotient cusp image

The high horodisc is precisely invariant under the proved cyclic cusp
subgroup.  Its actual subgroup orbit quotient is therefore homeomorphic
to its image in the full triangle orbit space.  The exponential cusp
coordinate identifies this image with a punctured complex ball.

All quotients and topologies are inherited from the already constructed
triangle action.  No identification of the global quotient with a sphere
or any complex structure at the added cusp is assumed here.
-/

noncomputable section

open Function Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] triangleGeometricAction triangleGeometricAction_continuous

/-- The actual cyclic cusp quotient of the height-`Y` horodisc. -/
abbrev CuspHorodiscQuotient (Y : ℝ) :=
  LocalOrbitQuotient.LocalQuotient (Subgroup.zpowers triangleCuspGenerator)
    (horodisc Y) (cusp_horodisc_invariant Y)

/-- The genuine cyclic-orbit projection on the horodisc. -/
def cuspHorodiscProjection (Y : ℝ) : horodisc Y → CuspHorodiscQuotient Y :=
  LocalOrbitQuotient.localProjection _ _ _

theorem cuspHorodiscProjection_eq_iff (Y : ℝ) (z w : horodisc Y) :
    cuspHorodiscProjection Y z = cuspHorodiscProjection Y w ↔
      ∃ n : ℤ, triangleGeometricRepresentation (triangleCuspGenerator ^ n) (w : ℍ) =
        (z : ℍ) := by
  rw [cuspHorodiscProjection, LocalOrbitQuotient.localProjection_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    refine ⟨n, ?_⟩
    rw [hn]
    exact hg
  · rintro ⟨n, hn⟩
    exact ⟨⟨triangleCuspGenerator ^ n, Subgroup.zpow_mem_zpowers _ _⟩, hn⟩

theorem cuspHorodiscProjection_surjective (Y : ℝ) :
    Surjective (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_surjective _ _ _

theorem cuspHorodiscProjection_continuous (Y : ℝ) :
    Continuous (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_continuous _ _ _

theorem cuspHorodiscProjection_isOpenQuotientMap (Y : ℝ) :
    IsOpenQuotientMap (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_isOpenQuotientMap _ _ _

/-- The full quotient projection restricted to the horodisc, with its
actual image as codomain. -/
def cuspImageProjection (Y : ℝ) : horodisc Y → cuspImage Y :=
  LocalOrbitQuotient.imageProjection (G := TriangleGroup) (horodisc Y)

@[simp] theorem cuspImageProjection_coe (Y : ℝ) (z : horodisc Y) :
    (cuspImageProjection Y z : TriangleOrbitSpace) = triangleOrbitProjection (z : ℍ) := rfl

theorem cuspImageProjection_surjective (Y : ℝ) : Surjective (cuspImageProjection Y) :=
  LocalOrbitQuotient.imageProjection_surjective (horodisc Y)

theorem cuspImageProjection_continuous (Y : ℝ) : Continuous (cuspImageProjection Y) :=
  LocalOrbitQuotient.imageProjection_continuous (horodisc Y)

theorem cuspImageProjection_isOpenQuotientMap (Y : ℝ) :
    IsOpenQuotientMap (cuspImageProjection Y) :=
  LocalOrbitQuotient.imageProjection_isOpenQuotientMap (horodisc Y)

/-- Precise invariance identifies the actual cyclic quotient of the
high horodisc with its open image in the full triangle quotient. -/
def cuspHorodiscImageHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    CuspHorodiscQuotient Y ≃ₜ cuspImage Y :=
  LocalOrbitQuotient.localHomeomorph (Subgroup.zpowers triangleCuspGenerator)
    (horodisc Y) (cusp_horodisc_invariant Y)
    (triangle_horodisc_overlap_mem_cusp Y hY)

@[simp] theorem cuspHorodiscImageHomeomorph_mk (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    cuspHorodiscImageHomeomorph Y hY (cuspHorodiscProjection Y z) =
      cuspImageProjection Y z := rfl

@[simp] theorem cuspHorodiscImageHomeomorph_symm_mk (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    (cuspHorodiscImageHomeomorph Y hY).symm (cuspImageProjection Y z) =
      cuspHorodiscProjection Y z :=
  (cuspHorodiscImageHomeomorph Y hY).symm_apply_apply (cuspHorodiscProjection Y z)

/-- Two representatives high in the horodisc have the same full orbit
precisely when their actual exponential coordinates agree. -/
theorem cuspImageProjection_eq_iff (Y : ℝ) (hY : width ≤ Y) (z w : horodisc Y) :
    cuspImageProjection Y z = cuspImageProjection Y w ↔ cuspQ (z : ℍ) = cuspQ (w : ℍ) := by
  rw [← cuspHorodiscImageHomeomorph_mk Y hY z, ← cuspHorodiscImageHomeomorph_mk Y hY w,
    (cuspHorodiscImageHomeomorph Y hY).injective.eq_iff,
    cuspHorodiscProjection_eq_iff, cuspQ_eq_iff]

/-- The exponential, descended to the actual cyclic quotient of the
horodisc by its proved equality-of-fibres criterion. -/
def cuspHorodiscToBall (Y : ℝ) : CuspHorodiscQuotient Y → puncturedCuspBall Y :=
  Quotient.lift (cuspQHorodisc Y) fun z w h =>
    (cuspQHorodisc_eq_iff Y z w).mpr
      ((cuspHorodiscProjection_eq_iff Y z w).mp (Quotient.sound h))

@[simp] theorem cuspHorodiscToBall_mk (Y : ℝ) (z : horodisc Y) :
    cuspHorodiscToBall Y (cuspHorodiscProjection Y z) = cuspQHorodisc Y z := rfl

theorem cuspHorodiscToBall_injective (Y : ℝ) : Injective (cuspHorodiscToBall Y) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro z w h
  exact (cuspHorodiscProjection_eq_iff Y z w).mpr ((cuspQHorodisc_eq_iff Y z w).mp h)

theorem cuspHorodiscToBall_surjective (Y : ℝ) (hY : 0 ≤ Y) :
    Surjective (cuspHorodiscToBall Y) := by
  intro q
  obtain ⟨z, rfl⟩ := cuspQHorodisc_surjective Y hY q
  exact ⟨cuspHorodiscProjection Y z, rfl⟩

theorem cuspHorodiscToBall_continuous (Y : ℝ) : Continuous (cuspHorodiscToBall Y) :=
  (cuspQHorodisc_continuous Y).quotient_lift _

theorem cuspHorodiscToBall_isOpenMap (Y : ℝ) : IsOpenMap (cuspHorodiscToBall Y) :=
  IsOpenMap.of_comp (cuspHorodiscProjection_continuous Y)
    (cuspHorodiscProjection_surjective Y) (cuspQHorodisc_isOpenMap Y)

/-- The actual cyclic quotient of a nonnegative-height horodisc is the
punctured ball with radius given by the exact cusp exponential. -/
def cuspHorodiscBallHomeomorph (Y : ℝ) (hY : 0 ≤ Y) :
    CuspHorodiscQuotient Y ≃ₜ puncturedCuspBall Y :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (cuspHorodiscToBall Y)
      ⟨cuspHorodiscToBall_injective Y, cuspHorodiscToBall_surjective Y hY⟩)
    (cuspHorodiscToBall_continuous Y) (cuspHorodiscToBall_isOpenMap Y)

@[simp] theorem cuspHorodiscBallHomeomorph_mk (Y : ℝ) (hY : 0 ≤ Y) (z : horodisc Y) :
    cuspHorodiscBallHomeomorph Y hY (cuspHorodiscProjection Y z) = cuspQHorodisc Y z := rfl

/-- The genuine exponential cusp chart on the open cusp image in the
full actual triangle orbit space.  The lower height bound is sufficient
for the proved precise invariance; no quotient uniformization is used. -/
def cuspImageHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    cuspImage Y ≃ₜ puncturedCuspBall Y :=
  (cuspHorodiscImageHomeomorph Y hY).symm.trans
    (cuspHorodiscBallHomeomorph Y (width_pos.le.trans hY))

@[simp] theorem cuspImageHomeomorph_mk (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspImageHomeomorph Y hY (cuspImageProjection Y z) = cuspQHorodisc Y z := by
  change cuspHorodiscToBall Y
    ((cuspHorodiscImageHomeomorph Y hY).symm (cuspImageProjection Y z)) = _
  rw [cuspHorodiscImageHomeomorph_symm_mk]
  rfl

/-- The chart evaluates to the original, unmodified exponential on
every representative in the high horodisc. -/
@[simp] theorem cuspImageHomeomorph_mk_coe (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (cuspImageHomeomorph Y hY (cuspImageProjection Y z) : ℂ) = cuspQ (z : ℍ) := by
  rw [cuspImageHomeomorph_mk]
  rfl

theorem cuspImageHomeomorph_mk_exp (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (cuspImageHomeomorph Y hY (cuspImageProjection Y z) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℍ) / width) := by
  rw [cuspImageHomeomorph_mk_coe, cuspQ_eq_exp]

@[simp] theorem cuspImageHomeomorph_symm_q (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (cuspImageHomeomorph Y hY).symm (cuspQHorodisc Y z) = cuspImageProjection Y z := by
  rw [← cuspImageHomeomorph_mk Y hY z, Homeomorph.symm_apply_apply]

/-- Inside a high cusp image, going higher in the horodisc is exactly
shrinking the radius in the actual exponential coordinate. -/
theorem cuspImageHomeomorph_norm_lt_iff (Y Z : ℝ) (hY : width ≤ Y) (hYZ : Y ≤ Z)
    (x : cuspImage Y) :
    ‖(cuspImageHomeomorph Y hY x : ℂ)‖ < cuspRadius Z ↔
      (x : TriangleOrbitSpace) ∈ cuspImage Z := by
  obtain ⟨z, rfl⟩ := cuspImageProjection_surjective Y x
  rw [cuspImageHomeomorph_mk_coe]
  change ‖cuspQ (z : ℍ)‖ < Real.exp (-2 * Real.pi * Z / width) ↔
    ∃ w : ℍ, Z < w.im ∧ triangleOrbitProjection w = triangleOrbitProjection (z : ℍ)
  rw [cuspQ_norm_lt_exp_iff]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, he⟩
    have hwY : w ∈ horodisc Y := hYZ.trans_lt hw
    have he' : cuspImageProjection Y ⟨w, hwY⟩ = cuspImageProjection Y z := Subtype.ext he
    have hq := (cuspImageProjection_eq_iff Y hY ⟨w, hwY⟩ z).mp he'
    have hnorm := (cuspQ_norm_lt_exp_iff Z w).mpr hw
    rw [hq] at hnorm
    exact (cuspQ_norm_lt_exp_iff Z (z : ℍ)).mp hnorm

/-- Changing the chosen high horodisc does not change the complex cusp
coordinate on the common image. -/
theorem cuspImageHomeomorph_restrict (Y Z : ℝ) (hY : width ≤ Y) (hYZ : Y ≤ Z)
    (x : cuspImage Z) :
    (cuspImageHomeomorph Y hY
      ⟨(x : TriangleOrbitSpace), cuspImage_antitone hYZ x.property⟩ : ℂ) =
      (cuspImageHomeomorph Z (hY.trans hYZ) x : ℂ) := by
  obtain ⟨z, rfl⟩ := cuspImageProjection_surjective Z x
  have hzY : (z : ℍ) ∈ horodisc Y := hYZ.trans_lt z.property
  change (cuspImageHomeomorph Y hY (cuspImageProjection Y ⟨z, hzY⟩) : ℂ) = _
  rw [cuspImageHomeomorph_mk_coe, cuspImageHomeomorph_mk_coe]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
