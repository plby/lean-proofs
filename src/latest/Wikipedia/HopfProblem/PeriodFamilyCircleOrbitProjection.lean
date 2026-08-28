import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitAction
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLinear
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLattice

/-!
# The original period torus maps to the marked three-dimensional quotient

The displayed real-linear projection takes the original four-column
period lattice onto the integral span of `(6μ,1)`, `(τ,0)`, and `(1,0)`.
Its descended map has exactly the original delta-circle orbits as fibres.
In particular the `6μ` translation is retained, not removed by an unmarked
product identification.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open Elliptic
open SpecialPeriods.Threefold.VerticalAction.Period (vector)

local notation "Circle" => AddCircle (1 : ℝ)

/-- Every original period maps to a period of the marked orbit model. -/
theorem linearProjection_mem_orbitLattice (p : PeriodDomain) {z : ComplexPlane₂}
    (hz : z ∈ p.lattice) : linearProjection p z ∈ orbitLattice p := by
  obtain ⟨n, hn⟩ := (p.mem_lattice_iff z).mp hz
  rw [← hn, p.periodVector_eq_sum, ← periodEquiv_realCast, linearProjection_periodEquiv]
  exact (mem_orbitLattice_iff_projectedPeriods p _).mpr ⟨fun i => n i.castSucc, rfl⟩

/-- The image is exactly the displayed lattice, including its first generator. -/
theorem linearProjection_map_lattice (p : PeriodDomain) :
    p.lattice.map ((linearProjection p).toLinearMap.restrictScalars ℤ) = orbitLattice p := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact linearProjection_mem_orbitLattice p hw
  · intro hz
    obtain ⟨n, rfl⟩ := (mem_orbitLattice_iff_projectedPeriods p z).mp hz
    let v : Lattice := Fin.snoc n 0
    refine ⟨periodEquiv p (realCast v), ?_, ?_⟩
    · exact (periodEquiv_mem_lattice_iff p _).mpr ⟨v, rfl⟩
    · change linearProjection p (periodEquiv p (realCast v)) = _
      rw [linearProjection_periodEquiv]
      congr 1
      ext i
      simp [v, realCast]

/-- The map on the original complex period quotient induced by the literal `L`. -/
def torusProjection (p : PeriodDomain) : p.Torus →ₗ[ℤ] OrbitModel p :=
  p.lattice.mapQ (orbitLattice p) ((linearProjection p).toLinearMap.restrictScalars ℤ)
    (fun _ hz => linearProjection_mem_orbitLattice p hz)

@[simp] theorem torusProjection_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    torusProjection p (p.lattice.mkQ z) = orbitClass p (linearProjection p z) := rfl

theorem torusProjection_continuous (p : PeriodDomain) : Continuous (torusProjection p) := by
  apply p.lattice.isQuotientMap_mkQ.continuous_iff.mpr
  exact (orbitClass_continuous p).comp (linearProjection p).continuous

theorem torusProjection_surjective (p : PeriodDomain) :
    Function.Surjective (torusProjection p) := by
  intro x
  obtain ⟨z, rfl⟩ := orbitClass_surjective p x
  obtain ⟨w, rfl⟩ := linearProjection_surjective p z
  exact ⟨p.lattice.mkQ w, rfl⟩

/-- Real vertical translation is killed before passing to either quotient. -/
@[simp] theorem linearProjection_vector_real (p : PeriodDomain) (t : ℝ) :
    linearProjection p (vector (t : ℂ)) = 0 := by
  simp [linearProjection_apply, vector]

@[simp] theorem torusProjection_circleFlow (p : PeriodDomain) (t : Circle) (x : p.Torus) :
    torusProjection p (circleFlow p t x) = torusProjection p x := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [circleFlow_coe, map_add, torusProjection_mkQ, linearProjection_vector_real,
    map_zero, add_zero]

/-- Equality in the marked three-dimensional quotient is exactly one original
delta-circle orbit, including all lattice identifications. -/
theorem torusProjection_eq_iff (p : PeriodDomain) (x y : p.Torus) :
    torusProjection p x = torusProjection p y ↔
      ∃ t : Circle, circleFlow p t y = x := by
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := p.lattice.mkQ_surjective x
    obtain ⟨w, rfl⟩ := p.lattice.mkQ_surjective y
    have hl : linearProjection p (z - w) ∈ orbitLattice p := by
      rw [map_sub]
      exact (orbitClass_eq_iff p _ _).mp h
    rw [← linearProjection_map_lattice p] at hl
    obtain ⟨v, hv, he⟩ := hl
    change linearProjection p v = linearProjection p (z - w) at he
    have hk : linearProjection p ((z - w) - v) = 0 := by
      rw [map_sub, he, sub_self]
    obtain ⟨t, ht⟩ := (linearProjection_eq_zero_iff p _).mp hk
    change (z - w) - v = vector (t : ℂ) at ht
    have hz : z = w + vector (t : ℂ) + v := by
      calc
        z = ((z - w) - v) + v + w := by abel
        _ = w + vector (t : ℂ) + v := by rw [ht]; abel
    refine ⟨(t : Circle), ?_⟩
    have hv₀ : p.lattice.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hv
    simp only [circleFlow_coe_mkQ, hz, map_add, hv₀, add_zero]
  · rintro ⟨t, rfl⟩
    exact torusProjection_circleFlow p t y

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
