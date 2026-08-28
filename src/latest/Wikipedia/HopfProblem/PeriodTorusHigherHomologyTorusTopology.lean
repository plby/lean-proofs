import Wikipedia.HopfProblem.EllipticFlatTorus
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Actual period tori as products of circles

The quotient by the standard integral lattice is identified with the
product of four actual additive circles, with its product topology.
The formula on covering-space representatives fixes the coordinate
order used later for higher singular homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic FirstHurewicz

/-- A product of actual unit-period additive circles. -/
abbrev ProductTorus (n : ℕ) := Fin n → AddCircle (1 : ℝ)

/-- Reduction of each real coordinate modulo the integer lattice. -/
def coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ ProductTorus n where
  toFun x i := (x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; exact AddCircle.coe_add (1 : ℝ) (x i) (y i)

@[simp] theorem coordinateProjection_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateProjection n x i = (x i : AddCircle (1 : ℝ)) := rfl

theorem coordinateProjection_continuous (n : ℕ) : Continuous (coordinateProjection n) := by
  exact continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))

/-- The kernel consists exactly of tuples of integers, coordinate by coordinate. -/
theorem coordinateProjection_eq_zero_iff (n : ℕ) (x : Fin n → ℝ) :
    coordinateProjection n x = 0 ↔ ∃ v : Fin n → ℤ, x = fun i => (v i : ℝ) := by
  constructor
  · intro h
    have hi : ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
      intro i
      have hz := congrFun h i
      change (x i : AddCircle (1 : ℝ)) = 0 at hz
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    choose v hv using hi
    exact ⟨v, funext fun i => (hv i).symm⟩
  · rintro ⟨v, rfl⟩
    ext i
    change ((v i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨v i, by simp⟩

theorem coordinateProjection_surjective (n : ℕ) :
    Function.Surjective (coordinateProjection n) := by
  intro t
  have h : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = t i := by
    intro i
    exact QuotientAddGroup.mk_surjective (t i)
  choose x hx using h
  exact ⟨x, funext hx⟩

/-- Splitting off the first coordinate is an actual product homeomorphism. -/
def productTorusSuccHomeomorph (n : ℕ) :
    ProductTorus (n + 1) ≃ₜ AddCircle (1 : ℝ) × ProductTorus n where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := Fin.cons_self_tail x
  right_inv x := by simp
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

@[simp] theorem productTorusSuccHomeomorph_apply (n : ℕ) (x : ProductTorus (n + 1)) :
    productTorusSuccHomeomorph n x = (x 0, fun i => x i.succ) := rfl

@[simp] theorem productTorusSuccHomeomorph_symm_apply (n : ℕ)
    (x : AddCircle (1 : ℝ) × ProductTorus n) :
    (productTorusSuccHomeomorph n).symm x = Fin.cons x.1 x.2 := rfl

/-- The empty product has its actual one-point topology. -/
def productTorusZeroHomeomorph : ProductTorus 0 ≃ₜ PUnit where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The positive straight loop with a specified integral coordinate tuple. -/
def coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) : Path (0 : ProductTorus n) 0 :=
  ((Path.segment (0 : Fin n → ℝ) (fun i => (v i : ℝ))).map
    (coordinateProjection_continuous n)).cast (map_zero (coordinateProjection n)).symm
      ((coordinateProjection_eq_zero_iff n _).mpr ⟨v, rfl⟩).symm

@[simp] theorem coordinatePeriodLoop_apply (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) (i : Fin n) :
    coordinatePeriodLoop n v t i = ((t : ℝ) * (v i : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [coordinatePeriodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add,
    coordinateProjection_apply, Pi.smul_apply, smul_eq_mul]

/-- The standard real lattice is exactly the kernel of coordinate reduction. -/
theorem standardLattice_le_coordinateProjection_ker :
    standardLattice ≤ LinearMap.ker (coordinateProjection 4).toIntLinearMap := by
  intro x hx
  obtain ⟨v, rfl⟩ := (standardLattice_mem_iff x).mp hx
  exact (coordinateProjection_eq_zero_iff 4 _).mpr ⟨v, rfl⟩

/-- The actual real lattice quotient maps to its four circle coordinates. -/
def flatTorusCircleMap : RealTorus₄ →ₗ[ℤ] ProductTorus 4 :=
  standardLattice.liftQ (coordinateProjection 4).toIntLinearMap
    standardLattice_le_coordinateProjection_ker

@[simp] theorem flatTorusCircleMap_mkQ (x : RealPlane₄) :
    flatTorusCircleMap (standardLattice.mkQ x) = coordinateProjection 4 x := rfl

theorem flatTorusCircleMap_continuous : Continuous flatTorusCircleMap := by
  apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
  exact coordinateProjection_continuous 4

theorem flatTorusCircleMap_injective : Function.Injective flatTorusCircleMap := by
  intro a b hab
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective a
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective b
  have hz : coordinateProjection 4 (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hab
  obtain ⟨v, hv⟩ := (coordinateProjection_eq_zero_iff 4 (x - y)).mp hz
  apply (flatTorus_mkQ_eq_iff x y).mpr
  exact ⟨v, hv⟩

theorem flatTorusCircleMap_surjective : Function.Surjective flatTorusCircleMap := by
  intro t
  obtain ⟨x, hx⟩ := coordinateProjection_surjective 4 t
  exact ⟨standardLattice.mkQ x, hx⟩

/-- The quotient topology agrees with the product topology on the four circles. -/
def flatTorusCircleHomeomorph : RealTorus₄ ≃ₜ ProductTorus 4 :=
  Equiv.toHomeomorphOfContinuousClosed (Equiv.ofBijective flatTorusCircleMap
    ⟨flatTorusCircleMap_injective, flatTorusCircleMap_surjective⟩)
      flatTorusCircleMap_continuous flatTorusCircleMap_continuous.isClosedMap

@[simp] theorem flatTorusCircleHomeomorph_mkQ (x : RealPlane₄) :
    flatTorusCircleHomeomorph (standardLattice.mkQ x) = coordinateProjection 4 x := rfl

/-- The actual complex period torus has the same ordered circle coordinates. -/
def periodTorusCircleHomeomorph (p : PeriodDomain) : p.Torus ≃ₜ ProductTorus 4 :=
  (flatTorusPeriodHomeomorph p).symm.trans flatTorusCircleHomeomorph

@[simp] theorem periodTorusCircleHomeomorph_flatProjection
    (p : PeriodDomain) (x : RealCoordinates) :
    periodTorusCircleHomeomorph p (flatProjection p x) = coordinateProjection 4 x := by
  rw [periodTorusCircleHomeomorph, Homeomorph.trans_apply,
    flatTorusPeriodHomeomorph_symm_flatProjection, flatTorusCircleHomeomorph_mkQ]

@[simp] theorem periodTorusCircleHomeomorph_zero (p : PeriodDomain) :
    periodTorusCircleHomeomorph p 0 = 0 := by
  have h := periodTorusCircleHomeomorph_flatProjection p 0
  simpa only [flatProjection, map_zero] using h

/-- The coordinate homeomorphism preserves the actual positive period loops. -/
theorem periodTorusCircleHomeomorph_periodLoop_apply
    (p : PeriodDomain) (v : Lattice) (t : unitInterval) :
    periodTorusCircleHomeomorph p (p.periodLoop v t) = coordinatePeriodLoop 4 v t := by
  rw [PeriodDomain.periodLoop_apply]
  have hv : (t : ℝ) • p.periodVector v = periodEquiv p ((t : ℝ) • realCast v) := by
    rw [map_smul, periodEquiv_realCast, p.periodVector_eq_sum]
  rw [hv]
  change periodTorusCircleHomeomorph p (flatProjection p ((t : ℝ) • realCast v)) = _
  rw [periodTorusCircleHomeomorph_flatProjection]
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

theorem periodTorusCircleHomeomorph_periodLoop (p : PeriodDomain) (v : Lattice) :
    (p.periodLoop v).map (periodTorusCircleHomeomorph p).continuous =
      (coordinatePeriodLoop 4 v).cast (periodTorusCircleHomeomorph_zero p)
        (periodTorusCircleHomeomorph_zero p) := by
  apply Path.ext
  funext t
  exact periodTorusCircleHomeomorph_periodLoop_apply p v t

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
