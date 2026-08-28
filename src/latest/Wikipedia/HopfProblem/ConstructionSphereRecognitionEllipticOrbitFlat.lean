import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlat
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusTopology

/-!
# The marked delta-circle quotient of the original real four-torus

The original circle coordinates are ordered `(gamma,u,w,delta)`.  Removing
only the fourth coordinate is an open quotient map onto the actual product
of the first three circles.  Its fibres are exactly the translates of the
already constructed positive delta circle, with a unique circle parameter.
The original quotient topology and the original delta marking are retained.
No finite elliptic action is removed by this construction.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbitFlat

open Elliptic PeriodTorusHigherHomology
open SpecialPeriods.Threefold.Homology.DeltaSweep

local notation "Circle" => AddCircle (1 : ℝ)

/-- The actual three circle coordinates `(gamma,u,w)`, with their product topology. -/
abbrev DeltaBase := ProductTorus 3

/-- Remove precisely the fourth coordinate from the original standard-lattice quotient. -/
def dropDelta : RealTorus₄ →ₗ[ℤ] DeltaBase where
  toFun x i := flatTorusCircleMap x i.castSucc
  map_add' x y := by
    ext i
    exact congrFun (flatTorusCircleMap.map_add x y) i.castSucc
  map_smul' r x := by
    ext i
    exact congrFun (flatTorusCircleMap.map_smul r x) i.castSucc

@[simp] theorem dropDelta_apply (x : RealTorus₄) (i : Fin 3) :
    dropDelta x i = flatTorusCircleHomeomorph x i.castSucc := rfl

/-- The exact first-three-coordinate formula on every original real representative. -/
@[simp] theorem dropDelta_mkQ (a : RealCoordinates) :
    dropDelta (standardLattice.mkQ a) =
      coordinateProjection 3 (fun i => a i.castSucc) := rfl

@[simp] theorem dropDelta_mkQ_apply (a : RealCoordinates) (i : Fin 3) :
    dropDelta (standardLattice.mkQ a) i = (a i.castSucc : Circle) := rfl

/-- The first retained coordinate is precisely the original gamma circle. -/
@[simp] theorem dropDelta_apply_zero (x : RealTorus₄) :
    dropDelta x 0 = TrianglePeriodFamily.GammaZero.fibreGamma x := rfl

theorem dropDelta_continuous : Continuous dropDelta :=
  continuous_pi (fun i => (continuous_apply i.castSucc).comp flatTorusCircleMap_continuous)

def dropDeltaMap : C(RealTorus₄, DeltaBase) := ⟨dropDelta, dropDelta_continuous⟩

@[simp] theorem dropDeltaMap_apply (x : RealTorus₄) : dropDeltaMap x = dropDelta x := rfl

/-- The unchanged fourth circle coordinate of the original real torus. -/
def deltaCoordinate : RealTorus₄ →ₗ[ℤ] Circle :=
  (LinearMap.proj (3 : Fin 4)).comp flatTorusCircleMap

@[simp] theorem deltaCoordinate_apply (x : RealTorus₄) :
    deltaCoordinate x = flatTorusCircleHomeomorph x 3 := rfl

@[simp] theorem deltaCoordinate_mkQ (a : RealCoordinates) :
    deltaCoordinate (standardLattice.mkQ a) = (a 3 : Circle) := rfl

theorem deltaCoordinate_continuous : Continuous deltaCoordinate :=
  (continuous_apply 3).comp flatTorusCircleMap_continuous

/-- A literal product splitting of the actual four circle coordinates. -/
def splitDelta : RealTorus₄ ≃ₜ DeltaBase × Circle where
  toFun x := (dropDelta x, deltaCoordinate x)
  invFun p := flatTorusCircleHomeomorph.symm (Fin.snoc p.1 p.2)
  left_inv x := by
    apply flatTorusCircleHomeomorph.injective
    change flatTorusCircleHomeomorph
        (flatTorusCircleHomeomorph.symm
          (Fin.snoc (Fin.init (flatTorusCircleHomeomorph x))
            (flatTorusCircleHomeomorph x (Fin.last 3)))) = flatTorusCircleHomeomorph x
    rw [Homeomorph.apply_symm_apply, Fin.snoc_init_self]
  right_inv p := by
    apply Prod.ext
    · ext i
      change flatTorusCircleHomeomorph
          (flatTorusCircleHomeomorph.symm (Fin.snoc p.1 p.2)) i.castSucc = p.1 i
      rw [Homeomorph.apply_symm_apply, Fin.snoc_castSucc]
    · change flatTorusCircleHomeomorph
          (flatTorusCircleHomeomorph.symm (Fin.snoc p.1 p.2)) (Fin.last 3) = p.2
      rw [Homeomorph.apply_symm_apply, Fin.snoc_last]
  continuous_toFun := dropDelta_continuous.prodMk deltaCoordinate_continuous
  continuous_invFun := flatTorusCircleHomeomorph.symm.continuous.comp
    ((continuous_fst : Continuous (Prod.fst : DeltaBase × Circle → DeltaBase)).finSnoc
      continuous_snd)

@[simp] theorem splitDelta_apply (x : RealTorus₄) :
    splitDelta x = (dropDelta x, deltaCoordinate x) := rfl

@[simp] theorem splitDelta_mkQ (a : RealCoordinates) :
    splitDelta (standardLattice.mkQ a) =
      (coordinateProjection 3 (fun i => a i.castSucc), (a 3 : Circle)) := rfl

@[simp] theorem splitDelta_symm_apply (p : DeltaBase × Circle) :
    splitDelta.symm p = flatTorusCircleHomeomorph.symm (Fin.snoc p.1 p.2) := rfl

/-- This is an open quotient for the original quotient and product topologies. -/
theorem dropDelta_isOpenQuotientMap : IsOpenQuotientMap dropDelta :=
  isOpenQuotientMap_fst.comp splitDelta.isOpenQuotientMap

theorem dropDelta_surjective : Function.Surjective dropDelta :=
  dropDelta_isOpenQuotientMap.surjective

theorem dropDelta_isQuotientMap : IsQuotientMap dropDelta :=
  dropDelta_isOpenQuotientMap.isQuotientMap

/-- The already constructed actual positive delta circle vanishes in exactly these coordinates. -/
@[simp] theorem dropDelta_deltaCircle (d : Circle) : dropDelta (deltaCircle d) = 0 := by
  ext i
  rw [dropDelta_apply, flatTorusCircleHomeomorph_deltaCircle]
  fin_cases i <;> simp [coordinateCircleMap_apply, deltaLattice]

/-- The fourth coordinate recovers the original delta-circle parameter,
without a multiple or sign. -/
@[simp] theorem deltaCoordinate_deltaCircle (d : Circle) :
    deltaCoordinate (deltaCircle d) = d := by
  rw [deltaCoordinate_apply, flatTorusCircleHomeomorph_deltaCircle]
  simp [coordinateCircleMap_apply, deltaLattice]

theorem deltaCircle_injective : Function.Injective deltaCircle := by
  intro d e h
  have he := congrArg deltaCoordinate h
  simpa only [deltaCoordinate_deltaCircle] using he

@[simp] theorem dropDelta_add_deltaCircle (x : RealTorus₄) (d : Circle) :
    dropDelta (x + deltaCircle d) = dropDelta x := by
  rw [map_add, dropDelta_deltaCircle, add_zero]

@[simp] theorem deltaCoordinate_add_deltaCircle (x : RealTorus₄) (d : Circle) :
    deltaCoordinate (x + deltaCircle d) = deltaCoordinate x + d := by
  rw [map_add, deltaCoordinate_deltaCircle]

/-- Equality in the actual three-circle target is precisely the original delta orbit relation. -/
theorem dropDelta_eq_iff (x y : RealTorus₄) :
    dropDelta x = dropDelta y ↔ ∃ d : Circle, x = y + deltaCircle d := by
  constructor
  · intro h
    refine ⟨deltaCoordinate x - deltaCoordinate y, ?_⟩
    apply splitDelta.injective
    apply Prod.ext
    · change dropDelta x = dropDelta (y + deltaCircle (deltaCoordinate x - deltaCoordinate y))
      rw [dropDelta_add_deltaCircle]
      exact h
    · change deltaCoordinate x =
        deltaCoordinate (y + deltaCircle (deltaCoordinate x - deltaCoordinate y))
      rw [deltaCoordinate_add_deltaCircle]
      abel
  · rintro ⟨d, rfl⟩
    exact dropDelta_add_deltaCircle y d

/-- The actual delta parameter in each quotient fibre is unique. -/
theorem dropDelta_eq_iff_existsUnique (x y : RealTorus₄) :
    dropDelta x = dropDelta y ↔ ∃! d : Circle, x = y + deltaCircle d := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (dropDelta_eq_iff x y).mp h
    refine ⟨d, hd, ?_⟩
    intro e he
    exact deltaCircle_injective (add_left_cancel (he.symm.trans hd))
  · rintro ⟨d, hd, _⟩
    exact (dropDelta_eq_iff x y).mpr ⟨d, hd⟩

/-- There is no extra circle isotropy on the original four-torus. -/
theorem add_deltaCircle_eq_self_iff (x : RealTorus₄) (d : Circle) :
    x + deltaCircle d = x ↔ d = 0 := by
  constructor
  · intro h
    have he := congrArg deltaCoordinate h
    rw [deltaCoordinate_add_deltaCircle] at he
    exact add_left_cancel (he.trans (add_zero _).symm)
  · rintro rfl
    rw [deltaCircle_zero, add_zero]

/-- The original real fourth-coordinate translation has exactly the integral periods. -/
theorem add_real_delta_eq_self_iff (x : RealTorus₄) (t : ℝ) :
    x + standardLattice.mkQ (t • Pi.basisFun ℝ (Fin 4) 3) = x ↔
      ∃ n : ℤ, (n : ℝ) = t := by
  rw [← deltaCircle_real_apply, add_deltaCircle_eq_self_iff]
  simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ) (x := t))

/-- The quotient forgets precisely the literal original real delta translation. -/
theorem dropDelta_add_real_delta (x : RealTorus₄) (t : ℝ) :
    dropDelta (x + standardLattice.mkQ (t • Pi.basisFun ℝ (Fin 4) 3)) = dropDelta x := by
  rw [← deltaCircle_real_apply, dropDelta_add_deltaCircle]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbitFlat
