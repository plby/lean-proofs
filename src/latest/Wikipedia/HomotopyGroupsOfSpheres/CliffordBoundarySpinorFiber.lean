import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryHopfPair
import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-! # The Hopf two-plane preserves actual circle fibers and has simply connected total space -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open NoExoticSixSphere NoExoticSixSphere.RankSixComplexProjection

def pairFiber : C(Circle, UnitPair) where
  toFun z := ⟨(z : ℂ) • pairPole.val, mem_sphere_zero_iff_norm.mpr (by
    rw [norm_smul, Circle.norm_coe, unitPair_norm, one_mul])⟩
  continuous_toFun := (continuous_subtype_val.smul continuous_const).subtype_mk _

theorem pairFiber_one : pairFiber 1 = pairPole := by
  apply Subtype.ext
  change (1 : ℂ) • pairPole.val = pairPole.val
  rw [one_smul]

theorem hopfMap_pairFiber (z : Circle) : hopfMap (pairFiber z) = structurePole := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [hopfMap, hopfCoordinates, pairFiber, pairPole, structurePole,
      EuclideanSpace.basisFun_apply]

theorem unscaledPairVector_smul (z : ℂ) (q : PairSpace) :
    unscaledPairVector (z • q) = z • unscaledPairVector q := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [unscaledPairVector]

theorem spinorPlaneMap_pairFiber (z : Circle) :
    spinorPlaneMap (pairFiber z) = phaseSmul z (spinorPlaneMap pairPole) := by
  apply Subtype.ext
  change planeCoefficient • unscaledPairVector ((z : ℂ) • pairPole.val) =
    (z : ℂ) • (planeCoefficient • unscaledPairVector pairPole.val)
  rw [unscaledPairVector_smul, smul_comm]

theorem exists_poleSpinor : ∃ A : UnitSpinor, A = spinorPlaneMap pairPole :=
  ⟨spinorPlaneMap pairPole, rfl⟩

/-- A named base spinor with its exact coordinate identity, without unfolding the coordinates. -/
def poleSpinor : UnitSpinor := Classical.choose exists_poleSpinor

theorem poleSpinor_eq : poleSpinor = spinorPlaneMap pairPole :=
  Classical.choose_spec exists_poleSpinor

theorem structureMap_pole : structureMap structurePole = fromSpinor poleSpinor := by
  rw [poleSpinor_eq]
  have h := fromSpinor_plane pairPole
  rw [hopfMap_pairPole] at h
  exact h.symm

theorem pair_finrank_real : Module.finrank ℝ PairSpace = 4 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

def pairCoordinates : PairSpace ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((stdOrthonormalBasis ℝ PairSpace).reindex (finCongr pair_finrank_real)).repr

def unitPairHomeomorph : UnitPair ≃ₜ Sphere 3 := unitSphereCongr pairCoordinates

def pairFiberLoop (q : GenLoop (Fin 1) Circle 1) : GenLoop (Fin 1) UnitPair pairPole :=
  pointedMapGenLoop pairFiber 1 pairPole pairFiber_one q

theorem pairFiberLoop_nullhomotopic (q : GenLoop (Fin 1) Circle 1) :
    GenLoop.Homotopic (pairFiberLoop q) GenLoop.const :=
  genLoop_homotopic_const_of_homeomorph_sphere (by decide : 1 < 3)
    unitPairHomeomorph pairPole (pairFiberLoop q)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
