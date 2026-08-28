import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.PeriodMatrixComparison
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Comparing the two actual singular homology markings of a period torus

The period-domain coordinates index the columns `[Z | I]`, while the
full-period coordinates index `[I | Z]`. The existing biholomorphism is
induced by the identity on the covering vector space. It therefore sends
each actual straight period loop to the same loop with the two blocks
reordered. Naturality of actual singular homology proves the resulting
marked comparison, including the exact ordered coordinate formula.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodDomain

open FirstHurewicz

/-- Reorder the source's four column coordinates `[Z | I]` into the
two integer pairs used for `[I | Z]`. -/
def fullPeriodCoordinatesEquiv : Lattice ≃ₗ[ℤ] FullPeriodMatrix.IntegerPeriods where
  toFun c := (![c 2, c 3], ![c 0, c 1])
  invFun c := ![c.2 0, c.2 1, c.1 0, c.1 1]
  left_inv c := by ext i; fin_cases i <;> rfl
  right_inv c := by ext i <;> fin_cases i <;> rfl
  map_add' c d := by ext i <;> fin_cases i <;> rfl
  map_smul' n c := by ext i <;> fin_cases i <;> rfl

@[simp] theorem fullPeriodCoordinatesEquiv_apply (c : Lattice) :
    fullPeriodCoordinatesEquiv c = (![c 2, c 3], ![c 0, c 1]) := rfl

@[simp] theorem fullPeriodCoordinatesEquiv_symm_apply (c : FullPeriodMatrix.IntegerPeriods) :
    fullPeriodCoordinatesEquiv.symm c = ![c.2 0, c.2 1, c.1 0, c.1 1] := rfl

variable (p : PeriodDomain) (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock)

/-- The actual continuous map underlying the identity-induced comparison
biholomorphism of the two period quotients. -/
def fullPeriodContinuousMap : C(p.Torus, q.Torus) :=
  ⟨p.fullPeriodBiholomorph q h, (p.fullPeriodBiholomorph q h).continuous⟩

@[simp] theorem fullPeriodContinuousMap_mkQ (z : ComplexPlane₂) :
    p.fullPeriodContinuousMap q h (p.lattice.mkQ z) = q.lattice.mkQ z := rfl

@[simp] theorem fullPeriodContinuousMap_zero : p.fullPeriodContinuousMap q h 0 = 0 := by
  simpa only [map_zero] using p.fullPeriodContinuousMap_mkQ q h 0

include h in
/-- Reordering the coordinates leaves the actual complex period vector unchanged. -/
theorem fullPeriod_periodVector (c : Lattice) :
    q.periodVector (fullPeriodCoordinatesEquiv c) = p.periodVector c := by
  ext i
  fin_cases i <;>
    simp [FullPeriodMatrix.periodVector, periodVector, fullPeriodCoordinatesEquiv,
      h, PeriodPoint.leftBlock, PeriodPoint.matrix, dotProduct,
      Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The comparison sends the actual marked straight loop to the
corresponding actual straight loop, with only its basepoint equality cast. -/
theorem fullPeriod_periodLoop (c : Lattice) :
    (p.periodLoop c).map (p.fullPeriodContinuousMap q h).continuous =
      (q.periodLoop (fullPeriodCoordinatesEquiv c)).cast
        (p.fullPeriodContinuousMap_zero q h) (p.fullPeriodContinuousMap_zero q h) := by
  ext t
  change p.fullPeriodContinuousMap q h (p.periodLoop c t) =
    q.periodLoop (fullPeriodCoordinatesEquiv c) t
  rw [periodLoop_apply, fullPeriodContinuousMap_mkQ,
    FullPeriodMatrix.periodLoop_apply, p.fullPeriod_periodVector q h]

/-- Naturality of genuine singular homology on the actual marked period loops. -/
theorem fullPeriod_inducedHomology_periodLoop (c : Lattice) :
    inducedHomology (p.fullPeriodContinuousMap q h) (loopHomologyClass (p.periodLoop c)) =
      loopHomologyClass (q.periodLoop (fullPeriodCoordinatesEquiv c)) := by
  rw [inducedHomology_loopHomologyClass, p.fullPeriod_periodLoop q h]
  rfl

/-- The two actual integral singular homology markings differ by precisely
the indicated exchange of their period blocks. -/
theorem fullPeriod_singularH1 (a : SingularH1 p.Torus) :
    q.singularH1Equiv (inducedHomology (p.fullPeriodContinuousMap q h) a) =
      fullPeriodCoordinatesEquiv (p.singularH1Equiv a) := by
  obtain ⟨c, rfl⟩ := p.singularH1Equiv.symm.surjective a
  rw [p.singularH1Equiv_symm_apply, p.fullPeriod_inducedHomology_periodLoop q h,
    q.singularH1Equiv_periodLoop, p.singularH1Equiv_periodLoop]

/-- Explicitly, the source coordinate order `(v₀,v₁,v₂,v₃)` becomes
the pair `((v₂,v₃),(v₀,v₁))` in the cusp/full-period convention. -/
theorem fullPeriod_singularH1_coordinates (a : SingularH1 p.Torus) :
    q.singularH1Equiv (inducedHomology (p.fullPeriodContinuousMap q h) a) =
      (![p.singularH1Equiv a 2, p.singularH1Equiv a 3],
        ![p.singularH1Equiv a 0, p.singularH1Equiv a 1]) :=
  p.fullPeriod_singularH1 q h a

/-- The corresponding equality of actual induced integral linear maps. -/
theorem fullPeriod_singularH1_conjugate :
    q.singularH1Equiv.toLinearMap.comp
      ((inducedHomology (p.fullPeriodContinuousMap q h)).comp
        p.singularH1Equiv.symm.toLinearMap) = fullPeriodCoordinatesEquiv.toLinearMap := by
  apply LinearMap.ext
  intro c
  change q.singularH1Equiv
    (inducedHomology (p.fullPeriodContinuousMap q h) (p.singularH1Equiv.symm c)) =
      fullPeriodCoordinatesEquiv c
  rw [p.fullPeriod_singularH1 q h, LinearEquiv.apply_symm_apply]

/-- The comparison isomorphism of actual singular homology, with its
forward map proved below to be the actual map induced by the biholomorphism. -/
def fullPeriodSingularH1Equiv : SingularH1 p.Torus ≃ₗ[ℤ] SingularH1 q.Torus :=
  (p.singularH1Equiv.trans fullPeriodCoordinatesEquiv).trans q.singularH1Equiv.symm

@[simp] theorem fullPeriodSingularH1Equiv_apply (a : SingularH1 p.Torus) :
    p.fullPeriodSingularH1Equiv q a = inducedHomology (p.fullPeriodContinuousMap q h) a := by
  apply q.singularH1Equiv.injective
  change q.singularH1Equiv
    (q.singularH1Equiv.symm (fullPeriodCoordinatesEquiv (p.singularH1Equiv a))) = _
  rw [LinearEquiv.apply_symm_apply, p.fullPeriod_singularH1 q h]

theorem fullPeriodSingularH1Equiv_toLinearMap :
    (p.fullPeriodSingularH1Equiv q).toLinearMap =
      inducedHomology (p.fullPeriodContinuousMap q h) := by
  apply LinearMap.ext
  exact p.fullPeriodSingularH1Equiv_apply q h

end Wikipedia.HopfProblem.PeriodDomain
