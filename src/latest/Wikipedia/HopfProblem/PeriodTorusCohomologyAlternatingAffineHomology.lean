import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarking
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# The actual affine elliptic action on the exterior homology marking

The linear fixed-period biholomorphism acts on positive period loops
by its actual integral matrix.  Naturality of the genuine exterior-square
marking therefore gives its action on actual second singular homology.
The previously proved translation homotopy identifies the affine action
with that linear action, for every integral twist.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

open FirstHurewicz SingularMayerVietoris

/-- The genuine fixed-period linear biholomorphism is additive on the quotient torus. -/
theorem linearBiholomorph_add (j : Kind) (p : FixedPeriod j) (x y : p.val.Torus) :
    linearBiholomorph j p (x + y) = linearBiholomorph j p x + linearBiholomorph j p y := by
  obtain ⟨u, rfl⟩ := p.val.lattice.mkQ_surjective x
  obtain ⟨v, rfl⟩ := p.val.lattice.mkQ_surjective y
  rw [← map_add, linearBiholomorph_mkQ]
  simp only [map_add, linearBiholomorph_mkQ]

@[simp] theorem linearBiholomorph_zero (j : Kind) (p : FixedPeriod j) :
    linearBiholomorph j p 0 = 0 := by
  simpa only [map_zero] using linearBiholomorph_mkQ j p 0

/-- The actual linear elliptic map sends each positive period class by its integral matrix. -/
theorem linearBiholomorph_singularH1_symm (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    singularHomologyMap
        ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) 1
        (p.val.singularH1Equiv.symm v) =
      p.val.singularH1Equiv.symm (j.matrix.mulVecLin v) := by
  let f : C(p.val.Torus, p.val.Torus) := (linearBiholomorph j p).toHomeomorph
  have hzero : f 0 = 0 := by
    change linearBiholomorph j p (0 : p.val.Torus) = 0
    exact linearBiholomorph_zero j p
  have hcast : (fun i => ((j.matrix *ᵥ v) i : ℂ)) =
      j.matrix.map (Int.castRingHom ℂ) *ᵥ (fun i => (v i : ℂ)) := by
    funext i
    exact (Int.castRingHom ℂ).map_mulVec j.matrix v i
  have hperiod : linearMatrix j p.val *ᵥ p.val.periodVector v =
      p.val.periodVector (j.matrix *ᵥ v) := by
    rw [PeriodDomain.periodVector_apply, PeriodDomain.periodVector_apply, hcast,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, linearMatrix_period_matrix]
  have hloop : (p.val.periodLoop v).map f.continuous =
      (p.val.periodLoop (j.matrix *ᵥ v)).cast hzero hzero := by
    ext t
    change linearBiholomorph j p (p.val.periodLoop v t) =
      p.val.periodLoop (j.matrix *ᵥ v) t
    rw [PeriodDomain.periodLoop_apply, linearBiholomorph_mkQ,
      PeriodDomain.periodLoop_apply, linearEquiv_apply, Matrix.mulVec_smul, hperiod]
  rw [PeriodDomain.singularH1Equiv_symm_apply, PeriodDomain.singularH1Equiv_symm_apply]
  change inducedHomology f (loopHomologyClass (p.val.periodLoop v)) =
    loopHomologyClass (p.val.periodLoop (j.matrix *ᵥ v))
  rw [inducedHomology_loopHomologyClass, hloop]
  rfl

/-- The positive period marking gives the actual matrix action on all first homology. -/
theorem linearBiholomorph_singularH1 (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 1) :
    p.val.singularH1Equiv (singularHomologyMap
        ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) 1 a) =
      j.matrix.mulVecLin (p.val.singularH1Equiv a) := by
  obtain ⟨v, rfl⟩ := p.val.singularH1Equiv.symm.surjective a
  rw [linearBiholomorph_singularH1_symm, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Conjugating the actual linear first-homology map gives the literal integral matrix map. -/
theorem linearBiholomorph_singularH1_conjugate (j : Kind) (p : FixedPeriod j) :
    p.val.singularH1Equiv.toLinearMap.comp
        ((singularHomologyMap
          ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) 1).comp
          p.val.singularH1Equiv.symm.toLinearMap) =
      j.matrix.mulVecLin := by
  apply LinearMap.ext
  intro v
  change p.val.singularH1Equiv (singularHomologyMap
    ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus)) 1
    (p.val.singularH1Equiv.symm v)) = j.matrix.mulVecLin v
  rw [linearBiholomorph_singularH1_symm, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.Elliptic

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic SingularMayerVietoris

/-- The actual fixed-period linear map acts by the exterior square of its integral matrix. -/
theorem periodTorusH2ExteriorEquiv_linearBiholomorph (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 2) :
    periodTorusH2ExteriorEquiv p.val
      (singularHomologyMap ((linearBiholomorph j p).toHomeomorph :
        C(p.val.Torus, p.val.Torus)) 2 a) =
      exteriorPower.map 2 j.matrix.mulVecLin (periodTorusH2ExteriorEquiv p.val a) :=
  periodTorusH2ExteriorEquiv_natural p.val p.val
    ((linearBiholomorph j p).toHomeomorph : C(p.val.Torus, p.val.Torus))
    (linearBiholomorph_add j p) j.matrix.mulVecLin
    (linearBiholomorph_singularH1_symm j p) a

/-- Every actual affine twist has the same proved exterior-square homology action. -/
theorem periodTorusH2ExteriorEquiv_affineBiholomorph (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (a : SingularHomology p.val.Torus 2) :
    periodTorusH2ExteriorEquiv p.val
      (singularHomologyMap ((affineBiholomorph j p v).toHomeomorph :
        C(p.val.Torus, p.val.Torus)) 2 a) =
      exteriorPower.map 2 j.matrix.mulVecLin (periodTorusH2ExteriorEquiv p.val a) := by
  rw [affineBiholomorph_singularHomologyMap]
  exact periodTorusH2ExteriorEquiv_linearBiholomorph j p a

/-- Equality of the entire actual induced linear map in the exterior-square marking. -/
theorem periodTorusH2_linearBiholomorph_conjugate (j : Kind) (p : FixedPeriod j) :
    (periodTorusH2ExteriorEquiv p.val).toLinearMap.comp
      ((singularHomologyMap ((linearBiholomorph j p).toHomeomorph :
        C(p.val.Torus, p.val.Torus)) 2).comp
          (periodTorusH2ExteriorEquiv p.val).symm.toLinearMap) =
      exteriorPower.map 2 j.matrix.mulVecLin := by
  apply LinearMap.ext
  intro a
  change periodTorusH2ExteriorEquiv p.val
    (singularHomologyMap ((linearBiholomorph j p).toHomeomorph :
      C(p.val.Torus, p.val.Torus)) 2 ((periodTorusH2ExteriorEquiv p.val).symm a)) = _
  rw [periodTorusH2ExteriorEquiv_linearBiholomorph, LinearEquiv.apply_symm_apply]

/-- The genuine affine map gives the same complete exterior-square operator for every twist. -/
theorem periodTorusH2_affineBiholomorph_conjugate (j : Kind) (p : FixedPeriod j)
    (v : Lattice) :
    (periodTorusH2ExteriorEquiv p.val).toLinearMap.comp
      ((singularHomologyMap ((affineBiholomorph j p v).toHomeomorph :
        C(p.val.Torus, p.val.Torus)) 2).comp
          (periodTorusH2ExteriorEquiv p.val).symm.toLinearMap) =
      exteriorPower.map 2 j.matrix.mulVecLin := by
  rw [affineBiholomorph_singularHomologyMap, periodTorusH2_linearBiholomorph_conjugate]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
