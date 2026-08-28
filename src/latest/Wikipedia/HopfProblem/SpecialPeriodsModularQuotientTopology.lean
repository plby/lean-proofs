import Wikipedia.HopfProblem.SpecialPeriodsModularQuotient
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

/-!
# Topology of the actual modular orbit quotient

The arithmetic action of `SL₂(ℤ)` on the upper half-plane is properly
discontinuous, including its nontrivial finite stabilizers. Consequently
the actual orbit space is Hausdorff, locally compact, second countable and
path connected. Neither a free action nor separation of orbits by `j` is
assumed.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods

instance modularGroup_continuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ :=
    continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)

/-- Transfer arithmetic proper discontinuity along the faithful matrix
embedding, without assuming the induced Möbius action is faithful. -/
instance modularGroup_properlyDiscontinuous : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  constructor
  intro K L hK hL
  have hfinite : {g : GL (Fin 2) ℝ | g ∈ 𝒮ℒ ∧ (g • K ∩ L).Nonempty}.Finite :=
    (Subgroup.properlyDiscontinuousSMul_iff 𝒮ℒ).mp inferInstance hK hL
  have hpre := hfinite.preimage
    (Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (n := Fin 2) (S := ℝ)).injOn
  exact hpre.subset fun γ hγ => ⟨⟨γ, rfl⟩, hγ⟩

theorem modularOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap modularOrbitProjection :=
  MulAction.isOpenQuotientMap_quotientMk

theorem modularOrbitProjection_isOpenMap : IsOpenMap modularOrbitProjection :=
  modularOrbitProjection_isOpenQuotientMap.isOpenMap

instance modularOrbitSpace_t2 : T2Space ModularOrbitSpace :=
  t2Space_of_properlyDiscontinuousSMul_of_t2Space

instance modularOrbitSpace_locallyCompact : LocallyCompactSpace ModularOrbitSpace :=
  modularOrbitProjection_isOpenQuotientMap.locallyCompactSpace

instance modularOrbitSpace_secondCountable : SecondCountableTopology ModularOrbitSpace :=
  ContinuousConstSMul.secondCountableTopology

instance modularOrbitSpace_pathConnected : PathConnectedSpace ModularOrbitSpace :=
  modularOrbitProjection_surjective.pathConnectedSpace modularOrbitProjection_continuous

theorem modularGroup_stabilizer_finite (z : ℍ) :
    (MulAction.stabilizer SL(2, ℤ) z : Set SL(2, ℤ)).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer z

/-- Near a point, only elements of its finite stabilizer can identify
points of that neighbourhood with each other. -/
theorem modularGroup_exists_nhds_disjoint_image (z : ℍ) :
    ∃ U ∈ 𝓝 z, ∀ γ : SL(2, ℤ), γ • z ≠ z → Disjoint ((γ • ·) '' U) U :=
  ProperlyDiscontinuousSMul.exists_nhds_disjoint_image SL(2, ℤ) z

end Wikipedia.HopfProblem.SpecialPeriods
