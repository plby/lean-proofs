import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPolygons
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonMinimum

/-! # Balanced real involutions are homeomorphic to the actual minimum polygon locus -/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices

variable {m : ℕ}

def minimumSet (n : ℕ) (τ : Fin (m + 2) → ℝ) : Set (VertexSpace.Space (Index n) m) :=
  {v | v ∈ admissible specialIdentity (antipode n) m ∧
    energy specialIdentity (antipode n) τ v = (4 * n : ℝ) * Real.pi ^ 2}

variable (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))

include hτ hzero hone hsmall

theorem rotationVertices_mem_minimumSet (J : BalancedRealInvolutions.Space n) :
    rotationVertices τ J ∈ minimumSet n τ :=
  ⟨rotationVertices_admissible τ hzero hone J (hsmall J),
    energy_rotationVertices τ hzero hone J (hsmall J) hτ⟩

def minimumParametrization : C(BalancedRealInvolutions.Space n, minimumSet n τ) where
  toFun J := ⟨rotationVertices τ J, rotationVertices_mem_minimumSet n τ hτ hzero hone hsmall J⟩
  continuous_toFun := (continuous_rotationVertices n τ).subtype_mk _

theorem minimumParametrization_injective :
    Function.Injective (minimumParametrization n τ hτ hzero hone hsmall) := by
  intro J K h
  have hp := congrArg (fun w : minimumSet n τ ↦
    path specialIdentity (antipode n) τ hτ w.val w.property.1 (1 / 2)) h
  have hJ := path_rotationVertices τ hzero hone J (hsmall J) hτ
    (t := 1 / 2) (by norm_num)
  have hK := path_rotationVertices τ hzero hone K (hsmall K) hτ
    (t := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring] at hJ hK
  have he : rotation J (Real.pi / 2) = rotation K (Real.pi / 2) := hJ.symm.trans (hp.trans hK)
  apply Subtype.ext
  simpa only [rotation_midpoint_recover] using
    congrArg (fun B : SpecialSpace (Index n) ↦ B.val.val.val.map Complex.im) he

variable (hcompact : IsCompact
  (energySublevel specialIdentity (antipode n) τ ((4 * n : ℝ) * Real.pi ^ 2)))

include hcompact

theorem minimumParametrization_surjective :
    Function.Surjective (minimumParametrization n τ hτ hzero hone hsmall) := by
  intro v
  have hv : v.val ∈ energySublevel specialIdentity (antipode n) τ ((4 * n : ℝ) * Real.pi ^ 2) :=
    ⟨v.property.1, v.property.2.le⟩
  obtain ⟨J, hJ⟩ := (energy_eq_min_iff_rotation n τ hτ hzero hone _ hcompact v.val hv).mp
    v.property.2
  refine ⟨J, Subtype.ext ?_⟩
  funext j
  have ht : τ j.castSucc.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le _)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last _)
  have he := (path_vertex specialIdentity (antipode n) τ hτ v.val v.property.1
    j.castSucc.succ).symm.trans (hJ _ ht)
  change rotation J (τ j.castSucc.succ * Real.pi) = v.val j
  simpa only [vertices_interior] using he.symm

def rotationMinimumHomeomorph : BalancedRealInvolutions.Space n ≃ₜ minimumSet n τ :=
  IsHomeomorph.homeomorph (minimumParametrization n τ hτ hzero hone hsmall)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨(minimumParametrization n τ hτ hzero hone hsmall).continuous,
        minimumParametrization_injective n τ hτ hzero hone hsmall,
        minimumParametrization_surjective n τ hτ hzero hone hsmall hcompact⟩)

theorem rotationMinimumHomeomorph_apply (J : BalancedRealInvolutions.Space n) :
    (rotationMinimumHomeomorph n τ hτ hzero hone hsmall hcompact J).val =
      rotationVertices τ J := rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
