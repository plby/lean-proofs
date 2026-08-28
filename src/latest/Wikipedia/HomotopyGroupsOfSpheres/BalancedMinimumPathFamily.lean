import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumPathFamily

/-!
# The balanced real orbit embeds into the antipodal path space

Evaluation at the midpoint recovers the original real matrix. This is a
closed embedding into the native path space. No homotopy equivalence is
asserted by the construction of this map.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices NoExoticSixSphere.PathFamilies

private def phaseMap (n : ℕ) : C(I × Space n, ℝ × Space n) where
  toFun z := ((z.1 : ℝ) * Real.pi, z.2)
  continuous_toFun := by
    have ht : Continuous (fun z : I × Space n ↦ (z.1 : ℝ) * Real.pi) :=
      (continuous_subtype_val.comp continuous_fst).mul_const Real.pi
    exact ht.prodMk continuous_snd

private def rotationMap (n : ℕ) : C(ℝ × Space n, SpecialSpace (Index n)) :=
  ⟨fun z ↦ rotation z.2 z.1, continuous_rotation n⟩

def family (n : ℕ) : C(I × Space n, SpecialSpace (Index n)) :=
  (rotationMap n).comp (phaseMap n)

theorem family_zero (n : ℕ) (J : Space n) : family n (0, J) = specialIdentity := by
  change rotation J ((0 : ℝ) * Real.pi) = specialIdentity
  rw [zero_mul, rotation_zero]

theorem family_one (n : ℕ) (J : Space n) : family n (1, J) = antipode n := by
  change rotation J ((1 : ℝ) * Real.pi) = antipode n
  rw [one_mul, rotation_pi]

def pathMap (n : ℕ) : C(Space n, Path specialIdentity (antipode n)) :=
  curry (family n) (family_zero n) (family_one n)

theorem pathMap_midpoint (n : ℕ) (J : Space n) :
    ((pathMap n J) (⟨1 / 2, by norm_num⟩ : I)).val.val.val.map Complex.im = J.val := by
  change (rotation J ((1 / 2 : ℝ) * Real.pi)).val.val.val.map Complex.im = J.val
  rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring]
  exact rotation_midpoint_recover J

theorem pathMap_injective (n : ℕ) : Function.Injective (pathMap n) := by
  intro J K h
  have he := congrArg (fun p : Path specialIdentity (antipode n) ↦
    (p (⟨1 / 2, by norm_num⟩ : I)).val.val.val.map Complex.im) h
  rw [pathMap_midpoint, pathMap_midpoint] at he
  exact Subtype.ext he

theorem pathMap_isClosedEmbedding (n : ℕ) : Topology.IsClosedEmbedding (pathMap n) :=
  (pathMap n).continuous.isClosedEmbedding (pathMap_injective n)

def pathRangeHomeomorph (n : ℕ) : Space n ≃ₜ Set.range (pathMap n) :=
  (pathMap_isClosedEmbedding n).isEmbedding.toHomeomorph

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
