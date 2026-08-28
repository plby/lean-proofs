import Wikipedia.HopfProblem.DegreeCollapseMiddleLabelBasis
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction
import Wikipedia.NoExoticSixSphere.ModHomologyModule
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Actual coefficient reduction bounds the mod-two middle dimension

An additive image of n integral generators is spanned by their actual
reductions over F2. Apply this to the native integral basis of the same
separated Morse system and the actual surjective coefficient map.
-/

noncomputable section

open Set Function
open Classical
open scoped ContDiff Manifold Topology BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.ReductionRank

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {ι : Type*} [Fintype ι]

def coordinateSum (v : ι → V) : (ι → 𝕜) →ₗ[𝕜] V where
  toFun a := ∑ i, a i • v i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum, smul_smul]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem integer_image_expansion (R : (ι → ℤ) →+ W) (z : ι → ℤ) :
    R z = ∑ i, (z i : ZMod 2) • R (Pi.single i 1) := by
  classical
  have hz : z = ∑ i, z i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Pi.single_apply]
  calc
    R z = R (∑ i, z i • Pi.single i (1 : ℤ)) := congrArg R hz
    _ = ∑ i, (z i : ZMod 2) • R (Pi.single i 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem exists_coefficient_surjection (R : (ι → ℤ) →+ W) (hR : Surjective R) :
    ∃ L : (ι → ZMod 2) →ₗ[ZMod 2] W, Surjective L := by
  classical
  refine ⟨coordinateSum (fun i => R (Pi.single i 1)), ?_⟩
  intro w
  obtain ⟨z, rfl⟩ := hR w
  exact ⟨fun i => (z i : ZMod 2), (integer_image_expansion R z).symm⟩

theorem finrank_le_of_integer_surjection (R : (ι → ℤ) →+ W) (hR : Surjective R) :
    Module.finrank (ZMod 2) W ≤ Fintype.card ι := by
  obtain ⟨L, hL⟩ := exists_coefficient_surjection R hR
  simpa only [Module.finrank_fintype_fun_eq_card] using LinearMap.finrank_le_finrank_of_surjective hL

end Wikipedia.HopfProblem.DegreeCollapse.ReductionRank

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

open SingularMayerVietoris SphereHomologyCoefficients NoExoticSixSphere
attribute [local instance] modHomologyModule

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [SimplyConnectedSpace M]
  (D : SeparatedSystem E M) (m : M) [h₂ : Subsingleton (π_ 2 M m)]

include D m h₂ in
theorem middle_modTwo_finite : Module.Finite (ZMod 2) (ModHomology 2 M 3) := by
  obtain ⟨n, -, ⟨b⟩⟩ := D.exists_middle_label_basis
  let R : (Fin n → ℤ) →+ ModHomology 2 M 3 :=
    (reductionHomologyMap 2 M 3).toAddMonoidHom.comp b.toAddEquiv.toAddMonoidHom
  have hR : Surjective R := (TwoConnectedCoefficients.middleReduction_surjective m).comp b.surjective
  obtain ⟨L, hL⟩ := ReductionRank.exists_coefficient_surjection R hR
  exact Module.Finite.of_surjective L hL

include m h₂ in
theorem middle_modTwo_finrank_le :
    Module.finrank (ZMod 2) (ModHomology 2 M 3) ≤ Nat.card D.MiddleLabel := by
  obtain ⟨n, ⟨e⟩, ⟨b⟩⟩ := D.exists_middle_label_basis
  let R : (Fin n → ℤ) →+ ModHomology 2 M 3 :=
    (reductionHomologyMap 2 M 3).toAddMonoidHom.comp b.toAddEquiv.toAddMonoidHom
  have hR : Surjective R := (TwoConnectedCoefficients.middleReduction_surjective m).comp b.surjective
  have hb := ReductionRank.finrank_le_of_integer_surjection R hR
  have hc : n = Nat.card D.MiddleLabel := by simpa only [Nat.card_fin] using Nat.card_congr e
  simpa only [Fintype.card_fin, hc] using hb

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
