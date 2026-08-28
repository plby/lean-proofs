import Wikipedia.HopfProblem.DegreeCollapseFiniteCoefficientRank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Finite dual families of full possible size give a nondegenerate form

Evaluation against the opposite family recovers each coefficient. Thus
each coordinate map is injective. A matching dimension bound makes it
onto, and the two original families supply actual dual bases.
-/

noncomputable section

open Function Classical
open scoped BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.FiniteDualFamily

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype ι]
  (B : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜) (a b : ι → V)
  (hB : ∀ i j, B (a i) (b j) = if i = j then 1 else 0)

include hB

theorem coordinate_sum_eval (z : ι → 𝕜) (j : ι) :
    B (ReductionRank.coordinateSum (𝕜 := 𝕜) a z) (b j) = z j := by
  change (B.flip (b j)) (∑ i, z i • a i) = z j
  simp [map_sum, map_smul, LinearMap.flip_apply, hB]

theorem coordinateSum_injective : Injective (ReductionRank.coordinateSum (𝕜 := 𝕜) a) := by
  intro z w he
  funext j
  have h := congrArg (fun x => B x (b j)) he
  simpa only [coordinate_sum_eval B a b hB] using h

variable [FiniteDimensional 𝕜 V]

theorem coordinateSum_bijective (hdim : Module.finrank 𝕜 V ≤ Fintype.card ι) :
    Bijective (ReductionRank.coordinateSum (𝕜 := 𝕜) a) := by
  have hi := coordinateSum_injective B a b hB
  have hle := LinearMap.finrank_le_finrank_of_injective hi
  have he : Module.finrank 𝕜 (ι → 𝕜) = Module.finrank 𝕜 V := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      le_antisymm hle (by simpa only [Module.finrank_fintype_fun_eq_card] using hdim)
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mp hi⟩

def familyEquiv (hdim : Module.finrank 𝕜 V ≤ Fintype.card ι) : (ι → 𝕜) ≃ₗ[𝕜] V :=
  LinearEquiv.ofBijective (ReductionRank.coordinateSum (𝕜 := 𝕜) a)
    (coordinateSum_bijective B a b hB hdim)

theorem separatingLeft (hdim : Module.finrank 𝕜 V ≤ Fintype.card ι) :
    B.SeparatingLeft := by
  intro x hx
  obtain ⟨z, rfl⟩ := (coordinateSum_bijective B a b hB hdim).surjective x
  have hz : z = 0 := by
    funext j
    exact (coordinate_sum_eval B a b hB z j).symm.trans (hx (b j))
  rw [hz, map_zero]

theorem nondegenerate (hdim : Module.finrank 𝕜 V ≤ Fintype.card ι) :
    B.Nondegenerate := by
  refine ⟨separatingLeft B a b hB hdim, ?_⟩
  apply separatingLeft B.flip b a _ hdim
  intro i j
  change B (a j) (b i) = if i = j then 1 else 0
  rw [hB]
  simp only [eq_comm]

end Wikipedia.HopfProblem.DegreeCollapse.FiniteDualFamily
