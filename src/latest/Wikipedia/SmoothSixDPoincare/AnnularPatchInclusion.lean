import Wikipedia.SmoothSixDPoincare.SmoothAnnularExchange
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphIntoOpen

/-! # Full-source native inclusion of the annular normal patch -/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

open PuncturedHandle

variable {N P : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem nonempty_surgeryAnnulus (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] :
    Nonempty (openSurgeryAnnulus N) := by
  let _ : Nontrivial N := Module.nontrivial_of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ N = n + 1)]
    omega)
  obtain ⟨v⟩ : Nonempty (UnitSphere N) :=
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
  refine ⟨⟨v.val, ?_⟩⟩
  change (1 / 2 : ℝ) < ‖v.val‖ ∧ ‖v.val‖ < (3 / 2 : ℝ)
  rw [mem_sphere_zero_iff_norm.mp v.property]
  norm_num

theorem nonempty_annularParameters (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)] :
    Nonempty (AnnularParameters N P) := by
  let _ : Nontrivial N := Module.nontrivial_of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ N = m + 1)]
    omega)
  let _ : Nonempty (UnitSphere N) :=
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
  let _ := nonempty_surgeryAnnulus (N := P) n
  infer_instance

def annularInclusionPartial (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)] :
    PartialDiffeomorph ((𝓡 m).prod 𝓘(ℝ, P)) ((𝓡 m).prod 𝓘(ℝ, P))
      (AnnularParameters N P) (UnitSphere N × P) ∞ := by
  let _ := nonempty_surgeryAnnulus (N := P) n
  exact PartialChart.prod (Diffeomorph.refl (𝓡 m) (UnitSphere N) ∞).toPartialDiffeomorph
    (PartialChart.openInclusion (openSurgeryAnnulus P))

theorem annularInclusionPartial_source (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)] :
    (annularInclusionPartial (N := N) (P := P) m n).source = univ := by
  apply eq_univ_of_forall
  intro z
  exact ⟨mem_univ z.1, mem_univ z.2⟩

theorem annularInclusionPartial_point (m n : ℕ)
    [Fact (Module.finrank ℝ N = m + 1)] [Fact (Module.finrank ℝ P = n + 1)]
    (z : AnnularParameters N P) : annularInclusionPartial m n z = (z.1, z.2.val) := rfl

end Wikipedia.SmoothSixDPoincare.MorseHandle
