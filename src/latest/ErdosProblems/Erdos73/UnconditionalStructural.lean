import ErdosProblems.Erdos73.ProjectiveAntipodalObstruction
import ErdosProblems.Erdos73.ControlledPortDefect

/-! The unconditional high-order hereditary-defect structural theorem. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem reedDefectHighOrderBramble : ReedDefectHighOrderBrambleStatement := by
  intro r p C
  letI : LinearOrder (Fin (2 * (r + 1)) × Fin (2 * (r + 1))) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨N, hN, word, hsurj, hNC, hF⟩ := exists_high_defect_antipodal_word r
  let ell := oddCrossingWallHavenBound (portDefectHandleCount N (p + 1)) (p + 1)
  refine ⟨ell, C + C + ell, le_refl _, ?_⟩
  intro V _ G hbramble horder
  by_cases hpack : HasOddCyclePacking (p + 1) G
  · exact Or.inl hpack
  obtain ⟨haven⟩ := exists_brambleHaven hbramble horder
  exact Or.inr (Or.inr (haven.defect_of_antipodal_port_word (p + 1) (le_refl _)
    hpack hN word hsurj hNC (r + 1) hF))

end
end Erdos73
