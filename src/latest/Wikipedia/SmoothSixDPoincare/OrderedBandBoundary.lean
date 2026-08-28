import Wikipedia.SmoothSixDPoincare.OrderedBandSmooth

/-!
# Exact boundary preservation by the retained regular-band map

Both directions use the recorded ambient map, rather than another choice of
homeomorphism between the same sublevels.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
  {S : SurgeryWindows E f} {i j : Fin S.count} (B : S.BandData i j)

theorem sublevelHomeomorph_level_iff (x : {x : M // f x ≤ S.upper (S.point i)}) :
    f (B.sublevelHomeomorph x).val = S.lower (S.point j) ↔
      f x.val = S.upper (S.point i) := by
  constructor
  · intro hx
    have hmem : B.ambient x.val ∈
        B.ambient '' {y : M | f y = S.upper (S.point i)} := by
      rw [B.level_image]
      exact hx
    obtain ⟨y, hy, heq⟩ := hmem
    exact B.ambient.injective heq ▸ hy
  · intro hx
    exact (congrArg f (B.level_coe ⟨x.val, hx⟩)).symm.trans
      (B.level ⟨x.val, hx⟩).property

theorem sublevelHomeomorph_symm_level_iff (x : {x : M // f x ≤ S.lower (S.point j)}) :
    f (B.sublevelHomeomorph.symm x).val = S.upper (S.point i) ↔
      f x.val = S.lower (S.point j) := by
  have h := B.sublevelHomeomorph_level_iff (B.sublevelHomeomorph.symm x)
  rw [B.sublevelHomeomorph.apply_symm_apply] at h
  exact h.symm

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData
