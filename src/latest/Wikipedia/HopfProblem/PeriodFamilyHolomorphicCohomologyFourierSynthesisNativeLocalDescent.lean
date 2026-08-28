import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothDescent

/-!
# Smooth descent on an original open subset

Only the pullback over the given open set is required to be smooth.
The actual local inverse of the original covering gives smoothness at
each point of that open set. No regularity across its boundary is used.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local

variable {E F G H K L M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace L]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  [TopologicalSpace P] [ChartedSpace L P]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {Q : ModelWithCorners ℝ G L} {n : ℕ∞ω}

/-- Descent on the original open through actual covering local inverses.
The pullback need not be smooth outside the full inverse image of that open. -/
theorem contMDiffOn_of_comp_real_localDiffeomorph {q : M → N} {f : N → P}
    (hq : IsLocalDiffeomorph I J ω q) (hs : Function.Surjective q)
    {s : Set N} (hsopen : IsOpen s)
    (hf : ContMDiffOn I Q n (f ∘ q) (q ⁻¹' s)) : ContMDiffOn J Q n f s := by
  intro y hy
  apply ContMDiffAt.contMDiffWithinAt
  obtain ⟨x, rfl⟩ := hs y
  have hfx : ContMDiffAt I Q n (f ∘ q) x :=
    hf.contMDiffAt ((hsopen.preimage hq.contMDiff.continuous).mem_nhds hy)
  have hi : ContMDiffAt J I n (hq x).localInverse (q x) :=
    (hq x).localInverse_contMDiffAt.of_le le_top
  have hinv : (hq x).localInverse (q x) = x :=
    (hq x).localInverse_left_inv (hq x).localInverse_mem_target
  have hfx' : ContMDiffAt I Q n (f ∘ q) ((hq x).localInverse (q x)) := by
    simpa only [hinv] using hfx
  have h := hfx'.comp (q x) hi
  apply h.congr_of_eventuallyEq
  filter_upwards [(hq x).localInverse_eventuallyEq_right] with z hz
  change f z = f (q ((hq x).localInverse z))
  rw [show q ((hq x).localInverse z) = z from hz]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local
