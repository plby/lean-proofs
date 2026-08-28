import Wikipedia.SmoothSixDPoincare.NativeSheetProjection
import Wikipedia.SmoothSixDPoincare.CompactLocalDiffeomorph

/-!
# Recover the actual source chart from a clean ambient sheet chart

The native projection is injective on the entire original sheet above the
ambient chart target. Its local inverses glue to one genuine partial
diffeomorphism. The inverse chart parametrizes exactly the zero normal section,
and its composition with the original sheet map is the original ambient chart.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeSheetCoordinates

variable {D B E G H M N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [Nonempty N]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) (F : N → M)

/-- A clean ambient chart canonically supplies a genuine chart on the original native sheet. -/
theorem exists_induced_sheet_chart (hF : ContMDiff I 𝓘(ℝ, E) ∞ F) (hinjF : Injective F)
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ range F ↔ z.2 = 0)
    (hdim : Module.finrank ℝ G = Module.finrank ℝ D)
    (hiF : ∀ x, Injective (mfderiv I 𝓘(ℝ, E) F x)) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, D) I D N ∞,
      c.source = {u | (u, (0 : B)) ∈ Φ.source} ∧
      c.target = F ⁻¹' Φ.target ∧
      (∀ u ∈ c.source, F (c u) = Φ (u, 0)) ∧
      ∀ x, c.symm x = projection Φ F x := by
  let U := F ⁻¹' Φ.target
  have hU : IsOpen U := Φ.open_target.preimage hF.continuous
  have hzero (x : N) (hx : x ∈ U) : (Φ.symm (F x)).2 = 0 :=
    (hclean _ (Φ.map_target' hx)).mp ⟨x, (Φ.right_inv' hx).symm⟩
  have hinj : InjOn (projection Φ F) U := by
    intro x hx y hy heq
    have hc : Φ.symm (F x) = Φ.symm (F y) :=
      Prod.ext heq ((hzero x hx).trans (hzero y hy).symm)
    apply hinjF
    exact (Φ.right_inv' hx).symm.trans ((congrArg Φ hc).trans (Φ.right_inv' hy))
  let p := partialDiffeomorphOfInjectiveLocal hU hinj
    (isLocalDiffeomorphOn_projection Φ F hF hclean hdim hiF)
  have htarget : p.target = {u | (u, (0 : B)) ∈ Φ.source} := by
    change projection Φ F '' U = _
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      have heq : (projection Φ F x, (0 : B)) = Φ.symm (F x) :=
        Prod.ext rfl (hzero x hx).symm
      change (projection Φ F x, (0 : B)) ∈ Φ.source
      rw [heq]
      exact Φ.map_target' hx
    · intro hu
      obtain ⟨x, hx⟩ := (hclean (u, 0) hu).mpr rfl
      have hxU : x ∈ U := by
        change F x ∈ Φ.target
        rw [hx]
        exact Φ.map_source' hu
      refine ⟨x, hxU, ?_⟩
      change (Φ.symm (F x)).1 = u
      rw [hx]
      exact congrArg Prod.fst (Φ.left_inv' hu)
  refine ⟨p.symm, htarget, rfl, ?_, fun _ => rfl⟩
  intro u hu
  have hx : p.symm u ∈ U := p.map_target' hu
  have hp : projection Φ F (p.symm u) = u := p.right_inv' hu
  have heq : Φ.symm (F (p.symm u)) = (u, (0 : B)) :=
    Prod.ext hp (hzero (p.symm u) hx)
  exact (Φ.right_inv' hx).symm.trans (congrArg Φ heq)

end Wikipedia.SmoothSixDPoincare.NativeSheetCoordinates
