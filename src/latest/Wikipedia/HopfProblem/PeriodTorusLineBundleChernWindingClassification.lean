import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWinding
import Mathlib.Analysis.Convex.Contractible

/-!
# Winding classifies actual based homotopies

Two punctured-plane loops with the same winding have logarithmic lifts
with the same endpoints. The simply connected covering plane supplies
a relative-endpoint homotopy, whose exponential is a homotopy of the
original loops. In particular zero winding is exactly null-homotopy.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open Topology unitInterval

/-- Equal winding gives an actual endpoint-preserving homotopy of based loops. -/
theorem homotopic_of_windingNumber_eq {γ δ : BasedLoop}
    (h : windingNumber γ = windingNumber δ) : γ.Homotopic δ := by
  have he : normalizedLoopLog γ 1 = normalizedLoopLog δ 1 := by
    rw [normalizedLoopLog_endpoint, normalizedLoopLog_endpoint, h]
  let Γ : Path (0 : ℂ) (normalizedLoopLog γ 1) :=
    ⟨normalizedLoopLog γ, normalizedLoopLog_zero γ, rfl⟩
  let Δ : Path (0 : ℂ) (normalizedLoopLog γ 1) :=
    ⟨normalizedLoopLog δ, normalizedLoopLog_zero δ, he.symm⟩
  have hl : Γ.Homotopic Δ := SimplyConnectedSpace.paths_homotopic Γ Δ
  let expMap : C(ℂ, PuncturedPlane) :=
    ⟨fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩,
      Complex.isCoveringMap_exp.continuous⟩
  have hmap : (expMap.comp (normalizedLoopLog γ)).HomotopicRel
      (expMap.comp (normalizedLoopLog δ)) {0, 1} :=
    Nonempty.map (fun H => H.compContinuousMap expMap) hl
  have hg : expMap.comp (normalizedLoopLog γ) = γ.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact Subtype.ext (normalizedLoopLog_exp γ t)
  have hd : expMap.comp (normalizedLoopLog δ) = δ.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact Subtype.ext (normalizedLoopLog_exp δ t)
  rw [hg, hd] at hmap
  exact hmap

/-- Actual based homotopy is equivalent to equality of the covering-space winding. -/
theorem homotopic_iff_windingNumber_eq (γ δ : BasedLoop) :
    γ.Homotopic δ ↔ windingNumber γ = windingNumber δ :=
  ⟨windingNumber_homotopic, homotopic_of_windingNumber_eq⟩

/-- Every based loop is homotopic to the counterclockwise exponential loop of its winding. -/
theorem homotopic_exponentialLoop (γ : BasedLoop) :
    γ.Homotopic (exponentialLoop (windingNumber γ)) :=
  homotopic_of_windingNumber_eq (windingNumber_exponentialLoop _).symm

/-- Vanishing winding is exactly the vanishing of the actual based loop obstruction. -/
theorem windingNumber_eq_zero_iff_nullhomotopic (γ : BasedLoop) :
    windingNumber γ = 0 ↔ γ.Homotopic (Path.refl puncturedOne) := by
  rw [homotopic_iff_windingNumber_eq, windingNumber_refl]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
