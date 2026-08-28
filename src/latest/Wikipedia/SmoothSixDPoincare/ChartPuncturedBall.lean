import Wikipedia.SmoothSixDPoincare.PuncturedBallHomotopy
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The punctured local chart neighborhood and its actual inner sphere

Restrict the original open partial homeomorphism to a ball wholly inside
its source. Removing the actual chart center gives a homeomorphism from
the literal punctured ball; radial contraction identifies any smaller
positive-radius sphere with this original punctured neighborhood.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ChartPuncturedBall

variable {E M : Type*} [NormedAddCommGroup E]
  [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)

def openSet : Set M := c '' ball (0 : E) R

def puncturedSet : Set M := {c 0}ᶜ ∩ openSet c R

variable (hR : 0 < R) (hs : closedBall (0 : E) R ⊆ c.source)

include hR hs in
theorem zero_mem_source : (0 : E) ∈ c.source := hs (by simpa using hR.le)

include hs in
theorem ball_subset_source : ball (0 : E) R ⊆ c.source := ball_subset_closedBall.trans hs

include hs in
theorem isOpen_openSet : IsOpen (openSet c R) :=
  c.isOpen_image_of_subset_source isOpen_ball (ball_subset_source c R hs)

include hR in
theorem center_mem_openSet : c 0 ∈ openSet c R :=
  mem_image_of_mem c (by simpa using hR)

def ballHomeomorph : ball (0 : E) R ≃ₜ openSet c R :=
  c.homeomorphOfImageSubsetSource (ball_subset_source c R hs) rfl

include hR hs in
theorem image_puncturedBall :
    c '' {x : E | x ≠ 0 ∧ ‖x‖ < R} = puncturedSet c R := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hxR⟩, rfl⟩
    have hx : x ∈ ball (0 : E) R := mem_ball_zero_iff.mpr hxR
    refine ⟨?_, ⟨x, hx, rfl⟩⟩
    change c x ≠ c 0
    exact fun h => hx0 (c.injOn (ball_subset_source c R hs hx) (zero_mem_source c R hR hs) h)
  · rintro ⟨hy0, x, hxR, rfl⟩
    refine ⟨x, ⟨?_, mem_ball_zero_iff.mp hxR⟩, rfl⟩
    intro hx0
    subst x
    exact hy0 rfl

def puncturedHomeomorph : PuncturedBall.Space E R ≃ₜ puncturedSet c R :=
  c.homeomorphOfImageSubsetSource
    (fun _ hx => ball_subset_source c R hs (mem_ball_zero_iff.mpr hx.2))
    (image_puncturedBall c R hR hs)

theorem puncturedHomeomorph_apply (x : PuncturedBall.Space E R) :
    (puncturedHomeomorph c R hR hs x).val = c x.val := rfl

variable [NormedSpace ℝ E]

def sphereHomotopyEquiv (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    sphere (0 : E) 1 ≃ₕ puncturedSet c R :=
  (PuncturedBall.sphereHomotopyEquiv R r hr hrR).trans
    (puncturedHomeomorph c R hR hs).toHomotopyEquiv

/-- The overlap equivalence retains the original chart evaluated at the actual inner radius. -/
theorem sphereHomotopyEquiv_apply (r : ℝ) (hr : 0 < r) (hrR : r < R)
    (u : sphere (0 : E) 1) :
    (sphereHomotopyEquiv c R hR hs r hr hrR u).val = c (r • (u : E)) := rfl

end Wikipedia.SmoothSixDPoincare.ChartPuncturedBall
