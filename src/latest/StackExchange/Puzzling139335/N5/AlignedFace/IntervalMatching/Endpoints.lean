import StackExchange.Puzzling139335.Definitions
import Mathlib.Tactic

/-!
# Matching the endpoints of two top-side intervals

Exact descriptions of the top contacts, together with coordinate relations
between the two maps, transport all four interval endpoints.  The resulting
upper and lower bounds determine the translation or reflection parameter.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

/-- A coordinate relation transports a complete top-contact interval into
the other image's exact top-contact interval. -/
theorem top_interval_mapsTo_of_coordinates {X : Type*} {P : Set X}
    {F G : X → Plane} {l u l' u' : ℝ} {f : ℝ → ℝ}
    (hF : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ F '' P ↔ l ≤ x ∧ x ≤ u)
    (hG : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ G '' P ↔ l' ≤ x ∧ x ≤ u')
    (hx : ∀ p, G p 0 = f (F p 0)) (hy : ∀ p, G p 1 = F p 1) :
    MapsTo f (Icc l u) (Icc l' u') := by
  intro x hxI
  obtain ⟨p, hp, hpF⟩ := (hF x).mpr hxI
  have hp0 : F p 0 = x := congrArg (fun q : Plane => q 0) hpF
  have hp1 : F p 1 = 1 := congrArg (fun q : Plane => q 1) hpF
  apply (hG (f x)).mp
  refine ⟨p, hp, ?_⟩
  ext i
  fin_cases i
  · exact (hx p).trans (congrArg f hp0)
  · exact (hy p).trans hp1

/-- A common horizontal translation matching `[m,1]` to `[b,m]` has the
forced displacement `m-1=b-m`, and the intervals have equal length. -/
theorem translation_interval_matching {X : Type*} {P : Set X}
    {R D : X → Plane} {b m δ : ℝ}
    (hbm : b < m) (hm1 : m < 1)
    (hR : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ R '' P ↔ m ≤ x ∧ x ≤ 1)
    (hD : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ D '' P ↔ b ≤ x ∧ x ≤ m)
    (hx : ∀ p, D p 0 = R p 0 + δ) (hy : ∀ p, D p 1 = R p 1) :
    δ = m - 1 ∧ δ = b - m ∧ 2 * m = 1 + b := by
  have hforward := top_interval_mapsTo_of_coordinates (f := fun x => x + δ) hR hD hx hy
  have hbackX : ∀ p, R p 0 = D p 0 - δ := by
    intro p
    rw [hx p]
    ring
  have hbackY : ∀ p, R p 1 = D p 1 := fun p => (hy p).symm
  have hback := top_interval_mapsTo_of_coordinates (f := fun x => x - δ)
    hD hR hbackX hbackY
  have hRm := hforward (show m ∈ Icc m 1 from ⟨le_rfl, hm1.le⟩)
  have hR1 := hforward (show (1 : ℝ) ∈ Icc m 1 from ⟨hm1.le, le_rfl⟩)
  have hDb := hback (show b ∈ Icc b m from ⟨le_rfl, hbm.le⟩)
  have hDm := hback (show m ∈ Icc b m from ⟨hbm.le, le_rfl⟩)
  have hδm : δ = m - 1 := by linarith only [hR1.2, hDm.2]
  have hδb : δ = b - m := by linarith only [hRm.1, hDb.1]
  exact ⟨hδm, hδb, by linarith only [hδm, hδb]⟩

/-- A vertical reflection matching `[m,1]` to `[b,m]` has the forced
coordinate sum `κ=2m=1+b`. -/
theorem reflection_interval_matching {X : Type*} {P : Set X}
    {R D : X → Plane} {b m κ : ℝ}
    (hbm : b < m) (hm1 : m < 1)
    (hR : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ R '' P ↔ m ≤ x ∧ x ≤ 1)
    (hD : ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ D '' P ↔ b ≤ x ∧ x ≤ m)
    (hx : ∀ p, D p 0 = κ - R p 0) (hy : ∀ p, D p 1 = R p 1) :
    κ = 2 * m ∧ κ = 1 + b ∧ 2 * m = 1 + b := by
  have hforward := top_interval_mapsTo_of_coordinates (f := fun x => κ - x) hR hD hx hy
  have hbackX : ∀ p, R p 0 = κ - D p 0 := by
    intro p
    rw [hx p]
    ring
  have hbackY : ∀ p, R p 1 = D p 1 := fun p => (hy p).symm
  have hback := top_interval_mapsTo_of_coordinates (f := fun x => κ - x)
    hD hR hbackX hbackY
  have hRm := hforward (show m ∈ Icc m 1 from ⟨le_rfl, hm1.le⟩)
  have hR1 := hforward (show (1 : ℝ) ∈ Icc m 1 from ⟨hm1.le, le_rfl⟩)
  have hDb := hback (show b ∈ Icc b m from ⟨le_rfl, hbm.le⟩)
  have hDm := hback (show m ∈ Icc b m from ⟨hbm.le, le_rfl⟩)
  have hκm : κ = 2 * m := by linarith only [hRm.2, hDm.1]
  have hκb : κ = 1 + b := by linarith only [hR1.1, hDb.2]
  exact ⟨hκm, hκb, hκm.symm.trans hκb⟩

end Puzzling139335.N5.AlignedFace
