import Wikipedia.HopfProblem.DegreeCollapsePassageSharedFrames

/-!
# Actual supported passages with a common crossing time

The whole ambient isotopy, its one compact support, and the exact unique
sheet crossing are retained after the constructed increasing clock change.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

variable (E) in
structure CenteredSheetPassage (f : X → M) (g : Y → M) (x : X) (y : Y) (O : Set M) where
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  avoids : support ⊆ Oᶜ
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ family
  zero : ∀ z, family (0, z) = z
  slices : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = family (t, z)
  fixedOutside : ∀ t z, z ∉ support → family (t, z) = z
  crossing : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y,
    family (t, f u) = g v ↔ t = 1 / 2 ∧ u = x ∧ v = y

theorem CenteredSheetPassage.fixed_on_protected
    {f : X → M} {g : Y → M} {x : X} {y : Y} {O : Set M}
    (A : CenteredSheetPassage E f g x y O) (t : ℝ) (z : M) (hz : z ∈ O) :
    A.family (t, z) = z :=
  A.fixedOutside t z (fun h => A.avoids h hz)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def LongitudinalTubeMotion.centeredSheetPassage
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞}
    (A : LongitudinalTubeMotion Φ)
    (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hD0 : D 0 = 0) (hpoint : D (1 / 2) = A.time)
    (hinterval : MapsTo D (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    {f : X → M} {g : Y → M} {x : X} {y : Y} {O : Set M}
    (havoid : Φ.target ⊆ Oᶜ)
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y,
      A.family (t, f u) = g v ↔ t = A.time ∧ u = x ∧ v = y) :
    CenteredSheetPassage E f g x y O where
  family := fun p => A.family (D p.1, p.2)
  support := A.support
  compact_support := A.compact_support
  avoids := A.support_subset.trans havoid
  smooth := A.smooth.comp ((D.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  zero := by intro z; change A.family (D 0, z) = z; rw [hD0, A.zero]
  slices := fun t => A.slices (D t)
  fixedOutside := fun t z hz => A.fixedOutside (D t) z hz
  crossing := by
    intro t ht u v
    rw [hcross (D t) (hinterval ht) u v]
    constructor
    · rintro ⟨h, hu, hv⟩
      exact ⟨D.injective (h.trans hpoint.symm), hu, hv⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨hpoint, rfl, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
