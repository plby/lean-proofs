import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Fibrewise linearity of native trivialization gluing

The standard topological gluing operations preserve complex-linear fibre
coordinates. In particular, the seam correction in `Trivialization.piecewiseLe`
is the native continuous linear coordinate change, so no membership of the
resulting chart in a chosen trivialization atlas is needed.
-/

noncomputable section

open Bundle Set

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological

variable {M F : Type*} [TopologicalSpace M] [TopologicalSpace F]
    [AddCommMonoid F] [Module ℂ F]
    {E : M → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (TotalSpace F E)]

/-- Restricting the open base set does not change the fibre coordinates. -/
instance linear_restrOpen (e : Trivialization F (π F E)) [e.IsLinear ℂ]
    (s : Set M) (hs : IsOpen s) : (e.restrOpen s hs).IsLinear ℂ where
  linear b hb := by
    change IsLinearMap ℂ (fun v : E b => (e ⟨b, v⟩).2)
    exact e.linear ℂ hb.1

/-- A piecewise chart chooses the same branch for every vector in one fibre. -/
instance linear_piecewise (e e' : Trivialization F (π F E))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] (s : Set M)
    (Hs : e.baseSet ∩ frontier s = e'.baseSet ∩ frontier s)
    (Heq : EqOn e e' ((π F E) ⁻¹' (e.baseSet ∩ frontier s))) :
    (e.piecewise e' s Hs Heq).IsLinear ℂ where
  linear b hb := by
    classical
    change IsLinearMap ℂ
      (fun v : E b => (((π F E) ⁻¹' s).piecewise e e' ⟨b, v⟩).2)
    change b ∈ s.ite e.baseSet e'.baseSet at hb
    by_cases hbs : b ∈ s
    · have hbe : b ∈ e.baseSet := by simpa [Set.ite, hbs] using hb
      simpa only [Set.piecewise, Set.mem_preimage, if_pos hbs]
        using e.linear ℂ hbe
    · have hbe : b ∈ e'.baseSet := by simpa [Set.ite, hbs] using hb
      simpa only [Set.piecewise, Set.mem_preimage, if_neg hbs]
        using e'.linear ℂ hbe

/-- Disjoint gluing also selects a branch independently of the fibre vector. -/
instance linear_disjointUnion (e e' : Trivialization F (π F E))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] (H : Disjoint e.baseSet e'.baseSet) :
    (e.disjointUnion e' H).IsLinear ℂ where
  linear b hb := by
    classical
    change IsLinearMap ℂ (fun v : E b => (e.source.piecewise e e' ⟨b, v⟩).2)
    change b ∈ e.baseSet ∪ e'.baseSet at hb
    by_cases hbe : b ∈ e.baseSet
    · simpa only [Set.piecewise, e.source_eq, Set.mem_preimage,
        if_pos hbe] using e.linear ℂ hbe
    · have hbe' : b ∈ e'.baseSet := hb.resolve_left hbe
      simpa only [Set.piecewise, e.source_eq, Set.mem_preimage,
        if_neg hbe] using e'.linear ℂ hbe'

/-- Postcomposition by a fibre-linear homeomorphism preserves linearity. -/
theorem linear_transFiberHomeomorph (e : Trivialization F (π F E)) [e.IsLinear ℂ]
    (h : F ≃ₜ F) (hlin : IsLinearMap ℂ h) :
    (e.transFiberHomeomorph h).IsLinear ℂ where
  linear b hb := by
    refine ⟨?_, ?_⟩
    · intro v w
      change h (e ⟨b, v + w⟩).2 = h (e ⟨b, v⟩).2 + h (e ⟨b, w⟩).2
      rw [(e.linear ℂ hb).map_add, hlin.map_add]
    · intro c v
      change h (e ⟨b, c • v⟩).2 = c • h (e ⟨b, v⟩).2
      rw [(e.linear ℂ hb).map_smul, hlin.map_smul]

/-- The topological coordinate change is the underlying map of `coordChangeL`. -/
theorem linear_coordChangeHomeomorph (e e' : Trivialization F (π F E))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] {b : M}
    (he : b ∈ e.baseSet) (he' : b ∈ e'.baseSet) :
    IsLinearMap ℂ (e.coordChangeHomeomorph e' he he') := by
  have hcoe : (e.coordChangeHomeomorph e' he he' : F → F) =
      e.coordChangeL ℂ e' b := by
    funext v
    exact (e.coordChangeL_apply' e' ⟨he, he'⟩ v).symm
  rw [hcoe]
  exact (e.coordChangeL ℂ e' b).toLinearEquiv.toLinearMap.isLinear

/-- Gluing equal linear charts at an ordered seam preserves linearity. -/
instance linear_piecewiseLeOfEq [LinearOrder M] [OrderTopology M]
    (e e' : Trivialization F (π F E)) [e.IsLinear ℂ] [e'.IsLinear ℂ]
    (a : M) (he : a ∈ e.baseSet) (he' : a ∈ e'.baseSet)
    (heq : ∀ p, (π F E) p = a → e p = e' p) :
    (e.piecewiseLeOfEq e' a he he' heq).IsLinear ℂ := by
  unfold Trivialization.piecewiseLeOfEq
  exact linear_piecewise e e' (Iic a) _ _

/-- The native seam-corrected ordered gluing is fibrewise complex-linear. -/
instance linear_piecewiseLe [LinearOrder M] [OrderTopology M]
    (e e' : Trivialization F (π F E)) [e.IsLinear ℂ] [e'.IsLinear ℂ]
    (a : M) (he : a ∈ e.baseSet) (he' : a ∈ e'.baseSet) :
    (e.piecewiseLe e' a he he').IsLinear ℂ := by
  have : (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e he' he)).IsLinear ℂ :=
    linear_transFiberHomeomorph e' _ (linear_coordChangeHomeomorph e' e he' he)
  unfold Trivialization.piecewiseLe
  exact linear_piecewiseLeOfEq e
    (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e he' he)) a he he' _

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological
