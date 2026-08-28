import Wikipedia.NoExoticSixSphere.OrthogonalCutoffDescent
import Wikipedia.NoExoticSixSphere.EnergyDeformationIteration
import Wikipedia.NoExoticSixSphere.OrthogonalNoncriticalMargin
import Mathlib.Topology.Homotopy.Equiv

/-!
# Deforming a polygon sublevel across a noncritical band

Compactness, the explicit velocity-jump descent and finite iteration give a
native relative homotopy from the identity on an upper energy sublevel to a
map into a lower sublevel. All slices are energy nonincreasing, and polygons
below the cutoff threshold remain fixed.
-/

open Set unitInterval
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem exists_band_deformation (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (l k E : ℝ) (hlk : l < k) (hcompact : IsCompact (energySublevel a b τ E))
    (hn : ∀ v ∈ energyBand a b τ l E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    ∃ F : C(energySublevel a b τ E, energySublevel a b τ E),
      ∃ H : ContinuousMap.HomotopyRel (ContinuousMap.id _) F
        {v : energySublevel a b τ E | energy a b τ v.1 ≤ l},
      (∀ s v, energy a b τ (H (s, v)).1 ≤ energy a b τ v.1) ∧
        ∀ v, energy a b τ (F v).1 ≤ k := by
  obtain ⟨δ, hδ, H, hzero, hfixed, hle, hdrop⟩ :=
    exists_cutoff_descent a b τ l k E hlk hcompact hn
  exact EnergyDeformationIteration.exists_lowering_homotopy H
    (fun v ↦ energy a b τ v.1) {v | energy a b τ v.1 ≤ l} k E δ hδ
    (fun v ↦ v.2.2) hzero hfixed hle hdrop

/-- Sublevels separated by a compact noncritical energy band are homotopy
equivalent. The inverse map is the actual sublevel inclusion. -/
theorem nonempty_sublevel_homotopyEquiv (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (k E : ℝ) (hkE : k ≤ E)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hn : ∀ v ∈ energyBand a b τ k E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    Nonempty (ContinuousMap.HomotopyEquiv (energySublevel a b τ E)
      (energySublevel a b τ k)) := by
  obtain ⟨l, hlk, hn'⟩ := exists_noncritical_margin a b τ k E hcompact hn
  obtain ⟨F, H, hle, hlow⟩ := exists_band_deformation a b τ l k E hlk hcompact hn'
  let inc : C(energySublevel a b τ k, energySublevel a b τ E) :=
    ⟨fun v ↦ ⟨v.1, v.2.1, v.2.2.trans hkE⟩, continuous_subtype_val.subtype_mk _⟩
  let down : C(energySublevel a b τ E, energySublevel a b τ k) :=
    ⟨fun v ↦ ⟨(F v).1, (F v).2.1, hlow v⟩,
      (continuous_subtype_val.comp F.continuous).subtype_mk _⟩
  have hleft : (inc.comp down).Homotopic (ContinuousMap.id _) := by
    have heq : inc.comp down = F := by
      ext v
      rfl
    rw [heq]
    exact ⟨H.toHomotopy.symm⟩
  let K : ContinuousMap.Homotopy (ContinuousMap.id (energySublevel a b τ k))
      (down.comp inc) := {
    toFun := fun p ↦ ⟨(H (p.1, inc p.2)).1, (H (p.1, inc p.2)).2.1,
      (hle p.1 (inc p.2)).trans p.2.2.2⟩
    continuous_toFun := (continuous_subtype_val.comp
      (H.continuous.comp (continuous_fst.prodMk (inc.continuous.comp continuous_snd)))).subtype_mk _
    map_zero_left := by
      intro v
      apply Subtype.ext
      exact congrArg (fun w : energySublevel a b τ E ↦ w.1) (H.apply_zero (inc v))
    map_one_left := by
      intro v
      apply Subtype.ext
      exact congrArg (fun w : energySublevel a b τ E ↦ w.1) (H.apply_one (inc v)) }
  exact ⟨⟨down, inc, hleft, ⟨K.symm⟩⟩⟩

end NoExoticSixSphere.OrthogonalPolygon
