/-
Vendored from danlyng/Econlib (Apache-2.0), retrieved 2026-08-16.
Upstream path: Econlib source: ConvexHomeomorph.lean
-/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Homeomorphisms between convex compact sets, unit balls, and unit cubes

This module establishes that in finite-dimensional real normed spaces, convex compact sets with
nonempty interior are homeomorphic to the closed unit ball, and more generally that any nonempty
convex compact set is homeomorphic to a unit cube `Set.Icc 0 1` in `Fin k → ℝ` for some `k`
(namely, the dimension of its affine span).

These homeomorphisms let fixed-point theorems proved for the unit cube or ball transfer to
arbitrary convex compact domains.

## Main statements

* `homeoUnitBall` — a convex compact set with nonempty interior in a finite-dimensional real normed
  space is homeomorphic to the closed unit ball.
* `homeoOfFinrankEq` — closed unit balls in finite-dimensional real normed spaces of equal
  dimension are homeomorphic.
* `unitCubeHomeoUnitBall` — the unit cube `Set.Icc 0 1` in `Fin n → ℝ` is homeomorphic to the
  closed unit ball in `Fin n → ℝ`.
* `homeoUnitCubeOfConvexCompact` — any nonempty convex compact set in a finite-dimensional real
  normed space is homeomorphic to a unit cube of some dimension.

## Tags

homeomorphism, convex, compact, unit ball, unit cube, finite-dimensional
-/

@[expose] public section

/-- A convex compact set with nonempty interior in a finite-dimensional real normed space is
homeomorphic to the closed unit ball. -/
lemma homeoUnitBall {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty) :
    Nonempty (s ≃ₜ Metric.closedBall (0 : V) 1) := by
  obtain ⟨e, -, he, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni hcmpct.isBounded
  rw [closure_eq_iff_isClosed.mpr hcmpct.isClosed] at he
  exact ⟨he ▸ e.image s⟩

/-- Closed unit balls in finite-dimensional real normed spaces of equal dimension are
homeomorphic. -/
theorem homeoOfFinrankEq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0 : V) 1 ≃ₜ Metric.closedBall (0 : W) 1) := by
  let L := ContinuousLinearEquiv.ofFinrankEq hreq
  let S := L.toHomeomorph ⁻¹' (Metric.closedBall (0 : W) 1)
  have hconv : Convex ℝ S := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have hcpt : IsCompact S := L.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall 0 1)
  have hint : (interior S).Nonempty := by
    rw [← Homeomorph.preimage_interior]
    exact (L.toHomeomorph.surjective.nonempty_preimage).mpr
      ⟨0, by rw [interior_closedBall (0 : W) (one_ne_zero)]; exact Metric.mem_ball_self one_pos⟩
  obtain ⟨e⟩ := homeoUnitBall S hconv hcpt hint
  exact ⟨e.symm.trans (L.toHomeomorph.sets rfl)⟩

/-- The unit cube `Set.Icc 0 1` in `Fin n → ℝ` is homeomorphic to the closed unit ball. -/
lemma unitCubeHomeoUnitBall {n : ℕ} :
    Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1) := by
  apply homeoUnitBall _ (convex_Icc 0 1) isCompact_Icc
  rw [show Set.Icc (0 : Fin n → ℝ) 1 = Set.pi Set.univ (fun _ => Set.Icc 0 1) from ?_]
  · rw [interior_pi_set (Set.toFinite _)]
    simp only [interior_Icc]
    exact ⟨fun _ => 1/2, Set.mem_pi.mpr (fun _ _ => by constructor <;> norm_num)⟩
  · ext x; simp [Set.mem_Icc, Pi.le_def]

/-- Any nonempty convex compact set in a finite-dimensional real normed space is homeomorphic to
the unit cube `Set.Icc 0 1` in `Fin k → ℝ` for some `k`. -/
lemma homeoUnitCubeOfConvexCompact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by
  haveI := hne.coe_sort
  obtain ⟨p, hp⟩ := hne
  let W := affineSpan ℝ s
  let q : W := ⟨p, mem_affineSpan ℝ hp⟩
  let g := (AffineIsometryEquiv.constVSub ℝ q).symm
  let f : W.direction → V := Subtype.val ∘ g
  let s' := f ⁻¹' s
  have hcvx' : Convex ℝ s' :=
    hcvx.affine_preimage (W.subtype.comp g.toAffineMap)
  have hint' : (interior s').Nonempty := by
    erw [Convex.interior_nonempty_iff_affineSpan_eq_top hcvx']
    dsimp only [s', f]
    erw [Set.preimage_comp, ← AffineSubspace.comap_span, affineSpan_coe_preimage_eq_top]
    rfl
  have hemb : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp g.toHomeomorph.isEmbedding
  have hmaps : Set.MapsTo f s' s := fun _ h ↦ h
  have hsurj : Function.Surjective (hmaps.restrict f s' s) := by
    rw [Set.MapsTo.restrict_surjective_iff]
    dsimp only [s', f]
    rw [Set.preimage_comp]
    exact Set.SurjOn.comp_right (AffineIsometryEquiv.surjective g) fun v hv ↦
      ⟨⟨v, mem_affineSpan ℝ hv⟩, hv, rfl⟩
  let e := (hemb.restrict hmaps).toHomeomorphOfSurjective hsurj
  have hcmpct' : IsCompact s' := by
    rw [isCompact_iff_compactSpace] at hcmpct ⊢
    exact e.symm.compactSpace
  obtain ⟨e₂⟩ := homeoUnitBall s' hcvx' hcmpct' hint'
  let k := Module.finrank ℝ W.direction
  obtain ⟨e₃⟩ := @unitCubeHomeoUnitBall k
  obtain ⟨e₄⟩ := homeoOfFinrankEq (Module.finrank_fin_fun ℝ (n := k)).symm
  exact ⟨k, ⟨(e.symm.trans e₂).trans (e₄.trans e₃.symm)⟩⟩

