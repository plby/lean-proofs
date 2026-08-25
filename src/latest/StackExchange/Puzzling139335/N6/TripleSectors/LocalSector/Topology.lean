import StackExchange.Puzzling139335.SegmentCrossing.Collar

/-!
# A filled local sector from its actual frontier

The two linear coordinates are independent.  Their positive quadrant is the
sector between the actual boundary branches.  A common negative ray outside
the region selects this sector as the interior side.
-/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.LocalSector

/-- A connected set avoiding a frontier lies on one side; an actual exterior
point selects the exterior side. -/
theorem subset_interior_compl_of_preconnected
    {P U : Set Plane} (hU : IsPreconnected U)
    (hoff : U ⊆ (frontier P)ᶜ) (hw : ∃ w ∈ U, w ∉ P) :
    U ⊆ interior Pᶜ := by
  have hcover : U ⊆ interior P ∪ interior Pᶜ := by
    simpa only [compl_frontier_eq_union_interior] using hoff
  have hdis : Disjoint (interior P) (interior Pᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    exact interior_subset hxc (interior_subset hx)
  obtain hin | hout := IsPreconnected.subset_or_subset isOpen_interior isOpen_interior
    hdis hcover hU
  · obtain ⟨w, hwU, hwP⟩ := hw
    exact False.elim (hwP (interior_subset (hin hwU)))
  · exact hout

/-- Every ray meets every ball about its vertex at a positive parameter. -/
theorem exists_pos_smul_mem_ball (w : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t • w ∈ ball (0 : Plane) r := by
  let t : ℝ := r / (2 * (‖w‖ + 1))
  have hn : 0 < ‖w‖ + 1 := by positivity
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) hn)
  have hmul : t * (2 * (‖w‖ + 1)) = r := by
    exact div_mul_cancel₀ r (ne_of_gt (mul_pos (by norm_num) hn))
  refine ⟨t, ht, ?_⟩
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  nlinarith [norm_nonneg w]

/-- A nonconstant linear coordinate that is nonnegative throughout an open
set is strictly positive there. -/
theorem strict_linear_of_open_nonnegative
    (f : Plane →L[ℝ] ℝ) (hf : Function.Surjective f)
    {U : Set Plane} (hU : IsOpen U) (hsub : U ⊆ f ⁻¹' Ici (0 : ℝ)) :
    U ⊆ f ⁻¹' Ioi (0 : ℝ) := by
  intro x hx
  have hxi : x ∈ interior (f ⁻¹' Ici (0 : ℝ)) :=
    interior_mono hsub (hU.interior_eq.symm ▸ hx)
  rwa [f.interior_preimage hf, interior_Ici] at hxi

/-- If an actual frontier has nonnegative linear coordinates near the origin,
the negative half-ball is exterior, provided it contains an exterior ray. -/
theorem negative_half_ball_exterior
    {P : Set Plane} (f : Plane →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r)
    (hfront : ∀ x ∈ ball (0 : Plane) r, x ∈ frontier P → 0 ≤ f x)
    {w : Plane} (hfw : f w < 0) (hout : ∀ t : ℝ, 0 < t → t • w ∉ P) :
    ball (0 : Plane) r ∩ f ⁻¹' Iio (0 : ℝ) ⊆ interior Pᶜ := by
  apply subset_interior_compl_of_preconnected
  · exact ((convex_ball (0 : Plane) r).inter
      ((convex_Iio (0 : ℝ)).linear_preimage f.toLinearMap)).isPreconnected
  · intro x hx hxf
    exact (not_lt_of_ge (hfront x hx.1 hxf)) hx.2
  · obtain ⟨t, ht, htball⟩ := exists_pos_smul_mem_ball w hr
    refine ⟨t • w, ⟨htball, ?_⟩, hout t ht⟩
    change f (t • w) < 0
    simpa only [map_smul, smul_eq_mul] using mul_neg_of_pos_of_neg ht hfw

/-- A regular closed region whose local frontier consists of the two positive
coordinate axes has exactly the positive sector as its local interior.

Only the stated local frontier containment and a common exterior ray are used;
there is no polygon, tangent, angle, or local-sector assumption.
-/
theorem interior_eq_positive_sector_of_local_frontier
    {P : Set Plane} (f g : Plane →L[ℝ] ℝ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hzero : (0 : Plane) ∈ closure (interior P))
    {r : ℝ} (hr : 0 < r)
    (hfront : ∀ x ∈ ball (0 : Plane) r, x ∈ frontier P →
      0 ≤ f x ∧ 0 ≤ g x ∧ (f x = 0 ∨ g x = 0))
    {w : Plane} (hfw : f w < 0) (hgw : g w < 0)
    (hout : ∀ t : ℝ, 0 < t → t • w ∉ P) :
    ball (0 : Plane) r ∩ interior P =
      ball (0 : Plane) r ∩ {x | 0 < f x ∧ 0 < g x} := by
  have hnegf := negative_half_ball_exterior f hr
    (fun x hx hxf => (hfront x hx hxf).1) hfw hout
  have hnegg := negative_half_ball_exterior g hr
    (fun x hx hxf => (hfront x hx hxf).2.1) hgw hout
  have hnonnegf : ball (0 : Plane) r ∩ interior P ⊆ f ⁻¹' Ici (0 : ℝ) := by
    intro x hx
    by_contra h
    have hfx : f x < 0 := lt_of_not_ge h
    exact interior_subset (hnegf ⟨hx.1, hfx⟩) (interior_subset hx.2)
  have hnonnegg : ball (0 : Plane) r ∩ interior P ⊆ g ⁻¹' Ici (0 : ℝ) := by
    intro x hx
    by_contra h
    have hgx : g x < 0 := lt_of_not_ge h
    exact interior_subset (hnegg ⟨hx.1, hgx⟩) (interior_subset hx.2)
  have hfpos := strict_linear_of_open_nonnegative f hf
    (isOpen_ball.inter isOpen_interior) hnonnegf
  have hgpos := strict_linear_of_open_nonnegative g hg
    (isOpen_ball.inter isOpen_interior) hnonnegg
  let U : Set Plane := ball (0 : Plane) r ∩ {x | 0 < f x ∧ 0 < g x}
  have hforward : ball (0 : Plane) r ∩ interior P ⊆ U := by
    intro x hx
    exact ⟨hx.1, hfpos hx, hgpos hx⟩
  have hconv : Convex ℝ U := by
    exact (convex_ball (0 : Plane) r).inter
      (((convex_Ioi (0 : ℝ)).linear_preimage f.toLinearMap).inter
        ((convex_Ioi (0 : ℝ)).linear_preimage g.toLinearMap))
  have hoff : U ⊆ (frontier P)ᶜ := by
    intro x hx hxf
    rcases (hfront x hx.1 hxf).2.2 with hfx | hgx
    · exact (ne_of_gt hx.2.1) hfx
    · exact (ne_of_gt hx.2.2) hgx
  have hcover : U ⊆ interior P ∪ interior Pᶜ := by
    simpa only [compl_frontier_eq_union_interior] using hoff
  have hdis : Disjoint (interior P) (interior Pᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    exact interior_subset hxc (interior_subset hx)
  obtain hin | houtside := IsPreconnected.subset_or_subset isOpen_interior isOpen_interior
    hdis hcover hconv.isPreconnected
  · exact Subset.antisymm hforward (fun x hx => ⟨hx.1, hin hx⟩)
  · obtain ⟨z, hzball, hzP⟩ :=
      mem_closure_iff.mp hzero (ball (0 : Plane) r) isOpen_ball (mem_ball_self hr)
    exact False.elim (interior_subset (houtside (hforward ⟨hzball, hzP⟩))
      (interior_subset hzP))

end Puzzling139335.N6.TripleSectors.LocalSector
