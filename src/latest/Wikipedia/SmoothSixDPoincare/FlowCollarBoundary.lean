import Wikipedia.SmoothSixDPoincare.FlowCollarHomeomorph

/-!
# The actual flow-collar homeomorphism preserves the ambient frontiers

The remaining time equals the full collar length precisely on the outer
frontier. Rescaling carries this locus to the first-entry locus of the inner
region. Thus the existing explicit sublevel homeomorphism also gives the
boundary identification needed for the Morse surgery presentation.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {X : Type*} [TopologicalSpace X] {F : Flow ℝ X} {A B : Set X}
  (d : FlowCollarData F A B)

theorem duration_lt_time_iff_interior (x : B) :
    d.duration x < d.time ↔ (x : X) ∈ interior B := by
  constructor
  · intro hlt
    have hi := d.strict_outer (d.origin x).val (d.origin x).property
      (d.time - d.duration x) (sub_pos.mpr hlt)
    rwa [d.origin_reconstruct] at hi
  · intro hi
    have hcore : F d.time x.val ∈ interior d.core := by
      apply preimage_interior_subset_interior_preimage
        (F.continuous continuous_const continuous_id)
      change F (-d.time) (F d.time x.val) ∈ interior B
      simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hi
    exact entryTime_lt_of_flow_mem_interior F d.time_pos hcore

theorem duration_eq_time_iff_frontier (x : B) :
    d.duration x = d.time ↔ (x : X) ∈ frontier B := by
  rw [frontier, d.closed_outer.closure_eq]
  constructor
  · intro heq
    refine ⟨x.property, ?_⟩
    intro hi
    have hlt := (d.duration_lt_time_iff_interior x).mpr hi
    exact (ne_of_lt hlt) heq
  · intro hx
    apply le_antisymm (d.duration_le x)
    exact le_of_not_gt (fun hlt => hx.2 ((d.duration_lt_time_iff_interior x).mp hlt))

/-- Rescaling sends interior to interior, using the actual entry times and strict absorption. -/
theorem rescale_mem_interior_iff (x : B) :
    (d.rescale x).val ∈ interior A ↔ x.val ∈ interior B := by
  suffices h : (d.rescale x).val ∈ interior A ↔ d.duration x < d.time from
    h.trans (d.duration_lt_time_iff_interior x)
  constructor
  · intro hi
    by_contra hnot
    have heq : d.duration x = d.time := le_antisymm (d.duration_le x) (le_of_not_gt hnot)
    have horigin : (d.origin x).val = x.val := by
      change F (d.duration x - d.time) x.val = x.val
      rw [heq, sub_self, F.map_zero_apply]
    have hentry : F (d.delay x) (d.origin x).val ∈ interior A := by
      rw [d.rescale_from_origin, heq, d.time_mul_factor, sub_sub_cancel] at hi
      exact hi
    by_cases hpos : 0 < d.delay x
    · have hlt := entryTime_lt_of_flow_mem_interior F hpos hentry
      exact (lt_irrefl (d.delay x)) hlt
    · have hzero : d.delay x = 0 := le_antisymm (le_of_not_gt hpos) (d.delay_nonneg x)
      rw [hzero, F.map_zero_apply, horigin] at hentry
      have hB := interior_mono d.inner_subset hentry
      exact hnot ((d.duration_lt_time_iff_interior x).mpr hB)
  · intro hlt
    rw [d.rescale_from_origin]
    have hmul := mul_lt_mul_of_pos_right hlt (d.factor_pos x)
    rw [d.time_mul_factor] at hmul
    have hdelay : d.delay x < d.time - d.duration x * d.factor x := by linarith
    exact flow_mem_interior_of_entryTime_lt F d.closed_inner d.strict_inner
      (d.hits_inner (d.origin x).property) hdelay

/-- The homeomorphism's actual map carries exactly the outer ambient frontier to the inner one. -/
theorem innerMap_mem_frontier_iff (x : B) :
    (d.innerMap x).val ∈ frontier A ↔ x.val ∈ frontier B := by
  change (d.rescale x).val ∈ frontier A ↔ x.val ∈ frontier B
  rw [frontier, frontier, d.closed_inner.closure_eq, d.closed_outer.closure_eq]
  constructor
  · intro hx
    exact ⟨x.property, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mpr hi)⟩
  · intro hx
    exact ⟨d.rescale_mem_inner x, fun hi => hx.2 ((d.rescale_mem_interior_iff x).mp hi)⟩

theorem homeomorph_mem_frontier_iff [T2Space X] [CompactSpace B] (x : B) :
    (d.homeomorph x).val ∈ frontier A ↔ x.val ∈ frontier B :=
  d.innerMap_mem_frontier_iff x

/-- On the outer frontier the actual collar rescaling is precisely first entry
along the original flow, with no further reparametrization of the endpoint. -/
theorem homeomorph_eq_flow_entryTime [T2Space X] [CompactSpace B]
    (x : B) (hx : x.val ∈ frontier B) :
    (d.homeomorph x).val = F (entryTime F A x.val) x.val := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hx
  have ho : (d.origin x).val = x.val := by
    change F (d.duration x - d.time) x.val = x.val
    rw [ht, sub_self, F.map_zero_apply]
  change (d.rescale x).val = _
  rw [d.rescale_from_origin, ht, d.time_mul_factor, sub_sub_cancel]
  change F (entryTime F A (d.origin x).val) (d.origin x).val = _
  rw [ho]

/-- A known trajectory from the outer frontier to the inner frontier computes
the constructed homeomorphism exactly. -/
theorem homeomorph_eq_flow_of_mem_frontier [T2Space X] [CompactSpace B]
    (x : B) (hx : x.val ∈ frontier B) {t : ℝ} (ht : 0 ≤ t)
    (hfront : F t x.val ∈ frontier A) :
    (d.homeomorph x).val = F t x.val := by
  rw [d.homeomorph_eq_flow_entryTime x hx,
    entryTime_eq_of_flow_mem_frontier F d.closed_inner d.strict_inner ht hfront]

/-- The inverse collar homeomorphism follows any backward trajectory from the
inner frontier to the outer frontier. -/
theorem homeomorph_symm_eq_flow_of_mem_frontier [T2Space X] [CompactSpace B]
    (y : A) (hy : y.val ∈ frontier A) {t : ℝ} (ht : t ≤ 0)
    (hfront : F t y.val ∈ frontier B) :
    (d.homeomorph.symm y).val = F t y.val := by
  have hmem : F t y.val ∈ B := by
    simpa only [d.closed_outer.closure_eq] using frontier_subset_closure hfront
  let x : B := ⟨F t y.val, hmem⟩
  have hreturn : F (-t) x.val = y.val := by
    change F (-t) (F t y.val) = y.val
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have heq : d.homeomorph x = y := by
    apply Subtype.ext
    rw [d.homeomorph_eq_flow_of_mem_frontier x hfront (neg_nonneg.mpr ht)
      (hreturn ▸ hy), hreturn]
  have hinv := congrArg d.homeomorph.symm heq
  rw [d.homeomorph.symm_apply_apply] at hinv
  exact congrArg (fun z : B => z.val) hinv.symm

/-- Restrict the explicit flow-collar map and inverse to the full ambient frontiers. -/
def frontierHomeomorph [T2Space X] [CompactSpace B] : frontier B ≃ₜ frontier A := by
  have hB : frontier B ⊆ B := by
    intro x hx
    have hxc : x ∈ closure B := frontier_subset_closure hx
    rwa [d.closed_outer.closure_eq] at hxc
  have hA : frontier A ⊆ A := by
    intro x hx
    have hxc : x ∈ closure A := frontier_subset_closure hx
    rwa [d.closed_inner.closure_eq] at hxc
  let iB : frontier B → B := fun x => ⟨x, hB x.property⟩
  let iA : frontier A → A := fun y => ⟨y, hA y.property⟩
  have hiB : Continuous iB := continuous_subtype_val.subtype_mk _
  have hiA : Continuous iA := continuous_subtype_val.subtype_mk _
  let f : frontier B → frontier A := fun x =>
    ⟨(d.homeomorph (iB x)).val, (d.homeomorph_mem_frontier_iff (iB x)).mpr x.property⟩
  let g : frontier A → frontier B := fun y =>
    ⟨(d.homeomorph.symm (iA y)).val, by
      apply (d.homeomorph_mem_frontier_iff (d.homeomorph.symm (iA y))).mp
      rw [d.homeomorph.apply_symm_apply]
      exact y.property⟩
  exact {
    toFun := f
    invFun := g
    left_inv := fun x => Subtype.ext
      (congrArg (fun z : B => z.val) (d.homeomorph.symm_apply_apply (iB x)))
    right_inv := fun y => Subtype.ext
      (congrArg (fun z : A => z.val) (d.homeomorph.apply_symm_apply (iA y)))
    continuous_toFun :=
      (continuous_subtype_val.comp (d.homeomorph.continuous.comp hiB)).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.comp (d.homeomorph.symm.continuous.comp hiA)).subtype_mk _ }

/-- Points shared by the inner region and the outer frontier are not moved by rescaling. -/
theorem rescale_eq_self_of_mem_inner_frontier_outer (x : B) (hxA : x.val ∈ A)
    (hxB : x.val ∈ frontier B) : d.rescale x = x := by
  have ht := (d.duration_eq_time_iff_frontier x).mpr hxB
  have hret := d.duration_le_retained x hxA
  rw [ht] at hret
  have hfac : d.factor x = 1 := by
    nlinarith [d.factor_le_one x, d.time_pos]
  apply Subtype.ext
  change F (d.shift x) x.val = x.val
  simp only [shift, hfac, sub_self, mul_zero, F.map_zero_apply]

theorem homeomorph_fixed_on_common_frontier [T2Space X] [CompactSpace B]
    (x : B) (hxA : x.val ∈ A) (hxB : x.val ∈ frontier B) :
    (d.homeomorph x).val = x.val :=
  congrArg (fun y : B => y.val) (d.rescale_eq_self_of_mem_inner_frontier_outer x hxA hxB)

theorem homeomorph_symm_fixed_on_common_frontier [T2Space X] [CompactSpace B]
    (y : A) (hyB : y.val ∈ frontier B) : (d.homeomorph.symm y).val = y.val := by
  let x : B := ⟨y.val, d.inner_subset y.property⟩
  have heq : d.homeomorph x = y :=
    Subtype.ext (d.homeomorph_fixed_on_common_frontier x y.property hyB)
  have hh := congrArg d.homeomorph.symm heq
  rw [d.homeomorph.symm_apply_apply] at hh
  exact congrArg (fun z : B => z.val) hh.symm

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData
