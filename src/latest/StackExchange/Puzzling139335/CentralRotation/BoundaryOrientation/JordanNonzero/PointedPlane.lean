import Wikipedia.SchoenfliesTheorem.JordanSchoenflies

/-!
# A pointed global Jordan–Schoenflies extension

The pointed extension over the closed interior and the extension over the
closed exterior have the same boundary values.  Pasting them therefore gives
a homeomorphism of the whole plane with the prescribed interior-point image.
-/

open Set

namespace Schoenflies

variable {C C' : Set Plane}

/-- A boundary homeomorphism extends to the whole plane while carrying one
specified interior point to another.  This is the unbundled form. -/
theorem jordan_schoenflies_pointed {f g : Plane → Plane} {x y : Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C')
    (hfg : IsHomeoOn f g C C') (hx : x ∈ inside C) (hy : y ∈ inside C') :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G univ univ ∧ EqOn F f C ∧ F x = y := by
  have hsC : IsSeparating C := jordan_curve_theorem hC
  have hsC' : IsSeparating C' := jordan_curve_theorem hC'
  obtain ⟨Fi, Gi, hFi, hFieq, hFix⟩ :=
    pointed_extension squareExtension C C' f g x y hC hC' hfg hx hy
  obtain ⟨Fe, Ge, hFe, hFeeq⟩ :=
    exterior_extension_of_squareExtension squareExtension hC hC' hfg
  have hFeout : Fe '' outside C = outside C' :=
    image_outside_eq hFe hFeeq hfg.image_eq
  have hGeout : Ge '' outside C' = outside C :=
    hFe.image_inv_eq Set.subset_union_right hFeout
  have hGieq : EqOn Gi g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fi (g w) = w := by
      rw [hFieq hgw]
      exact hfg.invOn.2 hw
    calc
      Gi w = Gi (Fi (g w)) := by rw [hFw]
      _ = g w := hFi.invOn.1 (Set.mem_union_left _ hgw)
  have hGeeq : EqOn Ge g C' := by
    intro w hw
    have hgw : g w ∈ C := hfg.mapsTo_inv hw
    have hFw : Fe (g w) = w := by
      rw [hFeeq hgw]
      exact hfg.invOn.2 hw
    calc
      Ge w = Ge (Fe (g w)) := by rw [hFw]
      _ = g w := hFe.invOn.1 (Set.mem_union_left _ hgw)
  have hFint : EqOn (paste (C ∪ inside C) Fi Fe) Fi (C ∪ inside C) :=
    fun _ hz => paste_of_mem hz
  have hFext : EqOn (paste (C ∪ inside C) Fi Fe) Fe (C ∪ outside C) := by
    rintro z (hzC | hzout)
    · rw [paste_of_mem (Set.mem_union_left _ hzC), hFieq hzC, hFeeq hzC]
    · refine paste_of_notMem fun hz => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hz.resolve_left fun h => Set.disjoint_left.1
          (disjoint_curve_outside C) h hzout) hzout
  have hGint : EqOn (paste (C' ∪ inside C') Gi Ge) Gi (C' ∪ inside C') :=
    fun _ hw => paste_of_mem hw
  have hGext : EqOn (paste (C' ∪ inside C') Gi Ge) Ge (C' ∪ outside C') := by
    rintro w (hwC | hwout)
    · rw [paste_of_mem (Set.mem_union_left _ hwC), hGieq hwC, hGeeq hwC]
    · refine paste_of_notMem fun hw => ?_
      exact Set.disjoint_left.1 disjoint_inside_outside
        (hw.resolve_left fun h => Set.disjoint_left.1
          (disjoint_curve_outside C') h hwout) hwout
  refine ⟨paste (C ∪ inside C) Fi Fe, paste (C' ∪ inside C') Gi Ge,
    ⟨mapsTo_univ _ _, mapsTo_univ _ _, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← union_inside_union_outside C]
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC)
      (isClosed_union_outside hsC) (hFi.continuousOn.congr hFint)
      (hFe.continuousOn.congr hFext)
  · rw [← union_inside_union_outside C']
    exact Plane.continuousOn_union_of_isClosed (isClosed_union_inside hsC')
      (isClosed_union_outside hsC') (hFi.continuousOn_inv.congr hGint)
      (hFe.continuousOn_inv.congr hGext)
  · intro z _
    by_cases hz : z ∈ C ∪ inside C
    · rw [hFint hz, hGint (hFi.mapsTo hz), hFi.invOn.1 hz]
    · have hzout : z ∈ outside C := mem_outside_of_notMem_union_inside hz
      have hzL : z ∈ C ∪ outside C := Or.inr hzout
      have hFz : Fe z ∈ outside C' := by
        rw [← hFeout]
        exact ⟨z, hzout, rfl⟩
      rw [hFext hzL, hGext (Or.inr hFz), hFe.invOn.1 hzL]
  · intro w _
    by_cases hw : w ∈ C' ∪ inside C'
    · rw [hGint hw, hFint (hFi.mapsTo_inv hw), hFi.invOn.2 hw]
    · have hwout : w ∈ outside C' := mem_outside_of_notMem_union_inside hw
      have hwL : w ∈ C' ∪ outside C' := Or.inr hwout
      have hGw : Ge w ∈ outside C := by
        rw [← hGeout]
        exact ⟨w, hwout, rfl⟩
      rw [hGext hwL, hFext (Or.inr hGw), hFe.invOn.2 hwL]
  · exact fun z hz => (hFint (Set.mem_union_left _ hz)).trans (hFieq hz)
  · exact (hFint (Or.inr hx)).trans hFix

/-- The pointed global extension packaged as a homeomorphism of the plane. -/
theorem jordan_schoenflies_homeomorph_pointed {f g : Plane → Plane} {x y : Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C')
    (hfg : IsHomeoOn f g C C') (hx : x ∈ inside C) (hy : y ∈ inside C') :
    ∃ F : Plane ≃ₜ Plane, EqOn F f C ∧ F x = y := by
  obtain ⟨F, G, hFG, hFeq, hFx⟩ := jordan_schoenflies_pointed hC hC' hfg hx hy
  exact ⟨hFG.homeomorphOfUniv, hFeq, hFx⟩

/-- A bundled boundary homeomorphism has a global extension with any prescribed
interior-point image. -/
theorem jordan_schoenflies_of_homeomorph_pointed {x y : Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C')
    (hx : x ∈ inside C) (hy : y ∈ inside C') :
    ∃ F : Plane ≃ₜ Plane, (∀ z : ↥C, F z = e z) ∧ F x = y := by
  obtain ⟨f, g, hfg, hfe⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, hF, hFx⟩ := jordan_schoenflies_homeomorph_pointed hC hC' hfg hx hy
  exact ⟨F, (fun z => (hF z.2).trans (hfe z z.2)), hFx⟩

end Schoenflies
