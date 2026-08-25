import StackExchange.Puzzling139335.JordanRegion
import Wikipedia.SchoenfliesTheorem.JordanSchoenflies
import Mathlib.Analysis.Convex.Topology

/-!
# Access arcs in Jordan regions

The square extension in the existing Schoenflies development pulls a straight
segment back to an access arc.  Thus every boundary point of a Jordan region is
accessible from any prescribed interior point, even for a nonrectifiable curve.
-/

open Set

namespace Schoenflies.IsJordanCurve

/-- Any interior point can be joined to any boundary point by a simple arc
whose other points lie strictly inside the Jordan curve. -/
theorem exists_arc_to_boundary {C : Set Plane} {x y : Plane}
    (hC : IsJordanCurve C) (hx : x ∈ inside C) (hy : y ∈ C) :
    ∃ A : Set Plane, IsArcBetween A x y ∧ A \ {y} ⊆ inside C := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨f, g, hfg, -⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, G, hF, hFeq⟩ := squareExtension C f g hC hfg
  have hFC : F '' C = modelCurve := (Set.EqOn.image_eq hFeq).trans hfg.image_eq
  have hFin : F '' inside C = Plane.openSquare 0 1 := by
    rw [← closedSquare_sdiff_modelCurve]
    exact image_eq_diff_of_bijOn_union hF.bijOn hFC (disjoint_curve_inside C)
  have hGFin : MapsTo G (Plane.openSquare 0 1) (inside C) := by
    intro z hz
    rw [← hFin] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [hF.invOn.1 (Or.inr hw)] using hw
  have hxQ : F x ∈ interior (Plane.closedSquare 0 1) := by
    rw [interior_closedSquare_zero_one, ← hFin]
    exact ⟨x, hx, rfl⟩
  have hyQ : F y ∈ Plane.closedSquare 0 1 := hF.mapsTo (Or.inl hy)
  have hxy : F x ≠ F y := by
    intro h
    exact hx.1 (hF.injOn (Or.inr hx) (Or.inl hy) h ▸ hy)
  have hseg : segment ℝ (F x) (F y) ⊆ Plane.closedSquare 0 1 :=
    (Plane.convex_closedSquare 0 1).segment_subset (interior_subset hxQ) hyQ
  have hGFx : G (F x) = x := hF.invOn.1 (Or.inr hx)
  have hGFy : G (F y) = y := hF.invOn.1 (Or.inl hy)
  refine ⟨G '' segment ℝ (F x) (F y), ?_, ?_⟩
  · simpa only [hGFx, hGFy] using
      (isArcBetween_segment hxy).image_of_injOn hseg hF.continuousOn_inv hF.symm.injOn
  · rintro z ⟨⟨w, hw, rfl⟩, hzy⟩
    have hwy : w ≠ F y := by
      intro h
      apply hzy
      simp only [h, hGFy, mem_singleton_iff]
    rcases eq_or_ne w (F x) with rfl | hwx
    · simpa only [hGFx] using hx
    · apply hGFin
      rw [← interior_closedSquare_zero_one]
      exact (Plane.convex_closedSquare 0 1).openSegment_interior_self_subset_interior
        hxQ hyQ (mem_openSegment_of_ne_left_right hwx.symm hwy.symm hw)

/-- A square chart of the closed Jordan domain can put any specified interior
point at the centre of the model square. -/
theorem exists_pointed_square_chart {C : Set Plane} {x : Plane}
    (hC : IsJordanCurve C) (hx : x ∈ inside C) :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G (C ∪ inside C) (Plane.closedSquare 0 1) ∧
      F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 ∧ F x = 0 := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨f, g, hfg, -⟩ := exists_isHomeoOn_of_homeomorph e
  have hzero : (0 : Plane) ∈ inside modelCurve := by
    rw [inside_modelCurve, mem_openSquare_zero_one]
    simp [Plane.supNorm]
  obtain ⟨F, G, hF, hFeq, hFx⟩ := pointed_extension squareExtension
    C modelCurve f g x 0 hC isJordanCurve_modelCurve hfg hx hzero
  have hFC : F '' C = modelCurve := (Set.EqOn.image_eq hFeq).trans hfg.image_eq
  have hFin := image_inside_eq hF hFeq hfg.image_eq
  rw [inside_modelCurve] at hFin
  rw [modelCurve_union_inside] at hF
  exact ⟨F, G, hF, hFC, hFin, hFx⟩

/-- Boundary access arcs can be chosen simultaneously so that distinct arcs
meet only at their common prescribed interior endpoint. -/
theorem exists_disjoint_arcs_to_boundary {ι : Type*} {C : Set Plane} {x : Plane}
    (hC : IsJordanCurve C) (hx : x ∈ inside C) (b : ι → Plane)
    (hb : ∀ i, b i ∈ C) (hinj : Function.Injective b) :
    ∃ A : ι → Set Plane,
      (∀ i, IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ inside C) ∧
      ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  obtain ⟨F, G, hF, hFC, hFin, hFx⟩ := hC.exists_pointed_square_chart hx
  have hGFin : MapsTo G (Plane.openSquare 0 1) (inside C) := by
    intro z hz
    rw [← hFin] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [hF.invOn.1 (Or.inr hw)] using hw
  have hG0 : G 0 = x := by rw [← hFx]; exact hF.invOn.1 (Or.inr hx)
  have hGFb (i : ι) : G (F (b i)) = b i := hF.invOn.1 (Or.inl (hb i))
  have hframe (i : ι) : Plane.supDist (F (b i)) 0 = 1 := by
    have hmodel : F (b i) ∈ modelCurve := by
      rw [← hFC]
      exact ⟨b i, hb i, rfl⟩
    change Plane.supNorm (F (b i)) = 1 at hmodel
    simpa only [Plane.supDist, sub_zero] using hmodel
  have hseg (i : ι) : segment ℝ 0 (F (b i)) ⊆ Plane.closedSquare 0 1 :=
    Plane.segment_subset_closedSquare (by norm_num) (hframe i).le
  have hne (i : ι) : (0 : Plane) ≠ F (b i) := by
    intro h
    have hxb : x = b i := hF.injOn (Or.inr hx) (Or.inl (hb i)) (hFx.trans h)
    exact hx.1 (hxb ▸ hb i)
  refine ⟨fun i => G '' segment ℝ 0 (F (b i)), ?_, ?_, ?_⟩
  · intro i
    simpa only [hG0, hGFb] using (isArcBetween_segment (hne i)).image_of_injOn
      (hseg i) hF.continuousOn_inv hF.symm.injOn
  · intro i z hz
    obtain ⟨⟨w, hw, rfl⟩, hzb⟩ := hz
    have hwb : w ≠ F (b i) := by
      intro h
      apply hzb
      simp only [h, hGFb, mem_singleton_iff]
    apply hGFin
    change Plane.supDist w 0 < 1
    have hpos : 0 < Plane.supDist (F (b i)) 0 := by rw [hframe]; norm_num
    simpa only [hframe] using Plane.supDist_lt_of_mem_segment hpos hw hwb
  · intro i j hij
    apply Subset.antisymm
    · rintro z ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
      have hv_eq : v = u := hF.symm.injOn (hseg j hv) (hseg i hu) hvu
      subst v
      have hbij : F (b i) ≠ F (b j) := by
        intro h
        exact hij (hinj (hF.injOn (Or.inl (hb i)) (Or.inl (hb j)) h))
      have hu0 : u = 0 := Plane.radial_meet (by norm_num) (hframe i) (hframe j)
        hbij (fun h => False.elim (h rfl)) hu hv
      exact mem_singleton_iff.mpr (hu0 ▸ hG0)
    · exact singleton_subset_iff.mpr
        ⟨⟨0, left_mem_segment ℝ _ _, hG0⟩, ⟨0, left_mem_segment ℝ _ _, hG0⟩⟩

end Schoenflies.IsJordanCurve

namespace Puzzling139335.IsJordanRegion

/-- Every frontier point of a closed Jordan piece has a simple access arc
starting at any prescribed interior point. -/
theorem exists_arc_to_frontier {P : Set Plane} {x y : Plane}
    (hP : IsJordanRegion P) (hx : x ∈ interior P) (hy : y ∈ frontier P) :
    ∃ A : Set Plane, Schoenflies.IsArcBetween A x y ∧ A \ {y} ⊆ interior P := by
  obtain ⟨C, hC, rfl⟩ := hP
  have hsep := Schoenflies.jordan_curve_theorem hC
  rw [interior_closure_inside hsep] at hx ⊢
  rw [frontier_closure_inside hsep] at hy
  exact hC.exists_arc_to_boundary hx hy

/-- Simultaneous, mutually disjoint access spokes for a closed Jordan piece. -/
theorem exists_disjoint_arcs_to_frontier {ι : Type*} {P : Set Plane} {x : Plane}
    (hP : IsJordanRegion P) (hx : x ∈ interior P) (b : ι → Plane)
    (hb : ∀ i, b i ∈ frontier P) (hinj : Function.Injective b) :
    ∃ A : ι → Set Plane,
      (∀ i, Schoenflies.IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ interior P) ∧
      ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  obtain ⟨C, hC, rfl⟩ := hP
  have hsep := Schoenflies.jordan_curve_theorem hC
  rw [interior_closure_inside hsep] at hx ⊢
  simp only [frontier_closure_inside hsep] at hb
  exact hC.exists_disjoint_arcs_to_boundary hx b hb hinj

end Puzzling139335.IsJordanRegion
