import ErdosProblems.Erdos633b.DoubledPartition
import ErdosProblems.Erdos633b.CoordinateHalfplanes
import ErdosProblems.Erdos633b.Patch

/-! Closed geometric regions and exact finite assembly for the doubled triangle. -/

namespace Erdos633b.DoubledPartition

noncomputable def region (T : Triangle) (u v r μ h : ℝ) : Piece → Set Plane
  | .abd => T.support ∩ ({p | 0 ≤ T.coordForm v (-u) p} ∩
      {p | T.coordForm v (1 - u) p ≤ v})
  | .bdg => T.support ∩ ({p | v ≤ T.coordForm v (1 - u) p} ∩
      {p | delta u v r ≤ T.coordForm (r - v) (u + r - 1) p})
  | .aef => T.support ∩ ({p | T.coordForm v (-u) p ≤ 0} ∩
      ({p | T.coordForm (r - v) (u + r - 1) p ≤ h + delta u v r} ∩
        {p | (r - 1) * μ ≤ T.coordForm (r - μ) (r - 1) p}))
  | .cfg => T.support ∩ ({p | T.coordForm (r - μ) (r - 1) p ≤ (r - 1) * μ} ∩
      ({p | T.coordForm v (-u) p ≤ 0} ∩
        {p | T.coordForm (r - v) (u + r - 1) p ≤ delta u v r}))
  | .trapezoid => T.support ∩ ({p | T.coordForm v (-u) p ≤ 0} ∩
      ({p | h + delta u v r ≤ T.coordForm (r - v) (u + r - 1) p} ∩
        ({p | T.coordForm (r - v) (u + r - 1) p ≤ delta u v r} ∩
          {p | (r - 1) * μ ≤ T.coordForm (r - μ) (r - 1) p})))

theorem ad_form (T : Triangle) (u v : ℝ) (p : Plane) :
    T.coordForm v (-u) p = ad u v (T.coord 1 p) (T.coord 2 p) := by
  dsimp only [Triangle.coordForm_apply, ad]
  ring

theorem bd_form (T : Triangle) (u v : ℝ) (p : Plane) :
    T.coordForm v (1 - u) p = bd u v (T.coord 1 p) (T.coord 2 p) + v := by
  dsimp only [Triangle.coordForm_apply, bd]
  ring

theorem dg_form (T : Triangle) (u v r : ℝ) (p : Plane) :
    T.coordForm (r - v) (u + r - 1) p =
      dg u v r (T.coord 1 p) (T.coord 2 p) + delta u v r := by
  dsimp only [Triangle.coordForm_apply, dg, delta]
  ring

theorem fg_form (T : Triangle) (r μ : ℝ) (p : Plane) :
    T.coordForm (r - μ) (r - 1) p = fg r μ (T.coord 1 p) (T.coord 2 p) + (r - 1) * μ := by
  dsimp only [Triangle.coordForm_apply, fg]
  ring

theorem mem_region (T : Triangle) (u v r μ h : ℝ) (k : Piece) (p : Plane) :
    p ∈ region T u v r μ h k ↔ closed u v r μ h (T.coord 1 p) (T.coord 2 p) k := by
  cases k <;> simp only [region, Set.mem_inter_iff, Set.mem_ofPred_eq, ad_form, bd_form,
    dg_form, fg_form, Triangle.mem_support_iff_coords, closed, outer, constraints,
    add_le_iff_nonpos_left, le_add_iff_nonneg_left, add_le_add_iff_right]

theorem mem_interior_region (T : Triangle) (u v r μ h : ℝ) (hv : 0 < v)
    (hvr : v < r) (hr1 : r < 1) (k : Piece) (p : Plane) :
    p ∈ interior (region T u v r μ h k) ↔
      p ∈ interior T.support ∧ inside u v r μ h (T.coord 1 p) (T.coord 2 p) k := by
  have hal := T.interior_coordForm_le v (-u) 0 (Or.inl hv.ne')
  have hag := T.interior_coordForm_ge v (-u) 0 (Or.inl hv.ne')
  have hbl := T.interior_coordForm_le v (1 - u) v (Or.inl hv.ne')
  have hbg := T.interior_coordForm_ge v (1 - u) v (Or.inl hv.ne')
  have hgl (c : ℝ) := T.interior_coordForm_le (r - v) (u + r - 1) c
    (Or.inl (sub_pos.mpr hvr).ne')
  have hgg (c : ℝ) := T.interior_coordForm_ge (r - v) (u + r - 1) c
    (Or.inl (sub_pos.mpr hvr).ne')
  have hfl := T.interior_coordForm_le (r - μ) (r - 1) ((r - 1) * μ)
    (Or.inr (sub_neg.mpr hr1).ne)
  have hfg := T.interior_coordForm_ge (r - μ) (r - 1) ((r - 1) * μ)
    (Or.inr (sub_neg.mpr hr1).ne)
  cases k <;> simp only [region, interior_inter, hal, hag, hbl, hbg, hgl, hgg, hfl, hfg] <;>
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ad_form, bd_form, dg_form, fg_form, inside,
      add_lt_iff_neg_right, lt_add_iff_pos_left, add_lt_add_iff_right]

theorem regions_cover (T : Triangle) (u v r μ h : ℝ) (hv : 0 < v) (hr : 0 < r)
    (huv : u + v < 1) (hδ : 0 < delta u v r) :
    (⋃ k : Piece, region T u v r μ h k) = T.support := by
  ext p
  simp only [Set.mem_iUnion, mem_region, Triangle.mem_support_iff_coords]
  constructor
  · rintro ⟨k, hk⟩
    exact hk.1
  · exact exists_closed u v r μ h _ _ hv hr huv hδ

theorem regions_disjoint_interiors (T : Triangle) (u v r μ h : ℝ)
    (hv : 0 < v) (hvr : v < r) (hr1 : r < 1) (hh : h ≤ 0) :
    Pairwise fun k l =>
      Disjoint (interior (region T u v r μ h k)) (interior (region T u v r μ h l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro p hk hl
  exact hkl (inside_unique u v r μ h _ _ hh k l
    ((mem_interior_region T u v r μ h hv hvr hr1 k p).mp hk).2
    ((mem_interior_region T u v r μ h hv hvr hr1 l p).mp hl).2)

noncomputable def assemble (T R : Triangle) (u v r μ h : ℝ)
    (hv : 0 < v) (hr : 0 < r) (hvr : v < r) (hr1 : r < 1)
    (huv : u + v < 1) (hδ : 0 < delta u v r) (hh : h ≤ 0)
    (n : Piece → ℕ) (d : ∀ k, Patch R (region T u v r μ h k) (n k)) :
    Patch R T.support (∑ k, n k) := by
  have result := Patch.glue R (region T u v r μ h) n d
    (regions_disjoint_interiors T u v r μ h hv hvr hr1 hh)
  rwa [regions_cover T u v r μ h hv hr huv hδ] at result

end Erdos633b.DoubledPartition
