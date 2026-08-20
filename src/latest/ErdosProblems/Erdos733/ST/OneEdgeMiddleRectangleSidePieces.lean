import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlanarRot90CoefficientUniqueness
import ErdosProblems.Erdos733.ST.PlanarRot90Decomposition
import ErdosProblems.Erdos733.ST.PlanarRot90Norm

open Classical
noncomputable section

-- [TABLET NODE: OneEdgeMiddleRectangleSidePieces]
lemma OneEdgeMiddleRectangleSidePieces
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (t0 t1 δ : ℝ)
    (hab : a ≠ b)
    (ht0 : 0 < t0) (ht01 : t0 < t1) (ht1 : t1 < 1)
    (hδ : 0 < δ)
    (hsep :
      ∀ m, m ∈ AffineMap.lineMap a b '' Set.Icc t0 t1 →
        ∀ y, y ∈ A → δ ≤ dist m y) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ middleRect leftSide rightSide : Set (EuclideanSpace ℝ (Fin 2)),
        middleRect.Nonempty ∧ IsOpen middleRect ∧
        leftSide.Nonempty ∧ IsOpen leftSide ∧ IsConnected leftSide ∧
        rightSide.Nonempty ∧ IsOpen rightSide ∧ IsConnected rightSide ∧
        leftSide ⊆ middleRect ∧ rightSide ⊆ middleRect ∧
        leftSide ⊆ (A ∪ segment ℝ a b)ᶜ ∧
        rightSide ⊆ (A ∪ segment ℝ a b)ᶜ ∧
        middleRect \ segment ℝ a b ⊆ leftSide ∪ rightSide := by
-- BODY
  classical
  let d : EuclideanSpace ℝ (Fin 2) := b - a
  let n : EuclideanSpace ℝ (Fin 2) := PlanarRot90 d
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr hab.symm
  have hnorm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let ε : ℝ := δ / (2 * ‖d‖)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hwidth : ε * ‖d‖ < δ := by
    dsimp [ε]
    field_simp [ne_of_gt hnorm_pos]
    linarith
  let coord : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => inner ℝ (x - a) d / (‖d‖ ^ 2)
  let side : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => inner ℝ (x - a) n / (‖d‖ ^ 2)
  let middleRect : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | coord x ∈ Set.Ioo t0 t1 ∧ side x ∈ Set.Ioo (-ε) ε}
  let leftSide : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | coord x ∈ Set.Ioo t0 t1 ∧ side x ∈ Set.Ioo 0 ε}
  let rightSide : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | coord x ∈ Set.Ioo t0 t1 ∧ side x ∈ Set.Ioo (-ε) 0}
  have hcoord_cont : Continuous coord := by
    dsimp [coord]
    fun_prop
  have hside_cont : Continuous side := by
    dsimp [side]
    fun_prop
  have hmiddle_open : IsOpen middleRect := by
    dsimp [middleRect]
    exact (isOpen_Ioo.preimage hcoord_cont).inter (isOpen_Ioo.preimage hside_cont)
  have hleft_open : IsOpen leftSide := by
    dsimp [leftSide]
    exact (isOpen_Ioo.preimage hcoord_cont).inter (isOpen_Ioo.preimage hside_cont)
  have hright_open : IsOpen rightSide := by
    dsimp [rightSide]
    exact (isOpen_Ioo.preimage hcoord_cont).inter (isOpen_Ioo.preimage hside_cont)
  have hcoord_chart (u v : ℝ) :
      coord (a + u • d + v • n) = u := by
    have hrep :
        (a + u • d + v • n) - a = u • d + v • PlanarRot90 d := by
      dsimp [n]
      module
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d)
        (v := (a + u • d + v • n) - a) hd hrep
    simpa [coord, n] using hcoeff.1.symm
  have hside_chart (u v : ℝ) :
      side (a + u • d + v • n) = v := by
    have hrep :
        (a + u • d + v • n) - a = u • d + v • PlanarRot90 d := by
      dsimp [n]
      module
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d)
        (v := (a + u • d + v • n) - a) hd hrep
    simpa [side, n] using hcoeff.2.symm
  let mid : ℝ := (t0 + t1) / 2
  have hmid : mid ∈ Set.Ioo t0 t1 := by
    dsimp [mid]
    constructor <;> linarith
  have hhalf_left : ε / 2 ∈ Set.Ioo 0 ε := by
    constructor <;> linarith
  have hhalf_right : -(ε / 2) ∈ Set.Ioo (-ε) 0 := by
    constructor <;> linarith
  have hhalf_rect_left : ε / 2 ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith
  have hmiddle_nonempty : middleRect.Nonempty := by
    refine ⟨a + mid • d + (ε / 2) • n, ?_⟩
    exact ⟨by simpa [hcoord_chart] using hmid,
      by simpa [hside_chart] using hhalf_rect_left⟩
  have hleft_nonempty : leftSide.Nonempty := by
    refine ⟨a + mid • d + (ε / 2) • n, ?_⟩
    exact ⟨by simpa [hcoord_chart] using hmid,
      by simpa [hside_chart] using hhalf_left⟩
  have hright_nonempty : rightSide.Nonempty := by
    refine ⟨a + mid • d + (-(ε / 2)) • n, ?_⟩
    constructor
    · rw [hcoord_chart]
      exact hmid
    · rw [hside_chart]
      exact hhalf_right
  have hcoord_combo
      (x y : EuclideanSpace ℝ (Fin 2)) (r s : ℝ) (hrs : r + s = 1) :
      coord (r • x + s • y) = r • coord x + s • coord y := by
    dsimp [coord]
    have hvec : r • x + s • y - a = r • (x - a) + s • (y - a) := by
      calc
        r • x + s • y - a = r • x + s • y - (r + s) • a := by
          rw [hrs, one_smul]
        _ = r • (x - a) + s • (y - a) := by
          module
    rw [hvec, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hside_combo
      (x y : EuclideanSpace ℝ (Fin 2)) (r s : ℝ) (hrs : r + s = 1) :
      side (r • x + s • y) = r • side x + s • side y := by
    dsimp [side]
    have hvec : r • x + s • y - a = r • (x - a) + s • (y - a) := by
      calc
        r • x + s • y - a = r • x + s • y - (r + s) • a := by
          rw [hrs, one_smul]
        _ = r • (x - a) + s • (y - a) := by
          module
    rw [hvec, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hleft_convex : Convex ℝ leftSide := by
    intro x hx y hy r s hr hs hrs
    dsimp [leftSide] at hx hy ⊢
    constructor
    · have h :=
        (convex_Ioo (𝕜 := ℝ) t0 t1) hx.1 hy.1 hr hs hrs
      simpa [hcoord_combo x y r s hrs] using h
    · have h :=
        (convex_Ioo (𝕜 := ℝ) (0 : ℝ) ε) hx.2 hy.2 hr hs hrs
      simpa [hside_combo x y r s hrs] using h
  have hright_convex : Convex ℝ rightSide := by
    intro x hx y hy r s hr hs hrs
    dsimp [rightSide] at hx hy ⊢
    constructor
    · have h :=
        (convex_Ioo (𝕜 := ℝ) t0 t1) hx.1 hy.1 hr hs hrs
      simpa [hcoord_combo x y r s hrs] using h
    · have h :=
        (convex_Ioo (𝕜 := ℝ) (-ε) (0 : ℝ)) hx.2 hy.2 hr hs hrs
      simpa [hside_combo x y r s hrs] using h
  have hleft_connected : IsConnected leftSide :=
    hleft_convex.isConnected hleft_nonempty
  have hright_connected : IsConnected rightSide :=
    hright_convex.isConnected hright_nonempty
  have hleft_subset_middle : leftSide ⊆ middleRect := by
    intro x hx
    dsimp [leftSide] at hx
    dsimp [middleRect]
    exact ⟨hx.1, ⟨by linarith [hε, hx.2.1], hx.2.2⟩⟩
  have hright_subset_middle : rightSide ⊆ middleRect := by
    intro x hx
    dsimp [rightSide] at hx
    dsimp [middleRect]
    exact ⟨hx.1, ⟨hx.2.1, by linarith [hε, hx.2.2]⟩⟩
  have hside_segment {x : EuclideanSpace ℝ (Fin 2)}
      (hxseg : x ∈ segment ℝ a b) : side x = 0 := by
    rw [segment_eq_image_lineMap] at hxseg
    rcases hxseg with ⟨t, ht, rfl⟩
    have hrep :
        AffineMap.lineMap a b t - a =
          t • d + (0 : ℝ) • PlanarRot90 d := by
      rw [AffineMap.lineMap_apply_module]
      dsimp [d]
      module
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := d)
        (v := AffineMap.lineMap a b t - a) hd hrep
    simpa [side, n] using hcoeff.2.symm
  have hsegment_of_coord_side_zero {x : EuclideanSpace ℝ (Fin 2)}
      (hxcoord : coord x ∈ Set.Ioo t0 t1) (hxside : side x = 0) :
      x ∈ segment ℝ a b := by
    rw [segment_eq_image_lineMap]
    refine ⟨coord x, ⟨?_, ?_⟩, ?_⟩
    · linarith [ht0, hxcoord.1]
    · linarith [ht1, hxcoord.2]
    · rw [AffineMap.lineMap_apply_module]
      have hdecomp :
          x - a = coord x • d + side x • n := by
        simpa [coord, side, n] using PlanarRot90Decomposition d (x - a) hd
      calc
        (1 - coord x) • a + coord x • b =
            a + coord x • (b - a) := by
          module
        _ = a + (x - a) := by
          rw [hdecomp, hxside]
          simp [d, n]
        _ = x := by
          module
  have hdist_axis (x : EuclideanSpace ℝ (Fin 2)) :
      dist (AffineMap.lineMap a b (coord x)) x = |side x| * ‖d‖ := by
    rw [dist_eq_norm]
    have hdecomp :
        x - a = coord x • d + side x • n := by
      simpa [coord, side, n] using PlanarRot90Decomposition d (x - a) hd
    have hsub :
        AffineMap.lineMap a b (coord x) - x = - side x • n := by
      rw [AffineMap.lineMap_apply_module]
      calc
        (1 - coord x) • a + coord x • b - x =
            a + coord x • (b - a) - x := by
              module
        _ =
            - ((x - a) - coord x • d) := by
              dsimp [d]
              module
        _ = - side x • n := by
              rw [hdecomp]
              module
    rw [hsub]
    simpa using
      (by
        rw [norm_smul, PlanarRot90Norm, Real.norm_eq_abs, abs_neg] :
          ‖(-side x) • n‖ = |side x| * ‖d‖)
  have hsubset_compl_of_side_interval
      {S : Set (EuclideanSpace ℝ (Fin 2))}
      (hS_coord : ∀ x, x ∈ S → coord x ∈ Set.Ioo t0 t1)
      (hS_side_abs : ∀ x, x ∈ S → |side x| < ε)
      (hS_side_ne : ∀ x, x ∈ S → side x ≠ 0) :
      S ⊆ (A ∪ segment ℝ a b)ᶜ := by
    intro x hx hxUnion
    rcases hxUnion with hxA | hxseg
    · let m := AffineMap.lineMap a b (coord x)
      have hm_mem : m ∈ AffineMap.lineMap a b '' Set.Icc t0 t1 := by
        refine ⟨coord x, ⟨?_, ?_⟩, rfl⟩
        · exact le_of_lt (hS_coord x hx).1
        · exact le_of_lt (hS_coord x hx).2
      have hsep_x : δ ≤ dist m x := hsep m hm_mem x hxA
      have hdist_lt : dist m x < δ := by
        calc
          dist m x = |side x| * ‖d‖ := hdist_axis x
          _ < ε * ‖d‖ := mul_lt_mul_of_pos_right (hS_side_abs x hx) hnorm_pos
          _ < δ := hwidth
      exact not_lt_of_ge hsep_x hdist_lt
    · exact hS_side_ne x hx (hside_segment hxseg)
  have hleft_subset_compl : leftSide ⊆ (A ∪ segment ℝ a b)ᶜ := by
    refine hsubset_compl_of_side_interval ?_ ?_ ?_
    · intro x hx
      exact hx.1
    · intro x hx
      dsimp [leftSide] at hx
      exact abs_lt.mpr ⟨by linarith [hε, hx.2.1], hx.2.2⟩
    · intro x hx
      dsimp [leftSide] at hx
      exact ne_of_gt hx.2.1
  have hright_subset_compl : rightSide ⊆ (A ∪ segment ℝ a b)ᶜ := by
    refine hsubset_compl_of_side_interval ?_ ?_ ?_
    · intro x hx
      exact hx.1
    · intro x hx
      dsimp [rightSide] at hx
      exact abs_lt.mpr ⟨hx.2.1, by linarith [hε, hx.2.2]⟩
    · intro x hx
      dsimp [rightSide] at hx
      exact ne_of_lt hx.2.2
  have hcover : middleRect \ segment ℝ a b ⊆ leftSide ∪ rightSide := by
    intro x hx
    rcases hx with ⟨hxrect, hxnotseg⟩
    dsimp [middleRect] at hxrect
    rcases lt_trichotomy (side x) 0 with hneg | hzero | hpos
    · right
      dsimp [rightSide]
      exact ⟨hxrect.1, ⟨hxrect.2.1, hneg⟩⟩
    · exfalso
      exact hxnotseg (hsegment_of_coord_side_zero hxrect.1 hzero)
    · left
      dsimp [leftSide]
      exact ⟨hxrect.1, ⟨hpos, hxrect.2.2⟩⟩
  exact ⟨ε, hε, middleRect, leftSide, rightSide,
    hmiddle_nonempty, hmiddle_open,
    hleft_nonempty, hleft_open, hleft_connected,
    hright_nonempty, hright_open, hright_connected,
    hleft_subset_middle, hright_subset_middle,
    hleft_subset_compl, hright_subset_compl, hcover⟩
