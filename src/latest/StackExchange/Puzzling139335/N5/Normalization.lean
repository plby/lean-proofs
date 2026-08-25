import StackExchange.Puzzling139335.N5.SplitPair
import StackExchange.Puzzling139335.N5.DiagonalPair
import StackExchange.Puzzling139335.Transform

/-!
# Actual square normalization of the five-incidence configuration

One square symmetry puts the shared corner at the origin and the two
neighboring corners at bottom right and top left.  Conjugating the actual
relative placement then gives the diagonal reflection between the pieces.
-/

open Set

namespace Puzzling139335.N5

open SquareSymmetry

theorem exists_corner_chart {s a b : Fin 4}
    (horder : (a = s + 1 ∧ b = s + 3) ∨ (a = s + 3 ∧ b = s + 1)) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f '' unitSquare = unitSquare ∧
      f (corner s) = corner 0 ∧ f (corner a) = corner 1 ∧
      f (corner b) = corner 3 ∧ f (corner (s + 2)) = corner 2 := by
  have hsa : a = s + 1 ∨ a = s + 3 := by
    rcases horder with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hsb : b = s + 1 ∨ b = s + 3 := by
    rcases horder with h | h
    · exact Or.inr h.2
    · exact Or.inl h.2
  have hab : a ≠ b := by
    rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases s <;> decide
  have hzero : cornerFlip s (corner s) = corner 0 := by
    rw [cornerFlip_corner]
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hopp : cornerFlip s (corner (s + 2)) = corner 2 := by
    fin_cases s <;> ext i <;> fin_cases i <;>
      norm_num [cornerFlipPoint, corner, Fin.ext_iff, Fin.val_add]
  have hne : cornerFlip s (corner a) ≠ cornerFlip s (corner b) := by
    intro h
    exact hab (corner_injective ((cornerFlip s).injective h))
  have hd0 : ReflectionSeparation.diagonal (corner 0) = corner 0 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hd1 : ReflectionSeparation.diagonal (corner 1) = corner 3 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hd2 : ReflectionSeparation.diagonal (corner 2) = corner 2 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hd3 : ReflectionSeparation.diagonal (corner 3) = corner 1 := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  rcases cornerFlip_adjacent s a hsa with ha | ha
  · have hb : cornerFlip s (corner b) = corner 3 := by
      rcases cornerFlip_adjacent s b hsb with hb | hb
      · exact (hne (ha.trans hb.symm)).elim
      · exact hb
    exact ⟨cornerFlip s, cornerFlip_image_unitSquare s, hzero, ha, hb, hopp⟩
  · have hb : cornerFlip s (corner b) = corner 1 := by
      rcases cornerFlip_adjacent s b hsb with hb | hb
      · exact hb
      · exact (hne (ha.trans hb.symm)).elim
    refine ⟨(cornerFlip s).trans ReflectionSeparation.diagonal, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        ((cornerFlip s).trans ReflectionSeparation.diagonal) '' unitSquare =
            ReflectionSeparation.diagonal '' (cornerFlip s '' unitSquare) := by
          simp only [AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
        _ = unitSquare := by
          rw [cornerFlip_image_unitSquare, ReflectionSeparation.diagonal_image_unitSquare]
    · change ReflectionSeparation.diagonal (cornerFlip s (corner s)) = corner 0
      rw [hzero, hd0]
    · change ReflectionSeparation.diagonal (cornerFlip s (corner a)) = corner 1
      rw [ha, hd3]
    · change ReflectionSeparation.diagonal (cornerFlip s (corner b)) = corner 3
      rw [hb, hd1]
    · change ReflectionSeparation.diagonal (cornerFlip s (corner (s + 2))) = corner 2
      rw [hopp, hd2]

/-- Matching actual intrinsic endpoints becomes the actual diagonal
reflection after one common change of the square's orientation. -/
theorem exists_normalized_pair (d : SquareDissection) {s a b p q r : Fin 4}
    (horder : (a = s + 1 ∧ b = s + 3) ∨ (a = s + 3 ∧ b = s + 1))
    (hsp : corner s ∈ d.piece p) (hpa : corner a ∈ d.piece p)
    (hr : corner (s + 2) ∈ d.piece r)
    (hts : d.intrinsicCorner p s = d.intrinsicCorner q s)
    (htab : d.intrinsicCorner p a = d.intrinsicCorner q b) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f '' unitSquare = unitSquare ∧
      corner 0 ∈ f '' d.piece p ∧ corner 1 ∈ f '' d.piece p ∧
      ReflectionSeparation.diagonal '' (f '' d.piece p) = f '' d.piece q ∧
      corner 2 ∈ f '' d.piece r := by
  obtain ⟨f, hfS, hfs, hfa, hfb, hfopp⟩ := exists_corner_chart horder
  let d' := d.map f hfS
  let g := (f.symm.trans (d.relativePlacement p q)).trans f
  have hgimage : g '' d'.piece p = d'.piece q := by
    change g '' (f '' d.piece p) = f '' d.piece q
    calc
      g '' (f '' d.piece p) = f '' (d.relativePlacement p q '' d.piece p) := by
        simp only [g, AffineIsometryEquiv.coe_trans, image_image, Function.comp_def,
          f.symm_apply_apply]
      _ = f '' d.piece q := by rw [d.relativePlacement_image]
  have hg0 : g (corner 0) = corner 0 := by
    calc
      g (corner 0) = g (f (corner s)) := by rw [hfs]
      _ = f (d.relativePlacement p q (corner s)) := by simp [g]
      _ = f (corner s) := by rw [d.relativePlacement_corner hts]
      _ = corner 0 := hfs
  have hg1 : g (corner 1) = corner 3 := by
    calc
      g (corner 1) = g (f (corner a)) := by rw [hfa]
      _ = f (d.relativePlacement p q (corner a)) := by simp [g]
      _ = f (corner b) := by rw [d.relativePlacement_corner htab]
      _ = corner 3 := hfb
  have hgdiag := congruence_eq_diagonal d' p q g hgimage hg0 hg1
  refine ⟨f, hfS, ?_, ?_, ?_, ?_⟩
  · rw [← hfs]
    exact mem_image_of_mem f hsp
  · rw [← hfa]
    exact mem_image_of_mem f hpa
  · change ReflectionSeparation.diagonal '' d'.piece p = d'.piece q
    rwa [← hgdiag]
  · rw [← hfopp]
    exact mem_image_of_mem f hr

theorem exists_normalized_double_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s p q r : Fin 4}
    (hs : d.cornerTileCount s = 2) (hpq : p ≠ q)
    (hpcount : d.tileCornerCount p = 2) (hqcount : d.tileCornerCount q = 2)
    (hrcount : d.tileCornerCount r = 1)
    (hsp : corner s ∈ d.piece p) (hsq : corner s ∈ d.piece q) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f '' unitSquare = unitSquare ∧
      corner 0 ∈ f '' d.piece p ∧ corner 1 ∈ f '' d.piece p ∧
      ReflectionSeparation.diagonal '' (f '' d.piece p) = f '' d.piece q ∧
      corner 2 ∈ f '' d.piece r := by
  obtain ⟨a, b, horder, hpa, _, hr, hts, htab⟩ :=
    two_double_tiles_share_pair d hc hN htypes hs hpq hpcount hqcount hrcount hsp hsq
  exact exists_normalized_pair d horder hsp hpa hr hts htab

/-- The source point of a unique target corner cannot be a square corner
when the source and target pieces have different corner counts. -/
theorem preimage_unique_corner_not_corner (d : SquareDissection) {i j b : Fin 4}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (hunique : ∀ k, k ≠ j → corner b ∉ d.piece k)
    (hcount : d.tileCornerCount i ≠ d.tileCornerCount j) (a : Fin 4) :
    e.symm (corner b) ≠ corner a := by
  intro hcorner
  have hinv : e.symm '' d.piece j = d.piece i := by
    rw [← he, image_image]
    simp
  have hS := d.unique_corner_congruence_preserves_square j i b a e.symm hinv
    hcorner hunique
  exact hcount (d.tileCornerCount_eq_of_square_congruence j i e.symm hinv hS).symm

end Puzzling139335.N5
