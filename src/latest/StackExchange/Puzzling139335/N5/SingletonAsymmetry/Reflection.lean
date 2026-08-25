import StackExchange.Puzzling139335.N5.SingletonAsymmetry
import StackExchange.Puzzling139335.N5.AcuteSymmetry

/-!
# The singleton-corner piece is not diagonally invariant

The base piece has only one forty-five-degree support point.  Any intrinsic
symmetry fixes that point, whereas a diagonal symmetry of the singleton
piece would send its image onto the square diagonal.  The proved actual
coordinate obstruction excludes this.
-/

open Set Metric

namespace Puzzling139335.N5

theorem Normalized.base_support45 {d : SquareDissection} (h : Normalized d) :
    AcuteCorner.Supports45 (d.piece 0) (corner 0) := by
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, ?_, ?_⟩
  · change corner 0 = (0 : Plane)
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  · rintro _ ⟨p, hp, rfl⟩
    change 0 ≤ p 1 ∧ p 1 ≤ p 0
    exact ⟨(d.piece_subset 0 hp).2.1, h.below_diagonal hp⟩

theorem Normalized.full_bottom_right {d : SquareDissection} (h : Normalized d) :
    UnitPairs.IsFullSquareCorner (d.piece 0) (corner 1) := by
  have hcount := count_one_of_ne_split d h.incidence_count h.split_count
    (by decide : (1 : Fin 4) ≠ 0)
  have hunique := unique_corner_of_count_one d hcount h.bottom_right
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood 0 hunique
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, 1, ε, hε, ?_, rfl, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact d.piece_subset 0 hp
  · intro p hp
    exact ⟨p, hnear hp, rfl⟩

theorem Normalized.symmetry_fixes_origin {d : SquareDissection} (h : Normalized d)
    (hc : d.HasProtectedCenter) (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' d.piece 0 = d.piece 0) : g (corner 0) = corner 0 :=
  symmetry_fixes_corner_zero d hc 0 h.bottom_left h.bottom_right
    h.full_bottom_right h.base_support45 g hg

theorem Normalized.singleton_not_diagonal_invariant {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    ReflectionSeparation.diagonal '' d.piece 2 ≠ d.piece 2 := by
  intro hR
  obtain ⟨e, he⟩ := d.congruent 0 2
  let g := (e.trans ReflectionSeparation.diagonal).trans e.symm
  have hg : g '' d.piece 0 = d.piece 0 := by
    calc
      g '' d.piece 0 = e.symm '' (ReflectionSeparation.diagonal '' (e '' d.piece 0)) := by
        simp only [g, AffineIsometryEquiv.coe_trans, image_image, Function.comp_def]
      _ = e.symm '' d.piece 2 := by rw [he, hR]
      _ = d.piece 0 := by
        rw [← he, image_image]
        simp
  have hfix := h.symmetry_fixes_origin hc g hg
  have hdiag : ReflectionSeparation.diagonal (e (corner 0)) = e (corner 0) := by
    have hefix := congrArg e hfix
    simpa only [g, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      e.apply_symm_apply] using hefix
  have hcoords : e (corner 0) 0 = e (corner 0) 1 := by
    simpa only [ReflectionSeparation.diagonal_apply_zero] using
      (congrArg (fun p : Plane => p 0) hdiag).symm
  exact h.origin_image_off_diagonal hc e he hcoords

end Puzzling139335.N5
