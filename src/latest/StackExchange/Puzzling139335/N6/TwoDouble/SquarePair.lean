import StackExchange.Puzzling139335.N6.TwoDouble.FullPair
import StackExchange.Puzzling139335.ReflectionSeparation

/-!
# Remaining maps of an actual square-symmetry pair

Quarter-turns are excluded by the established dissection theorem. The
identity would identify two pieces with nonempty disjoint interiors.
The remaining actual congruence is one of the four square reflections
or the half-turn about its center.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

private theorem pointReflection_formula (p : Plane) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter p =
      (!₂[1 - p 0, 1 - p 1] : Plane) := by
  ext i
  fin_cases i <;>
    simp [AffineIsometryEquiv.pointReflection_apply, squareCenter,
      vsub_eq_sub, vadd_eq_add] <;> ring

/-- The relative map of two actual square-symmetry copies in a putative
counterexample is a reflection or a central half-turn. -/
theorem square_pair_map_cases (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j) (hS : e '' unitSquare = unitSquare) :
    e = ReflectionSeparation.horizontal ∨ e = ReflectionSeparation.vertical ∨
      e = ReflectionSeparation.diagonal ∨ e = ReflectionSeparation.antiDiagonal ∨
      e = AffineIsometryEquiv.pointReflection ℝ squareCenter := by
  have hinvol : Function.Involutive e := by
    rcases SymmetryOrbit.square_symmetry_classification e hS.subset with hquarter | hinvol
    · exact (d.not_hasProtectedCenter_of_quarterTurn_pair hij e hquarter hS.subset he hc).elim
    · exact hinvol
  have hnotid : ¬ (∀ p : Plane, e p = p) := by
    intro hid
    obtain ⟨p, hp⟩ := (d.jordan i).interior_nonempty
    have hpj : p ∈ interior (d.piece j) := by
      have himage := (mem_interior_image_affineIsometry e).mpr hp
      rwa [he, hid] at himage
    exact Set.disjoint_left.mp (d.disjoint_interiors hij) hp hpj
  obtain ⟨b, hb | hb⟩ := SquareSymmetry.coordinate_forms_of_maps_square_into_square e hS.subset
  · fin_cases b
    · exfalso
      apply hnotid
      intro p
      rw [hb]
      ext k
      fin_cases k <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]
    · refine Or.inr (Or.inl ?_)
      apply AffineIsometryEquiv.ext
      intro p
      exact hb p
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      ext p k
      rw [hb, pointReflection_formula]
      fin_cases k <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]
    · refine Or.inl ?_
      apply AffineIsometryEquiv.ext
      intro p
      exact hb p
  · fin_cases b
    · refine Or.inr (Or.inr (Or.inl ?_))
      ext p k
      rw [hb]
      fin_cases k <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]
    · exfalso
      have h := hinvol (corner 0)
      simp only [hb] at h
      have hcoord := congrArg (fun p : Plane => p 0) h
      norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff] at hcoord
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      ext p k
      rw [hb]
      fin_cases k <;> norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]
    · exfalso
      have h := hinvol (corner 0)
      simp only [hb] at h
      have hcoord := congrArg (fun p : Plane => p 0) h
      norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff] at hcoord

end Puzzling139335.N6.TwoDouble
