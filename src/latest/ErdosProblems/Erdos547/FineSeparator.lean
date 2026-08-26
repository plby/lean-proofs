import ErdosProblems.Erdos547.ParitySeparator
import ErdosProblems.Erdos547.SeparatedAttachments

/-!
# Fine separators of finite trees

The remaining components are small, have at most two equally coloured cut
neighbours, and any two distinct cut neighbours have distance at least six.
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_fine_separator_at_scale {U : Type*} [Fintype U] (T : SimpleGraph U)
    [DecidableRel T.Adj] (hT : T.IsTree) (r : U) (q : ℕ) (hq : 1 ≤ q)
    (col : T.Coloring (Fin 2)) :
    ∃ Z : Finset U, r ∈ Z ∧ q * Z.card ≤ 30 * (Fintype.card U + q) ∧
      ∀ C : Finset U, Disjoint C Z → (T.induce (C : Set U)).Connected →
        C.card ≤ 2 * q - 1 ∧ (Z.filter (fun v ↦ 0 < degreeIn T C v)).card ≤ 2 ∧
        ∀ u ∈ Z, ∀ v ∈ Z, 0 < degreeIn T C u → 0 < degreeIn T C v →
          col u = col v ∧ (u ≠ v → 6 ≤ T.dist u v) := by
  classical
  obtain ⟨S, H, hrS, hSH, hH, hScount, hdeg, hclosed, hsmall⟩ :=
    exists_parity_separator T hT r q hq col
  obtain ⟨Z, hSZ, hZH, hZcount, hZdeg, hZclosed, hlong⟩ :=
    exists_short_path_closed_extension T hT.isAcyclic col S H hSH hdeg hclosed
  refine ⟨Z, hSZ hrS, ?_, ?_⟩
  · have hh := Nat.mul_le_mul_left q hZcount
    nlinarith only [hh, hScount]
  · intro C hCZ hC
    refine ⟨(hsmall C (hCZ.mono_right hSZ) hC).1,
      card_cut_neighbours_le_two T hT.isAcyclic C H Z hC hH hZH hCZ
        (fun u hu hn ↦ (hZdeg u hu hn).le), ?_⟩
    intro u hu v hv hdu hdv
    refine ⟨cut_attachment_colours_equal T hT.isAcyclic col C H Z hC hH hZH hCZ hZclosed
      hu hv hdu hdv, ?_⟩
    intro huv
    exact cut_attachment_distance_lower T hT.isAcyclic C H Z hC.preconnected hH.preconnected
      hZH hCZ hlong hu hv huv hdu hdv

open scoped Classical in
theorem exists_fine_separator {U : Type*} [Fintype U] (T : SimpleGraph U)
    [DecidableRel T.Adj] (hT : T.IsTree) (r : U) (ℓ : ℕ)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ Fintype.card U) (col : T.Coloring (Fin 2)) :
    ∃ Z : Finset U, r ∈ Z ∧ ℓ * Z.card ≤ 180 * Fintype.card U ∧
      ∀ C : Finset U, Disjoint C Z → (T.induce (C : Set U)).Connected →
        C.card ≤ ℓ ∧ (Z.filter (fun v ↦ 0 < degreeIn T C v)).card ≤ 2 ∧
        ∀ u ∈ Z, ∀ v ∈ Z, 0 < degreeIn T C u → 0 < degreeIn T C v →
          col u = col v ∧ (u ≠ v → 6 ≤ T.dist u v) := by
  classical
  let q := ℓ / 2
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hqn : q ≤ Fintype.card U := by dsimp [q]; omega
  have hℓq : ℓ ≤ 3 * q := by dsimp [q]; omega
  obtain ⟨Z, hr, hcount, hsmall⟩ := exists_fine_separator_at_scale T hT r q hq col
  refine ⟨Z, hr, ?_, ?_⟩
  · have hh := Nat.mul_le_mul_right Z.card hℓq
    nlinarith only [hh, hcount, hqn]
  · intro C hCZ hC
    obtain ⟨hc, htwo, hrest⟩ := hsmall C hCZ hC
    refine ⟨?_, htwo, hrest⟩
    dsimp [q] at hc
    omega

end Erdos547

#print axioms Erdos547.exists_fine_separator
