import StackExchange.Puzzling139335.N6.TripleIncidence
import StackExchange.Puzzling139335.N6.TripleEqualParity
import StackExchange.Puzzling139335.N6.TripleOppositeParity
import StackExchange.Puzzling139335.SymmetryOrbit

/-!
# Discharging the opposite-parity normalization hypotheses

The remaining piece is recovered from the actual cover. Its corner
preimage is a full corner because the opposite square corner is uniquely
owned. Repeating the source's full corner there would give three actual
square-symmetry copies, which is already impossible.
-/

open Set

namespace Puzzling139335.N6

open TripleSectors
open ReflectionSeparation (diagonal)

noncomputable section

theorem supports45_of_subset_thirtyCone {P : Set Plane} (hP : P ⊆ thirtyCone) :
    AcuteCorner.Supports45 P 0 := by
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, rfl, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have h := hP hp
  change 0 ≤ p 1 ∧ p 1 ≤ p 0
  refine ⟨h.1, ?_⟩
  have hm := mul_le_mul_of_nonneg_right one_lt_sqrt_three.le h.1
  linarith only [hm, h.2.1]

private theorem origin_mem_middle {P M : Set Plane} (h0 : (0 : Plane) ∈ P)
    (hM : M = rotateThirty '' P ∨ M = reflectThirty '' P) : (0 : Plane) ∈ M := by
  rcases hM with rfl | rfl
  · have hfix : rotateThirty 0 = (0 : Plane) := by
      apply point_ext <;> simp
    exact hfix ▸ mem_image_of_mem rotateThirty h0
  · have hfix : reflectThirty 0 = (0 : Plane) := by
      apply point_ext <;> simp
    exact hfix ▸ mem_image_of_mem reflectThirty h0

private theorem origin_mem_diagonal {P : Set Plane} (h0 : (0 : Plane) ∈ P) :
    (0 : Plane) ∈ diagonal '' P := by
  have hfix : diagonal 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> simp
  exact hfix ▸ mem_image_of_mem diagonal h0

/-- The first three normalized placements are precisely the three owners
of the origin; the fourth piece misses it. -/
theorem normalized_origin_owners (d : SquareDissection) (hc : d.HasProtectedCenter)
    (h0 : (0 : Plane) ∈ d.piece 0)
    (hM : d.piece 1 = rotateThirty '' d.piece 0 ∨
      d.piece 1 = reflectThirty '' d.piece 0)
    (hQ : d.piece 2 = diagonal '' d.piece 0) :
    d.cornerTileCount 0 = 3 ∧ corner 0 ∉ d.piece 3 := by
  classical
  have hcorner0 : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> rfl
  have hi0 : corner 0 ∈ d.piece 0 := by simpa only [hcorner0] using h0
  have hi1 : corner 0 ∈ d.piece 1 := by
    simpa only [hcorner0] using origin_mem_middle h0 hM
  have hi2 : corner 0 ∈ d.piece 2 := by
    rw [hQ]
    simpa only [hcorner0] using origin_mem_diagonal h0
  have hi3 : corner 0 ∉ d.piece 3 := by
    intro h
    apply d.not_all_contain_corner hc 0
    intro i
    fin_cases i
    · exact hi0
    · exact hi1
    · exact hi2
    · exact h
  have heq : (Finset.univ.filter fun i => corner 0 ∈ d.piece i) =
      ({0, 1, 2} : Finset (Fin 4)) := by
    ext i
    fin_cases i <;> simp [hi0, hi1, hi2, hi3]
  refine ⟨?_, hi3⟩
  change (Finset.univ.filter fun i => corner 0 ∈ d.piece i).card = 3
  rw [heq]
  decide

private theorem corner_one_not_mem_reflected_middle {P : Set Plane}
    (hP : P ⊆ thirtyCone) : corner 1 ∉ reflectThirty '' P := by
  rintro ⟨p, hp, heq⟩
  have h := hP hp
  have hfirst := congrArg (fun z : Plane => z 0) heq
  have hsecond := congrArg (fun z : Plane => z 1) heq
  simp only [reflectThirty_zero, reflectThirty_one] at hfirst hsecond
  norm_num [corner, Fin.ext_iff] at hfirst hsecond
  have hy : p 1 = Real.sqrt 3 * p 0 := by linarith only [hsecond]
  have hprod : Real.sqrt 3 * p 1 = 3 * p 0 := by
    rw [hy]
    calc
      _ = Real.sqrt 3 ^ 2 * p 0 := by ring
      _ = _ := by rw [sqrt_three_sq]
  have hx0 : p 0 = 0 := by
    have hxnonneg := thirtyCone_first_nonneg h
    have hcone := h.2.1
    rw [hprod] at hcone
    linarith only [hcone, hxnonneg]
  rw [hx0] at hy hfirst
  simp only [mul_zero] at hy
  rw [hy] at hfirst
  norm_num at hfirst

/-- In the opposite-parity normalization the source must own the lower
right corner; the middle and reflected copies cannot reach that corner. -/
theorem normalized_source_corner_one (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (h0 : (0 : Plane) ∈ d.piece 0) (hP : d.piece 0 ⊆ thirtyCone)
    (hM : d.piece 1 = rotateThirty '' d.piece 0 ∨
      d.piece 1 = reflectThirty '' d.piece 0)
    (hQ : d.piece 2 = diagonal '' d.piece 0) : corner 1 ∈ d.piece 0 := by
  obtain ⟨hs, hnot⟩ := normalized_origin_owners d hc h0 hM hQ
  have hD : corner 1 ∉ d.piece 3 := by
    intro h
    have hindex := (nonowner_corner_iff d hc hN hs hnot h0
      (supports45_of_subset_thirtyCone hP) 1).mp h
    exact (by decide : (1 : Fin 4) ≠ 2) hindex
  have hMid : corner 1 ∉ d.piece 1 := by
    rcases hM with hM | hM
    · rw [hM]
      rintro ⟨p, hp, heq⟩
      have hlt := rotateThirty_first_lt_one (hP hp)
      rw [heq] at hlt
      norm_num [corner, Fin.ext_iff] at hlt
    · rw [hM]
      exact corner_one_not_mem_reflected_middle hP
  have hLast : corner 1 ∉ d.piece 2 := by
    rw [hQ]
    rintro ⟨p, hp, heq⟩
    have hfirst := congrArg (fun z : Plane => z 0) heq
    have hsecond := congrArg (fun z : Plane => z 1) heq
    simp only [ReflectionSeparation.diagonal_apply_zero,
      ReflectionSeparation.diagonal_apply_one] at hfirst hsecond
    norm_num [corner, Fin.ext_iff] at hfirst hsecond
    have hbound := (hP hp).2.1
    rw [hfirst, hsecond] at hbound
    exact (not_le_of_gt sqrt_three_pos) (by simpa using hbound)
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare 1)
  fin_cases i
  · exact hi
  · exact (hMid hi).elim
  · exact (hLast hi).elim
  · exact (hD hi).elim

/-- The preimage of the opposite square corner is a full corner of the
source, and is distinct from its lower-right full corner. -/
theorem normalized_opposite_full_corner (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (h0 : (0 : Plane) ∈ d.piece 0) (hP : d.piece 0 ⊆ thirtyCone)
    (hM : d.piece 1 = rotateThirty '' d.piece 0 ∨
      d.piece 1 = reflectThirty '' d.piece 0)
    (hQ : d.piece 2 = diagonal '' d.piece 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 3) :
    UnitPairs.IsFullSquareCorner (d.piece 0) (e.symm (corner 2)) ∧
      e.symm (corner 2) ≠ corner 1 := by
  obtain ⟨hs, hnot⟩ := normalized_origin_owners d hc h0 hM hQ
  have hB := normalized_source_corner_one d hc hN h0 hP hM hQ
  have hC : corner 2 ∈ d.piece 3 := by
    simpa only [Fin.reduceAdd] using opposite_mem_of_triple_not_mem d hc hs hnot
  have hcountB : d.cornerTileCount 1 = 1 :=
    unique_away_from_triple d hN hs (by decide)
  have hcountC : d.cornerTileCount 2 = 1 :=
    unique_away_from_triple d hN hs (by decide)
  have huniqueB := N5.unique_corner_of_count_one d hcountB hB
  have huniqueC := N5.unique_corner_of_count_one d hcountC hC
  constructor
  · obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood 3 huniqueC
    refine ⟨e, 2, ε, hε, ?_, e.apply_symm_apply _, ?_⟩
    · rw [he]
      exact d.piece_subset 3
    · rwa [he]
  · intro heq
    have heB : e (corner 1) = corner 2 := by
      rw [← heq, e.apply_symm_apply]
    have heS := d.unique_corner_congruence_preserves_square 0 3 1 2 e he heB huniqueB
    exact d.not_hasProtectedCenter_of_three_square_symmetry_copies
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3) diagonal e
      ReflectionSeparation.diagonal_image_unitSquare.subset heS.subset hQ.symm he hc

/-- Both possible middle parities are impossible after the three actual
corner pieces have been normalized. Every full-corner hypothesis of the
geometric obstruction is derived here from the dissection. -/
theorem normalized_opposite_parity_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (h0 : (0 : Plane) ∈ d.piece 0) (hP : d.piece 0 ⊆ thirtyCone)
    (hM : d.piece 1 = rotateThirty '' d.piece 0 ∨
      d.piece 1 = reflectThirty '' d.piece 0)
    (hQ : d.piece 2 = diagonal '' d.piece 0) : False := by
  obtain ⟨e, he⟩ := d.congruent 0 3
  obtain ⟨hC, hCB⟩ := normalized_opposite_full_corner d hc hN h0 hP hM hQ e he
  have hB := normalized_source_corner_one d hc hN h0 hP hM hQ
  have heS : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 3
  have hdisP : Disjoint (interior (d.piece 0)) (interior (e '' d.piece 0)) := by
    rw [he]
    exact d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 3)
  have hdisQ : Disjoint (interior (diagonal '' d.piece 0))
      (interior (e '' d.piece 0)) := by
    rw [← hQ, he]
    exact d.disjoint_interiors (by decide : (2 : Fin 4) ≠ 3)
  have hcover : unitSquare ⊆ d.piece 0 ∪ d.piece 1 ∪ diagonal '' d.piece 0 ∪
      e '' d.piece 0 := by
    rw [← hQ, he]
    intro x hx
    obtain ⟨i, hi⟩ := d.exists_piece_mem hx
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl hi))
    · exact Or.inl (Or.inl (Or.inr hi))
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  exact TripleOppositeParity.normalized_middle_parity_impossible
    (d.jordan 0) hP h0 hB hM e heS hC (e.apply_symm_apply _) hCB hdisP hdisQ hcover

end

end Puzzling139335.N6
