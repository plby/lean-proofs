import StackExchange.Puzzling139335.N5.TypeReduction
import StackExchange.Puzzling139335.Transform

/-!
# Physical incidence counts under a common square symmetry

The counts transported here are physical corner memberships.  No
invariance of independently chosen intrinsic placements is assumed.
-/

open Set

namespace Puzzling139335.N5

theorem tileCornerCount_map (d : SquareDissection) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) (i : Fin 4) :
    (d.map e he).tileCornerCount i = d.tileCornerCount i := by
  classical
  let σ := SquareSymmetry.cornerPermutation e he.subset
  have hσ (a : Fin 4) : e (corner a) = corner (σ a) :=
    SquareSymmetry.cornerPermutation_apply e he.subset a
  have hmem (a : Fin 4) :
      corner a ∈ d.piece i ↔ corner (σ a) ∈ (d.map e he).piece i := by
    change corner a ∈ d.piece i ↔ corner (σ a) ∈ e '' d.piece i
    rw [← hσ]
    constructor
    · exact mem_image_of_mem e
    · rintro ⟨p, hp, hpa⟩
      exact e.injective hpa ▸ hp
  symm
  change (Finset.univ.filter fun a => corner a ∈ d.piece i).card =
    (Finset.univ.filter fun a => corner a ∈ (d.map e he).piece i).card
  apply Finset.card_bij (fun a _ => σ a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (hmem a).mp ha
  · intro a _ b _ hab
    exact σ.injective hab
  · intro b hb
    refine ⟨σ.symm b, ?_, σ.apply_symm_apply b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact (hmem (σ.symm b)).mpr (by simpa using hb)

theorem cornerIncidenceCount_map (d : SquareDissection) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) :
    (d.map e he).cornerIncidenceCount = d.cornerIncidenceCount := by
  rw [SquareDissection.cornerIncidenceCount_eq_sum_tileCornerCount,
    SquareDissection.cornerIncidenceCount_eq_sum_tileCornerCount]
  exact Finset.sum_congr rfl (fun i _ => tileCornerCount_map d e he i)

theorem split_corner_eq_of_two_owners (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) {s a p q : Fin 4}
    (hs : d.cornerTileCount s = 2) (hpq : p ≠ q)
    (hp : corner a ∈ d.piece p) (hq : corner a ∈ d.piece q) : a = s := by
  by_contra has
  have hone := count_one_of_ne_split d hN hs has
  exact unique_corner_of_count_one d hone hp q hpq.symm hq

theorem count_two_of_two_owners (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) {a p q : Fin 4}
    (hpq : p ≠ q) (hp : corner a ∈ d.piece p) (hq : corner a ∈ d.piece q) :
    d.cornerTileCount a = 2 := by
  obtain ⟨s, hs, _⟩ := exists_split_corner d hN
  rw [split_corner_eq_of_two_owners d hN hs hpq hp hq]
  exact hs

end Puzzling139335.N5
