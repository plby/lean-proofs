import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.N5.AllCornered
import StackExchange.Puzzling139335.DoubleCorner

/-!
# From five actual incidences to the normalized diagonal configuration

The support and center exclusions at the shared corner are proved by the
two-piece Jordan-corner theorem.  They are not assumptions of the final
reduction.  The resulting dissection is obtained by a common square
symmetry and a permutation of the original four pieces.
-/

open Set

namespace Puzzling139335.N5

theorem exists_double_pair_indices_of_split_support (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s : Fin 4} {A : Plane}
    (hs : d.cornerTileCount s = 2) (hA : A ∈ splitCornerTypes d)
    (h45 : AcuteCorner.Supports45 (d.piece 0) A)
    (hcenter : ∀ i, corner s ∈ d.piece i →
      squareCenter ∉ interior (d.piece i)) :
    ∃ σ : Equiv.Perm (Fin 4),
      d.tileCornerCount (σ 0) = 2 ∧ d.tileCornerCount (σ 1) = 2 ∧
      d.tileCornerCount (σ 2) = 1 ∧ d.tileCornerCount (σ 3) = 0 ∧
      corner s ∈ d.piece (σ 0) ∧ corner s ∈ d.piece (σ 1) := by
  obtain ⟨z, hz⟩ := exists_cornerless_of_split_support d hc hN htypes hs hA h45 hcenter
  obtain ⟨σ, h | h⟩ := tile_count_patterns d hc hN
  · rcases h with ⟨h₀, h₁, h₂, h₃⟩
    obtain ⟨j, rfl⟩ := σ.surjective z
    exfalso
    fin_cases j
    · exact (by decide : (2 : ℕ) ≠ 0) (h₀.symm.trans hz)
    · exact (by decide : (1 : ℕ) ≠ 0) (h₁.symm.trans hz)
    · exact (by decide : (1 : ℕ) ≠ 0) (h₂.symm.trans hz)
    · exact (by decide : (1 : ℕ) ≠ 0) (h₃.symm.trans hz)
  · exact ⟨σ, h.1, h.2.1, h.2.2.1, h.2.2.2,
      double_contains_split_of_support45 d hc hN hs hA h45 (σ 0) h.1,
      double_contains_split_of_support45 d hc hN hs hA h45 (σ 1) h.2.1⟩

theorem exists_normalized_of_split_support (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s : Fin 4} {A : Plane}
    (hs : d.cornerTileCount s = 2) (hA : A ∈ splitCornerTypes d)
    (h45 : AcuteCorner.Supports45 (d.piece 0) A)
    (hcenter : ∀ i, corner s ∈ d.piece i →
      squareCenter ∉ interior (d.piece i)) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ Normalized d' := by
  obtain ⟨σ, hp, hq, hr, hz, hsp, hsq⟩ :=
    exists_double_pair_indices_of_split_support d hc hN htypes hs hA h45 hcenter
  have hpq : σ 0 ≠ σ 1 := σ.injective.ne (by decide : (0 : Fin 4) ≠ 1)
  obtain ⟨f, hfS, hBL, hBR, hPQ, hTR⟩ :=
    exists_normalized_double_pair d hc hN htypes hs hpq hp hq hr hsp hsq
  let E := d.map f hfS
  let D := E.reindex σ
  have hE : E.HasProtectedCenter := (d.map_hasProtectedCenter f hfS).mpr hc
  have hD : D.HasProtectedCenter := (E.reindex_hasProtectedCenter σ).mpr hE
  refine ⟨D, hD, ?_⟩
  constructor
  · change (d.map f hfS).tileCornerCount (σ 0) = 2
    rw [tileCornerCount_map]
    exact hp
  · change (d.map f hfS).tileCornerCount (σ 1) = 2
    rw [tileCornerCount_map]
    exact hq
  · change (d.map f hfS).tileCornerCount (σ 2) = 1
    rw [tileCornerCount_map]
    exact hr
  · change (d.map f hfS).tileCornerCount (σ 3) = 0
    rw [tileCornerCount_map]
    exact hz
  · exact hBL
  · exact hBR
  · exact hPQ
  · exact hTR

/-- The actual five-incidence reduction.  All forty-five-degree supports
and split-corner center exclusions are discharged inside the proof. -/
theorem exists_normalized_of_five (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) :
    ∃ d' : SquareDissection, d'.HasProtectedCenter ∧ Normalized d' := by
  obtain ⟨s, hs, _⟩ := exists_split_corner d hN
  obtain ⟨i, k, hik, howners⟩ := split_corner_owners d s hs
  have hi : corner s ∈ d.piece i := (howners i).mpr (Or.inl rfl)
  have hk : corner s ∈ d.piece k := (howners k).mpr (Or.inr rfl)
  have hother : ∀ l, l ≠ i → l ≠ k → corner s ∉ d.piece l := by
    intro l hli hlk hl
    rcases (howners l).mp hl with h | h
    · exact hli h
    · exact hlk h
  have htype := intrinsicCorners_eq_at_split d hc hN htypes hs hi hk
  have h45 := d.same_intrinsic_double_corner_prototype_support hik hi hk hother htype
  have hpair := d.same_intrinsic_double_corner hik hi hk hother htype
  have hcenter : ∀ l, corner s ∈ d.piece l →
      squareCenter ∉ interior (d.piece l) := by
    intro l hl
    rcases (howners l).mp hl with rfl | rfl
    · exact hpair.2.2.1
    · exact hpair.2.2.2
  have hA : d.intrinsicCorner i s ∈ splitCornerTypes d :=
    (mem_splitCornerTypes d).mpr ⟨i, s, hi, by omega, rfl⟩
  exact exists_normalized_of_split_support d hc hN htypes hs hA h45 hcenter

end Puzzling139335.N5
