import ErdosProblems.Erdos633b.SmallPrimitivePhases
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions1
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions2
import ErdosProblems.Erdos633b.GroupTwoResidueExclusions3

/-! Exact remaining phase lists for the first three group-2 shapes.
All omitted phases are discharged by proved degree or residue obstructions. -/

namespace Erdos633b

def groupTwoPhasePairs1 : Finset (ℕ × ℕ) :=
  {(8, 1), (10, 1), (12, 1), (15, 2), (18, 1), (20, 1), (20, 3), (30, 1)}

def groupTwoPhasePairs2 : Finset (ℕ × ℕ) :=
  {(9, 1), (12, 1), (15, 2), (16, 1), (18, 1), (24, 1), (30, 1)}

def groupTwoPhasePairs3 : Finset (ℕ × ℕ) :=
  {(8, 1), (12, 1), (20, 1), (20, 3)}

namespace Tiling

theorem groupTwo_first_phase_cases {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 3 * d.tile.angle 1) :
    ∃ D j : ℕ, (D, j) ∈ groupTwoPhasePairs1 ∧
      d.tile.angle 0 = 2 * Real.pi * j / D := by
  have hs : GroupTwoShape d.tile T := ⟨hg, Or.inl ⟨h0, h1, h2⟩⟩
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_primitive_phase_cases hrat hs
  simp only [smallPrimitivePhases, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim (d.groupTwo_residue_exclusion_7_1_1 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨8, 1, by decide, ha⟩
  · exact False.elim (d.groupTwo_residue_exclusion_9_1_1 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨10, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 11 := by
      rw [ha]
      exact primitive_cosine_root 11 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 11 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 11 ≤ 8) hb)
  · exact ⟨12, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 13 := by
      rw [ha]
      exact primitive_cosine_root 13 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 13 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 13 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 13 := by
      rw [ha]
      exact primitive_cosine_root 13 2 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 13 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 13 ≤ 8) hb)
  · exact False.elim (d.groupTwo_residue_exclusion_14_1_1 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_15_1_1 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨15, 2, by decide, ha⟩
  · exact False.elim (d.groupTwo_residue_exclusion_16_1_1 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨18, 1, by decide, ha⟩
  · exact ⟨20, 1, by decide, ha⟩
  · exact ⟨20, 3, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 21 := by
      rw [ha]
      exact primitive_cosine_root 21 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 21 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 21 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 21 := by
      rw [ha]
      exact primitive_cosine_root 21 2 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 21 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 21 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 22 := by
      rw [ha]
      exact primitive_cosine_root 22 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 22 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 22 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 22 := by
      rw [ha]
      exact primitive_cosine_root 22 3 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 22 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 22 ≤ 8) hb)
  · exact False.elim (d.groupTwo_residue_exclusion_24_1_1 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 26 := by
      rw [ha]
      exact primitive_cosine_root 26 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 26 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 26 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 26 := by
      rw [ha]
      exact primitive_cosine_root 26 3 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 26 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 26 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 28 := by
      rw [ha]
      exact primitive_cosine_root 28 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 28 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 28 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 28 := by
      rw [ha]
      exact primitive_cosine_root 28 3 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 28 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 28 ≤ 8) hb)
  · exact ⟨30, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 36 := by
      rw [ha]
      exact primitive_cosine_root 36 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 36 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 36 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 36 := by
      rw [ha]
      exact primitive_cosine_root 36 5 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 36 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 36 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 42 := by
      rw [ha]
      exact primitive_cosine_root 42 1 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 42 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 42 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 42 := by
      rw [ha]
      exact primitive_cosine_root 42 5 (by decide) (by decide)
    have hb := d.groupTwo_first_totient_bound hg h0 h1 h2 42 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 42 ≤ 8) hb)

theorem groupTwo_second_phase_cases {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = 2 * d.tile.angle 1)
    (h2 : T.angle 2 = 2 * d.tile.angle 0 + d.tile.angle 1) :
    ∃ D j : ℕ, (D, j) ∈ groupTwoPhasePairs2 ∧
      d.tile.angle 0 = 2 * Real.pi * j / D := by
  have hs : GroupTwoShape d.tile T := ⟨hg, Or.inr (Or.inl ⟨h0, h1, h2⟩)⟩
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_primitive_phase_cases hrat hs
  simp only [smallPrimitivePhases, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim (d.groupTwo_residue_exclusion_7_1_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_8_1_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨9, 1, by decide, ha⟩
  · exact False.elim (d.groupTwo_residue_exclusion_10_1_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 11 := by
      rw [ha]
      exact primitive_cosine_root 11 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 11 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 11 ≤ 8) hb)
  · exact ⟨12, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 13 := by
      rw [ha]
      exact primitive_cosine_root 13 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 13 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 13 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 13 := by
      rw [ha]
      exact primitive_cosine_root 13 2 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 13 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 13 ≤ 8) hb)
  · exact False.elim (d.groupTwo_residue_exclusion_14_1_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_15_1_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨15, 2, by decide, ha⟩
  · exact ⟨16, 1, by decide, ha⟩
  · exact ⟨18, 1, by decide, ha⟩
  · exact False.elim (d.groupTwo_residue_exclusion_20_1_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_20_3_2 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 21 := by
      rw [ha]
      exact primitive_cosine_root 21 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 21 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 21 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 21 := by
      rw [ha]
      exact primitive_cosine_root 21 2 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 21 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 21 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 22 := by
      rw [ha]
      exact primitive_cosine_root 22 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 22 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 22 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 22 := by
      rw [ha]
      exact primitive_cosine_root 22 3 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 22 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 22 ≤ 8) hb)
  · exact ⟨24, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 26 := by
      rw [ha]
      exact primitive_cosine_root 26 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 26 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 26 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 26 := by
      rw [ha]
      exact primitive_cosine_root 26 3 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 26 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 26 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 28 := by
      rw [ha]
      exact primitive_cosine_root 28 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 28 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 28 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 28 := by
      rw [ha]
      exact primitive_cosine_root 28 3 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 28 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 28 ≤ 8) hb)
  · exact ⟨30, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 36 := by
      rw [ha]
      exact primitive_cosine_root 36 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 36 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 36 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 36 := by
      rw [ha]
      exact primitive_cosine_root 36 5 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 36 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 36 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 42 := by
      rw [ha]
      exact primitive_cosine_root 42 1 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 42 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 42 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 42 := by
      rw [ha]
      exact primitive_cosine_root 42 5 (by decide) (by decide)
    have hb := d.groupTwo_second_totient_bound hg h0 h1 h2 42 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 42 ≤ 8) hb)

theorem groupTwo_third_phase_cases {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (hg : d.tile.angle 2 = 2 * Real.pi / 3)
    (h0 : T.angle 0 = d.tile.angle 0)
    (h1 : T.angle 1 = d.tile.angle 0 + d.tile.angle 1)
    (h2 : T.angle 2 = d.tile.angle 0 + 2 * d.tile.angle 1) :
    ∃ D j : ℕ, (D, j) ∈ groupTwoPhasePairs3 ∧
      d.tile.angle 0 = 2 * Real.pi * j / D := by
  have hs : GroupTwoShape d.tile T := ⟨hg, Or.inr (Or.inr (Or.inl ⟨h0, h1, h2⟩))⟩
  obtain ⟨D, j, hm, ha⟩ := d.groupTwo_primitive_phase_cases hrat hs
  simp only [smallPrimitivePhases, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact False.elim (d.groupTwo_residue_exclusion_7_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨8, 1, by decide, ha⟩
  · exact False.elim (d.groupTwo_residue_exclusion_9_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_10_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 11 := by
      rw [ha]
      exact primitive_cosine_root 11 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 11 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 11 ≤ 8) hb)
  · exact ⟨12, 1, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 13 := by
      rw [ha]
      exact primitive_cosine_root 13 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 13 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 13 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 13 := by
      rw [ha]
      exact primitive_cosine_root 13 2 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 13 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 13 ≤ 8) hb)
  · exact False.elim (d.groupTwo_residue_exclusion_14_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_15_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_15_2_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_16_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact False.elim (d.groupTwo_residue_exclusion_18_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · exact ⟨20, 1, by decide, ha⟩
  · exact ⟨20, 3, by decide, ha⟩
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 21 := by
      rw [ha]
      exact primitive_cosine_root 21 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 21 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 21 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 21 := by
      rw [ha]
      exact primitive_cosine_root 21 2 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 21 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 21 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 22 := by
      rw [ha]
      exact primitive_cosine_root 22 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 22 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 22 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 22 := by
      rw [ha]
      exact primitive_cosine_root 22 3 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 22 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 22 ≤ 8) hb)
  · exact False.elim (d.groupTwo_residue_exclusion_24_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 26 := by
      rw [ha]
      exact primitive_cosine_root 26 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 26 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 26 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 26 := by
      rw [ha]
      exact primitive_cosine_root 26 3 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 26 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 26 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 28 := by
      rw [ha]
      exact primitive_cosine_root 28 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 28 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 28 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 28 := by
      rw [ha]
      exact primitive_cosine_root 28 3 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 28 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 28 ≤ 8) hb)
  · exact False.elim (d.groupTwo_residue_exclusion_30_1_3 hg h0 h1 h2
      (by simpa only [Nat.cast_one, Nat.cast_ofNat] using ha))
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 36 := by
      rw [ha]
      exact primitive_cosine_root 36 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 36 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 36 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 36 := by
      rw [ha]
      exact primitive_cosine_root 36 5 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 36 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 36 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 42 := by
      rw [ha]
      exact primitive_cosine_root 42 1 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 42 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 42 ≤ 8) hb)
  · have hz : IsPrimitiveRoot (Complex.exp ((d.tile.angle 0 : ℂ) * Complex.I)) 42 := by
      rw [ha]
      exact primitive_cosine_root 42 5 (by decide) (by decide)
    have hb := d.groupTwo_third_totient_bound hg h0 h1 h2 42 (by decide) hz
    exact False.elim ((by decide : ¬ Nat.totient 42 ≤ 8) hb)

end Tiling
end Erdos633b
