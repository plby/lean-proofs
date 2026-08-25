import StackExchange.Puzzling139335.ReflectionSeparation.Generic
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Reflection separation for the square

These are consequences of the actual Jordan-region and congruence hypotheses.
In particular, a corner selecting one side of a reflection does not need to
be an unsplit corner.
-/

open Set

namespace Puzzling139335.ReflectionSeparation

private theorem coordinate_continuous (i : Fin 2) : Continuous (fun p : Plane => p i) :=
  (EuclideanSpace.proj i).continuous

theorem horizontal_side {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : horizontal '' P = Q) (hdis : Disjoint (interior P) (interior Q)) :
    P ⊆ {p | p 1 ≤ (1 / 2 : ℝ)} ∨ P ⊆ {p | (1 / 2 : ℝ) ≤ p 1} :=
  subset_le_or_ge_of_fixed_level hP horizontal he hdis (fun p => p 1)
    (coordinate_continuous 1) (1 / 2) (fun _ h => horizontal_fixed h)

theorem horizontal_below_of_mem {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : horizontal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    {p : Plane} (hp : p ∈ P) (hbelow : p 1 < (1 / 2 : ℝ)) :
    P ⊆ {q | q 1 ≤ (1 / 2 : ℝ)} :=
  subset_le_of_fixed_level_of_mem_lt hP horizontal he hdis (fun p => p 1)
    (coordinate_continuous 1) (1 / 2) (fun _ h => horizontal_fixed h) hp hbelow

theorem horizontal_above_of_mem {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : horizontal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    {p : Plane} (hp : p ∈ P) (habove : (1 / 2 : ℝ) < p 1) :
    P ⊆ {q | (1 / 2 : ℝ) ≤ q 1} :=
  subset_ge_of_fixed_level_of_mem_gt hP horizontal he hdis (fun p => p 1)
    (coordinate_continuous 1) (1 / 2) (fun _ h => horizontal_fixed h) hp habove

theorem horizontal_below_of_bottom_left {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : horizontal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    (hcorner : corner 0 ∈ P) : P ⊆ {p | p 1 ≤ (1 / 2 : ℝ)} :=
  horizontal_below_of_mem hP he hdis hcorner (by norm_num [corner, Fin.ext_iff])

theorem horizontal_below_of_bottom_right {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : horizontal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    (hcorner : corner 1 ∈ P) : P ⊆ {p | p 1 ≤ (1 / 2 : ℝ)} :=
  horizontal_below_of_mem hP he hdis hcorner (by norm_num [corner, Fin.ext_iff])

/-- A reflected pair containing a bottom corner occupies opposite half-planes. -/
theorem horizontal_halves_of_bottom_left {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : horizontal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    (hcorner : corner 0 ∈ P) :
    P ⊆ {p | p 1 ≤ (1 / 2 : ℝ)} ∧ Q ⊆ {p | (1 / 2 : ℝ) ≤ p 1} := by
  have hbelow := horizontal_below_of_bottom_left hP he hdis hcorner
  refine ⟨hbelow, ?_⟩
  intro q hq
  rw [← he] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  change (1 / 2 : ℝ) ≤ horizontal p 1
  rw [horizontal_apply_one]
  have h := hbelow hp
  change p 1 ≤ (1 / 2 : ℝ) at h
  linarith

theorem vertical_side {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : vertical '' P = Q) (hdis : Disjoint (interior P) (interior Q)) :
    P ⊆ {p | p 0 ≤ (1 / 2 : ℝ)} ∨ P ⊆ {p | (1 / 2 : ℝ) ≤ p 0} :=
  subset_le_or_ge_of_fixed_level hP vertical he hdis (fun p => p 0)
    (coordinate_continuous 0) (1 / 2) (fun _ h => vertical_fixed h)

theorem vertical_left_of_mem {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : vertical '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    {p : Plane} (hp : p ∈ P) (hleft : p 0 < (1 / 2 : ℝ)) :
    P ⊆ {q | q 0 ≤ (1 / 2 : ℝ)} :=
  subset_le_of_fixed_level_of_mem_lt hP vertical he hdis (fun p => p 0)
    (coordinate_continuous 0) (1 / 2) (fun _ h => vertical_fixed h) hp hleft

theorem vertical_left_of_bottom_left {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : vertical '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    (hcorner : corner 0 ∈ P) : P ⊆ {p | p 0 ≤ (1 / 2 : ℝ)} :=
  vertical_left_of_mem hP he hdis hcorner (by norm_num [corner, Fin.ext_iff])

theorem diagonal_side {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : diagonal '' P = Q) (hdis : Disjoint (interior P) (interior Q)) :
    P ⊆ {p | p 0 ≤ p 1} ∨ P ⊆ {p | p 1 ≤ p 0} := by
  have h := subset_le_or_ge_of_fixed_level hP diagonal he hdis
    (fun p => p 0 - p 1) ((coordinate_continuous 0).sub (coordinate_continuous 1))
    0 (fun _ h => diagonal_fixed (sub_eq_zero.mp h))
  simpa only [sub_nonpos, sub_nonneg] using h

theorem diagonal_below_of_mem {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : diagonal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    {p : Plane} (hp : p ∈ P) (hbelow : p 1 < p 0) : P ⊆ {q | q 1 ≤ q 0} := by
  have h := subset_ge_of_fixed_level_of_mem_gt hP diagonal he hdis
    (fun p => p 0 - p 1) ((coordinate_continuous 0).sub (coordinate_continuous 1))
    0 (fun _ h => diagonal_fixed (sub_eq_zero.mp h)) hp (sub_pos.mpr hbelow)
  simpa only [sub_nonneg] using h

theorem diagonal_below_of_bottom_right {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : diagonal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    (hcorner : corner 1 ∈ P) : P ⊆ {p | p 1 ≤ p 0} :=
  diagonal_below_of_mem hP he hdis hcorner (by norm_num [corner, Fin.ext_iff])

theorem antiDiagonal_side {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : antiDiagonal '' P = Q) (hdis : Disjoint (interior P) (interior Q)) :
    P ⊆ {p | p 0 + p 1 ≤ 1} ∨ P ⊆ {p | 1 ≤ p 0 + p 1} :=
  subset_le_or_ge_of_fixed_level hP antiDiagonal he hdis (fun p => p 0 + p 1)
    ((coordinate_continuous 0).add (coordinate_continuous 1)) 1
    (fun _ h => antiDiagonal_fixed h)

theorem antiDiagonal_below_of_mem {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : antiDiagonal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    {p : Plane} (hp : p ∈ P) (hbelow : p 0 + p 1 < 1) :
    P ⊆ {q | q 0 + q 1 ≤ 1} :=
  subset_le_of_fixed_level_of_mem_lt hP antiDiagonal he hdis (fun p => p 0 + p 1)
    ((coordinate_continuous 0).add (coordinate_continuous 1)) 1
    (fun _ h => antiDiagonal_fixed h) hp hbelow

theorem antiDiagonal_below_of_bottom_left {P Q : Set Plane} (hP : IsJordanRegion P)
    (he : antiDiagonal '' P = Q) (hdis : Disjoint (interior P) (interior Q))
    (hcorner : corner 0 ∈ P) : P ⊆ {p | p 0 + p 1 ≤ 1} :=
  antiDiagonal_below_of_mem hP he hdis hcorner (by norm_num [corner, Fin.ext_iff])

end Puzzling139335.ReflectionSeparation

namespace Puzzling139335

theorem SquareDissection.horizontal_pair_halves_of_bottom_left (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (he : ReflectionSeparation.horizontal '' d.piece i = d.piece j)
    (hcorner : corner 0 ∈ d.piece i) :
    d.piece i ⊆ {p | p 1 ≤ (1 / 2 : ℝ)} ∧
      d.piece j ⊆ {p | (1 / 2 : ℝ) ≤ p 1} :=
  ReflectionSeparation.horizontal_halves_of_bottom_left (d.jordan i) he
    (d.disjoint_interiors hij) hcorner

end Puzzling139335
