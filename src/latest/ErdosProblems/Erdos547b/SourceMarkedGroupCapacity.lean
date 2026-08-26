/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePrivatePairGeometry

/-!
# Total-source-load allocation for private marked groups

At each step any good group with enough room may be used. The source
schedule leaves a uniform gap between total selected mass and the capacity
of the good groups, even when the exceptional groups change with the root.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGroupCapacity

open Finset SimpleGraph
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoSourceMarkedTripleEmbedding

def capacity (α : ℚ) (N : ℕ) : ℝ := 3 * (1 - 2 * (eta α : ℝ) - 4 * (gamma α : ℝ)) * N

theorem parameter_bounds {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 ≤ (eta α : ℝ) ∧ 0 ≤ (gamma α : ℝ) ∧
      6 * (eta α : ℝ) + 12 * (gamma α : ℝ) + (epsilon α : ℝ) / 2 ≤ 1 / 4 ∧
      (epsilon α : ℝ) ≤ 1 / 64 := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have he : eta α ≤ 1 / 1000000 := by linarith only [hu.2.2.1, hu.2.1, hu.1]
  have hd : degreeError α ≤ eta α / 1000 := by
    exact_mod_cast (Erdos547b.ZhaoSourceNearFullNumerics.parameter_bounds hα hα1).2.2.1
  have hg : gamma α ≤ eta α / 1000 := by
    linarith only [hu.2.2.2.2.2.1, hd, hp.2.2.1]
  have hep : epsilon α ≤ eta α / 1000 := by
    linarith only [hu.2.2.2.2.2.2, hg, hp.2.2.1]
  have heScaled : (1000000 : ℚ) * eta α ≤ 1 := by linarith only [he]
  have heR : (1000000 : ℝ) * (eta α : ℝ) ≤ 1 := by exact_mod_cast heScaled
  have hgR : (gamma α : ℝ) ≤ (eta α : ℝ) / 1000 := by exact_mod_cast hg
  have hepR : (epsilon α : ℝ) ≤ (eta α : ℝ) / 1000 := by exact_mod_cast hep
  refine ⟨by exact_mod_cast hp.2.2.1.le, by exact_mod_cast hp.2.2.2.2.2.2.1.le, ?_, ?_⟩ <;>
    linarith only [heR, hgR, hepR]

theorem capacity_margins {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (N : ℕ) :
    (11 / 4 : ℝ) * N ≤ capacity α N - freshBranchBound α N ∧
      capacity α N ≤ 3 * N := by
  have hp := parameter_bounds hα hα1
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hm : (freshBranchBound α N : ℝ) ≤ (epsilon α : ℝ) * N / 2 :=
    Nat.floor_le (by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hp.2.2.1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have heN := mul_nonneg hp.1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hgN := mul_nonneg hp.2.1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  unfold capacity
  constructor <;> nlinarith only [hm, hscaled, heN, hgN]

theorem occupied_bounds {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (N mass marks occupiedC occupiedPairs : ℕ)
    (hmass : (mass : ℝ) ≤ capacity α N)
    (hmarks : (marks : ℝ) ≤ (epsilon α : ℝ) * N)
    (hC : 3 * occupiedC ≤ mass + 3 * marks)
    (hPairs : occupiedPairs ≤ mass) :
    (occupiedC : ℝ) ≤ (1 - 2 * (eta α : ℝ) - 3 * (gamma α : ℝ)) * N ∧
      occupiedPairs ≤ 3 * N := by
  have hCR : 3 * (occupiedC : ℝ) ≤ mass + 3 * (marks : ℝ) := by exact_mod_cast hC
  have he := (parameter_margin hα hα1 N).1.le
  have heN := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  constructor
  · unfold capacity at hmass
    nlinarith only [hmass, hmarks, hCR, heN]
  · have hm : (mass : ℝ) ≤ 3 * N := hmass.trans (capacity_margins hα hα1 N).2
    have hmNat : mass ≤ 3 * N := by exact_mod_cast hm
    exact hPairs.trans hmNat

theorem exists_good_group_with_room {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {I : Type*} [Fintype I] [DecidableEq I] (hI : 0 < Fintype.card I)
    (N : ℕ) (hN : 0 < N) (load : I → ℕ) (bad : Finset I)
    (hbad : 16 * bad.card ≤ Fintype.card I)
    (htotal : (∑ i, (load i : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * Fintype.card I * N) :
    ∃ i : I, i ∉ bad ∧ (load i : ℝ) + freshBranchBound α N ≤ capacity α N := by
  let good : Finset I := Finset.univ \ bad
  have hcount : 15 * Fintype.card I ≤ 16 * good.card := by
    have hsplit := Finset.card_sdiff_add_card_inter (Finset.univ : Finset I) bad
    simp only [Finset.univ_inter, Finset.card_univ] at hsplit
    change good.card + bad.card = Fintype.card I at hsplit
    omega
  have hgood : good.Nonempty := Finset.card_pos.mp (by omega)
  by_contra! hn
  have hstrict : (good.card : ℝ) * ((11 / 4 : ℝ) * N) < ∑ i ∈ good, (load i : ℝ) := by
    have h := Finset.sum_lt_sum_of_nonempty hgood (fun i hi =>
      lt_of_le_of_lt (capacity_margins hα hα1 N).1
        (show capacity α N - freshBranchBound α N < (load i : ℝ) by
          have hiBad : i ∉ bad := (Finset.mem_sdiff.mp hi).2
          linarith only [hn i hiBad]))
    simpa only [Finset.sum_const, nsmul_eq_mul] using h
  have hsum : (∑ i ∈ good, (load i : ℝ)) ≤ ∑ i, (load i : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good) (by intros; positivity)
  have hcountR : (15 : ℝ) * Fintype.card I ≤ 16 * (good.card : ℝ) := by exact_mod_cast hcount
  have hcountN := mul_le_mul_of_nonneg_right hcountR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hε := (parameter_bounds hα hα1).2.2.2
  have hεScaled := mul_le_mul_of_nonneg_right hε
    (show (0 : ℝ) ≤ Fintype.card I * N by positivity)
  have hpos : (0 : ℝ) < Fintype.card I * N := by positivity
  nlinarith only [hstrict, hsum, htotal, hcountN, hεScaled, hpos]

end Erdos547b.ZhaoSourceMarkedGroupCapacity

#print axioms Erdos547b.ZhaoSourceMarkedGroupCapacity.capacity_margins
#print axioms Erdos547b.ZhaoSourceMarkedGroupCapacity.occupied_bounds
#print axioms Erdos547b.ZhaoSourceMarkedGroupCapacity.exists_good_group_with_room
