/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartThreeResidualNumerics

/-!
# Initialization and propagation of the Part-3 residual invariant

The Appendix alternatives are converted from natural cardinalities without
truncated-subtraction errors. Previously embedded vertices and permanently
deleted vertices are both counted as occupied.
-/

noncomputable section

namespace Erdos547b.ZhaoSourcePartThreeResidualNumerics

open Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54AppendixA

theorem ResidualInvariant.of_cleanup (dx dy N error x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxError : x ≤ 3 * error) (hyError : y ≤ 3 * error) :
    ResidualInvariant dx dy N error x y := by
  left
  rw [abs_le]
  constructor <;> linarith only [hx, hy, hxError, hyError]

/-- The real form of the Appendix trichotomy propagates the occupied-side
invariant, while old density-threshold alternatives persist monotonically. -/
theorem ResidualInvariant.advance
    (dx dy N error x y u v P Q rootReserve small : ℝ)
    (_hdx : 0 ≤ dx) (hdxOne : dx ≤ 1) (_hdy : 0 ≤ dy) (hdyOne : dy ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (herror : 0 ≤ error) (hroot : rootReserve ≤ 4 * error) (hsmall : small ≤ 3 * error)
    (hP : dx * (N - x) - 2 * error ≤ P)
    (hQ : dy * (N - y) - 2 * error ≤ Q)
    (hinv : ResidualInvariant dx dy N error x y)
    (htrichotomy :
      |((N - x) - u) - ((N - y) - v)| ≤ max |(N - x) - (N - y)| small ∨
        (P ≤ u + rootReserve ∧ P ≤ v + rootReserve) ∨
        (Q ≤ u + rootReserve ∧ Q ≤ v + rootReserve)) :
    ResidualInvariant dx dy N error (x + u) (y + v) := by
  rcases hinv with hbal | hhigh | hhigh
  · rcases htrichotomy with hnew | hPload | hQload
    · left
      have hdiff : |(N - x) - (N - y)| = |x - y| := by
        rw [show (N - x) - (N - y) = -(x - y) by ring, abs_neg]
      have hdiffNew : |((N - x) - u) - ((N - y) - v)| = |(x + u) - (y + v)| := by
        rw [show ((N - x) - u) - ((N - y) - v) = -((x + u) - (y + v)) by ring, abs_neg]
      rw [hdiff, hdiffNew] at hnew
      exact hnew.trans (max_le hbal hsmall)
    · right; left
      have hnonneg := mul_nonneg (sub_nonneg.mpr hdxOne) hx
      have hdiff := (abs_le.mp hbal).2
      constructor <;> nlinarith only [hPload.1, hPload.2, hP, hroot, hdiff, hnonneg, herror]
    · right; right
      have hnonneg := mul_nonneg (sub_nonneg.mpr hdyOne) hy
      have hdiff := (abs_le.mp hbal).1
      constructor <;> nlinarith only [hQload.1, hQload.2, hQ, hroot, hdiff, hnonneg, herror]
  · exact Or.inr (Or.inl ⟨hhigh.1.trans (le_add_of_nonneg_right hu),
      hhigh.2.trans (le_add_of_nonneg_right hv)⟩)
  · exact Or.inr (Or.inr ⟨hhigh.1.trans (le_add_of_nonneg_right hu),
      hhigh.2.trans (le_add_of_nonneg_right hv)⟩)

theorem natAbsDiff_cast (u v : ℕ) : (natAbsDiff u v : ℝ) = |(u : ℝ) - v| := by
  rcases le_total u v with huv | hvu
  · have huvReal : (u : ℝ) ≤ v := by exact_mod_cast huv
    simp only [natAbsDiff, Nat.sub_eq_zero_of_le huv, Nat.zero_max,
      Nat.cast_sub huv, abs_of_nonpos (sub_nonpos.mpr huvReal)]
    ring
  · have hvuReal : (v : ℝ) ≤ u := by exact_mod_cast hvu
    simp only [natAbsDiff, Nat.sub_eq_zero_of_le hvu, Nat.max_zero,
      Nat.cast_sub hvu, abs_of_nonneg (sub_nonneg.mpr hvuReal)]

/-- Literal natural-cardinality Appendix output has exactly the real
trichotomy used by the source invariant, when its used loads fit. -/
theorem appendix_trichotomy_real {b : ℕ} (F : OrderedRootedForest b)
    (orient : Fin b → Fin 2 ≃ Fin 2) (X Y P Q rootReserve small : ℕ)
    (hX : sideLoad F orient 0 ≤ X) (hY : sideLoad F orient 1 ≤ Y)
    (h : AppendixA2Trichotomy F orient X Y P Q rootReserve small) :
    |((X : ℝ) - sideLoad F orient 0) - ((Y : ℝ) - sideLoad F orient 1)| ≤
        max |(X : ℝ) - Y| (small : ℝ) ∨
      ((P : ℝ) ≤ sideLoad F orient 0 + rootReserve ∧
        (P : ℝ) ≤ sideLoad F orient 1 + rootReserve) ∨
      ((Q : ℝ) ≤ sideLoad F orient 0 + rootReserve ∧
        (Q : ℝ) ≤ sideLoad F orient 1 + rootReserve) := by
  rcases h with h | h | h
  · left
    have hcast : (natAbsDiff (X - sideLoad F orient 0) (Y - sideLoad F orient 1) : ℝ) ≤
        max (natAbsDiff X Y : ℝ) (small : ℝ) := by exact_mod_cast h
    simpa only [natAbsDiff_cast, Nat.cast_sub hX, Nat.cast_sub hY] using hcast
  · right; left
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · right; right
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

end Erdos547b.ZhaoSourcePartThreeResidualNumerics

#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.ResidualInvariant.of_cleanup
#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.ResidualInvariant.advance
#print axioms Erdos547b.ZhaoSourcePartThreeResidualNumerics.appendix_trichotomy_real
