import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic
import Mathlib.Topology.Order.Lattice

/-!
# Continuous prefix minima on cubes of arbitrary dimension

Successive differences of these minima are barycentric coordinates for
the simplex quotient.  The empty prefix has value one; one additional
zero after the final prefix makes the coordinate sum telescope.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

/-- The minimum of the first `k` cube coordinates, with empty minimum one. -/
def prefixMinimum {n : ℕ} (u : Fin n → I) (k : ℕ) : I :=
  (Finset.univ.filter fun i : Fin n => i.val < k).inf u

@[simp] theorem prefixMinimum_zero {n : ℕ} (u : Fin n → I) :
    prefixMinimum u 0 = 1 := by
  simp [prefixMinimum]
  rfl

theorem prefixMinimum_antitone {n : ℕ} (u : Fin n → I) :
    Antitone (prefixMinimum u) := by
  intro k l hkl
  apply Finset.inf_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hkl

theorem prefixMinimum_le_coordinate {n : ℕ} (u : Fin n → I)
    (k : ℕ) (i : Fin n) (hi : i.val < k) : prefixMinimum u k ≤ u i :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem prefixMinimum_succ {n : ℕ} (u : Fin n → I) (k : ℕ) (hk : k < n) :
    prefixMinimum u (k + 1) = min (prefixMinimum u k) (u ⟨k, hk⟩) := by
  have hs : (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  unfold prefixMinimum
  rw [hs, Finset.inf_insert]
  exact min_comm _ _

theorem continuous_prefixMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → I => prefixMinimum u k) :=
  Continuous.finset_inf_apply (fun i _ => continuous_apply i)

/-- Prefix minima extended by zero after the last cube coordinate. -/
def extendedMinimum {n : ℕ} (u : Fin n → I) (k : ℕ) : I :=
  if k ≤ n then prefixMinimum u k else 0

theorem extendedMinimum_of_le {n : ℕ} (u : Fin n → I) (k : ℕ) (hk : k ≤ n) :
    extendedMinimum u k = prefixMinimum u k := if_pos hk

@[simp] theorem extendedMinimum_zero {n : ℕ} (u : Fin n → I) :
    extendedMinimum u 0 = 1 := by
  simp [extendedMinimum]

@[simp] theorem extendedMinimum_last_succ {n : ℕ} (u : Fin n → I) :
    extendedMinimum u (n + 1) = 0 := by
  simp [extendedMinimum]

theorem extendedMinimum_antitone {n : ℕ} (u : Fin n → I) :
    Antitone (extendedMinimum u) := by
  intro k l hkl
  by_cases hl : l ≤ n
  · have hk := hkl.trans hl
    simpa only [extendedMinimum, if_pos hk, if_pos hl] using
      prefixMinimum_antitone u hkl
  · rw [show extendedMinimum u l = 0 from if_neg hl]
    exact bot_le

theorem continuous_extendedMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → I => extendedMinimum u k) := by
  by_cases hk : k ≤ n
  · simpa only [extendedMinimum, if_pos hk] using continuous_prefixMinimum n k
  · simpa only [extendedMinimum, if_neg hk] using
      (continuous_const : Continuous (fun _ : Fin n → I => (0 : I)))

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
