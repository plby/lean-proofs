import Wikipedia.SchoenfliesTheorem.Curve
import Mathlib.Data.Finset.Sort

/-!
# Finite ordered breakpoints

Insert the two endpoints and the midpoint into a finite subset of the unit
interval, then enumerate the resulting set in increasing order.  Consecutive
breakpoints have no point of the original finite set strictly between them.
-/

open Set

namespace Puzzling139335

private theorem finite_set_ordered_breakpoints {F : Set ℝ} (hF : F.Finite)
    (hFI : F ⊆ Icc 0 1) (h0 : 0 ∈ F) (h1 : 1 ∈ F) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧ range t = F := by
  classical
  let s := hF.toFinset
  have hs0 : (0 : ℝ) ∈ s := hF.mem_toFinset.mpr h0
  have hs1 : (1 : ℝ) ∈ s := hF.mem_toFinset.mpr h1
  have htwo : 2 ≤ s.card := by
    calc
      2 = ({0, 1} : Finset ℝ).card := by norm_num
      _ ≤ s.card := Finset.card_le_card (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hs0
        · obtain rfl := Finset.mem_singleton.mp hx
          exact hs1)
  let n := s.card - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hcard : s.card = n + 1 := by dsimp [n]; omega
  let t : Fin (n + 1) → ℝ := s.orderEmbOfFin hcard
  have hmono : StrictMono t := (s.orderEmbOfFin hcard).strictMono
  have hrange : range t = F := by
    simp only [t, Finset.range_orderEmbOfFin, s, Set.Finite.coe_toFinset]
  have hmem (i : Fin (n + 1)) : t i ∈ F := hrange ▸ mem_range_self i
  have ht0 : t 0 = 0 := by
    obtain ⟨i, hi⟩ : (0 : ℝ) ∈ range t := hrange.symm ▸ h0
    apply le_antisymm
    · simpa only [hi] using hmono.monotone (Fin.zero_le i)
    · exact (hFI (hmem 0)).1
  have ht1 : t (Fin.last n) = 1 := by
    obtain ⟨i, hi⟩ : (1 : ℝ) ∈ range t := hrange.symm ▸ h1
    apply le_antisymm
    · exact (hFI (hmem (Fin.last n))).2
    · simpa only [hi] using hmono.monotone i.le_last
  exact ⟨n, hn, t, hmono, ht0, ht1, hrange⟩

/-- If the three required anchor parameters already belong to the finite set,
the ordered breakpoint sequence has exactly that set as its range. -/
theorem exists_partition_with_exact_range {B : Set ℝ} (hB : B.Finite)
    (hBI : B ⊆ Icc 0 1) (h0 : 0 ∈ B) (hhalf : (1 / 2 : ℝ) ∈ B)
    (h1 : 1 ∈ B) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧ range t = B := by
  obtain ⟨n, hn, t, ht, ht0, ht1, hrange⟩ := finite_set_ordered_breakpoints hB hBI h0 h1
  exact ⟨n, hn, t, ht, ht0, ht1, hrange.symm ▸ hhalf, hrange⟩

/-- Consecutive terms of a strictly increasing finite sequence leave no other
term strictly between them. -/
theorem strictMono_consecutive_range_disjoint {n : ℕ} {t : Fin (n + 1) → ℝ}
    (ht : StrictMono t) (k : Fin n) :
    Disjoint (Ioo (t k.castSucc) (t k.succ)) (range t) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨j, rfl⟩
  have hleft : k.castSucc < j := ht.lt_iff_lt.mp hx.1
  have hright : j < k.succ := ht.lt_iff_lt.mp hx.2
  have hleft' : (k : ℕ) < (j : ℕ) := hleft
  have hright' : (j : ℕ) < (k : ℕ) + 1 := hright
  omega

/-- A finite exceptional subset of the unit interval can be made into
breakpoints, while retaining `0`, `1/2`, and `1`. -/
theorem exists_partition_avoiding_finite {B : Set ℝ} (hB : B.Finite)
    (hBI : B ⊆ Icc 0 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → ℝ,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (1 / 2 : ℝ) ∈ range t ∧
      ∀ k : Fin n, Disjoint (Ioo (t k.castSucc) (t k.succ)) B := by
  let F : Set ℝ := insert 0 (insert 1 (insert (1 / 2) B))
  have hF : F.Finite := ((hB.insert (1 / 2)).insert 1).insert 0
  have hFI : F ⊆ Icc 0 1 := by
    intro x hx
    rcases hx with rfl | rfl | rfl | hx
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · constructor <;> norm_num
    · exact hBI hx
  have h0 : (0 : ℝ) ∈ F := Or.inl rfl
  have h1 : (1 : ℝ) ∈ F := Or.inr (Or.inl rfl)
  have hhalf : (1 / 2 : ℝ) ∈ F := Or.inr (Or.inr (Or.inl rfl))
  have hBF : B ⊆ F := fun _ hx => Or.inr (Or.inr (Or.inr hx))
  obtain ⟨n, hn, t, ht, ht0, ht1, htrange⟩ := finite_set_ordered_breakpoints hF hFI h0 h1
  refine ⟨n, hn, t, ht, ht0, ht1, htrange.symm ▸ hhalf, ?_⟩
  intro k
  have hdis := strictMono_consecutive_range_disjoint ht k
  rw [htrange] at hdis
  exact hdis.mono_right hBF

/-- Every breakpoint lies in the unit interval. -/
theorem partition_mem_unitInterval {n : ℕ} {t : Fin (n + 1) → ℝ}
    (ht : StrictMono t) (h0 : t 0 = 0) (h1 : t (Fin.last n) = 1)
    (i : Fin (n + 1)) : t i ∈ Icc 0 1 := by
  constructor
  · simpa only [h0] using ht.monotone (Fin.zero_le i)
  · simpa only [h1] using ht.monotone i.le_last

end Puzzling139335
