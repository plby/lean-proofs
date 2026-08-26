import ErdosProblems.Erdos421.Blocks

/-!
# Elementary counting ingredients

These are the monotonicity and size bounds used before applying the analytic
point-count and prime-gap estimates. Those estimates are not assumed here.
-/

namespace Erdos421

def intervalProduct (m s : ℕ) : ℕ := ∏ i ∈ Finset.range s, (m + i)

/-- At a fixed positive length, an ordinary interval product determines its start. -/
theorem intervalProduct_strictMono {s : ℕ} (hs : 0 < s) :
    StrictMono (fun m ↦ intervalProduct m s) := by
  intro m n hmn
  change intervalProduct m s < intervalProduct n s
  have hn : 0 < n := by omega
  by_cases hm : m = 0
  · have hz : intervalProduct 0 s = 0 := by
      unfold intervalProduct
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hs)
      rfl
    rw [hm, hz]
    exact Finset.prod_pos (fun i _ ↦ by omega)
  · apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      omega
    · intro i _
      omega
    · exact Finset.nonempty_range_iff.mpr (by omega)

theorem intervalProduct_injective {s : ℕ} (hs : 0 < s) :
    Function.Injective (fun m ↦ intervalProduct m s) :=
  (intervalProduct_strictMono hs).injective

/-- The factor-count bound used in both raw-root and child counting. -/
theorem witness_power_bound {E R : Finset ℕ} {X : ℕ}
    (hE : ∀ e ∈ E, 2 ≤ e) (hR : ∀ r ∈ R, r ≤ X)
    (heq : E.prod id = R.prod id) : 2 ^ E.card ≤ X ^ R.card := by
  calc
    2 ^ E.card ≤ E.prod id := Finset.pow_card_le_prod E id 2 hE
    _ = R.prod id := heq
    _ ≤ X ^ R.card := Finset.prod_le_pow_card R id X hR

/-- There are at most `r - 1` starts for an `r`-block crossing a fixed adjacency.
The condition `i ≤ k` and `k + 1 < i + r` means that both indices `k` and
`k + 1` belong to the half-open block `[i,i+r)`. -/
theorem crossing_starts_card_le (k r : ℕ) :
    ((Finset.range (k + 1)).filter (fun i ↦ k + 1 < i + r)).card ≤ r - 1 := by
  have hsub : (Finset.range (k + 1)).filter (fun i ↦ k + 1 < i + r) ⊆
      Finset.Icc (k + 2 - r) k := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hir, hi⟩
    have hik := Finset.mem_range.mp hir
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

end Erdos421
