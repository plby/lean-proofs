-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.GSn
import ErdosProblems.Erdos1177.GSnPotential

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# No short odd cycles in `GS_n(κ)` (Erdős–Galvin–Hajnal, Lemma 8.3(A))

This file proves that the generalized Specker graph `GS_n(κ)` of
`ErdosProblems.Erdos1177.GSn` contains **no odd cycle of length `≤ 2n+1`**
(`noShortOddCycle_n : NoShortOddCycle (graph n κ) n`).

The proof is the delta-lemma argument.  Suppose `C_m` (`m = 2i+1`, `3 ≤ m ≤ 2n+1`)
sits in `GS_n(κ)` as an injective cyclic sequence `A : ℤ/m → Vtx`.  Orient each
edge `A j — A(j+1)`: it is an *ascent* if `IsEdge (A j) (A(j+1))` (the "below"
vertex is `A j`) and a *descent* otherwise.  Assign increments `incr j = -n`
(ascent) / `n+1` (descent).  When the descents are the minority
(`(2n+1)·#descents ≤ n·m`, achievable up to reversing the cycle since `m` is odd
and `m ≤ 2n+1`), the total increment is `≤ 0` and the positive increments total
`≤ n²+n`.  The max-window potential `pot` of `ErdosProblems.Erdos1177.GSnPotential` then
produces an index assignment `k j ∈ [0, n²+n]` with
`(A j)_{k_j} < (A(j+1))_{k_{j+1}}` around the whole cycle — a strictly increasing
function on the cyclic group `ℤ/m`, which is impossible.
-/

open Cardinal Finset

namespace Erdos1177
namespace GSn

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {n : ℕ}

/-- A strictly increasing function around a finite cycle `ℤ/m` cannot exist. -/
theorem no_cyclic_strictMono {α : Type*} [Preorder α] (m : ℕ) (hm : 0 < m)
    (f : ZMod m → α) (h : ∀ j : ZMod m, f j < f (j + 1)) : False := by
  have : NeZero m := ⟨hm.ne'⟩
  have hg : StrictMono (fun k : ℕ => f (k : ZMod m)) := by
    apply strictMono_nat_of_lt_succ
    intro k; have := h (k : ZMod m); simpa [Nat.cast_succ] using! this
  have := hg hm; simp only [Nat.cast_zero, ZMod.natCast_self] at this
  exact lt_irrefl _ this

section Cycle

variable {m : ℕ} (A : ZMod m → Vtx n κ)

open Classical in
/-- The edge increment: `-n` on ascents (`IsEdge (A j) (A(j+1))`), `n+1` on
descents. -/
noncomputable def incr (j : ZMod m) : ℤ :=
  if IsEdge (A j).1 (A (j + 1)).1 then -(n : ℤ) else (n + 1)

open Classical in
/-- The number of descent edges. -/
noncomputable def descCount [NeZero m] : ℕ :=
  (Finset.univ.filter (fun j : ZMod m => ¬ IsEdge (A j).1 (A (j + 1)).1)).card

/-- **Core delta-lemma contradiction.**  Under the two sum bounds (total increment
`≤ 0`, positive increments `≤ n²+n`), a cyclic sequence of adjacent vertices is
impossible. -/
theorem cycle_false (hm : 0 < m) [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1)))
    (hsum : ∑ e : ZMod m, incr A e ≤ 0)
    (hpos : ∑ e : ZMod m, max (incr A e) 0 ≤ (n * n + n : ℤ)) : False := by
  classical
  set k : ZMod m → ℕ := fun j => (pot m hm (incr A) j).toNat with hk_def
  have hpot_nn : ∀ j, 0 ≤ pot m hm (incr A) j := fun j => pot_nonneg m hm _ j
  have hk_eq : ∀ j, (k j : ℤ) = pot m hm (incr A) j := by
    intro j; rw [hk_def]; simp only; rw [Int.toNat_of_nonneg (hpot_nn j)]
  have hk_lt : ∀ j, k j < L n := by
    intro j
    have h1 : pot m hm (incr A) j ≤ (n * n + n : ℤ) :=
      le_trans (pot_le_posSum m hm (incr A) j) hpos
    have h2 : (k j : ℤ) ≤ (n * n + n : ℤ) := by rw [hk_eq]; exact h1
    have h3 : k j ≤ n * n + n := by exact_mod_cast h2
    simp only [L]; omega
  set f : ZMod m → Pt κ := fun j => (A j).1 ⟨k j, hk_lt j⟩ with hf_def
  apply no_cyclic_strictMono m hm f
  intro j
  have hstep : (k j : ℤ) + incr A j ≤ (k (j + 1) : ℤ) := by
    have := pot_step m hm (incr A) hsum j; rw [hk_eq, hk_eq]; exact this
  by_cases hasc : IsEdge (A j).1 (A (j + 1)).1
  · have hincr : incr A j = -(n : ℤ) := by rw [incr]; simp [hasc]
    rw [hincr] at hstep
    have hle : k j ≤ k (j + 1) + n := by
      have : (k j : ℤ) ≤ (k (j + 1) : ℤ) + n := by linarith
      exact_mod_cast this
    exact edge_lt_of_index_le (A j).2 (A (j + 1)).2 hasc (hk_lt j) (hk_lt (j + 1)) hle
  · have hincr : incr A j = (n + 1 : ℤ) := by rw [incr]; simp [hasc]
    rw [hincr] at hstep
    have hedge : IsEdge (A (j + 1)).1 (A j).1 := by
      rcases hAadj j with h | h
      · exact absurd h hasc
      · exact h
    have hge : k j + n + 1 ≤ k (j + 1) := by
      have : (k j : ℤ) + n + 1 ≤ (k (j + 1) : ℤ) := by linarith
      exact_mod_cast this
    exact edge_gt_of_index_ge (A (j + 1)).2 hedge (hk_lt (j + 1)) (hk_lt j) hge

/-
Total increment in terms of the descent count: `∑ incr = -n·m + (2n+1)·D`.
-/
theorem sum_incr_eq [NeZero m] :
    ∑ e : ZMod m, incr A e = -(n : ℤ) * m + (2 * n + 1) * descCount A := by
  unfold incr;
  simp +decide only [neg_mul];
  rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring

/-
Total of positive increments: `∑ max(incr,0) = (n+1)·D`.
-/
theorem sum_max_incr_eq [NeZero m] :
    ∑ e : ZMod m, max (incr A e) 0 = (n + 1 : ℤ) * descCount A := by
  convert! Finset.sum_congr rfl fun x hx => show max ( if IsEdge ( A x ).1 ( A ( x + 1 ) ).1 then - ( n : ℤ ) else ( n + 1 : ℤ ) ) 0 = if IsEdge ( A x ).1 ( A ( x + 1 ) ).1 then 0 else ( n + 1 : ℤ ) from ?_ using 1;
  all_goals norm_num [ Finset.sum_ite ];
  convert! mul_comm _ _ using 2;
  split_ifs <;> norm_num ; linarith

/-- **Core contradiction, in terms of the descent count.**  If the descents are a
"minority" in the sense `(2n+1)·D ≤ n·m`, and `m ≤ 2n+1`, a cycle is impossible. -/
theorem cycle_false' (hm : 0 < m) [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1)))
    (hmle : m ≤ 2 * n + 1)
    (hD : (2 * n + 1) * descCount A ≤ n * m) : False := by
  have hDn : descCount A ≤ n := by
    have h2 : n * m ≤ n * (2 * n + 1) := by gcongr
    nlinarith [hD, h2]
  refine cycle_false A hm hAadj ?_ ?_
  · rw [sum_incr_eq]
    have hz : (2 * n + 1 : ℤ) * descCount A ≤ (n : ℤ) * m := by exact_mod_cast hD
    have hmz : (m : ℤ) ≤ 2 * n + 1 := by exact_mod_cast hmle
    nlinarith [hz, hmz]
  · rw [sum_max_incr_eq]
    have hz : (descCount A : ℤ) ≤ n := by exact_mod_cast hDn
    nlinarith [hz]

/-- The reversed cycle `A ∘ neg`. -/
def reverseCycle : ZMod m → Vtx n κ := fun j => A (-j)

theorem reverseCycle_adj [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1))) :
    ∀ j : ZMod m, (graph n κ).Adj (reverseCycle A j) (reverseCycle A (j + 1)) := by
  intro j
  have := hAadj (-j - 1)
  simp [reverseCycle] at this ⊢
  ring_nf at this ⊢
  exact this.symm

/-
The descent count of the reversed cycle is `m - D` (the ascent count of `A`).
-/
theorem descCount_reverse [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1))) :
    descCount (reverseCycle A) = m - descCount A := by
  refine' eq_tsub_of_add_eq _;
  convert! Finset.card_add_card_compl ( Finset.filter ( fun j => ¬ IsEdge ( A ( -j ) ).1 ( A ( -j - 1 ) ).1 ) Finset.univ ) using 1;
  congr! 1;
  all_goals try exact Classical.decPred _;
  · unfold descCount reverseCycle
    have hneg (j : ZMod m) : -(j + 1) = -j - 1 := by ring
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hneg j]
  · refine' Finset.card_bij ( fun j _ => -j - 1 ) _ _ _ <;> simp +decide only [mem_compl, mem_filter, mem_univ, true_and, not_not, exists_prop, neg_sub,
    sub_neg_eq_add, add_sub_cancel_left];
    · intro a ha; specialize hAadj a; simp_all +decide [ add_comm, graph ] ;
      exact hAadj.resolve_left ha;
    · intro b hb;
      use -b - 1;
      have := not_isEdge_both ( A ( -b - 1 ) |>.2 ) ( A ( -b ) |>.2 ) ; simp_all +decide [ sub_eq_add_neg, add_assoc ];
  · cases m <;> aesop

end Cycle

/-- Arithmetic core of the minority condition. -/
theorem arith_minority (n D m : ℕ) (h1 : 2 * D + 1 ≤ m) (h2 : m ≤ 2 * n + 1) :
    (2 * n + 1) * D ≤ n * m := by
  have hDn : D ≤ n := by omega
  nlinarith [h1, h2, hDn, Nat.mul_le_mul_left n h1]

/-- **Lemma 8.3(A): `GS_n(κ)` has no odd cycle of length `≤ 2n+1`.** -/
theorem noShortOddCycle_n : NoShortOddCycle (graph n κ) n := by
  intro m hodd hm3 hmle ⟨A, hAinj, hAadj⟩
  classical
  have : NeZero m := ⟨by omega⟩
  have hm0 : 0 < m := by omega
  -- descent count D of A; either A or its reversal has the minority condition
  set D := descCount A with hD_def
  have hDle : D ≤ m := by
    rw [hD_def, descCount]
    exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, ZMod.card])
  -- m is odd, so 2*D ≠ m
  have hodd2 : 2 * D ≠ m := by
    rintro he
    have hme : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
    exact hme ⟨D, by omega⟩
  rcases Nat.lt_or_ge (2 * D) m with hcase | hcase
  · -- descents minority for A
    have h2D : 2 * D + 1 ≤ m := by omega
    exact cycle_false' A hm0 hAadj hmle (arith_minority n D m h2D hmle)
  · -- descents majority: reverse
    have h2Dgt : m < 2 * D := by omega
    have hA'adj := reverseCycle_adj A hAadj
    have hD' : descCount (reverseCycle A) = m - D := descCount_reverse A hAadj
    have hRlt : 2 * descCount (reverseCycle A) + 1 ≤ m := by rw [hD']; omega
    exact cycle_false' (reverseCycle A) hm0 hA'adj hmle
      (arith_minority n (descCount (reverseCycle A)) m hRlt hmle)

end GSn
end Erdos1177
