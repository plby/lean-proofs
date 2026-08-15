/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file audits the formal specification proposed for Erdős Problem 1105.

The classical anti-Ramsey theorem is true, but the upstream definition below colors
all of `Sym2 (Fin n)`, including diagonal pairs.  The formal path assertion is false
already for `k = n = 5`, and the formal cycle asymptotic is false already for triangles.
We give kernel-checked counterexamples to both proposed theorem types.

Mathematical details and a Leanization plan for a corrected definition are in
`tex/1105.tex`.
-/

import Mathlib

namespace Erdos1105

open SimpleGraph

/-- A graph homomorphism is rainbow when distinct source edges receive distinct colors.
This is the definition used by the upstream formal-conjectures specification. -/
def IsRainbow {α V : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (f : H →g G) {C : Type*} (c : Sym2 V → C) : Prop :=
  Function.Injective fun e : H.edgeSet ↦ c (Sym2.map f e)

/-- The upstream anti-Ramsey definition.  Its coloring domain includes diagonal pairs. -/
noncomputable def antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {q | ∃ c : Sym2 (Fin n) → Fin q, Function.Surjective c ∧
    ∀ f : H →g (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c}

/-- Five private diagonal colors and one common off-diagonal color. -/
def diagonalColoringFive (z : Sym2 (Fin 5)) : Fin 6 :=
  if h : z.IsDiag then Fin.castLE (by omega) (z.diagElem h) else 5

lemma diagonalColoringFive_surjective : Function.Surjective diagonalColoringFive := by
  intro i
  by_cases hi : i.val < 5
  · let v : Fin 5 := ⟨i.val, hi⟩
    refine ⟨Sym2.diag v, ?_⟩
    apply Fin.ext
    simp [diagonalColoringFive, v, Sym2.diag]
  · have hi5 : i.val = 5 := by omega
    refine ⟨s((0 : Fin 5), (1 : Fin 5)), ?_⟩
    apply Fin.ext
    simp [diagonalColoringFive, Sym2.mk_isDiag_iff, hi5]

private def firstPathEdge : (pathGraph 5).edgeSet :=
  ⟨s((0 : Fin 5), (1 : Fin 5)), by simp [SimpleGraph.mem_edgeSet, pathGraph_adj]⟩

private def secondPathEdge : (pathGraph 5).edgeSet :=
  ⟨s((1 : Fin 5), (2 : Fin 5)), by simp [SimpleGraph.mem_edgeSet, pathGraph_adj]⟩

private lemma firstPathEdge_ne_secondPathEdge : firstPathEdge ≠ secondPathEdge := by
  intro h
  have hval := congrArg Subtype.val h
  simp [firstPathEdge, secondPathEdge, Sym2.eq] at hval

lemma diagonalColoringFive_no_rainbow
    (f : pathGraph 5 →g (⊤ : SimpleGraph (Fin 5))) :
    ¬IsRainbow f diagonalColoringFive := by
  intro hf
  apply firstPathEdge_ne_secondPathEdge
  apply hf
  change diagonalColoringFive (Sym2.map f s((0 : Fin 5), (1 : Fin 5))) =
    diagonalColoringFive (Sym2.map f s((1 : Fin 5), (2 : Fin 5)))
  have h01 : ¬s(f (0 : Fin 5), f (1 : Fin 5)).IsDiag := by
    rw [Sym2.mk_isDiag_iff]
    exact (f.map_adj (by simp [pathGraph_adj])).ne
  have h12 : ¬s(f (1 : Fin 5), f (2 : Fin 5)).IsDiag := by
    rw [Sym2.mk_isDiag_iff]
    exact (f.map_adj (by simp [pathGraph_adj])).ne
  simp only [Sym2.map_mk]
  simp [diagonalColoringFive, h01, h12]

/-- The upstream quantity is at least six at `H = P₅`, `n = 5`. -/
theorem six_le_antiRamseyNum_pathGraph_five :
    6 ≤ antiRamseyNum (pathGraph 5) 5 := by
  unfold antiRamseyNum
  let S : Set ℕ := {q | ∃ c : Sym2 (Fin 5) → Fin q, Function.Surjective c ∧
    ∀ f : pathGraph 5 →g (⊤ : SimpleGraph (Fin 5)), ¬IsRainbow f c}
  have hmem : 6 ∈ S :=
    ⟨diagonalColoringFive, diagonalColoringFive_surjective,
      diagonalColoringFive_no_rainbow⟩
  have hbdd : BddAbove S := by
    refine ⟨Fintype.card (Sym2 (Fin 5)), ?_⟩
    intro q hq
    rcases hq with ⟨c, hc, _⟩
    simpa using Fintype.card_le_of_surjective c hc
  exact le_csSup hbdd hmem

/-- The numerical expression asserted by formal part (ii) equals five at `k = n = 5`. -/
lemma proposedPathFormulaAtFive :
    let k := 5
    let n := 5
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    max ((k - 2).choose 2 + 1)
      ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) = 5 := by
  have hodd : Odd 5 := ⟨2, by norm_num⟩
  norm_num [hodd, Nat.choose]

/-- The exact formal statement proposed as part (ii) of Erdős 1105 is false. -/
theorem not_erdos_1105_parts_ii :
    ¬(∀ (k n : ℕ), 5 ≤ k → k ≤ n →
      let ℓ := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)) := by
  intro h
  have hfive := h 5 5 (by omega) (by omega)
  have hvalue : antiRamseyNum (pathGraph 5) 5 = 5 := by
    simpa only using hfive.trans proposedPathFormulaAtFive
  have hlower := six_le_antiRamseyNum_pathGraph_five
  omega

/-- `answer(True)` elaborates to `True`, so this directly negates the proposed theorem type. -/
theorem not_erdos_1105_parts_ii_type :
    ¬(True ↔ ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
      let ℓ := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)) := by
  simpa only [true_iff] using not_erdos_1105_parts_ii

/-!
The cycle assertion is also false for the upstream definition.  For `n ≥ 2`, give
each diagonal pair its own color `0, ..., n - 1`, and color an off-diagonal pair
`{a,b}` by `n + max a b - 1`.  This is surjective onto `2n - 1` colors.  Every
triangle has two edges incident with its largest-labelled image vertex, and those
two edges have the same color.
-/

/-- The value of the diagonal-plus-maximum coloring on an ordered pair. -/
def triangleColorValue (n : ℕ) (hn : 2 ≤ n) (a b : Fin n) : Fin (2 * n - 1) :=
  if h : a = b then
    ⟨a.val, by omega⟩
  else
    ⟨n + max a.val b.val - 1, by
      have hmax : 1 ≤ max a.val b.val := by
        by_contra hzero
        have ha : a.val = 0 := by omega
        have hb : b.val = 0 := by omega
        exact h (Fin.ext (ha.trans hb.symm))
      omega⟩

lemma triangleColorValue_comm (n : ℕ) (hn : 2 ≤ n) (a b : Fin n) :
    triangleColorValue n hn a b = triangleColorValue n hn b a := by
  apply Fin.ext
  by_cases h : a = b
  · subst b
    simp [triangleColorValue]
  · have h' : b ≠ a := Ne.symm h
    simp [triangleColorValue, h, h', max_comm]

/-- A symmetric coloring of all pairs (including diagonal pairs) by `2n - 1` colors. -/
def triangleColoring (n : ℕ) (hn : 2 ≤ n) : Sym2 (Fin n) → Fin (2 * n - 1) :=
  Sym2.lift ⟨triangleColorValue n hn, triangleColorValue_comm n hn⟩

lemma triangleColoring_surjective (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective (triangleColoring n hn) := by
  intro i
  by_cases hi : i.val < n
  · let v : Fin n := ⟨i.val, hi⟩
    refine ⟨Sym2.diag v, ?_⟩
    apply Fin.ext
    simp [triangleColoring, triangleColorValue, Sym2.diag, v]
  · have hin : n ≤ i.val := by omega
    have hiv : i.val - n + 1 < n := by omega
    let v : Fin n := ⟨i.val - n + 1, hiv⟩
    let z : Fin n := ⟨0, by omega⟩
    have hv0 : z ≠ v := by
      intro h
      have hval := congrArg Fin.val h
      simp [z, v] at hval
    refine ⟨s(z, v), ?_⟩
    apply Fin.ext
    simp [triangleColoring, triangleColorValue, hv0, z, v]
    omega

private def triangleEdgeZeroOne : (cycleGraph 3).edgeSet :=
  ⟨s((0 : Fin 3), (1 : Fin 3)), by simp [cycleGraph_three_eq_top]⟩

private def triangleEdgeZeroTwo : (cycleGraph 3).edgeSet :=
  ⟨s((0 : Fin 3), (2 : Fin 3)), by simp [cycleGraph_three_eq_top]⟩

private def triangleEdgeOneTwo : (cycleGraph 3).edgeSet :=
  ⟨s((1 : Fin 3), (2 : Fin 3)), by simp [cycleGraph_three_eq_top]⟩

private lemma triangleEdgeZeroOne_ne_zeroTwo :
    triangleEdgeZeroOne ≠ triangleEdgeZeroTwo := by
  intro h
  have hval := congrArg Subtype.val h
  simp [triangleEdgeZeroOne, triangleEdgeZeroTwo, Sym2.eq] at hval

private lemma triangleEdgeZeroOne_ne_oneTwo :
    triangleEdgeZeroOne ≠ triangleEdgeOneTwo := by
  intro h
  have hval := congrArg Subtype.val h
  simp [triangleEdgeZeroOne, triangleEdgeOneTwo, Sym2.eq] at hval

private lemma triangleEdgeZeroTwo_ne_oneTwo :
    triangleEdgeZeroTwo ≠ triangleEdgeOneTwo := by
  intro h
  have hval := congrArg Subtype.val h
  simp [triangleEdgeZeroTwo, triangleEdgeOneTwo, Sym2.eq] at hval

/-- No homomorphic image of `C₃` is rainbow for the diagonal-plus-maximum coloring. -/
lemma triangleColoring_no_rainbow (n : ℕ) (hn : 2 ≤ n)
    (f : cycleGraph 3 →g (⊤ : SimpleGraph (Fin n))) :
    ¬IsRainbow f (triangleColoring n hn) := by
  intro hf
  have h01 : f (0 : Fin 3) ≠ f (1 : Fin 3) :=
    (f.map_adj (by simp [cycleGraph_three_eq_top])).ne
  have h02 : f (0 : Fin 3) ≠ f (2 : Fin 3) :=
    (f.map_adj (by simp [cycleGraph_three_eq_top])).ne
  have h12 : f (1 : Fin 3) ≠ f (2 : Fin 3) :=
    (f.map_adj (by simp [cycleGraph_three_eq_top])).ne
  rcases le_total (f (1 : Fin 3)).val (f (0 : Fin 3)).val with h10 | h01v
  · rcases le_total (f (2 : Fin 3)).val (f (0 : Fin 3)).val with h20 | h02v
    · apply triangleEdgeZeroOne_ne_zeroTwo
      apply hf
      apply Fin.ext
      simp [triangleEdgeZeroOne, triangleEdgeZeroTwo, triangleColoring,
        triangleColorValue, h01, h02, h10, h20]
    · apply triangleEdgeZeroTwo_ne_oneTwo
      apply hf
      apply Fin.ext
      have h12v : (f (1 : Fin 3)).val ≤ (f (2 : Fin 3)).val := h10.trans h02v
      simp [triangleEdgeZeroTwo, triangleEdgeOneTwo, triangleColoring,
        triangleColorValue, h02, h12, h02v, h12v]
  · rcases le_total (f (2 : Fin 3)).val (f (1 : Fin 3)).val with h21 | h12v
    · apply triangleEdgeZeroOne_ne_oneTwo
      apply hf
      apply Fin.ext
      simp [triangleEdgeZeroOne, triangleEdgeOneTwo, triangleColoring,
        triangleColorValue, h01, h12, h01v, h21]
    · apply triangleEdgeZeroTwo_ne_oneTwo
      apply hf
      apply Fin.ext
      have h02v : (f (0 : Fin 3)).val ≤ (f (2 : Fin 3)).val := h01v.trans h12v
      simp [triangleEdgeZeroTwo, triangleEdgeOneTwo, triangleColoring,
        triangleColorValue, h02, h12, h02v, h12v]

/-- Under the upstream definition, the triangle anti-Ramsey number is at least `2n - 1`. -/
theorem two_mul_sub_one_le_antiRamseyNum_cycleGraph_three (n : ℕ) (hn : 2 ≤ n) :
    2 * n - 1 ≤ antiRamseyNum (cycleGraph 3) n := by
  unfold antiRamseyNum
  let S : Set ℕ := {q | ∃ c : Sym2 (Fin n) → Fin q, Function.Surjective c ∧
    ∀ f : cycleGraph 3 →g (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c}
  have hmem : 2 * n - 1 ∈ S :=
    ⟨triangleColoring n hn, triangleColoring_surjective n hn,
      triangleColoring_no_rainbow n hn⟩
  have hbdd : BddAbove S := by
    refine ⟨Fintype.card (Sym2 (Fin n)), ?_⟩
    intro q hq
    rcases hq with ⟨c, hc, _⟩
    simpa using Fintype.card_le_of_surjective c hc
  exact le_csSup hbdd hmem

open Asymptotics Filter

/-- The proposed cycle asymptotic is false for the upstream, diagonal-inclusive definition. -/
theorem not_erdos_1105_parts_i :
    ¬(∀ k : ℕ, 3 ≤ k →
      ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
          (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)))) := by
  intro h
  have hO :
      ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph 3) n : ℝ) - n) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ))) := by
    convert h 3 (by omega) using 1
    norm_num
  rw [isBigO_one_nat_atTop_iff] at hO
  rcases hO with ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (C + 2) 2)
  have hN2real : (2 : ℝ) ≤ (N : ℝ) :=
    (le_max_right (C + 2) 2).trans hN.le
  have hN2 : 2 ≤ N := by exact_mod_cast hN2real
  have hlower := two_mul_sub_one_le_antiRamseyNum_cycleGraph_three N hN2
  have hlowerR :
      ((2 * N - 1 : ℕ) : ℝ) ≤ (antiRamseyNum (cycleGraph 3) N : ℝ) := by
    exact_mod_cast hlower
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * N)] at hlowerR
  norm_num at hlowerR
  have hdiff :
      (N : ℝ) - 1 ≤ (antiRamseyNum (cycleGraph 3) N : ℝ) - N := by
    linarith
  have hdiff_le_norm :
      (antiRamseyNum (cycleGraph 3) N : ℝ) - N ≤
        ‖(antiRamseyNum (cycleGraph 3) N : ℝ) - N‖ :=
    Real.le_norm_self _
  have hC' := hC N
  have hCN : C + 2 < (N : ℝ) := (le_max_left (C + 2) 2).trans_lt hN
  linarith

/-- `answer(True)` elaborates to `True`, so this directly negates proposed part (i). -/
theorem not_erdos_1105_parts_i_type :
    ¬(True ↔ ∀ k : ℕ, 3 ≤ k →
      ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
          (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)))) := by
  simpa only [true_iff] using not_erdos_1105_parts_i

#print axioms not_erdos_1105_parts_ii_type
#print axioms not_erdos_1105_parts_i_type

end Erdos1105
