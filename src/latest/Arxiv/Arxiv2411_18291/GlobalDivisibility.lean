import Arxiv.Arxiv2411_18291.VertexDeletion

/-!
# The integer incidence lattice on every sufficiently large vertex set

This completes Remark `rem:div` of arXiv:2411.18291. The proof inducts on
the number of vertices. It first represents the link at one vertex, subtracts
the cones over that representation, and then represents the remaining vector
on the vertex-deleted graph. The base case on `q+r` vertices is the local
inclusion–exclusion argument from `Divisibility`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {q r : ℕ}

/-- At uniformity zero there is only the empty edge, and any clique realizes
any integer coefficient on it. -/
theorem integrallyDecomposable_zero_uniformity (hq : q ≤ Fintype.card V)
    (J : Block V 0 → ℤ) : IntegrallyDecomposable q J := by
  obtain ⟨S, _, hS⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hq)
  let Q : Block V q := ⟨S, hS⟩
  let e₀ : Block V 0 := ⟨∅, rfl⟩
  refine ⟨fun P => if P = Q then J e₀ else 0, ?_⟩
  funext e
  have he : e = e₀ := Subtype.ext (card_eq_zero.mp e.property)
  subst e
  simp [boundary, e₀]

private theorem degreeDivisible_induction (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (q r : ℕ),
      Fintype.card V = n → r ≤ q → q + r ≤ n →
      ∀ J : Block V r → ℤ, DegreeDivisible q J → IntegrallyDecomposable q J := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ q r hcard hqr hn J hJ
    cases r with
    | zero =>
      exact integrallyDecomposable_zero_uniformity (by omega) J
    | succ r =>
      cases q with
      | zero => omega
      | succ q =>
        by_cases heq : Fintype.card V = (q + 1) + (r + 1)
        · exact integrallyDecomposable_of_degreeDivisible heq hqr hJ
        · have hpos : 0 < Fintype.card V := by omega
          obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
          let W := {x : V // x ≠ v}
          let σ : Option W ≃ V := Equiv.optionSubtypeNe v
          have hc : Fintype.card W + 1 = n := by
            rw [← Fintype.card_option, Fintype.card_congr σ, hcard]
          have hlt : Fintype.card W < n := by omega
          let J' : Block (Option W) (r + 1) → ℤ :=
            fun e => J (mapBlock σ.toEmbedding e)
          have hJ' : DegreeDivisible (q + 1) J' := hJ.relabel σ
          obtain ⟨Φ, hΦ⟩ := ih (Fintype.card W) hlt W q r rfl (by omega)
            (by omega) (linkVector J') hJ'.link
          let C := liftVector coneBlock Φ
          let K := J' - boundary (r + 1) C
          have hC : IntegrallyDecomposable (q + 1) (boundary (r + 1) C) := ⟨C, rfl⟩
          have hKdiv : DegreeDivisible (q + 1) K := hJ'.sub hC.degreeDivisible
          have hzero : ∀ e, none ∈ e.val → K e = 0 := by
            intro e he
            obtain ⟨e', rfl⟩ := exists_coneBlock he
            change J' (coneBlock e') - boundary (r + 1) (liftVector coneBlock Φ)
              (coneBlock e') = 0
            rw [boundary_coneVector, hΦ]
            simp only [linkVector, sub_self]
          obtain ⟨Ψ, hΨ⟩ := ih (Fintype.card W) hlt W (q + 1) (r + 1) rfl hqr
            (by omega) (restrictVector K) (hKdiv.restrict hzero)
          have hK : IntegrallyDecomposable (q + 1) K := by
            refine ⟨liftVector (mapBlock Function.Embedding.some) Ψ, ?_⟩
            funext e
            by_cases he : none ∈ e.val
            · rw [boundary_extendVector_of_none Ψ e he, hzero e he]
            · obtain ⟨e', rfl⟩ := exists_someBlock he
              rw [boundary_extendVector, hΨ]
              rfl
          have hJ'int : IntegrallyDecomposable (q + 1) J' := by
            simpa only [K, sub_add_cancel] using hK.add hC
          have hback := hJ'int.relabel σ.symm
          have heback : (fun e => J' (mapBlock σ.symm.toEmbedding e)) = J := by
            funext e
            exact congrArg J ((blockEquiv σ).apply_symm_apply e)
          rwa [heback] at hback

/-- For `n ≥ q+r`, all standard degree divisibilities suffice for an integral
clique decomposition. No design or absorber existence is assumed. -/
theorem integrallyDecomposable_of_degreeDivisible_of_le (hqr : r ≤ q)
    (hn : q + r ≤ Fintype.card V) {J : Block V r → ℤ} (hJ : DegreeDivisible q J) :
    IntegrallyDecomposable q J :=
  degreeDivisible_induction (Fintype.card V) V q r rfl hqr hn J hJ

/-- The complete degree-divisibility criterion in Remark `rem:div`. -/
theorem integrallyDecomposable_iff_degreeDivisible_of_le (hqr : r ≤ q)
    (hn : q + r ≤ Fintype.card V) (J : Block V r → ℤ) :
    IntegrallyDecomposable q J ↔ DegreeDivisible q J :=
  ⟨IntegrallyDecomposable.degreeDivisible,
    integrallyDecomposable_of_degreeDivisible_of_le hqr hn⟩

/-- For complete hypergraphs the criterion reduces to the familiar numerical
conditions indexed by `0 ≤ i ≤ r`. -/
theorem complete_divisible_iff (hqr : r ≤ q) (hn : q + r ≤ Fintype.card V) :
    Divisible q (complete V r) ↔
      ∀ i ≤ r, (q - i).choose (r - i) ∣ (Fintype.card V - i).choose (r - i) := by
  constructor
  · intro h i hi
    obtain ⟨I, _, hI⟩ := exists_subset_card_eq (s := (univ : Finset V))
      (show i ≤ univ.card from by simpa using (show i ≤ Fintype.card V by omega))
    simpa only [hI] using h.complete_degree_dvd I (by omega)
  · intro h
    apply integrallyDecomposable_of_degreeDivisible_of_le hqr hn
    intro I hI
    rw [degree_indicator]
    have hc : ((complete V r).filter fun e => I ⊆ e.val).card =
        (Fintype.card V - I.card).choose (r - I.card) := by
      simpa [complete] using card_blocks_between (r := r) I univ (subset_univ I) hI
    rw [hc]
    exact_mod_cast h I.card hI

end Arxiv2411_18291
