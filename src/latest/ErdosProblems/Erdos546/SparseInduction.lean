/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.SparseFamily

/-!
# The exact Fox--Sudakov block induction

This file performs the dyadic sparsification iteration.  The local input is
an ordinary sparse-pair statement: every sufficiently large reservoir has
two disjoint equal sides, each losing at most the prescribed dyadic factor.

The proof uses one fixed leaf size
`b = N / (2 * 2 ^ ((Q + 5) * D)) ^ (Q + 1)`.  At a binary node the first
low-degree restriction is made before constructing the left child.  Its
resulting carrier is then used for the low-degree restriction on the right.
This ordering is what controls the new cross term without asserting that
`PairSparse` is preserved by arbitrary restriction.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset SimpleGraph

/-- The local sparse-pair input consumed by the exact block induction. -/
def LocalSparsePairHypothesis {N : ℕ} (n D Q : ℕ)
    (H : SimpleGraph (Fin N)) : Prop :=
  ∀ U : Finset (Fin N), n * 2 ^ ((Q + 5) * D) ≤ U.card →
    ∃ A B : Finset (Fin N),
      A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧ A.Nonempty ∧
      A.card = B.card ∧
      U.card / 2 ^ ((Q + 5) * D) ≤ A.card ∧
      PairSparse (Q + 3) H A B

private theorem foxSudakov_exponent_le {D Q : ℕ}
    (hQ : 15 ≤ Q) (hD : 1 ≤ D) :
    (((Q + 5) * D + 1) * (Q + 1)) ≤ 8 * D * Q ^ 2 := by
  have hleft : (Q + 5) * D + 1 ≤ 2 * Q * D := by
    calc
      (Q + 5) * D + 1 ≤ (Q + 5) * D + D :=
        Nat.add_le_add_left hD _
      _ = (Q + 6) * D := by ring
      _ ≤ (2 * Q) * D := Nat.mul_le_mul_right D (by omega)
      _ = 2 * Q * D := by ring
  have hright : Q + 1 ≤ 2 * Q := by omega
  calc
    ((Q + 5) * D + 1) * (Q + 1) ≤
        (2 * Q * D) * (2 * Q) := Nat.mul_le_mul hleft hright
    _ = 4 * D * Q ^ 2 := by ring
    _ ≤ 8 * D * Q ^ 2 := by
      calc
        4 * D * Q ^ 2 = 4 * (D * Q ^ 2) := by ring
        _ ≤ 8 * (D * Q ^ 2) :=
          Nat.mul_le_mul_right (D * Q ^ 2) (by norm_num)
        _ = 8 * D * Q ^ 2 := by ring

private theorem foxSudakov_scale_pow_le {D Q : ℕ}
    (hQ : 15 ≤ Q) (hD : 1 ≤ D) :
    (2 * 2 ^ ((Q + 5) * D)) ^ (Q + 1) ≤
      2 ^ (8 * D * Q ^ 2) := by
  rw [show 2 * 2 ^ ((Q + 5) * D) =
      2 ^ (((Q + 5) * D) + 1) by rw [pow_succ]; ring]
  calc
    (2 ^ ((Q + 5) * D + 1)) ^ (Q + 1) =
        2 ^ (((Q + 5) * D + 1) * (Q + 1)) := by
          rw [pow_mul]
    _ ≤ 2 ^ (8 * D * Q ^ 2) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
        (foxSudakov_exponent_le hQ hD)

/-- Exact Fox--Sudakov sparsification from an ordinary local sparse-pair
hypothesis.  The output has both the requested density and the full
`2^(8 D Q^2)` cardinality guarantee. -/
theorem exists_squareSparse_of_local_sparse_pairs
    {N n D Q : ℕ} (H : SimpleGraph (Fin N))
    (hQ : 15 ≤ Q) (hD : 1 ≤ D)
    (hN : n * 2 ^ (8 * D * Q ^ 2) ≤ N)
    (hlocal : LocalSparsePairHypothesis n D Q H) :
    ∃ S : Finset (Fin N), SquareSparse Q H S ∧
      N ≤ 2 ^ (8 * D * Q ^ 2) * S.card := by
  classical
  let M := 2 ^ ((Q + 5) * D)
  let K := 2 * M
  let L := 2 ^ (Q + 1)
  let b := N / K ^ (Q + 1)
  have hMpos : 0 < M := by simp [M]
  have hKpos : 0 < K := by positivity
  have hLpos : 0 < L := by positivity
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    obtain ⟨A, B, hA, _hB, _hAB, hAne, _hcard, _hsize, _hsparse⟩ :=
      hlocal ∅ (by simp [hn0])
    exact hAne.ne_empty (Finset.subset_empty.mp hA)
  have hscale : K ^ (Q + 1) ≤ 2 ^ (8 * D * Q ^ 2) := by
    simpa [K, M] using foxSudakov_scale_pow_le hQ hD
  have hnb : n ≤ b := by
    apply (Nat.le_div_iff_mul_le (pow_pos hKpos _)).2
    exact (Nat.mul_le_mul_left n hscale).trans hN
  have hbpos : 0 < b := hnpos.trans_le hnb
  have hroot : K ^ (Q + 1) * b ≤ N := by
    simpa [b] using Nat.mul_div_le N (K ^ (Q + 1))
  have build : ∀ j : ℕ, ∀ U : Finset (Fin N),
      K ^ j * b ≤ U.card →
      ∃ S : Finset (Fin N), S ⊆ U ∧ S.card = 2 ^ j * b ∧
        L * squareEdgeCount H S ≤
          S.card ^ 2 + L * (2 ^ j * b ^ 2) := by
    intro j
    induction j with
    | zero =>
        intro U hU
        have hbU : b ≤ U.card := by simpa using hU
        obtain ⟨S, hSU, hScard⟩ := Finset.exists_subset_card_eq hbU
        refine ⟨S, hSU, by simpa using hScard, ?_⟩
        have hedge : squareEdgeCount H S ≤ S.card ^ 2 := by
          unfold squareEdgeCount
          simpa only [pow_two] using
            (@SimpleGraph.card_interedges_le_mul (Fin N) H
              (Classical.decRel H.Adj) S S)
        simp only [pow_zero, one_mul]
        calc
          L * squareEdgeCount H S ≤ L * S.card ^ 2 :=
            Nat.mul_le_mul_left L hedge
          _ ≤ S.card ^ 2 + L * (b ^ 2) := by
            rw [hScard]
            omega
    | succ j ih =>
        intro U hU
        have hreservoir : n * M ≤ U.card := by
          calc
            n * M ≤ b * M := Nat.mul_le_mul_right M hnb
            _ ≤ (K ^ j * b) * M := by
              apply Nat.mul_le_mul_right M
              calc
                b = 1 * b := by simp
                _ ≤ K ^ j * b :=
                  Nat.mul_le_mul_right b (Nat.one_le_pow j K hKpos)
            _ ≤ (K ^ j * b) * K := by
              apply Nat.mul_le_mul_left
              dsimp [K]
              omega
            _ = K ^ (j + 1) * b := by
              rw [pow_succ]
              ring
            _ ≤ U.card := by simpa [Nat.succ_eq_add_one] using hU
        obtain ⟨A, B, hAU, hBU, hAB, hAne, hcard, hlarge, hpair⟩ :=
          hlocal U (by simpa [M] using hreservoir)
        have hBne : B.Nonempty := by simpa [← Finset.card_pos, ← hcard] using hAne
        let t := K ^ j * b
        have htwo_t : 2 * t ≤ A.card := by
          have hMK : M * (2 * t) = K ^ (j + 1) * b := by
            dsimp [t, K]
            rw [pow_succ]
            ring
          have : 2 * t ≤ U.card / M := by
            apply (Nat.le_div_iff_mul_le hMpos).2
            calc
              2 * t * M = M * (2 * t) := by ring
              _ = K ^ (j + 1) * b := hMK
              _ ≤ U.card := by simpa [Nat.succ_eq_add_one] using hU
          exact this.trans hlarge
        have hpair' : 2 * 2 ^ (Q + 2) * crossEdgeCount H A B ≤
            A.card * B.card := by
          rw [show 2 * 2 ^ (Q + 2) = 2 ^ (Q + 3) by
            rw [show Q + 3 = (Q + 2) + 1 by omega, pow_succ]; ring]
          simpa [PairSparse, hcard] using hpair
        obtain ⟨X, hXA, hXcard, hXdeg⟩ :=
          exists_lowDegree_subset (C := 2 ^ (Q + 2)) H A B
            (by simpa [Finset.card_pos] using hBne) hpair' htwo_t
        have hXt : K ^ j * b ≤ X.card := by simp [hXcard, t]
        obtain ⟨P, hPX, hPcard, hPbound⟩ := ih X hXt
        have hPB : 2 * L * crossEdgeCount H B P ≤ B.card * P.card := by
          rw [crossEdgeCount_comm H B P]
          have hsum : 2 ^ (Q + 2) * crossEdgeCount H P B ≤
              P.card * B.card := by
            rw [crossEdgeCount_eq_sum_crossDegree, Finset.mul_sum]
            calc
              ∑ x ∈ P, 2 ^ (Q + 2) * crossDegree H B x ≤
                  ∑ _x ∈ P, B.card := by
                    apply Finset.sum_le_sum
                    intro x hx
                    exact hXdeg x (hPX hx)
              _ = P.card * B.card := by simp
          simpa [L, show 2 * 2 ^ (Q + 1) = 2 ^ (Q + 2) by
              rw [show Q + 2 = (Q + 1) + 1 by omega, pow_succ]; ring,
            Nat.mul_comm] using hsum
        obtain ⟨Y, hYB, hYcard, hYdeg⟩ :=
          exists_lowDegree_subset (C := L) (t := t) H B P
            (by rw [hPcard]; positivity) hPB (by
              rw [← hcard]
              exact htwo_t)
        have hYt : K ^ j * b ≤ Y.card := by simp [hYcard, t]
        obtain ⟨Z, hZY, hZcard, hZbound⟩ := ih Y hYt
        have hPZ : Disjoint P Z :=
          hAB.mono (hPX.trans hXA) (hZY.trans hYB)
        have hcross : L * crossEdgeCount H P Z ≤ P.card * Z.card := by
          rw [crossEdgeCount_comm H P Z, crossEdgeCount_eq_sum_crossDegree,
            Finset.mul_sum]
          calc
            ∑ z ∈ Z, L * crossDegree H P z ≤ ∑ _z ∈ Z, P.card := by
              apply Finset.sum_le_sum
              intro z hz
              exact hYdeg z (hZY hz)
            _ = Z.card * P.card := by simp
            _ = P.card * Z.card := by ring
        have hPne : P.Nonempty := by rw [← Finset.card_pos, hPcard]; positivity
        have hZne : Z.Nonempty := by rw [← Finset.card_pos, hZcard]; positivity
        refine ⟨P ∪ Z, union_subset (hPX.trans hXA |>.trans hAU)
            (hZY.trans hYB |>.trans hBU), ?_, ?_⟩
        · rw [card_union_of_disjoint hPZ, hPcard, hZcard]
          rw [pow_succ]
          ring
        · rw [squareEdgeCount_union H P Z hPne hZne hPZ,
            card_union_of_disjoint hPZ]
          calc
            L * (squareEdgeCount H P + squareEdgeCount H Z +
                2 * crossEdgeCount H P Z) =
                L * squareEdgeCount H P + L * squareEdgeCount H Z +
                  2 * (L * crossEdgeCount H P Z) := by ring
            _ ≤ (P.card ^ 2 + L * (2 ^ j * b ^ 2)) +
                (Z.card ^ 2 + L * (2 ^ j * b ^ 2)) +
                  2 * (P.card * Z.card) := by omega
            _ = (P.card + Z.card) ^ 2 +
                L * (2 ^ (j + 1) * b ^ 2) := by
                  rw [pow_succ]
                  ring
  obtain ⟨S, hSuniv, hScard, hSbound⟩ :=
    build (Q + 1) Finset.univ (by simpa using hroot)
  refine ⟨S, ?_, ?_⟩
  · rw [SquareSparse]
    have hLQ : L = 2 * 2 ^ Q := by
      simp only [L]
      rw [pow_succ]
      ring
    have hleaf : L * (2 ^ (Q + 1) * b ^ 2) = S.card ^ 2 := by
      rw [hScard]
      simp only [L]
      ring
    rw [hleaf] at hSbound
    have htwice : 2 * (2 ^ Q * squareEdgeCount H S) ≤
        2 * S.card ^ 2 := by
      calc
        2 * (2 ^ Q * squareEdgeCount H S) =
            L * squareEdgeCount H S := by rw [hLQ]; ring
        _ ≤ S.card ^ 2 + S.card ^ 2 := hSbound
        _ = 2 * S.card ^ 2 := by ring
    have := Nat.le_of_mul_le_mul_left htwice (by norm_num : 0 < (2 : ℕ))
    simpa [pow_two] using this
  · have hdivUpper : N < K ^ (Q + 1) * (b + 1) := by
      simpa [b] using Nat.lt_mul_div_succ N (pow_pos hKpos (Q + 1))
    have hbSucc : b + 1 ≤ 2 * b := by omega
    calc
      N ≤ K ^ (Q + 1) * (b + 1) := hdivUpper.le
      _ ≤ K ^ (Q + 1) * (2 * b) :=
        Nat.mul_le_mul_left _ hbSucc
      _ ≤ 2 ^ (8 * D * Q ^ 2) * (2 * b) :=
        Nat.mul_le_mul_right (2 * b) hscale
      _ ≤ 2 ^ (8 * D * Q ^ 2) * (L * b) := by
        apply Nat.mul_le_mul_left
        have : 2 ≤ L := by
          dsimp [L]
          calc
            2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (Q + 1) :=
              Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
                (show 1 ≤ Q + 1 by omega)
        exact Nat.mul_le_mul_right b this
      _ = 2 ^ (8 * D * Q ^ 2) * S.card := by rw [hScard]

end Erdos546
