import ErdosProblems.Erdos546.MonoPair
import ErdosProblems.Erdos546.Numeric

/-!
# The finite doubling iteration for Erdős Problem 546

This module contains the arithmetic-independent assembly of the Sudakov
amplification step.  The scale begins at `q = 5` and doubles.  The recursion is
well founded because its measure is `s - q`; legality gives `q < s`, while the
recursive scale is `2q`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset SimpleGraph

/-- A graph fits into the clique side of a monochromatic pair as soon as that
side has at least as many vertices as the graph. -/
theorem isContained_of_monoPair_of_card_le
    {v N : ℕ} {G : SimpleGraph (Fin v)} {H : SimpleGraph (Fin N)}
    {X Y : Finset (Fin N)} (hpair : MonoPair H X Y) (hcard : v ≤ X.card) :
    G ⊑ H := by
  have hsubtype : Fintype.card (Fin v) ≤ Fintype.card (↑X : Set (Fin N)) := by
    simpa using hcard
  let f : Fin v ↪ (↑X : Set (Fin N)) :=
    (Function.Embedding.nonempty_of_card_le hsubtype).some
  refine ⟨⟨⟨fun x ↦ (f x : Fin N), ?_⟩, ?_⟩⟩
  · intro a b hab
    apply hpair.2.1 (f a).property (f b).property
    intro heq
    exact hab.ne (f.injective (Subtype.ext heq))
  · intro a b hab
    exact f.injective (Subtype.ext hab)

theorem contained_in_one_colour_of_hasMonoPair_of_card_le
    {v N : ℕ} {G : SimpleGraph (Fin v)} {R : SimpleGraph (Fin N)}
    {X Y : Finset (Fin N)} (hpair : HasMonoPair R X Y) (hcard : v ≤ X.card) :
    G ⊑ R ∨ G ⊑ Rᶜ := by
  rcases hpair with hred | hblue
  · exact Or.inl (isContained_of_monoPair_of_card_le hred hcard)
  · exact Or.inr (isContained_of_monoPair_of_card_le hblue hcard)

/-- The initial Erdős--Szekeres pair at scale `q=5`, including the full
rounded reservoir invariant. -/
theorem exists_initial_iteration_pair {N s : ℕ} (R : SimpleGraph (Fin N))
    (hN : N = 2 ^ (32768 * s)) (hs : 32 ≤ s) :
    ∃ X Y : Finset (Fin N), HasMonoPair R X Y ∧
      5 ^ 3 * s ≤ X.card ∧
      reservoirBuffer s * 2 ^ reservoirExponent 5 s ≤ Y.card := by
  let k := 125 * s
  have hfour : 4 ^ k ≤ N := by
    rw [hN]
    calc
      4 ^ k = 2 ^ (250 * s) := by
        calc
          4 ^ k = (2 ^ 2) ^ k := by norm_num
          _ = 2 ^ (2 * k) := (pow_mul 2 2 k).symm
          _ = 2 ^ (250 * s) := by congr 1; dsimp [k]; omega
      _ ≤ 2 ^ (32768 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨X, Y, hpair, hX, hbound⟩ :=
    exists_diagonal_monoPair_four_pow_bound k N R hfour
  refine ⟨X, Y, hpair, ?_, ?_⟩
  · rw [hX]
    simp [k]
  · have hkpow : 4 ^ k = 2 ^ (250 * s) := by
      calc
        4 ^ k = (2 ^ 2) ^ k := by norm_num
        _ = 2 ^ (2 * k) := (pow_mul 2 2 k).symm
        _ = 2 ^ (250 * s) := by congr 1; dsimp [k]; omega
    have htwok : 2 * k = 250 * s := by simp [k]; ring
    have hbound' :
        2 ^ (250 * s) * 2 ^ ((32768 - 250) * s) ≤
          2 ^ (250 * s) * (Y.card + 250 * s) := by
      calc
        2 ^ (250 * s) * 2 ^ ((32768 - 250) * s) = N := by
          rw [hN, ← pow_add]
          congr 1
          norm_num
          ring
        _ ≤ 4 ^ k * (Y.card + 2 * k) := hbound
        _ = 2 ^ (250 * s) * (Y.card + 250 * s) := by rw [hkpow, htwok]
    have hcancel : 2 ^ ((32768 - 250) * s) ≤ Y.card + 250 * s :=
      Nat.le_of_mul_le_mul_left hbound' (by positivity)
    have hsub : 2 ^ ((32768 - 250) * s) - 250 * s ≤ Y.card := by omega
    exact (starting_reservoir_le_sub hs).trans hsub

/-- Abstract finite assembly of an amplification theorem with the exact
signature used in this development.  This isolates termination and all
rounding from the graph-theoretic proof of one amplification step. -/
theorem iterate_amplification
    {v N s : ℕ} (G : SimpleGraph (Fin v)) (R : SimpleGraph (Fin N))
    (hvertex : v ≤ 2 * s ^ 2)
    (hstep : ∀ (q : ℕ) (X Y : Finset (Fin N)),
      5 ≤ q → 2 ^ q ≤ s →
      HasMonoPair R X Y → q ^ 3 * s ≤ X.card →
      reservoirBuffer s * 2 ^ reservoirExponent q s ≤ Y.card →
      G ⊑ R ∨ G ⊑ Rᶜ ∨
        ∃ X' Y' : Finset (Fin N), HasMonoPair R X' Y' ∧
          pairTarget q s ≤ X'.card ∧
          (2 * q) ^ 3 * s ≤ X'.card ∧
          reservoirBuffer s * 2 ^ reservoirExponent (2 * q) s ≤ Y'.card)
    {q : ℕ} {X Y : Finset (Fin N)}
    (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ s)
    (hpair : HasMonoPair R X Y) (hX : q ^ 3 * s ≤ X.card)
    (hY : reservoirBuffer s * 2 ^ reservoirExponent q s ≤ Y.card) :
    G ⊑ R ∨ G ⊑ Rᶜ := by
  let rec loop (q : ℕ) (X Y : Finset (Fin N))
      (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ s)
      (hpair : HasMonoPair R X Y) (hX : q ^ 3 * s ≤ X.card)
      (hY : reservoirBuffer s * 2 ^ reservoirExponent q s ≤ Y.card) :
      G ⊑ R ∨ G ⊑ Rᶜ := by
    rcases hstep q X Y hq hlegal hpair hX hY with hcopy | hcopy | hnext
    · exact Or.inl hcopy
    · exact Or.inr hcopy
    · obtain ⟨X', Y', hpair', ht, hX', hY'⟩ := hnext
      by_cases hcross : s < 2 ^ (2 * q)
      · apply contained_in_one_colour_of_hasMonoPair_of_card_le hpair'
        have hspos : 0 < s := (Nat.two_pow_pos q).trans_le hlegal
        exact hvertex.trans ((crossing_pairTarget_gt hspos hcross).le.trans ht)
      · have hlegal' : 2 ^ (2 * q) ≤ s := by omega
        exact loop (2 * q) X' Y' (by omega) hlegal' hpair' hX' hY'
  termination_by s - q
  decreasing_by
    have hqpow : q < 2 ^ q := Nat.lt_two_pow_self
    have hqs : q < s := hqpow.trans_le hlegal
    omega
  exact loop q X Y hq hlegal hpair hX hY

end Erdos546
