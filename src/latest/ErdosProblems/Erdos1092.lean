/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1092.
https://www.erdosproblems.com/forum/thread/1092

Informal authors:
- Vojtěch Rödl

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1092.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1092.lean
-/
/-
This is a Lean formalization of the negative answer to Erdős Problem 1092.
The mathematical resolution and the fidelity analysis of the exact formal
statement are documented in `tex/1092.tex`.
-/

import Mathlib

namespace Erdos1092

open Classical SimpleGraph Finset Asymptotics Filter

/--
Let `f r m` be maximal such that if every `m`-vertex subgraph of any finite
graph can be made `r`-colourable by deleting at most `f r m` edges, then the
ambient graph is `(r + 1)`-colourable.
-/
noncomputable def f (r m : ℕ) : ℕ :=
  sSup {k : ℕ |
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ H : Subgraph G, Fintype.card H.verts = m →
        ∃ E : Finset (Sym2 H.verts),
          E ⊆ H.coe.edgeFinset ∧ E.card ≤ k ∧
          chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
      chromaticNumber G ≤ (r + 1 : ℕ∞)}

/-- In the exact specification, `f 2 m` vanishes once `m ≥ 5`.
The witness refuting every candidate threshold is the complete graph on four
vertices: it has no `m`-vertex subgraph, but it is not 3-colourable. -/
lemma f_two_eq_zero_of_five_le {m : ℕ} (hm : 5 ≤ m) : f 2 m = 0 := by
  have hset :
      {k : ℕ |
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          (∀ H : Subgraph G, Fintype.card H.verts = m →
            ∃ E : Finset (Sym2 H.verts),
              E ⊆ H.coe.edgeFinset ∧ E.card ≤ k ∧
              chromaticNumber (H.coe.deleteEdges E) ≤ (2 : ℕ∞)) →
          chromaticNumber G ≤ (2 + 1 : ℕ∞)} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hk
    have hχ := hk 4 (⊤ : SimpleGraph (Fin 4)) (by
      intro H hH
      have hcard : Fintype.card H.verts ≤ 4 := by
        calc
          Fintype.card H.verts ≤ Fintype.card (Fin 4) :=
            Fintype.card_subtype_le _
          _ = 4 := Fintype.card_fin 4
      omega)
    norm_num [chromaticNumber_top] at hχ
  simp only [f, Nat.cast_ofNat, hset, csSup_empty, Nat.bot_eq_zero]

/-- The real-valued sequence `f 2 n` is eventually zero. -/
lemma f_two_eventually_zero :
    (fun n : ℕ => (f 2 n : ℝ)) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 5] with n hn
  simp [f_two_eq_zero_of_five_le hn]

/-- The identity sequence is not little-o of `f 2`. -/
lemma not_id_isLittleO_f_two :
    ¬ (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (f 2 n : ℝ)) := by
  intro h
  have hzero :
      (fun n : ℕ => (n : ℝ)) =o[atTop] (fun _ => (0 : ℝ)) :=
    h.congr' EventuallyEq.rfl f_two_eventually_zero
  have heq : (fun n : ℕ => (n : ℝ)) =ᶠ[atTop] (fun _ => (0 : ℝ)) :=
    isLittleO_zero_right_iff.mp hzero
  obtain ⟨N, hN⟩ := eventually_atTop.1 heq
  have hEq := hN (max N 1) (Nat.le_max_left N 1)
  have hpos : 1 ≤ max N 1 := Nat.le_max_right N 1
  have hEq' : ((max N 1 : ℕ) : ℝ) = 0 := by simpa only using hEq
  have hz : max N 1 = 0 := by exact_mod_cast hEq'
  omega

/-- Twice the identity sequence is not little-o of `f 2`. -/
lemma not_two_mul_id_isLittleO_f_two :
    ¬ (fun n : ℕ => ((2 : ℝ) * n)) =o[atTop]
        (fun n : ℕ => (f 2 n : ℝ)) := by
  intro h
  have hzero :
      (fun n : ℕ => ((2 : ℝ) * n)) =o[atTop] (fun _ => (0 : ℝ)) :=
    h.congr' EventuallyEq.rfl f_two_eventually_zero
  have heq : (fun n : ℕ => ((2 : ℝ) * n)) =ᶠ[atTop]
      (fun _ => (0 : ℝ)) := isLittleO_zero_right_iff.mp hzero
  obtain ⟨N, hN⟩ := eventually_atTop.1 heq
  have hEq := hN (max N 1) (Nat.le_max_left N 1)
  have hpos : 1 ≤ max N 1 := Nat.le_max_right N 1
  have hcast : ((max N 1 : ℕ) : ℝ) = 0 := by nlinarith [hEq]
  have hz : max N 1 = 0 := by exact_mod_cast hcast
  omega

/-- Erdős Problem 1092 has a negative answer for `r = 2`. -/
theorem f_asymptotic_2 :
    ¬ (fun (n : ℕ) => (n : ℝ)) =o[atTop] (fun (n : ℕ) => (f 2 n : ℝ)) := by
  exact fun h => not_id_isLittleO_f_two h

/-- The proposed assertion for every `r` also has a negative answer. -/
theorem not_erdos_1092 :
    ¬ ∀ r : ℕ,
      (fun n : ℕ => ((r : ℝ) * n)) =o[atTop]
        (fun n : ℕ => (f r n : ℝ)) := by
  intro h
  exact not_two_mul_id_isLittleO_f_two (h 2)

end Erdos1092

#print axioms Erdos1092.f_asymptotic_2
#print axioms Erdos1092.not_erdos_1092

alias _root_.Erdos1092.f_asymptotic_general := _root_.Erdos1092.not_erdos_1092
