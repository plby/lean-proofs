/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 895.
https://www.erdosproblems.com/forum/thread/895

Informal authors:
- Ben Barber

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos895.md
-/
import Mathlib
import Mathlib.Tactic.Sat.FromLRAT

/-!
# Erdős Problem 895

This file formalizes the sharp finite resolution reported by Ben Barber:
every triangle-free graph on the labelled vertices `{1, ..., n}`, with
`n ≥ 18`, contains three distinct independent vertices `a`, `b`, `a + b`.

Lean vertex `i : Fin n` represents the mathematical label `i.val + 1`.
The finite `n = 18` core is reconstructed from an LRAT certificate by
Mathlib's kernel-checked propositional proof generator.
-/

namespace Erdos895

/-- The exact distinct-summand configuration in zero-based `Fin n` coordinates.

If Lean's vertices `a` and `b` have mathematical labels `a.val + 1` and
`b.val + 1`, their sum has `Fin` value `a.val + b.val + 1`. -/
def HasIndependentSchurTriple {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (hsum : a.val + b.val + 1 < n),
    a.val < b.val ∧
      ¬G.Adj a b ∧
      ¬G.Adj a ⟨a.val + b.val + 1, hsum⟩ ∧
      ¬G.Adj b ⟨a.val + b.val + 1, hsum⟩

/-! ## Certified propositional core -/

/-
The 153 variables are the unordered pairs of `[18]`, in lexicographic order.
The CNF consists of 816 triangle clauses and 72 clauses saying that every
distinct-summand Schur triple contains an edge.  The LRAT trace derives the
empty clause using only reverse-unit-propagation steps.
-/
lrat_proof erdos895_cnf_unsatisfiable
  (include_str "Erdos895/Certificate.cnf")
  (include_str "Erdos895/Certificate.lrat")

/-!
The certificate command exposes its conclusion as a balanced disjunction of
the 888 ways in which one input clause can fail.  The following bridge
specializes the 153 variables to an arbitrary relation on `Fin 18`.
-/
theorem core_contradiction_fin
    (R : Fin 18 → Fin 18 → Prop)
    (htri : ∀ ⦃i j k⦄, ¬ (R i j ∧ R i k ∧ R j k))
    (hadd : ∀ ⦃i j k : Fin 18⦄, i.val < j.val → i.val + j.val + 1 = k.val →
      ¬ (¬ R i j ∧ ¬ R i k ∧ ¬ R j k)) : False := by
  have h := erdos895_cnf_unsatisfiable

    (R 0 1)
    (R 0 2)
    (R 0 3)
    (R 0 4)
    (R 0 5)
    (R 0 6)
    (R 0 7)
    (R 0 8)
    (R 0 9)
    (R 0 10)
    (R 0 11)
    (R 0 12)
    (R 0 13)
    (R 0 14)
    (R 0 15)
    (R 0 16)
    (R 0 17)
    (R 1 2)
    (R 1 3)
    (R 1 4)
    (R 1 5)
    (R 1 6)
    (R 1 7)
    (R 1 8)
    (R 1 9)
    (R 1 10)
    (R 1 11)
    (R 1 12)
    (R 1 13)
    (R 1 14)
    (R 1 15)
    (R 1 16)
    (R 1 17)
    (R 2 3)
    (R 2 4)
    (R 2 5)
    (R 2 6)
    (R 2 7)
    (R 2 8)
    (R 2 9)
    (R 2 10)
    (R 2 11)
    (R 2 12)
    (R 2 13)
    (R 2 14)
    (R 2 15)
    (R 2 16)
    (R 2 17)
    (R 3 4)
    (R 3 5)
    (R 3 6)
    (R 3 7)
    (R 3 8)
    (R 3 9)
    (R 3 10)
    (R 3 11)
    (R 3 12)
    (R 3 13)
    (R 3 14)
    (R 3 15)
    (R 3 16)
    (R 3 17)
    (R 4 5)
    (R 4 6)
    (R 4 7)
    (R 4 8)
    (R 4 9)
    (R 4 10)
    (R 4 11)
    (R 4 12)
    (R 4 13)
    (R 4 14)
    (R 4 15)
    (R 4 16)
    (R 4 17)
    (R 5 6)
    (R 5 7)
    (R 5 8)
    (R 5 9)
    (R 5 10)
    (R 5 11)
    (R 5 12)
    (R 5 13)
    (R 5 14)
    (R 5 15)
    (R 5 16)
    (R 5 17)
    (R 6 7)
    (R 6 8)
    (R 6 9)
    (R 6 10)
    (R 6 11)
    (R 6 12)
    (R 6 13)
    (R 6 14)
    (R 6 15)
    (R 6 16)
    (R 6 17)
    (R 7 8)
    (R 7 9)
    (R 7 10)
    (R 7 11)
    (R 7 12)
    (R 7 13)
    (R 7 14)
    (R 7 15)
    (R 7 16)
    (R 7 17)
    (R 8 9)
    (R 8 10)
    (R 8 11)
    (R 8 12)
    (R 8 13)
    (R 8 14)
    (R 8 15)
    (R 8 16)
    (R 8 17)
    (R 9 10)
    (R 9 11)
    (R 9 12)
    (R 9 13)
    (R 9 14)
    (R 9 15)
    (R 9 16)
    (R 9 17)
    (R 10 11)
    (R 10 12)
    (R 10 13)
    (R 10 14)
    (R 10 15)
    (R 10 16)
    (R 10 17)
    (R 11 12)
    (R 11 13)
    (R 11 14)
    (R 11 15)
    (R 11 16)
    (R 11 17)
    (R 12 13)
    (R 12 14)
    (R 12 15)
    (R 12 16)
    (R 12 17)
    (R 13 14)
    (R 13 15)
    (R 13 16)
    (R 13 17)
    (R 14 15)
    (R 14 16)
    (R 14 17)
    (R 15 16)
    (R 15 17)
    (R 16 17)
  simpa (disch := omega) only [htri, hadd, or_false] using h

/-! ## From the propositional core back to graphs -/

/-- The certified finite core, stated in graph language. -/
theorem finite_eighteen (G : SimpleGraph (Fin 18)) (hG : G.CliqueFree 3) :
    HasIndependentSchurTriple G := by
  by_contra hno
  apply core_contradiction_fin G.Adj
  · intro i j k hadj
    exact hG {i, j, k} (SimpleGraph.is3Clique_triple_iff.2 hadj)
  · intro i j k hij hsum hnon
    apply hno
    have hlt : i.val + j.val + 1 < 18 := by omega
    have hk : k = ⟨i.val + j.val + 1, hlt⟩ := by
      apply Fin.ext
      exact hsum.symm
    refine ⟨i, j, hlt, hij, hnon.1, ?_, ?_⟩
    · simpa only [hk] using hnon.2.1
    · simpa only [hk] using hnon.2.2

/-- Restrict to the first eighteen labelled vertices, apply the certified
finite theorem, and transport its witnesses back to the original graph. -/
theorem explicit_bound {n : ℕ} (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : HasIndependentSchurTriple G := by
  let f : Fin 18 ↪ Fin n := Fin.castLEEmb hn
  let H : SimpleGraph (Fin 18) := G.comap f
  have hH : H.CliqueFree 3 :=
    hG.comap (SimpleGraph.Embedding.comap f G).isContained
  obtain ⟨a, b, hsum, hab, hiab, hias, hibs⟩ := finite_eighteen H hH
  have hsum_n : (f a).val + (f b).val + 1 < n := by
    change a.val + b.val + 1 < n
    omega
  refine ⟨f a, f b, hsum_n, hab, hiab, ?_, ?_⟩
  · have hs_eq :
        (⟨(f a).val + (f b).val + 1, hsum_n⟩ : Fin n) =
          f ⟨a.val + b.val + 1, hsum⟩ := by
      apply Fin.ext
      rfl
    simpa only [H, SimpleGraph.comap_adj, hs_eq] using hias
  · have hs_eq :
        (⟨(f a).val + (f b).val + 1, hsum_n⟩ : Fin n) =
          f ⟨a.val + b.val + 1, hsum⟩ := by
      apply Fin.ext
      rfl
    simpa only [H, SimpleGraph.comap_adj, hs_eq] using hibs

/-- Erdős Problem 895, with the sharp threshold supplied by the certificate. -/
theorem erdos_895 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 → HasIndependentSchurTriple G := by
  exact ⟨18, fun _ hn G hG ↦ explicit_bound hn G hG⟩

#print axioms Erdos895.erdos_895

end Erdos895
