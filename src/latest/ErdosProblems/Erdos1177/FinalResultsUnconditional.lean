-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E3Discharged
import ErdosProblems.Erdos1177.E2Genuine
import ErdosProblems.Erdos1177.E5HK

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fully unconditional headline results (E2, E3, E4, E5 all discharged)

The four literature inputs used by the paper's final results are now proved:
**E2** (`Erdos1177.e2_EH_oddgirth`), **E3** (`Erdos1177.e3_EGH_P`), **E4**
(`Erdos1177.e4_Reiher`), and **E5** (`Erdos1177.e5_HK_loose7`).  Consequently all
headline resolutions of arXiv:2606.24882 are completely unconditional theorems,
with no carried literature hypotheses.

Everything below is `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`). -/

open Cardinal

namespace Erdos1177

universe u

/-! ### Resolution of Erdős Problem #593 (unconditional) -/

/-- **Resolution of Erdős Problem #593** (`thm:classification`), unconditional.
For every finite triple system, obligatoriness, membership in `B`, and the
intrinsic Levi-graph condition are equivalent. -/
theorem classification_unconditional (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_no_E34 e2_EH_oddgirth F

/-- **Obligatoriness is exactly membership in `B`**, unconditional. -/
theorem obligatory_iff_bclass_unconditional (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  obligatory_iff_bclass_no_E34 e2_EH_oddgirth F

/-! ### Exact-spectrum dichotomy and Problem #1177 (unconditional) -/

/-- **Erdős Problem #1177, part (1)**, unconditional.  If an exact-`ℵ₁`-chromatic
`G`-free triple system exists, then one exists on at most `2^(2^ℵ₀)` vertices. -/
theorem problem_1177_part1_unconditional
    (G : FTS) (h : G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u}))) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
        ¬ G.Embeds H ∧ #W ≤
          (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) :=
  problem_1177_part1 (reiherExpansion_of_E4 e4_Reiher) e3_EGH_P e2_EH_oddgirth G h

/-- Mathlib identifies the cardinal successor of `ℵ₀` with the literal first
aleph by `Cardinal.succ_aleph0`:
`Order.succ (ℵ₀ : Cardinal.{u}) = Cardinal.aleph 1`. -/
theorem problem_1177_part1_aleph_one
    (G : FTS) (h : G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u})) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
        ¬ G.Embeds H ∧ #W ≤
          (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  rw [← Cardinal.succ_aleph0] at h ⊢
  exact problem_1177_part1_unconditional G h

/-- **Exact-spectrum class dichotomy** (`thm:spectrum`), unconditional. -/
theorem spectrum_dichotomy_unconditional (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_no_E34 e2_EH_oddgirth F lam

/-- **Erdős Problem #1177, part (3)** (`thm:1177`), unconditional. -/
theorem problem_1177_part3_unconditional
    (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa) (h : G.FGnonempty kappa)
    (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_no_E34 e2_EH_oddgirth G kappa hk h lam hlam

/-- Problem 1177(3), with its starting cardinal written literally as `ℵ₁`. -/
theorem problem_1177_part3_aleph_one
    (G : FTS) (h : G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}))
    (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam := by
  rw [← Cardinal.succ_aleph0] at h
  exact problem_1177_part3_unconditional G _ (Order.lt_succ _) h lam hlam

/-! ### Compatibility corollaries (unconditional) -/

/-- **Compatibility (1)** (`cor:compatibility`(1)): every obligatory finite triple
system is strongly tripartite.  Unconditional. -/
theorem obligatory_stronglyTripartite_unconditional (F : FTS)
    (hobl : FTS.Obligatory.{u} F) : F.StronglyTripartite :=
  obligatory_stronglyTripartite_no_E34 e2_EH_oddgirth F hobl

/-- **Compatibility (3)** (`cor:compatibility`(3)): for `n ≥ 3`, the private-vertex
cycle expansion `C_n^+` is obligatory iff `n` is even.  Unconditional. -/
theorem cycleExpansion_obligatory_iff_unconditional (n : ℕ) (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n :=
  cycleExpansion_obligatory_iff_no_E34 e2_EH_oddgirth n hn

/-! ### The E5-dependent statements, now fully unconditional -/

/-- **Erdős Problem #1177, part (2)** (`cor:intro-1177`(2)), in its reusable
form parameterized by the Hajnal–Komjáth statement E5. -/
theorem problem_1177_part2_only_E5 (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2_no_E34 e2_EH_oddgirth hE5

/-- **Compatibility (4)** (`cor:compatibility`(4)), in its reusable form
parameterized by E5: the loose cycle `C_7^{(3)}` is linearly obligatory but not
obligatory. -/
theorem C7_linearlyObligatory_not_obligatory_only_E5 (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory_no_E34 e2_EH_oddgirth hE5

/-
**Erdős Problem #1177, part (2)**, fully unconditional after discharge of
Hajnal–Komjáth E5.
-/
theorem problem_1177_part2_unconditional :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2_only_E5 e5_HK_loose7

/-- Problem 1177(2), with every occurrence of the first uncountable cardinal
written literally as `Cardinal.aleph 1`. -/
theorem problem_1177_part2_aleph_one :
    ∃ (G H : FTS),
      G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
      H.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K := by
  rw [← Cardinal.succ_aleph0]
  exact problem_1177_part2_unconditional

/-
**Compatibility (4)**: the loose cycle `C_7^{(3)}` is linearly obligatory
but not obligatory, fully unconditional after discharge of E5.
-/
theorem C7_linearlyObligatory_not_obligatory_unconditional :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory_only_E5 e5_HK_loose7

end Erdos1177
