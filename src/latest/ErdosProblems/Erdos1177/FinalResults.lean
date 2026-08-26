-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Consequences
import ErdosProblems.Erdos1177.ReiherPassage

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Headline results depending only on the literature interfaces E1–E5

Every headline resolution of arXiv:2606.24882 was assembled above from
propositions carried as explicit hypotheses.  All of the paper's *internal*
machinery has been fully proved (`ErdosProblems.Erdos1177.AmalgClosure`,
`ErdosProblems.Erdos1177.DecompReverse`, `ErdosProblems.Erdos1177.Lift`, `ErdosProblems.Erdos1177.Reservoir`,
`ErdosProblems.Erdos1177.NegativeDirection`, `ErdosProblems.Erdos1177.CycleCollapse`,
`ErdosProblems.Erdos1177.Calibration`, …), and every remaining carried input has been
reduced to the **five literature theorems E1–E5** stated in
`ErdosProblems.Erdos1177.External`.

In particular the strengthened `ReiherExpansion` used throughout is *exactly*
Reiher's published theorem **E4** (`reiherExpansion_iff_E4`), the §6 reservoir
output `AllLinearExists` is derived from **E3** (`allLinearExists_of_E3`), and the
negative core from **E2**+**E3** (`negativeCore_of`).

This file restates the headline results with the external hypotheses given as the
verbatim literature interfaces `E4_Reiher` (E4), `E3_EGH_P` (E3),
`E2_EH_oddgirth` (E2) and `E5_HK_loose7` (E5) — so that *nothing except E1–E5 is
undischarged*, and E1–E5 are invoked exactly as the named literature theorems. -/

open Cardinal

namespace Erdos1177

universe u

/-! ### Resolution of Erdős Problem #593 -/

/-- **Resolution of Erdős Problem #593** (`thm:classification`), depending only on
the literature interfaces E4, E3, E2.  For every finite triple system,
obligatoriness, membership in `B`, and the intrinsic Levi-graph condition are
equivalent. -/
theorem classification_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_of_E3 (reiherExpansion_of_E4 hE4) h3 hE2 F

/-- **Obligatoriness is exactly membership in `B`**, depending only on E4, E3, E2. -/
theorem obligatory_iff_bclass_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  (classification_final hE4 h3 hE2 F).1

/-! ### Exact-spectrum dichotomy and Problem #1177 -/

/-- **Exact-spectrum class dichotomy** (`thm:spectrum`), depending only on
E4, E3, E2. -/
theorem spectrum_dichotomy_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_of_E3 (reiherExpansion_of_E4 hE4) h3 hE2 F lam

/-- **Erdős Problem #1177, part (3)** (`thm:1177`), depending only on E4, E3, E2. -/
theorem problem_1177_part3_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_of_E3 (reiherExpansion_of_E4 hE4) h3 hE2 G kappa hk h lam hlam

/-- **Erdős Problem #1177, part (2)** (`cor:intro-1177`(2)), depending only on the
literature interfaces E4, E3, E2 and E5. -/
theorem problem_1177_part2_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2 (reiherExpansion_of_E4 hE4) h3 hE2 hE5

/-! ### Compatibility corollaries -/

/-- **Compatibility (1)** (`cor:compatibility`(1)): every obligatory finite triple
system is strongly tripartite.  Depends only on E4, E3, E2. -/
theorem obligatory_stronglyTripartite_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  obligatory_stronglyTripartite (reiherExpansion_of_E4 hE4) h3 hE2 F hobl

/-- **Compatibility (2)** (`cor:compatibility`(2)): every finite triple-system
forest is obligatory.  Depends only on E4. -/
theorem forest_obligatory_final (hE4 : E4_Reiher.{u}) {F : FTS} (h : F.Forest) :
    FTS.Obligatory.{u} F :=
  forest_obligatory (reiherExpansion_of_E4 hE4) h

/-- **Compatibility (3)** (`cor:compatibility`(3)): for `n ≥ 3`, the private-vertex
cycle expansion `C_n^+` is obligatory iff `n` is even.  Depends only on E4, E3, E2. -/
theorem cycleExpansion_obligatory_iff_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (n : ℕ) (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n :=
  cycleExpansion_obligatory_iff (reiherExpansion_of_E4 hE4) h3 hE2 n hn

/-- **Compatibility (4)** (`cor:compatibility`(4)): the loose cycle
`C_7^{(3)}` is linearly obligatory but not obligatory.  Depends only on
E4, E3, E2 and E5. -/
theorem C7_linearlyObligatory_not_obligatory_final (hE4 : E4_Reiher.{u})
    (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory (reiherExpansion_of_E4 hE4) h3 hE2 hE5

end Erdos1177
