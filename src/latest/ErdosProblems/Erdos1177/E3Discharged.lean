-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.FinalResults
import ErdosProblems.Erdos1177.E4Proof
import ErdosProblems.Erdos1177.E3Proof

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# E3 discharged: the headline results no longer assume the Erdős–Galvin–Hajnal input

The literature input **E3** (`E3_EGH_P`, the Erdős–Galvin–Hajnal simultaneous
common-colour edge-labelling property `P` at `δ(ρ)`, their Definition 6.2 and
Corollary 9.7) is now a **proved theorem** (`Erdos1177.e3_EGH_P`, in
`ErdosProblems.Erdos1177.E3Proof`), obtained from the universal level-graph construction
of Erdős–Galvin–Hajnal Theorem 8.1 (which is what actually yields property `P`).

Combined with the already-discharged **E4** (`Erdos1177.e4_Reiher`,
`ErdosProblems.Erdos1177.E4Proof`), every headline result that used to carry E3 and E4 as
explicit hypotheses can be restated with *both* removed.  The only remaining
literature inputs are **E2** (`E2_EH_oddgirth`) and, for Problem #1177(2) and the
loose-`7`-cycle corollary, **E5** (`E5_HK_loose7`).

Everything below is `sorry`-free and axiom-clean. -/

open Cardinal

namespace Erdos1177

universe u

/-! ### Resolution of Erdős Problem #593 (E3 and E4 discharged) -/

/-- **Resolution of Erdős Problem #593** (`thm:classification`), with E3 and E4
discharged (now depending only on E2). -/
theorem classification_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_final e4_Reiher e3_EGH_P hE2 F

/-- **Obligatoriness is exactly membership in `B`**, with E3 and E4 discharged. -/
theorem obligatory_iff_bclass_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  obligatory_iff_bclass_final e4_Reiher e3_EGH_P hE2 F

/-! ### Exact-spectrum dichotomy and Problem #1177 (E3 and E4 discharged) -/

/-- **Exact-spectrum class dichotomy** (`thm:spectrum`), with E3 and E4 discharged. -/
theorem spectrum_dichotomy_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS)
    (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_final e4_Reiher e3_EGH_P hE2 F lam

/-- **Erdős Problem #1177, part (3)** (`thm:1177`), with E3 and E4 discharged. -/
theorem problem_1177_part3_no_E34 (hE2 : E2_EH_oddgirth.{u})
    (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa) (h : G.FGnonempty kappa)
    (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_final e4_Reiher e3_EGH_P hE2 G kappa hk h lam hlam

/-- **Erdős Problem #1177, part (2)**, with E3 and E4 discharged (still uses E2, E5). -/
theorem problem_1177_part2_no_E34 (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2_final e4_Reiher e3_EGH_P hE2 hE5

/-! ### Compatibility corollaries (E3 and E4 discharged) -/

/-- **Compatibility (1)**: every obligatory finite triple system is strongly
tripartite, with E3 and E4 discharged. -/
theorem obligatory_stronglyTripartite_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS)
    (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  obligatory_stronglyTripartite_final e4_Reiher e3_EGH_P hE2 F hobl

/-- **Compatibility (3)**: for `n ≥ 3`, the private-vertex cycle expansion `C_n^+`
is obligatory iff `n` is even, with E3 and E4 discharged. -/
theorem cycleExpansion_obligatory_iff_no_E34 (hE2 : E2_EH_oddgirth.{u}) (n : ℕ)
    (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n :=
  cycleExpansion_obligatory_iff_final e4_Reiher e3_EGH_P hE2 n hn

/-- **Compatibility (4)**: the loose cycle `C_7^{(3)}` is linearly obligatory but
not obligatory, with E3 and E4 discharged (still uses E2, E5). -/
theorem C7_linearlyObligatory_not_obligatory_no_E34 (hE2 : E2_EH_oddgirth.{u})
    (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory_final e4_Reiher e3_EGH_P hE2 hE5

end Erdos1177
