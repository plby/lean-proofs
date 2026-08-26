-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.CycleCollapse
import ErdosProblems.Erdos1177.External

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Negative direction plumbing (§5, §7)

This file connects the §4 bridge-trace necessity results (`ErdosProblems.Erdos1177.CycleCollapse`)
to the exact-spectrum construction.  It provides the chromatic facts about the
complete graph and the infiniteness of the lift, and assembles the case-(ii)
(no bridge selector) branch of the negative direction into a genuine
`FGnonempty` witness, with **no external theorem** required.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u

/-
The complete graph on `lam.out` has (weak) chromatic number exactly `lam`.
A proper colouring of the complete graph is an injection, so it needs `≥ lam`
colours, and the identity is a proper `lam`-colouring.
-/
theorem completeGraph_hasChromatic (lam : Cardinal.{u}) :
    (SimpleGraph.toHG (⊤ : SimpleGraph lam.out)).HasChromatic lam := by
  constructor;
  · refine' ⟨ id, _ ⟩;
    intro e he; simp_all +decide [ SimpleGraph.toHG ] ;
    rcases he with ⟨ x, y, hxy, rfl ⟩ ; exact ⟨ x, by simp +decide, y, by simp +decide, hxy ⟩ ;
  · intro θ hθ hcolorable
    obtain ⟨c, hc⟩ := hcolorable
    have hinjective : Function.Injective c := by
      intro x y; have := hc; simp_all +decide [ SimpleGraph.toHG ] ;
      have := hc { x, y } ; by_cases h : x = y <;> simp_all +decide ;
      specialize this x y h rfl; tauto;
    exact hθ.not_ge ( by simpa [ Cardinal.mk_out ] using! Cardinal.mk_le_of_injective hinjective )

/-
Every lift is a triple system (each edge has exactly three vertices).
-/
theorem liftHG_tripleSystem {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u}) :
    (liftHG A κ).IsTripleSystem := by
  intro e he;
  convert! Set.ncard_eq_three.mpr ( Erdos1177.liftHG_isTripleSystem A κ e he )

/-
**A nonlinear system cannot embed into a linear host.**  (`thm:EHR-nonlinear`
complement: the negative direction for case (i) uses this together with a linear
exact-λ host.)
-/
theorem nonlinear_not_embeds_linear {F : FTS} (hF : ¬ F.Linear)
    {W : Type u} {H : Hypergraph W} (hH : H.Linear) : ¬ F.Embeds H := by
  contrapose! hF; rcases hF with ⟨ f, hf, hfe ⟩ ;
  intro e₁ he₁ e₂ he₂ hne;
  have := hH ( f '' ↑e₁ ) ( hfe e₁ he₁ ) ( f '' ↑e₂ ) ( hfe e₂ he₂ ) ?_;
  · exact Finset.card_le_one.mpr fun x hx y hy => hf <| this ( Set.mem_inter ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hx |>.1 ) ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hx |>.2 ) ) ( Set.mem_inter ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hy |>.1 ) ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hy |>.2 ) );
  · exact fun h => hne <| Finset.coe_injective <| Set.image_injective.mpr hf h

/-- **§6 output** (`cor:all-linear`), carried as an explicit hypothesis: for every
uncountable cardinal `κ` there is a *linear* triple system of chromatic number
exactly `κ`.  This is the sole output of the transfinite reservoir recursion of
§6 needed for the negative direction (case (i)). -/
def AllLinearExists : Prop :=
  ∀ (kappa : Cardinal.{u}), ℵ₀ < kappa →
    ∃ (W : Type u) (H : Hypergraph W), H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic kappa

/-- Case (ii) extraction: if some edge of `F` carries no bridge incidence, then
`F` has no bridge selector. -/
theorem no_bridgeSelector_of {F : FTS}
    (h : ∃ ed : {e : Finset F.V // e ∈ F.edges}, ∀ w ∈ ed.1, ¬ IsBridgeInc F w ed) :
    ¬ Nonempty (BridgeSelector F) := by
  rintro ⟨bs⟩
  obtain ⟨ed, hed⟩ := h
  exact hed (bs.p ed) (bs.isBridge ed).1 (bs.isBridge ed)

/-- **The negative core follows from the §6 output and E2.**  Assuming only
`AllLinearExists` (the transfinite reservoir recursion's conclusion, §6) and
`E2_EH_oddgirth` (the imported Erdős–Hajnal high-odd-girth theorem), the negative
half `NegativeCore` holds: if `F ∉ B` then every uncountable `λ` carries an
exact-`λ`-chromatic `F`-free triple system.  All of the internal §4–§5
bridge-trace machinery is discharged here (`ErdosProblems.Erdos1177.CycleCollapse`); the
three cases of the obstruction trichotomy are handled by: case (i)
(`nonlinear`) via `AllLinearExists`; case (ii) (no bridge selector) via the lift
of the complete graph (self-contained); case (iii) (odd Berge cycle) via `E2`. -/
theorem negativeCore_of (hlin6 : AllLinearExists.{u}) (hE2 : E2_EH_oddgirth.{u}) :
    NegativeCore.{u} := by
  intro F lam hnb hlam
  have hni : ¬ F.reduce.IntrinsicObligatory :=
    fun h => hnb ((finiteDecomposition_holds F).mpr h)
  by_cases hLin : F.reduce.Linear
  · by_cases hBr : ∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
        ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed
    · -- case (iii): linear, all bridges, so some Berge cycle is odd
      have hEx : ∃ c : BergeCycle F.reduce, ¬ Even c.m := by
        by_contra he; push_neg at he; exact hni ⟨hLin, hBr, he⟩
      obtain ⟨c, hcOdd⟩ := hEx
      have hodd : Odd c.m := (Nat.even_or_odd c.m).resolve_left hcOdd
      have hm3 : 3 ≤ c.m := by
        have := c.hm; rcases hodd with ⟨k, hk⟩; omega
      obtain ⟨V, A, hcard, hAchr, hAgirth⟩ := hE2 lam hlam c.m
      refine ⟨Node A lam × V, liftHG A lam, liftHG_tripleSystem _ _,
        lift_hasChromatic A lam hAchr, ?_⟩
      intro hemb
      exact lift_omits_of_bergeCycle hLin c
        (hAgirth c.m hodd hm3 (by omega)) (F.reduce_embeds_of_embeds hemb)
    · -- case (ii): linear, some edge has no bridge incidence
      push_neg at hBr
      have hns : ¬ Nonempty (BridgeSelector F.reduce) := no_bridgeSelector_of hBr
      refine ⟨Node (⊤ : SimpleGraph lam.out) lam × lam.out, liftHG (⊤) lam,
        liftHG_tripleSystem _ _,
        lift_hasChromatic (⊤) lam (completeGraph_hasChromatic lam), ?_⟩
      intro hemb
      exact lift_omits_of_no_bridgeSelector hLin hns (F.reduce_embeds_of_embeds hemb)
  · -- case (i): nonlinear
    obtain ⟨W, H, htri, hHlin, hchr⟩ := hlin6 lam hlam
    refine ⟨W, H, htri, hchr, ?_⟩
    intro hemb
    exact nonlinear_not_embeds_linear hLin hHlin (F.reduce_embeds_of_embeds hemb)

/-! ### Headline results with the §4–§5 engine discharged

The following restate the paper's headline resolutions with the internal
bridge-trace engine (§4–§5) *removed from the hypotheses*: they now depend only on
`ReiherExpansion` (= E4, Reiher, external), `AllLinearExists` (= the §6 reservoir
recursion's output `cor:all-linear`), and `E2_EH_oddgirth` (external).  The
`NegativeCore` hypothesis is supplied internally by `negativeCore_of`. -/

/-- **Resolution of Erdős Problem #593** with the §4–§5 engine discharged. -/
theorem classification_of (hexp : ReiherExpansion.{u}) (hlin6 : AllLinearExists.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification hexp (negativeCore_of hlin6 hE2) F

/-- **Exact-spectrum dichotomy** with the §4–§5 engine discharged. -/
theorem spectrum_dichotomy_of (hexp : ReiherExpansion.{u}) (hlin6 : AllLinearExists.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy hexp (negativeCore_of hlin6 hE2) F lam

/-- **Erdős Problem #1177, part (3)** with the §4–§5 engine discharged. -/
theorem problem_1177_part3_of (hexp : ReiherExpansion.{u}) (hlin6 : AllLinearExists.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3 hexp (negativeCore_of hlin6 hE2) G kappa hk h lam hlam

end Erdos1177
