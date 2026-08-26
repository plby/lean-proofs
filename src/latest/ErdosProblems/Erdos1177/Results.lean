-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.AmalgClosure
import ErdosProblems.Erdos1177.DecompReverse

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The headline resolutions of Erdős Problems 593 and 1177

This file assembles the paper's two headline theorems.  Every theorem here is
**`sorry`-free**: the whole file uses no `sorry` and no `axiom`.  The results are
proved from four named propositions carried as *explicit hypotheses* (never as
axioms) — precisely the paper's inputs that are not otherwise formalized in this
development:

* `ReiherExpansion` — the E4 interface (Reiher's theorem that `K_{n,n}⁺` is
  obligatory, `thm:Reiher`, together with the subhypergraph passage of
  `lem:obligatory-closure`): every bipartite expansion `J⁺` is obligatory.
* `AmalgClosure` — closure of the obligatory systems under one-point
  amalgamation (`lem:obligatory-closure`, proved in the paper via the
  de Bruijn–Erdős compactness theorem).
* `NegativeCore` — the negative half of #593 and the spectrum construction
  (§4–§6): if `F ∉ B` then every uncountable `λ` carries an exact-`λ`-chromatic
  `F`-free system.  In the paper this is the obstruction trichotomy plus the
  complete-rank one-apex lift (§3, **fully proved** in `ErdosProblems.Erdos1177.Lift`),
  the bridge-trace theorem (§4, from E1/E2), and exact linear calibration
  (§6, from E3).
* `FiniteDecomposition` — the finite bridge decomposition
  (`prop:finite-decomposition`, §5).

Everything else is proved here: the positive half `bclass_obligatory` (by
induction on `B`, its edgeless/isomorphism/disjoint-union cases fully proved as
`edgeless_obligatory`, `obligatory_iso`, `obligatory_disjUnion`), the
equivalence of obligatoriness and membership in `B` (`classification`), the
exact-spectrum dichotomy (`spectrum_dichotomy`), and Problem #1177(3)
(`problem_1177_part3`).
-/

open Cardinal

namespace Erdos1177

universe u

/-! ### Pure-logic bridge between obligatoriness and the spectrum -/

/-- An obligatory finite triple system has empty spectrum: it embeds into every
uncountably chromatic triple system, so no exact-`λ`-chromatic `F`-free system
exists. (Fully proved.) -/
theorem obligatory_not_inSpec (F : FTS) (lam : Cardinal.{u})
    (hobl : FTS.Obligatory.{u} F) : ¬ F.InSpec lam := by
  rintro ⟨hlam, W, H, htri, hchr, hne⟩
  exact hne (hobl H htri (hchr.2 ℵ₀ hlam))

/-! ### The positive half: members of `B` are obligatory (§5) -/

/-- Edgeless finite triple systems are obligatory (they embed into any infinite
host). (Fully proved.) -/
theorem edgeless_obligatory (F : FTS) (h : F.edges = ∅) : FTS.Obligatory.{u} F := by
  intro W H htri huc
  have hinf : Infinite W := huc.infinite htri
  obtain ⟨f, hf, -⟩ := exists_injective_avoiding (fun (_ : Empty) => (Classical.arbitrary W)) F.V
  exact ⟨f, hf, fun e he => absurd he (by rw [h]; simp)⟩

/-
Obligatory systems are closed under disjoint union
(`lem:obligatory-closure`).
-/
theorem obligatory_disjUnion {F G : FTS} (ihF : FTS.Obligatory.{u} F)
    (ihG : FTS.Obligatory.{u} G) : FTS.Obligatory.{u} (F.disjUnion G) := by
  intro W H htri huc
  obtain ⟨fF, hfF, hfFe⟩ := ihF H htri huc
  obtain ⟨gG, hgG, hgGe⟩ := ihG H htri huc
  have hS : Set.Finite (Set.range fF) := by
    exact Set.toFinite _
  generalize_proofs at *; (
  obtain ⟨g0, hg0, hg0e⟩ : ∃ g0 : G.V → W, Function.Injective g0 ∧ ∀ e ∈ G.edges, g0 '' (e : Set G.V) ∈ {e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ} := by
    obtain ⟨g0, hg0, hg0e⟩ : ∃ g0 : G.V → W, Function.Injective g0 ∧ ∀ e ∈ G.edges, g0 '' (e : Set G.V) ∈ {e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ} := by
      have hHR : (⟨{e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
        exact restrict_uc htri huc hS
      convert! ihG _ _ hHR using 1
      generalize_proofs at *; (
      exact fun e he => htri e he.1)
    generalize_proofs at *; (
    use g0)
  generalize_proofs at *; (
  obtain ⟨g, hg, hg'⟩ : ∃ g : G.V → W, Function.Injective g ∧ (∀ e ∈ G.edges, g '' (e : Set G.V) ∈ H.edges) ∧ ∀ x, g x ∉ Set.range fF := by
    obtain ⟨Bad, hBad⟩ : ∃ Bad : Finset G.V, ∀ x, g0 x ∈ Set.range fF ↔ x ∈ Bad := by
      have hBad : Set.Finite {x : G.V | g0 x ∈ Set.range fF} := by
        exact Set.Finite.preimage ( fun x => by aesop ) hS
      generalize_proofs at *; (
      exact ⟨ hBad.toFinset, fun x => by simp ⟩)
    generalize_proofs at *; (
    obtain ⟨emb, hemb, hemb'⟩ : ∃ emb : Bad → W, Function.Injective emb ∧ ∀ x, emb x ∉ Set.range g0 ∧ emb x ∉ Set.range fF := by
      have h_inf : Set.Infinite (Set.univ \ (Set.range g0 ∪ Set.range fF)) := by
        have h_infinite : Infinite W := by
          apply Hypergraph.UncountablyChromatic.infinite htri huc
        generalize_proofs at *; (
        exact Set.infinite_univ.diff ( Set.Finite.union ( Set.toFinite ( Set.range g0 ) ) hS ))
      generalize_proofs at *; (
      have := h_inf.natEmbedding
      generalize_proofs at *; (
      use fun x => this (Fintype.equivFin Bad x).val
      generalize_proofs at *; (
      exact ⟨ fun x y hxy => by simpa [ Fin.ext_iff ] using! Fintype.equivFin Bad |>.injective <| Fin.ext <| by simpa using! this.injective <| Subtype.ext hxy, fun x => ⟨ fun hx => this ( Fintype.equivFin Bad x ).val |>.2.2 <| Or.inl hx, fun hx => this ( Fintype.equivFin Bad x ).val |>.2.2 <| Or.inr hx ⟩ ⟩)))
    generalize_proofs at *; (
    use fun x => if hx : x ∈ Bad then emb ⟨x, hx⟩ else g0 x
    generalize_proofs at *; (
    refine' ⟨ _, _, _ ⟩;
    · intro x y hxy; by_cases hx : x ∈ Bad <;> by_cases hy : y ∈ Bad <;> simp_all +decide [ Function.Injective.eq_iff hg0, Function.Injective.eq_iff hemb ] ;
      exact False.elim ( hemb' x hx |>.1 y hxy.symm );
    · intro e he
      have h_image : (fun x => if hx : x ∈ Bad then emb ⟨x, hx⟩ else g0 x) '' (e : Set G.V) = g0 '' (e : Set G.V) := by
        ext x
        simp;
        constructor <;> rintro ⟨ y, hy, rfl ⟩ <;> use y <;> simp_all +decide ;
        · exact fun h => hg0e e he |>.2 hy <| by obtain ⟨ x, hx ⟩ := hBad y |>.2 h; aesop;
        · exact fun h => False.elim <| hg0e e he |>.2 hy <| by aesop;
      generalize_proofs at *; (
      exact h_image.symm ▸ hg0e e he |>.1);
    · grind)))
  generalize_proofs at *; (
  refine' ⟨ Sum.elim fF g, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
  · rintro ( a | a ) ( b | b ) <;> simp +decide [ * ];
    · exact fun h => congr_arg Sum.inl ( hfF h );
    · exact Ne.symm ( hg'.2 a b );
    · exact fun h => congr_arg Sum.inr ( hg h );
  · simp +decide [ FTS.disjUnion ];
    rintro e ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp +decide [ *, Set.image_image ])))

/-! ### The paper's remaining inputs, carried as explicit hypotheses

The following four propositions are the paper's inputs that are *not* proved in
this development.  Two are imported literature theorems (as the paper's
"external theorem interface" prescribes), and two are the paper's heaviest
internal engines; all are carried below as explicit hypotheses (never as
axioms), so that every theorem stated afterwards is `sorry`-free modulo exactly
these named inputs. -/

/-- **E4-interface** (Reiher, `thm:Reiher`, plus the subhypergraph passage of
`lem:obligatory-closure`): every private-vertex expansion `J⁺` of a finite
bipartite graph `J` is obligatory. -/
def ReiherExpansion : Prop :=
  ∀ {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ) [DecidableRel J.Adj],
    J.Colorable 2 → FTS.Obligatory.{u} (graphExpansion J)

/-- **Amalgamation closure** (`lem:obligatory-closure`, proved in the paper via
the de Bruijn–Erdős compactness theorem): the obligatory systems are closed
under one-point amalgamation. -/
def AmalgClosure : Prop :=
  ∀ {F G : FTS} (x : F.V) (y : G.V), FTS.Obligatory.{u} F → FTS.Obligatory.{u} G →
    FTS.Obligatory.{u} (F.amalgamate G x y)

/-- **`AmalgClosure` holds** (`lem:obligatory-closure`, one-point amalgamation):
fully proved in `ErdosProblems.Erdos1177.AmalgClosure` (elementary apart from the de
Bruijn–Erdős compactness theorem, itself proved in `ErdosProblems.Erdos1177.Compactness`).
-/
theorem amalgClosure_holds : AmalgClosure.{u} :=
  fun x y hF hG => amalgamate_obligatory x y hF hG

/-- **Negative half of Problem #593 and the spectrum construction** (§4–§6): if
`F ∉ B`, then for every uncountable `λ` there is an exact-`λ`-chromatic `F`-free
triple system.  In the paper this is the obstruction trichotomy combined with the
complete-rank one-apex lift (§3, fully proved in `ErdosProblems.Erdos1177.Lift`), the
bridge-trace theorem (§4, from E1/E2), and exact linear calibration (§6, from
E3). -/
def NegativeCore : Prop :=
  ∀ (F : FTS) (lam : Cardinal.{u}), ¬ Bclass F → ℵ₀ < lam → F.FGnonempty lam

/-- **Finite bridge decomposition** (`prop:finite-decomposition`, §5): membership
in `B` is equivalent to the intrinsic bridge/even-Berge-cycle condition. -/
def FiniteDecomposition : Prop :=
  ∀ (F : FTS), Bclass F ↔ F.reduce.IntrinsicObligatory

/-- **`FiniteDecomposition` holds** (`prop:finite-decomposition`, §5): fully proved
in `ErdosProblems.Erdos1177.DecompReverse` (the finite bridge decomposition, via the
separation dichotomy `ErdosProblems.Erdos1177.DecompExpansion` — amalgamation at a bridge
cut vertex or recognition as a bipartite expansion). -/
theorem finiteDecomposition_valid : FiniteDecomposition :=
  finiteDecomposition_holds

/-- **Positive half of Problem #593** (§5): every member of the class `B` is
obligatory.  Proved by induction on the construction of `B`; the edgeless,
isomorphism and disjoint-union cases are discharged by the fully-proved lemmas
above, the amalgamation case by the now fully-proved `amalgClosure_holds`
(`ErdosProblems.Erdos1177.AmalgClosure`), and the expansion case by the carried input
`ReiherExpansion` (E4). -/
theorem bclass_obligatory (hexp : ReiherExpansion.{u})
    (F : FTS) (h : Bclass F) : FTS.Obligatory.{u} F := by
  induction h with
  | edgeless F hF => exact edgeless_obligatory F hF
  | expansion J hJ => exact hexp J hJ
  | iso hiso _ ih => exact obligatory_iso hiso ih
  | union _ _ ihF ihG => exact obligatory_disjUnion ihF ihG
  | amalg x y _ _ ihF ihG => exact amalgClosure_holds x y ihF ihG

/-! ### Resolution of Erdős Problem #593 -/

/-- **Resolution of Erdős Problem #593** (`thm:classification`).  For every
finite triple system, obligatoriness, membership in the class `B`, and the
intrinsic Levi-graph condition are equivalent.  Proved from the paper's inputs
carried as explicit hypotheses; the theorem itself is `sorry`-free. -/
theorem classification (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧
    (Bclass F ↔ F.reduce.IntrinsicObligatory) := by
  refine ⟨⟨fun hobl => ?_, bclass_obligatory hexp F⟩, finiteDecomposition_holds F⟩
  by_contra hnb
  obtain ⟨W, H, htri, hchr, hne⟩ :=
    hneg F (Order.succ (ℵ₀ : Cardinal.{u})) hnb (Order.lt_succ _)
  exact hne (hobl H htri (hchr.2 ℵ₀ (Order.lt_succ _)))

/-- Obligatoriness is exactly membership in `B`. -/
theorem obligatory_iff_bclass (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  (classification hexp hneg F).1

/-! ### Exact-spectrum dichotomy and Problem #1177 -/

/-- **Exact-spectrum class dichotomy** (`thm:spectrum`).  For every finite triple
system `F` and cardinal `λ`, `λ ∈ Spec(F)` iff `F ∉ B` and `λ` is uncountable.
Equivalently, `Spec(F) = ∅` when `F ∈ B` and `Spec(F) = {λ : λ > ℵ₀}` otherwise.
Proved (sorry-free) from the carried inputs. -/
theorem spectrum_dichotomy (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) := by
  constructor
  · intro hspec
    exact ⟨fun hb => obligatory_not_inSpec F lam (bclass_obligatory hexp F hb) hspec,
      hspec.1⟩
  · rintro ⟨hb, hlam⟩
    exact ⟨hlam, hneg F lam hb hlam⟩

/-- **Erdős Problem #1177, part (3)** (`thm:1177`): if `F_G(κ) ≠ ∅` for one
uncountable `κ`, then `F_G(λ) ≠ ∅` for every uncountable `λ`.  Proved
(sorry-free) from the spectrum dichotomy. -/
theorem problem_1177_part3 (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam := by
  have hnb : ¬ Bclass G := ((spectrum_dichotomy hexp hneg G kappa).mp ⟨hk, h⟩).1
  exact ((spectrum_dichotomy hexp hneg G lam).mpr ⟨hnb, hlam⟩).2

end Erdos1177
