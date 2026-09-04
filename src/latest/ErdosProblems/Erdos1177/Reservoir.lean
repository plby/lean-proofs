-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.ReservoirBuild
import ErdosProblems.Erdos1177.ReservoirLower
import ErdosProblems.Erdos1177.NegativeDirection

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The §6 reservoir recursion: assembly (`cor:all-linear`)

This file assembles the §6 exact linear calibration into its final output
`AllLinearExists` (`cor:all-linear`): for every uncountable cardinal `κ` there is
a *linear* triple system of chromatic number exactly `κ`.

* `successor_linear` (`thm:successor-linear`): the successor case `κ = μ⁺`, given
  by `CalibData.L`.
* `allLinear_limit`: the limit case, a disjoint union of successor systems along
  a cofinal family (`lem:successors-cofinal`).
* `allLinearExists_of_E3` : `E3_EGH_P → AllLinearExists` — the full §6 reservoir
  recursion discharged.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u

/-! ### Disjoint unions of hypergraphs -/

/-- The disjoint union of a `J`-indexed family of hypergraphs. -/
def Hypergraph.sigma {J : Type u} {W : J → Type u} (H : ∀ j, Hypergraph (W j)) :
    Hypergraph (Σ j, W j) :=
  ⟨{e | ∃ (j : J) (t : Set (W j)), t ∈ (H j).edges ∧ e = Sigma.mk j '' t}⟩

/-
A disjoint union of triple systems is a triple system.
-/
theorem Hypergraph.sigma_isTripleSystem {J : Type u} {W : J → Type u}
    (H : ∀ j, Hypergraph (W j)) (h : ∀ j, (H j).IsTripleSystem) :
    (Hypergraph.sigma H).IsTripleSystem := by
  intro e he; obtain ⟨j, t, ht, rfl⟩ := he; specialize h j t ht; simp_all +decide [ Set.ncard_image_of_injective, Function.Injective ] ;

/-
A disjoint union of linear systems is linear.
-/
theorem Hypergraph.sigma_linear {J : Type u} {W : J → Type u}
    (H : ∀ j, Hypergraph (W j)) (h : ∀ j, (H j).Linear) :
    (Hypergraph.sigma H).Linear := by
  intro e₁ he₁ e₂ he₂ hne;
  obtain ⟨ j₁, t₁, ht₁, rfl ⟩ := he₁
  obtain ⟨ j₂, t₂, ht₂, rfl ⟩ := he₂;
  by_cases h : j₁ = j₂ <;> simp_all +decide [ Set.Subsingleton ];
  · subst h;
    intro a ha x hx hax b hb y hy hay; have := h j₁ t₁ ht₁ t₂ ht₂; simp_all +decide [ Set.Subsingleton ] ;
    exact this ( by aesop ) ha hx hb hy;
  · aesop

/-
**Chromatic number of a disjoint union.**  If each component `H j` has
chromatic number `κs j ≤ κ`, and the `κs j` are cofinal below `κ` (every `θ < κ`
is exceeded by some `κs j`), then the disjoint union has chromatic number exactly
`κ`.
-/
theorem Hypergraph.sigma_hasChromatic {J : Type u} {W : J → Type u}
    (H : ∀ j, Hypergraph (W j)) (κ : Cardinal.{u}) (κs : J → Cardinal.{u})
    (hchr : ∀ j, (H j).HasChromatic (κs j)) (hle : ∀ j, κs j ≤ κ)
    (hcof : ∀ θ, θ < κ → ∃ j, θ < κs j) :
    (Hypergraph.sigma H).HasChromatic κ := by
  constructor;
  · obtain ⟨c, hc⟩ : ∃ c : (Σ j, W j) → κ.out, (Hypergraph.sigma H).ProperColoring c := by
      obtain ⟨c, hc⟩ : ∃ c : (Σ j, W j) → κ.out, ∀ j, ∀ e ∈ (H j).edges, ∃ u ∈ e, ∃ v ∈ e, c ⟨j, u⟩ ≠ c ⟨j, v⟩ := by
        have h_coloring : ∀ j, ∃ c : W j → κ.out, ∀ e ∈ (H j).edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v := by
          intro j
          obtain ⟨c, hc⟩ := (hchr j).left
          have h_colorable : (H j).ColorableBy κ := by
            grind +suggestions
          generalize_proofs at *; (
          obtain ⟨ c, hc ⟩ := h_colorable; use c; aesop;);
        choose c hc using h_coloring;
        exact ⟨ fun ⟨ j, u ⟩ => c j u, fun j e he => hc j e he ⟩;
      use c;
      intro e he; obtain ⟨ j, t, ht, rfl ⟩ := he; specialize hc j t ht; aesop;
    exact ⟨ c, hc ⟩;
  · intro θ hθ hcolorable
    obtain ⟨j, hj⟩ := hcof θ hθ
    have hcolorable_j : (H j).ColorableBy θ := by
      obtain ⟨ c, hc ⟩ := hcolorable;
      use fun w => c ⟨j, w⟩;
      intro e he; specialize hc ( Sigma.mk j '' e ) ; simp_all +decide only [ne_eq] ;
      exact hc ⟨ j, e, he, by aesop ⟩
    exact (hchr j).right θ hj hcolorable_j

/-! ### The two cases -/

/-- **Successor case** (`thm:successor-linear`): for infinite `μ`, there is a
linear triple system of chromatic number exactly `κ = μ⁺`. -/
theorem successor_linear (h3 : E3_EGH_P.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic (Order.succ μ) := by
  obtain ⟨D⟩ := exists_calibData h3 μ hμ
  exact ⟨_, D.L, D.L_isTripleSystem, D.L_linear, D.L_colorable, D.L_lower⟩

/-- **The §6 reservoir recursion, fully discharged** (`cor:all-linear`): from the
Erdős–Galvin–Hajnal property-`P` input `E3`, for every uncountable cardinal `κ`
there is a linear triple system of chromatic number exactly `κ`. -/
theorem allLinearExists_of_E3 (h3 : E3_EGH_P.{u}) : AllLinearExists.{u} := by
  intro κ hκ
  by_cases hsucc : ∃ ν : Cardinal.{u}, κ = Order.succ ν
  · -- successor case
    obtain ⟨ν, rfl⟩ := hsucc
    have hν : ℵ₀ ≤ ν := by
      by_contra h
      push_neg at h
      exact absurd (Order.succ_le_of_lt h) (not_le.mpr hκ)
    obtain ⟨W, H, htri, hlin, hchr⟩ := successor_linear h3 ν hν
    exact ⟨W, H, htri, hlin, hchr⟩
  · -- limit case
    push_neg at hsucc
    -- choose, for each level `α < κ.ord`, an uncountable successor `ν_α⁺ < κ`
    -- with `α < (ν_α⁺).ord`
    have hpick : ∀ a : κ.ord.ToType,
        ∃ ν : Cardinal.{u}, ℵ₀ ≤ ν ∧ Order.succ ν < κ ∧
          Ordinal.typein (α := κ.ord.ToType) (· < ·) a < (Order.succ ν).ord := by
      intro a
      exact successors_cofinal κ hκ hsucc _ (Ordinal.typein_lt_self a)
    choose ν hνℵ hνlt hνrk using hpick
    -- the family of successor systems
    have hcomp : ∀ a : κ.ord.ToType, ∃ (W : Type u) (H : Hypergraph W),
        H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic (Order.succ (ν a)) :=
      fun a => successor_linear h3 (ν a) (hνℵ a)
    choose W H htri hlin hchr using hcomp
    refine ⟨Σ a : κ.ord.ToType, W a, Hypergraph.sigma H,
      Hypergraph.sigma_isTripleSystem H htri, Hypergraph.sigma_linear H hlin,
      Hypergraph.sigma_hasChromatic H κ (fun a => Order.succ (ν a)) hchr
        (fun a => le_of_lt (hνlt a)) ?_⟩
    -- cofinality: every θ < κ is exceeded by some κs a = ν_a⁺
    intro θ hθ
    have hθord : θ.ord < κ.ord := (Cardinal.ord_lt_ord).mpr hθ
    refine ⟨Ordinal.enum (α := κ.ord.ToType) (· < ·)
      ⟨θ.ord, by rw [Ordinal.type_toType]; exact hθord ⟩, ?_⟩
    have hrk := hνrk (Ordinal.enum (α := κ.ord.ToType) (· < ·)
      ⟨θ.ord, by rw [Ordinal.type_toType]; exact hθord⟩)
    rw [Ordinal.typein_enum] at hrk
    exact (Cardinal.ord_lt_ord).mp hrk

/-! ### Headline results with the §6 reservoir recursion discharged

With `allLinearExists_of_E3` the §6 output `AllLinearExists` is no longer carried
as a hypothesis: it is derived from the genuine external Erdős–Galvin–Hajnal
input `E3_EGH_P`.  The following restate the headline resolutions depending only
on the external interface theorems `ReiherExpansion` (= E4), `E3_EGH_P` (= E3),
and `E2_EH_oddgirth` (= E2). -/

/-- **Resolution of Erdős Problem #593** with the §6 reservoir recursion
discharged (depending only on the external theorems E4, E3, E2). -/
theorem classification_of_E3 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_of hexp (allLinearExists_of_E3 h3) hE2 F

/-- **Exact-spectrum dichotomy** with the §6 reservoir recursion discharged. -/
theorem spectrum_dichotomy_of_E3 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_of hexp (allLinearExists_of_E3 h3) hE2 F lam

/-- **Erdős Problem #1177, part (3)** with the §6 reservoir recursion discharged. -/
theorem problem_1177_part3_of_E3 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_of hexp (allLinearExists_of_E3 h3) hE2 G kappa hk h lam hlam

end Erdos1177
