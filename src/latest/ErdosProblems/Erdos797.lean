/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 797.
https://www.erdosproblems.com/forum/thread/797

Informal authors:
- Noga Alon
- Colin McDiarmid
- Bruce Reed

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos797.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 797.
https://www.erdosproblems.com/latex/797

Informal authors:
- Noga Alon
- Colin McDiarmid
- Bruce Reed

Formal authors:
- OpenAI Codex

The detailed mathematical reconstruction is in `tex/797.tex`.
-/

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Lemmas

namespace Erdos797

noncomputable section

open scoped BigOperators
open Finset Function Set

/-! ## Acyclic colorings and the extremal function -/

/-- A vertex coloring is acyclic when it is proper and no graph-theoretic cycle
uses only two colors.  The last clause deliberately quantifies over two colors
which may coincide; properness makes that harmless. -/
def IsAcyclicColoring {V C : Type*} (G : SimpleGraph V) (c : V → C) : Prop :=
  (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) ∧
    ∀ ⦃v⦄ (w : G.Walk v v), w.IsCycle →
      ¬ ∃ a b : C, ∀ u ∈ w.support, c u = a ∨ c u = b

namespace IsAcyclicColoring

theorem comp_injective {V C D : Type*} {G : SimpleGraph V} {c : V → C}
    (hc : IsAcyclicColoring G c) {e : C → D} (he : Injective e) :
    IsAcyclicColoring G (e ∘ c) := by
  constructor
  · intro u v huv h
    exact hc.1 huv (he h)
  · intro v w hw htwo
    obtain ⟨a, b, hab⟩ := htwo
    have ha : ∀ u ∈ w.support, e (c u) = a ∨ e (c u) = b := by
      simpa [Function.comp_apply] using hab
    let u₀ := w.getVert 0
    have hu₀ : u₀ ∈ w.support := w.getVert_mem_support 0
    rcases ha u₀ hu₀ with hca | hcb
    · by_cases hb : ∃ z, e z = b
      · obtain ⟨z, hz⟩ := hb
        apply hc.2 w hw
        refine ⟨c u₀, z, fun u hu ↦ ?_⟩
        rcases ha u hu with hu' | hu'
        · exact Or.inl (he (hu'.trans hca.symm))
        · exact Or.inr (he (hu'.trans hz.symm))
      · apply hc.2 w hw
        refine ⟨c u₀, c u₀, fun u hu ↦ Or.inl ?_⟩
        rcases ha u hu with hu' | hu'
        · exact he (hu'.trans hca.symm)
        · exact (hb ⟨c u, hu'⟩).elim
    · by_cases ha' : ∃ z, e z = a
      · obtain ⟨z, hz⟩ := ha'
        apply hc.2 w hw
        refine ⟨z, c u₀, fun u hu ↦ ?_⟩
        rcases ha u hu with hu' | hu'
        · exact Or.inl (he (hu'.trans hz.symm))
        · exact Or.inr (he (hu'.trans hcb.symm))
      · apply hc.2 w hw
        refine ⟨c u₀, c u₀, fun u hu ↦ Or.inl ?_⟩
        rcases ha u hu with hu' | hu'
        · exact (ha' ⟨c u, hu'⟩).elim
        · exact he (hu'.trans hcb.symm)

theorem of_injective {V C : Type*} {G : SimpleGraph V} {c : V → C}
    (hc : Injective c) : IsAcyclicColoring G c := by
  constructor
  · intro u v huv h
    exact huv.ne (hc h)
  · intro v w hw
    rintro ⟨a, b, hab⟩
    have hlen : 3 ≤ w.length := hw.three_le_length
    let u₀ := w.getVert 0
    let u₁ := w.getVert 1
    let u₂ := w.getVert 2
    have h₀ := hab u₀ (w.getVert_mem_support 0)
    have h₁ := hab u₁ (w.getVert_mem_support 1)
    have h₂ := hab u₂ (w.getVert_mem_support 2)
    have hadj₀₁ : G.Adj u₀ u₁ := w.adj_getVert_succ (by omega)
    have hadj₁₂ : G.Adj u₁ u₂ := w.adj_getVert_succ (by omega)
    have hne₀₂ : u₀ ≠ u₂ := by
      intro h
      have := hw.getVert_injOn'
        (show 0 ≤ w.length - 1 by omega) (show 2 ≤ w.length - 1 by omega) h
      omega
    have hcne₀₁ : c u₀ ≠ c u₁ := fun h ↦ hadj₀₁.ne (hc h)
    have hcne₁₂ : c u₁ ≠ c u₂ := fun h ↦ hadj₁₂.ne (hc h)
    have hcne₀₂ : c u₀ ≠ c u₂ := fun h ↦ hne₀₂ (hc h)
    rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    all_goals simp_all

end IsAcyclicColoring

/-- `AcyclicBound d k` says that every finite simple graph of maximum degree at
most `d` has an acyclic coloring from a palette of exactly `k` available colors. -/
noncomputable def graphMaxDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.maxDegree

def AcyclicBound (d k : ℕ) : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), graphMaxDegree G ≤ d →
    ∃ c : Fin n → Fin k, IsAcyclicColoring G c

lemma AcyclicBound.mono_colors {d k l : ℕ} (h : AcyclicBound d k) (hkl : k ≤ l) :
    AcyclicBound d l := by
  intro n G hG
  obtain ⟨c, hc⟩ := h n G hG
  exact ⟨Fin.castLE hkl ∘ c, hc.comp_injective (Fin.castLE_injective hkl)⟩

lemma AcyclicBound.anti_degree {d e k : ℕ} (h : AcyclicBound e k) (hde : d ≤ e) :
    AcyclicBound d k := by
  intro n G hG
  exact h n G (hG.trans hde)

/-- The extremal acyclic chromatic function from Problem 797, characterized as
the least universal palette size for maximum degree at most `d`. -/
noncomputable def extremalAcyclicNumber (d : ℕ) : ℕ :=
  sInf {k : ℕ | AcyclicBound d k}

notation "f₇₉₇" => extremalAcyclicNumber

lemma extremalAcyclicNumber_le {d k : ℕ} (h : AcyclicBound d k) : f₇₉₇ d ≤ k :=
  Nat.sInf_le h

/-! ## Exact independence for finite product spaces -/

/-- A predicate on colorings is determined by `S` if changing coordinates
outside `S` cannot change its truth value. -/
def DeterminedBy {V C : Type*} (A : (V → C) → Prop) (S : Finset V) : Prop :=
  ∀ ⦃ω ω' : V → C⦄, (∀ v ∈ S, ω v = ω' v) → (A ω ↔ A ω')

/-- Under the uniform counting measure on a finite function space, predicates
depending on disjoint coordinate sets are independent.  The conclusion is the
cross-multiplied cardinality identity, so no division or probability API is
needed. -/
theorem cylinder_independent
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Nonempty C]
    (A B : (V → C) → Prop) (S T : Finset V)
    [DecidablePred A] [DecidablePred B]
    (hA : DeterminedBy A S) (hB : DeterminedBy B T) (hST : Disjoint S T) :
    Fintype.card {ω : V → C // A ω ∧ B ω} * Fintype.card (V → C) =
      Fintype.card {ω : V → C // A ω} * Fintype.card {ω : V → C // B ω} := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun v : V ↦ v ∈ S) (fun _ ↦ C)
  let L := (v : {v : V // v ∈ S}) → C
  let R := (v : {v : V // v ∉ S}) → C
  let l₀ : L := fun _ ↦ Classical.choice inferInstance
  let r₀ : R := fun _ ↦ Classical.choice inferInstance
  let PA : L → Prop := fun l ↦ A (e.symm (l, r₀))
  let PB : R → Prop := fun r ↦ B (e.symm (l₀, r))
  have hAe : ∀ ω : V → C, A ω ↔ PA (e ω).1 := by
    intro ω
    apply hA
    intro v hv
    change ω v = if h : v ∈ S then ω v else r₀ ⟨v, h⟩
    simp [hv]
  have hBe : ∀ ω : V → C, B ω ↔ PB (e ω).2 := by
    intro ω
    apply hB
    intro v hv
    have hvS : v ∉ S := fun hvS ↦ Finset.disjoint_left.mp hST hvS hv
    change ω v = if h : v ∈ S then l₀ ⟨v, h⟩ else ω v
    simp [hvS]
  let eAB₀ : {ω : V → C // A ω ∧ B ω} ≃ {z : L × R // PA z.1 ∧ PB z.2} :=
    Equiv.subtypeEquiv e (fun ω ↦ by rw [← hAe, ← hBe])
  let eAB₁ : {z : L × R // PA z.1 ∧ PB z.2} ≃
      {l : L // PA l} × {r : R // PB r} :=
    { toFun := fun z ↦ (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
      invFun := fun z ↦ ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  let eA₀ : {ω : V → C // A ω} ≃ {z : L × R // PA z.1} :=
    Equiv.subtypeEquiv e hAe
  let eA₁ : {z : L × R // PA z.1} ≃ {l : L // PA l} × R :=
    { toFun := fun z ↦ (⟨z.1.1, z.2⟩, z.1.2)
      invFun := fun z ↦ ⟨(z.1.1, z.2), z.1.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  let eB₀ : {ω : V → C // B ω} ≃ {z : L × R // PB z.2} :=
    Equiv.subtypeEquiv e hBe
  let eB₁ : {z : L × R // PB z.2} ≃ L × {r : R // PB r} :=
    { toFun := fun z ↦ (z.1.1, ⟨z.1.2, z.2⟩)
      invFun := fun z ↦ ⟨(z.1, z.2.1), z.2.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hAB := Fintype.card_congr (eAB₀.trans eAB₁)
  have hAcard := Fintype.card_congr (eA₀.trans eA₁)
  have hBcard := Fintype.card_congr (eB₀.trans eB₁)
  have hAll := Fintype.card_congr e
  simp only [Fintype.card_prod] at hAB hAcard hBcard hAll
  rw [hAB, hAll, hAcard, hBcard]
  ring

/-! ## A finite cardinality form of the variable local lemma -/

section FiniteLocalLemma

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Nonempty Ω]

/-- The assignments avoiding every event indexed by `S`. -/
noncomputable def avoid (bad : ι → Ω → Prop) (S : Finset ι) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω ↦ ∀ i ∈ S, ¬bad i ω

/-- The assignments in event `i` which avoid every event indexed by `S`. -/
noncomputable def restricted (bad : ι → Ω → Prop) (i : ι) (S : Finset ι) : Finset Ω := by
  classical
  exact (avoid bad S).filter (bad i)

@[simp] lemma mem_avoid {bad : ι → Ω → Prop} {S : Finset ι} {ω : Ω} :
    ω ∈ avoid bad S ↔ ∀ i ∈ S, ¬bad i ω := by
  classical
  simp [avoid]

@[simp] lemma mem_restricted {bad : ι → Ω → Prop} {i : ι} {S : Finset ι} {ω : Ω} :
    ω ∈ restricted bad i S ↔ bad i ω ∧ ∀ j ∈ S, ¬bad j ω := by
  classical
  simp [restricted, and_comm]

lemma restricted_eq_empty_of_mem {bad : ι → Ω → Prop} {i : ι} {S : Finset ι}
    (hi : i ∈ S) : restricted bad i S = ∅ := by
  classical
  ext ω
  simp only [mem_restricted, Finset.notMem_empty, iff_false, not_and]
  exact fun hbad havoid ↦ havoid i hi hbad

lemma restricted_mono {bad : ι → Ω → Prop} {i : ι} {S T : Finset ι}
    (hTS : T ⊆ S) : restricted bad i S ⊆ restricted bad i T := by
  classical
  intro ω hω
  simp only [mem_restricted] at hω ⊢
  exact ⟨hω.1, fun j hj ↦ hω.2 j (hTS hj)⟩

lemma avoid_insert_card_add_restricted_card (bad : ι → Ω → Prop) (i : ι) (S : Finset ι) :
    (avoid bad (insert i S)).card + (restricted bad i S).card = (avoid bad S).card := by
  classical
  have hins : avoid bad (insert i S) =
      (avoid bad S).filter fun ω ↦ ¬bad i ω := by
    ext ω
    simp [and_comm]
  rw [hins, restricted]
  simpa using (avoid bad S).card_filter_add_card_filter_not (fun ω ↦ ¬bad i ω)

/-- Nonsymmetric finite local lemma in a multiplicative cardinality form.

`indep` is exactly the independence equation needed in the standard proof: event
`i` is independent of avoiding any family consisting entirely of non-neighbors.
The use of finite cardinalities keeps this theorem independent of measure theory. -/
theorem finite_local_lemma
    (bad : ι → Ω → Prop) (neighbor : ι → Finset ι) (y : ι → ℝ)
    (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, y i < 1)
    (hmass : ∀ i,
      ((restricted bad i ∅).card : ℝ) ≤
        y i * (∏ j ∈ neighbor i, (1 - y j)) * Fintype.card Ω)
    (indep : ∀ i T, (∀ j ∈ T, j ∉ neighbor i) →
      ((restricted bad i T).card : ℝ) * Fintype.card Ω =
        ((restricted bad i ∅).card : ℝ) * (avoid bad T).card) :
    ∃ ω : Ω, ∀ i, ¬bad i ω := by
  classical
  have hclaim : ∀ S : Finset ι, ∀ i,
      ((restricted bad i S).card : ℝ) ≤ y i * (avoid bad S).card := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro i
      by_cases hiS : i ∈ S
      · rw [restricted_eq_empty_of_mem hiS]
        simpa using mul_nonneg (hy0 i) (Nat.cast_nonneg (avoid bad S).card)
      · let T := S.filter fun j ↦ j ∉ neighbor i
        let U := S.filter fun j ↦ j ∈ neighbor i
        have hTsub : T ⊆ S := Finset.filter_subset _ _
        have hUsub : U ⊆ S := Finset.filter_subset _ _
        have hTU : T ∪ U = S := by
          ext j
          simp [T, U]
          tauto
        have hdisj : Disjoint T U := by
          refine Finset.disjoint_left.mpr ?_
          intro j hjT hjU
          simp [T] at hjT
          simp [U] at hjU
          exact hjT.2 hjU.2
        have hTnon : ∀ j ∈ T, j ∉ neighbor i := by
          intro j hj
          exact (Finset.mem_filter.mp hj).2
        have hchain :
            (∏ j ∈ U, (1 - y j)) * ((avoid bad T).card : ℝ) ≤
              (avoid bad (T ∪ U)).card := by
          have haux : ∀ U' : Finset ι, U' ⊆ U →
              (∏ j ∈ U', (1 - y j)) * ((avoid bad T).card : ℝ) ≤
                (avoid bad (T ∪ U')).card := by
            intro U'
            induction U' using Finset.induction_on with
            | empty => simp
            | @insert j U' hjU' hrec =>
              intro hsub
              have hjU : j ∈ U := hsub (Finset.mem_insert_self _ _)
              have hU'sub : U' ⊆ U := fun z hz ↦ hsub (Finset.mem_insert_of_mem hz)
              have hprev := hrec hU'sub
              have hjS : j ∈ S := hUsub hjU
              have hjT : j ∉ T := by
                intro hj
                exact (Finset.disjoint_left.mp hdisj) hj hjU
              have hjprev : j ∉ T ∪ U' := by
                simp only [Finset.mem_union, not_or]
                exact ⟨hjT, hjU'⟩
              have hproper : T ∪ U' ⊂ S := by
                refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
                · intro z hz
                  rcases Finset.mem_union.mp hz with hz | hz
                  · exact hTsub hz
                  · exact hUsub (hU'sub hz)
                · intro heq
                  exact hjprev (heq ▸ hjS)
              have hsmall := ih (T ∪ U') hproper j
              have hcard := avoid_insert_card_add_restricted_card bad j (T ∪ U')
              have hcardR :
                  ((avoid bad (insert j (T ∪ U'))).card : ℝ) +
                      (restricted bad j (T ∪ U')).card =
                    (avoid bad (T ∪ U')).card := by
                exact_mod_cast hcard
              have hstep :
                  (1 - y j) * ((avoid bad (T ∪ U')).card : ℝ) ≤
                    (avoid bad (insert j (T ∪ U'))).card := by
                nlinarith [hsmall]
              rw [Finset.prod_insert hjU', show T ∪ insert j U' =
                insert j (T ∪ U') by ext; simp]
              calc
                (1 - y j) * (∏ x ∈ U', (1 - y x)) * (avoid bad T).card =
                    (1 - y j) *
                      ((∏ x ∈ U', (1 - y x)) * (avoid bad T).card) := by ring
                _ ≤ (1 - y j) * (avoid bad (T ∪ U')).card := by
                  exact mul_le_mul_of_nonneg_left hprev (sub_nonneg.mpr (hy1 j).le)
                _ ≤ (avoid bad (insert j (T ∪ U'))).card := hstep
          exact haux U (fun _ ↦ id)
        rw [hTU] at hchain
        have hrest : restricted bad i S ⊆ restricted bad i T :=
          restricted_mono hTsub
        have hcardrest :
            ((restricted bad i S).card : ℝ) ≤ (restricted bad i T).card := by
          exact_mod_cast Finset.card_le_card hrest
        have hind := indep i T hTnon
        have hΩpos : (0 : ℝ) < Fintype.card Ω := by
          exact_mod_cast Fintype.card_pos
        have hbadT :
            ((restricted bad i T).card : ℝ) ≤
              y i * (∏ j ∈ neighbor i, (1 - y j)) * (avoid bad T).card := by
          have hmul := calc
              ((restricted bad i T).card : ℝ) * Fintype.card Ω =
                  ((restricted bad i ∅).card : ℝ) * (avoid bad T).card := hind
              _ ≤ (y i * (∏ j ∈ neighbor i, (1 - y j)) * Fintype.card Ω) *
                    (avoid bad T).card := by
                exact mul_le_mul_of_nonneg_right (hmass i) (Nat.cast_nonneg _)
              _ = (y i * (∏ j ∈ neighbor i, (1 - y j)) *
                    (avoid bad T).card) * Fintype.card Ω := by ring
          by_contra hnot
          have hlt : y i * (∏ j ∈ neighbor i, (1 - y j)) *
                (avoid bad T).card < (restricted bad i T).card := lt_of_not_ge hnot
          exact (not_lt_of_ge hmul) (mul_lt_mul_of_pos_right hlt hΩpos)
        have hprodmono :
            (∏ j ∈ neighbor i, (1 - y j)) ≤ ∏ j ∈ U, (1 - y j) := by
          apply Finset.prod_le_prod_of_subset_of_le_one
          · intro j hj
            exact (Finset.mem_filter.mp hj).2
          · intro j hj
            exact sub_nonneg.mpr (hy1 j).le
          · intro j hjN hjU
            linarith [hy0 j]
        calc
          ((restricted bad i S).card : ℝ) ≤ (restricted bad i T).card := hcardrest
          _ ≤ y i * (∏ j ∈ neighbor i, (1 - y j)) * (avoid bad T).card := hbadT
          _ ≤ y i * (∏ j ∈ U, (1 - y j)) * (avoid bad T).card := by
            gcongr
            exact hy0 i
          _ ≤ y i * (avoid bad S).card := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hchain (hy0 i)
  have hpositive : (0 : ℝ) < (avoid bad Finset.univ).card := by
    have haux : ∀ S : Finset ι,
        (∏ i ∈ S, (1 - y i)) * Fintype.card Ω ≤ (avoid bad S).card := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [avoid]
      | @insert i S hi hS =>
        have hc := hclaim S i
        have hcard := avoid_insert_card_add_restricted_card bad i S
        have hcardR :
            ((avoid bad (insert i S)).card : ℝ) + (restricted bad i S).card =
              (avoid bad S).card := by
          exact_mod_cast hcard
        have hstep :
            (1 - y i) * ((avoid bad S).card : ℝ) ≤
              (avoid bad (insert i S)).card := by
          nlinarith [hc]
        rw [Finset.prod_insert hi]
        calc
          (1 - y i) * (∏ j ∈ S, (1 - y j)) * Fintype.card Ω =
              (1 - y i) * ((∏ j ∈ S, (1 - y j)) * Fintype.card Ω) := by ring
          _ ≤ (1 - y i) * (avoid bad S).card := by
            exact mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr (hy1 i).le)
          _ ≤ (avoid bad (insert i S)).card := hstep
    have hprodpos : 0 < ∏ i : ι, (1 - y i) :=
      Finset.prod_pos fun i _ ↦ sub_pos.mpr (hy1 i)
    have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    exact (mul_pos hprodpos hΩ).trans_le (haux Finset.univ)
  have hnonempty : (avoid bad Finset.univ).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hpositive)
  obtain ⟨ω, hω⟩ := hnonempty
  exact ⟨ω, fun i ↦ (mem_avoid.mp hω) i (Finset.mem_univ i)⟩

/-- Avoiding a finite family of cylinder events is determined by the union of
their coordinate supports. -/
lemma determined_avoid
    {V C : Type*} [DecidableEq V]
    (bad : ι → (V → C) → Prop) (support : ι → Finset V)
    (hdet : ∀ i, DeterminedBy (bad i) (support i)) (T : Finset ι) :
    DeterminedBy (fun ω ↦ ∀ i ∈ T, ¬bad i ω) (T.biUnion support) := by
  classical
  intro ω ω' hagree
  constructor
  · intro havoid i hi hbad'
    have hcoord : ∀ v ∈ support i, ω v = ω' v := by
      intro v hv
      exact hagree v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
    exact havoid i hi ((hdet i hcoord).mpr hbad')
  · intro havoid i hi hbad
    have hcoord : ∀ v ∈ support i, ω v = ω' v := by
      intro v hv
      exact hagree v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
    exact havoid i hi ((hdet i hcoord).mp hbad)

/-- The overlap neighbor finset associated to a family of finite coordinate
supports.  Including an event itself is harmless and simplifies the definition. -/
noncomputable def overlapNeighbors {V : Type*} [DecidableEq V]
    (support : ι → Finset V) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun j ↦ ¬Disjoint (support i) (support j)

/-- The exact independence equation required by `finite_local_lemma` follows
automatically when non-neighbors have disjoint coordinate supports. -/
lemma restricted_independent_of_support
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Nonempty C]
    (bad : ι → (V → C) → Prop) (support : ι → Finset V)
    (hdet : ∀ i, DeterminedBy (bad i) (support i)) :
    ∀ i T, (∀ j ∈ T, j ∉ overlapNeighbors support i) →
      ((restricted bad i T).card : ℝ) * Fintype.card (V → C) =
        ((restricted bad i ∅).card : ℝ) * (avoid bad T).card := by
  classical
  intro i T hnon
  let B : (V → C) → Prop := fun ω ↦ ∀ j ∈ T, ¬bad j ω
  have hdisj : Disjoint (support i) (T.biUnion support) := by
    rw [Finset.disjoint_left]
    intro v hvi hvT
    obtain ⟨j, hjT, hvj⟩ := Finset.mem_biUnion.mp hvT
    have hj := hnon j hjT
    have hij : Disjoint (support i) (support j) := by
      simpa [overlapNeighbors] using hj
    exact Finset.disjoint_left.mp hij hvi hvj
  have hcyl := cylinder_independent (bad i) B (support i) (T.biUnion support)
    (hdet i) (determined_avoid bad support hdet T) hdisj
  have hIT : Fintype.card {ω : V → C // bad i ω ∧ B ω} =
      (restricted bad i T).card := by
    apply Fintype.card_of_subtype
    intro ω
    simp [B]
  have hI : Fintype.card {ω : V → C // bad i ω} =
      (restricted bad i ∅).card := by
    apply Fintype.card_of_subtype
    intro ω
    simp
  have hT : Fintype.card {ω : V → C // B ω} = (avoid bad T).card := by
    apply Fintype.card_of_subtype
    intro ω
    simp [B]
  rw [hIT, hI, hT] at hcyl
  exact_mod_cast hcyl

end FiniteLocalLemma

/-! ## The Alon--McDiarmid--Reed bad events -/

namespace UpperBound

/-- The four event families in the AMR upper-bound proof. -/
inductive BadIndex (V : Type*) where
  | edge (u v : V)
  | path (v0 v1 v2 v3 v4 : V)
  | square (v0 v1 v2 v3 : V)
  | special (u v : V)
  deriving DecidableEq

/-- A sum-of-products presentation used to furnish the finite event index and
later to split sums and counting arguments by event type. -/
abbrev BadIndex.Data (V : Type*) :=
  (V × V) ⊕ (V × V × V × V × V) ⊕ (V × V × V × V) ⊕ (V × V)

def BadIndex.equivData {V : Type*} : BadIndex V ≃ BadIndex.Data V where
  toFun
    | .edge u v => Sum.inl (u, v)
    | .path v0 v1 v2 v3 v4 => Sum.inr (Sum.inl (v0, v1, v2, v3, v4))
    | .square v0 v1 v2 v3 => Sum.inr (Sum.inr (Sum.inl (v0, v1, v2, v3)))
    | .special u v => Sum.inr (Sum.inr (Sum.inr (u, v)))
  invFun
    | Sum.inl (u, v) => .edge u v
    | Sum.inr (Sum.inl (v0, v1, v2, v3, v4)) => .path v0 v1 v2 v3 v4
    | Sum.inr (Sum.inr (Sum.inl (v0, v1, v2, v3))) => .square v0 v1 v2 v3
    | Sum.inr (Sum.inr (Sum.inr (u, v))) => .special u v
  left_inv := by intro i; cases i <;> rfl
  right_inv := by
    intro x
    rcases x with x | x
    · rcases x with ⟨u, v⟩
      rfl
    · rcases x with x | x
      · rcases x with ⟨v0, v1, v2, v3, v4⟩
        rfl
      · rcases x with x | x
        · rcases x with ⟨v0, v1, v2, v3⟩
          rfl
        · rcases x with ⟨u, v⟩
          rfl

noncomputable instance {V : Type*} [Fintype V] : Fintype (BadIndex V) :=
  Fintype.ofEquiv (BadIndex.Data V) BadIndex.equivData.symm

def BadIndex.support {V : Type*} [DecidableEq V] : BadIndex V → Finset V
  | .edge u v => {u, v}
  | .path v0 v1 v2 v3 v4 => {v0, v1, v2, v3, v4}
  | .square v0 v1 v2 v3 => {v0, v1, v2, v3}
  | .special u v => {u, v}

noncomputable def commonNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact G.neighborFinset u ∩ G.neighborFinset v

/-- The AMR threshold is `r²`: a pair is special when it has more than that
many common neighbors. -/
def IsSpecial {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (u v : V) : Prop :=
  r ^ 2 < (commonNeighbors G u v).card

def BadIndex.Valid {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) : BadIndex V → Prop
  | .edge u v => u < v ∧ G.Adj u v
  | .path v0 v1 v2 v3 v4 =>
      ({v0, v1, v2, v3, v4} : Finset V).card = 5 ∧
        G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v4
  | .square v0 v1 v2 v3 =>
      ({v0, v1, v2, v3} : Finset V).card = 4 ∧
        G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v0 ∧
        ¬IsSpecial G r v0 v2 ∧ ¬IsSpecial G r v1 v3
  | .special u v => u < v ∧ IsSpecial G r u v

def BadIndex.occurs {V C : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (i : BadIndex V) (color : V → C) : Prop :=
  i.Valid G r ∧ match i with
    | .edge u v => color u = color v
    | .path v0 v1 v2 v3 v4 =>
        color v0 = color v2 ∧ color v2 = color v4 ∧ color v1 = color v3
    | .square v0 v1 v2 v3 => color v0 = color v2 ∧ color v1 = color v3
    | .special u v => color u = color v

theorem BadIndex.occurs_determined {V C : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (i : BadIndex V) :
    DeterminedBy (i.occurs G r : (V → C) → Prop) i.support := by
  classical
  intro color color' hagree
  cases i with
  | edge u v =>
      have hu := hagree u (by simp [BadIndex.support])
      have hv := hagree v (by simp [BadIndex.support])
      simp [BadIndex.occurs, hu, hv]
  | path v0 v1 v2 v3 v4 =>
      have h0 := hagree v0 (by simp [BadIndex.support])
      have h1 := hagree v1 (by simp [BadIndex.support])
      have h2 := hagree v2 (by simp [BadIndex.support])
      have h3 := hagree v3 (by simp [BadIndex.support])
      have h4 := hagree v4 (by simp [BadIndex.support])
      simp [BadIndex.occurs, h0, h1, h2, h3, h4]
  | square v0 v1 v2 v3 =>
      have h0 := hagree v0 (by simp [BadIndex.support])
      have h1 := hagree v1 (by simp [BadIndex.support])
      have h2 := hagree v2 (by simp [BadIndex.support])
      have h3 := hagree v3 (by simp [BadIndex.support])
      simp [BadIndex.occurs, h0, h1, h2, h3]
  | special u v =>
      have hu := hagree u (by simp [BadIndex.support])
      have hv := hagree v (by simp [BadIndex.support])
      simp [BadIndex.occurs, hu, hv]

lemma isSpecial_comm {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (u v : V) :
    IsSpecial G r u v ↔ IsSpecial G r v u := by
  classical
  simp [IsSpecial, commonNeighbors, Finset.inter_comm]

private lemma cycle_getVert_ne {V : Type*}
    {G : SimpleGraph V} {u : V}
    {w : G.Walk u u} (hw : w.IsCycle) {i j : ℕ}
    (hi : i ≤ w.length - 1) (hj : j ≤ w.length - 1) (hij : i ≠ j) :
    w.getVert i ≠ w.getVert j := by
  intro h
  exact hij (hw.getVert_injOn' hi hj h)

private lemma cycle_first_four_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u : V}
    {w : G.Walk u u} (hw : w.IsCycle) (hm : 4 ≤ w.length) :
    ({w.getVert 0, w.getVert 1, w.getVert 2, w.getVert 3} : Finset V).card = 4 := by
  have h01 : w.getVert 0 ≠ w.getVert 1 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h02 : w.getVert 0 ≠ w.getVert 2 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h03 : w.getVert 0 ≠ w.getVert 3 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h12 : w.getVert 1 ≠ w.getVert 2 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h13 : w.getVert 1 ≠ w.getVert 3 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h23 : w.getVert 2 ≠ w.getVert 3 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h0 : w.getVert 0 ∉ ({w.getVert 1, w.getVert 2, w.getVert 3} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h01, h02, h03⟩
  have h1 : w.getVert 1 ∉ ({w.getVert 2, w.getVert 3} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h13⟩
  have h2 : w.getVert 2 ∉ ({w.getVert 3} : Finset V) := by
    simpa only [Finset.mem_singleton] using h23
  rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h1,
    Finset.card_insert_of_notMem h2]
  simp

private lemma cycle_first_five_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u : V}
    {w : G.Walk u u} (hw : w.IsCycle) (hm : 5 ≤ w.length) :
    ({w.getVert 0, w.getVert 1, w.getVert 2, w.getVert 3, w.getVert 4} :
      Finset V).card = 5 := by
  have h01 : w.getVert 0 ≠ w.getVert 1 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h02 : w.getVert 0 ≠ w.getVert 2 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h03 : w.getVert 0 ≠ w.getVert 3 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h04 : w.getVert 0 ≠ w.getVert 4 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h12 : w.getVert 1 ≠ w.getVert 2 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h13 : w.getVert 1 ≠ w.getVert 3 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h14 : w.getVert 1 ≠ w.getVert 4 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h23 : w.getVert 2 ≠ w.getVert 3 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h24 : w.getVert 2 ≠ w.getVert 4 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h34 : w.getVert 3 ≠ w.getVert 4 := cycle_getVert_ne hw (by omega) (by omega) (by omega)
  have h0 : w.getVert 0 ∉
      ({w.getVert 1, w.getVert 2, w.getVert 3, w.getVert 4} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h01, h02, h03, h04⟩
  have h1 : w.getVert 1 ∉
      ({w.getVert 2, w.getVert 3, w.getVert 4} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h13, h14⟩
  have h2 : w.getVert 2 ∉ ({w.getVert 3, w.getVert 4} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h23, h24⟩
  have h3 : w.getVert 3 ∉ ({w.getVert 4} : Finset V) := by
    simpa only [Finset.mem_singleton] using h34
  rw [Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h1,
    Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h3]
  simp

/-- Avoidance of the four AMR bad-event families gives a proper coloring with
no bichromatic cycle. -/
theorem acyclic_of_avoid {V C : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (color : V → C)
    (havoid : ∀ i : BadIndex V, ¬i.occurs G r color) :
    IsAcyclicColoring G color := by
  have hproper : ∀ ⦃u v⦄, G.Adj u v → color u ≠ color v := by
    intro u v huv heq
    rcases lt_or_gt_of_ne huv.ne with huvlt | hvult
    · exact havoid (.edge u v) ⟨⟨huvlt, huv⟩, heq⟩
    · exact havoid (.edge v u) ⟨⟨hvult, huv.symm⟩, heq.symm⟩
  constructor
  · exact hproper
  · intro start w hw
    rintro ⟨a, b, hcolors⟩
    by_cases hlen5 : 5 ≤ w.length
    · let v0 := w.getVert 0
      let v1 := w.getVert 1
      let v2 := w.getVert 2
      let v3 := w.getVert 3
      let v4 := w.getVert 4
      have hadj01 : G.Adj v0 v1 := w.adj_getVert_succ (by omega)
      have hadj12 : G.Adj v1 v2 := w.adj_getVert_succ (by omega)
      have hadj23 : G.Adj v2 v3 := w.adj_getVert_succ (by omega)
      have hadj34 : G.Adj v3 v4 := w.adj_getVert_succ (by omega)
      have h0 := hcolors v0 (w.getVert_mem_support 0)
      have h1 := hcolors v1 (w.getVert_mem_support 1)
      have h2 := hcolors v2 (w.getVert_mem_support 2)
      have h3 := hcolors v3 (w.getVert_mem_support 3)
      have h4 := hcolors v4 (w.getVert_mem_support 4)
      have hne01 := hproper hadj01
      have hne12 := hproper hadj12
      have hne23 := hproper hadj23
      have hne34 := hproper hadj34
      have hpattern : color v0 = color v2 ∧ color v2 = color v4 ∧
          color v1 = color v3 := by
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
          rcases h4 with h4 | h4 <;> simp_all
      have hcard : ({v0, v1, v2, v3, v4} : Finset V).card = 5 := by
        simpa [v0, v1, v2, v3, v4] using cycle_first_five_card hw hlen5
      exact havoid (.path v0 v1 v2 v3 v4)
        ⟨⟨hcard, hadj01, hadj12, hadj23, hadj34⟩, hpattern⟩
    · have hlen3 := hw.three_le_length
      by_cases hlen4 : w.length = 4
      · let v0 := w.getVert 0
        let v1 := w.getVert 1
        let v2 := w.getVert 2
        let v3 := w.getVert 3
        have hadj01 : G.Adj v0 v1 := w.adj_getVert_succ (by omega)
        have hadj12 : G.Adj v1 v2 := w.adj_getVert_succ (by omega)
        have hadj23 : G.Adj v2 v3 := w.adj_getVert_succ (by omega)
        have hadj30 : G.Adj v3 v0 := by
          have hlast := w.adj_getVert_succ (i := 3) (by omega)
          have hv4 : w.getVert 4 = start := by simpa [hlen4] using w.getVert_length
          simpa [v0, v3, hv4] using hlast
        have h0 := hcolors v0 (w.getVert_mem_support 0)
        have h1 := hcolors v1 (w.getVert_mem_support 1)
        have h2 := hcolors v2 (w.getVert_mem_support 2)
        have h3 := hcolors v3 (w.getVert_mem_support 3)
        have hne01 := hproper hadj01
        have hne12 := hproper hadj12
        have hne23 := hproper hadj23
        have hpattern : color v0 = color v2 ∧ color v1 = color v3 := by
          rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
            rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all
        have hcard : ({v0, v1, v2, v3} : Finset V).card = 4 := by
          simpa [v0, v1, v2, v3] using cycle_first_four_card hw (by omega)
        have hne02 : v0 ≠ v2 := by
          intro h
          have hi := hw.getVert_injOn'
            (show 0 ≤ w.length - 1 by omega) (show 2 ≤ w.length - 1 by omega) h
          omega
        have hne13 : v1 ≠ v3 := by
          intro h
          have hi := hw.getVert_injOn'
            (show 1 ≤ w.length - 1 by omega) (show 3 ≤ w.length - 1 by omega) h
          omega
        by_cases hs02 : IsSpecial G r v0 v2
        · rcases lt_or_gt_of_ne hne02 with hlt | hgt
          · exact havoid (.special v0 v2) ⟨⟨hlt, hs02⟩, hpattern.1⟩
          · exact havoid (.special v2 v0)
              ⟨⟨hgt, (isSpecial_comm G r v0 v2).mp hs02⟩, hpattern.1.symm⟩
        · by_cases hs13 : IsSpecial G r v1 v3
          · rcases lt_or_gt_of_ne hne13 with hlt | hgt
            · exact havoid (.special v1 v3) ⟨⟨hlt, hs13⟩, hpattern.2⟩
            · exact havoid (.special v3 v1)
                ⟨⟨hgt, (isSpecial_comm G r v1 v3).mp hs13⟩, hpattern.2.symm⟩
          · exact havoid (.square v0 v1 v2 v3)
              ⟨⟨hcard, hadj01, hadj12, hadj23, hadj30, hs02, hs13⟩, hpattern⟩
      · have hlen : w.length = 3 := by omega
        let v0 := w.getVert 0
        let v1 := w.getVert 1
        let v2 := w.getVert 2
        have hadj01 : G.Adj v0 v1 := w.adj_getVert_succ (by omega)
        have hadj12 : G.Adj v1 v2 := w.adj_getVert_succ (by omega)
        have hadj20 : G.Adj v2 v0 := by
          have hlast := w.adj_getVert_succ (i := 2) (by omega)
          have hv3 : w.getVert 3 = start := by simpa [hlen] using w.getVert_length
          simpa [v0, v2, hv3] using hlast
        have h0 := hcolors v0 (w.getVert_mem_support 0)
        have h1 := hcolors v1 (w.getVert_mem_support 1)
        have h2 := hcolors v2 (w.getVert_mem_support 2)
        have hne01 := hproper hadj01
        have hne12 := hproper hadj12
        have hne20 := hproper hadj20
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          rcases h2 with h2 | h2 <;> simp_all

/-! ### Exact cardinalities of the four event patterns -/

/-- A predicate ignores a coordinate if changing only that coordinate cannot
change the predicate's truth value. -/
def IgnoresCoordinate {V C : Type*} (A : (V → C) → Prop) (v : V) : Prop :=
  ∀ ⦃ω ω' : V → C⦄, (∀ z, z ≠ v → ω z = ω' z) → (A ω ↔ A ω')

/-- If `A` ignores `v`, then assignments satisfying `A` and `ω v = ω u`,
together with one free color, are in bijection with assignments satisfying
`A`.  This is the exact finite counting step behind all four AMR event
probabilities. -/
private def forceCoordinateEquiv
    {V C : Type*} [DecidableEq V] (A : (V → C) → Prop) (u v : V)
    (huv : u ≠ v) (hA : IgnoresCoordinate A v) :
    ({ω : V → C // A ω ∧ ω v = ω u} × C) ≃ {ω : V → C // A ω} where
  toFun z :=
    ⟨Function.update z.1.1 v z.2,
      (hA (fun x hx ↦ by simp [hx])).mp z.1.2.1⟩
  invFun z :=
    (⟨Function.update z.1 v (z.1 u),
      (hA (fun x hx ↦ by simp [hx])).mp z.2,
      by simp [huv]⟩, z.1 v)
  left_inv := by
    rintro ⟨⟨ω, hAω, heq⟩, c⟩
    apply Prod.ext
    · apply Subtype.ext
      funext x
      by_cases hx : x = v
      · subst x
        simp [huv, heq]
      · simp [hx]
    · simp
  right_inv := by
    rintro ⟨ω, hAω⟩
    apply Subtype.ext
    funext x
    by_cases hx : x = v
    · subst x
      simp
    · simp [hx]

theorem card_force_eq_mul
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (A : (V → C) → Prop) [DecidablePred A]
    (u v : V) (huv : u ≠ v) (hA : IgnoresCoordinate A v) :
    Fintype.card {ω : V → C // A ω ∧ ω v = ω u} * Fintype.card C =
      Fintype.card {ω : V → C // A ω} := by
  classical
  simpa only [Fintype.card_prod] using
    Fintype.card_congr (forceCoordinateEquiv A u v huv hA)

lemma ignoresCoordinate_true {V C : Type*} (v : V) :
    IgnoresCoordinate (fun _ : V → C ↦ True) v := by
  intro ω ω' h
  simp

lemma ignoresCoordinate_eq {V C : Type*} {a b v : V} (ha : a ≠ v) (hb : b ≠ v) :
    IgnoresCoordinate (fun ω : V → C ↦ ω a = ω b) v := by
  intro ω ω' h
  change (ω a = ω b ↔ ω' a = ω' b)
  rw [h a ha, h b hb]

lemma IgnoresCoordinate.and {V C : Type*} {A B : (V → C) → Prop} {v : V}
    (hA : IgnoresCoordinate A v) (hB : IgnoresCoordinate B v) :
    IgnoresCoordinate (fun ω ↦ A ω ∧ B ω) v := by
  intro ω ω' h
  change (A ω ∧ B ω ↔ A ω' ∧ B ω')
  rw [hA h, hB h]

theorem card_pair_pattern_mul
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    {u v : V} (huv : u ≠ v) :
    Fintype.card {ω : V → C // ω u = ω v} * Fintype.card C =
      Fintype.card (V → C) := by
  classical
  simpa [eq_comm] using
    (card_force_eq_mul (fun _ : V → C ↦ True) u v huv (ignoresCoordinate_true v))

theorem card_square_pattern_mul_sq
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    {v0 v1 v2 v3 : V}
    (h02 : v0 ≠ v2) (h23 : v2 ≠ v3) (h03 : v0 ≠ v3)
    (h13 : v1 ≠ v3) :
    Fintype.card {ω : V → C // ω v0 = ω v2 ∧ ω v1 = ω v3} *
        Fintype.card C ^ 2 = Fintype.card (V → C) := by
  classical
  let P1 : (V → C) → Prop := fun ω ↦ ω v2 = ω v0
  let P2 : (V → C) → Prop := fun ω ↦ P1 ω ∧ ω v3 = ω v1
  have h1 : Fintype.card {ω : V → C // P1 ω} * Fintype.card C =
      Fintype.card (V → C) := by
    simpa [P1] using
      (card_force_eq_mul (fun _ : V → C ↦ True) v0 v2 h02 (ignoresCoordinate_true v2))
  have h2 : Fintype.card {ω : V → C // P2 ω} * Fintype.card C =
      Fintype.card {ω : V → C // P1 ω} := by
    simpa [P2] using card_force_eq_mul P1 v1 v3 h13
      (ignoresCoordinate_eq h23 h03)
  have hpat : Fintype.card {ω : V → C // ω v0 = ω v2 ∧ ω v1 = ω v3} =
      Fintype.card {ω : V → C // P2 ω} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (by
      intro ω
      simp [P1, P2, eq_comm])
  rw [hpat]
  calc
    Fintype.card {ω : V → C // P2 ω} * Fintype.card C ^ 2 =
        (Fintype.card {ω : V → C // P2 ω} * Fintype.card C) *
          Fintype.card C := by ring
    _ = Fintype.card {ω : V → C // P1 ω} * Fintype.card C := by rw [h2]
    _ = Fintype.card (V → C) := h1

theorem card_path_pattern_mul_cube
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    {v0 v1 v2 v3 v4 : V}
    (h02 : v0 ≠ v2) (h23 : v2 ≠ v3) (h03 : v0 ≠ v3) (h13 : v1 ≠ v3)
    (h24 : v2 ≠ v4) (h04 : v0 ≠ v4) (h34 : v3 ≠ v4) (h14 : v1 ≠ v4) :
    Fintype.card {ω : V → C //
        ω v0 = ω v2 ∧ ω v2 = ω v4 ∧ ω v1 = ω v3} *
        Fintype.card C ^ 3 = Fintype.card (V → C) := by
  classical
  let P1 : (V → C) → Prop := fun ω ↦ ω v2 = ω v0
  let P2 : (V → C) → Prop := fun ω ↦ P1 ω ∧ ω v3 = ω v1
  let P3 : (V → C) → Prop := fun ω ↦ P2 ω ∧ ω v4 = ω v2
  have h1 : Fintype.card {ω : V → C // P1 ω} * Fintype.card C =
      Fintype.card (V → C) := by
    simpa [P1] using
      (card_force_eq_mul (fun _ : V → C ↦ True) v0 v2 h02 (ignoresCoordinate_true v2))
  have h2 : Fintype.card {ω : V → C // P2 ω} * Fintype.card C =
      Fintype.card {ω : V → C // P1 ω} := by
    simpa [P2] using card_force_eq_mul P1 v1 v3 h13
      (ignoresCoordinate_eq h23 h03)
  have hP2 : IgnoresCoordinate P2 v4 := by
    apply IgnoresCoordinate.and
    · exact ignoresCoordinate_eq h24 h04
    · exact ignoresCoordinate_eq h34 h14
  have h3 : Fintype.card {ω : V → C // P3 ω} * Fintype.card C =
      Fintype.card {ω : V → C // P2 ω} := by
    simpa [P3] using card_force_eq_mul P2 v2 v4 h24 hP2
  have hpat : Fintype.card {ω : V → C //
        ω v0 = ω v2 ∧ ω v2 = ω v4 ∧ ω v1 = ω v3} =
      Fintype.card {ω : V → C // P3 ω} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (by
      intro ω
      simp [P1, P2, P3, eq_comm, and_comm, and_assoc])
  rw [hpat]
  calc
    Fintype.card {ω : V → C // P3 ω} * Fintype.card C ^ 3 =
        ((Fintype.card {ω : V → C // P3 ω} * Fintype.card C) *
          Fintype.card C) * Fintype.card C := by ring
    _ = (Fintype.card {ω : V → C // P2 ω} * Fintype.card C) *
          Fintype.card C := by rw [h3]
    _ = Fintype.card {ω : V → C // P1 ω} * Fintype.card C := by rw [h2]
    _ = Fintype.card (V → C) := h1

/-- Number of independent color equalities imposed by each AMR event family. -/
def BadIndex.constraintCount {V : Type*} : BadIndex V → ℕ
  | .edge _ _ => 1
  | .path _ _ _ _ _ => 3
  | .square _ _ _ _ => 2
  | .special _ _ => 1

/-- Exact uniform-cardinality bound for every valid event; invalid indices have
empty events.  In probability notation this says that the four event types
have probability at most `x⁻¹`, `x⁻³`, `x⁻²`, and `x⁻¹`. -/
theorem occurs_card_mul_palette_pow_le
    {V C : Type*} [Fintype V] [LinearOrder V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (i : BadIndex V)
    [DecidablePred (i.occurs G r : (V → C) → Prop)] :
    Fintype.card {ω : V → C // i.occurs G r ω} *
        Fintype.card C ^ i.constraintCount ≤ Fintype.card (V → C) := by
  classical
  cases i with
  | edge u v =>
      by_cases hvalid : (BadIndex.edge u v).Valid G r
      · have huv : u ≠ v := ne_of_lt hvalid.1
        have h := (card_pair_pattern_mul (C := C) huv).le
        simpa [BadIndex.occurs, hvalid, BadIndex.constraintCount] using h
      · simp [BadIndex.occurs, hvalid]
  | path v0 v1 v2 v3 v4 =>
      by_cases hvalid : (BadIndex.path v0 v1 v2 v3 v4).Valid G r
      · have hcard := hvalid.1
        have h02 : v0 ≠ v2 := by grind
        have h23 : v2 ≠ v3 := by grind
        have h03 : v0 ≠ v3 := by grind
        have h13 : v1 ≠ v3 := by grind
        have h24 : v2 ≠ v4 := by grind
        have h04 : v0 ≠ v4 := by grind
        have h34 : v3 ≠ v4 := by grind
        have h14 : v1 ≠ v4 := by grind
        have h :=
          (card_path_pattern_mul_cube (C := C) h02 h23 h03 h13 h24 h04 h34 h14).le
        simpa [BadIndex.occurs, hvalid, BadIndex.constraintCount] using h
      · simp [BadIndex.occurs, hvalid]
  | square v0 v1 v2 v3 =>
      by_cases hvalid : (BadIndex.square v0 v1 v2 v3).Valid G r
      · have hcard := hvalid.1
        have h02 : v0 ≠ v2 := by grind
        have h23 : v2 ≠ v3 := by grind
        have h03 : v0 ≠ v3 := by grind
        have h13 : v1 ≠ v3 := by grind
        have h := (card_square_pattern_mul_sq (C := C) h02 h23 h03 h13).le
        simpa [BadIndex.occurs, hvalid, BadIndex.constraintCount] using h
      · simp [BadIndex.occurs, hvalid]
  | special u v =>
      by_cases hvalid : (BadIndex.special u v).Valid G r
      · have huv : u ≠ v := ne_of_lt hvalid.1
        have h := (card_pair_pattern_mul (C := C) huv).le
        simpa [BadIndex.occurs, hvalid, BadIndex.constraintCount] using h
      · simp [BadIndex.occurs, hvalid]

/-! ### Counting bounded-degree paths -/

/-- A sequence of `n` successive neighbor choices starting at `u`.  This
recursive sigma type deliberately forgets the terminal vertex; it is the most
compact finite encoding for the path incidence counts. -/
def ChainsFrom {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (n : ℕ) → V → Type u
  | 0, _ => PUnit.{u + 1}
  | n + 1, u => Σ v : {v : V // v ∈ G.neighborFinset u}, ChainsFrom G n v

noncomputable instance chainsFromFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (u : V) : Fintype (ChainsFrom G n u) := by
  induction n generalizing u with
  | zero =>
      simp only [ChainsFrom]
      infer_instance
  | succ n ih =>
      simp only [ChainsFrom]
      letI (v : {v : V // v ∈ G.neighborFinset u}) :
          Fintype (ChainsFrom G n v.1) := ih v.1
      infer_instance

/-- A maximum-degree bound gives at most `dⁿ` length-`n` neighbor-choice
chains from any fixed vertex. -/
theorem card_chainsFrom_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (n : ℕ) (u : V) :
    Fintype.card (ChainsFrom G n u) ≤ d ^ n := by
  induction n generalizing u with
  | zero => simp [ChainsFrom]
  | succ n ih =>
      rw [show d ^ (n + 1) = d ^ n * d by simp [pow_succ]]
      simp only [ChainsFrom]
      rw [Fintype.card_sigma]
      calc
        (∑ v : {v : V // v ∈ G.neighborFinset u},
            Fintype.card (ChainsFrom G n v.1)) ≤
            ∑ _v : {v : V // v ∈ G.neighborFinset u}, d ^ n := by
          exact Finset.sum_le_sum fun v _ ↦ ih v.1
        _ = d ^ n * G.degree u := by
          simp [SimpleGraph.card_neighborFinset_eq_degree, Nat.mul_comm]
        _ ≤ d ^ n * d := Nat.mul_le_mul_left _ (hdeg u)

/-- An ordered five-vertex tuple used only for incidence counting. -/
structure PathTuple (V : Type*) where
  v0 : V
  v1 : V
  v2 : V
  v3 : V
  v4 : V

def pathTupleEquivData {V : Type*} : PathTuple V ≃ V × V × V × V × V where
  toFun p := (p.v0, p.v1, p.v2, p.v3, p.v4)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨v0, v1, v2, v3, v4⟩; rfl

noncomputable instance {V : Type*} [Fintype V] : Fintype (PathTuple V) :=
  Fintype.ofEquiv (V × V × V × V × V) pathTupleEquivData.symm

def PathTuple.IsWalk {V : Type*} (G : SimpleGraph V) (p : PathTuple V) : Prop :=
  G.Adj p.v0 p.v1 ∧ G.Adj p.v1 p.v2 ∧ G.Adj p.v2 p.v3 ∧ G.Adj p.v3 p.v4

def PathAt0 {V : Type*} (G : SimpleGraph V) (u : V) :=
  {p : PathTuple V // p.IsWalk G ∧ p.v0 = u}

private def pathAt0ToChains
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    PathAt0 G u → ChainsFrom G 4 u := by
  rintro ⟨⟨v0, v1, v2, v3, v4⟩, hw, hv0⟩
  change v0 = u at hv0
  subst v0
  refine ⟨⟨v1, by simpa [PathTuple.IsWalk] using hw.1⟩, ?_⟩
  refine ⟨⟨v2, by simpa [PathTuple.IsWalk] using hw.2.1⟩, ?_⟩
  refine ⟨⟨v3, by simpa [PathTuple.IsWalk] using hw.2.2.1⟩, ?_⟩
  exact ⟨⟨v4, by simpa [PathTuple.IsWalk] using hw.2.2.2⟩, PUnit.unit⟩

private theorem pathAt0ToChains_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Function.Injective (pathAt0ToChains G u) := by
  rintro ⟨⟨v0, v1, v2, v3, v4⟩, hw, hv0⟩
    ⟨⟨w0, w1, w2, w3, w4⟩, hw', hw0⟩ h
  change v0 = u at hv0
  change w0 = u at hw0
  subst v0
  subst w0
  simp only [pathAt0ToChains] at h
  have h1 : v1 = w1 := by exact congrArg (fun z ↦ z.1.1) h
  subst w1
  have h2 : v2 = w2 := by exact congrArg (fun z ↦ z.2.1.1) h
  subst w2
  have h3 : v3 = w3 := by exact congrArg (fun z ↦ z.2.2.1.1) h
  subst w3
  have h4 : v4 = w4 := by exact congrArg (fun z ↦ z.2.2.2.1.1) h
  subst w4
  rfl

theorem card_pathAt0_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (PathAt0 G u) ≤ d ^ 4 := by
  classical
  letI : Finite (PathAt0 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (PathAt0 G u) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (pathAt0ToChains G u)
      (pathAt0ToChains_injective G u)).trans
    (card_chainsFrom_le G hdeg 4 u)

theorem card_chainsFrom_prod_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (p q : ℕ) (u : V) :
    Fintype.card (ChainsFrom G p u × ChainsFrom G q u) ≤ d ^ (p + q) := by
  rw [Fintype.card_prod]
  calc
    Fintype.card (ChainsFrom G p u) * Fintype.card (ChainsFrom G q u) ≤
        d ^ p * d ^ q := Nat.mul_le_mul (card_chainsFrom_le G hdeg p u)
          (card_chainsFrom_le G hdeg q u)
    _ = d ^ (p + q) := (pow_add d p q).symm

def PathAt1 {V : Type*} (G : SimpleGraph V) (u : V) :=
  {p : PathTuple V // p.IsWalk G ∧ p.v1 = u}

private def pathAt1ToChains
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    PathAt1 G u → ChainsFrom G 1 u × ChainsFrom G 3 u := by
  rintro ⟨⟨v0, v1, v2, v3, v4⟩, hw, hv1⟩
  change v1 = u at hv1
  subst v1
  constructor
  · exact ⟨⟨v0, by simpa [PathTuple.IsWalk] using hw.1.symm⟩, PUnit.unit⟩
  · refine ⟨⟨v2, by simpa [PathTuple.IsWalk] using hw.2.1⟩, ?_⟩
    refine ⟨⟨v3, by simpa [PathTuple.IsWalk] using hw.2.2.1⟩, ?_⟩
    exact ⟨⟨v4, by simpa [PathTuple.IsWalk] using hw.2.2.2⟩, PUnit.unit⟩

private theorem pathAt1ToChains_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Function.Injective (pathAt1ToChains G u) := by
  rintro ⟨⟨v0, v1, v2, v3, v4⟩, hw, hv1⟩
    ⟨⟨w0, w1, w2, w3, w4⟩, hw', hw1⟩ h
  change v1 = u at hv1
  change w1 = u at hw1
  subst v1
  subst w1
  simp only [pathAt1ToChains] at h
  have h0 : v0 = w0 := by exact congrArg (fun z ↦ z.1.1.1) h
  subst w0
  have h2 : v2 = w2 := by exact congrArg (fun z ↦ z.2.1.1) h
  subst w2
  have h3 : v3 = w3 := by exact congrArg (fun z ↦ z.2.2.1.1) h
  subst w3
  have h4 : v4 = w4 := by exact congrArg (fun z ↦ z.2.2.2.1.1) h
  subst w4
  rfl

theorem card_pathAt1_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (PathAt1 G u) ≤ d ^ 4 := by
  classical
  letI : Finite (PathAt1 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (PathAt1 G u) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (pathAt1ToChains G u)
      (pathAt1ToChains_injective G u)).trans
    (by simpa using card_chainsFrom_prod_le G hdeg 1 3 u)

def PathAt2 {V : Type*} (G : SimpleGraph V) (u : V) :=
  {p : PathTuple V // p.IsWalk G ∧ p.v2 = u}

private def pathAt2ToChains
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    PathAt2 G u → ChainsFrom G 2 u × ChainsFrom G 2 u := by
  rintro ⟨⟨v0, v1, v2, v3, v4⟩, hw, hv2⟩
  change v2 = u at hv2
  subst v2
  constructor
  · refine ⟨⟨v1, by simpa [PathTuple.IsWalk] using hw.2.1.symm⟩, ?_⟩
    exact ⟨⟨v0, by simpa [PathTuple.IsWalk] using hw.1.symm⟩, PUnit.unit⟩
  · refine ⟨⟨v3, by simpa [PathTuple.IsWalk] using hw.2.2.1⟩, ?_⟩
    exact ⟨⟨v4, by simpa [PathTuple.IsWalk] using hw.2.2.2⟩, PUnit.unit⟩

private theorem pathAt2ToChains_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Function.Injective (pathAt2ToChains G u) := by
  rintro ⟨⟨v0, v1, v2, v3, v4⟩, hw, hv2⟩
    ⟨⟨w0, w1, w2, w3, w4⟩, hw', hw2⟩ h
  change v2 = u at hv2
  change w2 = u at hw2
  subst v2
  subst w2
  simp only [pathAt2ToChains] at h
  have h1 : v1 = w1 := by exact congrArg (fun z ↦ z.1.1.1) h
  subst w1
  have h0 : v0 = w0 := by exact congrArg (fun z ↦ z.1.2.1.1) h
  subst w0
  have h3 : v3 = w3 := by exact congrArg (fun z ↦ z.2.1.1) h
  subst w3
  have h4 : v4 = w4 := by exact congrArg (fun z ↦ z.2.2.1.1) h
  subst w4
  rfl

theorem card_pathAt2_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (PathAt2 G u) ≤ d ^ 4 := by
  classical
  letI : Finite (PathAt2 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (PathAt2 G u) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_le_of_injective (pathAt2ToChains G u)
      (pathAt2ToChains_injective G u)).trans
    (by simpa using card_chainsFrom_prod_le G hdeg 2 2 u)

def PathTuple.reverse {V : Type*} (p : PathTuple V) : PathTuple V :=
  ⟨p.v4, p.v3, p.v2, p.v1, p.v0⟩

@[simp] lemma PathTuple.reverse_reverse {V : Type*} (p : PathTuple V) :
    p.reverse.reverse = p := by
  cases p
  rfl

lemma PathTuple.isWalk_reverse_iff {V : Type*} (G : SimpleGraph V) (p : PathTuple V) :
    p.reverse.IsWalk G ↔ p.IsWalk G := by
  constructor
  · rintro ⟨h43, h32, h21, h10⟩
    exact ⟨h10.symm, h21.symm, h32.symm, h43.symm⟩
  · rintro ⟨h01, h12, h23, h34⟩
    exact ⟨h34.symm, h23.symm, h12.symm, h01.symm⟩

def PathAt3 {V : Type*} (G : SimpleGraph V) (u : V) :=
  {p : PathTuple V // p.IsWalk G ∧ p.v3 = u}

def PathAt4 {V : Type*} (G : SimpleGraph V) (u : V) :=
  {p : PathTuple V // p.IsWalk G ∧ p.v4 = u}

def pathAt3EquivPathAt1 {V : Type*} (G : SimpleGraph V) (u : V) :
    PathAt3 G u ≃ PathAt1 G u where
  toFun p := ⟨p.1.reverse, (PathTuple.isWalk_reverse_iff G p.1).mpr p.2.1, p.2.2⟩
  invFun p := ⟨p.1.reverse, (PathTuple.isWalk_reverse_iff G p.1).mpr p.2.1, p.2.2⟩
  left_inv := by intro p; apply Subtype.ext; exact PathTuple.reverse_reverse p.1
  right_inv := by intro p; apply Subtype.ext; exact PathTuple.reverse_reverse p.1

def pathAt4EquivPathAt0 {V : Type*} (G : SimpleGraph V) (u : V) :
    PathAt4 G u ≃ PathAt0 G u where
  toFun p := ⟨p.1.reverse, (PathTuple.isWalk_reverse_iff G p.1).mpr p.2.1, p.2.2⟩
  invFun p := ⟨p.1.reverse, (PathTuple.isWalk_reverse_iff G p.1).mpr p.2.1, p.2.2⟩
  left_inv := by intro p; apply Subtype.ext; exact PathTuple.reverse_reverse p.1
  right_inv := by intro p; apply Subtype.ext; exact PathTuple.reverse_reverse p.1

theorem card_pathAt3_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (PathAt3 G u) ≤ d ^ 4 := by
  rw [Nat.card_congr (pathAt3EquivPathAt1 G u)]
  exact card_pathAt1_le G hdeg u

theorem card_pathAt4_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (PathAt4 G u) ≤ d ^ 4 := by
  rw [Nat.card_congr (pathAt4EquivPathAt0 G u)]
  exact card_pathAt0_le G hdeg u

def IncidentPathTuple {V : Type*} (G : SimpleGraph V) (u : V) :=
  {p : PathTuple V // p.IsWalk G ∧
    (p.v0 = u ∨ p.v1 = u ∨ p.v2 = u ∨ p.v3 = u ∨ p.v4 = u)}

abbrev PathPositionSum {V : Type*} (G : SimpleGraph V) (u : V) :=
  PathAt0 G u ⊕ PathAt1 G u ⊕ PathAt2 G u ⊕ PathAt3 G u ⊕ PathAt4 G u

def incidentPathToPositionSum {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (u : V) : IncidentPathTuple G u → PathPositionSum G u := fun p ↦
  if h0 : p.1.v0 = u then Sum.inl ⟨p.1, p.2.1, h0⟩
  else if h1 : p.1.v1 = u then Sum.inr (Sum.inl ⟨p.1, p.2.1, h1⟩)
  else if h2 : p.1.v2 = u then Sum.inr (Sum.inr (Sum.inl ⟨p.1, p.2.1, h2⟩))
  else if h3 : p.1.v3 = u then
    Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨p.1, p.2.1, h3⟩)))
  else
    Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨p.1, p.2.1, by
      rcases p.2.2 with h | h | h | h | h
      · exact (h0 h).elim
      · exact (h1 h).elim
      · exact (h2 h).elim
      · exact (h3 h).elim
      · exact h⟩)))

def pathPositionSumVal {V : Type*} {G : SimpleGraph V} {u : V} :
    PathPositionSum G u → PathTuple V
  | Sum.inl p => p.1
  | Sum.inr (Sum.inl p) => p.1
  | Sum.inr (Sum.inr (Sum.inl p)) => p.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => p.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) => p.1

@[simp] lemma pathPositionSumVal_incidentPathToPositionSum
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) (p : IncidentPathTuple G u) :
    pathPositionSumVal (incidentPathToPositionSum G u p) = p.1 := by
  unfold incidentPathToPositionSum
  split_ifs <;> rfl

lemma incidentPathToPositionSum_injective
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) :
    Function.Injective (incidentPathToPositionSum G u) := by
  intro p q h
  apply Subtype.ext
  calc
    p.1 = pathPositionSumVal (incidentPathToPositionSum G u p) := by simp
    _ = pathPositionSumVal (incidentPathToPositionSum G u q) := congrArg pathPositionSumVal h
    _ = q.1 := by simp

/-- At most `5d⁴` ordered length-four walks can contain a fixed vertex when
the graph has maximum degree at most `d`. -/
theorem card_incidentPathTuple_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (IncidentPathTuple G u) ≤ 5 * d ^ 4 := by
  letI : Finite (PathAt0 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (PathAt1 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (PathAt2 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (PathAt3 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (PathAt4 G u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (PathAt0 G u) := Fintype.ofFinite _
  letI : Fintype (PathAt1 G u) := Fintype.ofFinite _
  letI : Fintype (PathAt2 G u) := Fintype.ofFinite _
  letI : Fintype (PathAt3 G u) := Fintype.ofFinite _
  letI : Fintype (PathAt4 G u) := Fintype.ofFinite _
  have hinj : Nat.card (IncidentPathTuple G u) ≤ Nat.card (PathPositionSum G u) :=
    Nat.card_le_card_of_injective (incidentPathToPositionSum G u)
      (incidentPathToPositionSum_injective G u)
  rw [Nat.card_sum, Nat.card_sum, Nat.card_sum, Nat.card_sum] at hinj
  have h0 := card_pathAt0_le G hdeg u
  have h1 := card_pathAt1_le G hdeg u
  have h2 := card_pathAt2_le G hdeg u
  have h3 := card_pathAt3_le G hdeg u
  have h4 := card_pathAt4_le G hdeg u
  omega

/-- Constructor discriminator used to isolate Type II events. -/
def BadIndex.IsPath {V : Type*} : BadIndex V → Prop
  | .path _ _ _ _ _ => True
  | _ => False

/-- Valid Type II indices whose support contains `u`. -/
def IncidentValidPath {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {i : BadIndex V // i.Valid G r ∧ u ∈ i.support ∧ i.IsPath}

def incidentValidPathToTuple
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    IncidentValidPath G r u → IncidentPathTuple G u := by
  rintro ⟨i, hvalid, hu, hpath⟩
  cases i with
  | edge a b => simp [BadIndex.IsPath] at hpath
  | path v0 v1 v2 v3 v4 =>
      exact ⟨⟨v0, v1, v2, v3, v4⟩, hvalid.2,
        by simpa [BadIndex.support, eq_comm] using hu⟩
  | square v0 v1 v2 v3 => simp [BadIndex.IsPath] at hpath
  | special a b => simp [BadIndex.IsPath] at hpath

lemma incidentValidPathToTuple_injective
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    Function.Injective (incidentValidPathToTuple G r u) := by
  rintro ⟨i, ⟨hvalidi, hui, hipath⟩⟩
    ⟨j, ⟨hvalidj, huj, hjpath⟩⟩ h
  cases i with
  | edge a b => simp [BadIndex.IsPath] at hipath
  | square a b c d => simp [BadIndex.IsPath] at hipath
  | special a b => simp [BadIndex.IsPath] at hipath
  | path v0 v1 v2 v3 v4 =>
      cases j with
      | edge a b => simp [BadIndex.IsPath] at hjpath
      | square a b c d => simp [BadIndex.IsPath] at hjpath
      | special a b => simp [BadIndex.IsPath] at hjpath
      | path w0 w1 w2 w3 w4 =>
          apply Subtype.ext
          have ht := congrArg Subtype.val h
          simp only [incidentValidPathToTuple] at ht
          change (⟨v0, v1, v2, v3, v4⟩ : PathTuple V) =
            ⟨w0, w1, w2, w3, w4⟩ at ht
          cases ht
          rfl

/-- The Type II incidence count used in the dependency estimate. -/
theorem card_incidentValidPath_le
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (IncidentValidPath G r u) ≤ 5 * d ^ 4 := by
  letI : Finite (IncidentPathTuple G u) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact (Nat.card_le_card_of_injective (incidentValidPathToTuple G r u)
    (incidentValidPathToTuple_injective G r u)).trans
      (card_incidentPathTuple_le G hdeg u)

structure SquareTuple (V : Type*) where
  v0 : V
  v1 : V
  v2 : V
  v3 : V

def squareTupleEquivData {V : Type*} : SquareTuple V ≃ V × V × V × V where
  toFun p := (p.v0, p.v1, p.v2, p.v3)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; rcases p with ⟨v0, v1, v2, v3⟩; rfl

noncomputable instance {V : Type*} [Fintype V] : Fintype (SquareTuple V) :=
  Fintype.ofEquiv (V × V × V × V) squareTupleEquivData.symm

def SquareTuple.IsAdmissible {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (p : SquareTuple V) : Prop :=
  G.Adj p.v0 p.v1 ∧ G.Adj p.v1 p.v2 ∧ G.Adj p.v2 p.v3 ∧ G.Adj p.v3 p.v0 ∧
    ¬IsSpecial G r p.v0 p.v2 ∧ ¬IsSpecial G r p.v1 p.v3

def SquareAt0 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {p : SquareTuple V // p.IsAdmissible G r ∧ p.v0 = u}

def chain2End {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (c : ChainsFrom G 2 u) : V :=
  c.2.1.1

def SquareCompletionCode {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u : V) :=
  Σ c : ChainsFrom G 2 u,
    {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
      v ∈ commonNeighbors G u (chain2End G u c)}

noncomputable def squareAt0ToCode
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (u : V) : SquareAt0 G r u → SquareCompletionCode G r u := by
  classical
  rintro ⟨⟨v0, v1, v2, v3⟩, h, hv0⟩
  change v0 = u at hv0
  subst v0
  refine ⟨⟨⟨v1, by simpa using h.1⟩,
    ⟨⟨v2, by simpa using h.2.1⟩, PUnit.unit⟩⟩,
    ⟨v3, h.2.2.2.2.1, ?_⟩⟩
  simp [commonNeighbors]
  exact ⟨h.2.2.2.1.symm, h.2.2.1⟩

lemma squareAt0ToCode_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (u : V) : Function.Injective (squareAt0ToCode G r u) := by
  rintro ⟨⟨v0, v1, v2, v3⟩, hv, hv0⟩
    ⟨⟨w0, w1, w2, w3⟩, hw, hw0⟩ h
  change v0 = u at hv0
  change w0 = u at hw0
  subst v0
  subst w0
  apply Subtype.ext
  simp only [squareAt0ToCode] at h
  have h1 : v1 = w1 := by exact congrArg (fun z ↦ z.1.1.1) h
  subst w1
  have h2 : v2 = w2 := by exact congrArg (fun z ↦ z.1.2.1.1) h
  subst w2
  have h3 : v3 = w3 := by exact congrArg (fun z ↦ z.2.1) h
  subst w3
  rfl

theorem card_squareCompletionCode_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (SquareCompletionCode G r u) ≤ d ^ 2 * r ^ 2 := by
  classical
  letI (c : ChainsFrom G 2 u) : Finite
      {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
        v ∈ commonNeighbors G u (chain2End G u c)} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI (c : ChainsFrom G 2 u) : Fintype
      {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
        v ∈ commonNeighbors G u (chain2End G u c)} := Fintype.ofFinite _
  change Nat.card (Σ c : ChainsFrom G 2 u,
    {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
      v ∈ commonNeighbors G u (chain2End G u c)}) ≤ d ^ 2 * r ^ 2
  rw [Nat.card_sigma]
  calc
    (∑ c : ChainsFrom G 2 u, Nat.card
        {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
          v ∈ commonNeighbors G u (chain2End G u c)}) ≤
        ∑ _c : ChainsFrom G 2 u, r ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      rw [Nat.card_eq_fintype_card]
      by_cases hns : ¬IsSpecial G r u (chain2End G u c)
      · calc
          Fintype.card {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
              v ∈ commonNeighbors G u (chain2End G u c)} ≤
              Fintype.card {v : V // v ∈ commonNeighbors G u (chain2End G u c)} := by
            exact Fintype.card_le_of_injective
              (fun v ↦ ⟨v.1, v.2.2⟩) (by
                intro a b h
                apply Subtype.ext
                exact congrArg (fun z :
                  {v : V // v ∈ commonNeighbors G u (chain2End G u c)} ↦ z.1) h)
          _ = (commonNeighbors G u (chain2End G u c)).card := Fintype.card_coe _
          _ ≤ r ^ 2 := Nat.le_of_not_gt hns
      · have hempty : IsEmpty
            {v : V // ¬IsSpecial G r u (chain2End G u c) ∧
              v ∈ commonNeighbors G u (chain2End G u c)} :=
          ⟨fun v ↦ (hns v.2.1).elim⟩
        simp
    _ = Fintype.card (ChainsFrom G 2 u) * r ^ 2 := by simp
    _ ≤ d ^ 2 * r ^ 2 := Nat.mul_le_mul_right _ (card_chainsFrom_le G hdeg 2 u)

theorem card_squareAt0_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (SquareAt0 G r u) ≤ d ^ 2 * r ^ 2 := by
  letI : Finite (SquareCompletionCode G r u) :=
    Finite.of_injective (fun z ↦ (z.1, z.2.1)) (by
      intro a b h
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      have hab : a = b := congrArg Prod.fst h
      subst b
      have hv : ha.1 = hb.1 := congrArg Prod.snd h
      cases Subtype.ext hv
      rfl)
  exact (Nat.card_le_card_of_injective (squareAt0ToCode G r u)
    (squareAt0ToCode_injective G r u)).trans
      (card_squareCompletionCode_le G hdeg u)

def SquareTuple.rotate {V : Type*} (p : SquareTuple V) : SquareTuple V :=
  ⟨p.v1, p.v2, p.v3, p.v0⟩

@[simp] lemma SquareTuple.rotate_four {V : Type*} (p : SquareTuple V) :
    p.rotate.rotate.rotate.rotate = p := by
  cases p
  rfl

lemma SquareTuple.isAdmissible_rotate
    {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) {p : SquareTuple V}
    (h : p.IsAdmissible G r) : p.rotate.IsAdmissible G r := by
  refine ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.1, h.2.2.2.2.2, ?_⟩
  intro hs
  exact h.2.2.2.2.1 ((isSpecial_comm G r p.v0 p.v2).mpr hs)

lemma SquareTuple.isAdmissible_rotate_iff
    {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (p : SquareTuple V) :
    p.rotate.IsAdmissible G r ↔ p.IsAdmissible G r := by
  constructor
  · intro h
    have h2 := SquareTuple.isAdmissible_rotate G r h
    have h3 := SquareTuple.isAdmissible_rotate G r h2
    have h4 := SquareTuple.isAdmissible_rotate G r h3
    simpa using h4
  · exact SquareTuple.isAdmissible_rotate G r

def SquareAt1 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {p : SquareTuple V // p.IsAdmissible G r ∧ p.v1 = u}

def SquareAt2 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {p : SquareTuple V // p.IsAdmissible G r ∧ p.v2 = u}

def SquareAt3 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {p : SquareTuple V // p.IsAdmissible G r ∧ p.v3 = u}

def squareAt1EquivAt0 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) : SquareAt1 G r u ≃ SquareAt0 G r u where
  toFun p := ⟨p.1.rotate, SquareTuple.isAdmissible_rotate G r p.2.1, p.2.2⟩
  invFun p :=
    ⟨p.1.rotate.rotate.rotate,
      (SquareTuple.isAdmissible_rotate G r
        (SquareTuple.isAdmissible_rotate G r
          (SquareTuple.isAdmissible_rotate G r p.2.1))), p.2.2⟩
  left_inv := by intro p; apply Subtype.ext; exact SquareTuple.rotate_four p.1
  right_inv := by intro p; apply Subtype.ext; exact SquareTuple.rotate_four p.1

def squareAt2EquivAt0 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) : SquareAt2 G r u ≃ SquareAt0 G r u where
  toFun p :=
    ⟨p.1.rotate.rotate,
      SquareTuple.isAdmissible_rotate G r (SquareTuple.isAdmissible_rotate G r p.2.1), p.2.2⟩
  invFun p :=
    ⟨p.1.rotate.rotate,
      SquareTuple.isAdmissible_rotate G r (SquareTuple.isAdmissible_rotate G r p.2.1), p.2.2⟩
  left_inv := by intro p; apply Subtype.ext; exact SquareTuple.rotate_four p.1
  right_inv := by intro p; apply Subtype.ext; exact SquareTuple.rotate_four p.1

def squareAt3EquivAt0 {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) : SquareAt3 G r u ≃ SquareAt0 G r u where
  toFun p :=
    ⟨p.1.rotate.rotate.rotate,
      SquareTuple.isAdmissible_rotate G r
        (SquareTuple.isAdmissible_rotate G r
          (SquareTuple.isAdmissible_rotate G r p.2.1)), p.2.2⟩
  invFun p := ⟨p.1.rotate, SquareTuple.isAdmissible_rotate G r p.2.1, p.2.2⟩
  left_inv := by intro p; apply Subtype.ext; exact SquareTuple.rotate_four p.1
  right_inv := by intro p; apply Subtype.ext; exact SquareTuple.rotate_four p.1

theorem card_squareAt1_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (SquareAt1 G r u) ≤ d ^ 2 * r ^ 2 := by
  rw [Nat.card_congr (squareAt1EquivAt0 G r u)]
  exact card_squareAt0_le G hdeg u

theorem card_squareAt2_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (SquareAt2 G r u) ≤ d ^ 2 * r ^ 2 := by
  rw [Nat.card_congr (squareAt2EquivAt0 G r u)]
  exact card_squareAt0_le G hdeg u

theorem card_squareAt3_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (SquareAt3 G r u) ≤ d ^ 2 * r ^ 2 := by
  rw [Nat.card_congr (squareAt3EquivAt0 G r u)]
  exact card_squareAt0_le G hdeg u

def IncidentSquareTuple {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {p : SquareTuple V // p.IsAdmissible G r ∧
    (p.v0 = u ∨ p.v1 = u ∨ p.v2 = u ∨ p.v3 = u)}

abbrev SquarePositionSum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  SquareAt0 G r u ⊕ SquareAt1 G r u ⊕ SquareAt2 G r u ⊕ SquareAt3 G r u

def incidentSquareToPositionSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    IncidentSquareTuple G r u → SquarePositionSum G r u := fun p ↦
  if h0 : p.1.v0 = u then Sum.inl ⟨p.1, p.2.1, h0⟩
  else if h1 : p.1.v1 = u then Sum.inr (Sum.inl ⟨p.1, p.2.1, h1⟩)
  else if h2 : p.1.v2 = u then Sum.inr (Sum.inr (Sum.inl ⟨p.1, p.2.1, h2⟩))
  else Sum.inr (Sum.inr (Sum.inr ⟨p.1, p.2.1, by
    rcases p.2.2 with h | h | h | h
    · exact (h0 h).elim
    · exact (h1 h).elim
    · exact (h2 h).elim
    · exact h⟩))

def squarePositionSumVal
    {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ} {u : V} :
    SquarePositionSum G r u → SquareTuple V
  | Sum.inl p => p.1
  | Sum.inr (Sum.inl p) => p.1
  | Sum.inr (Sum.inr (Sum.inl p)) => p.1
  | Sum.inr (Sum.inr (Sum.inr p)) => p.1

@[simp] lemma squarePositionSumVal_incidentSquareToPositionSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (u : V) (p : IncidentSquareTuple G r u) :
    squarePositionSumVal (incidentSquareToPositionSum G r u p) = p.1 := by
  unfold incidentSquareToPositionSum
  split_ifs <;> rfl

lemma incidentSquareToPositionSum_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    Function.Injective (incidentSquareToPositionSum G r u) := by
  intro p q h
  apply Subtype.ext
  calc
    p.1 = squarePositionSumVal (incidentSquareToPositionSum G r u p) := by simp
    _ = squarePositionSumVal (incidentSquareToPositionSum G r u q) :=
      congrArg squarePositionSumVal h
    _ = q.1 := by simp

theorem card_incidentSquareTuple_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (IncidentSquareTuple G r u) ≤ 4 * (d ^ 2 * r ^ 2) := by
  letI : Finite (SquareAt0 G r u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (SquareAt1 G r u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (SquareAt2 G r u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (SquareAt3 G r u) := Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (SquareAt0 G r u) := Fintype.ofFinite _
  letI : Fintype (SquareAt1 G r u) := Fintype.ofFinite _
  letI : Fintype (SquareAt2 G r u) := Fintype.ofFinite _
  letI : Fintype (SquareAt3 G r u) := Fintype.ofFinite _
  have hinj := Nat.card_le_card_of_injective (incidentSquareToPositionSum G r u)
    (incidentSquareToPositionSum_injective G r u)
  rw [Nat.card_sum, Nat.card_sum, Nat.card_sum] at hinj
  have h0 := card_squareAt0_le G (d := d) (r := r) hdeg u
  have h1 := card_squareAt1_le G (d := d) (r := r) hdeg u
  have h2 := card_squareAt2_le G (d := d) (r := r) hdeg u
  have h3 := card_squareAt3_le G (d := d) (r := r) hdeg u
  omega

def BadIndex.IsSquare {V : Type*} : BadIndex V → Prop
  | .square _ _ _ _ => True
  | _ => False

def IncidentValidSquare {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {i : BadIndex V // i.Valid G r ∧ u ∈ i.support ∧ i.IsSquare}

def incidentValidSquareToTuple
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    IncidentValidSquare G r u → IncidentSquareTuple G r u := by
  rintro ⟨i, hvalid, hu, hsquare⟩
  cases i with
  | edge a b => simp [BadIndex.IsSquare] at hsquare
  | path v0 v1 v2 v3 v4 => simp [BadIndex.IsSquare] at hsquare
  | square v0 v1 v2 v3 =>
      exact ⟨⟨v0, v1, v2, v3⟩, hvalid.2,
        by simpa [BadIndex.support, eq_comm] using hu⟩
  | special a b => simp [BadIndex.IsSquare] at hsquare

lemma incidentValidSquareToTuple_injective
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    Function.Injective (incidentValidSquareToTuple G r u) := by
  rintro ⟨i, ⟨hvalidi, hui, hisquare⟩⟩
    ⟨j, ⟨hvalidj, huj, hjsquare⟩⟩ h
  cases i with
  | edge a b => simp [BadIndex.IsSquare] at hisquare
  | path a b c d e => simp [BadIndex.IsSquare] at hisquare
  | special a b => simp [BadIndex.IsSquare] at hisquare
  | square v0 v1 v2 v3 =>
      cases j with
      | edge a b => simp [BadIndex.IsSquare] at hjsquare
      | path a b c d e => simp [BadIndex.IsSquare] at hjsquare
      | special a b => simp [BadIndex.IsSquare] at hjsquare
      | square w0 w1 w2 w3 =>
          apply Subtype.ext
          have ht := congrArg Subtype.val h
          simp only [incidentValidSquareToTuple] at ht
          change (⟨v0, v1, v2, v3⟩ : SquareTuple V) = ⟨w0, w1, w2, w3⟩ at ht
          cases ht
          rfl

theorem card_incidentValidSquare_le
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (IncidentValidSquare G r u) ≤ 4 * (d ^ 2 * r ^ 2) := by
  letI : Finite (IncidentSquareTuple G r u) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact (Nat.card_le_card_of_injective (incidentValidSquareToTuple G r u)
    (incidentValidSquareToTuple_injective G r u)).trans
      (card_incidentSquareTuple_le G hdeg u)

def BadIndex.IsEdge {V : Type*} : BadIndex V → Prop
  | .edge _ _ => True
  | _ => False

def IncidentValidEdge {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {i : BadIndex V // i.Valid G r ∧ u ∈ i.support ∧ i.IsEdge}

def endpointOther {V : Type*} [DecidableEq V] (u a b : V) : V :=
  if u = a then b else a

def incidentValidEdgeOther
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u : V) :
    IncidentValidEdge G r u → {v : V // v ∈ G.neighborFinset u} := by
  rintro ⟨i, hvalid, hu, hedge⟩
  cases i with
  | path a b c d e => simp [BadIndex.IsEdge] at hedge
  | square a b c d => simp [BadIndex.IsEdge] at hedge
  | special a b => simp [BadIndex.IsEdge] at hedge
  | edge a b =>
      have hab : u = a ∨ u = b := by simpa [BadIndex.support] using hu
      refine ⟨endpointOther u a b, ?_⟩
      by_cases h : u = a
      · simpa [endpointOther, h] using hvalid.2
      · have hub : u = b := hab.resolve_left h
        subst b
        simpa [endpointOther, h] using hvalid.2.symm

lemma incidentValidEdgeOther_injective
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (u : V) :
    Function.Injective (incidentValidEdgeOther G r u) := by
  rintro ⟨i, ⟨hvi, hui, hei⟩⟩ ⟨j, ⟨hvj, huj, hej⟩⟩ h
  cases i with
  | path a b c d e => simp [BadIndex.IsEdge] at hei
  | square a b c d => simp [BadIndex.IsEdge] at hei
  | special a b => simp [BadIndex.IsEdge] at hei
  | edge a b =>
      cases j with
      | path c d e f g => simp [BadIndex.IsEdge] at hej
      | square c d e f => simp [BadIndex.IsEdge] at hej
      | special c d => simp [BadIndex.IsEdge] at hej
      | edge c d =>
          have hui' : u = a ∨ u = b := by simpa [BadIndex.support] using hui
          have huj' : u = c ∨ u = d := by simpa [BadIndex.support] using huj
          rcases hui' with rfl | rfl <;> rcases huj' with rfl | rfl
          · have hbd : b = d := by
              simpa only [incidentValidEdgeOther, endpointOther, if_pos rfl, if_true] using
                congrArg Subtype.val h
            subst d
            rfl
          · have hbc : b = c := by
              simpa only [incidentValidEdgeOther, endpointOther, if_pos rfl, if_true,
                if_neg hvj.1.ne'] using congrArg Subtype.val h
            subst c
            exact (lt_asymm hvi.1 hvj.1).elim
          · have had : a = d := by
              simpa only [incidentValidEdgeOther, endpointOther, if_neg hvi.1.ne',
                if_pos rfl, if_true] using congrArg Subtype.val h
            subst d
            exact (lt_asymm hvj.1 hvi.1).elim
          · have hac : a = c := by
              simpa only [incidentValidEdgeOther, endpointOther, if_neg hvi.1.ne',
                if_neg hvj.1.ne'] using congrArg Subtype.val h
            subst c
            rfl

theorem card_incidentValidEdge_le
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (IncidentValidEdge G r u) ≤ d := by
  calc
    Nat.card (IncidentValidEdge G r u) ≤
        Nat.card {v : V // v ∈ G.neighborFinset u} :=
      Nat.card_le_card_of_injective (incidentValidEdgeOther G r u)
        (incidentValidEdgeOther_injective G r u)
    _ = Fintype.card {v : V // v ∈ G.neighborFinset u} :=
      Nat.card_eq_fintype_card
    _ = (G.neighborFinset u).card := Fintype.card_coe _
    _ = G.degree u := G.card_neighborFinset_eq_degree u
    _ ≤ d := hdeg u

def SpecialOther {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {v : V // v ≠ u ∧ IsSpecial G r u v}

noncomputable instance specialOtherFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) : Fintype (SpecialOther G r u) := by
  classical
  letI : Finite (SpecialOther G r u) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

lemma mem_commonNeighbors_iff
    {V : Type*} [Fintype V] (G : SimpleGraph V) (u v w : V) :
    w ∈ commonNeighbors G u v ↔ G.Adj u w ∧ G.Adj v w := by
  classical
  simp [commonNeighbors]

def SpecialWitness {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  Σ v : SpecialOther G r u, {w : V // w ∈ commonNeighbors G u v.1}

def NeighborTwoStepCode {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :=
  Σ w : {w : V // w ∈ G.neighborFinset u}, {v : V // v ∈ G.neighborFinset w}

def specialWitnessToCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (u : V) : SpecialWitness G r u → NeighborTwoStepCode G u := by
  rintro ⟨v, w⟩
  refine ⟨⟨w, ?_⟩, ⟨v.1, ?_⟩⟩
  · simpa using (mem_commonNeighbors_iff G u v.1 w).mp w.2 |>.1
  · simpa using (mem_commonNeighbors_iff G u v.1 w).mp w.2 |>.2.symm

lemma specialWitnessToCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (u : V) : Function.Injective (specialWitnessToCode G r u) := by
  rintro ⟨v, w⟩ ⟨v', w'⟩ h
  have hw : w.1 = w'.1 := by
    simpa only [specialWitnessToCode] using congrArg (fun z ↦ z.1.1) h
  have hv : v.1 = v'.1 := by
    simpa only [specialWitnessToCode] using congrArg (fun z ↦ z.2.1) h
  cases Subtype.ext hv
  cases Subtype.ext hw
  rfl

theorem card_neighborTwoStepCode_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (u : V) :
    Nat.card (NeighborTwoStepCode G u) ≤ d ^ 2 := by
  classical
  letI (w : {w : V // w ∈ G.neighborFinset u}) : Fintype
      {v : V // v ∈ G.neighborFinset w} := Fintype.ofFinite _
  change Nat.card (Σ w : {w : V // w ∈ G.neighborFinset u},
    {v : V // v ∈ G.neighborFinset w}) ≤ d ^ 2
  rw [Nat.card_sigma]
  calc
    (∑ w : {w : V // w ∈ G.neighborFinset u},
        Nat.card {v : V // v ∈ G.neighborFinset w}) ≤
        ∑ _w : {w : V // w ∈ G.neighborFinset u}, d := by
      apply Finset.sum_le_sum
      intro w hw
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact hdeg w
    _ = G.degree u * d := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        SimpleGraph.card_neighborFinset_eq_degree]
      simp [nsmul_eq_mul]
    _ ≤ d ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right d (hdeg u)

theorem card_specialWitness_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (u : V) :
    Nat.card (SpecialOther G r u) * (r ^ 2 + 1) ≤
      Nat.card (SpecialWitness G r u) := by
  classical
  letI : Fintype (SpecialOther G r u) := Fintype.ofFinite _
  letI (v : SpecialOther G r u) : Fintype
      {w : V // w ∈ commonNeighbors G u v.1} := Fintype.ofFinite _
  change Nat.card (SpecialOther G r u) * (r ^ 2 + 1) ≤
    Nat.card (Σ v : SpecialOther G r u,
      {w : V // w ∈ commonNeighbors G u v.1})
  rw [Nat.card_sigma]
  calc
    Nat.card (SpecialOther G r u) * (r ^ 2 + 1) =
        ∑ _v : SpecialOther G r u, (r ^ 2 + 1) := by simp
    _ ≤ ∑ v : SpecialOther G r u,
        Nat.card {w : V // w ∈ commonNeighbors G u v.1} := by
      apply Finset.sum_le_sum
      intro v hv
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact v.2.2

theorem card_specialOther_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hdr : d ≤ r ^ 3) (u : V) :
    Nat.card (SpecialOther G r u) ≤ r ^ 4 := by
  have hwitness : Nat.card (SpecialWitness G r u) ≤ d ^ 2 :=
    by
      classical
      letI : Fintype {w : V // w ∈ G.neighborFinset u} := Fintype.ofFinite _
      letI (w : {w : V // w ∈ G.neighborFinset u}) : Fintype
          {v : V // v ∈ G.neighborFinset w} := Fintype.ofFinite _
      letI : Finite (NeighborTwoStepCode G u) :=
        Finite.of_injective (fun z ↦ (z.1.1, z.2.1)) (by
          intro a b h
          have h1 : a.1.1 = b.1.1 := congrArg Prod.fst h
          have h2 : a.2.1 = b.2.1 := congrArg Prod.snd h
          apply Sigma.ext (Subtype.ext h1)
          exact (Subtype.heq_iff_coe_eq (fun x ↦ by simp [h1])).2 h2)
      letI (v : SpecialOther G r u) : Finite
          {w : V // w ∈ commonNeighbors G u v.1} :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI : Finite (SpecialWitness G r u) :=
        Finite.of_injective (fun z ↦ (z.1.1, z.2.1)) (by
          intro a b h
          have h1 : a.1.1 = b.1.1 := congrArg Prod.fst h
          have h2 : a.2.1 = b.2.1 := congrArg Prod.snd h
          apply Sigma.ext (Subtype.ext h1)
          exact (Subtype.heq_iff_coe_eq (fun x ↦ by simp [h1])).2 h2)
      exact (Nat.card_le_card_of_injective (specialWitnessToCode G r u)
        (specialWitnessToCode_injective G r u)).trans
        (card_neighborTwoStepCode_le G hdeg u)
  have hlower := card_specialWitness_lower G r u
  have hd2 : d ^ 2 ≤ (r ^ 3) ^ 2 := Nat.pow_le_pow_left hdr 2
  by_contra hnot
  have hlarge : r ^ 4 + 1 ≤ Nat.card (SpecialOther G r u) := by omega
  have hmul : (r ^ 4 + 1) * (r ^ 2 + 1) ≤ d ^ 2 :=
    (Nat.mul_le_mul_right (r ^ 2 + 1) hlarge).trans (hlower.trans hwitness)
  have hstrict : (r ^ 3) ^ 2 < (r ^ 4 + 1) * (r ^ 2 + 1) := by
    nlinarith [Nat.zero_le (r ^ 4), Nat.zero_le (r ^ 2)]
  omega

def BadIndex.IsSpecialIndex {V : Type*} : BadIndex V → Prop
  | .special _ _ => True
  | _ => False

def IncidentValidSpecial {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :=
  {i : BadIndex V // i.Valid G r ∧ u ∈ i.support ∧ i.IsSpecialIndex}

def incidentValidSpecialOther
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    IncidentValidSpecial G r u → SpecialOther G r u := by
  rintro ⟨i, hvalid, hu, hspecial⟩
  cases i with
  | edge a b => simp [BadIndex.IsSpecialIndex] at hspecial
  | path a b c d e => simp [BadIndex.IsSpecialIndex] at hspecial
  | square a b c d => simp [BadIndex.IsSpecialIndex] at hspecial
  | special a b =>
      have hab : u = a ∨ u = b := by simpa [BadIndex.support] using hu
      refine ⟨endpointOther u a b, ?_, ?_⟩
      · by_cases h : u = a
        · simpa [endpointOther, h] using hvalid.1.ne'
        · have hub : u = b := hab.resolve_left h
          subst b
          simpa [endpointOther, h] using hvalid.1.ne
      · by_cases h : u = a
        · simpa [endpointOther, h] using hvalid.2
        · have hub : u = b := hab.resolve_left h
          subst b
          simpa [endpointOther, h] using (isSpecial_comm G r a u).mp hvalid.2

lemma incidentValidSpecialOther_injective
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (r : ℕ) (u : V) :
    Function.Injective (incidentValidSpecialOther G r u) := by
  rintro ⟨i, ⟨hvi, hui, hsi⟩⟩ ⟨j, ⟨hvj, huj, hsj⟩⟩ h
  cases i with
  | edge a b => simp [BadIndex.IsSpecialIndex] at hsi
  | path a b c d e => simp [BadIndex.IsSpecialIndex] at hsi
  | square a b c d => simp [BadIndex.IsSpecialIndex] at hsi
  | special a b =>
      cases j with
      | edge c d => simp [BadIndex.IsSpecialIndex] at hsj
      | path c d e f g => simp [BadIndex.IsSpecialIndex] at hsj
      | square c d e f => simp [BadIndex.IsSpecialIndex] at hsj
      | special c d =>
          have hui' : u = a ∨ u = b := by simpa [BadIndex.support] using hui
          have huj' : u = c ∨ u = d := by simpa [BadIndex.support] using huj
          rcases hui' with rfl | rfl <;> rcases huj' with rfl | rfl
          · have hbd : b = d := by
              simpa only [incidentValidSpecialOther, endpointOther, if_pos rfl,
                if_true] using
                congrArg Subtype.val h
            subst d
            rfl
          · have hbc : b = c := by
              simpa only [incidentValidSpecialOther, endpointOther, if_pos rfl,
                if_true, if_neg hvj.1.ne'] using congrArg Subtype.val h
            subst c
            exact (lt_asymm hvi.1 hvj.1).elim
          · have had : a = d := by
              simpa only [incidentValidSpecialOther, endpointOther, if_neg hvi.1.ne',
                if_pos rfl, if_true] using congrArg Subtype.val h
            subst d
            exact (lt_asymm hvj.1 hvi.1).elim
          · have hac : a = c := by
              simpa only [incidentValidSpecialOther, endpointOther, if_neg hvi.1.ne',
                if_neg hvj.1.ne'] using congrArg Subtype.val h
            subst c
            rfl

theorem card_incidentValidSpecial_le
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hdr : d ≤ r ^ 3) (u : V) :
    Nat.card (IncidentValidSpecial G r u) ≤ r ^ 4 := by
  letI : Finite (SpecialOther G r u) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact (Nat.card_le_card_of_injective (incidentValidSpecialOther G r u)
      (incidentValidSpecialOther_injective G r u)).trans
        (card_specialOther_le G hdeg hdr u)

open Finset

noncomputable def eventWeight {V : Type*} (x : ℕ) (i : BadIndex V) : ℝ :=
  2 / (x : ℝ) ^ i.constraintCount

noncomputable def validWeight {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r x : ℕ) (i : BadIndex V) : ℝ := by
  classical
  exact if i.Valid G r then eventWeight x i else 0

theorem sum_indicator_eq_card_mul
    {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (a : ℝ) :
    (∑ i : α, if P i then a else 0) = Nat.card {i : α // P i} * a := by
  classical
  letI : Finite {i : α // P i} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype {i : α // P i} := Fintype.ofFinite _
  calc
    (∑ i : α, if P i then a else 0) =
        (∑ i : α, if P i then (1 : ℝ) else 0) * a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    _ = (Finset.univ.filter P).card * a := by
      rw [show (∑ i : α, if P i then (1 : ℝ) else 0) =
          (Finset.univ.filter P).card by simp [Finset.sum_boole]]
    _ = Nat.card {i : α // P i} * a := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem incidentWeightSum_eq
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r x : ℕ) (u : V) :
    (∑ i : BadIndex V, if u ∈ i.support then validWeight G r x i else 0) =
      Nat.card (IncidentValidEdge G r u) * (2 / (x : ℝ)) +
      Nat.card (IncidentValidPath G r u) * (2 / (x : ℝ) ^ 3) +
      Nat.card (IncidentValidSquare G r u) * (2 / (x : ℝ) ^ 2) +
      Nat.card (IncidentValidSpecial G r u) * (2 / (x : ℝ)) := by
  classical
  have hsplit (i : BadIndex V) :
      (if u ∈ i.support then validWeight G r x i else 0) =
        (if i.Valid G r ∧ u ∈ i.support ∧ i.IsEdge then 2 / (x : ℝ) else 0) +
        (if i.Valid G r ∧ u ∈ i.support ∧ i.IsPath then 2 / (x : ℝ) ^ 3 else 0) +
        (if i.Valid G r ∧ u ∈ i.support ∧ i.IsSquare then 2 / (x : ℝ) ^ 2 else 0) +
        (if i.Valid G r ∧ u ∈ i.support ∧ i.IsSpecialIndex then
          2 / (x : ℝ) else 0) := by
    by_cases hv : i.Valid G r <;> by_cases hu : u ∈ i.support <;>
      cases i <;> simp_all [validWeight, eventWeight, BadIndex.constraintCount,
        BadIndex.IsEdge, BadIndex.IsPath, BadIndex.IsSquare, BadIndex.IsSpecialIndex]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [sum_indicator_eq_card_mul, sum_indicator_eq_card_mul,
    sum_indicator_eq_card_mul, sum_indicator_eq_card_mul]
  rfl

theorem incidentWeightSum_le
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r x : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hdr : d ≤ r ^ 3) (u : V) :
    (∑ i : BadIndex V, if u ∈ i.support then validWeight G r x i else 0) ≤
      (d : ℝ) * (2 / (x : ℝ)) +
      (5 * d ^ 4 : ℝ) * (2 / (x : ℝ) ^ 3) +
      (4 * (d ^ 2 * r ^ 2) : ℝ) * (2 / (x : ℝ) ^ 2) +
      (r ^ 4 : ℝ) * (2 / (x : ℝ)) := by
  rw [incidentWeightSum_eq]
  gcongr
  · exact_mod_cast card_incidentValidEdge_le G hdeg u
  · exact_mod_cast card_incidentValidPath_le G hdeg u
  · exact_mod_cast card_incidentValidSquare_le G hdeg u
  · exact_mod_cast card_incidentValidSpecial_le G hdeg hdr u

theorem validWeight_nonneg
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r x : ℕ) (i : BadIndex V) :
    0 ≤ validWeight G r x i := by
  classical
  unfold validWeight eventWeight
  split_ifs <;> positivity

lemma BadIndex.support_card_le_five
    {V : Type*} [DecidableEq V] (i : BadIndex V) : i.support.card ≤ 5 := by
  cases i <;> grind [BadIndex.support, Finset.card_insert_le]

theorem overlapWeightSum_le
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r x : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hdr : d ≤ r ^ 3)
    (i : BadIndex V) :
    (∑ j ∈ overlapNeighbors BadIndex.support i, validWeight G r x j) ≤
      5 * ((d : ℝ) * (2 / (x : ℝ)) +
        (5 * d ^ 4 : ℝ) * (2 / (x : ℝ) ^ 3) +
        (4 * (d ^ 2 * r ^ 2) : ℝ) * (2 / (x : ℝ) ^ 2) +
        (r ^ 4 : ℝ) * (2 / (x : ℝ))) := by
  classical
  let B : ℝ := (d : ℝ) * (2 / (x : ℝ)) +
    (5 * d ^ 4 : ℝ) * (2 / (x : ℝ) ^ 3) +
    (4 * (d ^ 2 * r ^ 2) : ℝ) * (2 / (x : ℝ) ^ 2) +
    (r ^ 4 : ℝ) * (2 / (x : ℝ))
  have hone (j : BadIndex V) (hj : j ∈ overlapNeighbors BadIndex.support i) :
      validWeight G r x j ≤
        ∑ u ∈ i.support, if u ∈ j.support then validWeight G r x j else 0 := by
    have hnd : ¬Disjoint i.support j.support := by
      simpa [overlapNeighbors] using hj
    obtain ⟨u, hui, huj⟩ := Finset.not_disjoint_iff.mp hnd
    calc
      validWeight G r x j =
          (if u ∈ j.support then validWeight G r x j else 0) := by simp [huj]
      _ ≤ ∑ v ∈ i.support, if v ∈ j.support then validWeight G r x j else 0 := by
        exact Finset.single_le_sum (s := i.support)
          (f := fun v ↦ if v ∈ j.support then validWeight G r x j else 0)
          (by
            intro v hv
            split_ifs
            · exact validWeight_nonneg G r x j
            · exact le_rfl) hui
  have hfirst :
      (∑ j ∈ overlapNeighbors BadIndex.support i, validWeight G r x j) ≤
        ∑ j ∈ overlapNeighbors BadIndex.support i,
          ∑ u ∈ i.support, if u ∈ j.support then validWeight G r x j else 0 := by
    exact Finset.sum_le_sum fun j hj ↦ hone j hj
  have hextend :
      (∑ j ∈ overlapNeighbors BadIndex.support i,
          ∑ u ∈ i.support, if u ∈ j.support then validWeight G r x j else 0) ≤
        ∑ j : BadIndex V,
          ∑ u ∈ i.support, if u ∈ j.support then validWeight G r x j else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro j hj hnot
    exact Finset.sum_nonneg fun u hu ↦ by
      split_ifs
      · exact validWeight_nonneg G r x j
      · exact le_rfl
  have hswap :
      (∑ j : BadIndex V,
          ∑ u ∈ i.support, if u ∈ j.support then validWeight G r x j else 0) =
        ∑ u ∈ i.support,
          ∑ j : BadIndex V, if u ∈ j.support then validWeight G r x j else 0 := by
    rw [Finset.sum_comm]
  have hinner (u : V) :
      (∑ j : BadIndex V, if u ∈ j.support then validWeight G r x j else 0) ≤ B := by
    exact incidentWeightSum_le G hdeg hdr u
  calc
    (∑ j ∈ overlapNeighbors BadIndex.support i, validWeight G r x j) ≤
        ∑ j : BadIndex V,
          ∑ u ∈ i.support, if u ∈ j.support then validWeight G r x j else 0 :=
      hfirst.trans hextend
    _ = ∑ u ∈ i.support,
          ∑ j : BadIndex V, if u ∈ j.support then validWeight G r x j else 0 := hswap
    _ ≤ ∑ _u ∈ i.support, B := by
      exact Finset.sum_le_sum fun u hu ↦ hinner u
    _ = i.support.card * B := by simp
    _ ≤ 5 * B := by
      gcongr
      exact_mod_cast BadIndex.support_card_le_five i

theorem numerical_weight_bound {d r : ℕ} (hr : 1 ≤ r) (hdr : d ≤ r ^ 3) :
    5 * ((d : ℝ) * (2 / (64 * r ^ 4 : ℕ)) +
        (5 * d ^ 4 : ℝ) * (2 / (64 * r ^ 4 : ℕ) ^ 3) +
        (4 * (d ^ 2 * r ^ 2) : ℝ) * (2 / (64 * r ^ 4 : ℕ) ^ 2) +
        (r ^ 4 : ℝ) * (2 / (64 * r ^ 4 : ℕ))) < 1 / 2 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hdrR : (d : ℝ) ≤ (r : ℝ) ^ 3 := by exact_mod_cast hdr
  have hd2 : (d : ℝ) ^ 2 ≤ (r : ℝ) ^ 6 := by
    calc
      (d : ℝ) ^ 2 ≤ ((r : ℝ) ^ 3) ^ 2 := by gcongr
      _ = (r : ℝ) ^ 6 := by ring
  have hd4 : (d : ℝ) ^ 4 ≤ (r : ℝ) ^ 12 := by
    calc
      (d : ℝ) ^ 4 ≤ ((r : ℝ) ^ 3) ^ 4 := by gcongr
      _ = (r : ℝ) ^ 12 := by ring
  have hdr8 : (d : ℝ) * (r : ℝ) ^ 8 ≤ (r : ℝ) ^ 12 := by
    calc
      (d : ℝ) * (r : ℝ) ^ 8 ≤ (r : ℝ) ^ 3 * (r : ℝ) ^ 8 := by gcongr
      _ = (r : ℝ) ^ 11 := by ring
      _ ≤ (r : ℝ) ^ 12 := by
        rw [show (r : ℝ) ^ 12 = (r : ℝ) ^ 11 * r by ring]
        exact le_mul_of_one_le_right (by positivity) hrOne
  have hd2r6 : (d : ℝ) ^ 2 * (r : ℝ) ^ 6 ≤ (r : ℝ) ^ 12 := by
    calc
      (d : ℝ) ^ 2 * (r : ℝ) ^ 6 ≤ (r : ℝ) ^ 6 * (r : ℝ) ^ 6 := by gcongr
      _ = (r : ℝ) ^ 12 := by ring
  have hterm1 : (d : ℝ) * (64 ^ 2 * (r : ℝ) ^ 8) ≤
      64 ^ 2 * (r : ℝ) ^ 12 := by nlinarith [hdr8]
  have hterm2 : (d : ℝ) * (5 * (d : ℝ) ^ 3) ≤
      5 * (r : ℝ) ^ 12 := by nlinarith [hd4]
  have hterm3 : (d : ℝ) * ((d : ℝ) * 64 * (r : ℝ) ^ 6 * 4) ≤
      256 * (r : ℝ) ^ 12 := by nlinarith [hd2r6]
  have hr12pos : (0 : ℝ) < (r : ℝ) ^ 12 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp
  nlinarith [hterm1, hterm2, hterm3]

theorem overlapWeightSum_lt_half
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hr : 1 ≤ r) (hdr : d ≤ r ^ 3)
    (i : BadIndex V) :
    (∑ j ∈ overlapNeighbors BadIndex.support i,
      validWeight G r (64 * r ^ 4) j) < 1 / 2 :=
  (overlapWeightSum_le G hdeg hdr i).trans_lt (numerical_weight_bound hr hdr)

open Finset

theorem one_sub_sum_le_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (y : ι → ℝ)
    (hy0 : ∀ i ∈ s, 0 ≤ y i) (hy1 : ∀ i ∈ s, y i ≤ 1) :
    1 - ∑ i ∈ s, y i ≤ ∏ i ∈ s, (1 - y i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hih := ih (fun i hi ↦ hy0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hy1 i (Finset.mem_insert_of_mem hi))
      have hsum : 0 ≤ ∑ i ∈ s, y i :=
        Finset.sum_nonneg fun i hi ↦ hy0 i (Finset.mem_insert_of_mem hi)
      calc
        1 - (y a + ∑ i ∈ s, y i) ≤ (1 - y a) * (1 - ∑ i ∈ s, y i) := by
          nlinarith [hy0 a (Finset.mem_insert_self a s)]
        _ ≤ (1 - y a) * ∏ i ∈ s, (1 - y i) := by
          exact mul_le_mul_of_nonneg_left hih
            (sub_nonneg.mpr (hy1 a (Finset.mem_insert_self a s)))

theorem validWeight_lt_one
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 1 ≤ r)
    (i : BadIndex V) : validWeight G r (64 * r ^ 4) i < 1 := by
  classical
  have hrpos : 0 < r := by omega
  have hxNat : 2 < 64 * r ^ 4 := by
    nlinarith [Nat.one_le_pow 4 r hrpos]
  have hx : (2 : ℝ) < (64 * r ^ 4 : ℕ) := by exact_mod_cast hxNat
  have hxOne : (1 : ℝ) ≤ (64 * r ^ 4 : ℕ) := hx.le.trans' (by norm_num)
  have hx2 : ((64 * r ^ 4 : ℕ) : ℝ) ≤ ((64 * r ^ 4 : ℕ) : ℝ) ^ 2 := by
    calc
      ((64 * r ^ 4 : ℕ) : ℝ) = ((64 * r ^ 4 : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((64 * r ^ 4 : ℕ) : ℝ) * ((64 * r ^ 4 : ℕ) : ℝ) := by gcongr
      _ = ((64 * r ^ 4 : ℕ) : ℝ) ^ 2 := by ring
  have hx3 : ((64 * r ^ 4 : ℕ) : ℝ) ≤ ((64 * r ^ 4 : ℕ) : ℝ) ^ 3 := by
    calc
      ((64 * r ^ 4 : ℕ) : ℝ) ≤ ((64 * r ^ 4 : ℕ) : ℝ) ^ 2 := hx2
      _ = ((64 * r ^ 4 : ℕ) : ℝ) ^ 2 * 1 := by ring
      _ ≤ ((64 * r ^ 4 : ℕ) : ℝ) ^ 2 * ((64 * r ^ 4 : ℕ) : ℝ) := by gcongr
      _ = ((64 * r ^ 4 : ℕ) : ℝ) ^ 3 := by ring
  unfold validWeight
  split
  · unfold eventWeight
    cases i <;> simp only [BadIndex.constraintCount]
    all_goals apply (div_lt_one (by positivity)).2
    · simpa using hx
    · exact hx.trans_le hx3
    · exact hx.trans_le hx2
    · simpa using hx
  · exact zero_lt_one

theorem neighbor_product_ge_half
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hr : 1 ≤ r) (hdr : d ≤ r ^ 3)
    (i : BadIndex V) :
    (1 / 2 : ℝ) < ∏ j ∈ overlapNeighbors BadIndex.support i,
      (1 - validWeight G r (64 * r ^ 4) j) := by
  have hsum := overlapWeightSum_lt_half G hdeg hr hdr i
  have hprod := one_sub_sum_le_prod
    (overlapNeighbors BadIndex.support i) (validWeight G r (64 * r ^ 4))
    (fun j hj ↦ validWeight_nonneg G r (64 * r ^ 4) j)
    (fun j hj ↦ (validWeight_lt_one G r hr j).le)
  linarith

theorem exists_acyclic_coloring_of_cube_bound
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d r : ℕ} (hdeg : ∀ v, G.degree v ≤ d) (hr : 1 ≤ r) (hdr : d ≤ r ^ 3) :
    ∃ color : V → Fin (64 * r ^ 4), IsAcyclicColoring G color := by
  classical
  let x := 64 * r ^ 4
  have hx : 0 < x := by dsimp [x]; positivity
  let bad : BadIndex V → (V → Fin x) → Prop := fun i ↦ i.occurs G r
  let y : BadIndex V → ℝ := validWeight G r x
  let neighbor : BadIndex V → Finset (BadIndex V) :=
    overlapNeighbors BadIndex.support
  letI : Nonempty (Fin x) := Fin.pos_iff_nonempty.mp hx
  have hy0 : ∀ i, 0 ≤ y i := fun i ↦ validWeight_nonneg G r x i
  have hy1 : ∀ i, y i < 1 := by
    intro i
    simpa [x, y] using validWeight_lt_one G r hr i
  have hmass : ∀ i,
      ((restricted bad i ∅).card : ℝ) ≤
        y i * (∏ j ∈ neighbor i, (1 - y j)) * Fintype.card (V → Fin x) := by
    intro i
    by_cases hvalid : i.Valid G r
    · have hcard : (restricted bad i ∅).card =
          Fintype.card {ω : V → Fin x // i.occurs G r ω} := by
        symm
        apply Fintype.card_of_subtype
        intro ω
        simp [bad]
      have hcount := occurs_card_mul_palette_pow_le (C := Fin x) G r i
      have hcountNat :
          Fintype.card {ω : V → Fin x // i.occurs G r ω} *
              x ^ i.constraintCount ≤ Fintype.card (V → Fin x) := by
        simpa using hcount
      have hcountR :
          (Fintype.card {ω : V → Fin x // i.occurs G r ω} : ℝ) *
              (x : ℝ) ^ i.constraintCount ≤ Fintype.card (V → Fin x) := by
        exact_mod_cast hcountNat
      have hq : (0 : ℝ) < (x : ℝ) ^ i.constraintCount := by positivity
      have hprob :
          (Fintype.card {ω : V → Fin x // i.occurs G r ω} : ℝ) ≤
            (Fintype.card (V → Fin x) : ℝ) /
              (x : ℝ) ^ i.constraintCount :=
        (le_div_iff₀ hq).2 hcountR
      have hprod : (1 / 2 : ℝ) < ∏ j ∈ neighbor i, (1 - y j) := by
        simpa [x, y, neighbor] using neighbor_product_ge_half G hdeg hr hdr i
      rw [hcard]
      calc
        (Fintype.card {ω : V → Fin x // i.occurs G r ω} : ℝ) ≤
            (Fintype.card (V → Fin x) : ℝ) /
              (x : ℝ) ^ i.constraintCount := hprob
        _ = (2 / (x : ℝ) ^ i.constraintCount) * (1 / 2) *
              Fintype.card (V → Fin x) := by field_simp
        _ ≤ (2 / (x : ℝ) ^ i.constraintCount) *
              (∏ j ∈ neighbor i, (1 - y j)) * Fintype.card (V → Fin x) := by
          gcongr
        _ = y i * (∏ j ∈ neighbor i, (1 - y j)) *
              Fintype.card (V → Fin x) := by
          simp [y, validWeight, hvalid, eventWeight]
    · have hempty : restricted bad i ∅ = ∅ := by
        ext ω
        simp [bad, BadIndex.occurs, hvalid]
      simp [hempty, y, validWeight, hvalid]
  have hindep : ∀ i T, (∀ j ∈ T, j ∉ neighbor i) →
      ((restricted bad i T).card : ℝ) * Fintype.card (V → Fin x) =
        ((restricted bad i ∅).card : ℝ) * (avoid bad T).card := by
    simpa [bad, neighbor] using
      (restricted_independent_of_support
        (bad := fun i : BadIndex V ↦ (i.occurs G r : (V → Fin x) → Prop))
        (support := BadIndex.support) (fun i ↦ i.occurs_determined G r))
  obtain ⟨color, hcolor⟩ := finite_local_lemma bad neighbor y hy0 hy1 hmass hindep
  simpa [x] using (show ∃ color : V → Fin x, IsAcyclicColoring G color from
    ⟨color, acyclic_of_avoid G r color hcolor⟩)

def cubeCeil (d : ℕ) : ℕ := Nat.nthRoot 3 d + 1

theorem cubeCeil_pos (d : ℕ) : 1 ≤ cubeCeil d := by
  simp [cubeCeil]

theorem le_cube_cubeCeil (d : ℕ) : d ≤ cubeCeil d ^ 3 := by
  exact (Nat.lt_pow_nthRoot_add_one (by norm_num : (3 : ℕ) ≠ 0) d).le

theorem cube_cubeCeil_le_eight_mul {d : ℕ} (hd : 1 ≤ d) :
    cubeCeil d ^ 3 ≤ 8 * d := by
  let a := Nat.nthRoot 3 d
  have ha : 1 ≤ a := by
    rw [show a = Nat.nthRoot 3 d by rfl, Nat.le_nthRoot_iff (by norm_num)]
    simpa using hd
  have hacube : a ^ 3 ≤ d := by
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have ha2 : a ^ 2 ≤ a ^ 3 := by
    calc
      a ^ 2 = a ^ 2 * 1 := by ring
      _ ≤ a ^ 2 * a := Nat.mul_le_mul_left _ ha
      _ = a ^ 3 := by ring
  have ha1 : a ≤ a ^ 3 := by
    calc
      a = a * 1 := by ring
      _ ≤ a * a := Nat.mul_le_mul_left _ ha
      _ = a ^ 2 := by ring
      _ ≤ a ^ 3 := ha2
  have hone : 1 ≤ a ^ 3 := Nat.one_le_pow 3 a (by omega)
  dsimp [cubeCeil, a]
  nlinarith

theorem acyclicBound_cubeCeil (d : ℕ) :
    AcyclicBound d (64 * cubeCeil d ^ 4) := by
  intro n G hG
  classical
  have hdeg : ∀ v, G.degree v ≤ d := by
    intro v
    exact (G.degree_le_maxDegree v).trans (by simpa [graphMaxDegree] using hG)
  exact exists_acyclic_coloring_of_cube_bound G hdeg (cubeCeil_pos d)
    (le_cube_cubeCeil d)

theorem extremalAcyclicNumber_le_cubeCeil (d : ℕ) :
    f₇₉₇ d ≤ 64 * cubeCeil d ^ 4 :=
  extremalAcyclicNumber_le (acyclicBound_cubeCeil d)

/-- Integer-power form of the AMR upper estimate.  It is exactly the
rounding-free assertion `f(d) = O(d^(4/3))`. -/
theorem extremalAcyclicNumber_cube_le {d : ℕ} (hd : 1 ≤ d) :
    f₇₉₇ d ^ 3 ≤ 1024 ^ 3 * d ^ 4 := by
  have hf := Nat.pow_le_pow_left (extremalAcyclicNumber_le_cubeCeil d) 3
  have hr := Nat.pow_le_pow_left (cube_cubeCeil_le_eight_mul hd) 4
  calc
    f₇₉₇ d ^ 3 ≤ (64 * cubeCeil d ^ 4) ^ 3 := hf
    _ = 64 ^ 3 * (cubeCeil d ^ 3) ^ 4 := by ring
    _ ≤ 64 ^ 3 * (8 * d) ^ 4 := Nat.mul_le_mul_left _ hr
    _ = 1024 ^ 3 * d ^ 4 := by ring

end UpperBound

end

end Erdos797


namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

/-- `q` disjoint monochromatic pairs, represented by one injective map. -/
def MonochromaticPairing {V C : Type*} (c : V → C) (q : ℕ) : Prop :=
  ∃ p : Fin q × Fin 2 → V, Injective p ∧ ∀ i, c (p (i, 0)) = c (p (i, 1))

theorem exists_distinct_same_color
    {V C : Type*} [Fintype V] [Fintype C] (c : V → C)
    (hcard : Fintype.card C < Fintype.card V) :
    ∃ u v : V, u ≠ v ∧ c u = c v := by
  by_contra h
  push_neg at h
  have hc : Injective c := fun u v huv ↦ by
    by_contra huv'
    exact h u v huv' huv
  exact (not_le_of_gt hcard) (Fintype.card_le_of_injective c hc)

theorem exists_monochromaticPairing
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (c : V → C) (q : ℕ)
    (hcard : 2 * q + Fintype.card C ≤ Fintype.card V) :
    MonochromaticPairing c q := by
  induction q generalizing V with
  | zero =>
      refine ⟨fun z ↦ Fin.elim0 z.1, ?_, fun i ↦ Fin.elim0 i⟩
      intro x
      exact Fin.elim0 x.1
  | succ q ih =>
      have hlt : Fintype.card C < Fintype.card V := by omega
      obtain ⟨u, v, huv, hcol⟩ := exists_distinct_same_color c hlt
      let W := ↑(({u, v} : Finset V)ᶜ)
      let c' : W → C := c ∘ Subtype.val
      have hW : Fintype.card W = Fintype.card V - 2 := by
        dsimp only [W]
        rw [Fintype.card_coe]
        rw [Finset.card_compl, Finset.card_pair_eq_two_iff.mpr huv]
      have hcard' : 2 * q + Fintype.card C ≤ Fintype.card W := by
        rw [hW]
        omega
      obtain ⟨p, hp, hpc⟩ := ih c' hcard'
      let pV : Fin q × Fin 2 → V := Subtype.val ∘ p
      have hpV : Injective pV := Subtype.val_injective.comp hp
      let last : Fin 2 → V := fun j ↦ if j = 0 then u else v
      have hlast : Injective last := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [last]
      have hrange : Disjoint (Set.range pV) (Set.range last) := by
        rw [Set.disjoint_left]
        rintro x ⟨ij, rfl⟩ ⟨j, hj⟩
        have hpnot := (p ij).property
        fin_cases j <;> simp_all [W, pV, last]
      let P : Fin (q + 1) × Fin 2 → V := fun z ↦
        if h : (z.1 : ℕ) < q then pV (⟨z.1, h⟩, z.2) else last z.2
      refine ⟨P, ?_, ?_⟩
      · rintro ⟨i, a⟩ ⟨j, b⟩ hab
        by_cases hi : (i : ℕ) < q <;> by_cases hj : (j : ℕ) < q
        · let i' : Fin q := ⟨i, hi⟩
          let j' : Fin q := ⟨j, hj⟩
          have hpij : (i', a) = (j', b) := hpV (by simpa [P, hi, hj, i', j'] using hab)
          have hij' : i' = j' := congrArg (fun z : Fin q × Fin 2 ↦ z.1) hpij
          have hab' : a = b := congrArg (fun z : Fin q × Fin 2 ↦ z.2) hpij
          have hval : (i : ℕ) = (j : ℕ) := by
            simpa [i', j'] using congrArg Fin.val hij'
          apply Prod.ext
          · exact Fin.ext hval
          · exact hab'
        · exfalso
          let i' : Fin q := ⟨i, hi⟩
          have heq : pV (i', a) = last b := by simpa [P, hi, hj, i'] using hab
          exact Set.disjoint_left.mp hrange (Set.mem_range_self (i', a)) ⟨b, heq.symm⟩
        · exfalso
          let j' : Fin q := ⟨j, hj⟩
          have heq : pV (j', b) = last a := by simpa [P, hi, hj, j'] using hab.symm
          exact Set.disjoint_left.mp hrange (Set.mem_range_self (j', b)) ⟨a, heq.symm⟩
        · have hij : i = j := by apply Fin.ext; omega
          subst j
          have hab' : last a = last b := by simpa [P, hi, hj] using hab
          rw [hlast hab']
      · intro i
        by_cases hi : (i : ℕ) < q
        · let i' : Fin q := ⟨i, hi⟩
          simpa [P, hi, i', pV, c'] using hpc i'
        · simp [P, hi, last, hcol]

def graphOfSample {V : Type*} {M : ℕ} [NeZero M]
    (ω : V × V → Fin M) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ω (u, v) = 0 ∧ ω (v, u) = 0
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩

@[simp] theorem graphOfSample_adj {V : Type*} {M : ℕ} [NeZero M]
    (ω : V × V → Fin M) (u v : V) :
    (graphOfSample ω).Adj u v ↔
      u ≠ v ∧ ω (u, v) = 0 ∧ ω (v, u) = 0 := Iff.rfl

instance graphOfSample_decidableAdj {V : Type*} [DecidableEq V]
    {M : ℕ} [NeZero M] (ω : V × V → Fin M) :
    DecidableRel (graphOfSample ω).Adj := by
  intro u v
  simp only [graphOfSample_adj]
  infer_instance

theorem not_acyclic_of_monochromatic_square
    {V C : Type*} {G : SimpleGraph V} {c : V → C}
    {v0 v1 v2 v3 : V}
    (h01 : G.Adj v0 v1) (h12 : G.Adj v1 v2)
    (h23 : G.Adj v2 v3) (h30 : G.Adj v3 v0)
    (h02 : v0 ≠ v2) (h13 : v1 ≠ v3)
    (hc02 : c v0 = c v2) (hc13 : c v1 = c v3) :
    ¬ IsAcyclicColoring G c := by
  intro hc
  let w : G.Walk v0 v0 :=
    .cons h01 (.cons h12 (.cons h23 (.cons h30 .nil)))
  have hn01 : v0 ≠ v1 := h01.ne
  have hn12 : v1 ≠ v2 := h12.ne
  have hn23 : v2 ≠ v3 := h23.ne
  have hn30 : v3 ≠ v0 := h30.ne
  have hw : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    simp [w, Sym2.eq_iff, hn01, hn01.symm, hn12, hn12.symm,
      hn23, hn23.symm, hn30, hn30.symm, h02, h02.symm, h13, h13.symm]
  apply hc.2 w hw
  refine ⟨c v0, c v1, ?_⟩
  intro u hu
  simp [w] at hu
  rcases hu with rfl | rfl | rfl | hu
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl hc02.symm
  · rcases hu with rfl | rfl
    · exact Or.inr hc13.symm
    · exact Or.inl rfl

/-- A coloring is square-safe when it has no properly embedded complete
two-by-two bipartite graph whose two sides are monochromatic.  This is the
finite obstruction used in the AMR lower bound. -/
def IsSquareSafe {V C : Type*} (G : SimpleGraph V) (c : V → C) : Prop :=
  ∀ v0 v1 v2 v3,
    v0 ≠ v2 → v1 ≠ v3 → c v0 = c v2 → c v1 = c v3 →
      ¬ (G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v0)

theorem IsAcyclicColoring.isSquareSafe
    {V C : Type*} {G : SimpleGraph V} {c : V → C}
    (hc : IsAcyclicColoring G c) : IsSquareSafe G c := by
  intro v0 v1 v2 v3 h02 h13 hc02 hc13 h
  exact not_acyclic_of_monochromatic_square h.1 h.2.1 h.2.2.1 h.2.2.2
    h02 h13 hc02 hc13 hc

abbrev PairIndex (q : ℕ) := {z : Fin q × Fin q // z.1 < z.2}

@[simp] theorem card_pairIndex (q : ℕ) :
    Fintype.card (PairIndex q) = q.choose 2 := by
  classical
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin q))

abbrev BlockSlot := Fin 2 × Fin 2 × Fin 2

@[simp] theorem card_blockSlot : Fintype.card BlockSlot = 8 := by simp [BlockSlot]

def blockCoord {V : Type*} {q : ℕ} (p : Fin q × Fin 2 → V) :
    PairIndex q × BlockSlot → V × V := fun z ↦
  if z.2.2.2 = 0 then
    (p (z.1.1.1, z.2.1), p (z.1.1.2, z.2.2.1))
  else
    (p (z.1.1.2, z.2.2.1), p (z.1.1.1, z.2.1))

theorem blockCoord_injective {V : Type*} {q : ℕ}
    {p : Fin q × Fin 2 → V} (hp : Injective p) :
    Injective (blockCoord p) := by
  rintro ⟨⟨⟨i, j⟩, hij⟩, a, b, d⟩ ⟨⟨⟨k, l⟩, hkl⟩, c, e, t⟩ h
  fin_cases d <;> fin_cases t
  · simp only [blockCoord, Fin.isValue, Fin.zero_eta, ↓reduceIte] at h
    have h1 : (i, a) = (k, c) := hp (Prod.mk.inj h).1
    have h2 : (j, b) = (l, e) := hp (Prod.mk.inj h).2
    cases h1
    cases h2
    rfl
  · simp only [blockCoord, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      OfNat.ofNat, ne_eq, one_ne_zero, ↓reduceIte] at h
    have h1 : (i, a) = (l, e) := hp (Prod.mk.inj h).1
    have h2 : (j, b) = (k, c) := hp (Prod.mk.inj h).2
    have hil : i = l := congrArg Prod.fst h1
    have hjk : j = k := congrArg Prod.fst h2
    subst l
    subst k
    exact (lt_asymm hij hkl).elim
  · simp only [blockCoord, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      OfNat.ofNat, ne_eq, one_ne_zero, ↓reduceIte] at h
    have h1 : (j, b) = (k, c) := hp (Prod.mk.inj h).1
    have h2 : (i, a) = (l, e) := hp (Prod.mk.inj h).2
    have hjk : j = k := congrArg Prod.fst h1
    have hil : i = l := congrArg Prod.fst h2
    subst k
    subst l
    exact (lt_asymm hij hkl).elim
  · simp only [blockCoord, Fin.isValue, Fin.mk_one, OfNat.ofNat,
      ne_eq, one_ne_zero, ↓reduceIte] at h
    have h1 : (j, b) = (l, e) := hp (Prod.mk.inj h).1
    have h2 : (i, a) = (k, c) := hp (Prod.mk.inj h).2
    cases h1
    cases h2
    rfl

theorem squareSafe_implies_blockGood
    {V C : Type*} {q M : ℕ} [NeZero M]
    (p : Fin q × Fin 2 → V) (hp : Injective p)
    (c : V → C) (hmono : ∀ i, c (p (i, 0)) = c (p (i, 1)))
    (ω : V × V → Fin M) (hc : IsSquareSafe (graphOfSample ω) c) :
    ∀ z : PairIndex q, ∃ r : BlockSlot, ω (blockCoord p (z, r)) ≠ 0 := by
  intro z
  by_contra h
  push Not at h
  let i := z.1.1
  let j := z.1.2
  let v0 := p (i, 0)
  let v1 := p (j, 0)
  let v2 := p (i, 1)
  let v3 := p (j, 1)
  have h01 : (graphOfSample ω).Adj v0 v1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have := hp heq
      have : i = j := congrArg Prod.fst this
      exact (ne_of_lt z.2) this
    · simpa [blockCoord, v0, v1, i, j] using h ((0, 0, 0) : BlockSlot)
    · simpa [blockCoord, v0, v1, i, j] using h ((0, 0, 1) : BlockSlot)
  have h12 : (graphOfSample ω).Adj v1 v2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have := hp heq
      have : j = i := congrArg Prod.fst this
      exact (ne_of_gt z.2) this
    · simpa [blockCoord, v1, v2, i, j] using h ((1, 0, 1) : BlockSlot)
    · simpa [blockCoord, v1, v2, i, j] using h ((1, 0, 0) : BlockSlot)
  have h23 : (graphOfSample ω).Adj v2 v3 := by
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have := hp heq
      have : i = j := congrArg Prod.fst this
      exact (ne_of_lt z.2) this
    · simpa [blockCoord, v2, v3, i, j] using h ((1, 1, 0) : BlockSlot)
    · simpa [blockCoord, v2, v3, i, j] using h ((1, 1, 1) : BlockSlot)
  have h30 : (graphOfSample ω).Adj v3 v0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      have := hp heq
      have : j = i := congrArg Prod.fst this
      exact (ne_of_gt z.2) this
    · simpa [blockCoord, v3, v0, i, j] using h ((0, 1, 1) : BlockSlot)
    · simpa [blockCoord, v3, v0, i, j] using h ((0, 1, 0) : BlockSlot)
  have h02 : v0 ≠ v2 := fun heq ↦ by
    have := hp heq
    exact Fin.zero_ne_one (congrArg Prod.snd this)
  have h13 : v1 ≠ v3 := fun heq ↦ by
    have := hp heq
    exact Fin.zero_ne_one (congrArg Prod.snd this)
  exact hc v0 v1 v2 v3 h02 h13 (hmono i) (hmono j)
    ⟨h01, h12, h23, h30⟩

theorem acyclic_implies_blockGood
    {V C : Type*} {q M : ℕ} [NeZero M]
    (p : Fin q × Fin 2 → V) (hp : Injective p)
    (c : V → C) (hmono : ∀ i, c (p (i, 0)) = c (p (i, 1)))
    (ω : V × V → Fin M) (hc : IsAcyclicColoring (graphOfSample ω) c) :
    ∀ z : PairIndex q, ∃ r : BlockSlot, ω (blockCoord p (z, r)) ≠ 0 :=
  squareSafe_implies_blockGood p hp c hmono ω
    (IsAcyclicColoring.isSquareSafe hc)

end

end Erdos797.LowerBound

namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

abbrev RowGood {R C : Type*} (base : C) (g : R → C) : Prop :=
  ∃ r, g r ≠ base

noncomputable instance rowGoodFintype {R C : Type*} [Finite R] [Finite C]
    (base : C) : Fintype {g : R → C // RowGood base g} := Fintype.ofFinite _

noncomputable instance goodRowsFintype {B R C : Type*} [Finite B] [Finite R]
    [Finite C] (base : C) :
    Fintype {h : B → R → C // ∀ b, RowGood base (h b)} := Fintype.ofFinite _

noncomputable instance blockAvoidanceFintype {B R E C : Type*}
    [Finite B] [Finite R] [Finite E] [Finite C]
    (base : C) (f : B × R → E) :
    Fintype {w : E → C // ∀ b, ∃ r, w (f (b, r)) ≠ base} := Fintype.ofFinite _

noncomputable instance acyclicSamplesFintype
    {V C : Type*} [Finite V] [Finite C] {M : ℕ} [NeZero M]
    (c : V → C) :
    Fintype {ω : V × V → Fin M // IsAcyclicColoring (graphOfSample ω) c} :=
  Fintype.ofFinite _

noncomputable instance someAcyclicColoringSamplesFintype
    {V : Type*} [Finite V] {q M : ℕ} [NeZero M] :
    Fintype {ω : V × V → Fin M //
      ∃ c : V → Fin q, IsAcyclicColoring (graphOfSample ω) c} :=
  Fintype.ofFinite _

noncomputable instance squareSafeSamplesFintype
    {V C : Type*} [Finite V] [Finite C] {M : ℕ} [NeZero M]
    (c : V → C) :
    Fintype {ω : V × V → Fin M // IsSquareSafe (graphOfSample ω) c} :=
  Fintype.ofFinite _

noncomputable instance someSquareSafeColoringSamplesFintype
    {V : Type*} [Finite V] {q M : ℕ} [NeZero M] :
    Fintype {ω : V × V → Fin M //
      ∃ c : V → Fin q, IsSquareSafe (graphOfSample ω) c} :=
  Fintype.ofFinite _

theorem card_rowGood {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (base : C) :
    Fintype.card {g : R → C // RowGood base g} =
      Fintype.card C ^ Fintype.card R - 1 := by
  classical
  let Bad : (R → C) → Prop := fun g ↦ ∀ r, g r = base
  have hgood : Fintype.card {g : R → C // RowGood base g} =
      Fintype.card {g : R → C // ¬ Bad g} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (by
      intro g
      simp [RowGood, Bad])
  have hbad : Fintype.card {g : R → C // Bad g} = 1 := by
    letI : Unique {g : R → C // Bad g} :=
      { default := ⟨fun _ ↦ base, fun _ ↦ rfl⟩
        uniq := by
          intro g
          apply Subtype.ext
          funext r
          exact g.property r }
    exact Fintype.card_unique
  rw [hgood, Fintype.card_subtype_compl Bad, hbad]
  simp

private def goodRowsEquiv {B R C : Type*} (base : C) :
    {h : B → R → C // ∀ b, RowGood base (h b)} ≃
      ((b : B) → {g : R → C // RowGood base g}) where
  toFun h b := ⟨h.1 b, h.2 b⟩
  invFun h := ⟨fun b ↦ (h b).1, fun b ↦ (h b).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_goodRows {B R C : Type*} [Fintype B] [Fintype R] [Fintype C]
    [DecidableEq C]
    (base : C) :
    Fintype.card {h : B → R → C // ∀ b, RowGood base (h b)} =
      (Fintype.card C ^ Fintype.card R - 1) ^ Fintype.card B := by
  classical
  rw [Fintype.card_congr (goodRowsEquiv base), Fintype.card_pi]
  simp [card_rowGood]

private def splitGoodEquiv
    {B R E C : Type*} [Fintype B] [Fintype R] [DecidableEq E] [DecidableEq C]
    (base : C) (f : B × R → E) (hf : Injective f) :
    {w : E → C // ∀ b, ∃ r, w (f (b, r)) ≠ base} ≃
      {h : B → R → C // ∀ b, RowGood base (h b)} ×
        (((Set.range f)ᶜ : Set E) → C) := by
  let fr : B × R ≃ Set.range f := Equiv.ofInjective f hf
  refine
    { toFun := fun w ↦
        (⟨fun b r ↦ w.1 (f (b, r)), w.2⟩,
          fun e ↦ w.1 e)
      invFun := fun z ↦
        ⟨fun e ↦ if he : e ∈ Set.range f then
            z.1.1 (fr.symm ⟨e, he⟩).1 (fr.symm ⟨e, he⟩).2 else z.2 ⟨e, he⟩,
          fun b ↦ by
            obtain ⟨r, hr⟩ := z.1.2 b
            refine ⟨r, ?_⟩
            simpa [fr] using hr⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    apply Subtype.ext
    funext e
    by_cases he : e ∈ Set.range f
    · obtain ⟨a, rfl⟩ := he
      simp [fr]
    · simp [he]
  · rintro ⟨h, k⟩
    apply Prod.ext
    · apply Subtype.ext
      funext b r
      simp [fr]
    · funext e
      change (if he : (e : E) ∈ Set.range f then
          h.1 (fr.symm ⟨e, he⟩).1 (fr.symm ⟨e, he⟩).2 else k ⟨e, he⟩) = k e
      rw [dif_neg e.property]

theorem card_block_avoidance_mul
    {B R E C : Type*} [Fintype B] [Fintype R] [Fintype E]
    [Fintype C] [DecidableEq E] [DecidableEq C]
    (base : C) (f : B × R → E) (hf : Injective f) :
    Fintype.card {w : E → C // ∀ b, ∃ r, w (f (b, r)) ≠ base} *
        Fintype.card C ^ (Fintype.card B * Fintype.card R) =
      (Fintype.card C ^ Fintype.card R - 1) ^ Fintype.card B *
        Fintype.card (E → C) := by
  classical
  let K := ((Set.range f)ᶜ : Set E)
  have hsplit := Fintype.card_congr (splitGoodEquiv base f hf)
  have hA : Fintype.card (B × R) = Fintype.card B * Fintype.card R := by simp
  have hRange : Fintype.card (Set.range f) = Fintype.card (B × R) := by
    symm
    exact Fintype.card_congr (Equiv.ofInjective f hf)
  have hE : Fintype.card E = Fintype.card B * Fintype.card R + Fintype.card K := by
    calc
      Fintype.card E = Fintype.card (Set.range f) + Fintype.card K := by
        symm
        simpa only [Fintype.card_sum] using
          (Fintype.card_congr (Equiv.Set.sumCompl (Set.range f)))
      _ = _ := by rw [hRange, hA]
  rw [hsplit]
  simp only [Fintype.card_prod, Fintype.card_fun]
  rw [card_goodRows]
  rw [hE, pow_add]
  ring

theorem card_acyclic_samples_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} [NeZero M]
    (c : V → Fin q) (hcard : 3 * q ≤ Fintype.card V) :
    Fintype.card {ω : V × V → Fin M //
        IsAcyclicColoring (graphOfSample ω) c} * M ^ (8 * q.choose 2) ≤
      (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
  classical
  have hcard' : 2 * q + Fintype.card (Fin q) ≤ Fintype.card V := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨p, hp, hmono⟩ := exists_monochromaticPairing c q hcard'
  let Good : (V × V → Fin M) → Prop := fun ω ↦
    ∀ z : PairIndex q, ∃ r : BlockSlot, ω (blockCoord p (z, r)) ≠ 0
  have hsub : ∀ ω, IsAcyclicColoring (graphOfSample ω) c → Good ω := by
    intro ω hω
    exact acyclic_implies_blockGood p hp c hmono ω hω
  have hle : Fintype.card {ω : V × V → Fin M //
        IsAcyclicColoring (graphOfSample ω) c} ≤
      Fintype.card {ω : V × V → Fin M // Good ω} :=
    Fintype.card_subtype_mono _ _ hsub
  have hcount := card_block_avoidance_mul
    (base := (0 : Fin M)) (f := blockCoord p) (blockCoord_injective hp)
  change Fintype.card {ω : V × V → Fin M // Good ω} *
      Fintype.card (Fin M) ^
        (Fintype.card (PairIndex q) * Fintype.card BlockSlot) =
    (Fintype.card (Fin M) ^ Fintype.card BlockSlot - 1) ^
        Fintype.card (PairIndex q) * Fintype.card (V × V → Fin M) at hcount
  rw [card_pairIndex q] at hcount
  have hcount' :
      Fintype.card {ω : V × V → Fin M // Good ω} *
          M ^ (q.choose 2 * 8) =
        (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
    simpa only [card_blockSlot, Fintype.card_fin] using hcount
  calc
    Fintype.card {ω : V × V → Fin M //
        IsAcyclicColoring (graphOfSample ω) c} * M ^ (8 * q.choose 2) ≤
        Fintype.card {ω : V × V → Fin M // Good ω} *
          M ^ (8 * q.choose 2) := Nat.mul_le_mul_right _ hle
    _ = (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
      simpa only [Nat.mul_comm] using hcount'

theorem card_squareSafe_samples_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} [NeZero M]
    (c : V → Fin q) (hcard : 3 * q ≤ Fintype.card V) :
    Fintype.card {ω : V × V → Fin M //
        IsSquareSafe (graphOfSample ω) c} * M ^ (8 * q.choose 2) ≤
      (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
  classical
  have hcard' : 2 * q + Fintype.card (Fin q) ≤ Fintype.card V := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨p, hp, hmono⟩ := exists_monochromaticPairing c q hcard'
  let Good : (V × V → Fin M) → Prop := fun ω ↦
    ∀ z : PairIndex q, ∃ r : BlockSlot, ω (blockCoord p (z, r)) ≠ 0
  have hsub : ∀ ω, IsSquareSafe (graphOfSample ω) c → Good ω := by
    intro ω hω
    exact squareSafe_implies_blockGood p hp c hmono ω hω
  have hle : Fintype.card {ω : V × V → Fin M //
        IsSquareSafe (graphOfSample ω) c} ≤
      Fintype.card {ω : V × V → Fin M // Good ω} :=
    Fintype.card_subtype_mono _ _ hsub
  have hcount := card_block_avoidance_mul
    (base := (0 : Fin M)) (f := blockCoord p) (blockCoord_injective hp)
  change Fintype.card {ω : V × V → Fin M // Good ω} *
      Fintype.card (Fin M) ^
        (Fintype.card (PairIndex q) * Fintype.card BlockSlot) =
    (Fintype.card (Fin M) ^ Fintype.card BlockSlot - 1) ^
        Fintype.card (PairIndex q) * Fintype.card (V × V → Fin M) at hcount
  rw [card_pairIndex q] at hcount
  have hcount' :
      Fintype.card {ω : V × V → Fin M // Good ω} *
          M ^ (q.choose 2 * 8) =
        (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
    simpa only [card_blockSlot, Fintype.card_fin] using hcount
  calc
    Fintype.card {ω : V × V → Fin M //
        IsSquareSafe (graphOfSample ω) c} * M ^ (8 * q.choose 2) ≤
        Fintype.card {ω : V × V → Fin M // Good ω} *
          M ^ (8 * q.choose 2) := Nat.mul_le_mul_right _ hle
    _ = (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
      simpa only [Nat.mul_comm] using hcount'

theorem natCard_exists_le_sum
    {I X : Type*} [Fintype I] [Fintype X]
    (A : I → X → Prop) :
    Nat.card {x : X // ∃ i, A i x} ≤
      ∑ i : I, Nat.card {x : X // A i x} := by
  classical
  let pick : {x : X // ∃ i, A i x} → Σ i : I, {x : X // A i x} := fun x ↦
    ⟨Classical.choose x.2, x.1, Classical.choose_spec x.2⟩
  have hpick : Injective pick := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Σ i : I, {x : X // A i x} ↦ z.2.1) h
  calc
    Nat.card {x : X // ∃ i, A i x} ≤
        Nat.card (Σ i : I, {x : X // A i x}) :=
      Nat.card_le_card_of_injective pick hpick
    _ = ∑ i : I, Nat.card {x : X // A i x} := Nat.card_sigma

theorem card_some_acyclic_coloring_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} [NeZero M]
    (hcard : 3 * q ≤ Fintype.card V) :
    Fintype.card {ω : V × V → Fin M //
        ∃ c : V → Fin q, IsAcyclicColoring (graphOfSample ω) c} *
        M ^ (8 * q.choose 2) ≤
      q ^ Fintype.card V * (M ^ 8 - 1) ^ q.choose 2 *
        Fintype.card (V × V → Fin M) := by
  classical
  let A : (V → Fin q) → (V × V → Fin M) → Prop :=
    fun c ω ↦ IsAcyclicColoring (graphOfSample ω) c
  have hunion := natCard_exists_le_sum A
  calc
    Fintype.card {ω : V × V → Fin M //
        ∃ c : V → Fin q, IsAcyclicColoring (graphOfSample ω) c} *
        M ^ (8 * q.choose 2) ≤
      (∑ c : V → Fin q,
        Fintype.card {ω : V × V → Fin M // A c ω}) *
          M ^ (8 * q.choose 2) := Nat.mul_le_mul_right _ (by
            simpa [A, Nat.card_eq_fintype_card] using hunion)
    _ = ∑ c : V → Fin q,
        Fintype.card {ω : V × V → Fin M // A c ω} *
          M ^ (8 * q.choose 2) := by rw [Finset.sum_mul]
    _ ≤ ∑ _c : V → Fin q,
        (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
      exact Finset.sum_le_sum fun c _ ↦ by
        simpa [A] using card_acyclic_samples_mul_le c hcard
    _ = q ^ Fintype.card V * (M ^ 8 - 1) ^ q.choose 2 *
        Fintype.card (V × V → Fin M) := by
      simp [mul_assoc]

theorem card_some_squareSafe_coloring_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} [NeZero M]
    (hcard : 3 * q ≤ Fintype.card V) :
    Fintype.card {ω : V × V → Fin M //
        ∃ c : V → Fin q, IsSquareSafe (graphOfSample ω) c} *
        M ^ (8 * q.choose 2) ≤
      q ^ Fintype.card V * (M ^ 8 - 1) ^ q.choose 2 *
        Fintype.card (V × V → Fin M) := by
  classical
  let A : (V → Fin q) → (V × V → Fin M) → Prop :=
    fun c ω ↦ IsSquareSafe (graphOfSample ω) c
  have hunion := natCard_exists_le_sum A
  calc
    Fintype.card {ω : V × V → Fin M //
        ∃ c : V → Fin q, IsSquareSafe (graphOfSample ω) c} *
        M ^ (8 * q.choose 2) ≤
      (∑ c : V → Fin q,
        Fintype.card {ω : V × V → Fin M // A c ω}) *
          M ^ (8 * q.choose 2) := Nat.mul_le_mul_right _ (by
            simpa [A, Nat.card_eq_fintype_card] using hunion)
    _ = ∑ c : V → Fin q,
        Fintype.card {ω : V × V → Fin M // A c ω} *
          M ^ (8 * q.choose 2) := by rw [Finset.sum_mul]
    _ ≤ ∑ _c : V → Fin q,
        (M ^ 8 - 1) ^ q.choose 2 * Fintype.card (V × V → Fin M) := by
      exact Finset.sum_le_sum fun c _ ↦ by
        simpa [A] using card_squareSafe_samples_mul_le c hcard
    _ = q ^ Fintype.card V * (M ^ 8 - 1) ^ q.choose 2 *
        Fintype.card (V × V → Fin M) := by
      simp [mul_assoc]

end

end Erdos797.LowerBound

namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

theorem two_mul_sub_one_pow_le_pow {a : ℕ} (ha : 2 ≤ a) :
    2 * (a - 1) ^ a ≤ a ^ a := by
  have ha0 : a ≠ 0 := by omega
  have hbern : (a - 1) ^ a + a * (a - 1) ^ (a - 1) * 1 ≤
      ((a - 1) + 1) ^ a := by
    exact pow_add_mul_le_add_pow_of_sq_nonneg (R := ℕ) (by omega)
      (by positivity) (by positivity) (by omega) a
  have hself : (a - 1) ^ a ≤ a * (a - 1) ^ (a - 1) := by
    rw [← pow_sub_one_mul ha0]
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_right ((a - 1) ^ (a - 1)) (Nat.sub_le a 1))
  calc
    2 * (a - 1) ^ a = (a - 1) ^ a + (a - 1) ^ a := by omega
    _ ≤ (a - 1) ^ a + a * (a - 1) ^ (a - 1) := Nat.add_le_add_left hself _
    _ ≤ ((a - 1) + 1) ^ a := by simpa using hbern
    _ = a ^ a := by rw [Nat.sub_add_cancel (by omega)]

theorem pow_loss_of_blocks {a Q L : ℕ} (ha : 2 ≤ a) (hQ : a * L ≤ Q) :
    2 ^ L * (a - 1) ^ Q ≤ a ^ Q := by
  let t := Q - a * L
  have hQt : a * L + t = Q := Nat.add_sub_of_le hQ
  have hb := Nat.pow_le_pow_left (two_mul_sub_one_pow_le_pow ha) L
  have hb' : 2 ^ L * (a - 1) ^ (a * L) ≤ a ^ (a * L) := by
    simpa [mul_pow, pow_mul] using hb
  have ht : (a - 1) ^ t ≤ a ^ t :=
    Nat.pow_le_pow_left (Nat.sub_le a 1) t
  calc
    2 ^ L * (a - 1) ^ Q =
        (2 ^ L * (a - 1) ^ (a * L)) * (a - 1) ^ t := by
      rw [← hQt, pow_add]
      ring
    _ ≤ a ^ (a * L) * a ^ t := Nat.mul_le_mul hb' ht
    _ = a ^ Q := by rw [← pow_add, hQt]

def lowerM (s : ℕ) := 2 ^ s
def lowerA (s : ℕ) := lowerM s ^ 8
def lowerQ (s : ℕ) := 256 * s * lowerA s
def lowerN (s : ℕ) := 4 * lowerQ s
def lowerL (s : ℕ) := 120 * s * lowerQ s

instance lowerM_neZero (s : ℕ) : NeZero (lowerM s) :=
  ⟨by simp [lowerM]⟩

theorem lowerA_eq (s : ℕ) : lowerA s = 2 ^ (8 * s) := by
  simp [lowerA, lowerM, pow_mul, Nat.mul_comm]

theorem lowerQ_le_two_pow {s : ℕ} (hs : 1 ≤ s) :
    lowerQ s ≤ 2 ^ (16 * s) := by
  by_cases hs1 : s = 1
  · subst s
    norm_num [lowerQ, lowerA, lowerM]
  · have hs2 : 2 ≤ s := by omega
    have hspow : s ≤ 2 ^ s := s.lt_two_pow_self.le
    have hsexp : s ≤ 8 * s - 8 := by omega
    have hpowmono : 2 ^ s ≤ 2 ^ (8 * s - 8) := Nat.pow_le_pow_right (by omega) hsexp
    have hsmall : 2 ^ 8 * s ≤ 2 ^ (8 * s) := by
      calc
        2 ^ 8 * s ≤ 2 ^ 8 * 2 ^ (8 * s - 8) := Nat.mul_le_mul_left _ (hspow.trans hpowmono)
        _ = 2 ^ (8 * s) := by rw [← pow_add]; congr; omega
    rw [lowerQ, lowerA_eq]
    calc
      256 * s * 2 ^ (8 * s) = (2 ^ 8 * s) * 2 ^ (8 * s) := by norm_num
      _ ≤ 2 ^ (8 * s) * 2 ^ (8 * s) := Nat.mul_le_mul_right _ hsmall
      _ = 2 ^ (16 * s) := by rw [← pow_add]; congr; omega

theorem lower_choose_blocks {s : ℕ} (hs : 1 ≤ s) :
    lowerA s * lowerL s ≤ (lowerQ s).choose 2 := by
  rw [Nat.choose_two_right]
  have hA : 1 ≤ lowerA s := by
    exact Nat.one_le_pow 8 (lowerM s) (by simp [lowerM])
  have hq : lowerQ s = 256 * s * lowerA s := rfl
  have hq16 : 16 ≤ lowerQ s := by rw [hq]; nlinarith
  have heven : 2 ∣ lowerQ s := by
    rw [hq]
    simpa [mul_assoc] using
      (dvd_mul_of_dvd_left (by norm_num : 2 ∣ 256) (s * lowerA s))
  obtain ⟨k, hk⟩ := heven
  rw [hk]
  have hdiv : 2 * k * (2 * k - 1) / 2 = k * (2 * k - 1) := by
    calc
      2 * k * (2 * k - 1) / 2 = 2 * (k * (2 * k - 1)) / 2 := by ring
      _ = k * (2 * k - 1) := Nat.mul_div_right _ (by norm_num)
  rw [hdiv]
  have hkval : k = 128 * s * lowerA s := by
    have : 2 * k = 256 * s * lowerA s := hk.symm.trans hq
    apply Nat.mul_left_cancel (n := 2) (by norm_num)
    calc
      2 * k = 256 * s * lowerA s := this
      _ = 2 * (128 * s * lowerA s) := by ring
  have hcoef : 120 * lowerQ s ≤ 128 * (lowerQ s - 1) := by
    omega
  calc
    lowerA s * lowerL s = (s * lowerA s) * (120 * lowerQ s) := by
      simp [lowerL]
      ring
    _ ≤ (s * lowerA s) * (128 * (lowerQ s - 1)) :=
      Nat.mul_le_mul_left _ hcoef
    _ = (128 * s * lowerA s) * (lowerQ s - 1) := by ring
    _ = k * (lowerQ s - 1) := by rw [hkval]
    _ = k * (2 * k - 1) := by rw [hk]

theorem lower_color_numeric {s : ℕ} (hs : 1 ≤ s) :
    4 * lowerQ s ^ lowerN s * (lowerM s ^ 8 - 1) ^ (lowerQ s).choose 2 <
      lowerM s ^ (8 * (lowerQ s).choose 2) := by
  have hM : 2 ≤ lowerM s := by
    rw [lowerM]
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) hs)
  have hA : 2 ≤ lowerA s := by
    simpa [lowerA] using
      ((by norm_num : 2 ≤ 2 ^ 8).trans (Nat.pow_le_pow_left hM 8))
  have hblocks := pow_loss_of_blocks hA (lower_choose_blocks hs)
  have hqpow := Nat.pow_le_pow_left (lowerQ_le_two_pow hs) (lowerN s)
  have hqpow' : lowerQ s ^ lowerN s ≤ 2 ^ (16 * s * lowerN s) := by
    simpa [pow_mul] using hqpow
  have hqpos : 0 < lowerQ s := by
    simp [lowerQ, lowerA, lowerM]
    positivity
  have hsq : 1 ≤ s * lowerQ s := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hexp : 2 + 16 * s * lowerN s < lowerL s := by
    rw [lowerN, lowerL]
    nlinarith
  have hfront : 4 * lowerQ s ^ lowerN s < 2 ^ lowerL s := by
    calc
      4 * lowerQ s ^ lowerN s ≤ 2 ^ 2 * 2 ^ (16 * s * lowerN s) :=
        Nat.mul_le_mul_left _ hqpow'
      _ = 2 ^ (2 + 16 * s * lowerN s) := by rw [pow_add]
      _ < 2 ^ lowerL s := Nat.pow_lt_pow_right (by omega) hexp
  have hloss : 2 ^ lowerL s * (lowerA s - 1) ^ (lowerQ s).choose 2 ≤
      lowerA s ^ (lowerQ s).choose 2 := hblocks
  calc
    4 * lowerQ s ^ lowerN s * (lowerM s ^ 8 - 1) ^ (lowerQ s).choose 2 <
        2 ^ lowerL s * (lowerA s - 1) ^ (lowerQ s).choose 2 := by
      rw [lowerA]
      apply Nat.mul_lt_mul_of_pos_right hfront
      apply pow_pos
      have : 0 < lowerM s ^ 8 - 1 := by
        rw [← lowerA]
        omega
      exact this
    _ ≤ lowerA s ^ (lowerQ s).choose 2 := hloss
    _ = lowerM s ^ (8 * (lowerQ s).choose 2) := by
      rw [lowerA, ← pow_mul]

end

end Erdos797.LowerBound

namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

theorem lower_squareSafe_samples_quarter {s : ℕ} (hs : 1 ≤ s) :
    4 * Fintype.card {ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s) //
      ∃ c : Fin (lowerN s) → Fin (lowerQ s),
        IsSquareSafe (graphOfSample ω) c} <
      Fintype.card (Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) := by
  classical
  letI : NeZero (lowerM s) := ⟨by simp [lowerM]⟩
  let C := Fintype.card {ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s) //
    ∃ c : Fin (lowerN s) → Fin (lowerQ s),
      IsSquareSafe (graphOfSample ω) c}
  let P := lowerM s ^ (8 * (lowerQ s).choose 2)
  let R := lowerQ s ^ lowerN s *
    (lowerM s ^ 8 - 1) ^ (lowerQ s).choose 2
  let T := Fintype.card
    (Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s))
  have hcard : 3 * lowerQ s ≤ Fintype.card (Fin (lowerN s)) := by
    rw [Fintype.card_eq_nat_card, Nat.card_fin, lowerN]
    omega
  have hcount : C * P ≤ R * T := by
    simpa only [C, P, R, T, Fintype.card_fin] using
      (card_some_squareSafe_coloring_mul_le
        (V := Fin (lowerN s)) (q := lowerQ s) (M := lowerM s) hcard)
  have hnumeric : 4 * R < P := by
    simpa only [R, P, Nat.mul_assoc] using lower_color_numeric hs
  have hP : 0 < P := by
    dsimp only [P]
    exact pow_pos (by simp [lowerM]) _
  have hT : 0 < T := by
    dsimp only [T]
    exact Fintype.card_pos_iff.mpr ⟨fun _ ↦ 0⟩
  have hmul : (4 * C) * P < T * P := by
    calc
      (4 * C) * P = 4 * (C * P) := by ring
      _ ≤ 4 * (R * T) := Nat.mul_le_mul_left 4 hcount
      _ = (4 * R) * T := by ring
      _ < P * T := (Nat.mul_lt_mul_right hT).2 hnumeric
      _ = T * P := Nat.mul_comm _ _
  exact (Nat.mul_lt_mul_right hP).mp hmul

end

end Erdos797.LowerBound

namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

def twoFixedMap {E : Type*} [DecidableEq E] {M : ℕ} [NeZero M]
    (e f : E) :
    ({ω : E → Fin M // ω e = 0 ∧ ω f = 0}) × (Fin M × Fin M) →
      (E → Fin M) := fun z x ↦
  if x = e then z.2.1 else if x = f then z.2.2 else z.1.1 x

theorem twoFixedMap_injective {E : Type*} [DecidableEq E] {M : ℕ} [NeZero M]
    {e f : E} (hef : e ≠ f) : Injective (twoFixedMap (M := M) e f) := by
  rintro ⟨ω, ⟨a, b⟩⟩ ⟨ω', ⟨a', b'⟩⟩ h
  have ha : a = a' := by
    simpa [twoFixedMap] using congrFun h e
  have hb : b = b' := by
    simpa [twoFixedMap, hef.symm] using congrFun h f
  have hω : ω = ω' := by
    apply Subtype.ext
    funext x
    by_cases hxe : x = e
    · subst x
      exact ω.property.1.trans ω'.property.1.symm
    · by_cases hxf : x = f
      · subst x
        exact ω.property.2.trans ω'.property.2.symm
      · simpa [twoFixedMap, hxe, hxf] using congrFun h x
  cases hω
  cases ha
  cases hb
  rfl

theorem card_two_fixed_mul_le
    {E : Type*} [Fintype E] [DecidableEq E] {M : ℕ} [NeZero M]
    {e f : E} (hef : e ≠ f) :
    Fintype.card {ω : E → Fin M // ω e = 0 ∧ ω f = 0} * M ^ 2 ≤
      Fintype.card (E → Fin M) := by
  classical
  have hle := Fintype.card_le_of_injective (twoFixedMap (M := M) e f)
    (twoFixedMap_injective (M := M) hef)
  simpa [pow_two] using hle

def dartCount {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (ω : V × V → Fin M) : ℕ :=
  ((Finset.univ : Finset (V × V)).filter
    (fun z ↦ (graphOfSample ω).Adj z.1 z.2)).card

def adjSampleCount {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (u v : V) : ℕ :=
  ((Finset.univ : Finset (V × V → Fin M)).filter
    (fun ω ↦ (graphOfSample ω).Adj u v)).card

theorem card_adj_samples_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (u v : V) :
    Fintype.card {ω : V × V → Fin M // (graphOfSample ω).Adj u v} * M ^ 2 ≤
      Fintype.card (V × V → Fin M) := by
  classical
  by_cases huv : u = v
  · subst v
    simp [graphOfSample_adj]
  · have hfixed := card_two_fixed_mul_le (M := M)
      (e := (u, v)) (f := (v, u)) (by
        intro h
        exact huv (congrArg Prod.fst h))
    simpa [graphOfSample_adj, huv] using hfixed

theorem sum_dartCount_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] :
    (∑ ω : V × V → Fin M, dartCount ω) * M ^ 2 ≤
      Fintype.card (V × V) * Fintype.card (V × V → Fin M) := by
  classical
  have hdart (ω : V × V → Fin M) :
      dartCount ω = ∑ z : V × V,
        if (graphOfSample ω).Adj z.1 z.2 then 1 else 0 := by
    rw [dartCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hadj (z : V × V) : adjSampleCount (M := M) z.1 z.2 =
      ∑ ω : V × V → Fin M,
        if (graphOfSample ω).Adj z.1 z.2 then 1 else 0 := by
    rw [adjSampleCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hid : (∑ ω : V × V → Fin M, dartCount ω) =
      ∑ z : V × V, adjSampleCount (M := M) z.1 z.2 := by
    simp_rw [hdart, hadj]
    exact Finset.sum_comm
  rw [hid, Finset.sum_mul]
  calc
    ∑ z : V × V,
        adjSampleCount (M := M) z.1 z.2 * M ^ 2 ≤
      ∑ _z : V × V, Fintype.card (V × V → Fin M) := by
        exact Finset.sum_le_sum fun z _ ↦ by
          simpa only [adjSampleCount, Fintype.card_subtype] using
            card_adj_samples_mul_le (M := M) z.1 z.2
    _ = Fintype.card (V × V) * Fintype.card (V × V → Fin M) := by
      simp

def IsDenseSample {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (ω : V × V → Fin M) : Prop :=
  4 * Fintype.card V ^ 2 < M ^ 2 * dartCount ω

noncomputable instance isDenseSampleDecidable
    {V : Type*} [Fintype V] [DecidableEq V] {M : ℕ} [NeZero M] :
    DecidablePred (IsDenseSample (V := V) (M := M)) := Classical.decPred _

theorem lower_dense_samples_quarter {s : ℕ} (hs : 1 ≤ s) :
    4 * ((Finset.univ : Finset
      (Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s))).filter
        IsDenseSample).card <
      Fintype.card
        (Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) := by
  classical
  let Ω := Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)
  let D := (Finset.univ : Finset Ω).filter IsDenseSample
  let n := Fintype.card (Fin (lowerN s))
  let T := Fintype.card Ω
  have hn : 0 < n := by
    dsimp only [n]
    rw [Fintype.card_eq_nat_card, Nat.card_fin]
    simp only [lowerN, lowerQ, lowerA, lowerM]
    positivity
  have hn2 : 0 < n ^ 2 := pow_pos hn _
  have hT : 0 < T := by
    dsimp only [T, Ω]
    exact Fintype.card_pos_iff.mpr ⟨fun _ ↦ 0⟩
  have havg :
      (lowerM s) ^ 2 * (∑ ω : Ω, dartCount ω) ≤ n ^ 2 * T := by
    have h := sum_dartCount_mul_le
      (V := Fin (lowerN s)) (M := lowerM s)
    simpa only [Ω, n, T, Fintype.card_prod, pow_two,
      Nat.mul_comm] using h
  by_cases hD : D = ∅
  · simpa only [D, hD, Finset.card_empty, mul_zero] using hT
  · have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD
    have hstrict : D.card * (4 * n ^ 2) <
        ∑ ω ∈ D, (lowerM s) ^ 2 * dartCount ω := by
      calc
        D.card * (4 * n ^ 2) = ∑ _ω ∈ D, 4 * n ^ 2 := by simp
        _ < ∑ ω ∈ D, (lowerM s) ^ 2 * dartCount ω := by
          apply Finset.sum_lt_sum_of_nonempty hDne
          intro ω hω
          have hdense : IsDenseSample ω := (Finset.mem_filter.mp hω).2
          simpa only [IsDenseSample, n] using hdense
    have hsubset : (∑ ω ∈ D, (lowerM s) ^ 2 * dartCount ω) ≤
        (lowerM s) ^ 2 * (∑ ω : Ω, dartCount ω) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by simp)
    have hchain : D.card * (4 * n ^ 2) < n ^ 2 * T :=
      hstrict.trans_le (hsubset.trans havg)
    apply (Nat.mul_lt_mul_right hn2).mp
    simpa only [D, T, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain

theorem exists_sparse_square_obstructing_sample {s : ℕ} (hs : 1 ≤ s) :
    ∃ ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s),
      (∀ c : Fin (lowerN s) → Fin (lowerQ s),
        ¬ IsSquareSafe (graphOfSample ω) c) ∧
      lowerM s ^ 2 * dartCount ω ≤ 4 * lowerN s ^ 2 := by
  classical
  let Ω := Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)
  let A := (Finset.univ : Finset Ω).filter (fun ω ↦
    ∃ c : Fin (lowerN s) → Fin (lowerQ s),
      IsSquareSafe (graphOfSample ω) c)
  let B := (Finset.univ : Finset Ω).filter IsDenseSample
  let T := Fintype.card Ω
  have hA : 4 * A.card < T := by
    simpa only [A, T, Ω, Fintype.card_subtype] using
      lower_squareSafe_samples_quarter hs
  have hB : 4 * B.card < T := by
    simpa only [B, T, Ω] using lower_dense_samples_quarter hs
  have hsum : A.card + B.card < T := by omega
  have hunion : (A ∪ B).card < T :=
    (Finset.card_union_le A B).trans_lt hsum
  have hex : ∃ ω : Ω, ω ∉ A ∪ B := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset Ω) ⊆ A ∪ B := by
      intro ω _
      exact h ω
    have hc := Finset.card_le_card hsub
    have hcard : (Finset.univ : Finset Ω).card = T := by
      simp [T]
    rw [hcard] at hc
    omega
  obtain ⟨ω, hω⟩ := hex
  have hnotA : ω ∉ A := fun hmem ↦ hω (Finset.mem_union_left B hmem)
  have hnotB : ω ∉ B := fun hmem ↦ hω (Finset.mem_union_right A hmem)
  refine ⟨ω, ?_, ?_⟩
  · simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] using hnotA
  · have hdense : ¬ IsDenseSample ω := by
      simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hnotB
    rw [IsDenseSample, Fintype.card_eq_nat_card, Nat.card_fin] at hdense
    omega

end

end Erdos797.LowerBound

namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

theorem dartCount_eq_sum_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (ω : V × V → Fin M) :
    dartCount ω = ∑ v, (graphOfSample ω).degree v := by
  classical
  rw [dartCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]

def highVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (ω : V × V → Fin M) : Finset V :=
  Finset.univ.filter (fun v ↦
    32 * Fintype.card V < M ^ 2 * (graphOfSample ω).degree v)

theorem eight_mul_card_highVertices_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} [NeZero M] (ω : V × V → Fin M)
    (hn : 0 < Fintype.card V)
    (hsparse : M ^ 2 * dartCount ω ≤ 4 * Fintype.card V ^ 2) :
    8 * (highVertices ω).card < Fintype.card V := by
  classical
  let H := highVertices ω
  let n := Fintype.card V
  have hn4 : 0 < 4 * n := by positivity
  by_cases hH : H = ∅
  · simpa only [H, hH, Finset.card_empty, mul_zero] using hn
  · have hHne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH
    have hstrict : H.card * (32 * n) <
        ∑ v ∈ H, M ^ 2 * (graphOfSample ω).degree v := by
      calc
        H.card * (32 * n) = ∑ _v ∈ H, 32 * n := by simp
        _ < ∑ v ∈ H, M ^ 2 * (graphOfSample ω).degree v := by
          apply Finset.sum_lt_sum_of_nonempty hHne
          intro v hv
          have hv' := (Finset.mem_filter.mp hv).2
          simpa only [H, highVertices, n] using hv'
    have hsubset : (∑ v ∈ H, M ^ 2 * (graphOfSample ω).degree v) ≤
        M ^ 2 * (∑ v, (graphOfSample ω).degree v) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by simp)
    have hchain : H.card * (32 * n) < 4 * n ^ 2 := by
      calc
        H.card * (32 * n) <
            ∑ v ∈ H, M ^ 2 * (graphOfSample ω).degree v := hstrict
        _ ≤ M ^ 2 * (∑ v, (graphOfSample ω).degree v) := hsubset
        _ = M ^ 2 * dartCount ω := by rw [dartCount_eq_sum_degree]
        _ ≤ 4 * n ^ 2 := hsparse
    apply (Nat.mul_lt_mul_right hn4).mp
    dsimp only [H, n]
    convert hchain using 1 <;> ring

def lowerK (s : ℕ) := 128 * s * lowerA s

def lowerD (s : ℕ) := 32768 * s * lowerM s ^ 6

theorem lowerQ_eq_two_mul_lowerK (s : ℕ) :
    lowerQ s = 2 * lowerK s := by
  simp only [lowerQ, lowerK]
  ring

theorem lowerM_sq_mul_lowerD (s : ℕ) :
    lowerM s ^ 2 * lowerD s = 32 * lowerN s := by
  simp only [lowerD, lowerN, lowerQ, lowerA]
  ring

theorem degree_le_lowerD_of_not_mem_high
    {s : ℕ} (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s))
    {v : Fin (lowerN s)} (hv : v ∉ highVertices ω) :
    (graphOfSample ω).degree v ≤ lowerD s := by
  classical
  have hM : 0 < lowerM s := by simp [lowerM]
  have hnot : ¬ 32 * lowerN s <
      lowerM s ^ 2 * (graphOfSample ω).degree v := by
    simpa only [highVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.card_eq_nat_card, Nat.card_fin] using hv
  have hle : lowerM s ^ 2 * (graphOfSample ω).degree v ≤
      32 * lowerN s := by omega
  apply Nat.le_of_mul_le_mul_left
  · rw [lowerM_sq_mul_lowerD]
    exact hle
  · exact pow_pos hM 2

end

end Erdos797.LowerBound

namespace Erdos797.LowerBound

noncomputable section

open Finset Function Set

abbrev LowVertices {s : ℕ}
    (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :=
  {v : Fin (lowerN s) // v ∉ highVertices ω}

def lowGraph {s : ℕ}
    (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :
    SimpleGraph (LowVertices ω) :=
  (graphOfSample ω).induce {v | v ∉ highVertices ω}

noncomputable instance lowGraph_decidableAdj {s : ℕ}
    (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :
    DecidableRel (lowGraph ω).Adj := Classical.decRel _

theorem lowerN_eq_eight_mul_lowerK (s : ℕ) :
    lowerN s = 8 * lowerK s := by
  rw [lowerN, lowerQ_eq_two_mul_lowerK]
  ring

theorem card_highVertices_lt_lowerK
    {s : ℕ} (hs : 1 ≤ s)
    {ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)}
    (hsparse : lowerM s ^ 2 * dartCount ω ≤ 4 * lowerN s ^ 2) :
    (highVertices ω).card < lowerK s := by
  have hn : 0 < Fintype.card (Fin (lowerN s)) := by
    rw [Fintype.card_eq_nat_card, Nat.card_fin]
    simp [lowerN, lowerQ, lowerA, lowerM]
    positivity
  have h := eight_mul_card_highVertices_lt ω hn (by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using hsparse)
  rw [Fintype.card_eq_nat_card, Nat.card_fin] at h
  have hnK := lowerN_eq_eight_mul_lowerK s
  omega

theorem exists_monochromatic_square_lowGraph
    {s : ℕ} (hs : 1 ≤ s)
    {ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)}
    (hsparse : lowerM s ^ 2 * dartCount ω ≤ 4 * lowerN s ^ 2)
    (hobstruct : ∀ c : Fin (lowerN s) → Fin (lowerQ s),
      ¬ IsSquareSafe (graphOfSample ω) c) :
    ∀ c : LowVertices ω → Fin (lowerK s),
      ∃ v0 v1 v2 v3 : LowVertices ω,
        (lowGraph ω).Adj v0 v1 ∧ (lowGraph ω).Adj v1 v2 ∧
        (lowGraph ω).Adj v2 v3 ∧ (lowGraph ω).Adj v3 v0 ∧
        v0 ≠ v2 ∧ v1 ≠ v3 ∧ c v0 = c v2 ∧ c v1 = c v3 := by
  classical
  intro c
  let H := highVertices ω
  let X := Sum (Fin (lowerK s)) {v : Fin (lowerN s) // v ∈ H}
  have hhigh : H.card < lowerK s := by
    simpa only [H] using card_highVertices_lt_lowerK hs hsparse
  have hXcard : Fintype.card X ≤ lowerQ s := by
    rw [Fintype.card_eq_nat_card, Nat.card_sum, Nat.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_coe, lowerQ_eq_two_mul_lowerK]
    omega
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let enc : X → Fin (lowerQ s) := Fin.castLE hXcard ∘ eX
  have henc : Injective enc :=
    (Fin.castLE_injective hXcard).comp eX.injective
  let C : Fin (lowerN s) → Fin (lowerQ s) := fun v ↦
    if hv : v ∈ H then enc (Sum.inr ⟨v, hv⟩)
    else enc (Sum.inl (c ⟨v, hv⟩))
  have hunique : ∀ (v : Fin (lowerN s)) (hv : v ∈ H)
      (u : Fin (lowerN s)), C v = C u → u = v := by
    intro v hv u hcu
    by_cases hu : u ∈ H
    · have hx : (Sum.inr ⟨v, hv⟩ : X) = Sum.inr ⟨u, hu⟩ :=
        henc (by simpa only [C, dif_pos hv, dif_pos hu] using hcu)
      have hx' : (⟨v, hv⟩ : {v : Fin (lowerN s) // v ∈ H}) = ⟨u, hu⟩ :=
        Sum.inr.inj hx
      exact (congrArg Subtype.val hx').symm
    · have hx : (Sum.inr ⟨v, hv⟩ : X) = Sum.inl (c ⟨u, hu⟩) :=
        henc (by simpa only [C, dif_pos hv, dif_neg hu] using hcu)
      exact (Sum.inr_ne_inl hx).elim
  have hbad := hobstruct C
  rw [IsSquareSafe] at hbad
  push Not at hbad
  obtain ⟨v0, v1, v2, v3, h02, h13, hc02, hc13, hadj⟩ := hbad
  have hv0 : v0 ∉ H := by
    intro hv
    exact h02 (hunique v0 hv v2 hc02).symm
  have hv2 : v2 ∉ H := by
    intro hv
    exact h02 (hunique v2 hv v0 hc02.symm)
  have hv1 : v1 ∉ H := by
    intro hv
    exact h13 (hunique v1 hv v3 hc13).symm
  have hv3 : v3 ∉ H := by
    intro hv
    exact h13 (hunique v3 hv v1 hc13.symm)
  have hc02' : c ⟨v0, hv0⟩ = c ⟨v2, hv2⟩ := by
    have hx : (Sum.inl (c ⟨v0, hv0⟩) : X) = Sum.inl (c ⟨v2, hv2⟩) :=
      henc (by simpa only [C, dif_neg hv0, dif_neg hv2] using hc02)
    exact Sum.inl.inj hx
  have hc13' : c ⟨v1, hv1⟩ = c ⟨v3, hv3⟩ := by
    have hx : (Sum.inl (c ⟨v1, hv1⟩) : X) = Sum.inl (c ⟨v3, hv3⟩) :=
      henc (by simpa only [C, dif_neg hv1, dif_neg hv3] using hc13)
    exact Sum.inl.inj hx
  exact ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩, ⟨v2, hv2⟩, ⟨v3, hv3⟩,
    hadj.1, hadj.2.1, hadj.2.2.1, hadj.2.2.2,
    fun h ↦ h02 (congrArg Subtype.val h),
    fun h ↦ h13 (congrArg Subtype.val h), hc02', hc13'⟩

theorem no_acyclic_coloring_lowGraph
    {s : ℕ} (hs : 1 ≤ s)
    {ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)}
    (hsparse : lowerM s ^ 2 * dartCount ω ≤ 4 * lowerN s ^ 2)
    (hobstruct : ∀ c : Fin (lowerN s) → Fin (lowerQ s),
      ¬ IsSquareSafe (graphOfSample ω) c) :
    ∀ c : LowVertices ω → Fin (lowerK s),
      ¬ IsAcyclicColoring (lowGraph ω) c := by
  intro c hc
  obtain ⟨v0, v1, v2, v3, h01, h12, h23, h30, h02, h13, hc02, hc13⟩ :=
    exists_monochromatic_square_lowGraph hs hsparse hobstruct c
  exact not_acyclic_of_monochromatic_square h01 h12 h23 h30 h02 h13
    hc02 hc13 hc

def lowEquiv {s : ℕ}
    (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :
    Fin (Fintype.card (LowVertices ω)) ≃ LowVertices ω :=
  (Fintype.equivFin (LowVertices ω)).symm

def relabeledLowGraph {s : ℕ}
    (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :
    SimpleGraph (Fin (Fintype.card (LowVertices ω))) :=
  (lowGraph ω).comap (lowEquiv ω)

noncomputable instance relabeledLowGraph_decidableAdj {s : ℕ}
    (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :
    DecidableRel (relabeledLowGraph ω).Adj := Classical.decRel _

theorem relabeledLowGraph_maxDegree_le
    {s : ℕ} (ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)) :
    graphMaxDegree (relabeledLowGraph ω) ≤ lowerD s := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro i
  let emb : ↑((relabeledLowGraph ω).neighborFinset i) →
    ↑((graphOfSample ω).neighborFinset (lowEquiv ω i).1) := fun x ↦
    ⟨(lowEquiv ω x.1).1, by
      apply ((graphOfSample ω).mem_neighborFinset
        (lowEquiv ω i).1 (lowEquiv ω x.1).1).mpr
      have hx := ((relabeledLowGraph ω).mem_neighborFinset i x.1).mp x.2
      exact hx⟩
  have hemb : Injective emb := by
    intro x y h
    apply Subtype.ext
    apply (lowEquiv ω).injective
    apply Subtype.ext
    exact congrArg (fun z ↦ z.1) h
  have hdeg : (relabeledLowGraph ω).degree i ≤
      (graphOfSample ω).degree (lowEquiv ω i).1 := by
    simpa only [SimpleGraph.degree, Fintype.card_coe] using
      (Fintype.card_le_of_injective emb hemb)
  exact hdeg.trans
    (degree_le_lowerD_of_not_mem_high ω (lowEquiv ω i).2)

theorem no_acyclic_coloring_relabeledLowGraph
    {s : ℕ} (hs : 1 ≤ s)
    {ω : Fin (lowerN s) × Fin (lowerN s) → Fin (lowerM s)}
    (hsparse : lowerM s ^ 2 * dartCount ω ≤ 4 * lowerN s ^ 2)
    (hobstruct : ∀ c : Fin (lowerN s) → Fin (lowerQ s),
      ¬ IsSquareSafe (graphOfSample ω) c) :
    ∀ c : Fin (Fintype.card (LowVertices ω)) → Fin (lowerK s),
      ¬ IsAcyclicColoring (relabeledLowGraph ω) c := by
  intro c hc
  let cLow : LowVertices ω → Fin (lowerK s) := c ∘ (lowEquiv ω).symm
  obtain ⟨v0, v1, v2, v3, h01, h12, h23, h30, h02, h13, hc02, hc13⟩ :=
    exists_monochromatic_square_lowGraph hs hsparse hobstruct cLow
  apply not_acyclic_of_monochromatic_square
    (G := relabeledLowGraph ω) (c := c)
    (v0 := (lowEquiv ω).symm v0) (v1 := (lowEquiv ω).symm v1)
    (v2 := (lowEquiv ω).symm v2) (v3 := (lowEquiv ω).symm v3)
  · simpa [relabeledLowGraph] using h01
  · simpa [relabeledLowGraph] using h12
  · simpa [relabeledLowGraph] using h23
  · simpa [relabeledLowGraph] using h30
  · exact (lowEquiv ω).symm.injective.ne h02
  · exact (lowEquiv ω).symm.injective.ne h13
  · exact hc02
  · exact hc13
  · exact hc

theorem exists_lower_graph {s : ℕ} (hs : 1 ≤ s) :
    ∃ m : ℕ, ∃ G : SimpleGraph (Fin m),
      graphMaxDegree G ≤ lowerD s ∧
      ∀ c : Fin m → Fin (lowerK s), ¬ IsAcyclicColoring G c := by
  obtain ⟨ω, hobstruct, hsparse⟩ := exists_sparse_square_obstructing_sample hs
  exact ⟨Fintype.card (LowVertices ω), relabeledLowGraph ω,
    relabeledLowGraph_maxDegree_le ω,
    no_acyclic_coloring_relabeledLowGraph hs hsparse hobstruct⟩

theorem extremalAcyclicNumber_spec (d : ℕ) :
    AcyclicBound d (f₇₉₇ d) := by
  change sInf {k : ℕ | AcyclicBound d k} ∈ {k : ℕ | AcyclicBound d k}
  apply Nat.sInf_mem
  exact ⟨64 * UpperBound.cubeCeil d ^ 4,
    UpperBound.acyclicBound_cubeCeil d⟩

theorem lt_extremalAcyclicNumber_of_not_bound {d k : ℕ}
    (h : ¬ AcyclicBound d k) : k < f₇₉₇ d := by
  by_contra hnot
  have hle : f₇₉₇ d ≤ k := by omega
  exact h ((extremalAcyclicNumber_spec d).mono_colors hle)

/-- Exact finite family underlying the AMR lower estimate. -/
theorem lowerK_lt_extremalAcyclicNumber {s : ℕ} (hs : 1 ≤ s) :
    lowerK s < f₇₉₇ (lowerD s) := by
  apply lt_extremalAcyclicNumber_of_not_bound
  intro hbound
  obtain ⟨m, G, hdeg, hno⟩ := exists_lower_graph hs
  obtain ⟨c, hc⟩ := hbound m G hdeg
  exact hno c hc

end

end Erdos797.LowerBound

namespace Erdos797

noncomputable section

open Finset Function Set

namespace LowerBound

theorem extremalAcyclicNumber_mono : Monotone f₇₉₇ := by
  intro d e hde
  exact extremalAcyclicNumber_le
    ((extremalAcyclicNumber_spec e).anti_degree hde)

theorem exists_scale_above (d : ℕ) :
    ∃ s : ℕ, d < lowerD (s + 1) := by
  refine ⟨d, ?_⟩
  have hfac : 1 ≤ 32768 * lowerM (d + 1) ^ 6 := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 6 (by simp [lowerM]))
  calc
    d < d + 1 := by omega
    _ = (d + 1) * 1 := by ring
    _ ≤ (d + 1) * (32768 * lowerM (d + 1) ^ 6) :=
      Nat.mul_le_mul_left _ hfac
    _ = lowerD (d + 1) := by simp only [lowerD]; ring

def scaleIndex (d : ℕ) : ℕ := Nat.find (exists_scale_above d)

theorem lt_lowerD_scaleIndex_succ (d : ℕ) :
    d < lowerD (scaleIndex d + 1) :=
  Nat.find_spec (exists_scale_above d)

theorem scaleIndex_pos {d : ℕ} (hd : lowerD 1 ≤ d) :
    0 < scaleIndex d := by
  by_contra hzero
  have hspec := lt_lowerD_scaleIndex_succ d
  rw [Nat.eq_zero_of_not_pos hzero] at hspec
  simp only [zero_add] at hspec
  omega

theorem lowerD_scaleIndex_le {d : ℕ} (hd : lowerD 1 ≤ d) :
    lowerD (scaleIndex d) ≤ d := by
  have hspos := scaleIndex_pos hd
  have hmin : ¬ d < lowerD ((scaleIndex d - 1) + 1) := by
    apply Nat.find_min (exists_scale_above d)
    change scaleIndex d - 1 < scaleIndex d
    omega
  rw [Nat.sub_add_cancel hspos] at hmin
  omega

theorem lowerD_succ_le {s : ℕ} (hs : 1 ≤ s) :
    lowerD (s + 1) ≤ 128 * lowerD s := by
  have hstep : s + 1 ≤ 2 * s := by omega
  have hM : lowerM (s + 1) ^ 6 = 64 * lowerM s ^ 6 := by
    simp only [lowerM, pow_succ, mul_pow]
    norm_num
    ring
  rw [lowerD, lowerD, hM]
  calc
    32768 * (s + 1) * (64 * lowerM s ^ 6) ≤
        32768 * (2 * s) * (64 * lowerM s ^ 6) := by gcongr
    _ = 128 * (32768 * s * lowerM s ^ 6) := by ring

theorem exists_adjacent_lower_scale {d : ℕ} (hd : lowerD 1 ≤ d) :
    ∃ s : ℕ, 1 ≤ s ∧ lowerD s ≤ d ∧ d < 128 * lowerD s ∧
      lowerK s < f₇₉₇ d := by
  let s := scaleIndex d
  have hs : 1 ≤ s := scaleIndex_pos hd
  have hDs : lowerD s ≤ d := lowerD_scaleIndex_le hd
  have hdnext : d < lowerD (s + 1) := lt_lowerD_scaleIndex_succ d
  have hratio : lowerD (s + 1) ≤ 128 * lowerD s := lowerD_succ_le hs
  have hfscale : lowerK s < f₇₉₇ (lowerD s) :=
    lowerK_lt_extremalAcyclicNumber hs
  exact ⟨s, hs, hDs, hdnext.trans_le hratio,
    hfscale.trans_le (extremalAcyclicNumber_mono hDs)⟩

theorem lowerD_fourth_eq (s : ℕ) :
    lowerD s ^ 4 = 2 ^ 39 * s * lowerK s ^ 3 := by
  simp only [lowerD, lowerK, lowerA]
  ring

theorem lowerM_le_lowerD {s : ℕ} (hs : 1 ≤ s) :
    lowerM s ≤ lowerD s := by
  have hM : 1 ≤ lowerM s := Nat.one_le_pow s 2 (by norm_num)
  have hM6 : lowerM s ≤ lowerM s ^ 6 := by
    calc
      lowerM s = lowerM s * 1 := by ring
      _ ≤ lowerM s * lowerM s ^ 5 :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow 5 _ hM)
      _ = lowerM s ^ 6 := by ring
  calc
    lowerM s ≤ lowerM s ^ 6 := hM6
    _ = 1 * lowerM s ^ 6 := by ring
    _ ≤ (32768 * s) * lowerM s ^ 6 := by
      gcongr
      omega
    _ = lowerD s := by simp only [lowerD]

/-- Cube form of the AMR lower estimate, valid for every sufficiently large
maximum degree.  It is equivalent, up to the explicit constant, to
`d^(4/3) / (log d)^(1/3) ≪ f(d)`. -/
theorem fourth_le_log_mul_extremal_cube {d : ℕ} (hd : lowerD 1 ≤ d) :
    d ^ 4 ≤ 2 ^ 67 * Nat.log 2 d * f₇₉₇ d ^ 3 := by
  obtain ⟨s, hs, hDs, hd128, hK⟩ := exists_adjacent_lower_scale hd
  have hslog : s ≤ Nat.log 2 d := by
    apply Nat.le_log_of_pow_le (by norm_num)
    simpa only [lowerM] using (lowerM_le_lowerD hs).trans hDs
  have hdle : d ≤ 128 * lowerD s := hd128.le
  have hpow := Nat.pow_le_pow_left hdle 4
  have hKpow := Nat.pow_le_pow_left hK.le 3
  calc
    d ^ 4 ≤ (128 * lowerD s) ^ 4 := hpow
    _ = 2 ^ 28 * lowerD s ^ 4 := by ring
    _ = 2 ^ 67 * s * lowerK s ^ 3 := by rw [lowerD_fourth_eq]; ring
    _ ≤ 2 ^ 67 * Nat.log 2 d * f₇₉₇ d ^ 3 := by gcongr

end LowerBound

/-- The ratio `f(d) / d²` tends to zero. -/
theorem extremalAcyclicNumber_div_sq_tendsto_zero :
    Filter.Tendsto (fun d : ℕ ↦ (f₇₉₇ d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C : ℝ := (1024 : ℝ) ^ 3
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε ^ 3)
  refine ⟨max N 1, ?_⟩
  intro d hd
  have hdN : N ≤ d := (le_max_left N 1).trans hd
  have hd1 : 1 ≤ d := (le_max_right N 1).trans hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hε3 : 0 < ε ^ 3 := pow_pos hε _
  have hNd : (N : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdN
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd_sq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hquot : C / ε ^ 3 < (d : ℝ) ^ 2 := hN.trans_le (hNd.trans hd_sq)
  have hC : C < ε ^ 3 * (d : ℝ) ^ 2 := by
    have := (div_lt_iff₀ hε3).mp hquot
    simpa only [mul_comm] using this
  have huNat := UpperBound.extremalAcyclicNumber_cube_le hd1
  have hu : (f₇₉₇ d : ℝ) ^ 3 ≤ C * (d : ℝ) ^ 4 := by
    dsimp only [C]
    exact_mod_cast huNat
  have hcube : (f₇₉₇ d : ℝ) ^ 3 <
      (ε * (d : ℝ) ^ 2) ^ 3 := by
    calc
      (f₇₉₇ d : ℝ) ^ 3 ≤ C * (d : ℝ) ^ 4 := hu
      _ < (ε ^ 3 * (d : ℝ) ^ 2) * (d : ℝ) ^ 4 :=
        mul_lt_mul_of_pos_right hC (pow_pos hdR 4)
      _ = (ε * (d : ℝ) ^ 2) ^ 3 := by ring
  have htarget : 0 ≤ ε * (d : ℝ) ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  have hf : (f₇₉₇ d : ℝ) < ε * (d : ℝ) ^ 2 :=
    lt_of_pow_lt_pow_left₀ 3 htarget hcube
  have hratio : (f₇₉₇ d : ℝ) / (d : ℝ) ^ 2 < ε := by
    apply (div_lt_iff₀ (pow_pos hdR 2)).2
    simpa only [mul_comm] using hf
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hratio
  · positivity

/-- Standard Mathlib formulation of the affirmative answer to the question
`f(d) = o(d²)`. -/
theorem extremalAcyclicNumber_isLittleO_quadratic :
    (fun d : ℕ ↦ (f₇₉₇ d : ℝ)) =o[Filter.atTop]
      (fun d : ℕ ↦ (d : ℝ) ^ 2) := by
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2
  · exact extremalAcyclicNumber_div_sq_tendsto_zero
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h ↦ h⟩] with d hd
    intro hzero
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    exact (pow_ne_zero 2 hd0 hzero).elim

end


end Erdos797

namespace Erdos797

/-- Complete cube-form resolution of Erdős Problem 797.  The first conjunct is
\(f(d) \ll d^{4/3}\), the second is
\(d^{4/3}/(\log d)^{1/3} \ll f(d)\), and the third is the requested
consequence \(f(d)=o(d^2)\). -/
theorem erdos797_resolution :
    (∀ d : ℕ, 1 ≤ d → f₇₉₇ d ^ 3 ≤ 1024 ^ 3 * d ^ 4) ∧
    (∀ d : ℕ, LowerBound.lowerD 1 ≤ d →
      d ^ 4 ≤ 2 ^ 67 * Nat.log 2 d * f₇₉₇ d ^ 3) ∧
    ((fun d : ℕ ↦ (f₇₉₇ d : ℝ)) =o[Filter.atTop]
      (fun d : ℕ ↦ (d : ℝ) ^ 2)) := by
  refine ⟨?_, ?_, extremalAcyclicNumber_isLittleO_quadratic⟩
  · intro d hd
    exact UpperBound.extremalAcyclicNumber_cube_le hd
  · intro d hd
    exact LowerBound.fourth_le_log_mul_extremal_cube hd

#print axioms erdos797_resolution

end Erdos797
