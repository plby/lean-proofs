/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.Events
import ErdosProblems.Erdos565.FinalReduction
import ErdosProblems.Erdos565.Numeric
import ErdosProblems.Erdos565.Pullback
import ErdosProblems.Erdos565.RandomGraph
import Mathlib.Order.SymmDiff

/-!
# Finite restriction and state-counting infrastructure for Erdős problem 565

This file supplies the exact finite bridges used in the last probabilistic
reduction.  Pullback along an embedding has equinumerous graph fibres, so a
cardinality estimate for graphs on an induced vertex set transfers to ambient
graphs without introducing an unproved probability assumption.  We also package all
labelled target graphs of order at most `k` into one finite type.
-/

open scoped BigOperators symmDiff

namespace Erdos565
namespace FinalBridge

/-! ## Uniform finite fibres -/

section UniformFibers

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- The fibre of a function over a point. -/
abbrev Fiber (f : A → B) (b : B) := {a : A // f a = b}

/-- Every type is the disjoint union of the fibres of a function out of it. -/
noncomputable def totalEquivSigmaFiber (f : A → B) :
    A ≃ Σ b, Fiber f b where
  toFun a := ⟨f a, a, rfl⟩
  invFun a := a.2.1
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨b, a, ha⟩
    subst b
    rfl

/-- The preimage of a predicate is the disjoint union of the corresponding fibres. -/
noncomputable def preimageEquivSigmaFiber (f : A → B) (P : B → Prop) :
    {a : A // P (f a)} ≃ Σ b : {b : B // P b}, Fiber f b.1 where
  toFun a := ⟨⟨f a.1, a.2⟩, a.1, rfl⟩
  invFun a := ⟨a.2.1, a.2.2.symm ▸ a.1.2⟩
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨⟨b, hb⟩, a, ha⟩
    cases ha
    rfl

/-- The subtype cut out by a predicate is the coercion type of the
corresponding filter of the finite universe. -/
noncomputable def filterUnivEquivSubtype (P : A → Prop) [DecidablePred P] :
    ↥((Finset.univ : Finset A).filter P) ≃ {a : A // P a} where
  toFun a := ⟨a.1, (Finset.mem_filter.mp a.2).2⟩
  invFun a := ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

theorem card_filter_univ_eq_card_subtype (P : A → Prop) [DecidablePred P] :
    ((Finset.univ : Finset A).filter P).card = Fintype.card {a : A // P a} := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (filterUnivEquivSubtype P)

theorem card_eq_card_mul_fiber (f : A → B) (b₀ : B)
    (hfiber : ∀ b, Fintype.card (Fiber f b) = Fintype.card (Fiber f b₀)) :
    Fintype.card A = Fintype.card B * Fintype.card (Fiber f b₀) := by
  classical
  rw [Fintype.card_congr (totalEquivSigmaFiber f), Fintype.card_sigma]
  simp_rw [hfiber]
  simp

theorem card_preimage_eq_card_mul_fiber (f : A → B) (b₀ : B) (P : B → Prop)
    [DecidablePred P] [DecidablePred (P ∘ f)]
    (hfiber : ∀ b, Fintype.card (Fiber f b) = Fintype.card (Fiber f b₀)) :
    Fintype.card {a : A // P (f a)} =
      Fintype.card {b : B // P b} * Fintype.card (Fiber f b₀) := by
  classical
  rw [Fintype.card_congr (preimageEquivSigmaFiber f P), Fintype.card_sigma]
  simp_rw [hfiber]
  simp

/-- A denominator-cleared density estimate transfers through a map whose
fibres all have the same finite cardinality. -/
theorem uniformFiber_transfer (f : A → B) (b₀ : B) (P : B → Prop) (Q : ℕ)
    [DecidablePred P] [DecidablePred (P ∘ f)]
    (hfiber : ∀ b, Fintype.card (Fiber f b) = Fintype.card (Fiber f b₀))
    (h : Fintype.card {b : B // P b} * Q ≤ Fintype.card B) :
    Fintype.card {a : A // P (f a)} * Q ≤ Fintype.card A := by
  rw [card_preimage_eq_card_mul_fiber f b₀ P hfiber,
    card_eq_card_mul_fiber f b₀ hfiber]
  calc
    (Fintype.card {b : B // P b} * Fintype.card (Fiber f b₀)) * Q =
        (Fintype.card {b : B // P b} * Q) * Fintype.card (Fiber f b₀) := by
          ring
    _ ≤ Fintype.card B * Fintype.card (Fiber f b₀) :=
      Nat.mul_le_mul_right _ h

end UniformFibers

/-! ## Uniform fibres of graph restriction -/

section GraphFibers

open SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

/-- Pullback of symmetric difference is symmetric difference of pullbacks. -/
lemma comap_symmDiff (f : W → V) (G K : SimpleGraph V) :
    (G ∆ K).comap f = G.comap f ∆ K.comap f := by
  ext x y
  simp [symmDiff]

/-- Toggling the image of `H ∆ K` identifies the `H`- and `K`-fibres
of graph restriction. -/
noncomputable def graphFiberEquiv (f : W ↪ V) (H K : SimpleGraph W) :
    Fiber (SimpleGraph.comap f) H ≃ Fiber (SimpleGraph.comap f) K where
  toFun G := ⟨G.1 ∆ (H ∆ K).map f, by
    rw [comap_symmDiff, comap_map_eq, G.2]
    simp⟩
  invFun G := ⟨G.1 ∆ (H ∆ K).map f, by
    rw [comap_symmDiff, comap_map_eq, G.2]
    rw [symmDiff_comm H K, symmDiff_symmDiff_cancel_left]⟩
  left_inv G := by
    apply Subtype.ext
    simp
  right_inv G := by
    apply Subtype.ext
    simp

/-- Exact finite uniformity of an induced restriction: every graph-event
estimate on `W` transfers to graphs on `V` pulled back along `f`. -/
theorem card_comap_preimage_mul_le (f : W ↪ V) (P : SimpleGraph W → Prop)
    [DecidablePred P] [DecidablePred (P ∘ SimpleGraph.comap f)]
    (Q : ℕ) (h : Fintype.card {H : SimpleGraph W // P H} * Q ≤
      Fintype.card (SimpleGraph W)) :
    Fintype.card {G : SimpleGraph V // P (G.comap f)} * Q ≤
      Fintype.card (SimpleGraph V) := by
  classical
  apply uniformFiber_transfer (SimpleGraph.comap f) (⊥ : SimpleGraph W) P Q
  · intro H
    exact Fintype.card_congr (graphFiberEquiv f H ⊥)
  · exact h

end GraphFibers

/-! ## Janson invariance under injective relabelling -/

section JansonRelabelling

open Hypergraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype W] [DecidableEq W]

/-- Mapping a hypergraph along an injective relabelling preserves a Janson
witness.  The proof applies the existing pullback theorem to an inverse of
the injection; it therefore also covers embeddings into a larger ambient
vertex type, where the new vertices are isolated. -/
theorem Hypergraph.IsJanson.map_of_injective {H : Hypergraph V} (f : V → W)
    (hf : Function.Injective f) {p R : ℝ} (hp : 0 < p)
    (hH : H.IsJanson p R) : (H.map f).IsJanson p R := by
  classical
  let g : W → V := Function.invFun f
  have hgf : g ∘ f = id :=
    funext (Function.leftInverse_invFun hf)
  have hmap : (H.map f).map g = H := by
    rw [Hypergraph.map_comp, hgf, Hypergraph.map_id]
  have hinj : Hypergraph.EdgewiseInjective (H.map f) g := by
    rw [Hypergraph.edgewiseInjective_iff_card_image]
    intro E hE
    rcases Hypergraph.mem_map.mp hE with ⟨E₀, hE₀, rfl⟩
    rw [Finset.image_image, hgf, Finset.image_id,
      Finset.card_image_of_injective _ hf]
  apply Hypergraph.IsJanson.pullback hinj hp
  rwa [hmap]

/-- Injective relabelling is an exact invariance of the Janson property. -/
theorem Hypergraph.isJanson_map_iff_of_injective {H : Hypergraph V} (f : V → W)
    (hf : Function.Injective f) {p R : ℝ} (hp : 0 < p) :
    (H.map f).IsJanson p R ↔ H.IsJanson p R := by
  constructor
  · have hinj : Hypergraph.EdgewiseInjective H f :=
      fun _E _hE ↦ hf.injOn
    exact fun h ↦ Hypergraph.IsJanson.pullback hinj hp h
  · exact Hypergraph.IsJanson.map_of_injective f hf hp

end JansonRelabelling

/-! ## The finite type of bounded labelled targets -/

/-- A labelled graph with at most `k` vertices, carrying its order. -/
abbrev BoundedTarget (k : ℕ) := Σ s : Fin (k + 1), SimpleGraph (Fin s.1)

noncomputable instance (k : ℕ) : DecidableEq (BoundedTarget k) := Classical.decEq _

namespace BoundedTarget

def order {k : ℕ} (T : BoundedTarget k) : ℕ := T.1.1

def graph {k : ℕ} (T : BoundedTarget k) : SimpleGraph (Fin T.order) := T.2

lemma order_le {k : ℕ} (T : BoundedTarget k) : T.order ≤ k := by
  exact Nat.le_of_lt_succ T.1.2

def ofGraph {k : ℕ} (G : SimpleGraph (Fin k)) : BoundedTarget k :=
  ⟨⟨k, Nat.lt_succ_self k⟩, G⟩

@[simp] theorem order_ofGraph {k : ℕ} (G : SimpleGraph (Fin k)) :
    (ofGraph G).order = k := rfl

@[simp] theorem graph_ofGraph {k : ℕ} (G : SimpleGraph (Fin k)) :
    (ofGraph G).graph = G := rfl

/-- Crude exact count of all labelled graphs of order at most `k`. -/
theorem card_le (k : ℕ) :
    Fintype.card (BoundedTarget k) ≤ (k + 1) * 2 ^ k.choose 2 := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ s : Fin (k + 1), Fintype.card (SimpleGraph (Fin s.1)) ≤
        ∑ _s : Fin (k + 1), 2 ^ k.choose 2 := by
      apply Finset.sum_le_sum
      intro s _hs
      rw [RandomGraph.card_simpleGraph]
      simp only [Fintype.card_fin]
      exact Nat.pow_le_pow_right (by decide)
        (Nat.choose_le_choose 2 (Nat.le_of_lt_succ s.2))
    _ = (k + 1) * 2 ^ k.choose 2 := by simp

/-- The order-choice factor is absorbed into `2^k` for `k ≥ 2`. -/
theorem card_le_two_pow {k : ℕ} (hk : 2 ≤ k) :
    Fintype.card (BoundedTarget k) ≤ 2 ^ (k + k.choose 2) := by
  calc
    Fintype.card (BoundedTarget k) ≤ (k + 1) * 2 ^ k.choose 2 := card_le k
    _ ≤ 2 ^ k * 2 ^ k.choose 2 := by
      gcongr
      exact Nat.succ_le_iff.mpr Nat.lt_two_pow_self
    _ = 2 ^ (k + k.choose 2) := by rw [pow_add]

end BoundedTarget

/-! ## Counting descent states -/

abbrev DescentState (N r k : ℕ) :=
  FinalReduction.RamseyState (Fin N) (Fin r) (BoundedTarget k)

/-- The total number of vertex-set/target-vector states is exponentially
smaller than the final bad-event saving. -/
theorem card_descentState_le {N r k : ℕ} (hk : 2 ≤ k) :
    Fintype.card (DescentState N r k) ≤
      2 ^ (N + r * k + r * k.choose 2) := by
  classical
  rw [Fintype.card_congr FinalReduction.RamseyState.equivProd,
    Fintype.card_prod, Fintype.card_finset, Fintype.card_fin,
    Fintype.card_pi]
  calc
    2 ^ N * ∏ _i : Fin r, Fintype.card (BoundedTarget k) ≤
        2 ^ N * ∏ _i : Fin r, 2 ^ (k + k.choose 2) := by
      gcongr with i
      exact BoundedTarget.card_le_two_pow hk
    _ = 2 ^ (N + r * k + r * k.choose 2) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.card_eq_fintype_card, nsmul_eq_mul, ← pow_mul, ← pow_add]
      congr 1
      ring

/-- With the ACDFM host order, the complete state space is smaller than
the common denominator-saving factor in the terminal union bound. -/
theorem card_descentState_lt_finalSaving {r k : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) :
    Fintype.card (DescentState (Numeric.hostOrder r k) r k) <
      2 ^ Numeric.finalNumerator r k := by
  refine (card_descentState_le hk).trans_lt ?_
  apply Nat.pow_lt_pow_right (by decide)
  have h := Numeric.final_union_bound hr hk
  omega

/-! ## The concrete descent predicates -/

/-- The order vector carried by a descent state. -/
def stateOrder {N r k : ℕ} (s : DescentState N r k) (i : Fin r) : ℕ :=
  (s.targets i).order

/-- The target vector carried by a descent state. -/
def stateTargets {N r k : ℕ} (s : DescentState N r k) :
    Events.TargetVector r (stateOrder s) :=
  fun i ↦ (s.targets i).graph

/-- The natural-valued descent rank. -/
def stateRank {N r k : ℕ} (s : DescentState N r k) : ℕ :=
  FinalReduction.RamseyState.rank BoundedTarget.order s

@[simp] theorem stateRank_eq_totalOrder {N r k : ℕ}
    (s : DescentState N r k) :
    stateRank s = Events.totalOrder (stateOrder s) := rfl

theorem stateRank_le {N r k : ℕ} (s : DescentState N r k) :
    stateRank s ≤ r * k := by
  rw [stateRank_eq_totalOrder, Events.totalOrder]
  calc
    ∑ i, stateOrder s i ≤ ∑ _i : Fin r, k := by
      exact Finset.sum_le_sum fun i _ ↦ BoundedTarget.order_le (s.targets i)
    _ = r * k := by simp

/-- The denominator-cleared loss in one unit of target-order descent. -/
def descentFactor (r : ℕ) : ℕ := 8 * r * r ^ 50

/-- The fixed ACDFM density denominator, repeated here so this bridge can be
checked independently of the final key-lemma assembly module. -/
def finalDenominator (r k : ℕ) : ℕ := 2 ^ 25 * k ^ 2 * r ^ 4

/-- Exact admissibility of the current vertex set. -/
def StateAdmissible {N r k : ℕ} (s : DescentState N r k) : Prop :=
  N ≤ descentFactor r ^ (r * k - stateRank s) * s.vertices.card

/-- A state is bad when it is admissible and its induced host admits a
colouring with no Janson-distributed target-copy hypergraph. -/
def StateBad {N r k : ℕ} (H : SimpleGraph (Fin N))
    (s : DescentState N r k) : Prop :=
  StateAdmissible s ∧
    Events.BadForTargetsOn 1 (finalDenominator r k) (stateTargets s)
      (H.induce (↑s.vertices : Set (Fin N)))

/-- The key event attached to a state, in the current induced host. -/
def StateTerminal {N r k : ℕ} (H : SimpleGraph (Fin N))
    (s : DescentState N r k) : Prop :=
  Events.StrongInductionEventGlobalOn 1 (finalDenominator r k) 1
    (r ^ 50) (8 * r) (stateOrder s)
    (H.induce (↑s.vertices : Set (Fin N)))

/-- The initial state has every host vertex and one copy of the requested
target in each colour. -/
def initialState {N r k : ℕ} (G : SimpleGraph (Fin k)) :
    DescentState N r k where
  vertices := Finset.univ
  targets := fun _ ↦ BoundedTarget.ofGraph G

@[simp] theorem stateOrder_initialState {N r k : ℕ}
    (G : SimpleGraph (Fin k)) :
    stateOrder (initialState (N := N) (r := r) G) = fun _ ↦ k := by
  funext i
  rfl

@[simp] theorem stateRank_initialState {N r k : ℕ}
    (G : SimpleGraph (Fin k)) :
    stateRank (initialState (N := N) (r := r) G) = r * k := by
  rw [stateRank_eq_totalOrder, stateOrder_initialState, Events.totalOrder]
  simp

@[simp] theorem stateTargets_initialState {N r k : ℕ}
    (G : SimpleGraph (Fin k)) :
    stateTargets (initialState (N := N) (r := r) G) = fun _ ↦ G := rfl

@[simp] theorem vertices_initialState {N r k : ℕ}
    (G : SimpleGraph (Fin k)) :
    (initialState (N := N) (r := r) G).vertices = Finset.univ := rfl

/-- The local terminal bad set attached to a fixed descent state. -/
noncomputable def localTerminalBadSet {r k : ℕ}
    (s : DescentState (Numeric.hostOrder r k) r k) :
    Finset (SimpleGraph (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
  classical
  exact Finset.univ.filter fun K ↦
    Events.BadForTargetsOn 1 (finalDenominator r k) (stateTargets s) K ∧
      Events.StrongInductionEventGlobalOn 1 (finalDenominator r k) 1
        (r ^ 50) (8 * r) (stateOrder s) K

/-- A denominator-cleared key estimate on the induced vertex type transfers
exactly to the corresponding terminal bad event on ambient labelled graphs. -/
theorem terminalBadSet_card_mul_le_of_local {r k : ℕ}
    (s : DescentState (Numeric.hostOrder r k) r k) (Q : ℕ)
    (hlocal : (localTerminalBadSet s).card * Q ≤
        Fintype.card
          (SimpleGraph (↑s.vertices : Set (Fin (Numeric.hostOrder r k))))) :
    (FinalReduction.terminalBadSet
        (StateBad (r := r) (k := k))
        (StateTerminal (r := r) (k := k)) s).card * Q ≤
      Fintype.card (SimpleGraph (Fin (Numeric.hostOrder r k))) := by
  classical
  by_cases hs : StateAdmissible s
  · have hlocal' : Fintype.card
        {K : SimpleGraph (↑s.vertices : Set (Fin (Numeric.hostOrder r k))) //
          Events.BadForTargetsOn 1 (finalDenominator r k) (stateTargets s) K ∧
            Events.StrongInductionEventGlobalOn 1 (finalDenominator r k) 1
              (r ^ 50) (8 * r) (stateOrder s) K} * Q ≤
        Fintype.card
          (SimpleGraph (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
      rw [← card_filter_univ_eq_card_subtype]
      simpa [localTerminalBadSet] using hlocal
    let f : (↑s.vertices : Set (Fin (Numeric.hostOrder r k))) ↪
        Fin (Numeric.hostOrder r k) := Function.Embedding.subtype _
    have htransfer := card_comap_preimage_mul_le
      (V := Fin (Numeric.hostOrder r k))
      (W := (↑s.vertices : Set (Fin (Numeric.hostOrder r k))))
      (f := f)
      (P := fun K ↦
        Events.BadForTargetsOn 1 (finalDenominator r k) (stateTargets s) K ∧
          Events.StrongInductionEventGlobalOn 1 (finalDenominator r k) 1
            (r ^ 50) (8 * r) (stateOrder s) K)
      Q hlocal'
    rw [← card_filter_univ_eq_card_subtype] at htransfer
    have hf (H : SimpleGraph (Fin (Numeric.hostOrder r k))) :
        H.comap f = H.induce
          (↑s.vertices : Set (Fin (Numeric.hostOrder r k))) := by
      rfl
    simp_rw [hf] at htransfer
    simpa [FinalReduction.terminalBadSet, StateBad, StateTerminal, hs] using htransfer
  · simp [FinalReduction.terminalBadSet, StateBad, hs]

/-! ## Denominator-cleared terminal union bound -/

/-- A common denominator-cleared estimate for every terminal event suffices
for the finite union bound.  This form avoids introducing a rounded common
cardinality bound for the individual events. -/
theorem exists_not_initialBad_of_terminal_card_mul
    {Ω State : Type*} [Fintype Ω] [Nonempty Ω] [Fintype State]
    (rank : State → ℕ) (bad terminal : Ω → State → Prop)
    (initialBad : Ω → Prop) (initialState : Ω → State) (Q : ℕ)
    (start : ∀ ω, initialBad ω → bad ω (initialState ω))
    (descent : ∀ ω s, bad ω s → ¬ terminal ω s →
      ∃ t, bad ω t ∧ rank t < rank s)
    (key : ∀ s,
      (FinalReduction.terminalBadSet bad terminal s).card * Q ≤ Fintype.card Ω)
    (small : Fintype.card State < Q) :
    ∃ ω, ¬ initialBad ω := by
  classical
  have hcard :
      (FinalReduction.initialBadSet initialBad).card ≤
        ∑ s ∈ (Finset.univ : Finset State),
          (FinalReduction.terminalBadSet bad terminal s).card := by
    calc
      (FinalReduction.initialBadSet initialBad).card ≤
          (Finset.univ.biUnion
            (FinalReduction.terminalBadSet bad terminal)).card :=
        Finset.card_le_card
          (FinalReduction.initialBadSet_subset_terminalUnion rank bad terminal
            initialBad initialState start descent)
      _ ≤ ∑ s ∈ (Finset.univ : Finset State),
          (FinalReduction.terminalBadSet bad terminal s).card :=
        Finset.card_biUnion_le
  have hstrict :
      (FinalReduction.initialBadSet initialBad).card * Q < Fintype.card Ω * Q := by
    calc
      (FinalReduction.initialBadSet initialBad).card * Q ≤
          (∑ s ∈ (Finset.univ : Finset State),
            (FinalReduction.terminalBadSet bad terminal s).card) * Q :=
        Nat.mul_le_mul_right Q hcard
      _ = ∑ s ∈ (Finset.univ : Finset State),
          (FinalReduction.terminalBadSet bad terminal s).card * Q := by
        simp only [Finset.sum_mul]
      _ ≤ ∑ _s ∈ (Finset.univ : Finset State), Fintype.card Ω := by
        exact Finset.sum_le_sum fun s _ ↦ key s
      _ = Fintype.card State * Fintype.card Ω := by simp
      _ < Q * Fintype.card Ω :=
        Nat.mul_lt_mul_of_pos_right small Fintype.card_pos
      _ = Fintype.card Ω * Q := by ac_rfl
  by_contra hall
  push Not at hall
  have hinitial : FinalReduction.initialBadSet initialBad =
      (Finset.univ : Finset Ω) := by
    rw [FinalReduction.initialBadSet]
    exact Finset.filter_eq_self.mpr fun ω _ ↦ hall ω
  rw [hinitial, Finset.card_univ] at hstrict
  exact (Nat.lt_irrefl _ hstrict)

/-- Denominator-cleared terminal-event estimates yield an induced Ramsey
host of the prescribed order. -/
theorem inducedRamseyOrder_of_keyEstimate_mul
    {n N : ℕ} (G : SimpleGraph (Fin n))
    {State : Type*} [Fintype State]
    (rank : State → ℕ)
    (bad terminal : SimpleGraph (Fin N) → State → Prop)
    (initialState : SimpleGraph (Fin N) → State) (Q : ℕ)
    (start : ∀ H, ¬ IsInducedRamseyWitness G H → bad H (initialState H))
    (descent : ∀ H s, bad H s → ¬ terminal H s →
      ∃ t, bad H t ∧ rank t < rank s)
    (key : ∀ s,
      (FinalReduction.terminalBadSet bad terminal s).card * Q ≤
        Fintype.card (SimpleGraph (Fin N)))
    (small : Fintype.card State < Q) :
    IsInducedRamseyOrder G N := by
  classical
  obtain ⟨H, hH⟩ := exists_not_initialBad_of_terminal_card_mul
    rank bad terminal (fun H ↦ ¬ IsInducedRamseyWitness G H)
      initialState Q start descent key small
  exact ⟨H, not_not.mp hH⟩

theorem descentFactor_le_r_pow_100 {r : ℕ} (hr : 2 ≤ r) :
    descentFactor r ≤ r ^ 100 := by
  calc
    descentFactor r = 8 * r ^ 51 := by
      simp only [descentFactor]
      ring
    _ ≤ r ^ 3 * r ^ 51 := by
      gcongr
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ r ^ 3 := Numeric.two_pow_le_r_pow hr
    _ ≤ r ^ 100 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)

theorem admissible_hostOrder_le_mul {r k : ℕ} (hr : 2 ≤ r)
    (s : DescentState (Numeric.hostOrder r k) r k) (hs : StateAdmissible s) :
    Numeric.hostOrder r k ≤ r ^ (100 * r * k) * s.vertices.card := by
  calc
    Numeric.hostOrder r k ≤
        descentFactor r ^ (r * k - stateRank s) * s.vertices.card := hs
    _ ≤ (r ^ 100) ^ (r * k - stateRank s) * s.vertices.card := by
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (descentFactor_le_r_pow_100 hr) _)
    _ = r ^ (100 * (r * k - stateRank s)) * s.vertices.card := by
      rw [pow_mul]
    _ ≤ r ^ (100 * r * k) * s.vertices.card := by
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_right (by omega)
      calc
        100 * (r * k - stateRank s) ≤ 100 * (r * k) :=
          Nat.mul_le_mul_left 100 (Nat.sub_le _ _)
        _ = 100 * r * k := by ring

/-- Admissibility leaves enough vertices that the key-lemma saving still
dominates the final common saving used in the union bound. -/
theorem finalNumerator_le_keyExponent_of_admissible {r k : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (s : DescentState (Numeric.hostOrder r k) r k) (hs : StateAdmissible s) :
    Numeric.finalNumerator r k ≤
      s.vertices.card ^ 2 / r ^ 100 := by
  have hmul := admissible_hostOrder_le_mul hr s hs
  have hlarge : r ^ (1400 * r * k) ≤ s.vertices.card := by
    have hprod : r ^ (100 * r * k) * r ^ (1400 * r * k) ≤
        r ^ (100 * r * k) * s.vertices.card := by
      calc
        r ^ (100 * r * k) * r ^ (1400 * r * k) =
            Numeric.hostOrder r k := by
          simp only [Numeric.hostOrder, ← pow_add]
          congr 1
          ring
        _ ≤ r ^ (100 * r * k) * s.vertices.card := hmul
    exact Nat.le_of_mul_le_mul_left hprod (Nat.pow_pos (by omega : 0 < r))
  have hsquare : r ^ (2800 * r * k) ≤ s.vertices.card ^ 2 := by
    calc
      r ^ (2800 * r * k) = (r ^ (1400 * r * k)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ s.vertices.card ^ 2 := Nat.pow_le_pow_left hlarge 2
  have hden : 0 < r ^ 100 := Nat.pow_pos (by omega)
  rw [Nat.le_div_iff_mul_le hden]
  calc
    Numeric.finalNumerator r k * r ^ 100 =
        r ^ (2750 * r * k + 100) := by
      simp only [Numeric.finalNumerator, ← pow_add]
    _ ≤ r ^ (2800 * r * k) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    _ ≤ s.vertices.card ^ 2 := hsquare

/-! ## Flattening nested induced vertex sets -/

/-- A finite set of vertices of an induced graph, viewed back in the
original ambient vertex type. -/
def flattenFinset {V : Type*} [DecidableEq V] (S : Finset V)
    (W : Finset (↑S : Set V)) : Finset V :=
  W.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem card_flattenFinset {V : Type*} [DecidableEq V]
    (S : Finset V) (W : Finset (↑S : Set V)) :
    (flattenFinset S W).card = W.card := by
  simp [flattenFinset]

theorem flattenFinset_subset {V : Type*} [DecidableEq V]
    (S : Finset V) (W : Finset (↑S : Set V)) :
    flattenFinset S W ⊆ S := by
  intro v hv
  rw [flattenFinset, Finset.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact w.2

/-- The direct induced graph on the flattened set embeds inducedly into the
current induced graph, with image exactly the original nested finite set. -/
def flattenEmbedding {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (W : Finset (↑S : Set V)) :
    G.induce (↑(flattenFinset S W) : Set V) ↪g
      G.induce (↑S : Set V) where
  toFun x := ⟨x.1, flattenFinset_subset S W x.2⟩
  inj' := fun _ _ h ↦
    Subtype.ext (congrArg (fun z : (↑S : Set V) ↦ z.1) h)
  map_rel_iff' := Iff.rfl

@[simp] theorem range_flattenEmbedding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (W : Finset (↑S : Set V)) :
    Finset.univ.map (flattenEmbedding G S W).toEmbedding = W := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _hy, hyx⟩ := hx
    have hyval : y.1 = x.1 := congrArg Subtype.val hyx
    have hyflat : y.1 ∈ flattenFinset S W := y.2
    change y.1 ∈ W.map ⟨Subtype.val, Subtype.val_injective⟩ at hyflat
    rw [Finset.mem_map] at hyflat
    obtain ⟨z, hz, hzy⟩ := hyflat
    have hzx : z = x := Subtype.ext (hzy.trans hyval)
    simpa [hzx] using hz
  · intro hx
    let y : (↑(flattenFinset S W) : Set V) :=
      ⟨x.1, by
        change x.1 ∈ flattenFinset S W
        rw [flattenFinset, Finset.mem_map]
        exact ⟨x, hx, rfl⟩⟩
    rw [Finset.mem_map]
    refine ⟨y, Finset.mem_univ y, ?_⟩
    exact Subtype.ext rfl

/-- Pulling a coloring back along an induced embedding whose image is `W`
transports a restricted non-Janson obstruction to the source graph. -/
theorem badForColoringOn_pullback_embedding
    {U X V : Type*} [Fintype U] [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    (targets : Events.TargetVector r order)
    (K : SimpleGraph X) (G : SimpleGraph V)
    (coloring : G.EdgeLabeling (Fin r)) (e : K ↪g G) (W : Finset V)
    (range_e : Finset.univ.map e.toEmbedding = W)
    (hp : 0 < Events.rationalParameter pNum pDen)
    (hbad : ∀ i : Fin r,
      ¬ Hypergraph.IsJanson
        ((copyHypergraph (targets i) (Events.colorClassGraph coloring i) G).restrict W)
        (Events.rationalParameter pNum pDen)
        (Events.jansonRadius pNum pDen (Fintype.card X))) :
    Events.BadForColoringOn pNum pDen targets K (coloring.pullback e.toHom) := by
  classical
  intro i hi
  have hi' :
      Hypergraph.IsJanson
        (copyHypergraph (targets i) ((coloring.pullback e.toHom).labelGraph i) K)
        (Events.rationalParameter pNum pDen)
        (Events.jansonRadius pNum pDen (Fintype.card X)) := by
    simpa [Events.colorClassGraph] using hi
  have hiMap := Hypergraph.IsJanson.map_of_injective
    (fun x ↦ e x) e.injective hp hi'
  rw [map_copyHypergraph_pullback_embedding_eq_restrict
    (targets i) K G coloring i e W range_e] at hiMap
  exact hbad i (by simpa [Events.colorClassGraph] using hiMap)

/-- A coloring whose ambient copy hypergraphs are non-Janson after
restriction to a nested finite set remains bad on the directly flattened
induced graph. -/
theorem badForColoringOn_flatten
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    (targets : Events.TargetVector r order) (G : SimpleGraph V)
    (S : Finset V) (W : Finset (↑S : Set V))
    (coloring : (G.induce (↑S : Set V)).EdgeLabeling (Fin r))
    (hp : 0 < Events.rationalParameter pNum pDen)
    (hW : W.Nonempty)
    (hbad : ∀ i : Fin r,
      ¬ ((copyHypergraph (targets i) (Events.colorClassGraph coloring i)
        (G.induce (↑S : Set V))).restrict W).IsJanson
          (Events.rationalParameter pNum pDen)
          (Events.jansonRadius pNum pDen W.card)) :
    Events.BadForColoringOn pNum pDen targets
      (G.induce (↑(flattenFinset S W) : Set V))
      (coloring.pullback (flattenEmbedding G S W).toHom) := by
  classical
  have hflatPos : 0 < (flattenFinset S W).card := by
    rw [card_flattenFinset]
    exact Finset.card_pos.mpr hW
  letI : Nonempty (↑(flattenFinset S W) : Set V) := by
    rw [← Fintype.card_pos_iff]
    simpa using hflatPos
  intro i hi
  have hi' :
      (copyHypergraph (targets i)
        ((coloring.pullback (flattenEmbedding G S W).toHom).labelGraph i)
        (G.induce (↑(flattenFinset S W) : Set V))).IsJanson
          (Events.rationalParameter pNum pDen)
          (Events.jansonRadius pNum pDen W.card) := by
    simpa [Events.colorClassGraph, card_flattenFinset] using hi
  have hiMap := Hypergraph.IsJanson.map_of_injective
    (fun x ↦ (flattenEmbedding G S W) x)
    (flattenEmbedding G S W).injective hp hi'
  rw [map_copyHypergraph_pullback_embedding_eq_restrict
    (targets i) (G.induce (↑(flattenFinset S W) : Set V))
    (G.induce (↑S : Set V)) coloring i (flattenEmbedding G S W) W
    (range_flattenEmbedding G S W)] at hiMap
  exact hbad i (by simpa [Events.colorClassGraph] using hiMap)

/-! ## Strict descent to a terminal state -/

/-- Failure of the strong-induction event at a bad admissible state produces
another bad admissible state of strictly smaller total target order. -/
theorem state_descent {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k)
    (H : SimpleGraph (Fin (Numeric.hostOrder r k)))
    (s : DescentState (Numeric.hostOrder r k) r k)
    (hs : StateBad H s) (hterminal : ¬ StateTerminal H s) :
    ∃ t : DescentState (Numeric.hostOrder r k) r k,
      StateBad H t ∧ stateRank t < stateRank s := by
  classical
  rcases hs with ⟨hadmissible, hbad⟩
  unfold StateTerminal at hterminal
  obtain ⟨smaller, hcoord, htotal, targets, W, hW, coloring, hrestricted⟩ :=
    Events.exists_restricted_bad_of_not_strongInductionEventGlobalOn hterminal
  let nextTargets : Fin r → BoundedTarget k := fun i ↦
    ⟨⟨smaller i, Nat.lt_succ_of_le
      ((hcoord i).trans (BoundedTarget.order_le (s.targets i)))⟩, targets i⟩
  let t : DescentState (Numeric.hostOrder r k) r k :=
    { vertices := flattenFinset s.vertices W
      targets := nextTargets }
  have horderT : stateOrder t = smaller := by
    funext i
    rfl
  have htargetsT : stateTargets t = targets := rfl
  have hrankT : stateRank t = Events.totalOrder smaller := by
    rw [stateRank_eq_totalOrder, horderT]
  have hrankS : stateRank s = Events.totalOrder (stateOrder s) :=
    stateRank_eq_totalOrder s
  have hNpos : 0 < Numeric.hostOrder r k := Numeric.hostOrder_pos hr
  have hSpos : 0 < s.vertices.card := by
    by_contra hnot
    have hzero : s.vertices.card = 0 := Nat.eq_zero_of_not_pos hnot
    unfold StateAdmissible at hadmissible
    rw [hzero, Nat.mul_zero] at hadmissible
    omega
  have hsize : s.vertices.card ≤
      descentFactor r ^ (stateRank s - Events.totalOrder smaller) * W.card := by
    simpa [Events.MeetsDescendedSize, descentFactor, hrankS,
      mul_assoc, mul_left_comm, mul_comm] using hW
  have hWpos : W.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hnot
    have hzero : W.card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, Nat.mul_zero] at hsize
    omega
  have hexp :
      (r * k - stateRank s) +
          (stateRank s - Events.totalOrder smaller) =
        r * k - Events.totalOrder smaller := by
    have hrs := stateRank_le s
    omega
  have hadmissibleT : StateAdmissible t := by
    unfold StateAdmissible
    rw [hrankT]
    calc
      Numeric.hostOrder r k ≤
          descentFactor r ^ (r * k - stateRank s) * s.vertices.card := hadmissible
      _ ≤ descentFactor r ^ (r * k - stateRank s) *
          (descentFactor r ^ (stateRank s - Events.totalOrder smaller) * W.card) :=
        Nat.mul_le_mul_left _ hsize
      _ = (descentFactor r ^ (r * k - stateRank s) *
          descentFactor r ^ (stateRank s - Events.totalOrder smaller)) * W.card := by
        ring
      _ = descentFactor r ^
          ((r * k - stateRank s) +
            (stateRank s - Events.totalOrder smaller)) * W.card := by
        rw [pow_add]
      _ = descentFactor r ^ (r * k - Events.totalOrder smaller) *
          (flattenFinset s.vertices W).card := by
        rw [hexp, card_flattenFinset]
  have hpDen : 0 < finalDenominator r k := by
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)))
      (Nat.pow_pos (by omega))
  have hp : 0 < Events.rationalParameter 1 (finalDenominator r k) :=
    Events.rationalParameter_pos (by omega) hpDen
  have hbadColoring := badForColoringOn_flatten targets H s.vertices W coloring
    hp hWpos hrestricted
  have hbadT : Events.BadForTargetsOn 1 (finalDenominator r k)
      (stateTargets t)
      (H.induce (↑t.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
    refine ⟨coloring.pullback (flattenEmbedding H s.vertices W).toHom, ?_⟩
    change Events.BadForColoringOn 1 (finalDenominator r k) targets
      (H.induce (↑(flattenFinset s.vertices W) :
        Set (Fin (Numeric.hostOrder r k))))
      (coloring.pullback (flattenEmbedding H s.vertices W).toHom)
    exact hbadColoring
  refine ⟨t, ⟨hadmissibleT, hbadT⟩, ?_⟩
  rw [hrankT, hrankS]
  exact htotal

/-! ## The initial bad state -/

/-- Any host which fails the induced Ramsey property is bad at the constant
initial target state. -/
theorem state_start {k : ℕ} (hk : 2 ≤ k)
    (G : SimpleGraph (Fin k))
    (H : SimpleGraph (Fin (Numeric.hostOrder 2 k)))
    (hH : ¬ IsInducedRamseyWitness G H) :
    StateBad H (initialState (N := Numeric.hostOrder 2 k) (r := 2) G) := by
  classical
  have hNpos : 0 < Numeric.hostOrder 2 k := Numeric.hostOrder_pos (by decide)
  have hpDen : 0 < finalDenominator 2 k := by
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)))
      (Nat.pow_pos (by omega))
  have hbadH : Events.BadForTargetsOn 1 (finalDenominator 2 k)
      (fun _ : Fin 2 ↦ G) H := by
    by_contra hnotbad
    have hcopies : ∀ coloring : H.EdgeLabeling (Fin 2),
        ∃ i : Fin 2,
          (copyHypergraph G (Events.colorClassGraph coloring i) H).Nonempty := by
      intro coloring
      have hnotColor : ¬ Events.BadForColoringOn 1 (finalDenominator 2 k)
          (fun _ : Fin 2 ↦ G) H coloring := by
        intro hcolor
        exact hnotbad ⟨coloring, hcolor⟩
      obtain ⟨i, hi⟩ := Events.exists_janson_of_not_badForColoringOn hnotColor
      exact ⟨i, hi.nonempty (Events.rationalParameter_nonneg _ _)
        (Events.jansonRadius_pos (by omega) hpDen (by simpa using hNpos))⟩
    have hRamsey : IsInducedRamseyWitness G H := by
      intro coloring
      rw [monochromaticInducedCopy_iff_exists_copyHypergraph_nonempty]
      simpa [Events.colorClassGraph] using hcopies coloring
    exact hH hRamsey
  rcases hbadH with ⟨coloring, hcoloring⟩
  let e : H.induce
      (↑(Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) :
        Set (Fin (Numeric.hostOrder 2 k))) ↪g H :=
    SimpleGraph.Embedding.induce (G := H) _
  letI : Nonempty (Fin (Numeric.hostOrder 2 k)) := Fin.pos_iff_nonempty.mp hNpos
  letI : Nonempty
      (↑(Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) :
        Set (Fin (Numeric.hostOrder 2 k))) :=
    ⟨⟨Classical.choice inferInstance, by simp⟩⟩
  have hrange : Finset.univ.map e.toEmbedding =
      (Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) := by
    ext x
    simp [e]
  have hrestricted : ∀ i : Fin 2,
      ¬ ((copyHypergraph G (Events.colorClassGraph coloring i) H).restrict
        (Finset.univ : Finset (Fin (Numeric.hostOrder 2 k)))).IsJanson
          (Events.rationalParameter 1 (finalDenominator 2 k))
          (Events.jansonRadius 1 (finalDenominator 2 k)
            (Fintype.card
              (↑(Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) :
                Set (Fin (Numeric.hostOrder 2 k))))) := by
    intro i hi
    apply hcoloring i
    simpa using hi
  have hlocal := badForColoringOn_pullback_embedding
    (U := Fin k) (pNum := 1) (pDen := finalDenominator 2 k)
    (fun _ : Fin 2 ↦ G)
    (H.induce
      (↑(Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) :
        Set (Fin (Numeric.hostOrder 2 k)))) H coloring e
    (Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) hrange
    (Events.rationalParameter_pos (by omega) hpDen) hrestricted
  constructor
  · unfold StateAdmissible
    rw [stateRank_initialState]
    simp [initialState]
  · have hlocalBad : Events.BadForTargetsOn 1 (finalDenominator 2 k)
        (fun _ : Fin 2 ↦ G)
        (H.induce
          (↑(Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) :
            Set (Fin (Numeric.hostOrder 2 k)))) :=
      ⟨coloring.pullback e.toHom, hlocal⟩
    change Events.BadForTargetsOn 1 (finalDenominator 2 k)
      (fun _ : Fin 2 ↦ G)
      (H.induce
        (↑(Finset.univ : Finset (Fin (Numeric.hostOrder 2 k))) :
          Set (Fin (Numeric.hostOrder 2 k))))
    exact hlocalBad

end FinalBridge
end Erdos565
