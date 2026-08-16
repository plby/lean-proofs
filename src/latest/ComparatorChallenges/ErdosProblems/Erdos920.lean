/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Finset

noncomputable section

namespace SimpleGraph

theorem IndepSetFree.comap {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (f : H ↪g G) : G.IndepSetFree n → H.IndepSetFree n := by
  intro h
  rw [← cliqueFree_compl] at h ⊢
  exact CliqueFree.comap
    (((Embedding.complEquiv (G := H) (H := G)).toFun f).isContained) h

def Iso.compl {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro v w
    by_cases hvw : v = w
    · subst hvw
      simp
    · simpa [compl_adj, hvw, e.injective.ne_iff] using
        not_congr (e.map_adj_iff (v := v) (w := w))

theorem Iso.cliqueFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.CliqueFree n ↔ H.CliqueFree n := by
  constructor
  · intro h
    exact CliqueFree.comap e.symm.toEmbedding.isContained h
  · intro h
    exact CliqueFree.comap e.toEmbedding.isContained h

theorem Iso.indepSetFree_iff {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : G ≃g H) : G.IndepSetFree n ↔ H.IndepSetFree n := by
  simpa [indepSetFree_compl] using
    (Iso.cliqueFree_iff (n := n) (e := Iso.compl e))

end SimpleGraph

namespace Ramsey

/--
The Ramsey property on `n` vertices: every finite simple graph on `n` vertices contains
either a `k`-clique or an independent set of size `l`.
-/
def RamseyProperty (k l n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

lemma ramseyProperty_of_card {k l n : ℕ} {α : Type*} [Fintype α]
    (hcard : Fintype.card α = n) (hprop : RamseyProperty k l n) :
    ∀ G : SimpleGraph α, ¬ (G.CliqueFree k ∧ G.IndepSetFree l) := by
  intro G hbad
  let H : SimpleGraph (Fin n) := G.overFin hcard
  let e : G ≃g H := SimpleGraph.overFinIso (G := G) hcard
  have hcf : H.CliqueFree k := hbad.1.comap e.symm.toEmbedding.isContained
  have hcfCompl : Hᶜ.CliqueFree l := by
    have hGCompl : Gᶜ.CliqueFree l := by
      simpa [SimpleGraph.cliqueFree_compl] using hbad.2
    exact hGCompl.comap
      (((SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun e.symm.toEmbedding).isContained)
  have hif : H.IndepSetFree l := by
    simpa [SimpleGraph.cliqueFree_compl] using hcfCompl
  exact hprop H ⟨hcf, hif⟩

lemma ramseyProperty_mono {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

/-- Finite Ramsey's theorem, packaged as the existence of a size satisfying `RamseyProperty`. -/
theorem ramseyProperty_exists (k l : ℕ) : ∃ n, RamseyProperty k l n := by
  revert l
  induction k with
  | zero =>
      intro l
      refine ⟨0, ?_⟩
      intro G hbad
      simpa using hbad.1
  | succ k ih =>
      intro l
      induction l with
      | zero =>
          refine ⟨0, ?_⟩
          intro G hbad
          exact hbad.2 ∅ (by simp [SimpleGraph.isNIndepSet_iff])
      | succ l ihl =>
          rcases ih (l + 1) with ⟨m, hm⟩
          rcases ihl with ⟨n, hn⟩
          refine ⟨m + n + 1, ?_⟩
          intro G hbad
          classical
          let v : Fin (m + n + 1) := 0
          by_cases hdeg : m ≤ G.degree v
          · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
            have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
            have hcf : H.CliqueFree k := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce (G.neighborSet v)).coe).IsNClique k t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNClique k t' := by
                simpa [H, t'] using
                  (SimpleGraph.IsNClique.of_induce
                    (S := (⊤ : SimpleGraph.Subgraph G)) (F := G.neighborSet v) (cc := htInd))
              have hvt : ∀ b ∈ t', G.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              exact hbad.1 _ (ht'.insert hvt)
            have hif : H.IndepSetFree (l + 1) := by
              exact SimpleGraph.IndepSetFree.comap
                (SimpleGraph.Embedding.induce (G := G) (s := G.neighborSet v)) hbad.2
            exact ramseyProperty_of_card (G.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩
          · let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
            have hcompdeg : n ≤ Gᶜ.degree v := by
              rw [G.degree_compl (v := v), Fintype.card_fin]
              omega
            have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) :=
              ramseyProperty_mono hcompdeg hn
            have hcf : H.CliqueFree (k + 1) := by
              exact hbad.1.comap
                (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
            have hif : H.IndepSetFree l := by
              intro t ht
              let t' : Finset (Fin (m + n + 1)) :=
                Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
              have htInd :
                  (((⊤ : SimpleGraph.Subgraph G).induce
                    (Gᶜ.neighborSet v)).coe).IsNIndepSet l t := by
                rw [← SimpleGraph.induce_eq_coe_induce_top]
                exact ht
              have ht' : G.IsNIndepSet l t' := by
                simpa [H, t'] using
                  (SimpleGraph.isNIndepSet_induce
                    (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := l)).1 htInd
              have ht'compl : Gᶜ.IsNClique l t' := by
                simpa using ht'
              have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
                intro b hb
                rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
                exact x.property
              have ht'' : G.IsNIndepSet (l + 1) (insert v t') := by
                simpa using ht'compl.insert hvt
              exact hbad.2 _ ht''
            exact ramseyProperty_of_card (Gᶜ.card_neighborSet_eq_degree v) hprop H ⟨hcf, hif⟩

/-- The off-diagonal Ramsey number `R(k, l)`. -/
def ramseyNumber (k l : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ramseyProperty_exists k l)

end Ramsey

/-!
# Erdős Problem 920

The graph-theoretic Ramsey bridge is in `Bridge`, the finite-geometric Ramsey
construction is packaged in `RamseyPackaging`, and the asymptotic inversion is
in `Inversion`.
-/

open Real Filter

syntax (name := answerSyntax920) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

namespace Erdos920.RamseyPackaging

structure Digraph (V : Type*) where
  arc : V → V → Prop

/-- A labelled copy of the transitive tournament `T_r`. -/
def Digraph.HasTransitiveTournament {V : Type*} (D : Digraph V) (r : ℕ) : Prop :=
  ∃ v : Fin r → V, Function.Injective v ∧
    ∀ i j : Fin r, i < j → D.arc (v i) (v j)

/-- An ordered tuple with no arc pointing from an earlier entry to a later
entry.  Repetitions are intentionally allowed. -/
def Digraph.IsForwardIndependent {V : Type*} (D : Digraph V) {m : ℕ}
    (v : Fin m → V) : Prop :=
  ∀ i j : Fin m, i < j → ¬ D.arc (v i) (v j)

/-- The number of forward-independent ordered tuples. -/
def Digraph.forwardIndependentTupleCount {V : Type*} [Fintype V]
    (D : Digraph V) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin m → V)).filter
    (fun v => D.IsForwardIndependent v)).card

/-- The exact numerical information supplied by a `D*(t,q)` construction.
The exponent `t` is the projective parameter, so the forbidden transitive
tournament has `t+1` vertices. -/
structure DStarWitness (t m q : ℕ) (C : ℝ) where
  V : Type
  fintypeV : Fintype V
  D : Digraph V
  transitiveTournamentFree : ¬ D.HasTransitiveTournament (t + 1)
  vertex_lower : (q : ℝ) ^ (2 * t - 1) / 4 ≤ (@Fintype.card V fintypeV : ℝ)
  forward_bound :
    ((@Digraph.forwardIndependentTupleCount V fintypeV D m : ℕ) : ℝ) ≤
      (C * (q : ℝ) ^ t) ^ m

namespace DStarWitness

variable {t m q : ℕ} {C : ℝ}

/-- The retention probability used after the random-ordering argument. -/
def samplingDensity (_W : DStarWitness t m q C) : ℝ :=
  (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ t)

/-- The conclusion of the two standard finite averaging steps.

The first step chooses a random ordering and turns a `T_(t+1)`-free digraph
into a `K_(t+1)`-free graph.  The factorial saving changes the tuple bound
`(C q^t)^m` into `(e C q^t / m)^m`.  Keeping vertices with probability
`m/(e C q^t)` and deleting one vertex from every surviving independent
`m`-set then gives precisely the strict Ramsey inequality below.

Keeping this conclusion as a named property permits the finite probability
or double-counting proof to live in a separate module without concealing any
numeric assumption used by the final argument. -/
def HasAveragingSamplingConclusion (W : DStarWitness t m q C) : Prop :=
  W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) - 1 <
    (Ramsey.ramseyNumber (t + 1) m : ℝ)

/-- The two standard side conditions for the sampling parameter. -/
def SamplingSideConditions (W : DStarWitness t m q C) : Prop :=
  0 < W.samplingDensity ∧ W.samplingDensity ≤ 1

end DStarWitness

def HasDStarAtScale (u m : ℕ) (C κ : ℝ) : Prop :=
  ∃ q : ℕ, q.Prime ∧
    κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
    ∃ W : DStarWitness (u + 1) m q C,
      W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion

structure DStarFamily (u : ℕ) where
  C : ℝ
  κ : ℝ
  C_pos : 0 < C
  κ_pos : 0 < κ
  exists_eventually : ∀ᶠ m : ℕ in atTop, HasDStarAtScale u m C κ

end Erdos920.RamseyPackaging

namespace Erdos920

def chromaticValues (k n : ℕ) : Set ℕ :=
  {q | ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ q = G.chromaticNumber.toNat}

noncomputable def f (k n : ℕ) : ℕ :=
  sSup (chromaticValues k n)

/--
The final implication, isolated from the construction of Bradač's Ramsey
lower bound.  This is the narrow assembly interface used by the main theorem.
-/

theorem erdos_920_of_dStarFamilies
    (families : ∀ u : ℕ, 1 ≤ u → RamseyPackaging.DStarFamily u) :
    answer(True) ↔ ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  sorry

theorem erdos_920 :
    answer(True) ↔ ∀ k : ℕ, k ≥ 4 → ∃ c > 0,
      (fun n : ℕ ↦ (f k n : ℝ)) ≫
        (fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (log n) ^ c) := by
  sorry
