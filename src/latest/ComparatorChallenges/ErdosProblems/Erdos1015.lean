/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Finite Ramsey theory utilities

This file contains the finite two-color Ramsey definitions and elementary bounds shared by
multiple developments.
-/

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

open scoped SimpleGraph

namespace Erdos1015

open Ramsey SimpleGraph

/-- A red or blue clique of order t, with red encoded by G and blue by
independence in G. -/
def MonoClique {V : Type*} (G : SimpleGraph V) (t : ℕ) (K : Finset V) : Prop :=
  G.IsNClique t K ∨ G.IsNIndepSet t K

/-- TilesTo G t S R means that S minus R is partitioned into pairwise
vertex-disjoint monochromatic K_t's and R is the remainder. -/
inductive TilesTo {V : Type*} [DecidableEq V] (G : SimpleGraph V) (t : ℕ) :
    Finset V → Finset V → Prop
  | refl (R : Finset V) : TilesTo G t R R
  | add {K S R : Finset V} (hK : MonoClique G t K)
      (hdisj : Disjoint K S) (hrest : TilesTo G t S R) :
      TilesTo G t (K ∪ S) R

/-- Every red/blue graph on a finite n-vertex type has a packing leaving at
most b vertices.  Quantifying over all finite types makes the lower-bound
sum construction transparent; it is equivalent to using Fin n. -/
def RemainderBound (t n b : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = n →
    ∀ G : SimpleGraph V, ∃ R : Finset V,
      TilesTo G t univ R ∧ R.card ≤ b

theorem remainderBound_exists (t n : ℕ) : ∃ b, RemainderBound t n b := by
  refine ⟨n, ?_⟩
  intro V _ _ hcard G
  refine ⟨univ, .refl _, ?_⟩
  simp [hcard]

/-- The exact worst-case minimum uncovered count. -/
def packingRemainder (t n : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (remainderBound_exists t n)

/-- The inclusive Burr--Erdős--Spencer remainder. -/
def besRemainder (t n : ℕ) : ℕ :=
  let R := ramseyNumber t (t - 1)
  R - 1 + (n - (R - 1)) % t

/-- The reservoir size in the Burr--Erdős--Spencer proof. -/
def besReservoir (t : ℕ) : ℕ :=
  (t - 1) * (ramseyNumber t t - ramseyNumber t (t - 1)) +
    (t - 1) * (t - 2) + 1

/-- An explicit sufficient host threshold for the exact formula. -/
def besThreshold (t : ℕ) : ℕ :=
  ramseyNumber (besReservoir t) (besReservoir t)

theorem erdos1015_exact {t n : ℕ} (ht : 3 ≤ t)
    (hn : besThreshold t ≤ n) :
    packingRemainder t n = besRemainder t n := by
  sorry

end Erdos1015

end
