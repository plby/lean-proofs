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

lemma ramseyNumber_spec (k l : ℕ) : RamseyProperty k l (ramseyNumber k l) :=
  by
    classical
    exact Nat.find_spec (ramseyProperty_exists k l)

lemma ramseyProperty_one_left (l : ℕ) : RamseyProperty 1 l 1 := by
  intro G hbad
  simpa [SimpleGraph.cliqueFree_one] using hbad.1

lemma ramseyProperty_mono_vertices {k l n m : ℕ} (hnm : n ≤ m) :
    RamseyProperty k l n → RamseyProperty k l m := by
  intro h G hbad
  let f : Fin n ↪ Fin m := Fin.castLEEmb hnm
  have hcf : (G.comap f).CliqueFree k :=
    hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained
  have hif : (G.comap f).IndepSetFree l :=
    SimpleGraph.IndepSetFree.comap (SimpleGraph.Embedding.comap f G) hbad.2
  exact h (G.comap f) ⟨hcf, hif⟩

lemma ramseyNumber_le_of_property {k l n : ℕ} (hn : RamseyProperty k l n) :
    ramseyNumber k l ≤ n := by
  classical
  exact Nat.find_min' (ramseyProperty_exists k l) hn

lemma ramseyProperty_of_ramseyNumber_le {k l n : ℕ} (hn : ramseyNumber k l ≤ n) :
    RamseyProperty k l n :=
  ramseyProperty_mono_vertices hn (ramseyNumber_spec k l)

lemma ramseyProperty_zero_right (k : ℕ) : RamseyProperty k 0 0 := by
  intro G hbad
  have hnil : G.IsNIndepSet 0 (∅ : Finset (Fin 0)) := by
    simp [SimpleGraph.isNIndepSet_iff]
  exact hbad.2 _ hnil

lemma ramseyNumber_zero_right (k : ℕ) : ramseyNumber k 0 = 0 := by
  exact le_antisymm (ramseyNumber_le_of_property (ramseyProperty_zero_right k)) (Nat.zero_le _)

lemma ramseyNumber_pos {u m : ℕ} (hu : 1 ≤ u) (hm : 1 ≤ m) : 0 < ramseyNumber u m := by
  by_contra hpos
  have hz : ramseyNumber u m = 0 := Nat.eq_zero_of_not_pos hpos
  have hprop : RamseyProperty u m 0 := by
    simpa [hz] using ramseyNumber_spec u m
  let G : SimpleGraph (Fin 0) := ⊥
  have hcf : G.CliqueFree u := by
    have hcard : Fintype.card (Fin 0) < u := by
      simpa [Fintype.card_fin] using (Nat.succ_le_iff.mp hu)
    exact SimpleGraph.cliqueFree_of_card_lt (G := G) hcard
  have hif : G.IndepSetFree m := by
    rw [← SimpleGraph.cliqueFree_compl]
    have hcard : Fintype.card (Fin 0) < m := by
      simpa [Fintype.card_fin] using (Nat.succ_le_iff.mp hm)
    exact SimpleGraph.cliqueFree_of_card_lt (G := Gᶜ) hcard
  exact hprop G ⟨hcf, hif⟩

lemma ramseyProperty_one_right (k : ℕ) : RamseyProperty k 1 1 := by
  intro G hbad
  have hs : G.IsNIndepSet 1 (Finset.univ : Finset (Fin 1)) := by
    refine ⟨?_, by simp⟩
    simp [SimpleGraph.isIndepSet_iff]
  exact hbad.2 _ hs

lemma ramseyProperty_succ_succ_of_sum {k l m n : ℕ}
    (hm : RamseyProperty k (l + 1) m)
    (hn : RamseyProperty (k + 1) l n)
    (hpos : 0 < m + n) :
    RamseyProperty (k + 1) (l + 1) (m + n) := by
  intro G hbad
  classical
  let v : Fin (m + n) := ⟨0, hpos⟩
  by_cases hdeg : m ≤ G.degree v
  · let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
    have hprop : RamseyProperty k (l + 1) (G.degree v) := ramseyProperty_mono hdeg hm
    have hcf : H.CliqueFree k := by
      intro t ht
      let t' : Finset (Fin (m + n)) := Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
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
    have hprop : RamseyProperty (k + 1) l (Gᶜ.degree v) := ramseyProperty_mono hcompdeg hn
    have hcf : H.CliqueFree (k + 1) := by
      exact hbad.1.comap
        (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
    have hif : H.IndepSetFree l := by
      intro t ht
      let t' : Finset (Fin (m + n)) := Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
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

lemma ramseyNumber_recurrence (u m : ℕ) (hu : 1 ≤ u) :
    ramseyNumber (u + 1) (m + 1) ≤ ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
  apply ramseyNumber_le_of_property
  have hpos : 0 < ramseyNumber u (m + 1) + ramseyNumber (u + 1) m := by
    exact Nat.add_pos_left (ramseyNumber_pos hu (by omega)) _
  exact ramseyProperty_succ_succ_of_sum
    (ramseyNumber_spec u (m + 1))
    (ramseyNumber_spec (u + 1) m)
    hpos

lemma ramseyNumber_le_choose (u : ℕ) :
    ∀ m, ramseyNumber (u + 1) m ≤ Nat.choose (u + m - 1) u := by
  induction u with
  | zero =>
      intro m
      cases m with
      | zero =>
          simp [ramseyNumber_zero_right]
      | succ m =>
          have hle : ramseyNumber 1 (m + 1) ≤ 1 := by
            exact ramseyNumber_le_of_property (ramseyProperty_one_left (m + 1))
          simpa using hle
  | succ u ihu =>
      intro m
      induction m with
      | zero =>
          rw [ramseyNumber_zero_right]
          simp
      | succ m ihm =>
          have hrec : ramseyNumber (u + 2) (m + 1) ≤
              ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := by
            exact ramseyNumber_recurrence (u + 1) m (by omega)
          have hleft : ramseyNumber (u + 1) (m + 1) ≤ Nat.choose (u + m) u := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihu (m + 1)
          have hright : ramseyNumber (u + 2) m ≤ Nat.choose (u + m) (u + 1) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihm
          calc
            ramseyNumber (u + 2) (m + 1)
                ≤ ramseyNumber (u + 1) (m + 1) + ramseyNumber (u + 2) m := hrec
            _ ≤ Nat.choose (u + m) u + Nat.choose (u + m) (u + 1) := by
              exact Nat.add_le_add hleft hright
            _ = Nat.choose (u + m + 1) (u + 1) := by
              rw [Nat.choose_succ_succ' (u + m) u]
            _ = Nat.choose (u + 1 + (m + 1) - 1) (u + 1) := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Ramsey
