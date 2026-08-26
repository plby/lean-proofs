import ErdosProblems.Erdos556.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Qualitative finite Ramsey existence

The elementary two-colour induction is adapted from the existing proved
development in `Util/Ramsey.lean). Its dependencies are kept here so that
the #556 development is self-contained apart from Mathlib.
-/

namespace Erdos556.TwoColour

open Finset
open scoped SimpleGraph

theorem indepSetFree_comap {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {n : ℕ} (f : H ↪g G) :
    G.IndepSetFree n → H.IndepSetFree n := by
  intro h
  rw [← SimpleGraph.cliqueFree_compl] at h ⊢
  exact h.comap
    (((SimpleGraph.Embedding.complEquiv (G := H) (H := G)).toFun f).isContained)

def RamseyProperty (k l m : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin m), ¬ (G.CliqueFree k ∧ G.IndepSetFree l)

theorem ramseyProperty_of_card {k l m : ℕ} {V : Type*} [Fintype V]
    (hcard : Fintype.card V = m) (h : RamseyProperty k l m)
    (G : SimpleGraph V) : ¬ (G.CliqueFree k ∧ G.IndepSetFree l) := by
  classical
  intro hbad
  let e : Fin m ≃ V := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let f : Fin m ↪ V := e.toEmbedding
  exact h (G.comap f) ⟨hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained,
    indepSetFree_comap (SimpleGraph.Embedding.comap f G) hbad.2⟩

theorem ramseyProperty_mono {k l a b : ℕ} (hab : a ≤ b)
    (h : RamseyProperty k l a) : RamseyProperty k l b := by
  intro G hbad
  let f : Fin a ↪ Fin b := Fin.castLEEmb hab
  exact h (G.comap f) ⟨hbad.1.comap (SimpleGraph.Embedding.comap f G).isContained,
    indepSetFree_comap (SimpleGraph.Embedding.comap f G) hbad.2⟩


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
              exact indepSetFree_comap
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


end Erdos556.TwoColour

namespace Erdos556

open SimpleGraph
open scoped SimpleGraph

theorem cycle_of_not_cliqueFree {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (h : ¬ G.CliqueFree n) : cycleGraph n ⊑ G := by
  have htop : cycleGraph n ⊑ completeGraph (Fin n) := IsContained.of_le le_top
  exact htop.trans ((G.not_cliqueFree_iff_top_isContained n).mp h)

theorem ThreeColouring.cycle_of_comap {V W : Type*} (c : ThreeColouring V)
    (f : W ↪ V) {n : ℕ} {i : Fin 3}
    (h : cycleGraph n ⊑ (c.comap f).graph i) : cycleGraph n ⊑ c.graph i := by
  rw [c.graph_comap f i] at h
  exact h.trans (SimpleGraph.Embedding.comap f (c.graph i)).isContained

/-- Qualitative existence of the three-colour cycle Ramsey number. -/
theorem isRamseyOrder_exists (n : ℕ) : ∃ m, IsRamseyOrder n m := by
  classical
  obtain ⟨m, hm⟩ := TwoColour.ramseyProperty_exists n n
  obtain ⟨N, hN⟩ := TwoColour.ramseyProperty_exists n m
  refine ⟨N, ?_⟩
  intro c
  by_cases hred : (c.graph 0).CliqueFree n
  · have hnind : ¬ (c.graph 0).IndepSetFree m := fun hi => hN _ ⟨hred, hi⟩
    have hncompl : ¬ (c.graph 0)ᶜ.CliqueFree m := by
      simpa only [cliqueFree_compl] using hnind
    let e := (c.graph 0)ᶜ.topEmbeddingOfNotCliqueFree hncompl
    let f : Fin m ↪ Fin N := ⟨e, e.injective⟩
    let d := c.comap f
    have hzero {u v : Fin m} (huv : u ≠ v) : d.colour u v ≠ 0 := by
      intro hc
      have he := e.map_rel_iff.mpr huv
      exact he.2 ⟨f.injective.ne huv, hc⟩
    have hcomp : (d.graph 1)ᶜ ≤ d.graph 2 := by
      intro u v h
      have huv : u ≠ v := h.1
      have h0 := hzero huv
      have h1 : d.colour u v ≠ 1 := fun h1 => h.2 ⟨huv, h1⟩
      refine ⟨huv, ?_⟩
      have hc := (d.colour u v).isLt
      apply Fin.ext
      have h0v : (d.colour u v).val ≠ 0 := by
        intro hval
        exact h0 (Fin.ext hval)
      have h1v : (d.colour u v).val ≠ 1 := by
        intro hval
        exact h1 (Fin.ext hval)
      omega
    by_cases hblue : (d.graph 1).CliqueFree n
    · have hni : ¬ (d.graph 1).IndepSetFree n := fun hi => hm _ ⟨hblue, hi⟩
      have hnc : ¬ (d.graph 1)ᶜ.CliqueFree n := by
        simpa only [cliqueFree_compl] using hni
      have hcycle : cycleGraph n ⊑ d.graph 2 :=
        (cycle_of_not_cliqueFree hnc).mono_right hcomp
      exact ⟨2, c.cycle_of_comap f hcycle⟩
    · exact ⟨1, c.cycle_of_comap f (cycle_of_not_cliqueFree hblue)⟩
  · exact ⟨0, cycle_of_not_cliqueFree hred⟩

#print axioms isRamseyOrder_exists

end Erdos556
