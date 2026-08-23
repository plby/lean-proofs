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

end SimpleGraph

namespace Ramsey

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

def ramseyNumber (k l : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ramseyProperty_exists k l)

lemma ramseyNumber_spec (k l : ℕ) : RamseyProperty k l (ramseyNumber k l) :=
  by
    classical
    exact Nat.find_spec (ramseyProperty_exists k l)

end Ramsey

open scoped SimpleGraph

namespace Erdos720

open SimpleGraph

/-- Every two-coloring of the host contains a monochromatic target copy. -/
def Arrows {V W : Type*} (H : SimpleGraph V) (F : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph V, R ≤ H → F ⊑ R ∨ F ⊑ H \ R

/-- There is a finite arrowing host with exactly this many edges. -/
def IsSizeRamseyWitness {W : Type*} (F : SimpleGraph W) (m : ℕ) : Prop :=
  ∃ N : ℕ, ∃ H : SimpleGraph (Fin N), Nat.card H.edgeSet = m ∧ Arrows H F

lemma exists_sizeRamseyWitness {W : Type*} [Fintype W] (F : SimpleGraph W) :
    ∃ m, IsSizeRamseyWitness F m := by
  classical
  let k := Fintype.card W
  let N := Ramsey.ramseyNumber k k
  let H : SimpleGraph (Fin N) := ⊤
  have hFtop : F ⊑ (⊤ : SimpleGraph (Fin k)) := by
    let e : W ≃ Fin k := Fintype.equivFin W
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    intro a b hab
    simpa using hab.ne
  refine ⟨Nat.card H.edgeSet, N, H, rfl, ?_⟩
  intro R hRH
  have hRamsey : ¬ (R.CliqueFree k ∧ R.IndepSetFree k) :=
    Ramsey.ramseyNumber_spec k k R
  rcases not_and_or.mp hRamsey with hClique | hIndep
  · left
    have htop : (⊤ : SimpleGraph (Fin k)) ⊑ R := by
      rw [SimpleGraph.cliqueFree_iff] at hClique
      exact not_isEmpty_iff.mp hClique
    exact hFtop.trans htop
  · right
    have htop : (⊤ : SimpleGraph (Fin k)) ⊑ Rᶜ := by
      rw [← SimpleGraph.cliqueFree_compl, SimpleGraph.cliqueFree_iff] at hIndep
      exact not_isEmpty_iff.mp hIndep
    have hF : F ⊑ Rᶜ := hFtop.trans htop
    simpa [H] using hF

/-- The size-Ramsey number of a finite simple graph. -/
def sizeRamsey {W : Type*} [Fintype W] (F : SimpleGraph W) : ℕ :=
  by
    classical
    exact Nat.find (exists_sizeRamseyWitness F)

def cycleVertexConstant : ℕ := 8520192

def cycleRamseyEdgeConstant : ℕ :=
  4 * ((2 * cycleVertexConstant + 2) * cycleVertexConstant * cycleVertexConstant)

open Filter Topology

/-- The path and cycle size-Ramsey asymptotics, including effective bounds. -/
theorem erdos_problem_720 :
    (¬ Tendsto (fun n : ℕ ↦
      (sizeRamsey (pathGraph (n + 1)) : ℝ) / n) atTop atTop) ∧
    Tendsto (fun n : ℕ ↦
      (sizeRamsey (pathGraph (n + 1)) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0) ∧
    Tendsto (fun n : ℕ ↦ (sizeRamsey (cycleGraph n) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0) ∧
    (∀ᶠ n : ℕ in atTop, sizeRamsey (pathGraph (n + 1)) ≤ 6272 * n) ∧
    (∀ᶠ n : ℕ in atTop,
      sizeRamsey (cycleGraph n) ≤ cycleRamseyEdgeConstant * n) := by
  sorry

end Erdos720

end
