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

open scoped Classical in
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

Ramsey-number and directed-construction definitions for the two theorem
statements below.
-/

open Real Filter

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

open scoped SimpleGraph

namespace Erdos559


open scoped Classical in
/-- A uniform finite enumeration of graph copies, used so that all subtype
cardinalities below share the same canonical `Fintype` instances. -/
noncomputable local instance (priority := 2000) copyFintype
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Fintype (G.Copy H) :=
  Fintype.ofInjective (fun f : G.Copy H ↦ (f : V → W)) fun f g h ↦ by
    apply SimpleGraph.Copy.ext
    intro v
    exact congr_fun h v

/-! ## Size Ramsey definitions -/

/-- `H` is Ramsey for `G` if every red spanning subgraph `R ≤ H` contains a copy of `G`,
or the complementary set of host edges contains a copy of `G`.  Containment `⊑` is ordinary
(not necessarily induced) graph containment. -/
def IsRamseyFor {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∀ R : SimpleGraph V, R ≤ H → G ⊑ R ∨ G ⊑ (H \ R)

open scoped Classical in
/-- The number of unordered edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} [Finite V] (H : SimpleGraph V) : ℕ :=
  Nat.card H.edgeSet

open scoped Classical in
lemma edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : edgeCount H = H.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

open scoped Classical in
/-- There is a finite Ramsey host for every finite graph. -/
lemma ramseyHost_exists {W : Type*} [Fintype W] (G : SimpleGraph W) :
    ∃ (N : ℕ) (H : SimpleGraph (Fin N)), IsRamseyFor H G := by
  let n := Fintype.card W
  obtain ⟨N, hN⟩ := Ramsey.ramseyProperty_exists n n
  refine ⟨N, ⊤, ?_⟩
  intro R _
  have hor : ¬ R.CliqueFree n ∨ ¬ R.IndepSetFree n := not_and_or.mp (hN R)
  let G' : SimpleGraph (Fin n) := G.overFin rfl
  let e : G ≃g G' := SimpleGraph.overFinIso (G := G) rfl
  have hGtop : G ⊑ (⊤ : SimpleGraph (Fin n)) :=
    e.isContained.trans (SimpleGraph.IsContained.of_le le_top)
  rcases hor with hred | hblue
  · left
    have htop : (⊤ : SimpleGraph (Fin n)) ⊑ R := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hred
    exact hGtop.trans htop
  · right
    have hblue' : ¬ Rᶜ.CliqueFree n := by
      simpa only [SimpleGraph.cliqueFree_compl] using hblue
    have htop : (⊤ : SimpleGraph (Fin n)) ⊑ Rᶜ := by
      simpa only [SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hblue'
    have hdiff : (⊤ \ R : SimpleGraph (Fin N)) = Rᶜ := by
      ext u v
      simp [SimpleGraph.compl_adj]
    rw [hdiff]
    exact hGtop.trans htop

open scoped Classical in
/-- A natural number is realized as the edge count of a finite Ramsey host for `G`. -/
def HasRamseyHostWithEdges {W : Type*} [Fintype W] (G : SimpleGraph W) (m : ℕ) : Prop :=
  ∃ (N : ℕ) (H : SimpleGraph (Fin N)), IsRamseyFor H G ∧ edgeCount H = m

open scoped Classical in
lemma ramseyHostEdgeCount_exists {W : Type*} [Fintype W] (G : SimpleGraph W) :
    ∃ m, HasRamseyHostWithEdges G m := by
  obtain ⟨N, H, hH⟩ := ramseyHost_exists G
  exact ⟨edgeCount H, N, H, hH, rfl⟩

open scoped Classical in
/-- The size Ramsey number: the least number of edges in a finite graph Ramsey for `G`. -/
noncomputable def sizeRamseyNumber {W : Type*} [Fintype W] (G : SimpleGraph W) : ℕ :=
  Nat.find (ramseyHostEdgeCount_exists G)

open scoped Classical in
lemma sizeRamseyNumber_spec {W : Type*} [Fintype W] (G : SimpleGraph W) :
    HasRamseyHostWithEdges G (sizeRamseyNumber G) := by
  exact Nat.find_spec (ramseyHostEdgeCount_exists G)

open scoped Classical in
lemma sizeRamseyNumber_le_of_ramsey {W : Type*} [Fintype W] (G : SimpleGraph W)
    {N : ℕ} {H : SimpleGraph (Fin N)} (hH : IsRamseyFor H G) :
    sizeRamseyNumber G ≤ edgeCount H := by
  exact Nat.find_min' (ramseyHostEdgeCount_exists G) ⟨N, H, hH, rfl⟩

open scoped Classical in
lemma ramsey_edgeCount_ge_sizeRamseyNumber {W : Type*} [Fintype W]
    (G : SimpleGraph W) {N : ℕ} {H : SimpleGraph (Fin N)} (hH : IsRamseyFor H G) :
    sizeRamseyNumber G ≤ edgeCount H :=
  sizeRamseyNumber_le_of_ramsey G hH

open scoped Classical in
/-- The proposed uniform linear size-Ramsey bound at one fixed maximum degree. -/
def FixedDegreeLinearSizeRamsey (d : ℕ) : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.maxDegree ≤ d → sizeRamseyNumber G ≤ C * Fintype.card V

open scoped Classical in
/-- The assertion asked for in Erdős Problem 559. -/
def Erdos559Statement : Prop :=
  ∀ d : ℕ, FixedDegreeLinearSizeRamsey d

open scoped Classical in
theorem erdos_559 : ¬Erdos559Statement := by
  sorry

end Erdos559

end
