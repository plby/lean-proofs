/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SuspendedPath
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connected graphs of maximum degree two

The sparse-target decomposition needs an explicit enumeration of each
degree-two component.  A finite connected graph of maximum degree two which
has an endpoint is a path.  The result below records this in the indexed form
used by the suspended-path code.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

universe u

/-- An injective sequence indexed by `Fin n`, with consecutive vertices
adjacent.  Unlike `IsEndpointPath`, this also permits sequences of order zero
or one. -/
structure IsIndexedPath {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (p : Fin n → V) : Prop where
  injective : Function.Injective p
  adj : ∀ i j : Fin n, i.val + 1 = j.val → G.Adj (p i) (p j)

theorem degree_induce_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Set V} [Fintype S] (v : S) :
    (G.induce S).degree v ≤ G.degree v := by
  calc
    (G.induce S).degree v =
        ((G.induce S).neighborFinset v).card := rfl
    _ = (((G.induce S).neighborFinset v).map
        (Function.Embedding.subtype (· ∈ S))).card := by simp
    _ ≤ (G.neighborFinset v).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [G.mem_neighborFinset]
      exact ((G.induce S).mem_neighborFinset v y).mp hy
    _ = G.degree v := rfl

/-- Rooted path characterization of a finite connected graph of maximum
degree two. -/
theorem exists_bijective_indexedPath_start
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (s : V) (hs : G.degree s ≤ 1)
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ p : Fin (Fintype.card V) → V,
      Function.Bijective p ∧ IsIndexedPath G p ∧
        ∀ i, i.val = 0 → p i = s := by
  let P : ℕ → Prop := fun n ↦
    ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W = n → J.Connected →
      ∀ s : W, J.degree s ≤ 1 → (∀ v, J.degree v ≤ 2) →
      ∃ p : Fin (Fintype.card W) → W,
        Function.Bijective p ∧ IsIndexedPath J p ∧
          ∀ i, i.val = 0 → p i = s
  suffices hP : P (Fintype.card V) by
    exact hP V G rfl hconn s hs hdeg
  apply Nat.strong_induction_on (p := P) (Fintype.card V)
  intro n ih V _ _ G _ hn hconn s hs hdeg
  have hnpos : 0 < n := by
    rw [← hn, Fintype.card_pos_iff]
    exact hconn.nonempty
  by_cases hnone : n = 1
  · have hsub : Subsingleton V := by
      rw [← Fintype.card_le_one_iff_subsingleton, hn]
      omega
    let p : Fin (Fintype.card V) → V := fun _ ↦ s
    have hpbij : Function.Bijective p := by
      constructor
      · intro i j _
        apply Fin.ext
        have hi : i.val = 0 := by omega
        have hj : j.val = 0 := by omega
        omega
      · intro v
        refine ⟨⟨0, by rw [hn]; omega⟩, ?_⟩
        exact Subsingleton.elim _ _
    refine ⟨p, hpbij, ?_, fun _ _ ↦ rfl⟩
    constructor
    · exact hpbij.1
    · intro i j hij
      have hi : i.val = 0 := by omega
      have hj : j.val = 0 := by omega
      omega
  · have hntwo : 2 ≤ n := by omega
    letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [hn]
      omega)
    have hdegpos : 0 < G.degree s := by
      exact (G.degree_pos s).mpr (hconn.preconnected.not_isIsolated s)
    have hsone : G.degree s = 1 := by omega
    obtain ⟨u, hsu, hu_unique⟩ :=
      (G.degree_eq_one_iff_existsUnique_adj).mp hsone
    have hus : u ≠ s := hsu.ne'
    let S : Set V := ({s} : Set V)ᶜ
    let G' : SimpleGraph S := G.induce S
    have hconn' : G'.Connected := by
      exact hconn.induce_compl_singleton_of_degree_eq_one hsone
    let u' : S := ⟨u, by simpa [S] using hus⟩
    have hu'deg : G'.degree u' ≤ 1 := by
      have hmap :
          (G'.neighborFinset u').map
              (Function.Embedding.subtype (· ∈ S)) =
            G.neighborFinset u ∩ S.toFinset := by
        simpa only [G', u'] using G.map_neighborFinset_induce u'
      have hs_mem : s ∈ G.neighborFinset u := by
        rw [G.mem_neighborFinset]
        exact hsu.symm
      have hsub :
          ((G'.neighborFinset u').map
            (Function.Embedding.subtype (· ∈ S))) ⊆
            (G.neighborFinset u).erase s := by
        rw [hmap]
        intro x hx
        have hx' := Finset.mem_inter.mp hx
        rw [Finset.mem_erase]
        exact ⟨by simpa [S] using hx'.2, hx'.1⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_map] at hcard
      change G'.degree u' ≤ ((G.neighborFinset u).erase s).card at hcard
      rw [Finset.card_erase_of_mem hs_mem,
        G.card_neighborFinset_eq_degree] at hcard
      have hu2 := hdeg u
      omega
    have hdeg' : ∀ v : S, G'.degree v ≤ 2 := by
      intro v
      exact (degree_induce_le v).trans (hdeg v)
    have hcardS : Fintype.card S = n - 1 := by
      change Fintype.card ↑(({s} : Set V)ᶜ) = n - 1
      rw [Fintype.card_compl_set]
      simp [hn]
    have hcardSlt : Fintype.card S < n := by omega
    obtain ⟨q, hqbij, hqpath, hq0⟩ :=
      ih (Fintype.card S) hcardSlt S G' rfl hconn' u' hu'deg hdeg'
    have hcardSucc : Fintype.card V = Fintype.card S + 1 := by omega
    rw [hcardSucc]
    let tail : Fin (Fintype.card S) → V := fun i ↦ (q i).1
    let p : Fin (Fintype.card S + 1) → V := Fin.cases s tail
    have htail_inj : Function.Injective tail := by
      intro i j hij
      apply Fin.ext
      have hqeq : q i = q j := by
        apply Subtype.ext
        exact hij
      have := hqbij.1 hqeq
      exact congrArg Fin.val this
    have htail_ne_s (i) : tail i ≠ s := by
      exact (q i).2
    have hpinj : Function.Injective p := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => rfl
          | succ j => exact (htail_ne_s j hij.symm).elim
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (htail_ne_s i hij).elim
          | succ j => exact congrArg Fin.succ (htail_inj hij)
    have hpbij : Function.Bijective p := by
      exact (Fintype.bijective_iff_injective_and_card p).2
        ⟨hpinj, by rw [Fintype.card_fin]; exact hcardSucc.symm⟩
    have hpadj : ∀ i j : Fin (Fintype.card S + 1),
        i.val + 1 = j.val → G.Adj (p i) (p j) := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => omega
          | succ j =>
              let z : Fin (Fintype.card S) := ⟨0, by
                rw [hcardS]
                omega⟩
              have hj : j = z := Fin.ext (by
                change 0 + 1 = j.val + 1 at hij
                change j.val = z.val
                simp only [z]
                omega)
              have hqzero : q z = u' := by
                apply hq0
                rfl
              simpa only [p, Fin.cases_zero, Fin.cases_succ, tail, hj,
                hqzero, u'] using hsu
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              change i.val + 1 + 1 = 0 at hij
              omega
          | succ j =>
              apply hqpath.adj i j
              change i.val + 1 + 1 = j.val + 1 at hij
              omega
    exact ⟨p, hpbij, ⟨hpinj, hpadj⟩, fun i hi ↦ by
      have : i = 0 := Fin.ext hi
      subst i
      rfl⟩

end Erdos570
