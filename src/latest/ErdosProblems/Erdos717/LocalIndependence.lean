/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Maximum independent sets and low-pattern pruning inside a finite set. -/

import ErdosProblems.Erdos717.NeighborhoodPattern

open Function Set
open SimpleGraph

namespace Erdos717

/-- A finite vertex set has a largest independent subset, expressed without
changing the ambient vertex type. -/
theorem exists_maximum_independent_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset V) :
    ∃ I : Finset V, I ⊆ P ∧ G.IsIndepSet I ∧
      IndepBoundOn G P I.card := by
  classical
  let H := G.induce (P : Set V)
  obtain ⟨J, hJ⟩ := H.maximumIndepSet_exists
  let valEmb : P ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let I : Finset V := J.map valEmb
  have hIcard : I.card = J.card := by simp [I]
  have hIP : I ⊆ P := by
    intro x hx
    obtain ⟨y, _hyJ, rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  have hIind : G.IsIndepSet I := by
    rw [G.isIndepSet_iff]
    intro x hx y hy hxy
    obtain ⟨x', hx'J, hxx'⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'J, hyy'⟩ := Finset.mem_map.mp hy
    have hne' : x' ≠ y' := by
      intro h
      apply hxy
      rw [← hxx', ← hyy', h]
    have := (H.isIndepSet_iff.mp hJ.isIndepSet) hx'J hy'J hne'
    rw [← hxx', ← hyy']
    exact this
  refine ⟨I, hIP, hIind, ?_⟩
  intro A hAP hAind
  let liftEmb : A ↪ P :=
    ⟨fun x => ⟨x, hAP x.property⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun z : P => (z : V)) h)⟩
  let A' : Finset P := A.attach.map liftEmb
  have hA'card : A'.card = A.card := by simp [A']
  have hA'ind : H.IsIndepSet A' := by
    rw [H.isIndepSet_iff]
    intro x hx y hy hxy
    obtain ⟨x', hx'A, hxx'⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy'A, hyy'⟩ := Finset.mem_map.mp hy
    have hxA : (x' : V) ∈ A := by simpa using x'.property
    have hyA : (y' : V) ∈ A := by simpa using y'.property
    have hne : (x' : V) ≠ (y' : V) := by
      intro h
      apply hxy
      apply Subtype.ext
      rw [← hxx', ← hyy']
      exact h
    have := (G.isIndepSet_iff.mp hAind) hxA hyA hne
    rw [← hxx', ← hyy']
    exact this
  have := hJ.maximum A' hA'ind
  simpa only [hA'card, ← hIcard] using this

/-- Vertices outside `I` whose neighbourhood in `I` has size at most `b`. -/
def lowPatternFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (b : ℕ) : Finset V :=
  (P \ I).filter fun v => (G.neighborFinset v ∩ I).card ≤ b

/-- The complementary high-pattern vertices. -/
def highPatternFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (b : ℕ) : Finset V :=
  (P \ I).filter fun v => b < (G.neighborFinset v ∩ I).card

theorem low_high_pattern_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (hIP : I ⊆ P) (b : ℕ) :
    (lowPatternFinset G P I b).card +
      (highPatternFinset G P I b).card + I.card = P.card := by
  classical
  have hunion : lowPatternFinset G P I b ∪ highPatternFinset G P I b = P \ I := by
    ext x
    simp only [lowPatternFinset, highPatternFinset, Finset.mem_union,
      Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hle : (G.neighborFinset x ∩ I).card ≤ b
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, Nat.lt_of_not_ge hle⟩
  have hdisj : Disjoint (lowPatternFinset G P I b)
      (highPatternFinset G P I b) := by
    rw [Finset.disjoint_left]
    intro x hxL hxH
    have hle := (Finset.mem_filter.mp hxL).2
    have hlt := (Finset.mem_filter.mp hxH).2
    omega
  rw [← Finset.card_union_of_disjoint hdisj, hunion,
    Finset.card_sdiff_of_subset hIP]
  have hcard := Finset.card_le_card hIP
  omega

theorem lowPattern_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (b : ℕ) : lowPatternFinset G P I b ⊆ P :=
  (Finset.filter_subset _ _).trans Finset.sdiff_subset

theorem lowPattern_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (b : ℕ) : Disjoint I (lowPatternFinset G P I b) := by
  rw [Finset.disjoint_left]
  intro x hxI hxL
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxL).1).2 hxI

theorem lowPattern_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (b : ℕ) :
    ∀ v ∈ lowPatternFinset G P I b,
      (G.neighborFinset v ∩ I).card ≤ b := by
  intro v hv
  exact (Finset.mem_filter.mp hv).2

/-- Double-counting incidences with a bounded-degree independent set controls
the number of vertices having a large neighbourhood pattern. -/
theorem highPattern_card_mul_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I : Finset V) (D b : ℕ)
    (hIP : I ⊆ P) (hdegree : ∀ v ∈ P, G.degree v ≤ D) :
    (b + 1) * (highPatternFinset G P I b).card ≤ D * I.card := by
  classical
  let X := highPatternFinset G P I b
  have hlower : ∑ x ∈ X, (G.neighborFinset x ∩ I).card ≥
      X.card * (b + 1) := by
    calc
      X.card * (b + 1) = ∑ _x ∈ X, (b + 1) := by simp
      _ ≤ ∑ x ∈ X, (G.neighborFinset x ∩ I).card := by
        apply Finset.sum_le_sum
        intro x hx
        have := (Finset.mem_filter.mp hx).2
        omega
  have hswap : ∑ x ∈ X, (G.neighborFinset x ∩ I).card =
      ∑ i ∈ I, (G.neighborFinset i ∩ X).card := by
    have hleft (x : V) : (G.neighborFinset x ∩ I).card =
        ∑ i ∈ I, if G.Adj x i then 1 else 0 := by
      rw [show G.neighborFinset x ∩ I = I.filter fun i => G.Adj x i by
        ext i
        simp [G.mem_neighborFinset, and_comm]]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hright (i : V) : (G.neighborFinset i ∩ X).card =
        ∑ x ∈ X, if G.Adj x i then 1 else 0 := by
      rw [show G.neighborFinset i ∩ X = X.filter fun x => G.Adj x i by
        ext x
        simp [G.mem_neighborFinset, G.adj_comm, and_comm]]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    calc
      ∑ x ∈ X, (G.neighborFinset x ∩ I).card =
          ∑ x ∈ X, ∑ i ∈ I, if G.Adj x i then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            exact hleft x
      _ = ∑ i ∈ I, ∑ x ∈ X, if G.Adj x i then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i ∈ I, (G.neighborFinset i ∩ X).card := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact (hright i).symm
  have hupper : ∑ i ∈ I, (G.neighborFinset i ∩ X).card ≤ I.card * D := by
    calc
      ∑ i ∈ I, (G.neighborFinset i ∩ X).card ≤ ∑ i ∈ I, G.degree i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.card_le_card Finset.inter_subset_left
      _ ≤ ∑ _i ∈ I, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact hdegree i (hIP hi)
      _ = I.card * D := by simp
  rw [hswap] at hlower
  nlinarith

end Erdos717
