/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueExpansion
import ErdosProblems.Erdos570.CycleCliqueArithmetic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# BFS levels in the EFRS cycle--clique argument

This file carries out the expansion and level-size recurrence.  The one
remaining geometric input is stated explicitly as `CycleLevelIndependent`:
the first `floor ((m-1)/2)` distance levels of a `C_m`-free graph contain an
independent set of the EFRS size.  A separate file proves that ordered-tree
lemma.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- The vertices at graph distance exactly `i` from `x`. -/
def distanceLevel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.dist x v = i

@[simp] theorem mem_distanceLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {x v : V} {i : ℕ} :
    v ∈ distanceLevel G x i ↔ G.dist x v = i := by
  simp [distanceLevel]

theorem distanceLevel_zero_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Connected) (x : V) :
    distanceLevel G x 0 = {x} := by
  ext v
  simp [hconn.dist_eq_zero_iff, eq_comm]

/-- Every neighbor of a set in level `i` lies in one of the three adjacent
levels. -/
theorem relativeNeighborFinset_distanceLevel_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (i : ℕ) (B : Finset V)
    (hB : B ⊆ distanceLevel G x i) :
    relativeNeighborFinset G Finset.univ B ⊆
      distanceLevel G x (i - 1) ∪ distanceLevel G x i ∪
        distanceLevel G x (i + 1) := by
  intro v hv
  obtain ⟨-, y, hyB, hyv⟩ := mem_relativeNeighborFinset.mp hv
  have hyi : G.dist x y = i := mem_distanceLevel.mp (hB hyB)
  rcases SimpleGraph.Adj.diff_dist_adj (u := x) hyv with hsame | hup | hdown
  · simp [mem_distanceLevel, hsame, hyi]
  · simp [mem_distanceLevel, hup, hyi]
  · simp [mem_distanceLevel, hdown, hyi]

/-- The exact geometric statement proved by the ordered BFS-tree argument
of Erdős--Faudree--Rousseau--Schelp. -/
def CycleLevelIndependent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : Prop :=
    ¬ SimpleGraph.cycleGraph m ⊑ G →
    ∀ (x : V) (i : ℕ), 1 ≤ i → i ≤ (m - 1) / 2 →
      ∃ I : Finset V,
        I ⊆ distanceLevel G x i ∧
        G.IsIndepSet (I : Set V) ∧
        (distanceLevel G x i).card ≤ (m - 2) * I.card

/-- Expansion plus the ordered-level lemma force an independent set of size
`n`.  This is the combinatorial heart of the EFRS polynomial
cycle--clique Ramsey bound. -/
theorem efrs_expansion_forces_large_independent
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m a n : ℕ}
    (hm : 3 ≤ m) (ha : 1 ≤ a) (hn : n ≤ a ^ ((m - 1) / 2))
    (hconn : G.Connected)
    (hlevel : CycleLevelIndependent G m)
    (hcycle : ¬ SimpleGraph.cycleGraph m ⊑ G)
    (hexpand : ExpandsIndependentOn G ((m - 2) * (a + 2)) Finset.univ) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧ n ≤ I.card := by
  let t := (m - 1) / 2
  let c := m - 2
  have hcpos : 0 < c := by simp [c]; omega
  let x : V := Classical.choice (inferInstance : Nonempty V)
  have hlevels : ∀ i : ℕ, i ≤ t →
      ∃ I : Finset V,
        I ⊆ distanceLevel G x i ∧
        G.IsIndepSet (I : Set V) ∧
        (distanceLevel G x i).card ≤ c * I.card := by
    intro i hit
    by_cases hi0 : i = 0
    · subst i
      refine ⟨{x}, ?_, ?_, ?_⟩
      · rw [distanceLevel_zero_eq_singleton hconn]
      · simp [SimpleGraph.isIndepSet_iff]
      · rw [distanceLevel_zero_eq_singleton hconn]
        simp [c]
        omega
    · have hi : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hit' : i ≤ (m - 1) / 2 := by simpa only [t] using hit
      simpa only [c] using hlevel hcycle x i hi hit'
  choose B hBsub hBind hBcard using hlevels
  let C : ℕ → Finset V := fun i ↦
    if hi : i ≤ t then B i hi else ∅
  have hCsub : ∀ i : ℕ, i ≤ t → C i ⊆ distanceLevel G x i := by
    intro i hi
    simp only [C, dif_pos hi]
    exact hBsub i hi
  have hCind : ∀ i : ℕ, i ≤ t →
      G.IsIndepSet (C i : Set V) := by
    intro i hi
    simp only [C, dif_pos hi]
    exact hBind i hi
  have hCcard : ∀ i : ℕ, i ≤ t →
      (distanceLevel G x i).card ≤ c * (C i).card := by
    intro i hi
    simp only [C, dif_pos hi]
    exact hBcard i hi
  let b : ℕ → ℕ := fun i ↦ (C i).card
  have hb₀ : b 0 = 1 := by
    have hsub := hCsub 0 (by omega : 0 ≤ t)
    have hcard := hCcard 0 (by omega : 0 ≤ t)
    have hlevel₀ : distanceLevel G x 0 = {x} :=
      distanceLevel_zero_eq_singleton hconn x
    have hle : (C 0).card ≤ 1 := by
      simpa [hlevel₀] using Finset.card_le_card hsub
    have hpos : 1 ≤ (C 0).card := by
      rw [hlevel₀] at hcard
      simp only [Finset.card_singleton] at hcard
      have : 1 ≤ c * (C 0).card := hcard
      by_contra hz
      have : (C 0).card = 0 := by omega
      simp [this] at ‹1 ≤ c * (C 0).card›
    simp only [b]
    omega
  have htpos : 1 ≤ t := by simp [t]; omega
  have hb₁ : a + 2 ≤ b 1 := by
    let B₀ := C 0
    let B₁ := C 1
    have hB₀eq : B₀ = {x} := by
      apply Finset.eq_of_subset_of_card_le
      · simpa [B₀, distanceLevel_zero_eq_singleton hconn] using
          hCsub 0 (by omega : 0 ≤ t)
      · simp [B₀, hb₀, b]
    have hex := hexpand B₀
      (by simpa [B₀] using hCsub 0 (by omega : 0 ≤ t))
      (by simpa [B₀] using hCind 0 (by omega : 0 ≤ t))
    have hNsub := relativeNeighborFinset_distanceLevel_subset
      G x 0 B₀ (by simpa [B₀] using hCsub 0 (by omega : 0 ≤ t))
    have hNlevel₁ : relativeNeighborFinset G Finset.univ B₀ ⊆
        distanceLevel G x 1 := by
      intro v hv
      rw [hB₀eq] at hv
      obtain ⟨-, y, hy, hyv⟩ := mem_relativeNeighborFinset.mp hv
      simp only [Finset.mem_singleton] at hy
      subst y
      exact mem_distanceLevel.mpr (SimpleGraph.dist_eq_one_iff_adj.mpr hyv)
    have hchain : c * (a + 2) ≤ c * B₁.card := by
      calc
        c * (a + 2) = (m - 2) * (a + 2) * B₀.card := by
          simp [c, hB₀eq]
        _ ≤ (relativeNeighborFinset G Finset.univ B₀).card := hex
        _ ≤ (distanceLevel G x 1).card := Finset.card_le_card hNlevel₁
        _ ≤ c * B₁.card := by simpa [B₁] using hCcard 1 htpos
    have := Nat.le_of_mul_le_mul_left hchain hcpos
    simpa [b, B₁] using this
  have hrec : ∀ i : ℕ, 1 ≤ i → i < t →
      (a + 1) * b i ≤ b (i - 1) + b (i + 1) := by
    intro i hi hit
    have him1 : i - 1 ≤ t := by omega
    have hii : i ≤ t := by omega
    have hip1 : i + 1 ≤ t := by omega
    let Bm := C (i - 1)
    let Bi := C i
    let Bp := C (i + 1)
    let Am := distanceLevel G x (i - 1)
    let Ai := distanceLevel G x i
    let Ap := distanceLevel G x (i + 1)
    have hex := hexpand Bi (by simpa [Bi] using hCsub i hii)
      (by simpa [Bi] using hCind i hii)
    have hNsub : relativeNeighborFinset G Finset.univ Bi ⊆
        Am ∪ Ai ∪ Ap := by
      simpa [Am, Ai, Ap, Bi] using
        relativeNeighborFinset_distanceLevel_subset G x i Bi
          (by simpa [Bi] using hCsub i hii)
    have hunion : (Am ∪ Ai ∪ Ap).card ≤
        Am.card + Ai.card + Ap.card := by
      have h₁ := Finset.card_union_le Am Ai
      have h₂ := Finset.card_union_le (Am ∪ Ai) Ap
      omega
    have hscaled : c * (a + 2) * Bi.card ≤
        c * (Bm.card + Bi.card + Bp.card) := by
      calc
        c * (a + 2) * Bi.card =
            ((m - 2) * (a + 2)) * Bi.card := by simp [c]
        _ ≤ (relativeNeighborFinset G Finset.univ Bi).card := hex
        _ ≤ (Am ∪ Ai ∪ Ap).card := Finset.card_le_card hNsub
        _ ≤ Am.card + Ai.card + Ap.card := hunion
        _ ≤ c * Bm.card + c * Bi.card + c * Bp.card := by
          exact Nat.add_le_add
            (Nat.add_le_add (hCcard (i - 1) him1) (hCcard i hii))
            (hCcard (i + 1) hip1)
        _ = c * (Bm.card + Bi.card + Bp.card) := by ring
    have hcancel : (a + 2) * Bi.card ≤
        Bm.card + Bi.card + Bp.card :=
      Nat.le_of_mul_le_mul_left (by simpa [mul_assoc] using hscaled) hcpos
    have harith : (a + 1) * Bi.card ≤ Bm.card + Bp.card := by
      have hid : (a + 2) * Bi.card = (a + 1) * Bi.card + Bi.card := by ring
      rw [hid] at hcancel
      omega
    simpa [b, Bm, Bi, Bp] using harith
  have hfinalGrowth : a ^ t ≤ b t :=
    efrs_level_growth ha b hb₀ hb₁ hrec t le_rfl
  refine ⟨C t, hCind t le_rfl, ?_⟩
  simpa [b] using hn.trans hfinalGrowth

end Erdos570
