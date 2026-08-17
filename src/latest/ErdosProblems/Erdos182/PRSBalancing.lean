import ErdosProblems.Erdos182.Roof

/-!
# The PRS switching (balancing) lemma

This file proves the finite switching argument called Lemma 5.3.6 in
Shirazi's exposition of the Pyber--Rödl--Szemerédi theorem.  The right part
is the half-regular part, in accordance with the conventions in `Roof.lean`.
All estimates are stated over `ℕ`, after clearing the positive denominators.
-/

namespace Erdos182

open Finset

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A prospective balanced subgraph: `active` records the retained vertices
on the half-regular side and `picked b` records the edges retained at `b`.
Admissibility is imposed separately, so this data type is useful during a
switch. -/
structure BalancedChoice (A B : Type*) where
  active : Finset B
  picked : B → Finset A

namespace BalancedChoice

/-- The load of a left vertex in a choice. -/
noncomputable def load (C : BalancedChoice A B) (a : A) : ℕ :=
  by classical exact (C.active.filter fun b ↦ a ∈ C.picked b).card

/-- The associated bipartite graph. -/
def graph (C : BalancedChoice A B) : BipartiteGraph A B :=
  ⟨fun a b ↦ b ∈ C.active ∧ a ∈ C.picked b⟩

/-- Maximum load on the displayed left part. -/
noncomputable def maxLoad (C : BalancedChoice A B) (A₀ : Finset A) : ℕ :=
  A₀.sup C.load

/-- Number of displayed left vertices attaining the maximum load. -/
noncomputable def topCount (C : BalancedChoice A B) (A₀ : Finset A) : ℕ :=
  (A₀.filter fun a ↦ C.load a = C.maxLoad A₀).card

/-- A single natural-valued objective encoding lexicographic minimization of
maximum load and then of the number of maximizers. -/
noncomputable def cost (C : BalancedChoice A B) (A₀ : Finset A) : ℕ :=
  C.maxLoad A₀ * (A₀.card + 1) + C.topCount A₀

/-- Replace one active right vertex by an inactive one and use the prescribed
edge set at the new vertex. -/
noncomputable def switch (C : BalancedChoice A B) (old new : B) (T : Finset A) :
    BalancedChoice A B := by
  classical
  exact
    { active := insert new (C.active.erase old)
      picked := Function.update C.picked new T }

/-- The choice keeps exactly `ell` original edges at each active right vertex,
uses exactly `|A₀|` active vertices, and has no chosen left vertex outside
`A₀`. -/
def Admissible (C : BalancedChoice A B) (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (ell : ℕ) : Prop :=
  C.active ⊆ B₀ ∧ C.active.card = A₀.card ∧
    ∀ b ∈ C.active, C.picked b ⊆ G.leftNeighbors b ∧
      C.picked b ⊆ A₀ ∧ (C.picked b).card = ell

theorem graph_le_of_admissible {C : BalancedChoice A B} {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {ell : ℕ} (hC : C.Admissible G A₀ B₀ ell) :
    C.graph ≤ G := by
  intro a b hab
  exact (G.mem_leftNeighbors a b).mp ((hC.2.2 b hab.1).1 hab.2)

theorem graph_supportedOn_of_admissible {C : BalancedChoice A B}
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {ell : ℕ}
    (hC : C.Admissible G A₀ B₀ ell) : C.graph.SupportedOn A₀ C.active := by
  intro a b hab
  exact ⟨(hC.2.2 b hab.1).2.1 hab.2, hab.1⟩

@[simp]
theorem rightDegree_graph_of_mem {C : BalancedChoice A B} {b : B}
    (hb : b ∈ C.active) : C.graph.rightDegree b = (C.picked b).card := by
  classical
  simp [rightDegree, leftNeighbors, graph, hb]

@[simp]
theorem leftDegree_graph (C : BalancedChoice A B) (a : A) :
    C.graph.leftDegree a = C.load a := by
  classical
  unfold leftDegree rightNeighbors load
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and]
  change (C.graph.Adj a b ↔ b ∈ C.active ∧ a ∈ C.picked b)
  rfl

theorem isRightRegularOn_graph_of_admissible {C : BalancedChoice A B}
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {ell : ℕ}
    (hC : C.Admissible G A₀ B₀ ell) : C.graph.IsRightRegularOn C.active ell := by
  intro b hb
  rw [rightDegree_graph_of_mem hb]
  exact (hC.2.2 b hb).2.2

theorem load_le_maxLoad (C : BalancedChoice A B) {A₀ : Finset A} {a : A}
    (ha : a ∈ A₀) : C.load a ≤ C.maxLoad A₀ := by
  exact Finset.le_sup ha

theorem topCount_le_card (C : BalancedChoice A B) (A₀ : Finset A) :
    C.topCount A₀ ≤ A₀.card := by
  exact card_filter_le _ _

section

noncomputable local instance : DecidableEq A := Classical.decEq A
noncomputable local instance : DecidableEq B := Classical.decEq B

theorem load_switch (C : BalancedChoice A B) {old new : B} (T : Finset A)
    (hold : old ∈ C.active) (hnew : new ∉ C.active) (a : A) :
    (C.switch old new T).load a =
      C.load a - (if a ∈ C.picked old then 1 else 0) + (if a ∈ T then 1 else 0) := by
  have hset :
      (C.switch old new T).active.filter
          (fun b ↦ a ∈ (C.switch old new T).picked b) =
        if a ∈ T then
          insert new ((C.active.filter fun b ↦ a ∈ C.picked b).erase old)
        else (C.active.filter fun b ↦ a ∈ C.picked b).erase old := by
    ext b
    rw [mem_filter]
    simp only [switch]
    by_cases hbnew : b = new
    · subst b
      by_cases haT : a ∈ T <;> simp [haT, hnew]
    · by_cases haT : a ∈ T <;> simp [haT, hbnew, and_assoc]
  rw [load, load, hset]
  by_cases haold : a ∈ C.picked old <;> by_cases haT : a ∈ T <;>
    simp [haold, haT, hold, hnew]

end

end BalancedChoice

open BalancedChoice

/-- Vertices whose load is at least one below the maximum. -/
noncomputable def highLoadSet (C : BalancedChoice A B) (A₀ : Finset A) : Finset A := by
  classical
  exact A₀.filter fun a ↦ C.maxLoad A₀ - 1 ≤ C.load a

/-- The local conclusion furnished by the switching argument. -/
def IsSwitchingStable (C : BalancedChoice A B) (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (γ ell : ℕ) : Prop := by
  classical
  exact ∀ b ∈ B₀, b ∉ C.active →
    γ - ell + 1 ≤ (G.leftNeighbors b ∩ highLoadSet C A₀).card

/-- There is at least one admissible balanced choice whenever the original
right degrees are at least `ell` and the right part has at least as many
vertices as the left part. -/
theorem exists_admissibleBalancedChoice (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (γ ell : ℕ)
    (hcard : A₀.card ≤ B₀.card)
    (hsupp : G.SupportedOn A₀ B₀)
    (hreg : G.IsRightRegularOn B₀ γ) (hell : ell ≤ γ) :
    ∃ C : BalancedChoice A B, C.Admissible G A₀ B₀ ell := by
  classical
  obtain ⟨S, hSB, hScard⟩ := B₀.exists_subset_card_eq hcard
  have hpick : ∀ b ∈ S, ∃ T ⊆ G.leftNeighbors b, T ⊆ A₀ ∧ T.card = ell := by
    intro b hb
    have hbB : b ∈ B₀ := hSB hb
    have hncard : (G.leftNeighbors b).card = γ := hreg b hbB
    have hNA : G.leftNeighbors b ⊆ A₀ := by
      intro a ha
      exact (hsupp ((G.mem_leftNeighbors a b).mp ha)).1
    obtain ⟨T, hTN, hTcard⟩ := (G.leftNeighbors b).exists_subset_card_eq (hncard.symm ▸ hell)
    exact ⟨T, hTN, hTN.trans hNA, hTcard⟩
  let picked : B → Finset A := fun b ↦
    if hb : b ∈ S then Classical.choose (hpick b hb) else ∅
  let C : BalancedChoice A B := ⟨S, picked⟩
  refine ⟨C, hSB, hScard, ?_⟩
  intro b hb
  simp only [C, picked, hb, dif_pos]
  exact ⟨(Classical.choose_spec (hpick b hb)).1,
    (Classical.choose_spec (hpick b hb)).2⟩

theorem sum_load_eq_of_admissible {C : BalancedChoice A B}
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {ell : ℕ}
    (hC : C.Admissible G A₀ B₀ ell) :
    ∑ a ∈ A₀, C.load a = ell * A₀.card := by
  classical
  calc
    (∑ a ∈ A₀, C.load a) =
        ∑ a ∈ A₀, ∑ b ∈ C.active, if a ∈ C.picked b then 1 else 0 := by
          apply sum_congr rfl
          intro a _
          rw [Finset.sum_boole]
          rfl
    _ = ∑ b ∈ C.active, ∑ a ∈ A₀, if a ∈ C.picked b then 1 else 0 := by
          rw [sum_comm]
    _ = ∑ _b ∈ C.active, ell := by
          apply sum_congr rfl
          intro b hb
          have hp := hC.2.2 b hb
          rw [← hp.2.2, Finset.sum_boole]
          have heq : A₀.filter (fun a ↦ a ∈ C.picked b) = C.picked b := by
            ext a
            simp only [mem_filter]
            exact ⟨fun h ↦ h.2, fun h ↦ ⟨hp.2.1 h, h⟩⟩
          rw [heq]
          simp
    _ = ell * A₀.card := by simp [hC.2.1, Nat.mul_comm]

theorem regularDegree_le_maxLoad_of_admissible {C : BalancedChoice A B}
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B} {ell : ℕ}
    (hA : A₀.Nonempty) (hC : C.Admissible G A₀ B₀ ell) :
    ell ≤ C.maxLoad A₀ := by
  have hsum : (∑ a ∈ A₀, C.load a) ≤
      ∑ _a ∈ A₀, C.maxLoad A₀ := by
    exact sum_le_sum fun a ha ↦ C.load_le_maxLoad ha
  rw [sum_load_eq_of_admissible hC] at hsum
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hsum' : A₀.card * ell ≤ A₀.card * C.maxLoad A₀ := by
    simpa [Nat.mul_comm] using hsum
  exact Nat.le_of_mul_le_mul_left hsum' hA.card_pos

/-- A minimum-cost admissible choice is stable under all one-vertex
switches.  This is the finite switching argument in Shirazi Lemma 5.3.6. -/
theorem exists_admissible_isSwitchingStable (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (γ ell : ℕ)
    (hA : A₀.Nonempty) (hcard : A₀.card < B₀.card)
    (hsupp : G.SupportedOn A₀ B₀)
    (hreg : G.IsRightRegularOn B₀ γ) (hellpos : 1 ≤ ell) (hellγ : ell < γ) :
    ∃ C : BalancedChoice A B,
      C.Admissible G A₀ B₀ ell ∧ IsSwitchingStable C G A₀ B₀ γ ell := by
  classical
  have hex : ∃ n : ℕ, ∃ C : BalancedChoice A B,
      C.Admissible G A₀ B₀ ell ∧ C.cost A₀ = n := by
    obtain ⟨C, hC⟩ := exists_admissibleBalancedChoice G A₀ B₀ γ ell
      hcard.le hsupp hreg hellγ.le
    exact ⟨C.cost A₀, C, hC, rfl⟩
  let n := Nat.find hex
  obtain ⟨C, hC, hcost⟩ := Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro b hbB hbC
  by_contra hbad
  have hinter : (G.leftNeighbors b ∩ highLoadSet C A₀).card ≤ γ - ell := by
    omega
  have hNbcard : (G.leftNeighbors b).card = γ := hreg b hbB
  have hdiffcard : ell ≤ (G.leftNeighbors b \ highLoadSet C A₀).card := by
    have hpartition := card_sdiff_add_card_inter (G.leftNeighbors b) (highLoadSet C A₀)
    omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    (G.leftNeighbors b \ highLoadSet C A₀).exists_subset_card_eq hdiffcard
  have hTN : T ⊆ G.leftNeighbors b :=
    hTsub.trans sdiff_subset
  have hTA : T ⊆ A₀ := by
    intro a ha
    exact (hsupp ((G.mem_leftNeighbors a b).mp (hTN ha))).1
  have hTlow : ∀ a ∈ T, C.load a + 1 < C.maxLoad A₀ := by
    intro a ha
    have haA := hTA ha
    have hnot : a ∉ highLoadSet C A₀ := (mem_sdiff.mp (hTsub ha)).2
    simpa [highLoadSet, haA] using hnot
  have hDpos : 0 < C.maxLoad A₀ := by
    obtain ⟨old, hold⟩ : C.active.Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro he
      have := hC.2.1
      rw [he, card_empty] at this
      exact hA.card_pos.ne' this.symm
    obtain ⟨a, haPick⟩ : (C.picked old).Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro he
      have := (hC.2.2 old hold).2.2
      rw [he, card_empty] at this
      omega
    have haA : a ∈ A₀ := (hC.2.2 old hold).2.1 haPick
    have hload : 0 < C.load a := by
      rw [BalancedChoice.load, card_pos]
      exact ⟨old, mem_filter.mpr ⟨hold, haPick⟩⟩
    exact hload.trans_le (C.load_le_maxLoad haA)
  obtain ⟨aMax, haMaxA, haMax⟩ := Finset.exists_mem_eq_sup A₀ hA C.load
  have haMaxEq : C.load aMax = C.maxLoad A₀ := haMax.symm
  obtain ⟨old, hold, haOld⟩ : ∃ old ∈ C.active, aMax ∈ C.picked old := by
    have : 0 < C.load aMax := by omega
    rw [BalancedChoice.load, card_pos] at this
    obtain ⟨old, hold'⟩ := this
    exact ⟨old, (mem_filter.mp hold').1, (mem_filter.mp hold').2⟩
  let C' := C.switch old b T
  have hC' : C'.Admissible G A₀ B₀ ell := by
    refine ⟨?_, ?_, ?_⟩
    · intro b' hb'
      simp only [C', BalancedChoice.switch, mem_insert, mem_erase] at hb'
      rcases hb' with rfl | ⟨_, hb'⟩
      · exact hbB
      · exact hC.1 hb'
    · dsimp [C', BalancedChoice.switch]
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_erase_of_mem hold, hC.2.1]
        exact Nat.sub_add_cancel hA.card_pos
      · intro hbErase
        exact hbC (mem_erase.mp hbErase).2
    · intro b' hb'
      simp only [C', BalancedChoice.switch, mem_insert, mem_erase] at hb'
      rcases hb' with rfl | ⟨hb'old, hb'C⟩
      · simpa [C', BalancedChoice.switch] using ⟨hTN, hTA, hTcard⟩
      · have hb'ne : b' ≠ b := by
          intro heq
          exact hbC (heq ▸ hb'C)
        simpa [C', BalancedChoice.switch, hb'ne] using hC.2.2 b' hb'C
  have hload_le : ∀ a ∈ A₀, C'.load a ≤ C.maxLoad A₀ := by
    intro a haA
    change (C.switch old b T).load a ≤ C.maxLoad A₀
    rw [C.load_switch T hold hbC a]
    by_cases haT : a ∈ T
    · have := hTlow a haT
      simp [haT]
      omega
    · have := C.load_le_maxLoad haA
      simp [haT]
      omega
  have hmax_le : C'.maxLoad A₀ ≤ C.maxLoad A₀ := by
    exact Finset.sup_le hload_le
  have hnotT : aMax ∉ T := by
    intro haT
    have := hTlow aMax haT
    omega
  have hloadMax' : C'.load aMax < C.maxLoad A₀ := by
    change (C.switch old b T).load aMax < C.maxLoad A₀
    rw [C.load_switch T hold hbC aMax]
    simp [haOld, hnotT, haMaxEq, hDpos]
  have hcostlt : C'.cost A₀ < C.cost A₀ := by
    by_cases hmax : C'.maxLoad A₀ = C.maxLoad A₀
    · have htopsub :
          A₀.filter (fun a ↦ C'.load a = C'.maxLoad A₀) ⊂
            A₀.filter (fun a ↦ C.load a = C.maxLoad A₀) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro a ha
          have haA : a ∈ A₀ := (mem_filter.mp ha).1
          have hnew : C'.load a = C.maxLoad A₀ := (mem_filter.mp ha).2.trans hmax
          have holdle := C.load_le_maxLoad haA
          have hnotlow : a ∉ T := by
            intro haT
            have := hTlow a haT
            change (C.switch old b T).load a = C.maxLoad A₀ at hnew
            rw [C.load_switch T hold hbC a] at hnew
            simp [haT] at hnew
            omega
          change (C.switch old b T).load a = C.maxLoad A₀ at hnew
          rw [C.load_switch T hold hbC a] at hnew
          simp [hnotlow] at hnew
          exact mem_filter.mpr ⟨haA, by omega⟩
        · intro heq
          have haOldTop : aMax ∈ A₀.filter (fun a ↦ C.load a = C.maxLoad A₀) :=
            mem_filter.mpr ⟨haMaxA, haMaxEq⟩
          have haNewTop := heq.symm ▸ haOldTop
          exact (ne_of_lt hloadMax') ((mem_filter.mp haNewTop).2.trans hmax)
      have htoplt : C'.topCount A₀ < C.topCount A₀ :=
        card_lt_card htopsub
      simp only [BalancedChoice.cost, hmax]
      omega
    · have hmaxlt : C'.maxLoad A₀ < C.maxLoad A₀ := lt_of_le_of_ne hmax_le hmax
      have htop := C'.topCount_le_card A₀
      simp only [BalancedChoice.cost]
      have hsucc : C'.maxLoad A₀ + 1 ≤ C.maxLoad A₀ := by omega
      calc
        C'.maxLoad A₀ * (A₀.card + 1) + C'.topCount A₀
            ≤ C'.maxLoad A₀ * (A₀.card + 1) + A₀.card :=
          Nat.add_le_add_left htop _
        _ < (C'.maxLoad A₀ + 1) * (A₀.card + 1) := by
          simp only [Nat.add_mul, one_mul]
          omega
        _ ≤ C.maxLoad A₀ * (A₀.card + 1) :=
          Nat.mul_le_mul_right _ hsucc
        _ ≤ C.maxLoad A₀ * (A₀.card + 1) + C.topCount A₀ :=
          Nat.le_add_right _ _
  have hmin := Nat.find_min' hex ⟨C', hC', rfl⟩
  have hcostlt' : C'.cost A₀ < Nat.find hex := hcostlt.trans_eq hcost
  exact (not_lt_of_ge hmin) hcostlt'

/-- The two double counts after switching.  `Δ` is any upper bound for the
left degrees of the original graph. -/
theorem balancing_bound_of_stable {G : BipartiteGraph A B}
    {A₀ : Finset A} {B₀ : Finset B} {γ ell Δ : ℕ} {C : BalancedChoice A B}
    (hC : C.Admissible G A₀ B₀ ell)
    (hstable : IsSwitchingStable C G A₀ B₀ γ ell)
    (hdeg : ∀ a ∈ A₀, G.leftDegree a ≤ Δ) :
    (C.maxLoad A₀ - 1) * (γ - ell) * (B₀.card - A₀.card) ≤
      Δ * ell * A₀.card := by
  classical
  let X := highLoadSet C A₀
  let R := B₀ \ C.active
  have hRcard : R.card = B₀.card - A₀.card := by
    dsimp [R]
    rw [card_sdiff_of_subset hC.1, hC.2.1]
  have hcount₁ : R.card * (γ - ell + 1) ≤
      ∑ b ∈ R, (G.leftNeighbors b ∩ X).card := by
    calc
      R.card * (γ - ell + 1) = ∑ _b ∈ R, (γ - ell + 1) := by simp
      _ ≤ ∑ b ∈ R, (G.leftNeighbors b ∩ X).card := by
        exact sum_le_sum fun b hb ↦ hstable b (mem_sdiff.mp hb).1 (mem_sdiff.mp hb).2
  have hdouble : (∑ b ∈ R, (G.leftNeighbors b ∩ X).card) ≤
      ∑ a ∈ X, G.leftDegree a := by
    calc
      (∑ b ∈ R, (G.leftNeighbors b ∩ X).card) =
          ∑ b ∈ R, ∑ a ∈ X, if G.Adj a b then 1 else 0 := by
            apply sum_congr rfl
            intro b _
            rw [Finset.sum_boole]
            congr 1
            ext a
            simp [leftNeighbors, and_comm]
      _ = ∑ a ∈ X, ∑ b ∈ R, if G.Adj a b then 1 else 0 := by
            rw [sum_comm]
      _ ≤ ∑ a ∈ X, G.leftDegree a := by
            apply sum_le_sum
            intro a ha
            rw [leftDegree, rightNeighbors]
            rw [Finset.sum_boole]
            exact card_le_card
              (filter_subset_filter (p := fun b ↦ G.Adj a b) (subset_univ R))
  have hXsub : X ⊆ A₀ := by
    intro a ha
    exact (mem_filter.mp ha).1
  have hdegcount : (∑ a ∈ X, G.leftDegree a) ≤ X.card * Δ := by
    calc
      (∑ a ∈ X, G.leftDegree a) ≤ ∑ _a ∈ X, Δ := by
        exact sum_le_sum fun a ha ↦ hdeg a (hXsub ha)
      _ = X.card * Δ := by simp [Nat.mul_comm]
  have hfirst : R.card * (γ - ell) ≤ Δ * X.card := by
    calc
      R.card * (γ - ell) ≤ R.card * (γ - ell + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ ≤ ∑ b ∈ R, (G.leftNeighbors b ∩ X).card := hcount₁
      _ ≤ ∑ a ∈ X, G.leftDegree a := hdouble
      _ ≤ X.card * Δ := hdegcount
      _ = Δ * X.card := Nat.mul_comm _ _
  have hloadcount : (C.maxLoad A₀ - 1) * X.card ≤ ell * A₀.card := by
    have hlower : (C.maxLoad A₀ - 1) * X.card ≤ ∑ a ∈ X, C.load a := by
      calc
        (C.maxLoad A₀ - 1) * X.card = ∑ _a ∈ X, (C.maxLoad A₀ - 1) := by
          simp [Nat.mul_comm]
        _ ≤ ∑ a ∈ X, C.load a := by
          exact sum_le_sum fun a ha ↦ (mem_filter.mp ha).2
    have hsubsetSum : (∑ a ∈ X, C.load a) ≤ ∑ a ∈ A₀, C.load a :=
      sum_le_sum_of_subset_of_nonneg hXsub (fun _ _ _ ↦ Nat.zero_le _)
    have htotal : (∑ a ∈ A₀, C.load a) = ell * A₀.card := by
      calc
        (∑ a ∈ A₀, C.load a) =
            ∑ a ∈ A₀, ∑ b ∈ C.active, if a ∈ C.picked b then 1 else 0 := by
              apply sum_congr rfl
              intro a _
              rw [Finset.sum_boole]
              rfl
        _ = ∑ b ∈ C.active, ∑ a ∈ A₀, if a ∈ C.picked b then 1 else 0 := by
              rw [sum_comm]
        _ = ∑ _b ∈ C.active, ell := by
              apply sum_congr rfl
              intro b hb
              have hp := hC.2.2 b hb
              rw [← hp.2.2]
              rw [Finset.sum_boole]
              have heq : A₀.filter (fun a ↦ a ∈ C.picked b) = C.picked b := by
                ext a
                simp only [mem_filter]
                constructor
                · exact fun h ↦ h.2
                · exact fun h ↦ ⟨hp.2.1 h, h⟩
              rw [heq]
              simp
        _ = ell * A₀.card := by simp [hC.2.1, Nat.mul_comm]
    exact hlower.trans (hsubsetSum.trans_eq htotal)
  rw [← hRcard]
  calc
    (C.maxLoad A₀ - 1) * (γ - ell) * R.card =
        (C.maxLoad A₀ - 1) * (R.card * (γ - ell)) := by ac_rfl
    _ ≤ (C.maxLoad A₀ - 1) * (Δ * X.card) :=
      Nat.mul_le_mul_left _ hfirst
    _ = Δ * ((C.maxLoad A₀ - 1) * X.card) := by ac_rfl
    _ ≤ Δ * (ell * A₀.card) := Nat.mul_le_mul_left _ hloadcount
    _ = Δ * ell * A₀.card := by ac_rfl

/-- **PRS balancing lemma (Shirazi Lemma 5.3.6), denominator-free form.**

The input is `γ`-half-regular on the right, with a strictly larger right
part.  The hypothesis involving `L` is the cleared form of
`Δ(G) ≤ L * γ * |B₀| / |A₀|`.  The output is supported on a balanced
pair, is exactly `ell`-regular on its active right part, and its maximum left
degree `D` satisfies
`(D-1)(γ-ell)(|B₀|-|A₀|) ≤ γ |B₀| L ell`, which is equation (10)
with denominators cleared. -/
theorem prs_balancing (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (γ ell L : ℕ)
    (hA : A₀.Nonempty) (hcard : A₀.card < B₀.card)
    (hsupp : G.SupportedOn A₀ B₀)
    (hreg : G.IsRightRegularOn B₀ γ) (hellpos : 1 ≤ ell) (hellγ : ell < γ)
    (hdeg : ∀ a ∈ A₀, G.leftDegree a * A₀.card ≤ L * γ * B₀.card) :
    ∃ (H : BipartiteGraph A B) (B₁ : Finset B) (D : ℕ),
      H ≤ G ∧ H.SupportedOn A₀ B₁ ∧ B₁ ⊆ B₀ ∧
      B₁.card = A₀.card ∧ H.IsRightRegularOn B₁ ell ∧
      (∀ a ∈ A₀, H.leftDegree a ≤ D) ∧
      (D - 1) * (γ - ell) * (B₀.card - A₀.card) ≤ γ * B₀.card * L * ell := by
  classical
  obtain ⟨C, hC, hstable⟩ := exists_admissible_isSwitchingStable G A₀ B₀ γ ell
    hA hcard hsupp hreg hellpos hellγ
  let Δ := A₀.sup G.leftDegree
  have hΔ : ∀ a ∈ A₀, G.leftDegree a ≤ Δ := fun a ha ↦ Finset.le_sup ha
  have hΔscaled : Δ * A₀.card ≤ L * γ * B₀.card := by
    obtain ⟨a, haA, haeq⟩ := Finset.exists_mem_eq_sup A₀ hA G.leftDegree
    change A₀.sup G.leftDegree * A₀.card ≤ L * γ * B₀.card
    rw [haeq]
    exact hdeg a haA
  have hbal := balancing_bound_of_stable hC hstable hΔ
  refine ⟨C.graph, C.active, C.maxLoad A₀, C.graph_le_of_admissible hC,
    C.graph_supportedOn_of_admissible hC, hC.1, hC.2.1,
    C.isRightRegularOn_graph_of_admissible hC, ?_, ?_⟩
  · intro a ha
    rw [C.leftDegree_graph]
    exact C.load_le_maxLoad ha
  · calc
      (C.maxLoad A₀ - 1) * (γ - ell) * (B₀.card - A₀.card)
          ≤ Δ * ell * A₀.card := hbal
      _ = ell * (Δ * A₀.card) := by ac_rfl
      _ ≤ ell * (L * γ * B₀.card) := Nat.mul_le_mul_left _ hΔscaled
      _ = γ * B₀.card * L * ell := by ac_rfl

/-- Real-parameter version of `prs_balancing`.  Keeping `L` in `ℝ` is
essential in the PRS application, where `L` tends to one and rounding it to
a natural number would lose the final strict inequality. -/
theorem prs_balancing_real (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (γ ell : ℕ) (L : ℝ)
    (hA : A₀.Nonempty) (hcard : A₀.card < B₀.card)
    (hsupp : G.SupportedOn A₀ B₀)
    (hreg : G.IsRightRegularOn B₀ γ) (hellpos : 1 ≤ ell) (hellγ : ell < γ)
    (hdeg : ∀ a ∈ A₀,
      (G.leftDegree a : ℝ) * (A₀.card : ℝ) ≤
        L * (γ : ℝ) * (B₀.card : ℝ)) :
    ∃ (H : BipartiteGraph A B) (B₁ : Finset B) (D : ℕ),
      H ≤ G ∧ H.SupportedOn A₀ B₁ ∧ B₁ ⊆ B₀ ∧
      B₁.card = A₀.card ∧ H.IsRightRegularOn B₁ ell ∧
      (∀ a ∈ A₀, H.leftDegree a ≤ D) ∧ ell ≤ D ∧
      (((D - 1) * (γ - ell) * (B₀.card - A₀.card) : ℕ) : ℝ) ≤
        (γ : ℝ) * (B₀.card : ℝ) * L * (ell : ℝ) := by
  classical
  obtain ⟨C, hC, hstable⟩ := exists_admissible_isSwitchingStable G A₀ B₀ γ ell
    hA hcard hsupp hreg hellpos hellγ
  let Δ := A₀.sup G.leftDegree
  have hΔ : ∀ a ∈ A₀, G.leftDegree a ≤ Δ := fun a ha ↦ Finset.le_sup ha
  have hΔscaled : ((Δ : ℕ) : ℝ) * (A₀.card : ℝ) ≤
      L * (γ : ℝ) * (B₀.card : ℝ) := by
    obtain ⟨a, haA, haeq⟩ := Finset.exists_mem_eq_sup A₀ hA G.leftDegree
    have haeq' : Δ = G.leftDegree a := haeq
    rw [haeq']
    exact hdeg a haA
  have hbal := balancing_bound_of_stable hC hstable hΔ
  have hbalR :
      (((C.maxLoad A₀ - 1) * (γ - ell) * (B₀.card - A₀.card) : ℕ) : ℝ) ≤
        (((Δ * ell * A₀.card : ℕ) : ℝ)) := by
    exact_mod_cast hbal
  refine ⟨C.graph, C.active, C.maxLoad A₀, C.graph_le_of_admissible hC,
    C.graph_supportedOn_of_admissible hC, hC.1, hC.2.1,
    C.isRightRegularOn_graph_of_admissible hC, ?_,
    regularDegree_le_maxLoad_of_admissible hA hC, ?_⟩
  · intro a ha
    rw [C.leftDegree_graph]
    exact C.load_le_maxLoad ha
  · calc
      (((C.maxLoad A₀ - 1) * (γ - ell) * (B₀.card - A₀.card) : ℕ) : ℝ)
          ≤ (((Δ * ell * A₀.card : ℕ) : ℝ)) := hbalR
      _ = (ell : ℝ) * ((Δ : ℕ) : ℝ) * (A₀.card : ℝ) := by
        push_cast
        ring
      _ = (ell : ℝ) * (((Δ : ℕ) : ℝ) * (A₀.card : ℝ)) := by ring
      _ ≤ (ell : ℝ) * (L * (γ : ℝ) * (B₀.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hΔscaled (Nat.cast_nonneg ell)
      _ = (γ : ℝ) * (B₀.card : ℝ) * L * (ell : ℝ) := by ring

end BipartiteGraph

end Erdos182
