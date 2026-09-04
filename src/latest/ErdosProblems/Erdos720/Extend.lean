import ErdosProblems.Erdos720.Foundation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos720

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The (open) graph neighborhood of a finite vertex set. -/
noncomputable def setNeighbors (G : SimpleGraph V) (X : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∃ x ∈ X, G.Adj x v

@[simp] lemma mem_setNeighbors {G : SimpleGraph V} {X : Finset V} {v : V} :
    v ∈ setNeighbors G X ↔ ∃ x ∈ X, G.Adj x v := by
  classical
  simp [setNeighbors]

@[simp] lemma setNeighbors_empty (G : SimpleGraph V) :
    setNeighbors G ∅ = ∅ := by
  classical
  simp [setNeighbors]

lemma setNeighbors_union (G : SimpleGraph V) (X Y : Finset V) :
    setNeighbors G (X ∪ Y) = setNeighbors G X ∪ setNeighbors G Y := by
  classical
  ext v
  simp [mem_setNeighbors]
  aesop

lemma setNeighbors_mono {G : SimpleGraph V} {X Y : Finset V} (hXY : X ⊆ Y) :
    setNeighbors G X ⊆ setNeighbors G Y := by
  intro v hv
  rcases mem_setNeighbors.mp hv with ⟨x, hx, hxv⟩
  exact mem_setNeighbors.mpr ⟨x, hXY hx, hxv⟩

/-- Neighbors not yet occupied by a partial tree embedding. -/
noncomputable def outsideNeighbors (G : SimpleGraph V) (used X : Finset V) : Finset V :=
  setNeighbors G X \ used

lemma outsideNeighbors_union (G : SimpleGraph V) (used X Y : Finset V) :
    outsideNeighbors G used (X ∪ Y) =
      outsideNeighbors G used X ∪ outsideNeighbors G used Y := by
  ext v
  simp [outsideNeighbors, setNeighbors_union]
  aesop

lemma outsideNeighbors_inter_subset (G : SimpleGraph V) (used X Y : Finset V) :
    outsideNeighbors G used (X ∩ Y) ⊆
      outsideNeighbors G used X ∩ outsideNeighbors G used Y := by
  intro v hv
  simp only [outsideNeighbors, mem_sdiff, mem_inter] at hv ⊢
  exact ⟨⟨setNeighbors_mono inter_subset_left hv.1, hv.2⟩,
    setNeighbors_mono inter_subset_right hv.1, hv.2⟩

lemma outsideNeighbors_card_submodular (G : SimpleGraph V) (used X Y : Finset V) :
    (outsideNeighbors G used (X ∩ Y)).card +
        (outsideNeighbors G used (X ∪ Y)).card ≤
      (outsideNeighbors G used X).card + (outsideNeighbors G used Y).card := by
  let A := outsideNeighbors G used X
  let B := outsideNeighbors G used Y
  have hi : outsideNeighbors G used (X ∩ Y) ⊆ A ∩ B :=
    outsideNeighbors_inter_subset G used X Y
  have hu : outsideNeighbors G used (X ∪ Y) = A ∪ B :=
    outsideNeighbors_union G used X Y
  calc
    (outsideNeighbors G used (X ∩ Y)).card +
          (outsideNeighbors G used (X ∪ Y)).card
        ≤ (A ∩ B).card + (A ∪ B).card := by
            rw [hu]
            exact Nat.add_le_add_right (card_le_card hi) _
    _ = A.card + B.card := by
          rw [add_comm, card_union_add_card_inter]

/-- A partial bounded-degree tree embedding satisfying the Friedman--Pippenger
extendability inequalities.  `deg` records the degrees already used in the
partial tree. -/
structure ExtendableState (G : SimpleGraph V) (d m : ℕ) where
  used : Finset V
  deg : V → ℕ
  deg_off : ∀ ⦃v⦄, v ∉ used → deg v = 0
  deg_le : ∀ v, deg v ≤ d
  balance : ∀ X : Finset V, X.card ≤ 2 * m →
    d * X.card ≤ (outsideNeighbors G used X).card + ∑ x ∈ X, deg x

namespace ExtendableState

variable {G : SimpleGraph V} {d m : ℕ}

def Critical (S : ExtendableState G d m) (X : Finset V) : Prop :=
  X.card ≤ 2 * m ∧
    d * X.card = (outsideNeighbors G S.used X).card + ∑ x ∈ X, S.deg x

lemma critical_empty (S : ExtendableState G d m) : S.Critical ∅ := by
  simp [Critical, outsideNeighbors]

lemma sum_deg_le (S : ExtendableState G d m) (X : Finset V) :
    (∑ x ∈ X, S.deg x) ≤ d * X.card := by
  calc
    (∑ x ∈ X, S.deg x) ≤ ∑ _x ∈ X, d :=
      Finset.sum_le_sum fun x _ => S.deg_le x
    _ = d * X.card := by simp [Nat.mul_comm]

lemma critical_card_le_of_large_expansion (S : ExtendableState G d m)
    (hlarge : ∀ X : Finset V, m < X.card → X.card ≤ 2 * m →
      d * X.card + S.used.card + 1 ≤ (setNeighbors G X).card)
    {X : Finset V} (hX : S.Critical X) : X.card ≤ m := by
  by_contra hnot
  have hmX : m < X.card := Nat.lt_of_not_ge hnot
  have hNX : (setNeighbors G X).card ≤
      (outsideNeighbors G S.used X).card + S.used.card := by
    calc
      (setNeighbors G X).card ≤
          (outsideNeighbors G S.used X ∪ S.used).card := by
            apply card_le_card
            intro v hv
            by_cases hvu : v ∈ S.used
            · exact mem_union_right _ hvu
            · exact mem_union_left _ (mem_sdiff.mpr ⟨hv, hvu⟩)
      _ ≤ (outsideNeighbors G S.used X).card + S.used.card := card_union_le _ _
  have hext : (outsideNeighbors G S.used X).card ≤ d * X.card := by
    calc
      (outsideNeighbors G S.used X).card
          ≤ (outsideNeighbors G S.used X).card + ∑ x ∈ X, S.deg x := Nat.le_add_right _ _
      _ = d * X.card := hX.2.symm
  have := hlarge X hmX hX.1
  omega

lemma degreeSum_modular (f : V → ℕ) (X Y : Finset V) :
    (∑ x ∈ X ∩ Y, f x) + (∑ x ∈ X ∪ Y, f x) =
      (∑ x ∈ X, f x) + ∑ x ∈ Y, f x := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | @insert a X ha ih =>
      by_cases hay : a ∈ Y
      · simp [ha, hay, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · simp [ha, hay, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma critical_union (S : ExtendableState G d m)
    (hlarge : ∀ X : Finset V, m < X.card → X.card ≤ 2 * m →
      d * X.card + S.used.card + 1 ≤ (setNeighbors G X).card)
    {X Y : Finset V} (hX : S.Critical X) (hY : S.Critical Y) :
    S.Critical (X ∪ Y) := by
  have hXm : X.card ≤ m := S.critical_card_le_of_large_expansion hlarge hX
  have hYm : Y.card ≤ m := S.critical_card_le_of_large_expansion hlarge hY
  have hUcard : (X ∪ Y).card ≤ 2 * m := by
    calc (X ∪ Y).card ≤ X.card + Y.card := card_union_le _ _
         _ ≤ m + m := Nat.add_le_add hXm hYm
         _ = 2 * m := by omega
  have hIcard : (X ∩ Y).card ≤ 2 * m :=
    (card_le_card inter_subset_left).trans (hX.1)
  have hbalI := S.balance (X ∩ Y) hIcard
  have hbalU := S.balance (X ∪ Y) hUcard
  have hsub := outsideNeighbors_card_submodular G S.used X Y
  have hcardmod := card_union_add_card_inter X Y
  have hdegmod := degreeSum_modular S.deg X Y
  have hmulmod :
      d * (X ∪ Y).card + d * (X ∩ Y).card = d * X.card + d * Y.card := by
    rw [← Nat.mul_add, ← Nat.mul_add, hcardmod]
  have htotal :
      ((outsideNeighbors G S.used (X ∩ Y)).card + ∑ x ∈ X ∩ Y, S.deg x) +
          ((outsideNeighbors G S.used (X ∪ Y)).card + ∑ x ∈ X ∪ Y, S.deg x) ≤
        ((outsideNeighbors G S.used X).card + ∑ x ∈ X, S.deg x) +
          ((outsideNeighbors G S.used Y).card + ∑ x ∈ Y, S.deg x) := by
    omega
  refine ⟨hUcard, Nat.le_antisymm hbalU ?_⟩
  have hxEq := hX.2
  have hyEq := hY.2
  omega

lemma critical_biUnion (S : ExtendableState G d m)
    (hlarge : ∀ X : Finset V, m < X.card → X.card ≤ 2 * m →
      d * X.card + S.used.card + 1 ≤ (setNeighbors G X).card)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (X : ι → Finset V)
    (hcrit : ∀ i ∈ I, S.Critical (X i)) :
    S.Critical (I.biUnion X) := by
  induction I using Finset.induction_on with
  | empty => simpa using S.critical_empty
  | @insert i I hi ih =>
      rw [Finset.biUnion_insert]
      exact S.critical_union hlarge (hcrit i (mem_insert_self _ _))
        (ih fun j hj => hcrit j (mem_insert_of_mem hj))

def addLeafDeg (S : ExtendableState G d m) (s y : V) : V → ℕ :=
  fun v => S.deg v + (if v = s then 1 else 0) + (if v = y then 1 else 0)

lemma sum_addLeafDeg (S : ExtendableState G d m) (s y : V) (X : Finset V) :
    (∑ x ∈ X, S.addLeafDeg s y x) =
      (∑ x ∈ X, S.deg x) + (if s ∈ X then 1 else 0) + (if y ∈ X then 1 else 0) := by
  simp only [addLeafDeg, sum_add_distrib]
  simp [eq_comm]

lemma outsideNeighbors_insert_used (S : ExtendableState G d m) (y : V) (X : Finset V) :
    outsideNeighbors G (insert y S.used) X = (outsideNeighbors G S.used X).erase y := by
  simp [outsideNeighbors, sdiff_insert]

lemma card_outside_insert (S : ExtendableState G d m) (y : V) (X : Finset V) :
    (outsideNeighbors G (insert y S.used) X).card +
        (if y ∈ outsideNeighbors G S.used X then 1 else 0) =
      (outsideNeighbors G S.used X).card := by
  rw [S.outsideNeighbors_insert_used]
  by_cases hy : y ∈ outsideNeighbors G S.used X
  · rw [if_pos hy, card_erase_of_mem hy]
    have := card_pos.mpr ⟨y, hy⟩
    omega
  · simp [hy]

/-- The critical-set extension lemma. -/
lemma exists_add_leaf (S : ExtendableState G d m)
    (hm : 1 ≤ m) (hd : 1 ≤ d)
    (hlarge : ∀ X : Finset V, m < X.card → X.card ≤ 2 * m →
      d * X.card + S.used.card + 1 ≤ (setNeighbors G X).card)
    {s : V} (hs : s ∈ S.used) (hdeg : S.deg s < d) :
    ∃ y : V, y ∉ S.used ∧ G.Adj s y ∧
      ∃ S' : ExtendableState G d m,
        S'.used = insert y S.used ∧ S'.deg = S.addLeafDeg s y := by
  classical
  let Y := Finset.univ.filter (G.Adj s) \ S.used
  have hYcard : d - S.deg s ≤ Y.card := by
    have hb := S.balance {s} (by simp; omega)
    have hsum : (∑ x ∈ ({s} : Finset V), S.deg x) = S.deg s := by simp
    have hout : outsideNeighbors G S.used {s} = Y := by
      ext v
      simp [outsideNeighbors, setNeighbors, Y]
    rw [hsum, hout] at hb
    simp at hb
    omega
  have hYnonempty : Y.Nonempty := by
    have : 1 ≤ d - S.deg s := by omega
    exact card_pos.mp (lt_of_lt_of_le this hYcard)
  let badFamily : Finset (Finset V) :=
    Finset.univ.filter fun X => S.Critical X ∧ s ∉ X
  let Xstar : Finset V := badFamily.biUnion id
  have hstarcrit : S.Critical Xstar := by
    apply S.critical_biUnion hlarge
    intro X hX
    exact (by simpa [badFamily] using hX : S.Critical X ∧ s ∉ X).1
  have hstarsmall : Xstar.card ≤ m :=
    S.critical_card_le_of_large_expansion hlarge hstarcrit
  have hsnotstar : s ∉ Xstar := by
    simp only [Xstar, mem_biUnion]
    rintro ⟨X, hX, hsX⟩
    exact (by simpa [badFamily] using hX : S.Critical X ∧ s ∉ X).2 hsX
  have hnotcover : ¬(Y ⊆ setNeighbors G Xstar) := by
    intro hcover
    have houtEq : outsideNeighbors G S.used (insert s Xstar) =
        outsideNeighbors G S.used Xstar := by
      ext v
      rw [show insert s Xstar = {s} ∪ Xstar by simp,
        outsideNeighbors_union]
      constructor
      · intro hv
        rcases mem_union.mp hv with hv | hv
        · have hvY : v ∈ Y := by
            simpa [outsideNeighbors, setNeighbors, Y] using hv
          have hvY' := mem_sdiff.mp hvY
          have hvN := hcover hvY
          exact mem_sdiff.mpr ⟨hvN, hvY'.2⟩
        · exact hv
      · exact mem_union_right _
    have hcard : (insert s Xstar).card ≤ 2 * m := by
      rw [card_insert_of_notMem hsnotstar]
      omega
    have hbal := S.balance (insert s Xstar) hcard
    have hsumInsert : (∑ x ∈ insert s Xstar, S.deg x) =
        S.deg s + ∑ x ∈ Xstar, S.deg x := by
      rw [sum_insert hsnotstar]
    rw [card_insert_of_notMem hsnotstar, houtEq, hsumInsert] at hbal
    rw [Nat.mul_add] at hbal
    simp at hbal
    have hcritEq := hstarcrit.2
    omega
  have hex : ∃ y ∈ Y, y ∉ setNeighbors G Xstar := by
    simpa [Finset.not_subset] using hnotcover
  obtain ⟨y, hyY, hynstar⟩ := hex
  have hyY' := mem_sdiff.mp hyY
  have hyused : y ∉ S.used := hyY'.2
  have hadj : G.Adj s y := by simpa [Y] using hyY'.1
  have hys : y ≠ s := by
    intro h
    have hloop : G.Adj y y := by simpa [h] using hadj
    exact G.loopless.irrefl y hloop
  let deg' := S.addLeafDeg s y
  have hdegOff : ∀ ⦃v⦄, v ∉ insert y S.used → deg' v = 0 := by
    intro v hv
    have hvu : v ∉ S.used := fun h => hv (mem_insert_of_mem h)
    have hvs : v ≠ s := fun h => hv (h ▸ mem_insert_of_mem hs)
    have hvy : v ≠ y := by
      intro h
      subst v
      exact hv (mem_insert_self y _)
    simp [deg', addLeafDeg, S.deg_off hvu, hvs, hvy]
  have hdegLe : ∀ v, deg' v ≤ d := by
    intro v
    by_cases hvs : v = s
    · subst v
      simp [deg', addLeafDeg, hys, hys.symm]
      omega
    · by_cases hvy : v = y
      · subst v
        have hydeg : S.deg y = 0 := S.deg_off hyused
        simpa [deg', addLeafDeg, hydeg, hys] using hd
      · simpa [deg', addLeafDeg, hvs, hvy] using S.deg_le v
  have hbalance : ∀ X : Finset V, X.card ≤ 2 * m →
      d * X.card ≤ (outsideNeighbors G (insert y S.used) X).card +
        ∑ x ∈ X, deg' x := by
    intro X hXcard
    have hold := S.balance X hXcard
    have hcardEq := S.card_outside_insert y X
    dsimp [deg']
    rw [S.sum_addLeafDeg]
    by_cases hyN : y ∈ outsideNeighbors G S.used X
    · have hyNX : y ∈ setNeighbors G X := (mem_sdiff.mp hyN).1
      by_cases hyX : y ∈ X
      · simp [hyN, hyX] at hcardEq ⊢
        omega
      · by_cases hsX : s ∈ X
        · simp [hyN, hsX, hyX] at hcardEq ⊢
          omega
        · have hnotcrit : ¬S.Critical X := by
            intro hc
            have hmemBad : X ∈ badFamily := by simp [badFamily, hc, hsX]
            have hsub : X ⊆ Xstar := by
              intro v hv
              exact mem_biUnion.mpr ⟨X, hmemBad, hv⟩
            exact hynstar (setNeighbors_mono hsub hyNX)
          have hstrict : d * X.card <
              (outsideNeighbors G S.used X).card + ∑ x ∈ X, S.deg x := by
            exact lt_of_le_of_ne hold fun heq => hnotcrit ⟨hXcard, heq⟩
          simp [hyN, hsX, hyX] at hcardEq ⊢
          omega
    · simp [hyN] at hcardEq
      omega
  let S' : ExtendableState G d m :=
    { used := insert y S.used
      deg := deg'
      deg_off := hdegOff
      deg_le := hdegLe
      balance := hbalance }
  exact ⟨y, hyused, hadj, S', rfl, rfl⟩

end ExtendableState

end Erdos720
