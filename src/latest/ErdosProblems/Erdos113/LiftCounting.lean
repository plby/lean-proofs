import ErdosProblems.Erdos113.Alternating56

open scoped BigOperators

namespace Erdos113LiftCounting

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Index := Fin 28

def allChoices (S : Index → Finset V) : Finset (Index → V) :=
  Fintype.piFinset S

@[simp] lemma mem_allChoices {S : Index → Finset V} {y : Index → V} :
    y ∈ allChoices S ↔ ∀ i, y i ∈ S i := by
  simp [allChoices]

def duplicateEvent (S : Index → Finset V) (p q : Index) :
    Finset (Index → V) :=
  (allChoices S).filter fun y ↦ y p = y q

def forbiddenEvent (S : Index → Finset V) (X : Finset V) (p : Index) :
    Finset (Index → V) :=
  (allChoices S).filter fun y ↦ y p ∈ X

def indexPairs : Finset (Index × Index) :=
  Finset.univ.filter fun pq ↦ pq.1 ≠ pq.2

def duplicateBad (S : Index → Finset V) : Finset (Index → V) :=
  indexPairs.biUnion fun pq ↦ duplicateEvent S pq.1 pq.2

def forbiddenBad (S : Index → Finset V) (X : Finset V) :
    Finset (Index → V) :=
  Finset.univ.biUnion fun p ↦ forbiddenEvent S X p

def validChoices (S : Index → Finset V) (X : Finset V) :
    Finset (Index → V) :=
  allChoices S \ (duplicateBad S ∪ forbiddenBad S X)

@[simp] lemma mem_duplicateEvent {S : Index → Finset V} {p q : Index}
    {y : Index → V} :
    y ∈ duplicateEvent S p q ↔ (∀ i, y i ∈ S i) ∧ y p = y q := by
  simp [duplicateEvent]

@[simp] lemma mem_forbiddenEvent {S : Index → Finset V} {X : Finset V}
    {p : Index} {y : Index → V} :
    y ∈ forbiddenEvent S X p ↔ (∀ i, y i ∈ S i) ∧ y p ∈ X := by
  simp [forbiddenEvent]

@[simp] lemma mem_indexPairs {p q : Index} : (p, q) ∈ indexPairs ↔ p ≠ q := by
  simp [indexPairs]

lemma card_indexPairs_le : indexPairs.card ≤ 28 ^ 2 := by
  calc
    indexPairs.card ≤ (Finset.univ : Finset (Index × Index)).card :=
      Finset.card_filter_le _ _
    _ = 28 ^ 2 := by simp [pow_two]

private def restrictAway (p : Index) (y : Index → V) : Fin 27 → V :=
  fun i ↦ y (p.succAbove i)

lemma duplicateEvent_card_le (S : Index → Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (p q : Index) (hpq : p ≠ q) :
    (duplicateEvent S p q).card ≤ (2 * s) ^ 27 := by
  let T : Finset (Fin 27 → V) :=
    Fintype.piFinset fun i ↦ S (p.succAbove i)
  calc
    (duplicateEvent S p q).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn (restrictAway p)
      · intro y hy
        have hyall := (mem_duplicateEvent.mp hy).1
        change restrictAway p y ∈ T
        simp only [T, Fintype.mem_piFinset]
        intro i
        exact hyall (p.succAbove i)
      · intro y hy z hz hyz
        have hyeq := (mem_duplicateEvent.mp hy).2
        have hzeq := (mem_duplicateEvent.mp hz).2
        funext i
        by_cases hip : i = p
        · subst i
          have hqp : q ≠ p := hpq.symm
          obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hqp
          have hcoord := congrFun hyz k
          change y (p.succAbove k) = z (p.succAbove k) at hcoord
          rw [hk] at hcoord
          exact hyeq.trans (hcoord.trans hzeq.symm)
        · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hip
          have hcoord := congrFun hyz k
          change y (p.succAbove k) = z (p.succAbove k) at hcoord
          simpa [hk] using hcoord
    _ ≤ (2 * s) ^ 27 := by
      rw [show T.card = ∏ i : Fin 27, (S (p.succAbove i)).card by
        exact Fintype.card_piFinset _]
      calc
        ∏ i : Fin 27, (S (p.succAbove i)).card ≤
            ∏ _i : Fin 27, (2 * s) := by
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hupper _
        _ = (2 * s) ^ 27 := by simp

lemma forbiddenEvent_card_le (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (p : Index) :
    (forbiddenEvent S X p).card ≤ X.card * (2 * s) ^ 27 := by
  let T : Finset (Fin 27 → V) :=
    Fintype.piFinset fun i ↦ S (p.succAbove i)
  let U : Finset (V × (Fin 27 → V)) := X ×ˢ T
  let f : (Index → V) → V × (Fin 27 → V) := fun y ↦ (y p, restrictAway p y)
  calc
    (forbiddenEvent S X p).card ≤ U.card := by
      apply Finset.card_le_card_of_injOn f
      · intro y hy
        have hydata := mem_forbiddenEvent.mp hy
        change f y ∈ U
        rw [Finset.mem_product]
        refine ⟨hydata.2, ?_⟩
        simp only [T, Fintype.mem_piFinset]
        intro i
        exact hydata.1 (p.succAbove i)
      · intro y _hy z _hz hyz
        funext i
        by_cases hip : i = p
        · subst i
          exact congrArg Prod.fst hyz
        · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hip
          have hcoord := congrFun (congrArg Prod.snd hyz) k
          change y (p.succAbove k) = z (p.succAbove k) at hcoord
          simpa [hk] using hcoord
    _ ≤ X.card * (2 * s) ^ 27 := by
      rw [show U.card = X.card * T.card by simp [U]]
      gcongr
      rw [show T.card = ∏ i : Fin 27, (S (p.succAbove i)).card by
        exact Fintype.card_piFinset _]
      calc
        ∏ i : Fin 27, (S (p.succAbove i)).card ≤
            ∏ _i : Fin 27, (2 * s) := by
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hupper _
        _ = (2 * s) ^ 27 := by simp

lemma duplicateBad_card_le (S : Index → Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) :
    (duplicateBad S).card ≤ 28 ^ 2 * (2 * s) ^ 27 := by
  calc
    (duplicateBad S).card ≤
        ∑ pq ∈ indexPairs, (duplicateEvent S pq.1 pq.2).card := by
      exact Finset.card_biUnion_le
    _ ≤ indexPairs.card * (2 * s) ^ 27 := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul indexPairs
        (fun pq ↦ (duplicateEvent S pq.1 pq.2).card) ((2 * s) ^ 27)
        (fun pq hpq ↦ duplicateEvent_card_le S s hupper pq.1 pq.2
          (mem_indexPairs.mp hpq))
    _ ≤ 28 ^ 2 * (2 * s) ^ 27 := by
      gcongr
      exact card_indexPairs_le

lemma forbiddenBad_card_le (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (hX : X.card ≤ 28) :
    (forbiddenBad S X).card ≤ 28 ^ 2 * (2 * s) ^ 27 := by
  calc
    (forbiddenBad S X).card ≤
        ∑ p : Index, (forbiddenEvent S X p).card := by
      simpa [forbiddenBad] using
        (Finset.card_biUnion_le (s := (Finset.univ : Finset Index))
          (t := fun p ↦ forbiddenEvent S X p))
    _ ≤ ∑ _p : Index, (28 * (2 * s) ^ 27) := by
      gcongr with p
      exact (forbiddenEvent_card_le S X s hupper p).trans (by gcongr)
    _ = 28 ^ 2 * (2 * s) ^ 27 := by simp [pow_two]; ring

lemma bad_card_le (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hupper : ∀ i, (S i).card ≤ 2 * s) (hX : X.card ≤ 28) :
    (duplicateBad S ∪ forbiddenBad S X).card ≤
      1568 * (2 * s) ^ 27 := by
  calc
    (duplicateBad S ∪ forbiddenBad S X).card ≤
        (duplicateBad S).card + (forbiddenBad S X).card :=
      Finset.card_union_le _ _
    _ ≤ 28 ^ 2 * (2 * s) ^ 27 + 28 ^ 2 * (2 * s) ^ 27 :=
      Nat.add_le_add (duplicateBad_card_le S s hupper)
        (forbiddenBad_card_le S X s hupper hX)
    _ = 1568 * (2 * s) ^ 27 := by ring

lemma allChoices_card_lower (S : Index → Finset V) (s : ℕ)
    (hlower : ∀ i, s ≤ (S i).card) :
    s ^ 28 ≤ (allChoices S).card := by
  rw [show (allChoices S).card = ∏ i : Index, (S i).card by
    exact Fintype.card_piFinset _]
  calc
    s ^ 28 = ∏ _i : Index, s := by simp
    _ ≤ ∏ i : Index, (S i).card := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hlower i

lemma validChoices_half_lower (S : Index → Finset V) (X : Finset V) (s : ℕ)
    (hlower : ∀ i, s ≤ (S i).card)
    (hupper : ∀ i, (S i).card ≤ 2 * s)
    (hX : X.card ≤ 28)
    (hs : 3136 * 2 ^ 27 ≤ s) :
    s ^ 28 ≤ 2 * (validChoices S X).card := by
  let B := duplicateBad S ∪ forbiddenBad S X
  have hall := allChoices_card_lower S s hlower
  have hsplit : (allChoices S).card ≤ (validChoices S X).card + B.card := by
    simpa [validChoices, B, add_comm] using
      (Finset.card_le_card_sdiff_add_card (s := allChoices S) (t := B))
  have hbad : B.card ≤ 1568 * (2 * s) ^ 27 := by
    exact bad_card_le S X s hupper hX
  have hnum : 2 * (1568 * (2 * s) ^ 27) ≤ s ^ 28 := by
    calc
      2 * (1568 * (2 * s) ^ 27) = (3136 * 2 ^ 27) * s ^ 27 := by ring
      _ ≤ s * s ^ 27 := Nat.mul_le_mul_right (s ^ 27) hs
      _ = s ^ 28 := by ring
  omega

lemma mem_validChoices {S : Index → Finset V} {X : Finset V}
    {y : Index → V} :
    y ∈ validChoices S X ↔
      (∀ i, y i ∈ S i) ∧ Function.Injective y ∧ ∀ i, y i ∉ X := by
  constructor
  · intro hy
    have hydata := Finset.mem_sdiff.mp hy
    have hall := mem_allChoices.mp hydata.1
    refine ⟨hall, ?_, ?_⟩
    · intro p q hpq
      by_contra hpne
      apply hydata.2
      rw [Finset.mem_union]
      left
      rw [duplicateBad, Finset.mem_biUnion]
      exact ⟨(p, q), mem_indexPairs.mpr hpne, mem_duplicateEvent.mpr ⟨hall, hpq⟩⟩
    · intro p hpX
      apply hydata.2
      rw [Finset.mem_union]
      right
      rw [forbiddenBad, Finset.mem_biUnion]
      exact ⟨p, Finset.mem_univ _, mem_forbiddenEvent.mpr ⟨hall, hpX⟩⟩
  · rintro ⟨hall, hinj, hX⟩
    rw [validChoices, Finset.mem_sdiff]
    refine ⟨mem_allChoices.mpr hall, ?_⟩
    rw [Finset.mem_union]
    push_neg
    constructor
    · intro hdup
      rw [duplicateBad, Finset.mem_biUnion] at hdup
      obtain ⟨pq, hpq, hy⟩ := hdup
      exact (mem_indexPairs.mp hpq) (hinj (mem_duplicateEvent.mp hy).2)
    · intro hforbid
      rw [forbiddenBad, Finset.mem_biUnion] at hforbid
      obtain ⟨p, _hp, hy⟩ := hforbid
      exact hX p (mem_forbiddenEvent.mp hy).2

end

end Erdos113LiftCounting
