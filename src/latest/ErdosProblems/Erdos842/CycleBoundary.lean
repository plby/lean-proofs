import ErdosProblems.Erdos842.Coefficient

/-!
# Solving prescribed alternating boundaries on a finite directed cycle

The construction uses prefix parity.  Starting from a base bit, crossing a
used endpoint flips the selected/unselected state of the outgoing cycle edge.
An even number of used endpoints makes the state consistent at the wraparound.
-/

open scoped BigOperators

namespace Erdos842.CycleBoundary

/-- Canonical predecessor on the nonempty cyclic type `Fin m`. -/
noncomputable def finCyclePred {m : ℕ} (hm : 0 < m) : Equiv.Perm (Fin m) := by
  letI : NeZero m := ⟨hm.ne'⟩
  exact Equiv.subRight 1

/-- The distinguished zero vertex, without requiring a global `NeZero m` instance. -/
def finZero {m : ℕ} (hm : 0 < m) : Fin m := ⟨0, hm⟩

@[simp] theorem finZero_val {m : ℕ} (hm : 0 < m) : (finZero hm).val = 0 := rfl

/-- Away from zero, the canonical predecessor has the expected natural value. -/
theorem finCyclePred_val_of_ne_zero {m : ℕ} (hm : 0 < m) (v : Fin m)
    (hv : v ≠ finZero hm) :
    (finCyclePred hm v).val = v.val - 1 := by
  let : NeZero m := ⟨hm.ne'⟩
  have hv' : v ≠ (0 : Fin m) := by
    simpa [finZero] using hv
  simp only [finCyclePred, Equiv.subRight_apply]
  exact Fin.val_sub_one_of_ne_zero hv'

/-- Number of used endpoints up to and including `v` in the linear order on `Fin m`. -/
def prefixCount {m : ℕ} (used : Finset (Fin m)) (v : Fin m) : ℕ :=
  (used.filter fun u ↦ u ≤ v).card

/-- Encode a Boolean base bit as its natural parity value. -/
def boolNat (base : Bool) : ℕ := if base then 1 else 0

@[simp] theorem boolNat_false : boolNat false = 0 := rfl
@[simp] theorem boolNat_true : boolNat true = 1 := rfl

/-- The edge at `v` is selected exactly when the prefix parity equals the base bit. -/
noncomputable def selection {m : ℕ} (used : Finset (Fin m)) (base : Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v ↦ prefixCount used v % 2 = boolNat base

@[simp] theorem mem_selection {m : ℕ} (used : Finset (Fin m)) (base : Bool) (v : Fin m) :
    v ∈ selection used base ↔ prefixCount used v % 2 = boolNat base := by
  classical
  simp [selection]

/-- Prefix count at the final vertex is the total cardinality. -/
theorem prefixCount_last {k : ℕ} (used : Finset (Fin (k + 1))) :
    prefixCount used (Fin.last k) = used.card := by
  unfold prefixCount
  congr 1
  ext u
  simp only [Finset.mem_filter]
  constructor
  · exact fun hu ↦ hu.1
  · intro hu
    exact ⟨hu, Fin.le_last u⟩

/-- Before a nonzero vertex, the prefix gains exactly that vertex when it is used. -/
theorem prefixCount_eq_pred_add_indicator {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (v : Fin m) (hv : v ≠ finZero hm) :
    prefixCount used v = prefixCount used (finCyclePred hm v) + if v ∈ used then 1 else 0 := by
  classical
  have hpval : (finCyclePred hm v).val = v.val - 1 := by
    exact finCyclePred_val_of_ne_zero hm v hv
  by_cases hvu : v ∈ used
  · have heq : (used.filter fun u ↦ u ≤ v) =
        insert v (used.filter fun u ↦ u ≤ finCyclePred hm v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hu, huv⟩
        by_cases huv' : u = v
        · exact Or.inl huv'
        · right
          refine ⟨hu, ?_⟩
          apply Fin.le_iff_val_le_val.mpr
          rw [hpval]
          have hlt : u.val < v.val := lt_of_le_of_ne huv (by simpa [Fin.ext_iff] using huv')
          omega
      · rintro (rfl | ⟨hu, huPred⟩)
        · exact ⟨hvu, le_rfl⟩
        · refine ⟨hu, ?_⟩
          apply Fin.le_iff_val_le_val.mpr
          have := Fin.le_iff_val_le_val.mp huPred
          rw [hpval] at this
          omega
    rw [prefixCount, prefixCount, heq, Finset.card_insert_of_notMem]
    · simp [hvu]
    · simp only [Finset.mem_filter]
      push Not
      intro _
      apply Fin.lt_iff_val_lt_val.mpr
      rw [hpval]
      have hvne : v.val ≠ 0 := by
        intro h
        apply hv
        apply Fin.ext
        simpa [finZero] using h
      have hvpos : 0 < v.val := Nat.pos_of_ne_zero hvne
      omega
  · have heq : (used.filter fun u ↦ u ≤ v) =
        used.filter fun u ↦ u ≤ finCyclePred hm v := by
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hu, huv⟩
        refine ⟨hu, ?_⟩
        apply Fin.le_iff_val_le_val.mpr
        rw [hpval]
        have hne : u ≠ v := fun h ↦ hvu (h ▸ hu)
        have hlt : u.val < v.val := lt_of_le_of_ne huv (by simpa [Fin.ext_iff] using hne)
        omega
      · rintro ⟨hu, huPred⟩
        refine ⟨hu, ?_⟩
        apply Fin.le_iff_val_le_val.mpr
        have := Fin.le_iff_val_le_val.mp huPred
        rw [hpval] at this
        omega
    simp [prefixCount, heq, hvu]

/-- At zero, the predecessor prefix is the total cardinality and the zero prefix
is precisely the indicator of membership of zero. -/
theorem prefixCount_zero_and_pred {m : ℕ} (hm : 0 < m) (used : Finset (Fin m)) :
    prefixCount used (finZero hm) = (if finZero hm ∈ used then 1 else 0) ∧
      prefixCount used (finCyclePred hm (finZero hm)) = used.card := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  constructor
  · unfold prefixCount
    have heq : ((used.filter fun u ↦ u ≤ finZero (by omega : 0 < k + 1))) =
        if finZero (by omega : 0 < k + 1) ∈ used
          then {finZero (by omega : 0 < k + 1)} else ∅ := by
      ext u
      by_cases hz : finZero (by omega : 0 < k + 1) ∈ used
      · simp only [hz, ↓reduceIte, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hu, huv⟩
          apply Fin.ext
          have := Fin.le_iff_val_le_val.mp huv
          simp only [finZero_val] at this ⊢
          omega
        · rintro rfl
          exact ⟨hz, le_rfl⟩
      · simp only [hz, ↓reduceIte, Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hu, huv⟩
        apply hz
        have huv0 : u = finZero (by omega : 0 < k + 1) := by
          apply Fin.ext
          have := Fin.le_iff_val_le_val.mp huv
          simp only [finZero_val] at this ⊢
          omega
        simpa [huv0] using hu
    rw [heq]
    split <;> simp
  · have hpred : finCyclePred (by omega : 0 < k + 1)
        (finZero (by omega : 0 < k + 1)) = Fin.last k := by
      let : NeZero (k + 1) := ⟨by omega⟩
      ext
      simp [finCyclePred, finZero, Fin.last]
    rw [hpred]
    exact prefixCount_last used

/-- Adding one toggles parity relative to either Boolean base. -/
theorem add_one_parity_eq_boolNat_iff_not (a : ℕ) (base : Bool) :
    (a + 1) % 2 = boolNat base ↔ ¬a % 2 = boolNat base := by
  cases base <;> simp [boolNat] <;> omega

/-- A number of parity zero does not change the parity test. -/
theorem add_even_parity_eq_boolNat_iff (a e : ℕ) (he : e % 2 = 0) (base : Bool) :
    (a + e) % 2 = boolNat base ↔ a % 2 = boolNat base := by
  cases base <;> simp [boolNat] <;> omega

/-- Flipping the base bit complements the selected cycle edges. -/
theorem selection_not_base {m : ℕ} (used : Finset (Fin m)) (base : Bool) :
    selection used (!base) = Finset.univ \ selection used base := by
  classical
  ext v
  rw [mem_selection]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_selection]
  have hlt : prefixCount used v % 2 < 2 := Nat.mod_lt _ (by omega)
  cases base <;> simp only [Bool.not_false, Bool.not_true, boolNat_false, boolNat_true] <;>
    omega

/-- Across a used endpoint selection toggles; across an unused endpoint it is
unchanged.  Even cardinality is exactly what makes the assertion true at the
cyclic wraparound. -/
theorem mem_finCyclePred_selection_iff {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (base : Bool) (heven : Even used.card) (v : Fin m) :
    finCyclePred hm v ∈ selection used base ↔
      if v ∈ used then v ∉ selection used base else v ∈ selection used base := by
  classical
  by_cases hv0 : v = finZero hm
  · subst v
    obtain ⟨hzero, hpred⟩ := prefixCount_zero_and_pred hm used
    obtain ⟨q, hcard⟩ := heven
    rw [mem_selection, mem_selection, hpred, hzero, hcard]
    by_cases hused : finZero hm ∈ used <;>
      cases base <;> simp [hused, boolNat] <;> omega
  · rw [mem_selection, mem_selection]
    rw [prefixCount_eq_pred_add_indicator hm used v hv0]
    by_cases hused : v ∈ used
    · simp only [hused, if_pos]
      have ht := add_one_parity_eq_boolNat_iff_not
        (prefixCount used (finCyclePred hm v)) base
      tauto
    · simp [hused]

/-- The prescribed alternating sign at a used endpoint.  The first used
endpoint has sign determined by `base`, and signs alternate in increasing
order because `prefixCount` increases by one at each used endpoint. -/
def alternatingBoundary {m : ℕ} (used : Finset (Fin m)) (base : Bool) (v : Fin m) : ℤ :=
  if v ∈ used then
    if prefixCount used v % 2 = boolNat base then -1 else 1
  else 0

/-- Exact evaluation of `Coefficient.cycleBoundary` for the canonical
prefix-parity solution. -/
theorem cycleBoundary_selection {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (base : Bool) (heven : Even used.card) (v : Fin m) :
    Coefficient.cycleBoundary (finCyclePred hm) (selection used base) v =
      alternatingBoundary used base v := by
  classical
  have hpred := mem_finCyclePred_selection_iff hm used base heven v
  by_cases hused : v ∈ used
  · simp only [hused, if_pos] at hpred
    by_cases hcur : v ∈ selection used base
    · have hpred' : finCyclePred hm v ∉ selection used base := by
        simpa [hcur] using hpred
      have hpar : prefixCount used v % 2 = boolNat base :=
        (mem_selection used base v).mp hcur
      simp [Coefficient.cycleBoundary, alternatingBoundary, hused, hcur, hpred', hpar]
    · have hpred' : finCyclePred hm v ∈ selection used base := by
        exact hpred.mpr hcur
      have hpar : ¬prefixCount used v % 2 = boolNat base := by
        intro hp
        exact hcur ((mem_selection used base v).mpr hp)
      simp [Coefficient.cycleBoundary, alternatingBoundary, hused, hcur, hpred', hpar]
  · simp only [hused, if_false] at hpred
    by_cases hcur : v ∈ selection used base
    · have hpred' : finCyclePred hm v ∈ selection used base := hpred.mpr hcur
      simp [Coefficient.cycleBoundary, alternatingBoundary, hused, hcur, hpred']
    · have hpred' : finCyclePred hm v ∉ selection used base := by
        exact fun hp ↦ hcur (hpred.mp hp)
      simp [Coefficient.cycleBoundary, alternatingBoundary, hused, hcur, hpred']

/-- Off the prescribed endpoint set the constructed boundary vanishes. -/
theorem cycleBoundary_selection_of_notMem {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (base : Bool) (heven : Even used.card)
    {v : Fin m} (hv : v ∉ used) :
    Coefficient.cycleBoundary (finCyclePred hm) (selection used base) v = 0 := by
  rw [cycleBoundary_selection hm used base heven v]
  simp [alternatingBoundary, hv]

/-- At a prescribed endpoint the constructed boundary is `-1` precisely when
the prefix parity agrees with the base bit, and is `1` otherwise. -/
theorem cycleBoundary_selection_of_mem {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (base : Bool) (heven : Even used.card)
    {v : Fin m} (hv : v ∈ used) :
    Coefficient.cycleBoundary (finCyclePred hm) (selection used base) v =
      if prefixCount used v % 2 = boolNat base then -1 else 1 := by
  rw [cycleBoundary_selection hm used base heven v]
  simp [alternatingBoundary, hv]

/-- Flipping the base reverses every cyclic boundary value. -/
theorem cycleBoundary_selection_not_base {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (base : Bool) (v : Fin m) :
    Coefficient.cycleBoundary (finCyclePred hm) (selection used (!base)) v =
      -Coefficient.cycleBoundary (finCyclePred hm) (selection used base) v := by
  classical
  rw [selection_not_base]
  simp only [Coefficient.cycleBoundary, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases hp : finCyclePred hm v ∈ selection used base <;>
    by_cases hv : v ∈ selection used base <;> simp [hp, hv]

/-- Every vertex can be reached from every other vertex by iterating the
canonical predecessor. -/
theorem finCyclePred_transitive {m : ℕ} (hm : 0 < m) (u v : Fin m) :
    ∃ k : ℕ, (finCyclePred hm ^ k) u = v := by
  let : NeZero m := ⟨hm.ne'⟩
  refine ⟨(u - v).val, ?_⟩
  have hpow : ∀ k : ℕ, (finCyclePred hm ^ k) u = u - Fin.ofNat m k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        simp only [finCyclePred, Equiv.subRight_apply]
        rw [show Fin.ofNat m (k + 1) = Fin.ofNat m k + 1 by
          apply Fin.ext
          change (k + 1) % m = (k % m + 1 % m) % m
          exact Nat.add_mod k 1 m]
        abel
  rw [hpow]
  have hcoe : Fin.ofNat m (u - v).val = u - v := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (u - v).isLt]
  rw [hcoe]
  abel

/-- The prefix-parity construction is the unique cycle-edge set realizing its
nonzero alternating boundary. -/
theorem selection_unique {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (base : Bool) (heven : Even used.card)
    (hused : used.Nonempty) {T : Finset (Fin m)}
    (hboundary : ∀ v,
      Coefficient.cycleBoundary (finCyclePred hm) T v = alternatingBoundary used base v) :
    T = selection used base := by
  symm
  apply Coefficient.unique_of_cycleBoundary_eq_of_nonzero
    (pred := finCyclePred hm)
    (htrans := finCyclePred_transitive hm)
  · obtain ⟨v, hv⟩ := hused
    refine ⟨v, ?_⟩
    rw [cycleBoundary_selection hm used base heven v]
    by_cases hpar : prefixCount used v % 2 = boolNat base <;>
      simp [alternatingBoundary, hv, hpar]
  · intro v
    rw [cycleBoundary_selection hm used base heven v]
    exact (hboundary v).symm

/-- Existence and uniqueness of a cycle-edge selection with the prescribed
alternating boundary. -/
theorem exists_unique_selection {m : ℕ} (hm : 0 < m)
    (used : Finset (Fin m)) (heven : Even used.card) (hused : used.Nonempty)
    (base : Bool) :
    ∃! C : Finset (Fin m), ∀ v,
      Coefficient.cycleBoundary (finCyclePred hm) C v = alternatingBoundary used base v := by
  refine ⟨selection used base, cycleBoundary_selection hm used base heven, ?_⟩
  intro T hT
  exact selection_unique hm used base heven hused hT

end Erdos842.CycleBoundary
