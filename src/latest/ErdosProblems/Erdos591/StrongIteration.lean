import ErdosProblems.Erdos590

open Cardinal Ordinal

namespace Erdos591.StrongIteration

/-!
An abstract form of the fusion (or ``strong iteration'') part of the
Erdos--Milner argument.  The difficult one-step thinning argument is
isolated in `StepOracle`.  This file proves that such steps can be fused
along a countable well-order `B`, producing a blue-independent copy of the
lexicographic sum of `omega` over `B`.
-/

variable {B Y X : Type}

/-- A family of mutually separated, full `Y`-blocks in `X`. -/
structure BlockFamily (B Y X : Type) [LinearOrder B] [LinearOrder Y]
    [LinearOrder X] where
  embedding : B → Y ↪o X
  separated : ∀ {b c : B}, b < c → ∀ y z,
    embedding b y < embedding c z

/-- The data required from one fixed-set reindexing step.

The new family lies blockwise inside the old family after the order
reindexing `reindex`; every point of it is non-blue adjacent to `point`.
The fixed-set condition is what makes comparisons with all indices already
used by the fusion stable.  The final field is the same-block tail
condition needed when an index is revisited. -/
structure StepResult [LinearOrder B] [LinearOrder Y] [LinearOrder X]
    (blue : SimpleGraph X) (A : BlockFamily B Y X)
    (F : Finset B) (mu : B) where
  point : X
  reindex : B ↪o B
  fixes : ∀ b ∈ F, reindex b = b
  point_mem : point ∈ Set.range (A.embedding mu)
  next : BlockFamily B Y X
  next_sub : ∀ b y, ∃ z, next.embedding b y = A.embedding (reindex b) z
  not_adj : ∀ b y, ¬ blue.Adj point (next.embedding b y)
  point_below : ∀ y, point < next.embedding mu y

/-- The only combinatorial input to the fusion. -/
def StepOracle [LinearOrder B] [LinearOrder Y] [LinearOrder X]
    (blue : SimpleGraph X) : Prop :=
  ∀ (A : BlockFamily B Y X) (F : Finset B) (mu : B), mu ∈ F →
    Nonempty (StepResult blue A F mu)

section Schedule

variable [LinearOrder B] [Countable B] [Nonempty B]

/-- A chosen enumeration of a nonempty countable type. -/
noncomputable def enum : ℕ → B :=
  Classical.choose (exists_surjective_nat B)

theorem enum_surjective : Function.Surjective (enum : ℕ → B) :=
  Classical.choose_spec (exists_surjective_nat B)

/-- A chosen right inverse to `enum`. -/
noncomputable def code (b : B) : ℕ :=
  Classical.choose (enum_surjective b)

@[simp] theorem enum_code (b : B) : enum (code b) = b :=
  Classical.choose_spec (enum_surjective b)

theorem code_injective : Function.Injective (code : B → ℕ) := by
  intro b c h
  rw [← enum_code b, ← enum_code c, h]

/-- Stage `n` uses the first coordinate of the unpaired natural number. -/
noncomputable def index (n : ℕ) : B := enum n.unpair.1

/-- The finite set of all indices used through stage `n`. -/
noncomputable def past (n : ℕ) : Finset B :=
  (Finset.range (n + 1)).image index

theorem index_mem_past (n : ℕ) : index n ∈ (past n : Finset B) := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩

theorem index_mem_past_of_le {i n : ℕ} (hin : i ≤ n) :
    index i ∈ (past n : Finset B) := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hin), rfl⟩

/-- Stage at which the `k`th visit to `b` occurs. -/
noncomputable def occurrence (b : B) (k : ℕ) : ℕ :=
  Nat.pair (code b) k

theorem occurrence_strictMono (b : B) : StrictMono (occurrence b) := by
  intro k l hkl
  exact Nat.pair_lt_pair_right _ hkl

@[simp] theorem index_occurrence (b : B) (k : ℕ) :
    index (occurrence b k) = b := by
  simp [index, occurrence]

theorem occurrence_injective :
    Function.Injective (fun q : B × ℕ ↦ occurrence q.1 q.2) := by
  rintro ⟨b, k⟩ ⟨c, l⟩ h
  simp only [occurrence, Nat.pair_eq_pair] at h
  exact Prod.ext (code_injective h.1) h.2

end Schedule

section Fusion

variable [LinearOrder B] [WellFoundedLT B] [Countable B] [Nonempty B]
variable [LinearOrder Y] [Nonempty Y]
variable [LinearOrder X]
variable (blue : SimpleGraph X) (oracle : StepOracle (B := B) (Y := Y) blue)
variable (start : BlockFamily B Y X)

/-- The chosen step at a particular stage and for a particular current
family. -/
noncomputable def stepChoice (A : BlockFamily B Y X) (n : ℕ) :
    StepResult blue A (past n) (index n) :=
  Classical.choice (oracle A (past n) (index n) (index_mem_past n))

/-- The descending sequence of reservoir families. -/
noncomputable def familySeq : ℕ → BlockFamily B Y X
  | 0 => start
  | n + 1 => (stepChoice blue oracle (familySeq n) n).next

/-- The selected point and step data at stage `n`. -/
noncomputable def stepSeq (n : ℕ) :
    StepResult blue (familySeq blue oracle start n) (past n) (index n) :=
  stepChoice blue oracle (familySeq blue oracle start n) n

noncomputable def pointSeq (n : ℕ) : X :=
  (stepSeq blue oracle start n).point

/-- Transport an index of the family at stage `s+k` back to stage `s`. -/
noncomputable def backIndex : ℕ → ℕ → B → B
  | _, 0, b => b
  | s, k + 1, b =>
      (stepSeq blue oracle start s).reindex
        (backIndex (s + 1) k b)

theorem familySeq_range_back (s k : ℕ) (b : B) (y : Y) :
    ∃ z,
      (familySeq blue oracle start (s + k)).embedding b y =
        (familySeq blue oracle start s).embedding
          (backIndex blue oracle start s k b) z := by
  induction k generalizing s b y with
  | zero => exact ⟨y, rfl⟩
  | succ k ih =>
      obtain ⟨z, hz⟩ := ih (s + 1) b y
      have hz' :
          (familySeq blue oracle start (s + (k + 1))).embedding b y =
            (familySeq blue oracle start (s + 1)).embedding
              (backIndex blue oracle start (s + 1) k b) z := by
        simpa [Nat.add_assoc, Nat.add_comm k 1] using hz
      have hs := (stepSeq blue oracle start s).next_sub
        (backIndex blue oracle start (s + 1) k b) z
      rcases hs with ⟨w, hw⟩
      refine ⟨w, hz'.trans ?_⟩
      simpa [familySeq, stepSeq, backIndex] using hw

theorem backIndex_fix {i s : ℕ} (his : i ≤ s) (k : ℕ) :
    backIndex blue oracle start s k (index i) = index i := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [backIndex, ih (s := s + 1) (by omega)]
      exact (stepSeq blue oracle start s).fixes _
        (index_mem_past_of_le his)

theorem backIndex_lt_of_lt {i s : ℕ} (his : i ≤ s) {b : B}
    (hib : index i < b) (k : ℕ) :
    index i < backIndex blue oracle start s k b := by
  induction k generalizing s b with
  | zero => exact hib
  | succ k ih =>
      have hrel := (stepSeq blue oracle start s).reindex.strictMono
        (ih (s := s + 1) (by omega) hib)
      rw [(stepSeq blue oracle start s).fixes _
        (index_mem_past_of_le his)] at hrel
      exact hrel

theorem backIndex_lt_index_of_lt {i s : ℕ} (his : i ≤ s) {b : B}
    (hbi : b < index i) (k : ℕ) :
    backIndex blue oracle start s k b < index i := by
  induction k generalizing s b with
  | zero => exact hbi
  | succ k ih =>
      have hrel := (stepSeq blue oracle start s).reindex.strictMono
        (ih (s := s + 1) (by omega) hbi)
      rw [(stepSeq blue oracle start s).fixes _
        (index_mem_past_of_le his)] at hrel
      exact hrel

theorem point_later_representation (s k : ℕ) :
    ∃ z, pointSeq blue oracle start (s + k) =
      (familySeq blue oracle start s).embedding
        (backIndex blue oracle start s k (index (s + k))) z := by
  let n := s + k
  rcases (stepSeq blue oracle start n).point_mem with ⟨a, ha⟩
  obtain ⟨z, hz⟩ := familySeq_range_back blue oracle start s k
    (index n) a
  exact ⟨z, ha.symm.trans hz⟩

theorem point_lt_next (n : ℕ) {b : B} (hib : index n < b) (y : Y) :
    pointSeq blue oracle start n <
      (familySeq blue oracle start (n + 1)).embedding b y := by
  let S := stepSeq blue oracle start n
  rcases S.point_mem with ⟨a, ha⟩
  rcases S.next_sub b y with ⟨z, hz⟩
  have hfix := S.fixes (index n) (index_mem_past n)
  have hrel := (familySeq blue oracle start n).separated
    (S.reindex.strictMono hib) a z
  rw [hfix, ha] at hrel
  change S.point < S.next.embedding b y
  rwa [hz]

theorem next_lt_point (n : ℕ) {b : B} (hbi : b < index n) (y : Y) :
    (familySeq blue oracle start (n + 1)).embedding b y <
      pointSeq blue oracle start n := by
  let S := stepSeq blue oracle start n
  rcases S.point_mem with ⟨a, ha⟩
  rcases S.next_sub b y with ⟨z, hz⟩
  have hfix := S.fixes (index n) (index_mem_past n)
  have hrel := (familySeq blue oracle start n).separated
    (S.reindex.strictMono hbi) z a
  rw [hfix, ha] at hrel
  change S.next.embedding b y < S.point
  rwa [hz]

theorem point_lt_later_of_index_lt (m k : ℕ)
    (hidx : index (B := B) m < index (B := B) (m + 1 + k)) :
    pointSeq blue oracle start m <
      pointSeq blue oracle start (m + 1 + k) := by
  obtain ⟨z, hz⟩ := point_later_representation
    (B := B) (Y := Y) (X := X) blue oracle start (m + 1) k
  have hback := backIndex_lt_of_lt (B := B) (Y := Y) (X := X) blue oracle start
    (i := m) (s := m + 1) (by omega) hidx k
  have h := point_lt_next (B := B) (Y := Y) (X := X)
    blue oracle start m hback z
  rw [hz]
  exact h

theorem later_lt_point_of_index_lt (m k : ℕ)
    (hidx : index (B := B) (m + 1 + k) < index (B := B) m) :
    pointSeq blue oracle start (m + 1 + k) <
      pointSeq blue oracle start m := by
  obtain ⟨z, hz⟩ := point_later_representation
    (B := B) (Y := Y) (X := X) blue oracle start (m + 1) k
  have hback := backIndex_lt_index_of_lt
    (B := B) (Y := Y) (X := X) blue oracle start
    (i := m) (s := m + 1) (by omega) hidx k
  have h := next_lt_point (B := B) (Y := Y) (X := X)
    blue oracle start m hback z
  rw [hz]
  exact h

theorem point_lt_later_of_index_eq (m k : ℕ)
    (hidx : index (B := B) (m + 1 + k) = index (B := B) m) :
    pointSeq blue oracle start m <
      pointSeq blue oracle start (m + 1 + k) := by
  obtain ⟨z, hz⟩ := point_later_representation
    (B := B) (Y := Y) (X := X) blue oracle start (m + 1) k
  have hfix := backIndex_fix (B := B) (Y := Y) (X := X) blue oracle start
    (i := m) (s := m + 1) (by omega) k
  rw [hidx, hfix] at hz
  have h := (stepSeq blue oracle start m).point_below z
  change pointSeq blue oracle start m <
    (familySeq blue oracle start (m + 1)).embedding (index m) z at h
  rwa [hz]

theorem point_not_adj_later (m k : ℕ) :
    ¬ blue.Adj (pointSeq blue oracle start m)
      (pointSeq blue oracle start (m + 1 + k)) := by
  obtain ⟨z, hz⟩ := point_later_representation
    (B := B) (Y := Y) (X := X) blue oracle start (m + 1) k
  have h := (stepSeq blue oracle start m).not_adj
    (backIndex blue oracle start (m + 1) k (index (m + 1 + k))) z
  change ¬ blue.Adj (pointSeq blue oracle start m)
    ((familySeq blue oracle start (m + 1)).embedding _ z) at h
  rwa [← hz] at h

/-! ### The fused order embedding -/

/-- The block-first lexicographic sum of one copy of `omega` over every
index in `B`. -/
abbrev Fiber (B : Type) [LinearOrder B] := B ×ₗ ℕ

theorem typeLT_fiber : typeLT (Fiber B) = ω * typeLT B := by
  change type (Prod.Lex ((· < ·) : B → B → Prop)
    ((· < ·) : ℕ → ℕ → Prop)) = _
  rw [Ordinal.type_prod_lex, Ordinal.type_nat_lt]

noncomputable def selected (q : Fiber B) : X :=
  pointSeq blue oracle start
    (occurrence (ofLex q).1 (ofLex q).2)

theorem selected_strictMono :
    StrictMono (selected blue oracle start : Fiber B → X) := by
  intro q r hqr
  rcases Prod.Lex.lt_iff.mp hqr with hbc | ⟨hbc, hkl⟩
  · let m := occurrence (ofLex q).1 (ofLex q).2
    let n := occurrence (ofLex r).1 (ofLex r).2
    change pointSeq blue oracle start m < pointSeq blue oracle start n
    rcases lt_trichotomy m n with hmn | hmn | hnm
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hmn
      have hd' : n = m + 1 + d := by omega
      have hidx : index (B := B) m < index (B := B) n := by
        simpa [m, n] using hbc
      rw [hd'] at hidx ⊢
      exact point_lt_later_of_index_lt (B := B) (Y := Y) (X := X)
        blue oracle start m d hidx
    · have hidx : index (B := B) m = index (B := B) n :=
        congrArg (index (B := B)) hmn
      have : (ofLex q).1 = (ofLex r).1 := by
        simpa [m, n] using hidx
      exact ((lt_irrefl (ofLex q).1) (this ▸ hbc)).elim
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hnm
      have hd' : m = n + 1 + d := by omega
      have hidx : index (B := B) m < index (B := B) n := by
        simpa [m, n] using hbc
      rw [hd'] at hidx ⊢
      exact later_lt_point_of_index_lt (B := B) (Y := Y) (X := X)
        blue oracle start n d hidx
  · have hmn := occurrence_strictMono (B := B) (ofLex q).1 hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hmn
    have hd' : occurrence (ofLex r).1 (ofLex r).2 =
        occurrence (ofLex q).1 (ofLex q).2 + 1 + d := by
      simpa [hbc] using (show occurrence (ofLex q).1 (ofLex r).2 =
        occurrence (ofLex q).1 (ofLex q).2 + 1 + d by omega)
    change pointSeq blue oracle start (occurrence (ofLex q).1 (ofLex q).2) <
      pointSeq blue oracle start (occurrence (ofLex r).1 (ofLex r).2)
    rw [hd']
    apply point_lt_later_of_index_eq (B := B) (Y := Y) (X := X)
      blue oracle start (occurrence (ofLex q).1 (ofLex q).2) d
    rw [← hd']
    simp [hbc]

/-- The order embedding produced by the fusion. -/
noncomputable def orderEmbedding : Fiber B ↪o X :=
  OrderEmbedding.ofStrictMono (selected blue oracle start)
    (selected_strictMono blue oracle start)

theorem orderEmbedding_not_adj {q r : Fiber B} (hqr : q ≠ r) :
    ¬ blue.Adj (orderEmbedding blue oracle start q)
      (orderEmbedding blue oracle start r) := by
  have hocc : occurrence (ofLex q).1 (ofLex q).2 ≠
      occurrence (ofLex r).1 (ofLex r).2 := by
    intro h
    apply hqr
    apply toLex.injective
    exact occurrence_injective (B := B) h
  rcases lt_trichotomy (occurrence (ofLex q).1 (ofLex q).2)
      (occurrence (ofLex r).1 (ofLex r).2) with hlt | heq | hgt
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
    have hd' : occurrence (ofLex r).1 (ofLex r).2 =
        occurrence (ofLex q).1 (ofLex q).2 + 1 + d := by omega
    change ¬ blue.Adj
      (pointSeq blue oracle start (occurrence (ofLex q).1 (ofLex q).2))
      (pointSeq blue oracle start (occurrence (ofLex r).1 (ofLex r).2))
    rw [hd']
    exact point_not_adj_later (B := B) (Y := Y) (X := X)
      blue oracle start _ d
  · exact (hocc heq).elim
  · rw [blue.adj_comm]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
    have hd' : occurrence (ofLex q).1 (ofLex q).2 =
        occurrence (ofLex r).1 (ofLex r).2 + 1 + d := by omega
    change ¬ blue.Adj
      (pointSeq blue oracle start (occurrence (ofLex r).1 (ofLex r).2))
      (pointSeq blue oracle start (occurrence (ofLex q).1 (ofLex q).2))
    rw [hd']
    exact point_not_adj_later (B := B) (Y := Y) (X := X)
      blue oracle start _ d

include oracle start

/-- Order-embedding form of the abstract strong iteration theorem. -/
theorem exists_orderEmbedding_not_adj :
    ∃ e : Fiber B ↪o X, ∀ q r, q ≠ r → ¬ blue.Adj (e q) (e r) := by
  exact ⟨orderEmbedding blue oracle start,
    fun _ _ h ↦ orderEmbedding_not_adj blue oracle start h⟩

/-- Set form, including the exact ordinal type of the fused range. -/
theorem exists_set_type_not_adj [WellFoundedLT X] :
    ∃ S : Set X, typeLT S = ω * typeLT B ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ blue.Adj x y := by
  let e := orderEmbedding blue oracle start
  refine ⟨Set.range e, ?_, ?_⟩
  · have htype : typeLT (Fiber B) = typeLT (Set.range e) :=
      OrderIso.ordinalType_congr e.orderIso
    rw [typeLT_fiber] at htype
    exact htype.symm
  · intro x hx y hy hxy
    rcases hx with ⟨q, rfl⟩
    rcases hy with ⟨r, rfl⟩
    apply orderEmbedding_not_adj blue oracle start
    exact fun h ↦ hxy (congrArg e h)

end Fusion

/-! ### A wrapper recording the usual hypotheses

The hypotheses excluding a blue `K4` and a red `B` are used in the
mathematical one-step lemma that supplies the oracle.  Keeping that lemma as
an argument makes the exact logical boundary explicit. -/

section Wrapper

variable [LinearOrder B] [WellFoundedLT B] [Countable B] [Nonempty B]
variable [LinearOrder Y] [Nonempty Y]
variable [LinearOrder X]

def NoBlueK4 (blue : SimpleGraph X) : Prop :=
  ¬ ∃ S : Set X, blue.IsClique S ∧ #S = 4

def NoRedBCopy (blue : SimpleGraph X) : Prop :=
  ¬ ∃ e : B ↪o X, ∀ b c, b ≠ c → ¬ blue.Adj (e b) (e c)

theorem strong_iteration_under_hypotheses (blue : SimpleGraph X)
    (hK4 : NoBlueK4 blue) (hNoRed : NoRedBCopy (B := B) blue)
    (supply : NoBlueK4 blue → NoRedBCopy (B := B) blue →
      StepOracle (B := B) (Y := Y) blue)
    (start : BlockFamily B Y X) :
    ∃ e : Fiber B ↪o X, ∀ q r, q ≠ r → ¬ blue.Adj (e q) (e r) := by
  exact exists_orderEmbedding_not_adj blue (supply hK4 hNoRed) start

end Wrapper

end Erdos591.StrongIteration
