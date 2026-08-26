import ErdosProblems.Erdos118.Imported591.OuterLevels

open Set Ordinal

namespace Erdos118.Negative.InnerLevels

open WeakPigeon

/-!
Fixed-length extraction inside the raw shortlex order.  This is the small
piece of the Handbook's large-level argument which passes from a large set
of finite sequences to one large lexicographic level.
-/

/-- Raw finite sequences equipped with their shortlex order. -/
def OrderedSL := List ℕ

instance orderedSLLT : LT OrderedSL := ⟨SL⟩

instance orderedSLRelIsWellOrder :
    IsWellOrder OrderedSL ((· < ·) : OrderedSL → OrderedSL → Prop) := by
  change IsWellOrder (List ℕ) SL
  exact rawShortlexIsWellOrder

noncomputable instance orderedSLLinearOrder : LinearOrder OrderedSL := by
  letI : DecidableRel ((· < ·) : OrderedSL → OrderedSL → Prop) :=
    Classical.decRel _
  exact linearOrderOfSTO ((· < ·) : OrderedSL → OrderedSL → Prop)

instance orderedSLWellFoundedLT : WellFoundedLT OrderedSL :=
  ⟨orderedSLRelIsWellOrder.wf⟩

/-- The part of a shortlex set on one fixed sequence length. -/
def Fiber (L : Set OrderedSL) (n : ℕ) : Set OrderedSL :=
  {x | x ∈ L ∧ x.length = n}

@[simp] theorem mem_fiber {L : Set OrderedSL} {n : ℕ} {x : OrderedSL} :
    x ∈ Fiber L n ↔ x ∈ L ∧ x.length = n := Iff.rfl

theorem fiber_disjoint (L : Set OrderedSL) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (Fiber L m) (Fiber L n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact hmn (hxm.2.symm.trans hxn.2)

theorem fiber_separated (L : Set OrderedSL) {m n : ℕ} (hmn : m < n) :
    ∀ x ∈ Fiber L m, ∀ y ∈ Fiber L n, x < y := by
  intro x hx y hy
  change SL x y
  exact List.shortlex_def.2 (Or.inl (hx.2.trans_lt (hy.2 ▸ hmn)))

theorem mem_unionList_iff {ss : List (Set OrderedSL)} {x : OrderedSL} :
    x ∈ CNFStrong.unionList ss ↔ ∃ s ∈ ss, x ∈ s := by
  induction ss with
  | nil => simp [CNFStrong.unionList]
  | cons s ss ih => simp [CNFStrong.unionList, ih]

theorem fibers_consecutive_of_pairwise (L : Set OrderedSL) :
    ∀ {ns : List ℕ}, ns.Pairwise (· < ·) →
      CNFStrong.Consecutive (ns.map (Fiber L)) := by
  intro ns hns
  induction ns with
  | nil => trivial
  | cons n ns ih =>
      rw [List.pairwise_cons] at hns
      change Disjoint (Fiber L n)
          (CNFStrong.unionList (ns.map (Fiber L))) ∧
        (∀ x ∈ Fiber L n,
          ∀ y ∈ CNFStrong.unionList (ns.map (Fiber L)), x < y) ∧
        CNFStrong.Consecutive (ns.map (Fiber L))
      refine ⟨?_, ?_, ih hns.2⟩
      · rw [Set.disjoint_left]
        intro x hxn hxns
        rcases mem_unionList_iff.mp hxns with ⟨s, hs, hxs⟩
        rcases List.mem_map.mp hs with ⟨m, hm, rfl⟩
        exact Set.disjoint_left.mp
          (fiber_disjoint L (Nat.ne_of_lt (hns.1 m hm))) hxn hxs
      · intro x hxn y hy
        rcases mem_unionList_iff.mp hy with ⟨s, hs, hys⟩
        rcases List.mem_map.mp hs with ⟨m, hm, rfl⟩
        exact fiber_separated L (hns.1 m hm) x hxn y hys

theorem fibers_range_consecutive (L : Set OrderedSL) (r : ℕ) :
    CNFStrong.Consecutive ((List.range r).map (Fiber L)) :=
  fibers_consecutive_of_pairwise L List.pairwise_lt_range

theorem foldr_type_lt_principal (ss : List (Set OrderedSL))
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ s ∈ ss, typeLT s < delta) :
    ss.foldr (fun (s : Set OrderedSL) o ↦ typeLT s + o) 0 < delta := by
  induction ss with
  | nil => simpa using hdelta0
  | cons s ss ih =>
      simp only [List.foldr_cons]
      apply hdelta
      · exact hsmall s (by simp)
      · exact ih (fun t ht ↦ hsmall t (by simp [ht]))

theorem type_union_fibers_range_lt (L : Set OrderedSL) (r : ℕ)
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ n, typeLT (Fiber L n) < delta) :
    typeLT (CNFStrong.unionList ((List.range r).map (Fiber L))) < delta := by
  rw [CNFStrong.typeLT_unionList_of_consecutive _
    (fibers_range_consecutive L r)]
  apply foldr_type_lt_principal _ hdelta hdelta0
  intro s hs
  rcases List.mem_map.mp hs with ⟨n, -, rfl⟩
  exact hsmall n

noncomputable def initial_embeds_fibers_range (L : Set OrderedSL)
    (x : L) :
    RelEmbedding ((· < ·) : Set.Iio x → Set.Iio x → Prop)
      ((· < ·) :
        CNFStrong.unionList
          ((List.range (x.1.length + 1)).map (Fiber L)) →
        CNFStrong.unionList
          ((List.range (x.1.length + 1)).map (Fiber L)) → Prop) := by
  let f : Set.Iio x →
      CNFStrong.unionList ((List.range (x.1.length + 1)).map (Fiber L)) :=
    fun y ↦ ⟨y.1.1, by
      apply mem_unionList_iff.mpr
      refine ⟨Fiber L y.1.1.length, ?_, ⟨y.1.2, rfl⟩⟩
      apply List.mem_map.mpr
      refine ⟨y.1.1.length, List.mem_range.mpr ?_, rfl⟩
      apply Nat.lt_succ_iff.mpr
      have hlt : SL y.1.1 x.1 := y.2
      rcases List.shortlex_def.mp hlt with hlen | ⟨hlen, -⟩
      · exact hlen.le
      · exact hlen.le⟩
  exact
    { toFun := f
      inj' := by
        intro y z hyz
        have hraw : (f y).1 = (f z).1 := congrArg Subtype.val hyz
        change y.1.1 = z.1.1 at hraw
        exact Subtype.ext (Subtype.ext hraw)
      map_rel_iff' := by intro y z; rfl }

theorem typein_lt_of_fibers_small (L : Set OrderedSL)
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ n, typeLT (Fiber L n) < delta) (x : L) :
    typein LT.lt x < delta := by
  rw [← Ordinal.type_Iio_lt x]
  apply lt_of_le_of_lt (initial_embeds_fibers_range L x).ordinal_type_le
  exact type_union_fibers_range_lt L (x.1.length + 1)
    hdelta hdelta0 hsmall

theorem type_le_of_fibers_small (L : Set OrderedSL)
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ n, typeLT (Fiber L n) < delta) :
    typeLT L ≤ delta := by
  let coord : L → Set.Iio (typeLT delta.ToType) := fun x ↦
    ⟨typein LT.lt x, by
      simpa only [Set.mem_Iio, Ordinal.type_toType] using
        typein_lt_of_fibers_small L hdelta hdelta0 hsmall x⟩
  let e : RelEmbedding
      ((· < ·) : L → L → Prop)
      ((· < ·) : delta.ToType → delta.ToType → Prop) :=
    { toFun := fun x ↦ Ordinal.enum LT.lt (coord x)
      inj' := by
        intro x y hxy
        have hc : coord x = coord y :=
          (Ordinal.enum (r := LT.lt)).toEquiv.injective hxy
        apply Ordinal.typein_injective LT.lt
        exact congrArg Subtype.val hc
      map_rel_iff' := by
        intro x y
        calc
          Ordinal.enum (r := LT.lt) (coord x) <
                Ordinal.enum (r := LT.lt) (coord y) ↔ coord x < coord y :=
            (Ordinal.enum (r := LT.lt)).map_rel_iff
          _ ↔ typein LT.lt x < typein LT.lt y := Iff.rfl
          _ ↔ x < y := Ordinal.typein_lt_typein LT.lt }
  calc
    typeLT L ≤ typeLT delta.ToType := e.ordinal_type_le
    _ = delta := Ordinal.type_toType delta

/-- A large shortlex set has a fixed-length lexicographic level of the
next lower omega power. -/
theorem exists_large_fiber {L : Set OrderedSL} {k : ℕ}
    (hL : ω ^ ((k + 1 : ℕ) : Ordinal) < typeLT L) :
    ∃ n, ω ^ (k : Ordinal) ≤ typeLT (Fiber L n) := by
  by_contra h
  push Not at h
  have hle := type_le_of_fibers_small L
    (Ordinal.isPrincipal_add_omega0_opow (k : Ordinal))
    (Ordinal.opow_pos _ Ordinal.omega0_pos) h
  have hpow : ω ^ (k : Ordinal) < ω ^ ((k + 1 : ℕ) : Ordinal) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (by
      exact_mod_cast Nat.lt_succ_self k)
  exact (not_lt_of_ge hle) (hpow.trans hL)

/-- The same fixed-length fiber, now packaged as a set of `RawLevel n`. -/
def RawFiber (L : Set OrderedSL) (n : ℕ) : Set (RawLevel n) :=
  {x | (x.1 : OrderedSL) ∈ L}

noncomputable def fiberRawEquiv (L : Set OrderedSL) (n : ℕ) :
    ((· < ·) : Fiber L n → Fiber L n → Prop) ≃r
      ((· < ·) : RawFiber L n → RawFiber L n → Prop) where
  toEquiv :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  map_rel_iff' := by
    intro x y
    change List.Lex (· < ·) (show List ℕ from x.1) (show List ℕ from y.1) ↔
      List.Shortlex (· < ·) (show List ℕ from x.1) (show List ℕ from y.1)
    rw [List.shortlex_def]
    constructor
    · intro h
      exact Or.inr ⟨x.2.2.trans y.2.2.symm, h⟩
    · rintro (hlen | ⟨-, hlex⟩)
      have hxlen : (show List ℕ from x.1).length = n := x.2.2
      have hylen : (show List ℕ from y.1).length = n := y.2.2
      rw [hxlen, hylen] at hlen
      exact (Nat.lt_irrefl n hlen).elim
      exact hlex

theorem type_rawFiber (L : Set OrderedSL) (n : ℕ) :
    typeLT (RawFiber L n) = typeLT (Fiber L n) := by
  exact (fiberRawEquiv L n).ordinal_type_eq.symm

theorem exists_large_rawFiber {L : Set OrderedSL} {k : ℕ}
    (hL : ω ^ ((k + 1 : ℕ) : Ordinal) < typeLT L) :
    ∃ n, ω ^ (k : Ordinal) ≤ typeLT (RawFiber L n) := by
  obtain ⟨n, hn⟩ := exists_large_fiber hL
  refine ⟨n, ?_⟩
  rw [type_rawFiber]
  exact hn

end Erdos118.Negative.InnerLevels
