import ErdosProblems.Erdos118.Imported591.CNFStrong
import ErdosProblems.Erdos118.Imported591.WeakPigeon

open Set Ordinal

namespace Erdos118.Negative.LexPrefix

/-!
Prefix calculus for a fixed finite lexicographic level.  This is the
formal version of the maximal-prefix argument in Handbook Lemmas 9.22 and
9.23.  Prefixes are allowed to have length at most the ambient level.
-/

open WeakPigeon

def Fiber {n : ℕ} (W : Set (RawLevel n)) (p : List ℕ) :
    Set (RawLevel n) := {x | x ∈ W ∧ p <+: x.1}

@[simp] theorem mem_fiber {n : ℕ} {W : Set (RawLevel n)}
    {p : List ℕ} {x : RawLevel n} :
    x ∈ Fiber W p ↔ x ∈ W ∧ p <+: x.1 := Iff.rfl

def Child {n : ℕ} (W : Set (RawLevel n)) (p : List ℕ) (a : ℕ) :
    Set (RawLevel n) := Fiber W (p ++ [a])

theorem child_subset_fiber {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (a : ℕ) : Child W p a ⊆ Fiber W p := by
  rintro x ⟨hxW, hpx⟩
  exact ⟨hxW, (List.prefix_append p [a]).trans hpx⟩

theorem child_disjoint {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) {a b : ℕ} (hab : a ≠ b) :
    Disjoint (Child W p a) (Child W p b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  rcases hxa.2 with ⟨u, hu⟩
  rcases hxb.2 with ⟨v, hv⟩
  have h : p ++ [a] ++ u = p ++ [b] ++ v := hu.trans hv.symm
  have h' : a :: u = b :: v := by
    apply List.append_right_injective p
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  have : a = b := (List.cons.inj h').1
  exact hab this

theorem child_separated {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) {a b : ℕ} (hab : a < b) :
    ∀ x ∈ Child W p a, ∀ y ∈ Child W p b, x < y := by
  intro x hx y hy
  rcases hx.2 with ⟨u, hu⟩
  rcases hy.2 with ⟨v, hv⟩
  change RawLevelLex x y
  change List.Lex (· < ·) x.1 y.1
  rw [← hu, ← hv, List.append_assoc, List.append_assoc]
  exact List.Lex.append_left (· < ·) (List.Lex.rel hab) p

theorem fiber_eq_child_of_length_lt {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (x : RawLevel n)
    (hx : x ∈ Fiber W p) : x ∈ Child W p (x.1.get ⟨p.length, by
      simpa [x.2] using hp⟩) := by
  refine ⟨hx.1, ?_⟩
  exact List.concat_get_prefix hx.2 (by simpa [x.2] using hp)

theorem fiber_eq_iUnion_child {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) :
    Fiber W p = ⋃ a : ℕ, Child W p a := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.2 ⟨_, fiber_eq_child_of_length_lt W p hp x hx⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨a, hxa⟩
    exact child_subset_fiber W p a hxa

theorem fiber_subsingleton_of_length_eq {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length = n) :
    Subsingleton (Fiber W p) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  apply Subtype.ext
  apply Subtype.ext
  have hxp : p = x.1 := by
    rcases hx.2 with ⟨u, hu⟩
    have hulen : u.length = 0 := by
      have := congrArg List.length hu
      simp only [List.length_append, x.2, hp] at this
      omega
    simpa [List.length_eq_zero_iff.mp hulen] using hu
  have hyp : p = y.1 := by
    rcases hy.2 with ⟨u, hu⟩
    have hulen : u.length = 0 := by
      have := congrArg List.length hu
      simp only [List.length_append, y.2, hp] at this
      omega
    simpa [List.length_eq_zero_iff.mp hulen] using hu
  exact hxp.symm.trans hyp

theorem mem_unionList_iff {n : ℕ} {ss : List (Set (RawLevel n))}
    {x : RawLevel n} :
    x ∈ CNFStrong.unionList ss ↔ ∃ s ∈ ss, x ∈ s := by
  induction ss with
  | nil => simp [CNFStrong.unionList]
  | cons s ss ih => simp [CNFStrong.unionList, ih]

theorem children_consecutive_of_pairwise {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) :
    ∀ {as : List ℕ}, as.Pairwise (· < ·) →
      CNFStrong.Consecutive (as.map (Child W p)) := by
  intro as has
  induction as with
  | nil => trivial
  | cons a as ih =>
      rw [List.pairwise_cons] at has
      change Disjoint (Child W p a)
          (CNFStrong.unionList (as.map (Child W p))) ∧
        (∀ x ∈ Child W p a,
          ∀ y ∈ CNFStrong.unionList (as.map (Child W p)), x < y) ∧
        CNFStrong.Consecutive (as.map (Child W p))
      refine ⟨?_, ?_, ih has.2⟩
      · rw [Set.disjoint_left]
        intro x hxa hxas
        rcases mem_unionList_iff.mp hxas with ⟨s, hs, hxs⟩
        rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
        exact Set.disjoint_left.mp
          (child_disjoint W p (Nat.ne_of_lt (has.1 b hb))) hxa hxs
      · intro x hxa y hy
        rcases mem_unionList_iff.mp hy with ⟨s, hs, hys⟩
        rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
        exact child_separated W p (has.1 b hb) x hxa y hys

theorem range_pairwise_lt (m : ℕ) :
    (List.range m).Pairwise (· < ·) := by
  exact List.pairwise_lt_range

theorem children_range_consecutive {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (m : ℕ) :
    CNFStrong.Consecutive ((List.range m).map (Child W p)) :=
  children_consecutive_of_pairwise W p (range_pairwise_lt m)

theorem foldr_type_lt_principal {n : ℕ}
    {ss : List (Set (RawLevel n))} {beta : Ordinal}
    (hbeta : IsPrincipal (· + ·) beta) (hbeta0 : 0 < beta)
    (hsmall : ∀ s ∈ ss, typeLT s < beta) :
    ss.foldr (fun (s : Set (RawLevel n)) o ↦ typeLT s + o) 0 < beta := by
  induction ss with
  | nil => simpa using hbeta0
  | cons s ss ih =>
      simp only [List.foldr_cons]
      apply hbeta
      · exact hsmall s (by simp)
      · exact ih (fun t ht ↦ hsmall t (by simp [ht]))

theorem type_union_children_range_lt {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (m : ℕ)
    {beta : Ordinal} (hbeta : IsPrincipal (· + ·) beta)
    (hbeta0 : 0 < beta)
    (hsmall : ∀ a, typeLT (Child W p a) < beta) :
    typeLT (CNFStrong.unionList ((List.range m).map (Child W p))) < beta := by
  rw [CNFStrong.typeLT_unionList_of_consecutive _
    (children_range_consecutive W p m)]
  apply foldr_type_lt_principal hbeta hbeta0
  intro s hs
  rcases List.mem_map.mp hs with ⟨a, ha, rfl⟩
  exact hsmall a

noncomputable def initial_fiber_embeds_children_range {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (hp : p.length < n)
    (x : Fiber W p) :
    RelEmbedding ((· < ·) : Set.Iio x → Set.Iio x → Prop)
      ((· < ·) :
        CNFStrong.unionList
          ((List.range (x.1.1.get ⟨p.length, by
            simpa [x.1.2] using hp⟩ + 1)).map (Child W p)) →
          CNFStrong.unionList
            ((List.range (x.1.1.get ⟨p.length, by
              simpa [x.1.2] using hp⟩ + 1)).map (Child W p)) → Prop) := by
  let ax : ℕ := x.1.1.get ⟨p.length, by simpa [x.1.2] using hp⟩
  let f : Set.Iio x →
      CNFStrong.unionList ((List.range (ax + 1)).map (Child W p)) :=
    fun y ↦ ⟨y.1.1, by
      apply mem_unionList_iff.mpr
      let ay : ℕ := y.1.1.1.get ⟨p.length, by
        simpa [y.1.1.2] using hp⟩
      have hyChild : y.1.1 ∈ Child W p ay :=
        fiber_eq_child_of_length_lt W p hp y.1.1 y.1.2
      have hxChild : x.1 ∈ Child W p ax := by
        exact fiber_eq_child_of_length_lt W p hp x.1 x.2
      have hay : ay ≤ ax := by
        by_contra h
        have hxa : ax < ay := Nat.lt_of_not_ge h
        have hxy : x.1 < y.1.1 :=
          child_separated W p hxa x.1 hxChild y.1.1 hyChild
        exact (LT.lt.asymm y.2 hxy)
      refine ⟨Child W p ay, ?_, hyChild⟩
      apply List.mem_map.mpr
      exact ⟨ay, List.mem_range.mpr (Nat.lt_succ_iff.mpr hay), rfl⟩⟩
  exact
    { toFun := f
      inj' := by
        intro y z hyz
        have hraw : y.1.1 = z.1.1 :=
          congrArg (fun q ↦ q.1) hyz
        exact Subtype.ext (Subtype.ext hraw)
      map_rel_iff' := by
        intro y z
        rfl }

theorem typein_fiber_lt_of_children_small {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (hp : p.length < n)
    {beta : Ordinal} (hbeta : IsPrincipal (· + ·) beta)
    (hbeta0 : 0 < beta)
    (hsmall : ∀ a, typeLT (Child W p a) < beta)
    (x : Fiber W p) : typein LT.lt x < beta := by
  rw [← Ordinal.type_Iio_lt x]
  apply lt_of_le_of_lt
    (initial_fiber_embeds_children_range W p hp x).ordinal_type_le
  exact type_union_children_range_lt W p _ hbeta hbeta0 hsmall

theorem type_fiber_le_of_children_small {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (hp : p.length < n)
    {beta : Ordinal} (hbeta : IsPrincipal (· + ·) beta)
    (hbeta0 : 0 < beta)
    (hsmall : ∀ a, typeLT (Child W p a) < beta) :
    typeLT (Fiber W p) ≤ beta := by
  let coord : Fiber W p → Set.Iio (typeLT beta.ToType) := fun x ↦
    ⟨typein LT.lt x, by
      simpa only [Set.mem_Iio, Ordinal.type_toType] using
        typein_fiber_lt_of_children_small W p hp hbeta hbeta0 hsmall x⟩
  let e : RelEmbedding
      ((· < ·) : Fiber W p → Fiber W p → Prop)
      ((· < ·) : beta.ToType → beta.ToType → Prop) :=
    { toFun := fun x ↦ Ordinal.enum LT.lt (coord x)
      inj' := by
        intro x y hxy
        have hcoord : coord x = coord y :=
          (Ordinal.enum (r := LT.lt)).toEquiv.injective hxy
        apply Ordinal.typein_injective LT.lt
        exact congrArg Subtype.val hcoord
      map_rel_iff' := by
        intro x y
        calc
          Ordinal.enum (r := LT.lt) (coord x) <
                Ordinal.enum (r := LT.lt) (coord y) ↔
              coord x < coord y :=
            (Ordinal.enum (r := LT.lt)).map_rel_iff
          _ ↔ typein LT.lt x < typein LT.lt y := Iff.rfl
          _ ↔ x < y := Ordinal.typein_lt_typein LT.lt }
  calc
    typeLT (Fiber W p) ≤ typeLT beta.ToType := e.ordinal_type_le
    _ = beta := Ordinal.type_toType beta

theorem typeLT_le_one_of_subsingleton (X : Type*) [LinearOrder X]
    [WellFoundedLT X] [Subsingleton X] : typeLT X ≤ 1 := by
  classical
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    have hUnique : Nonempty (Unique X) := by
      exact ⟨{ default := Classical.choice hX,
                uniq := fun x ↦ Subsingleton.elim x _ }⟩
    have hEq : typeLT X = 1 :=
      (Ordinal.type_eq_one_iff_unique
        (r := ((· < ·) : X → X → Prop))).2 hUnique
    exact hEq.le
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    have hEq : typeLT X = 0 := Ordinal.type_eq_zero_of_empty _
    rw [hEq]
    exact zero_le

/-- Restrict a set to those members whose coordinate immediately after
`p` is strictly larger than `q`.  The definition is made on the ambient
level so that the existing child calculus can be reused verbatim. -/
def Above {n : ℕ} (W : Set (RawLevel n)) (p : List ℕ)
    (hp : p.length < n) (q : ℕ) : Set (RawLevel n) :=
  {x | x ∈ W ∧ p <+: x.1 ∧
    q < (x.1.drop p.length).headD 0}

theorem fiber_above_eq {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (q : ℕ) :
    Fiber (Above W p hp q) p = Above W p hp q := by
  ext x
  simp only [mem_fiber, Above, Set.mem_setOf_eq]
  aesop

theorem child_above_empty_of_le {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (q a : ℕ) (ha : a ≤ q) :
    Child (Above W p hp q) p a = ∅ := by
  ext x
  constructor
  · intro hx
    rcases hx.2 with ⟨u, hu⟩
    have hcoord : (x.1.drop p.length).headD 0 = a := by
      rw [← hu]
      simp
    have habove := hx.1.2.2
    rw [hcoord] at habove
    exact (not_lt_of_ge ha habove).elim
  · simp

theorem child_above_subset {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (q a : ℕ) :
    Child (Above W p hp q) p a ⊆ Child W p a := by
  rintro x hx
  exact ⟨hx.1.1, hx.2⟩

theorem typeLT_mono_set {A : Type*} [LinearOrder A] [WellFoundedLT A]
    {s t : Set A} (hst : s ⊆ t) : typeLT s ≤ typeLT t := by
  let e : ((· < ·) : s → s → Prop) ↪r
      ((· < ·) : t → t → Prop) :=
    RelEmbedding.ofMonotone (fun x : s ↦ (⟨x.1, hst x.2⟩ : t))
      (by intro x y hxy; exact hxy)
  exact e.ordinal_type_le

theorem type_fiber_above_le_of_children_small {n : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (hp : p.length < n)
    (q : ℕ) {delta : Ordinal}
    (hdelta : IsPrincipal (· + ·) delta) (hdelta0 : 0 < delta)
    (hsmall : ∀ a, q < a → typeLT (Child W p a) < delta) :
    typeLT (Above W p hp q) ≤ delta := by
  rw [← fiber_above_eq W p hp q]
  apply type_fiber_le_of_children_small (Above W p hp q) p hp
    hdelta hdelta0
  intro a
  by_cases ha : a ≤ q
  · rw [child_above_empty_of_le W p hp q a ha]
    simpa using hdelta0
  · exact (typeLT_mono_set (child_above_subset W p hp q a)).trans_lt
      (hsmall a (Nat.lt_of_not_ge ha))

theorem fiber_eq_initial_union_above {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (q : ℕ) :
    Fiber W p =
      CNFStrong.unionList ((List.range (q + 1)).map (Child W p)) ∪
        Above W p hp q := by
  ext x
  constructor
  · intro hx
    let a : ℕ := (x.1.drop p.length).headD 0
    have hchild : x ∈ Child W p a := by
      rcases hx.2 with ⟨u, hu⟩
      cases u with
      | nil =>
          have hlen := congrArg List.length hu
          simp [x.2] at hlen
          omega
      | cons b bs =>
          have hba : b = a := by
            simp only [a]
            rw [← hu]
            simp
          subst b
          refine ⟨hx.1, ?_⟩
          exact ⟨bs, by simpa [List.append_assoc] using hu⟩
    by_cases ha : a ≤ q
    · apply Or.inl
      apply mem_unionList_iff.mpr
      refine ⟨Child W p a, ?_, hchild⟩
      apply List.mem_map.mpr
      exact ⟨a, List.mem_range.mpr (Nat.lt_succ_iff.mpr ha), rfl⟩
    · exact Or.inr ⟨hx.1, hx.2, Nat.lt_of_not_ge ha⟩
  · rintro (hx | hx)
    · rcases mem_unionList_iff.mp hx with ⟨s, hs, hxs⟩
      rcases List.mem_map.mp hs with ⟨a, -, rfl⟩
      exact child_subset_fiber W p a hxs
    · exact ⟨hx.1, hx.2.1⟩

theorem initial_union_disjoint_above {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (q : ℕ) :
    Disjoint
      (CNFStrong.unionList ((List.range (q + 1)).map (Child W p)))
      (Above W p hp q) := by
  rw [Set.disjoint_left]
  intro x hxI hxA
  rcases mem_unionList_iff.mp hxI with ⟨s, hs, hxs⟩
  rcases List.mem_map.mp hs with ⟨a, ha, rfl⟩
  have haq : a ≤ q := Nat.lt_succ_iff.mp (List.mem_range.mp ha)
  rcases hxs.2 with ⟨u, hu⟩
  have hcoord : (x.1.drop p.length).headD 0 = a := by
    rw [← hu]
    simp
  have habove := hxA.2.2
  rw [hcoord] at habove
  exact (not_lt_of_ge haq habove)

theorem initial_union_below_above {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length < n) (q : ℕ) :
    ∀ x ∈ CNFStrong.unionList ((List.range (q + 1)).map (Child W p)),
      ∀ y ∈ Above W p hp q, x < y := by
  intro x hx y hy
  rcases mem_unionList_iff.mp hx with ⟨s, hs, hxs⟩
  rcases List.mem_map.mp hs with ⟨a, ha, rfl⟩
  let b : ℕ := (y.1.drop p.length).headD 0
  have hby : y ∈ Child W p b := by
    rcases hy.2.1 with ⟨u, hu⟩
    cases u with
    | nil =>
        have hlen := congrArg List.length hu
        simp [y.2] at hlen
        omega
    | cons c cs =>
        have hcb : c = b := by
          simp only [b]
          rw [← hu]
          simp
        subst c
        refine ⟨hy.1, ?_⟩
        exact ⟨cs, by simpa [List.append_assoc] using hu⟩
  have haq : a ≤ q := Nat.lt_succ_iff.mp (List.mem_range.mp ha)
  exact child_separated W p (haq.trans_lt hy.2.2) x hxs y hby

/-- Handbook Lemma 9.23 on a fixed finite level.  Below a maximal
`omega^k` prefix, children of every strictly smaller omega-power size occur
arbitrarily far out. -/
theorem exists_large_child_above {n k j : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length ≤ n)
    (htype : typeLT (Fiber W p) = ω ^ (k : Ordinal))
    (hmax : ∀ a, typeLT (Child W p a) < ω ^ (k : Ordinal))
    (hjk : j < k) (q : ℕ) :
    ∃ a, q < a ∧ ω ^ (j : Ordinal) ≤ typeLT (Child W p a) := by
  classical
  have hp' : p.length < n := by
    apply lt_of_le_of_ne hp
    intro hpn
    letI : Subsingleton (Fiber W p) :=
      fiber_subsingleton_of_length_eq W p hpn
    have hle := typeLT_le_one_of_subsingleton (Fiber W p)
    have hpow : 1 < ω ^ (k : Ordinal) := by
      rw [Ordinal.one_lt_opow]
      refine ⟨Ordinal.one_lt_omega0, ?_⟩
      exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt hjk)
    exact (not_le_of_gt hpow) (htype ▸ hle)
  by_contra h
  push_neg at h
  have hdelta0 : 0 < ω ^ (j : Ordinal) :=
    Ordinal.opow_pos _ Ordinal.omega0_pos
  have htail : typeLT (Above W p hp' q) ≤ ω ^ (j : Ordinal) :=
    type_fiber_above_le_of_children_small W p hp' q
      (Ordinal.isPrincipal_add_omega0_opow (j : Ordinal)) hdelta0 h
  let I : Set (RawLevel n) :=
    CNFStrong.unionList ((List.range (q + 1)).map (Child W p))
  have hI : typeLT I < ω ^ (k : Ordinal) :=
    type_union_children_range_lt W p (q + 1)
      (Ordinal.isPrincipal_add_omega0_opow (k : Ordinal))
      (Ordinal.opow_pos _ Ordinal.omega0_pos) hmax
  have hdelta : ω ^ (j : Ordinal) < ω ^ (k : Ordinal) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
      (by exact_mod_cast hjk)
  have hsum : typeLT I + typeLT (Above W p hp' q) <
      ω ^ (k : Ordinal) := by
    apply Ordinal.isPrincipal_add_omega0_opow (k : Ordinal)
    · exact hI
    · exact htail.trans_lt hdelta
  have hunion := CNFStrong.typeLT_union_of_separated I (Above W p hp' q)
    (initial_union_disjoint_above W p hp' q)
    (initial_union_below_above W p hp' q)
  have hfiber : Fiber W p = I ∪ Above W p hp' q :=
    fiber_eq_initial_union_above W p hp' q
  rw [← hfiber, htype] at hunion
  exact (lt_irrefl (ω ^ (k : Ordinal))) (hunion.symm ▸ hsum)

theorem child_empty_of_length_eq {n : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length = n) (a : ℕ) :
    Child W p a = ∅ := by
  ext x
  constructor
  · intro hx
    have hlen := hx.2.length_le
    simp only [List.length_append, List.length_singleton, x.2, hp] at hlen
    omega
  · simp

/-- A finite-level form of Handbook Lemma 9.22: every fiber of type at
least `ω^k` has an extending prefix whose fiber has exactly that type and
whose immediate child fibers all have smaller type. -/
theorem exists_maximal_prefix {n k : ℕ} (W : Set (RawLevel n))
    (p : List ℕ) (hp : p.length ≤ n)
    (hlarge : ω ^ (k : Ordinal) ≤ typeLT (Fiber W p)) :
    ∃ q : List ℕ, p <+: q ∧ q.length ≤ n ∧
      typeLT (Fiber W q) = ω ^ (k : Ordinal) ∧
      ∀ a, typeLT (Child W q a) < ω ^ (k : Ordinal) := by
  classical
  generalize hd : n - p.length = d
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
      have hbeta0 : 0 < ω ^ (k : Ordinal) :=
        Ordinal.opow_pos _ Ordinal.omega0_pos
      by_cases hchild : ∃ a, ω ^ (k : Ordinal) ≤ typeLT (Child W p a)
      · obtain ⟨a, ha⟩ := hchild
        have hplt : p.length < n := by
          apply lt_of_le_of_ne hp
          intro hpn
          have hempty := child_empty_of_length_eq W p hpn a
          have hzero : typeLT (Child W p a) = 0 := by
            rw [hempty]
            exact Ordinal.type_eq_zero_of_empty _
          rw [hzero] at ha
          exact (not_le_of_gt hbeta0) ha
        have hpnext : (p ++ [a]).length ≤ n := by simp; omega
        have hdlt : n - (p ++ [a]).length < d := by
          rw [← hd]
          simp only [List.length_append, List.length_singleton]
          omega
        obtain ⟨q, hpq, hqn, hqtype, hqmax⟩ :=
          ih (n - (p ++ [a]).length) hdlt (p ++ [a]) hpnext ha rfl
        refine ⟨q, ?_, hqn, hqtype, hqmax⟩
        exact (List.prefix_append p [a]).trans hpq
      · have hsmall : ∀ a,
            typeLT (Child W p a) < ω ^ (k : Ordinal) := by
          intro a
          exact lt_of_not_ge (fun ha ↦ hchild ⟨a, ha⟩)
        have hle : typeLT (Fiber W p) ≤ ω ^ (k : Ordinal) := by
          by_cases hpn : p.length = n
          · letI : Subsingleton (Fiber W p) :=
              fiber_subsingleton_of_length_eq W p hpn
            exact (typeLT_le_one_of_subsingleton (Fiber W p)).trans
              (Order.one_le_iff_pos.mpr hbeta0)
          · exact type_fiber_le_of_children_small W p (lt_of_le_of_ne hp hpn)
              (Ordinal.isPrincipal_add_omega0_opow (k : Ordinal)) hbeta0 hsmall
        exact ⟨p, List.prefix_refl p, hp, le_antisymm hle hlarge, hsmall⟩

theorem exists_maximal_prefix_above {n k j : ℕ}
    (W : Set (RawLevel n)) (p : List ℕ) (hp : p.length ≤ n)
    (htype : typeLT (Fiber W p) = ω ^ (k : Ordinal))
    (hmax : ∀ a, typeLT (Child W p a) < ω ^ (k : Ordinal))
    (hjk : j < k) (q : ℕ) :
    ∃ a r, q < a ∧ p ++ [a] <+: r ∧ r.length ≤ n ∧
      typeLT (Fiber W r) = ω ^ (j : Ordinal) ∧
      ∀ b, typeLT (Child W r b) < ω ^ (j : Ordinal) := by
  obtain ⟨a, hqa, ha⟩ := exists_large_child_above W p hp htype hmax hjk q
  obtain ⟨r, har, hrn, hrtype, hrmax⟩ :=
    exists_maximal_prefix W (p ++ [a]) (by
      have hp' : p.length < n := by
        apply lt_of_le_of_ne hp
        intro hpn
        have hempty := child_empty_of_length_eq W p hpn a
        rw [hempty, Ordinal.type_eq_zero_of_empty] at ha
        exact (not_le_of_gt (Ordinal.opow_pos _ Ordinal.omega0_pos)) ha
      simp; omega) ha
  exact ⟨a, r, hqa, har, hrn, hrtype, hrmax⟩

end Erdos118.Negative.LexPrefix
