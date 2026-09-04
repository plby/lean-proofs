import Mathlib

namespace Erdos118.Reused591

open Set
open Ordinal

namespace CNFStrong

variable {α : Type*} [LinearOrder α] [WellFoundedLT α]

/-- Two disjoint, consecutive subsets form an ordinal sum. -/
noncomputable def separatedUnionRelIso (s t : Set α) (hd : Disjoint s t)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    Sum.Lex ((· < ·) : s → s → Prop) ((· < ·) : t → t → Prop) ≃r
      ((· < ·) : ↥(s ∪ t) → ↥(s ∪ t) → Prop) := by
  classical
  refine
    { toEquiv := (Equiv.Set.union hd).symm
      map_rel_iff' := ?_ }
  intro x y
  cases x with
  | inl x =>
    cases y with
    | inl y => simp
    | inr y =>
      simp only [Equiv.Set.union_symm_apply_left,
        Equiv.Set.union_symm_apply_right]
      constructor
      · intro
        exact .sep x y
      · intro
        exact hst x x.2 y y.2
  | inr x =>
    cases y with
    | inl y =>
      simp only [Equiv.Set.union_symm_apply_left,
        Equiv.Set.union_symm_apply_right]
      constructor
      · intro h
        exact False.elim ((hst y y.2 x x.2).asymm h)
      · intro h
        nomatch h
    | inr y => simp

theorem typeLT_union_of_separated (s t : Set α) (hd : Disjoint s t)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    typeLT ↥(s ∪ t) = typeLT s + typeLT t := by
  rw [← Ordinal.type_sum_lex]
  exact (separatedUnionRelIso s t hd hst).ordinalType_congr.symm

/-- If each of two consecutive pieces is thinned without changing its order type,
then their union is also thinned without changing order type. -/
theorem typeLT_union_eq_of_piecewise {s t s' t' : Set α}
    (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hd : Disjoint s t) (hst : ∀ x ∈ s, ∀ y ∈ t, x < y)
    (hsTy : typeLT s' = typeLT s) (htTy : typeLT t' = typeLT t) :
    typeLT ↥(s' ∪ t') = typeLT ↥(s ∪ t) := by
  have hd' : Disjoint s' t' := hd.mono hs ht
  have hst' : ∀ x ∈ s', ∀ y ∈ t', x < y :=
    fun x hx y hy => hst x (hs hx) y (ht hy)
  rw [typeLT_union_of_separated s' t' hd' hst',
    typeLT_union_of_separated s t hd hst, hsTy, htTy]

/-- Union of a finite list of sets.  We keep this explicit (rather than use a
finitary indexed union) because its recursion is exactly the recursion of
ordinal addition. -/
def unionList : List (Set α) → Set α
  | [] => ∅
  | s :: ss => s ∪ unionList ss

/-- A list of pieces occurs from left to right, with no overlap. -/
def Consecutive : List (Set α) → Prop
  | [] => True
  | s :: ss =>
      Disjoint s (unionList ss) ∧
      (∀ x ∈ s, ∀ y ∈ unionList ss, x < y) ∧
      Consecutive ss

theorem typeLT_unionList_of_consecutive :
    ∀ (ss : List (Set α)), Consecutive ss →
      typeLT ↥(unionList ss) = ss.foldr (fun (s : Set α) o => typeLT s + o) 0
  | [], _ => by simp [unionList]
  | s :: ss, h => by
      rw [unionList, typeLT_union_of_separated s (unionList ss) h.1 h.2.1,
        typeLT_unionList_of_consecutive ss h.2.2]
      rfl

theorem unionList_mono :
    ∀ {ss tt : List (Set α)}, List.Forall₂ (· ⊆ ·) ss tt → unionList ss ⊆ unionList tt
  | [], [], _ => by simp [unionList]
  | s :: ss, t :: tt, h => by
      cases h with
      | cons hhead htail =>
          intro x hx
          rcases hx with hx | hx
          · exact Or.inl (hhead hx)
          · exact Or.inr (unionList_mono htail hx)

/-- Piecewise full order type implies full order type for a finite consecutive
partition.  This is the reconstruction statement needed by the finite-CNF
"strong type" argument. -/
theorem typeLT_unionList_eq_of_piecewise :
    ∀ {ss tt : List (Set α)}, Consecutive tt →
      List.Forall₂ (· ⊆ ·) ss tt →
      List.Forall₂ (fun (s t : Set α) => typeLT s = typeLT t) ss tt →
      typeLT ↥(unionList ss) = typeLT ↥(unionList tt)
  | [], [], _, _, _ => rfl
  | s :: ss, t :: tt, hcon, hsub, hty => by
      cases hsub with
      | cons hsubHead hsubTail =>
          cases hty with
          | cons htyHead htyTail =>
              have htailSub : unionList ss ⊆ unionList tt := unionList_mono hsubTail
              have hdisj : Disjoint s (unionList ss) :=
                hcon.1.mono hsubHead htailSub
              have hsep : ∀ x ∈ s, ∀ y ∈ unionList ss, x < y :=
                fun x hx y hy => hcon.2.1 x (hsubHead hx) y (htailSub hy)
              rw [unionList, unionList,
                typeLT_union_of_separated s (unionList ss) hdisj hsep,
                typeLT_union_of_separated t (unionList tt) hcon.1 hcon.2.1,
                htyHead,
                typeLT_unionList_eq_of_piecewise hcon.2.2 hsubTail htyTail]

theorem unionList_subset_of_forall_mem {ss : List (Set α)} {u : Set α}
    (h : ∀ s ∈ ss, s ⊆ u) : unionList ss ⊆ u := by
  induction ss with
  | nil => simp [unionList]
  | cons s ss ih =>
      intro x hx
      rcases hx with hx | hx
      · exact h s (by simp) hx
      · exact ih (fun t ht => h t (by simp [ht])) hx

/-! ## A finite additive-principal decomposition of every ordinal

This is equivalent to expanding the finite coefficients in Cantor normal
form.  Peeling off the leading `ω`-power is considerably easier to use in
Lean: `sub_omega0_opow_log_lt` is exactly the termination theorem. -/

noncomputable def principalTerms (o : Ordinal) : List Ordinal :=
  if h : o = 0 then []
  else ω ^ log ω o :: principalTerms (o - ω ^ log ω o)
termination_by o
decreasing_by exact sub_omega0_opow_log_lt h

@[simp] theorem principalTerms_zero : principalTerms 0 = [] := by
  rw [principalTerms, dif_pos rfl]

theorem principalTerms_ne_zero {o : Ordinal} (ho : o ≠ 0) :
    principalTerms o = ω ^ log ω o :: principalTerms (o - ω ^ log ω o) := by
  rw [principalTerms, dif_neg ho]

theorem principalTerms_foldr_add (o : Ordinal) :
    (principalTerms o).foldr (· + ·) 0 = o := by
  induction o using WellFoundedLT.induction with
  | ind o ih =>
      by_cases ho : o = 0
      · subst o
        simp
      · rw [principalTerms_ne_zero ho, List.foldr_cons,
          ih (o - ω ^ log ω o) (sub_omega0_opow_log_lt ho),
          Ordinal.add_sub_cancel_of_le (opow_log_le_self ω ho)]

theorem mem_principalTerms_is_omegaPower {o p : Ordinal}
    (hp : p ∈ principalTerms o) : ∃ e : Ordinal, p = ω ^ e := by
  induction o using WellFoundedLT.induction with
  | ind o ih =>
      by_cases ho : o = 0
      · simp [ho] at hp
      · rw [principalTerms_ne_zero ho] at hp
        simp only [List.mem_cons] at hp
        cases hp with
        | inl heq => exact ⟨_, heq⟩
        | inr hp => exact ih (o - ω ^ log ω o) (sub_omega0_opow_log_lt ho) hp

theorem mem_principalTerms_isPrincipal_add {o p : Ordinal}
    (hp : p ∈ principalTerms o) : IsPrincipal (· + ·) p := by
  obtain ⟨e, rfl⟩ := mem_principalTerms_is_omegaPower hp
  exact isPrincipal_add_omega0_opow e

theorem mem_principalTerms_ne_zero {o p : Ordinal}
    (hp : p ∈ principalTerms o) : p ≠ 0 := by
  obtain ⟨e, rfl⟩ := mem_principalTerms_is_omegaPower hp
  exact opow_ne_zero _ omega0_ne_zero

/-! ## Cutting a well-order at an ordinal coordinate -/

section Cuts

variable {β : Type} [LinearOrder β] [WellFoundedLT β]

def leftCut (p : Ordinal) : Set β := {x | typein LT.lt x < p}

def rightCut (p : Ordinal) : Set β := {x | p ≤ typein LT.lt x}

noncomputable def leftCutCoord (p : Ordinal) (hp : p ≤ typeLT β) (i : p.ToType) :
    Set.Iio (typeLT β) :=
  ⟨typein LT.lt i, (typein_lt_self i).trans_le hp⟩

noncomputable def leftCutIndexCoord (p : Ordinal) (x : leftCut (β := β) p) :
    Set.Iio (typeLT p.ToType) :=
  ⟨typein LT.lt (x : β), by
    rw [type_toType]
    exact x.2⟩

theorem typein_enum_leftCutCoord (p : Ordinal) (hp : p ≤ typeLT β) (i : p.ToType) :
    typein LT.lt (enum (α := β) LT.lt (leftCutCoord p hp i)) = typein LT.lt i :=
  typein_enum LT.lt (leftCutCoord p hp i).2

theorem typein_enum_leftCutIndexCoord (p : Ordinal) (x : leftCut (β := β) p) :
    typein LT.lt (enum (α := p.ToType) LT.lt (leftCutIndexCoord p x)) =
      typein LT.lt (x : β) :=
  typein_enum LT.lt (leftCutIndexCoord p x).2

noncomputable def leftCutRelIso (p : Ordinal) (hp : p ≤ typeLT β) :
    (LT.lt : p.ToType → p.ToType → Prop) ≃r
      (LT.lt : leftCut (β := β) p → leftCut (β := β) p → Prop) := by
  let f : p.ToType → leftCut (β := β) p := fun i =>
    ⟨enum (α := β) LT.lt (leftCutCoord p hp i),
      by
        change typein (α := β) LT.lt
          (enum (α := β) LT.lt (leftCutCoord p hp i)) < p
        exact (typein_enum (α := β) LT.lt
          ((typein_lt_self i).trans_le hp)).trans_lt (typein_lt_self i)⟩
  let g : leftCut (β := β) p → p.ToType := fun x =>
    enum (α := p.ToType) LT.lt (leftCutIndexCoord p x)
  have hfg : Function.LeftInverse g f := by
    intro i
    apply typein_injective (α := p.ToType) LT.lt
    dsimp [f, g]
    rw [typein_enum_leftCutIndexCoord, typein_enum_leftCutCoord]
  have hgf : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    apply typein_injective (α := β) LT.lt
    dsimp [f, g]
    rw [typein_enum_leftCutCoord, typein_enum_leftCutIndexCoord]
  refine
    { toEquiv := Equiv.mk f g hfg hgf
      map_rel_iff' := ?_ }
  intro i j
  change (f i : β) < (f j : β) ↔ i < j
  rw [← typein_lt_typein (α := β) LT.lt]
  dsimp [f]
  rw [typein_enum_leftCutCoord, typein_enum_leftCutCoord,
    typein_lt_typein (α := p.ToType) LT.lt]

theorem typeLT_leftCut (p : Ordinal) (hp : p ≤ typeLT β) :
    typeLT (leftCut (β := β) p) = p := by
  calc
    typeLT (leftCut (β := β) p) = typeLT p.ToType :=
      (leftCutRelIso p hp).ordinalType_congr.symm
    _ = p := type_toType p

theorem leftCut_disjoint_rightCut (p : Ordinal) :
    Disjoint (leftCut (β := β) p) (rightCut (β := β) p) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change typein LT.lt x < p at hx
  change p ≤ typein LT.lt x at hy
  exact (not_lt_of_ge hy) hx

theorem leftCut_union_rightCut (p : Ordinal) :
    leftCut (β := β) p ∪ rightCut (β := β) p = Set.univ := by
  ext x
  simp only [leftCut, rightCut, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact lt_or_ge _ _

theorem leftCut_lt_rightCut (p : Ordinal) :
    ∀ x ∈ leftCut (β := β) p, ∀ y ∈ rightCut (β := β) p, x < y := by
  intro x hx y hy
  change typein LT.lt x < p at hx
  change p ≤ typein LT.lt y at hy
  rw [← typein_lt_typein LT.lt]
  exact hx.trans_le hy

theorem typeLT_rightCut (p : Ordinal) (hp : p ≤ typeLT β) :
    typeLT (rightCut (β := β) p) = typeLT β - p := by
  have hsum := typeLT_union_of_separated
    (leftCut (β := β) p) (rightCut (β := β) p)
    (leftCut_disjoint_rightCut p) (leftCut_lt_rightCut p)
  rw [leftCut_union_rightCut, typeLT_leftCut p hp] at hsum
  have hsum' : typeLT β = p + typeLT (rightCut (β := β) p) := by
    have huniv : typeLT (Set.univ : Set β) = typeLT β :=
      (RelIso.mk (OrderIso.Set.univ : (Set.univ : Set β) ≃o β).toEquiv
        (fun {_ _} => (OrderIso.Set.univ : (Set.univ : Set β) ≃o β).lt_iff_lt)).ordinalType_congr
    rw [← huniv]
    exact hsum
  exact add_left_cancel (hsum'.symm.trans (Ordinal.add_sub_cancel_of_le hp).symm)

end Cuts

/-! ## Flattening sets of a subtype -/

section Flatten

variable {β : Type} [LinearOrder β] [WellFoundedLT β]

def liftSet (u : Set β) (s : Set u) : Set β := ((↑) : u → β) '' s

noncomputable def liftSetRelIso (u : Set β) (s : Set u) :
    (LT.lt : s → s → Prop) ≃r (LT.lt : liftSet u s → liftSet u s → Prop) := by
  refine
    { toEquiv := Equiv.Set.image ((↑) : u → β) s Subtype.val_injective
      map_rel_iff' := ?_ }
  intro x y
  rfl

theorem typeLT_liftSet (u : Set β) (s : Set u) :
    typeLT (liftSet u s) = typeLT s :=
  (liftSetRelIso u s).ordinalType_congr.symm

theorem liftSet_subset (u : Set β) (s : Set u) : liftSet u s ⊆ u := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

@[simp] theorem liftSet_univ (u : Set β) : liftSet u Set.univ = u := by
  ext x
  constructor
  · intro hx
    exact liftSet_subset u Set.univ hx
  · intro hx
    exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

theorem liftSet_union (u : Set β) (s t : Set u) :
    liftSet u (s ∪ t) = liftSet u s ∪ liftSet u t := by
  exact Set.image_union _ _ _

theorem liftSet_disjoint {u : Set β} {s t : Set u} (h : Disjoint s t) :
    Disjoint (liftSet u s) (liftSet u t) :=
  Set.disjoint_image_of_injective Subtype.val_injective h

theorem liftSet_lt {u : Set β} {s t : Set u}
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∀ x ∈ liftSet u s, ∀ y ∈ liftSet u t, x < y := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact h x hx y hy

def liftList (u : Set β) (ss : List (Set u)) : List (Set β) :=
  ss.map (liftSet u)

theorem unionList_liftList (u : Set β) :
    ∀ ss : List (Set u), unionList (liftList u ss) = liftSet u (unionList ss)
  | [] => by simp [liftList, unionList, liftSet]
  | s :: ss => by
      simp only [liftList, List.map_cons, unionList]
      change liftSet u s ∪ unionList (liftList u ss) =
        liftSet u (s ∪ unionList ss)
      rw [unionList_liftList, liftSet_union]

theorem consecutive_liftList (u : Set β) :
    ∀ {ss : List (Set u)}, Consecutive ss → Consecutive (liftList u ss)
  | [], _ => by simp [liftList, Consecutive]
  | s :: ss, h => by
      simp only [liftList, List.map_cons, Consecutive]
      change Disjoint (liftSet u s) (unionList (liftList u ss)) ∧
        (∀ x ∈ liftSet u s, ∀ y ∈ unionList (liftList u ss), x < y) ∧
        Consecutive (liftList u ss)
      rw [unionList_liftList]
      exact ⟨liftSet_disjoint h.1, liftSet_lt h.2.1,
        consecutive_liftList u h.2.2⟩

theorem mem_liftList {u : Set β} {ss : List (Set u)} {s : Set β}
    (hs : s ∈ liftList u ss) : ∃ t ∈ ss, s = liftSet u t := by
  rw [liftList, List.mem_map] at hs
  obtain ⟨t, ht, hts⟩ := hs
  exact ⟨t, ht, hts.symm⟩

end Flatten

/-! ## Existence of the finite strong-type partition -/

def IsOmegaPowerType {β : Type} [LinearOrder β] [WellFoundedLT β] (s : Set β) : Prop :=
  ∃ e : Ordinal, typeLT s = ω ^ e

theorem omegaPower_exponent_le_of_ambient
    {β : Type} [LinearOrder β] [WellFoundedLT β]
    {s : Set β} {e κ : Ordinal}
    (hs : typeLT s = ω ^ e) (hβ : typeLT β ≤ ω ^ κ) : e ≤ κ := by
  apply (opow_le_opow_iff_right one_lt_omega0).mp
  rw [← hs]
  exact (type_set_le s).trans hβ

def IsOmegaPowerPartition {β : Type} [LinearOrder β] [WellFoundedLT β]
    (ss : List (Set β)) : Prop :=
  Consecutive ss ∧ unionList ss = Set.univ ∧ ∀ s ∈ ss, IsOmegaPowerType s

theorem exists_omegaPowerPartition
    (β : Type) [LinearOrder β] [WellFoundedLT β] :
    ∃ ss : List (Set β), IsOmegaPowerPartition ss := by
  induction htype : typeLT β using WellFoundedLT.induction generalizing β with
  | ind o ih =>
      by_cases ho : o = 0
      · have hempty : IsEmpty β := by
          exact (@type_eq_zero_iff_isEmpty β LT.lt inferInstance).mp
            (htype.trans ho)
        let : IsEmpty β := hempty
        refine ⟨[], ?_⟩
        refine ⟨by simp [Consecutive], ?_, by simp⟩
        ext x
        exact isEmptyElim x
      · let p : Ordinal := ω ^ log ω o
        have hp : p ≤ o := by
          exact opow_log_le_self ω ho
        have hpβ : p ≤ typeLT β := hp.trans_eq htype.symm
        let r : Set β := rightCut (β := β) p
        have hrtype : typeLT r = o - p := by
          exact (typeLT_rightCut p hpβ).trans (congrArg (· - p) htype)
        have hrlt : o - p < o := by
          exact sub_omega0_opow_log_lt ho
        obtain ⟨rs, hrsCon, hrsUnion, hrsPower⟩ :=
          ih (o - p) hrlt r hrtype
        let tail : List (Set β) := liftList r rs
        have htailCon : Consecutive tail := consecutive_liftList r hrsCon
        have htailUnion : unionList tail = r := by
          change unionList (liftList r rs) = r
          rw [unionList_liftList, hrsUnion, liftSet_univ]
        refine ⟨leftCut (β := β) p :: tail, ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [Consecutive]
          refine ⟨?_, ?_, htailCon⟩
          · rw [htailUnion]
            exact leftCut_disjoint_rightCut p
          · rw [htailUnion]
            exact leftCut_lt_rightCut p
        · rw [unionList, htailUnion, leftCut_union_rightCut]
        · intro s hs
          rw [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact ⟨log ω o, typeLT_leftCut p hpβ⟩
          · obtain ⟨t, ht, rfl⟩ := mem_liftList hs
            obtain ⟨e, he⟩ := hrsPower t ht
            exact ⟨e, (typeLT_liftSet r t).trans he⟩

/-- The form used by strong-type constructions: every cell has a finite
consecutive partition into nonzero additive-principal pieces. -/
theorem exists_principalPartition
    (β : Type) [LinearOrder β] [WellFoundedLT β] :
    ∃ ss : List (Set β), Consecutive ss ∧ unionList ss = Set.univ ∧
      ∀ s ∈ ss, IsPrincipal (· + ·) (typeLT s) ∧ typeLT s ≠ 0 := by
  obtain ⟨ss, hcon, hunion, hp⟩ := exists_omegaPowerPartition β
  refine ⟨ss, hcon, hunion, ?_⟩
  intro s hs
  obtain ⟨e, he⟩ := hp s hs
  rw [he]
  exact ⟨isPrincipal_add_omega0_opow e, opow_ne_zero _ omega0_ne_zero⟩

/-! ## Exact reconstruction from full subpieces -/

def interList {β : Type*} (m : Set β) (ss : List (Set β)) : List (Set β) :=
  ss.map (m ∩ ·)

theorem unionList_interList {β : Type*} (m : Set β) :
    ∀ ss : List (Set β), unionList (interList m ss) = m ∩ unionList ss
  | [] => by simp [interList, unionList]
  | s :: ss => by
      simp only [interList, List.map_cons, unionList]
      change m ∩ s ∪ unionList (interList m ss) = m ∩ (s ∪ unionList ss)
      rw [unionList_interList]
      exact (Set.inter_union_distrib_left m s (unionList ss)).symm

theorem interList_forall₂_subset {β : Type*} (m : Set β) :
    ∀ ss : List (Set β), List.Forall₂ (· ⊆ ·) (interList m ss) ss
  | [] => .nil
  | _ :: ss => .cons Set.inter_subset_right (interList_forall₂_subset m ss)

theorem interList_forall₂_typeLT {β : Type*} [LinearOrder β] [WellFoundedLT β]
    (m : Set β) {ss : List (Set β)}
    (h : ∀ s ∈ ss, typeLT ↥(m ∩ s) = typeLT s) :
    List.Forall₂ (fun (s t : Set β) => typeLT s = typeLT t) (interList m ss) ss := by
  induction ss with
  | nil => exact .nil
  | cons s ss ih =>
      exact .cons (h s (by simp))
        (ih (fun t ht => h t (by simp [ht])))

theorem typeLT_univ {β : Type*} [LinearOrder β] [WellFoundedLT β] :
    typeLT (Set.univ : Set β) = typeLT β :=
  (RelIso.mk (OrderIso.Set.univ : (Set.univ : Set β) ≃o β).toEquiv
    (fun {_ _} => (OrderIso.Set.univ : (Set.univ : Set β) ≃o β).lt_iff_lt)).ordinalType_congr

/-- If a set is full on every piece of a finite consecutive partition, then it
has the full order type of the ambient well-order. -/
theorem typeLT_eq_of_full_on_partition
    {β : Type*} [LinearOrder β] [WellFoundedLT β]
    (m : Set β) {ss : List (Set β)}
    (hcon : Consecutive ss) (hunion : unionList ss = Set.univ)
    (hfull : ∀ s ∈ ss, typeLT ↥(m ∩ s) = typeLT s) :
    typeLT m = typeLT β := by
  have hrecon := typeLT_unionList_eq_of_piecewise hcon
    (interList_forall₂_subset m ss) (interList_forall₂_typeLT m hfull)
  rw [unionList_interList, hunion, Set.inter_univ] at hrecon
  exact hrecon.trans typeLT_univ

theorem typeLT_inter_eq_of_full_on_partition
    {β : Type*} [LinearOrder β] [WellFoundedLT β]
    (m d : Set β) {ss : List (Set β)}
    (hcon : Consecutive ss) (hunion : unionList ss = d)
    (hfull : ∀ s ∈ ss, typeLT ↥(m ∩ s) = typeLT s) :
    typeLT ↥(m ∩ d) = typeLT d := by
  have hrecon := typeLT_unionList_eq_of_piecewise hcon
    (interList_forall₂_subset m ss) (interList_forall₂_typeLT m hfull)
  rw [unionList_interList, hunion] at hrecon
  exact hrecon

/-- Ready-to-use cell lemma: choose the canonical finite `ω`-power partition,
and fullness on its pieces is sufficient for exact fullness on the cell. -/
theorem exists_omegaPowerPartition_reconstruct
    (β : Type) [LinearOrder β] [WellFoundedLT β] :
    ∃ ss : List (Set β), Consecutive ss ∧ unionList ss = Set.univ ∧
      (∀ s ∈ ss, IsOmegaPowerType s) ∧
      ∀ m : Set β, (∀ s ∈ ss, typeLT ↥(m ∩ s) = typeLT s) →
        typeLT m = typeLT β := by
  obtain ⟨ss, hcon, hunion, hp⟩ := exists_omegaPowerPartition β
  exact ⟨ss, hcon, hunion, hp,
    fun m hm => typeLT_eq_of_full_on_partition m hcon hunion hm⟩

/-- Ambient-set version.  This directly supplies, for every ordered cell `d`,
a finite consecutive family of `ω`-power pieces covering `d`; exact fullness
on the pieces reconstructs exact fullness on `d`. -/
theorem exists_omegaPowerPartition_reconstruct_set
    {β : Type} [LinearOrder β] [WellFoundedLT β] (d : Set β) :
    ∃ ss : List (Set β), Consecutive ss ∧ unionList ss = d ∧
      (∀ s ∈ ss, IsOmegaPowerType s) ∧
      ∀ m : Set β, (∀ s ∈ ss, typeLT ↥(m ∩ s) = typeLT s) →
        typeLT ↥(m ∩ d) = typeLT d := by
  obtain ⟨rs, hrsCon, hrsUnion, hrsPower⟩ := exists_omegaPowerPartition d
  let ss : List (Set β) := liftList d rs
  have hcon : Consecutive ss := consecutive_liftList d hrsCon
  have hunion : unionList ss = d := by
    change unionList (liftList d rs) = d
    rw [unionList_liftList, hrsUnion, liftSet_univ]
  refine ⟨ss, hcon, hunion, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_liftList hs
    obtain ⟨e, he⟩ := hrsPower t ht
    exact ⟨e, (typeLT_liftSet d t).trans he⟩
  · intro m hm
    exact typeLT_inter_eq_of_full_on_partition m d hcon hunion hm

end CNFStrong


end Erdos118.Reused591
