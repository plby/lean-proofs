/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos921.Tucker
import Mathlib

/-!
# Stable Kneser graphs

This file develops the finite Schrijver construction used for the lower bound
in Erdős Problem 921.  The chromatic lower bound is derived from the finite
Tucker theorem proved in `Tucker.lean`.
-/

open Function Set SimpleGraph
open scoped ENat

namespace Erdos921

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A subset of `Fin N` is cyclically stable if it contains no two cyclically
consecutive elements. -/
def CyclicallyStable {N : ℕ} (S : Finset (Fin N)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S,
    (i : ℕ) + 1 ≠ (j : ℕ) ∧ ¬((i : ℕ) = 0 ∧ (j : ℕ) + 1 = N)

/-- Vertices of the stable Kneser graph. -/
def StableSet (N r : ℕ) :=
  {S : Finset (Fin N) // S.card = r ∧ CyclicallyStable S}

instance (N r : ℕ) : Fintype (StableSet N r) :=
  Fintype.ofInjective (fun S : StableSet N r ↦ S.1) Subtype.val_injective

instance (N r : ℕ) : DecidableEq (StableSet N r) :=
  Classical.decEq _

/-- Schrijver's stable Kneser graph: two stable sets are adjacent exactly when
they are disjoint. -/
def stableKneser (N r : ℕ) : SimpleGraph (StableSet N r) where
  Adj S T := S ≠ T ∧ Disjoint S.1 T.1
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp]
lemma stableKneser_adj {N r : ℕ} (hr : 0 < r) {S T : StableSet N r} :
    (stableKneser N r).Adj S T ↔ Disjoint S.1 T.1 := by
  change (S ≠ T ∧ Disjoint S.1 T.1) ↔ Disjoint S.1 T.1
  rw [and_iff_right_iff_imp]
  intro hdis hST
  subst T
  have hempty : S.1 = ∅ := (Finset.disjoint_self_iff_empty S.1).mp hdis
  have : r = 0 := by rw [← S.2.1, hempty]; simp
  omega

/-! ## Alternating subsequences of a sign vector -/

open Tucker

/-- The Boolean sign attached to a coordinate.  On a consistent sign vector
this is used only at coordinates in one of the two supports. -/
def signAt {N : ℕ} (X : SignVector N) (i : Fin N) : Bool :=
  decide (i ∈ X.pos)

/-- A strictly increasing list of nonzero coordinates whose signs alternate. -/
def IsAlternating {N : ℕ} (X : SignVector N) (l : List (Fin N)) : Prop :=
  l.Pairwise (· < ·) ∧
    (∀ i ∈ l, i ∈ X.pos ∨ i ∈ X.neg) ∧
    l.IsChain (fun i j ↦ signAt X i ≠ signAt X j)

def HasAlternation {N : ℕ} (X : SignVector N) (a : ℕ) : Prop :=
  ∃ l : List (Fin N), l.length = a ∧ IsAlternating X l

lemma hasAlternation_zero {N : ℕ} (X : SignVector N) : HasAlternation X 0 := by
  exact ⟨[], rfl, by simp [IsAlternating]⟩

lemma alternating_length_le {N : ℕ} {X : SignVector N} {l : List (Fin N)}
    (hl : IsAlternating X l) : l.length ≤ N := by
  have hnodup : l.Nodup := hl.1.imp fun hlt ↦ ne_of_lt hlt
  exact hnodup.length_le_card.trans_eq (Fintype.card_fin N)

/-- Maximum length of an alternating subsequence of the nonzero signs. -/
def alternation {N : ℕ} (X : SignVector N) : ℕ :=
  Nat.findGreatest (HasAlternation X) N

lemma alternation_le {N : ℕ} (X : SignVector N) : alternation X ≤ N :=
  Nat.findGreatest_le _

lemma hasAlternation_alternation {N : ℕ} (X : SignVector N) :
    HasAlternation X (alternation X) :=
  Nat.findGreatest_spec (Nat.zero_le N) (hasAlternation_zero X)

lemma le_alternation_of_hasAlternation {N a : ℕ} {X : SignVector N}
    (h : HasAlternation X a) : a ≤ alternation X := by
  apply Nat.le_findGreatest
  · obtain ⟨l, rfl, hl⟩ := h
    exact alternating_length_le hl
  · exact h

lemma signAt_eq_true_iff {N : ℕ} {X : SignVector N} {i : Fin N} :
    signAt X i = true ↔ i ∈ X.pos := by
  simp [signAt]

lemma signAt_eq_false_iff_of_mem {N : ℕ} {X : SignVector N} (hX : X.Consistent)
    {i : Fin N} (hi : i ∈ X.pos ∨ i ∈ X.neg) :
    signAt X i = false ↔ i ∈ X.neg := by
  rw [signAt]
  simp only [decide_eq_false_iff_not]
  constructor
  · intro hip
    exact hi.resolve_left hip
  · intro hin hip
    exact Finset.disjoint_left.mp hX hip hin

lemma signAt_eq_of_le {N : ℕ} {X Y : SignVector N}
    (hX : X.Consistent) (hY : Y.Consistent) (hXY : X ≤ Y)
    {i : Fin N} (hi : i ∈ X.pos ∨ i ∈ X.neg) : signAt X i = signAt Y i := by
  rcases hi with hip | hin
  · have hiY : i ∈ Y.pos := hXY.1 hip
    simp [signAt, hip, hiY]
  · have hiY : i ∈ Y.neg := hXY.2 hin
    have hiXpos : i ∉ X.pos := fun hip ↦ Finset.disjoint_left.mp hX hip hin
    have hiYpos : i ∉ Y.pos := fun hip ↦ Finset.disjoint_left.mp hY hip hiY
    simp [signAt, hiXpos, hiYpos]

lemma signAt_negate {N : ℕ} {X : SignVector N} (hX : X.Consistent)
    {i : Fin N} (hi : i ∈ X.pos ∨ i ∈ X.neg) :
    signAt X.negate i = !(signAt X i) := by
  rcases hi with hip | hin
  · have hin' : i ∉ X.neg := fun hin ↦ Finset.disjoint_left.mp hX hip hin
    simp [signAt, SignVector.negate, hip, hin']
  · have hip' : i ∉ X.pos := fun hip ↦ Finset.disjoint_left.mp hX hip hin
    simp [signAt, SignVector.negate, hip', hin]

lemma IsAlternating.mono {N : ℕ} {X Y : SignVector N} {l : List (Fin N)}
    (hX : X.Consistent) (hY : Y.Consistent) (hXY : X ≤ Y)
    (hl : IsAlternating X l) : IsAlternating Y l := by
  refine ⟨hl.1, ?_, ?_⟩
  · intro i hi
    rcases hl.2.1 i hi with hip | hin
    · exact Or.inl (hXY.1 hip)
    · exact Or.inr (hXY.2 hin)
  · apply hl.2.2.imp_of_mem_imp
    intro i j hi hj hij
    rw [← signAt_eq_of_le hX hY hXY (hl.2.1 i hi),
      ← signAt_eq_of_le hX hY hXY (hl.2.1 j hj)]
    exact hij

lemma IsAlternating.negate {N : ℕ} {X : SignVector N} {l : List (Fin N)}
    (hX : X.Consistent) (hl : IsAlternating X l) : IsAlternating X.negate l := by
  refine ⟨hl.1, ?_, ?_⟩
  · intro i hi
    rcases hl.2.1 i hi with hip | hin
    · exact Or.inr hip
    · exact Or.inl hin
  · apply hl.2.2.imp_of_mem_imp
    intro i j hi hj hij
    rw [signAt_negate hX (hl.2.1 i hi), signAt_negate hX (hl.2.1 j hj)]
    simpa using hij

lemma HasAlternation.mono {N a : ℕ} {X Y : SignVector N}
    (hX : X.Consistent) (hY : Y.Consistent) (hXY : X ≤ Y)
    (h : HasAlternation X a) : HasAlternation Y a := by
  obtain ⟨l, hl, halt⟩ := h
  exact ⟨l, hl, halt.mono hX hY hXY⟩

lemma HasAlternation.negate {N a : ℕ} {X : SignVector N}
    (hX : X.Consistent) (h : HasAlternation X a) : HasAlternation X.negate a := by
  obtain ⟨l, hl, halt⟩ := h
  exact ⟨l, hl, halt.negate hX⟩

lemma alternation_mono {N : ℕ} {X Y : SignVector N}
    (hX : X.Consistent) (hY : Y.Consistent) (hXY : X ≤ Y) :
    alternation X ≤ alternation Y := by
  apply le_alternation_of_hasAlternation
  exact (hasAlternation_alternation X).mono hX hY hXY

lemma alternation_negate {N : ℕ} {X : SignVector N} (hX : X.Consistent) :
    alternation X.negate = alternation X := by
  apply le_antisymm
  · apply le_alternation_of_hasAlternation
    have h := (hasAlternation_alternation X.negate).negate
      (SignVector.consistent_negate hX)
    simpa using h
  · apply le_alternation_of_hasAlternation
    exact (hasAlternation_alternation X).negate hX

lemma alternation_pos_of_ne_zero {N : ℕ} {X : SignVector N}
    (hX : X.Consistent) (hne : X ≠ .zero N) : 0 < alternation X := by
  have hsupp : X.pos.Nonempty ∨ X.neg.Nonempty := by
    by_contra h
    push Not at h
    apply hne
    ext i <;> simp [SignVector.zero, h.1, h.2]
  rcases hsupp with hp | hn
  · obtain ⟨i, hi⟩ := hp
    have hAlt : HasAlternation X 1 := by
      refine ⟨[i], by simp, ?_⟩
      simp [IsAlternating, hi]
    exact Nat.zero_lt_of_lt (le_alternation_of_hasAlternation hAlt)
  · obtain ⟨i, hi⟩ := hn
    have hAlt : HasAlternation X 1 := by
      refine ⟨[i], by simp, ?_⟩
      simp [IsAlternating, hi]
    exact Nat.zero_lt_of_lt (le_alternation_of_hasAlternation hAlt)

def signSupport {N : ℕ} (X : SignVector N) : Finset (Fin N) :=
  X.pos ∪ X.neg

lemma mem_signSupport {N : ℕ} {X : SignVector N} {i : Fin N} :
    i ∈ signSupport X ↔ i ∈ X.pos ∨ i ∈ X.neg := by
  simp [signSupport]

lemma signSupport_nonempty_of_ne_zero {N : ℕ} {X : SignVector N}
    (hne : X ≠ .zero N) : (signSupport X).Nonempty := by
  by_contra h
  have hs : signSupport X = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hp : X.pos = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨i, hi⟩
    have : i ∈ signSupport X := mem_signSupport.mpr (Or.inl hi)
    simpa [hs] using this
  have hn : X.neg = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨i, hi⟩
    have : i ∈ signSupport X := mem_signSupport.mpr (Or.inr hi)
    simpa [hs] using this
  apply hne
  ext i <;> simp [SignVector.zero, hp, hn]

def firstCoord {N : ℕ} (X : SignVector N) (h : (signSupport X).Nonempty) : Fin N :=
  (signSupport X).min' h

def firstSign {N : ℕ} (X : SignVector N) (h : (signSupport X).Nonempty) : Bool :=
  signAt X (firstCoord X h)

lemma firstCoord_mem {N : ℕ} (X : SignVector N) (h : (signSupport X).Nonempty) :
    firstCoord X h ∈ signSupport X := Finset.min'_mem _ _

lemma firstCoord_le_of_mem {N : ℕ} (X : SignVector N)
    (h : (signSupport X).Nonempty) {i : Fin N} (hi : i ∈ signSupport X) :
    firstCoord X h ≤ i := Finset.min'_le _ _ hi

lemma IsAlternating.cons_of_lt {N : ℕ} {X : SignVector N}
    {i a : Fin N} {t : List (Fin N)} (hi : i ∈ signSupport X) (hia : i < a)
    (hsign : signAt X i ≠ signAt X a) (hl : IsAlternating X (a :: t)) :
    IsAlternating X (i :: a :: t) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, hl.1⟩
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hia
    · exact hia.trans ((List.pairwise_cons.mp hl.1).1 b hb)
  · intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact mem_signSupport.mp hi
    · exact hl.2.1 b (List.mem_cons.mpr hb)
  · exact hl.2.2.cons_of_ne_nil (by simp) hsign

lemma maximal_alternating_head_sign {N : ℕ} {X : SignVector N}
    (hX : X.Consistent) (hne : X ≠ .zero N) {l : List (Fin N)}
    (hlen : l.length = alternation X) (hl : IsAlternating X l) :
    l ≠ [] ∧ signAt X (l.head (by
      intro hnil
      subst l
      simp only [List.length_nil] at hlen
      have := alternation_pos_of_ne_zero hX hne
      omega)) = firstSign X (signSupport_nonempty_of_ne_zero hne) := by
  have haltpos := alternation_pos_of_ne_zero hX hne
  have hlnil : l ≠ [] := by
    intro hnil
    subst l
    simp only [List.length_nil] at hlen
    omega
  refine ⟨hlnil, ?_⟩
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hlnil
  let hsupp := signSupport_nonempty_of_ne_zero hne
  let m := firstCoord X hsupp
  have hma : m ≤ a := firstCoord_le_of_mem X hsupp
    (mem_signSupport.mpr (hl.2.1 a (by simp)))
  by_contra hsign
  have hmal : m < a := by
    exact lt_of_le_of_ne hma (fun hmaeq ↦ hsign (by simp [firstSign, m, hmaeq]))
  have hnew : IsAlternating X (m :: a :: t) := by
    apply IsAlternating.cons_of_lt (firstCoord_mem X hsupp) hmal
    · simpa [firstSign, m] using Ne.symm hsign
    · exact hl
  have hhas : HasAlternation X ((a :: t).length + 1) := by
    exact ⟨m :: a :: t, by simp, hnew⟩
  have hle := le_alternation_of_hasAlternation hhas
  rw [← hlen] at hle
  omega

@[simp] lemma signSupport_negate {N : ℕ} (X : SignVector N) :
    signSupport X.negate = signSupport X := by
  simp [signSupport, SignVector.negate, Finset.union_comm]

lemma firstSign_negate {N : ℕ} {X : SignVector N} (hX : X.Consistent)
    (h : (signSupport X).Nonempty) (h' : (signSupport X.negate).Nonempty) :
    firstSign X.negate h' = !(firstSign X h) := by
  have hcoord : firstCoord X.negate h' = firstCoord X h := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (by
        simpa using firstCoord_mem X h)
    · exact Finset.min'_le _ _ (by
        simpa using firstCoord_mem X.negate h')
  unfold firstSign
  rw [hcoord]
  exact signAt_negate hX (mem_signSupport.mp (firstCoord_mem X h))

lemma ne_zero_of_le_of_ne_zero {N : ℕ} {X Y : SignVector N}
    (hXY : X ≤ Y) (hX : X ≠ .zero N) : Y ≠ .zero N := by
  intro hY
  apply hX
  ext i
  · constructor
    · intro hi
      have := hXY.1 hi
      simpa [hY, SignVector.zero] using this
    · simp [SignVector.zero]
  · constructor
    · intro hi
      have := hXY.2 hi
      simpa [hY, SignVector.zero] using this
    · simp [SignVector.zero]

lemma firstSign_eq_of_le_of_alternation_eq {N : ℕ} {X Y : SignVector N}
    (hX : X.Consistent) (hY : Y.Consistent) (hXY : X ≤ Y)
    (hXne : X ≠ .zero N) (halt : alternation X = alternation Y) :
    firstSign X (signSupport_nonempty_of_ne_zero hXne) =
      firstSign Y (signSupport_nonempty_of_ne_zero
        (ne_zero_of_le_of_ne_zero hXY hXne)) := by
  obtain ⟨l, hlen, hl⟩ := hasAlternation_alternation X
  have hheadX := (maximal_alternating_head_sign hX hXne hlen hl).2
  have hlY := hl.mono hX hY hXY
  have hYne := ne_zero_of_le_of_ne_zero hXY hXne
  have hheadY :=
    (maximal_alternating_head_sign hY hYne (hlen.trans halt) hlY).2
  have hlnil := (maximal_alternating_head_sign hX hXne hlen hl).1
  have hmem : l.head hlnil ∈ X.pos ∨ l.head hlnil ∈ X.neg :=
    hl.2.1 _ (List.head_mem hlnil)
  calc
    firstSign X (signSupport_nonempty_of_ne_zero hXne) =
        signAt X (l.head hlnil) := hheadX.symm
    _ = signAt Y (l.head hlnil) := signAt_eq_of_le hX hY hXY hmem
    _ = firstSign Y (signSupport_nonempty_of_ne_zero hYne) := hheadY

lemma bool_even_chain_filter_lengths (r : ℕ) {l : List Bool}
    (hchain : l.IsChain (· ≠ ·)) (hlen : l.length = 2 * r) :
    (l.filter (· = true)).length = r ∧
      (l.filter (· = false)).length = r := by
  induction r generalizing l with
  | zero =>
      have : l = [] := List.length_eq_zero_iff.mp (by omega)
      subst l
      simp
  | succ r ih =>
      cases l with
      | nil => simp at hlen
      | cons b l =>
          cases l with
          | nil => simp at hlen; omega
          | cons c t =>
              have hbc : b ≠ c := hchain.rel
              have hrest : t.IsChain (· ≠ ·) := hchain.tail.tail
              have hlenrest : t.length = 2 * r := by simp at hlen; omega
              have hcounts := ih hrest hlenrest
              cases b <;> cases c <;> simp_all

lemma bool_even_chain_head_ne_last (r : ℕ) {l : List Bool}
    (hr : 0 < r) (hchain : l.IsChain (· ≠ ·)) (hlen : l.length = 2 * r) :
    l.head (by intro h; subst l; simp only [List.length_nil] at hlen; omega) ≠
      l.getLast (by intro h; subst l; simp only [List.length_nil] at hlen; omega) := by
  induction r using Nat.strong_induction_on generalizing l with
  | h r ih =>
      cases r with
      | zero => omega
      | succ r =>
          cases l with
          | nil => simp at hlen
          | cons b l =>
              cases l with
              | nil => simp at hlen; omega
              | cons c t =>
                  have hbc : b ≠ c := hchain.rel
                  by_cases hr0 : r = 0
                  · subst r
                    have ht : t = [] := by simpa using hlen
                    subst t
                    simpa using hbc
                  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
                    have htlen : t.length = 2 * r := by simp at hlen; omega
                    have htne : t ≠ [] := by
                      intro ht
                      subst t
                      simp at htlen
                      omega
                    obtain ⟨d, u, rfl⟩ := List.exists_cons_of_ne_nil htne
                    have hcd : c ≠ d := hchain.tail.rel
                    have hbd : b = d := by
                      cases b <;> cases c <;> cases d <;> simp_all
                    have htailchain : (d :: u).IsChain (· ≠ ·) := hchain.tail.tail
                    have htail := ih r (by omega) hrpos htailchain htlen
                    simpa [hbd] using htail

lemma sign_ne_of_consecutive_mem_sorted {N : ℕ} {X : SignVector N}
    {l : List (Fin N)} (hsorted : l.Pairwise (· < ·))
    (hchain : l.IsChain fun i j ↦ signAt X i ≠ signAt X j)
    {i j : Fin N} (hi : i ∈ l) (hj : j ∈ l) (hsucc : (i : ℕ) + 1 = (j : ℕ)) :
    signAt X i ≠ signAt X j := by
  obtain ⟨p, hp⟩ := List.mem_iff_get.mp hi
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp hj
  have hpqne : p ≠ q := by
    intro hpq
    subst q
    have hij : i = j := hp.symm.trans hq
    have := congrArg Fin.val hij
    omega
  have hpq : p < q := by
    rcases lt_or_gt_of_ne hpqne with hpq | hqp
    · exact hpq
    · have hji : j < i := by
        calc
          j = l.get q := hq.symm
          _ < l.get p := hsorted.rel_get_of_lt hqp
          _ = i := hp
      omega
  have hqval : (q : ℕ) = (p : ℕ) + 1 := by
    by_contra hne
    have hgap : (p : ℕ) + 1 < (q : ℕ) := by omega
    let u : Fin l.length :=
      ⟨(p : ℕ) + 1, hgap.trans q.isLt⟩
    have hpu : i < l.get u := by
      calc
        i = l.get p := hp.symm
        _ < l.get u := hsorted.rel_get_of_lt (show p < u by
          change (p : ℕ) < (u : ℕ)
          dsimp only [u]
          omega)
    have huq : l.get u < j := by
      calc
        l.get u < l.get q := hsorted.rel_get_of_lt (show u < q by
          change (u : ℕ) < (q : ℕ)
          dsimp only [u]
          exact hgap)
        _ = j := hq
    omega
  have hc := (List.isChain_iff_getElem.mp hchain) (p : ℕ) (by omega)
  have hp' : l[(p : ℕ)] = i := by simpa using hp
  have hq' : l[(p : ℕ) + 1] = j := by
    have : l[(q : ℕ)] = j := by simpa using hq
    simpa [hqval] using this
  simpa [hp', hq'] using hc

lemma sign_ne_of_wrap_mem_sorted_even {N r : ℕ} {X : SignVector N}
    {l : List (Fin N)} (hr : 0 < r) (hsorted : l.Pairwise (· < ·))
    (hchain : l.IsChain fun i j ↦ signAt X i ≠ signAt X j)
    (hlen : l.length = 2 * r) {i j : Fin N} (hi : i ∈ l) (hj : j ∈ l)
    (hi0 : (i : ℕ) = 0) (hjlast : (j : ℕ) + 1 = N) :
    signAt X i ≠ signAt X j := by
  have hnodup : l.Nodup := hsorted.imp fun hlt ↦ ne_of_lt hlt
  have hN : l.length ≤ N := by
    simpa using hnodup.length_le_card
  have hij : i < j := by
    change (i : ℕ) < (j : ℕ)
    omega
  obtain ⟨p, hp⟩ := List.mem_iff_get.mp hi
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp hj
  have hpq : p < q := by
    by_contra hpqn
    have hqp : q ≤ p := le_of_not_gt hpqn
    rcases hqp.eq_or_lt with hqp | hqp
    · have hij' : i = j := hp.symm.trans (hqp ▸ hq)
      exact (ne_of_lt hij) hij'
    · have hji : j < i := by
        calc
          j = l.get q := hq.symm
          _ < l.get p := hsorted.rel_get_of_lt hqp
          _ = i := hp
      exact (not_lt_of_ge (le_of_lt hij)) hji
  have hpzero : (p : ℕ) = 0 := by
    by_contra hp0
    let z : Fin l.length := ⟨0, by omega⟩
    have hzi : l.get z < i := by
      calc
        l.get z < l.get p := hsorted.rel_get_of_lt (show z < p by
          change (z : ℕ) < (p : ℕ)
          simp [z]
          omega)
        _ = i := hp
    omega
  have hqlast : (q : ℕ) + 1 = l.length := by
    by_contra hql
    have hqlt : (q : ℕ) + 1 < l.length := by omega
    let z : Fin l.length := ⟨(q : ℕ) + 1, hqlt⟩
    have hjz : j < l.get z := by
      calc
        j = l.get q := hq.symm
        _ < l.get z := hsorted.rel_get_of_lt (show q < z by
          change (q : ℕ) < (z : ℕ)
          simp [z])
    have hzlt : (l.get z : ℕ) < N := (l.get z).isLt
    omega
  have hlnil : l ≠ [] := by
    intro hnil
    subst l
    simp at hlen
    omega
  have hhead : l.head hlnil = i := by
    rw [List.head_eq_getElem]
    have hp' : l[(p : ℕ)] = i := by simpa using hp
    simpa [hpzero] using hp'
  have hlast : l.getLast hlnil = j := by
    rw [List.getLast_eq_getElem]
    have hq' : l[(q : ℕ)] = j := by simpa using hq
    have hqsub : (q : ℕ) = l.length - 1 := by omega
    simpa [hqsub] using hq'
  let signs := l.map (signAt X)
  have hsignChain : signs.IsChain (· ≠ ·) := by
    apply List.isChain_map_of_isChain (signAt X) (fun _ _ h ↦ h)
    exact hchain
  have hsignLen : signs.length = 2 * r := by simpa [signs] using hlen
  have hend := bool_even_chain_head_ne_last r hr hsignChain hsignLen
  have hend' : signAt X (l.head hlnil) ≠ signAt X (l.getLast hlnil) := by
    simpa [signs] using hend
  simpa [hhead, hlast] using hend'

def signClass {N : ℕ} (X : SignVector N) (l : List (Fin N)) (b : Bool) :
    Finset (Fin N) :=
  (l.filter fun i ↦ signAt X i = b).toFinset

lemma mem_signClass {N : ℕ} {X : SignVector N} {l : List (Fin N)}
    {b : Bool} {i : Fin N} :
    i ∈ signClass X l b ↔ i ∈ l ∧ signAt X i = b := by
  simp [signClass]

lemma signClass_card {N r : ℕ} {X : SignVector N} {l : List (Fin N)}
    (hl : IsAlternating X l) (hlen : l.length = 2 * r) (b : Bool) :
    (signClass X l b).card = r := by
  have hnodup : l.Nodup := hl.1.imp fun hlt ↦ ne_of_lt hlt
  have hfilterNodup : (l.filter fun i ↦ signAt X i = b).Nodup :=
    hnodup.filter _
  rw [signClass, List.toFinset_card_of_nodup hfilterNodup]
  let signs := l.map (signAt X)
  have hsignChain : signs.IsChain (· ≠ ·) := by
    apply List.isChain_map_of_isChain (signAt X) (fun _ _ h ↦ h)
    exact hl.2.2
  have hsignLen : signs.length = 2 * r := by simpa [signs] using hlen
  have hcounts := bool_even_chain_filter_lengths r hsignChain hsignLen
  cases b
  · have h := hcounts.2
    rw [List.filter_map] at h
    simpa [signs, Function.comp_def] using h
  · have h := hcounts.1
    rw [List.filter_map] at h
    simpa [signs, Function.comp_def] using h

lemma signClass_cyclicallyStable {N r : ℕ} {X : SignVector N}
    {l : List (Fin N)} (hr : 0 < r) (hl : IsAlternating X l)
    (hlen : l.length = 2 * r) (b : Bool) : CyclicallyStable (signClass X l b) := by
  intro i hi j hj
  obtain ⟨hil, hib⟩ := mem_signClass.mp hi
  obtain ⟨hjl, hjb⟩ := mem_signClass.mp hj
  constructor
  · intro hsucc
    exact sign_ne_of_consecutive_mem_sorted hl.1 hl.2.2 hil hjl hsucc
      (hib.trans hjb.symm)
  · rintro ⟨hi0, hjlast⟩
    exact sign_ne_of_wrap_mem_sorted_even hr hl.1 hl.2.2 hlen hil hjl hi0 hjlast
      (hib.trans hjb.symm)

lemma signClass_subset_support {N : ℕ} {X : SignVector N} (hX : X.Consistent)
    {l : List (Fin N)} (hl : IsAlternating X l) (b : Bool) :
    signClass X l b ⊆ if b then X.pos else X.neg := by
  intro i hi
  obtain ⟨hil, hib⟩ := mem_signClass.mp hi
  have himem := hl.2.1 i hil
  cases b
  · simp only [Bool.false_eq, ↓reduceIte]
    exact (signAt_eq_false_iff_of_mem hX himem).mp hib
  · simp only [↓reduceIte]
    exact signAt_eq_true_iff.mp hib

lemma stableSets_of_alternation {N r : ℕ} {X : SignVector N}
    (hX : X.Consistent) (hr : 0 < r) (halt : 2 * r ≤ alternation X) :
    (∃ S : StableSet N r, S.1 ⊆ X.pos) ∧
      ∃ T : StableSet N r, T.1 ⊆ X.neg := by
  obtain ⟨l, hlen, hl⟩ := hasAlternation_alternation X
  let u := l.take (2 * r)
  have hulength : u.length = 2 * r := by
    simp [u, List.length_take, hlen, Nat.min_eq_left halt]
  have hu : IsAlternating X u := by
    refine ⟨hl.1.take, ?_, hl.2.2.take _⟩
    intro i hi
    exact hl.2.1 i (List.mem_of_mem_take hi)
  let P := signClass X u true
  let M := signClass X u false
  have hPcard : P.card = r := signClass_card hu hulength true
  have hMcard : M.card = r := signClass_card hu hulength false
  have hPstable : CyclicallyStable P := signClass_cyclicallyStable hr hu hulength true
  have hMstable : CyclicallyStable M := signClass_cyclicallyStable hr hu hulength false
  refine ⟨⟨⟨P, hPcard, hPstable⟩, ?_⟩, ⟨⟨M, hMcard, hMstable⟩, ?_⟩⟩
  · simpa [P] using signClass_subset_support hX hu true
  · simpa [M] using signClass_subset_support hX hu false

/-! ## The Schrijver--Tucker labeling -/

/-- Stable vertices contained in the positive (`true`) or negative (`false`)
support of a sign vector. -/
def sideVertices {N r : ℕ} (X : SignVector N) (b : Bool) :
    Finset (StableSet N r) :=
  Finset.univ.filter fun S ↦ S.1 ⊆ if b then X.pos else X.neg

lemma mem_sideVertices {N r : ℕ} {X : SignVector N} {b : Bool}
    {S : StableSet N r} :
    S ∈ sideVertices X b ↔ S.1 ⊆ if b then X.pos else X.neg := by
  simp [sideVertices]

@[simp]
lemma sideVertices_negate {N r : ℕ} (X : SignVector N) (b : Bool) :
    sideVertices (r := r) X.negate b = sideVertices X (!b) := by
  cases b <;> ext S <;> simp [sideVertices, SignVector.negate]

/-- The set of colors used on stable vertices lying in one signed support. -/
def sideColors {N r c : ℕ} (C : (stableKneser N r).Coloring (Fin c))
    (X : SignVector N) (b : Bool) : Finset ℕ :=
  (sideVertices (r := r) X b).image fun S ↦ (C S : ℕ)

@[simp]
lemma sideColors_negate {N r c : ℕ}
    (C : (stableKneser N r).Coloring (Fin c)) (X : SignVector N) (b : Bool) :
    sideColors C X.negate b = sideColors C X (!b) := by
  simp [sideColors]

/-- Least color used on one side, with default value zero when that side has
no stable vertex.  The default is harmless and makes the labeling total even
on inconsistent ambient sign vectors. -/
def sideColorMin {N r c : ℕ} (C : (stableKneser N r).Coloring (Fin c))
    (X : SignVector N) (b : Bool) : ℕ :=
  if h : (sideColors C X b).Nonempty then (sideColors C X b).min' h else 0

@[simp]
lemma sideColorMin_negate {N r c : ℕ}
    (C : (stableKneser N r).Coloring (Fin c)) (X : SignVector N) (b : Bool) :
    sideColorMin C X.negate b = sideColorMin C X (!b) := by
  simp only [sideColorMin, sideColors_negate]

lemma exists_sideVertex_color_eq_min {N r c : ℕ}
    (C : (stableKneser N r).Coloring (Fin c)) {X : SignVector N} {b : Bool}
    (hside : (sideVertices (r := r) X b).Nonempty) :
    ∃ S : StableSet N r,
      S ∈ sideVertices X b ∧ (C S : ℕ) = sideColorMin C X b := by
  have hcolors : (sideColors C X b).Nonempty := by
    exact hside.image fun S ↦ (C S : ℕ)
  have hmem : (sideColors C X b).min' hcolors ∈ sideColors C X b :=
    Finset.min'_mem _ _
  change (sideColors C X b).min' hcolors ∈
    (sideVertices (r := r) X b).image (fun S ↦ (C S : ℕ)) at hmem
  obtain ⟨S, hS, hcolor⟩ := Finset.mem_image.mp hmem
  refine ⟨S, hS, ?_⟩
  simpa [sideColorMin, hcolors] using hcolor

lemma sideColorMin_lt {N r c : ℕ} (hc : 0 < c)
    (C : (stableKneser N r).Coloring (Fin c)) (X : SignVector N) (b : Bool) :
    sideColorMin C X b < c := by
  by_cases hcolors : (sideColors C X b).Nonempty
  · have hmem := Finset.min'_mem (sideColors C X b) hcolors
    obtain ⟨S, -, hval⟩ := Finset.mem_image.mp hmem
    rw [sideColorMin, dif_pos hcolors]
    rw [← hval]
    exact (C S).isLt
  · simp [sideColorMin, hcolors, hc]

lemma sideColorMin_ne {N r c : ℕ} (hr : 0 < r)
    (C : (stableKneser N r).Coloring (Fin c)) {X : SignVector N}
    (hX : X.Consistent) (halt : 2 * r ≤ alternation X) :
    sideColorMin C X true ≠ sideColorMin C X false := by
  obtain ⟨⟨S, hSsub⟩, ⟨T, hTsub⟩⟩ := stableSets_of_alternation hX hr halt
  have hSmem : S ∈ sideVertices X true := by
    simpa [mem_sideVertices] using hSsub
  have hTmem : T ∈ sideVertices X false := by
    simpa [mem_sideVertices] using hTsub
  obtain ⟨S', hS'mem, hS'color⟩ :=
    exists_sideVertex_color_eq_min C (X := X) (b := true) ⟨S, hSmem⟩
  obtain ⟨T', hT'mem, hT'color⟩ :=
    exists_sideVertex_color_eq_min C (X := X) (b := false) ⟨T, hTmem⟩
  have hS'sub : S'.1 ⊆ X.pos := by
    exact (mem_sideVertices (X := X) (b := true)).mp hS'mem
  have hT'sub : T'.1 ⊆ X.neg := by
    exact (mem_sideVertices (X := X) (b := false)).mp hT'mem
  have hdis : Disjoint S'.1 T'.1 := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    exact Finset.disjoint_left.mp hX (hS'sub hiS) (hT'sub hiT)
  intro hmin
  have hcolor : C S' = C T' := by
    apply Fin.ext
    exact hS'color.trans (hmin.trans hT'color.symm)
  exact C.valid ((stableKneser_adj hr).mpr hdis) hcolor

lemma sideVertices_nonempty_of_alternation {N r : ℕ} (hr : 0 < r)
    {X : SignVector N} (hX : X.Consistent) (halt : 2 * r ≤ alternation X)
    (b : Bool) : (sideVertices (r := r) X b).Nonempty := by
  obtain ⟨⟨P, hP⟩, ⟨M, hM⟩⟩ := stableSets_of_alternation hX hr halt
  cases b
  · exact ⟨M, mem_sideVertices.mpr (by simpa using hM)⟩
  · exact ⟨P, mem_sideVertices.mpr (by simpa using hP)⟩

/-- The side with the larger of the two least colors. -/
def preferredSide {N r c : ℕ} (C : (stableKneser N r).Coloring (Fin c))
    (X : SignVector N) : Bool :=
  decide (sideColorMin C X false < sideColorMin C X true)

lemma sideColorMin_preferredSide_eq_max {N r c : ℕ}
    (C : (stableKneser N r).Coloring (Fin c)) {X : SignVector N}
    (hne : sideColorMin C X true ≠ sideColorMin C X false) :
    sideColorMin C X (preferredSide C X) =
      max (sideColorMin C X true) (sideColorMin C X false) := by
  rcases lt_or_gt_of_ne hne with hpm | hmp
  · have hnmp : ¬sideColorMin C X false < sideColorMin C X true :=
      not_lt_of_ge hpm.le
    simp [preferredSide, hnmp, max_eq_right hpm.le]
  · simp [preferredSide, hmp, max_eq_left hmp.le]

lemma disjoint_opposite_sides_of_le {N : ℕ} {X Y : SignVector N}
    (hY : Y.Consistent) (hXY : X ≤ Y) (b : Bool) :
    Disjoint (if b then X.pos else X.neg)
      (if !b then Y.pos else Y.neg) := by
  cases b
  · simp only [Bool.false_eq, Bool.not_false, ↓reduceIte]
    exact hY.symm.mono hXY.2 fun _ h ↦ h
  · simp only [Bool.not_true, ↓reduceIte]
    exact hY.mono hXY.1 fun _ h ↦ h

/-- The signed label used in Schrijver's Tucker argument.  Low-alternation
vectors use magnitudes `0, ..., 2r-2`.  In the high-alternation case the
larger of the two distinct side minima is positive, so the magnitudes
`2r-1, ..., 2r+d-2` suffice.  Altogether this uses only `2r+d-1`
magnitudes, exactly the range of the deleted-origin Tucker lemma. -/
def schrijverLabel {r d : ℕ} (hr : 0 < r)
    (C : (stableKneser (2 * r + d) r).Coloring (Fin (d + 1)))
    (X : SignVector (2 * r + d)) : Atom (2 * r + d - 1) :=
  if hX : X = .zero (2 * r + d) then
    (⟨0, by omega⟩, false)
  else if hlow : alternation X < 2 * r then
    (⟨alternation X - 1, by omega⟩,
      firstSign X (signSupport_nonempty_of_ne_zero hX))
  else
    (⟨2 * r - 2 + max (sideColorMin C X true) (sideColorMin C X false), by
        have hp := sideColorMin_lt (by omega : 0 < d + 1) C X true
        have hm := sideColorMin_lt (by omega : 0 < d + 1) C X false
        have hmax : max (sideColorMin C X true) (sideColorMin C X false) < d + 1 :=
          (max_lt_iff).mpr ⟨hp, hm⟩
        omega⟩,
      preferredSide C X)

lemma schrijverLabel_antipodal {r d : ℕ} (hr : 0 < r)
    (C : (stableKneser (2 * r + d) r).Coloring (Fin (d + 1))) :
    ∀ X : SignVector (2 * r + d), X.Consistent → X ≠ .zero (2 * r + d) →
      schrijverLabel hr C X.negate = Atom.negate (schrijverLabel hr C X) := by
  intro X hX hXne
  have hnegne : X.negate ≠ .zero (2 * r + d) := by
    simpa using hXne
  have halt : alternation X.negate = alternation X := alternation_negate hX
  by_cases hlow : alternation X < 2 * r
  · simp only [schrijverLabel, hXne, hnegne, ↓reduceDIte, hlow, halt,
      Atom.negate]
    congr 1
    exact firstSign_negate hX _ _
  · have hhigh : 2 * r ≤ alternation X := by omega
    have hmins := sideColorMin_ne hr C hX hhigh
    simp only [schrijverLabel, hXne, hnegne, ↓reduceDIte, hlow, halt,
      preferredSide, sideColorMin_negate, Bool.not_true, Bool.not_false, Atom.negate]
    congr 1
    · simp [Nat.max_comm]
    · let p := sideColorMin C X true
      let m := sideColorMin C X false
      have hpm : p ≠ m := hmins
      change decide (p < m) = !(decide (m < p))
      rcases lt_or_gt_of_ne hpm with hlt | hgt
      · simp [hlt, not_lt_of_ge hlt.le]
      · simp [hgt, not_lt_of_ge hgt.le]

/-- Schrijver's lower bound in the parameterization used for Problem 921:
the stable Kneser graph on `2r+d` points is not colorable with `d+1`
colors. -/
theorem stableKneser_not_colorable {r d : ℕ} (hr : 0 < r) :
    ¬(stableKneser (2 * r + d) r).Colorable (d + 1) := by
  rintro ⟨C⟩
  obtain ⟨X, Y, hX, hY, hXne, hYne, hXY, hcomp⟩ :=
    finite_tucker_nonzero (by omega : 0 < 2 * r + d)
      (schrijverLabel hr C) (schrijverLabel_antipodal hr C)
  have hmono : alternation X ≤ alternation Y := alternation_mono hX hY hXY
  by_cases hXlow : alternation X < 2 * r
  · by_cases hYlow : alternation Y < 2 * r
    · have hmag := congrArg
        (fun a : Atom (2 * r + d - 1) ↦ (a.1 : ℕ)) hcomp
      simp only [schrijverLabel, hXne, hYne, ↓reduceDIte, hXlow, hYlow,
        Atom.negate] at hmag
      have hXpos := alternation_pos_of_ne_zero hX hXne
      have halt : alternation X = alternation Y := by omega
      have hfirst := firstSign_eq_of_le_of_alternation_eq hX hY hXY hXne halt
      have hsign := congrArg (fun a : Atom (2 * r + d - 1) ↦ a.2) hcomp
      simp only [schrijverLabel, hXne, hYne, ↓reduceDIte, hXlow, hYlow,
        Atom.negate] at hsign
      rw [hfirst] at hsign
      cases firstSign Y
          (signSupport_nonempty_of_ne_zero (ne_zero_of_le_of_ne_zero hXY hXne)) <;>
        simp at hsign
    · have hYhigh : 2 * r ≤ alternation Y := by omega
      have hminsY := sideColorMin_ne hr C hY hYhigh
      have hmaxpos : 0 < max (sideColorMin C Y true) (sideColorMin C Y false) := by
        rcases lt_or_gt_of_ne hminsY with hlt | hgt
        · rw [max_eq_right hlt.le]
          omega
        · rw [max_eq_left hgt.le]
          omega
      have hmag := congrArg
        (fun a : Atom (2 * r + d - 1) ↦ (a.1 : ℕ)) hcomp
      simp only [schrijverLabel, hXne, hYne, ↓reduceDIte, hXlow, hYlow,
        Atom.negate] at hmag
      omega
  · have hXhigh : 2 * r ≤ alternation X := by omega
    have hYhigh : 2 * r ≤ alternation Y := hXhigh.trans hmono
    have hYlow : ¬alternation Y < 2 * r := by omega
    have hminsX := sideColorMin_ne hr C hX hXhigh
    have hminsY := sideColorMin_ne hr C hY hYhigh
    have hmag := congrArg
      (fun a : Atom (2 * r + d - 1) ↦ (a.1 : ℕ)) hcomp
    simp only [schrijverLabel, hXne, hYne, ↓reduceDIte, hXlow, hYlow,
      Atom.negate] at hmag
    have hmax :
        max (sideColorMin C X true) (sideColorMin C X false) =
          max (sideColorMin C Y true) (sideColorMin C Y false) := by
      omega
    have hsign := congrArg (fun a : Atom (2 * r + d - 1) ↦ a.2) hcomp
    simp only [schrijverLabel, hXne, hYne, ↓reduceDIte, hXlow, hYlow,
      Atom.negate] at hsign
    have hopposite : preferredSide C Y = !(preferredSide C X) := by
      cases hx : preferredSide C X <;> cases hy : preferredSide C Y <;>
        simp_all
    have hsideX := sideVertices_nonempty_of_alternation hr hX hXhigh
      (preferredSide C X)
    have hsideY := sideVertices_nonempty_of_alternation hr hY hYhigh
      (preferredSide C Y)
    obtain ⟨S, hSmem, hScolor⟩ :=
      exists_sideVertex_color_eq_min C hsideX
    obtain ⟨T, hTmem, hTcolor⟩ :=
      exists_sideVertex_color_eq_min C hsideY
    have hSsub : S.1 ⊆ if preferredSide C X then X.pos else X.neg :=
      mem_sideVertices.mp hSmem
    have hTsub : T.1 ⊆ if !(preferredSide C X) then Y.pos else Y.neg := by
      simpa [hopposite] using (mem_sideVertices.mp hTmem)
    have hdis : Disjoint S.1 T.1 :=
      (disjoint_opposite_sides_of_le hY hXY (preferredSide C X)).mono
        hSsub hTsub
    have hSmin := sideColorMin_preferredSide_eq_max C hminsX
    have hTmin := sideColorMin_preferredSide_eq_max C hminsY
    have hcolorVal : (C S : ℕ) = (C T : ℕ) :=
      hScolor.trans (hSmin.trans (hmax.trans (hTmin.symm.trans hTcolor.symm)))
    have hcolor : C S = C T := Fin.ext hcolorVal
    exact C.valid ((stableKneser_adj hr).mpr hdis) hcolor

/-! ## The explicit upper coloring -/

lemma stableSet_nonempty {N r : ℕ} (hr : 0 < r) (S : StableSet N r) :
    S.1.Nonempty := by
  rw [← Finset.card_pos, S.2.1]
  exact hr

/-- Color a stable `r`-set by its least element, with all least elements at
least `d+1` merged into the final color. -/
def stableKneserColor {r d : ℕ} (hr : 0 < r) :
    StableSet (2 * r + d) r → Fin (d + 2) := fun S ↦
  ⟨min ((S.1.min' (stableSet_nonempty hr S) : Fin (2 * r + d)) : ℕ) (d + 1), by
    omega⟩

lemma stableKneserColor_proper {r d : ℕ} (hr : 0 < r)
    {S T : StableSet (2 * r + d) r}
    (hST : (stableKneser (2 * r + d) r).Adj S T) :
    stableKneserColor hr S ≠ stableKneserColor hr T := by
  let smin := S.1.min' (stableSet_nonempty hr S)
  let tmin := T.1.min' (stableSet_nonempty hr T)
  have hsmin : smin ∈ S.1 := Finset.min'_mem _ _
  have htmin : tmin ∈ T.1 := Finset.min'_mem _ _
  have hdis : Disjoint S.1 T.1 := (stableKneser_adj hr).mp hST
  intro heq
  have hval : min (smin : ℕ) (d + 1) = min (tmin : ℕ) (d + 1) := by
    exact congrArg Fin.val heq
  by_cases hs : (smin : ℕ) < d + 1
  · have ht : (tmin : ℕ) < d + 1 := by
      by_contra ht
      rw [min_eq_left hs.le, min_eq_right (by omega)] at hval
      omega
    have hst : smin = tmin := by
      apply Fin.ext
      simpa [min_eq_left hs.le, min_eq_left ht.le] using hval
    have hsminT : smin ∈ T.1 := by simpa [hst] using htmin
    exact Finset.disjoint_left.mp hdis hsmin hsminT
  · have ht : ¬(tmin : ℕ) < d + 1 := by
      intro ht
      rw [min_eq_right (by omega), min_eq_left ht.le] at hval
      omega
    let U := S.1 ∪ T.1
    let vals := U.image fun i : Fin (2 * r + d) ↦ (i : ℕ)
    have hUcard : U.card = 2 * r := by
      dsimp [U]
      rw [Finset.card_union_of_disjoint hdis, S.2.1, T.2.1]
      omega
    have hvalsCard : vals.card = 2 * r := by
      dsimp [vals]
      rw [Finset.card_image_iff.mpr Fin.val_injective.injOn]
      exact hUcard
    have hsubset : vals ⊆ Finset.Ico (d + 1) (2 * r + d) := by
      intro z hz
      obtain ⟨i, hiU, rfl⟩ := Finset.mem_image.mp hz
      have hilower : d + 1 ≤ (i : ℕ) := by
        rcases Finset.mem_union.mp hiU with hiS | hiT
        · exact (by omega : d + 1 ≤ (smin : ℕ)).trans
            (Finset.min'_le S.1 i hiS)
        · exact (by omega : d + 1 ≤ (tmin : ℕ)).trans
            (Finset.min'_le T.1 i hiT)
      exact Finset.mem_Ico.mpr ⟨hilower, i.isLt⟩
    have hcardle := Finset.card_le_card hsubset
    rw [hvalsCard, Nat.card_Ico] at hcardle
    omega

theorem stableKneser_colorable {r d : ℕ} (hr : 0 < r) :
    (stableKneser (2 * r + d) r).Colorable (d + 2) := by
  exact ⟨SimpleGraph.Coloring.mk (stableKneserColor hr)
    (fun h ↦ stableKneserColor_proper hr h)⟩

end

end Erdos921
