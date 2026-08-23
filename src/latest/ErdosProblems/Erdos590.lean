/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 590.
https://www.erdosproblems.com/forum/thread/590

Informal authors:
- C. C. Chang
- Jean A. Larson

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos590.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/590.lean
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Shortlex
import Mathlib.Data.List.SplitBy
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.RelIso.Set
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Erdős Problem 590

This file proves Chang's partition relation
`ω ^ ω → (ω ^ ω, 3)²`.  The concrete combinatorics follows Larson's proof
of the stronger finite theorem; see `tex/590.tex` for the mathematical
reconstruction and the correspondence between its lemmas and this file.
-/

open Cardinal Ordinal

universe u

/-- The mixed ordinal/cardinal partition relation `α → (β, c)²`. -/
def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
      ∃ s, blue.IsClique s ∧ #s = c

namespace Erdos590

namespace Larson

/-! ## Finite increasing sequences -/

/-- A finite strictly increasing sequence of natural numbers. -/
def IncList := {l : List ℕ // l.Pairwise (· < ·)}

instance : Inhabited IncList := ⟨⟨[], by simp⟩⟩

@[ext]
theorem IncList.ext {a b : IncList} (h : a.1 = b.1) : a = b :=
  Subtype.ext h

@[simp]
theorem IncList.coe_mk (l : List ℕ) (h) : (⟨l, h⟩ : IncList).1 = l :=
  rfl

/-- Length--lexicographic order on finite increasing sequences. -/
def LL (a b : IncList) : Prop :=
  List.Shortlex (· < ·) a.1 b.1

theorem LL_iff {a b : IncList} :
    LL a b ↔ a.1.length < b.1.length ∨
      a.1.length = b.1.length ∧ List.Lex (· < ·) a.1 b.1 :=
  List.shortlex_def

theorem LL.irrefl (a : IncList) : ¬ LL a a := by
  intro ha
  rcases LL_iff.mp ha with h | ⟨-, h⟩
  · exact Nat.lt_irrefl _ h
  · exact (List.lex_irrefl (r := (· < ·)) (by exact Nat.lt_irrefl)) _ h

theorem LL.asymm {a b : IncList} (hab : LL a b) : ¬ LL b a := by
  intro hba
  rcases LL_iff.mp hab with hab | ⟨hlen, hab⟩
  · rcases LL_iff.mp hba with hba | ⟨hba, -⟩
    · exact (Nat.not_lt_of_ge hab.le hba)
    · exact (Nat.ne_of_lt hab) hba.symm
  · rcases LL_iff.mp hba with hba | ⟨-, hba⟩
    · exact (Nat.ne_of_lt hba) hlen.symm
    · exact (List.lex_asymm (fun h₁ h₂ => Nat.lt_asymm h₁ h₂) hab hba)

theorem LL.trans {a b c : IncList} (hab : LL a b) (hbc : LL b c) : LL a c := by
  apply LL_iff.mpr
  rcases LL_iff.mp hab with hab | ⟨hablen, hab⟩
  · rcases LL_iff.mp hbc with hbc | ⟨hbclen, -⟩
    · exact Or.inl (hab.trans hbc)
    · exact Or.inl (hbclen ▸ hab)
  · rcases LL_iff.mp hbc with hbc | ⟨hbclen, hbc⟩
    · exact Or.inl (hablen ▸ hbc)
    · exact Or.inr
        ⟨hablen.trans hbclen, List.lex_trans (fun h₁ h₂ => Nat.lt_trans h₁ h₂) hab hbc⟩

theorem LL.trichotomous (a b : IncList) : LL a b ∨ a = b ∨ LL b a := by
  simpa [LL, IncList.ext_iff] using
    (trichotomous_of (List.Shortlex (· < ·)) a.1 b.1)

instance : IsStrictTotalOrder IncList LL where
  irrefl := LL.irrefl
  trans _ _ _ := LL.trans
  trichotomous a b hab hba := by
    rcases LL.trichotomous a b with h | rfl | h
    · exact (hab h).elim
    · rfl
    · exact (hba h).elim

noncomputable instance : LinearOrder IncList := by
  letI : DecidableRel LL := Classical.decRel LL
  exact linearOrderOfSTO LL

instance : WellFoundedLT IncList :=
  ⟨InvImage.wf Subtype.val (List.Shortlex.wf Nat.lt_wfRel.wf)⟩

instance incListLLIsWellOrder : IsWellOrder IncList LL where
  wf := InvImage.wf Subtype.val (List.Shortlex.wf Nat.lt_wfRel.wf)
  trichotomous a b hab hba := by
    rcases LL.trichotomous a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim

/-! ### The gap encoding of arbitrary lists -/

/-- Turn an arbitrary list of naturals into a strictly increasing list by
replacing entries by successive cumulative sums with a gap of one. -/
def intoInc : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, n :: ns => (k + n) :: intoInc (k + n + 1) ns

/-- Recover the successive gaps in an increasing list. -/
def fromInc : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, n :: ns => (n - k) :: fromInc (n + 1) ns

@[simp]
theorem length_intoInc (k : ℕ) (s : List ℕ) : (intoInc k s).length = s.length := by
  induction s generalizing k <;> simp [intoInc, *]

@[simp]
theorem fromInc_intoInc (k : ℕ) (s : List ℕ) : fromInc k (intoInc k s) = s := by
  induction s generalizing k with
  | nil => simp [intoInc, fromInc]
  | cons n ns ih => simp [intoInc, fromInc, ih]

theorem mem_intoInc_ge {k n : ℕ} {s : List ℕ} (hn : n ∈ intoInc k s) : k ≤ n := by
  induction s generalizing k with
  | nil => simp [intoInc] at hn
  | cons a s ih =>
      simp only [intoInc, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact Nat.le_add_right _ _
      · exact (Nat.le_add_right k a).trans (Nat.le_succ _ |>.trans (ih hn))

theorem pairwise_intoInc (k : ℕ) (s : List ℕ) :
    (intoInc k s).Pairwise (· < ·) := by
  induction s generalizing k with
  | nil => simp [intoInc]
  | cons n ns ih =>
      simp only [intoInc, List.pairwise_cons]
      refine ⟨?_, ih (k + n + 1)⟩
      intro x hx
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (mem_intoInc_ge hx)

/-- The gap encoding, packaged as an increasing list. -/
def encodeInc (s : List ℕ) : IncList := ⟨intoInc 0 s, pairwise_intoInc 0 s⟩

@[simp]
theorem encodeInc_val (s : List ℕ) : (encodeInc s).1 = intoInc 0 s := rfl

theorem encodeInc_injective : Function.Injective encodeInc := by
  intro s t h
  have hval : intoInc 0 s = intoInc 0 t := congrArg Subtype.val h
  simpa only [fromInc_intoInc] using congrArg (fromInc 0) hval

theorem lex_intoInc_iff (k : ℕ) (s t : List ℕ) :
    List.Lex (· < ·) (intoInc k s) (intoInc k t) ↔ List.Lex (· < ·) s t := by
  induction s generalizing k t with
  | nil => cases t <;> simp [intoInc]
  | cons a s ih =>
      cases t with
      | nil => simp [intoInc]
      | cons b t =>
          simp only [intoInc, List.cons_lex_cons_iff, Nat.add_lt_add_iff_left,
            Nat.add_left_cancel_iff]
          constructor
          · rintro (h | ⟨hab, h⟩)
            · exact Or.inl h
            · subst b
              exact Or.inr ⟨rfl, (ih (k + a + 1) t).mp h⟩
          · rintro (h | ⟨hab, h⟩)
            · exact Or.inl h
            · subst b
              exact Or.inr ⟨rfl, (ih (k + a + 1) t).mpr h⟩

theorem shortlex_intoInc_iff (k : ℕ) (s t : List ℕ) :
    List.Shortlex (· < ·) (intoInc k s) (intoInc k t) ↔
      List.Shortlex (· < ·) s t := by
  simp only [List.shortlex_def, length_intoInc, lex_intoInc_iff]

theorem encodeInc_LL_iff (s t : List ℕ) :
    LL (encodeInc s) (encodeInc t) ↔ List.Shortlex (· < ·) s t :=
  shortlex_intoInc_iff 0 s t

/-! ### Order types of the fixed-length levels -/

/-- Lists of naturals of one prescribed length. -/
def RawLevel (n : ℕ) := {l : List ℕ // l.length = n}

/-- Lexicographic comparison inside one fixed-length level. -/
def RawLevelLex {n : ℕ} (a b : RawLevel n) : Prop :=
  List.Lex (· < ·) a.1 b.1

theorem RawLevelLex.irrefl {n : ℕ} (a : RawLevel n) :
    ¬ RawLevelLex a a :=
  List.lex_irrefl (r := (· < ·)) (fun _ h ↦ Nat.lt_irrefl _ h) a.1

theorem RawLevelLex.trans {n : ℕ} {a b c : RawLevel n}
    (hab : RawLevelLex a b) (hbc : RawLevelLex b c) : RawLevelLex a c :=
  List.lex_trans (fun h₁ h₂ ↦ Nat.lt_trans h₁ h₂) hab hbc

theorem RawLevelLex.trichotomous {n : ℕ} (a b : RawLevel n) :
    RawLevelLex a b ∨ a = b ∨ RawLevelLex b a := by
  by_cases hab : RawLevelLex a b
  · exact Or.inl hab
  by_cases hba : RawLevelLex b a
  · exact Or.inr (Or.inr hba)
  · apply Or.inr; apply Or.inl
    apply Subtype.ext
    exact List.lex_trichotomous (r := (· < ·))
      (fun x y hxy hyx ↦ Nat.le_antisymm (Nat.le_of_not_gt hyx)
        (Nat.le_of_not_gt hxy)) hba hab

instance rawLevelLexStrictTotal (n : ℕ) :
    IsStrictTotalOrder (RawLevel n) RawLevelLex where
  irrefl := RawLevelLex.irrefl
  trans _ _ _ := RawLevelLex.trans
  trichotomous a b hab hba := by
    rcases RawLevelLex.trichotomous a b with h | rfl | h
    · exact (hab h).elim
    · rfl
    · exact (hba h).elim

noncomputable instance rawLevelLinearOrder (n : ℕ) : LinearOrder (RawLevel n) := by
  letI : DecidableRel (@RawLevelLex n) := Classical.decRel _
  exact linearOrderOfSTO RawLevelLex

instance rawLevelLexWellFounded (n : ℕ) :
    IsWellFounded (RawLevel n) RawLevelLex :=
  ⟨(InvImage.wf Subtype.val (List.Shortlex.wf Nat.lt_wfRel.wf)).mono (by
    intro a b hab
    change List.Shortlex (· < ·) a.1 b.1
    rw [List.shortlex_def]
    exact Or.inr ⟨a.2.trans b.2.symm, hab⟩)⟩

instance rawLevelWellFoundedLT (n : ℕ) : WellFoundedLT (RawLevel n) := by
  constructor
  change WellFounded (@RawLevelLex n)
  exact (rawLevelLexWellFounded n).wf

instance rawLevelIsWellOrder (n : ℕ) :
    IsWellOrder (RawLevel n) RawLevelLex where
  wf := IsWellFounded.wf
  trichotomous a b hab hba := by
    rcases RawLevelLex.trichotomous a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim

/-- Removing the head identifies the successor level with the
lexicographic product of `Nat` and the preceding level. -/
def rawLevelSuccEquiv (n : ℕ) : RawLevel (n + 1) ≃ ℕ × RawLevel n where
  toFun x :=
    ⟨x.1.headD 0, ⟨x.1.tail, by
      have hx : x.1 ≠ [] := by
        intro h
        have : 0 = n + 1 := by simpa [h] using x.2
        omega
      rw [List.length_tail, x.2]
      omega⟩⟩
  invFun x := ⟨x.1 :: x.2.1, by simp [x.2.2]⟩
  left_inv x := by
    apply Subtype.ext
    cases h : x.1 with
    | nil =>
        have := x.2
        simp [h] at this
    | cons a as => simp [h]
  right_inv x := by
    rcases x with ⟨a, xs⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

@[simp] theorem rawLevelSuccEquiv_fst (n x : ℕ) (xs : List ℕ)
    (h : (x :: xs).length = n + 1) :
    (rawLevelSuccEquiv n ⟨x :: xs, h⟩).1 = x := rfl

@[simp] theorem rawLevelSuccEquiv_snd_val (n x : ℕ) (xs : List ℕ)
    (h : (x :: xs).length = n + 1) :
    (rawLevelSuccEquiv n ⟨x :: xs, h⟩).2.1 = xs := rfl

/-- The preceding equivalence preserves the lexicographic relations. -/
def rawLevelSuccRelIso (n : ℕ) :
    @RawLevelLex (n + 1) ≃r
      Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex n) where
  toEquiv := rawLevelSuccEquiv n
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    cases a with
    | nil =>
        simp at ha
    | cons x xs =>
      cases b with
      | nil =>
          simp at hb
      | cons y ys =>
          simp [RawLevelLex, Prod.lex_def, List.cons_lex_cons_iff]

theorem rawLevel_type (n : ℕ) :
    Ordinal.type (@RawLevelLex n) = ω ^ n := by
  induction n with
  | zero =>
      have huniq : Nonempty (Unique (RawLevel 0)) := by
        let d : RawLevel 0 := ⟨[], rfl⟩
        exact ⟨{
          default := d
          uniq := fun x ↦ Subtype.ext (List.length_eq_zero_iff.mp x.2) }⟩
      have htype : Ordinal.type (@RawLevelLex 0) = 1 :=
        (Ordinal.type_eq_one_iff_unique).2 huniq
      simpa using htype
  | succ n ih =>
      rw [(rawLevelSuccRelIso n).ordinalType_congr]
      rw [Ordinal.type_prod_lex, ih, Ordinal.type_nat_lt]
      rw [pow_succ]

/-- Finite partitions do not lower the full lexicographic type of a raw
level: one cell contains an order-isomorphic copy of the whole level. -/
theorem rawLevel_finite_partition (n k : ℕ)
    (c : RawLevel n → Fin (k + 1)) :
    ∃ i : Fin (k + 1), ∃ e : (@RawLevelLex n) ↪r (@RawLevelLex n),
      ∀ x, c (e x) = i := by
  classical
  induction n with
  | zero =>
      let x0 : RawLevel 0 := ⟨[], rfl⟩
      refine ⟨c x0, RelEmbedding.refl _, ?_⟩
      intro x
      congr 1
      apply Subtype.ext
      exact List.length_eq_zero_iff.mp x.2
  | succ n ih =>
      let iso := rawLevelSuccRelIso n
      let cp : ℕ → RawLevel n → Fin (k + 1) := fun a x ↦
        c (iso.symm (a, x))
      choose ci ei hei using fun a ↦ ih (cp a)
      obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber ci
      let H : Set ℕ := ci ⁻¹' {i}
      haveI : Infinite H := hi
      let h : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet H
      let ep :
          Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex n) ↪r
            Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex n) :=
        RelEmbedding.ofMonotone
          (fun p : ℕ × RawLevel n ↦ (h p.1, ei (h p.1) p.2)) (by
            intro a b hab
            rcases a with ⟨a, x⟩
            rcases b with ⟨b, y⟩
            simp only [Prod.lex_def] at hab ⊢
            rcases hab with hab | ⟨rfl, hxy⟩
            · exact Or.inl (h.strictMono hab)
            · exact Or.inr ⟨rfl, (ei (h a)).map_rel_iff.mpr hxy⟩)
      let e := iso.toRelEmbedding.trans (ep.trans iso.symm.toRelEmbedding)
      refine ⟨i, e, ?_⟩
      intro x
      have hhH : h (iso x).1 ∈ H := by
        change Nat.orderEmbeddingOfSet H (iso x).1 ∈ H
        rw [Nat.orderEmbeddingOfSet_apply]
        exact (Nat.Subtype.ofNat H (iso x).1).property
      have hh : ci (h (iso x).1) = i := by simpa [H] using hhH
      change cp (h (iso x).1) (ei (h (iso x).1) (iso x).2) = i
      rw [hei]
      exact hh

/-- A pure component of a raw level is a specified embedded copy of some
(possibly lower) raw level. -/
structure PureComponent (p : ℕ) where
  exponent : ℕ
  embedding : (@RawLevelLex exponent) ↪r (@RawLevelLex p)

def PureComponent.Good {p : ℕ} (C : PureComponent p)
    (S : Set (RawLevel p)) : Prop :=
  ∃ e : (@RawLevelLex C.exponent) ↪r (@RawLevelLex C.exponent),
    ∀ x, C.embedding (e x) ∈ S

/-- If two sets cover a pure component, one of them contains a full copy of
that component. -/
theorem PureComponent.good_or_good_of_cover {p : ℕ} (C : PureComponent p)
    (S T : Set (RawLevel p))
    (hcover : ∀ x, C.embedding x ∈ S ∨ C.embedding x ∈ T) :
    C.Good S ∨ C.Good T := by
  classical
  let c : RawLevel C.exponent → Fin 2 := fun x ↦
    if C.embedding x ∈ S then 0 else 1
  obtain ⟨i, e, he⟩ := rawLevel_finite_partition C.exponent 1 c
  rcases i with ⟨i, hi⟩
  have hi01 : i = 0 ∨ i = 1 := by omega
  rcases hi01 with rfl | rfl
  · apply Or.inl
    refine ⟨e, ?_⟩
    intro x
    have hx := he x
    simpa [c] using hx
  · apply Or.inr
    refine ⟨e, ?_⟩
    intro x
    have hx := he x
    have hnot : C.embedding (e x) ∉ S := by
      simpa [c] using hx
    exact (hcover (e x)).resolve_left hnot

/-- A finite strong decomposition relative to a finite set of fixed points.
The components are pure powers of `ω`; being good on every component is
exactly the input needed to assemble a self-embedding fixing those points. -/
structure StrongDecomp (p : ℕ) (F : Finset (RawLevel p)) where
  components : List (PureComponent p)
  assemble : ∀ (S : Set (RawLevel p)),
    (∀ x ∈ F, x ∈ S) →
    (∀ C ∈ components, C.Good S) →
    ∃ g : (@RawLevelLex p) ↪r (@RawLevelLex p),
      (∀ x ∈ F, g x = x) ∧ ∀ x, g x ∈ S

noncomputable def strongDecompZero (F : Finset (RawLevel 0)) :
    StrongDecomp 0 F := by
  classical
  let x0 : RawLevel 0 := ⟨[], rfl⟩
  by_cases hx0 : x0 ∈ F
  · refine {
      components := []
      assemble := ?_ }
    intro S hFS _
    refine ⟨RelEmbedding.refl _, ?_, ?_⟩
    · intro x hx
      rfl
    · intro x
      have hxx0 : x = x0 := by
        apply Subtype.ext
        exact List.length_eq_zero_iff.mp x.2
      simpa [hxx0] using hFS x0 hx0
  · let C : PureComponent 0 := {
      exponent := 0
      embedding := RelEmbedding.refl _ }
    refine {
      components := [C]
      assemble := ?_ }
    intro S _ hgood
    obtain ⟨e, he⟩ := hgood C (by simp)
    refine ⟨e, ?_, ?_⟩
    · intro x hx
      have hxx0 : x = x0 := by
        apply Subtype.ext
        exact List.length_eq_zero_iff.mp x.2
      subst x
      exact (hx0 hx).elim
    · intro x
      exact he x

def rawLevelHead {p : ℕ} (x : RawLevel (p + 1)) : ℕ :=
  (rawLevelSuccRelIso p x).1

def rawLevelTail {p : ℕ} (x : RawLevel (p + 1)) : RawLevel p :=
  (rawLevelSuccRelIso p x).2

noncomputable def rawLevelFiber {p : ℕ} (F : Finset (RawLevel (p + 1)))
    (a : ℕ) : Finset (RawLevel p) := by
  classical
  exact (F.filter fun x ↦ rawLevelHead x = a).image rawLevelTail

theorem rawLevelTail_mem_fiber {p : ℕ} {F : Finset (RawLevel (p + 1))}
    {x : RawLevel (p + 1)} (hx : x ∈ F) :
    rawLevelTail x ∈ rawLevelFiber F (rawLevelHead x) := by
  classical
  simp only [rawLevelFiber, Finset.mem_image, Finset.mem_filter]
  exact ⟨x, ⟨hx, rfl⟩, rfl⟩

noncomputable def rawLevelFixedHeadEmbedding (p a : ℕ) :
    (@RawLevelLex p) ↪r (@RawLevelLex (p + 1)) :=
  (RelEmbedding.ofMonotone
    (r := @RawLevelLex p)
    (s := Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p))
    (fun x : RawLevel p ↦ (a, x)) (by
      intro x y hxy
      change Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p)
        (a, x) (a, y)
      simp only [Prod.lex_def]
      exact Or.inr ⟨trivial, hxy⟩)).trans
    (rawLevelSuccRelIso p).symm.toRelEmbedding

noncomputable def PureComponent.atHead {p : ℕ} (a : ℕ)
    (C : PureComponent p) : PureComponent (p + 1) where
  exponent := C.exponent
  embedding := C.embedding.trans (rawLevelFixedHeadEmbedding p a)

noncomputable def rawLevelTailEmbedding (p B : ℕ) :
    (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1)) := by
  let iso := rawLevelSuccRelIso p
  let shift :
      Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p) ↪r
        Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p) :=
    RelEmbedding.ofMonotone (fun x : ℕ × RawLevel p ↦ (B + x.1, x.2)) (by
      intro x y hxy
      rcases x with ⟨a, x⟩
      rcases y with ⟨b, y⟩
      simp only [Prod.lex_def] at hxy ⊢
      rcases hxy with hab | ⟨rfl, hxy⟩
      · exact Or.inl (Nat.add_lt_add_left hab B)
      · exact Or.inr ⟨rfl, hxy⟩)
  exact iso.toRelEmbedding.trans (shift.trans iso.symm.toRelEmbedding)

noncomputable def rawLevelTailComponent (p B : ℕ) :
    PureComponent (p + 1) where
  exponent := p + 1
  embedding := rawLevelTailEmbedding p B

theorem rawLevelTailEmbedding_head {p B : ℕ} (x : RawLevel (p + 1)) :
    rawLevelHead (rawLevelTailEmbedding p B x) = B + rawLevelHead x := by
  rfl

theorem rawLevelFixedHeadEmbedding_head {p a : ℕ} (x : RawLevel p) :
    rawLevelHead (rawLevelFixedHeadEmbedding p a x) = a := by
  rfl

noncomputable def rawLevelHeadBound {p : ℕ}
    (F : Finset (RawLevel (p + 1))) : ℕ :=
  F.sup rawLevelHead + 1

theorem rawLevelHead_lt_bound {p : ℕ} {F : Finset (RawLevel (p + 1))}
    {x : RawLevel (p + 1)} (hx : x ∈ F) :
    rawLevelHead x < rawLevelHeadBound F := by
  classical
  unfold rawLevelHeadBound
  have hle : rawLevelHead x ≤ F.sup rawLevelHead := Finset.le_sup hx
  omega

noncomputable def strongDecomp : (p : ℕ) →
    (F : Finset (RawLevel p)) → StrongDecomp p F
  | 0, F => strongDecompZero F
  | p + 1, F => by
      classical
      let B := rawLevelHeadBound F
      let child : (a : ℕ) → StrongDecomp p (rawLevelFiber F a) := fun a ↦
        strongDecomp p (rawLevelFiber F a)
      let lifted : ℕ → List (PureComponent (p + 1)) := fun a ↦
        (child a).components.map (PureComponent.atHead a)
      let tailC := rawLevelTailComponent p B
      let comps := (List.range B).flatMap lifted ++ [tailC]
      refine {
        components := comps
        assemble := ?_ }
      intro S hFS hgood
      let fiberSet : ℕ → Set (RawLevel p) := fun a ↦
        {t | rawLevelFixedHeadEmbedding p a t ∈ S}
      have hFiberF : ∀ a t, t ∈ rawLevelFiber F a → t ∈ fiberSet a := by
        intro a t ht
        simp only [rawLevelFiber, Finset.mem_image, Finset.mem_filter] at ht
        rcases ht with ⟨x, ⟨hxF, hxa⟩, hxt⟩
        subst t
        have heq : rawLevelFixedHeadEmbedding p a (rawLevelTail x) = x := by
          apply (rawLevelSuccRelIso p).injective
          change (a, rawLevelTail x) =
            (rawLevelHead x, rawLevelTail x)
          exact Prod.ext hxa.symm rfl
        change rawLevelFixedHeadEmbedding p a (rawLevelTail x) ∈ S
        rw [heq]
        exact hFS x hxF
      have hChildGood : ∀ a, a < B → ∀ C ∈ (child a).components,
          C.Good (fiberSet a) := by
        intro a ha C hC
        have hmem : C.atHead a ∈ comps := by
          simp only [comps, List.mem_append, List.mem_cons, List.mem_nil_iff,
            or_false]
          apply Or.inl
          rw [List.mem_flatMap]
          exact ⟨a, List.mem_range.mpr ha, by
            simp only [lifted, List.mem_map]
            exact ⟨C, hC, rfl⟩⟩
        obtain ⟨e, he⟩ := hgood (C.atHead a) hmem
        refine ⟨e, ?_⟩
        intro x
        exact he x
      have hChildAssemble : ∀ a, a < B →
          ∃ g : (@RawLevelLex p) ↪r (@RawLevelLex p),
            (∀ x ∈ rawLevelFiber F a, g x = x) ∧
              ∀ x, g x ∈ fiberSet a := by
        intro a ha
        exact (child a).assemble (fiberSet a) (hFiberF a)
          (hChildGood a ha)
      choose ga hgaFix hgaMem using hChildAssemble
      have htailMem : tailC ∈ comps := by
        simp [comps]
      obtain ⟨etail, hetail⟩ := hgood tailC htailMem
      let iso := rawLevelSuccRelIso p
      let mapFun : RawLevel (p + 1) → RawLevel (p + 1) := fun x ↦
        if hx : rawLevelHead x < B then
          rawLevelFixedHeadEmbedding p (rawLevelHead x)
            (ga (rawLevelHead x) hx (rawLevelTail x))
        else
          tailC.embedding (etail
            (iso.symm (rawLevelHead x - B, rawLevelTail x)))
      have hmono : ∀ ⦃x y⦄, RawLevelLex x y →
          RawLevelLex (mapFun x) (mapFun y) := by
        intro x y hxy
        have hprod : Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p)
            (iso x) (iso y) := iso.map_rel_iff.mpr hxy
        simp only [Prod.lex_def] at hprod
        by_cases hx : rawLevelHead x < B <;>
          by_cases hy : rawLevelHead y < B
        · simp only [mapFun, dif_pos hx, dif_pos hy]
          apply iso.map_rel_iff.mp
          change Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p)
            (rawLevelHead x,
              ga (rawLevelHead x) hx (rawLevelTail x))
            (rawLevelHead y,
              ga (rawLevelHead y) hy (rawLevelTail y))
          simp only [Prod.lex_def]
          rcases hprod with hhead | ⟨hhead, htail⟩
          · exact Or.inl (by simpa [rawLevelHead] using hhead)
          · have hheads : rawLevelHead x = rawLevelHead y := by
              simpa [rawLevelHead] using hhead
            apply Or.inr
            refine ⟨hheads, ?_⟩
            have hmap := (ga (rawLevelHead x) hx).map_rel_iff.mpr htail
            simpa [rawLevelTail, hheads] using hmap
        · simp only [mapFun, dif_pos hx, dif_neg hy]
          apply iso.map_rel_iff.mp
          change Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex p)
            (rawLevelHead x,
              ga (rawLevelHead x) hx (rawLevelTail x))
            (B + rawLevelHead
              (etail (iso.symm (rawLevelHead y - B, rawLevelTail y))),
              rawLevelTail
                (etail (iso.symm (rawLevelHead y - B, rawLevelTail y))))
          simp only [Prod.lex_def]
          apply Or.inl
          exact hx.trans_le (Nat.le_add_right B _)
        · exfalso
          rcases hprod with hhead | ⟨hhead, -⟩
          · have hh : rawLevelHead x < rawLevelHead y := by
              simpa [rawLevelHead] using hhead
            exact hx (hh.trans hy)
          · exact hx (by
              have hh : rawLevelHead x = rawLevelHead y := by
                simpa [rawLevelHead] using hhead
              exact hh ▸ hy)
        · simp only [mapFun, dif_neg hx, dif_neg hy]
          apply tailC.embedding.map_rel_iff.mpr
          apply etail.map_rel_iff.mpr
          apply iso.symm.map_rel_iff.mpr
          simp only [Prod.lex_def]
          rcases hprod with hhead | ⟨hhead, htail⟩
          · apply Or.inl
            exact (Nat.sub_lt_sub_iff_right (Nat.le_of_not_gt hx)).2
              (by simpa [rawLevelHead] using hhead)
          · apply Or.inr
            exact ⟨congrArg (fun z ↦ z - B)
              (by simpa [rawLevelHead] using hhead), htail⟩
      let g : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1)) :=
        RelEmbedding.ofMonotone mapFun hmono
      refine ⟨g, ?_, ?_⟩
      · intro x hxF
        have hxB : rawLevelHead x < B := rawLevelHead_lt_bound hxF
        change mapFun x = x
        simp only [mapFun, dif_pos hxB]
        rw [hgaFix (rawLevelHead x) hxB (rawLevelTail x)
          (rawLevelTail_mem_fiber hxF)]
        apply iso.injective
        rfl
      · intro x
        change mapFun x ∈ S
        by_cases hx : rawLevelHead x < B
        · simp only [mapFun, dif_pos hx]
          exact hgaMem (rawLevelHead x) hx (rawLevelTail x)
        · simp only [mapFun, dif_neg hx]
          exact hetail _
termination_by p => p

theorem List.lex_append_of_eq_length {r : α → α → Prop}
    {s t : List α} (hlen : s.length = t.length) (hst : List.Lex r s t)
    (u v : List α) : List.Lex r (s ++ u) (t ++ v) := by
  induction hst generalizing u v with
  | nil => simp at hlen
  | @rel a b s t hab =>
      exact List.Lex.rel hab
  | @cons a s t hst ih =>
      have hlen' : s.length = t.length := Nat.add_right_cancel hlen
      exact List.Lex.cons (ih hlen' u v)

noncomputable def rawLevelPrefixEmbedding (p q : ℕ) (v : RawLevel p) :
    (@RawLevelLex q) ↪r (@RawLevelLex (p + q)) :=
  RelEmbedding.ofMonotone
    (fun x : RawLevel q ↦ ⟨v.1 ++ x.1, by simp [v.2, x.2]⟩)
    (by
      intro x y hxy
      exact List.Lex.append_left _ hxy v.1)

theorem rawLevelPrefixEmbedding_separated {p q : ℕ} {v w : RawLevel p}
    (hvw : RawLevelLex v w) (x y : RawLevel q) :
    RawLevelLex (rawLevelPrefixEmbedding p q v x)
      (rawLevelPrefixEmbedding p q w y) := by
  exact List.lex_append_of_eq_length (v.2.trans w.2.symm) hvw x.1 y.1

def rawLevelZero (n : ℕ) : RawLevel n :=
  ⟨List.replicate n 0, by simp⟩

def rawLevelOne (n : ℕ) : RawLevel (n + 1) :=
  ⟨1 :: List.replicate n 0, by simp⟩

theorem rawLevelZero_ne_one (n : ℕ) :
    rawLevelZero (n + 1) ≠ rawLevelOne n := by
  intro h
  have hv : List.replicate (n + 1) 0 = 1 :: List.replicate n 0 :=
    congrArg Subtype.val h
  rw [List.replicate_succ] at hv
  exact Nat.zero_ne_one (List.cons.inj hv).1

/-- A separated family of copies of `ω^(p+1)`, indexed in order type
`ω^p`, inside the raw level of length `p + (p+1)`. -/
structure EMFamily (p : ℕ) where
  embedding : RawLevel p →
    ((@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + (p + 1))))
  separated : ∀ {v w : RawLevel p}, RawLevelLex v w →
    ∀ x y, RawLevelLex (embedding v x) (embedding w y)

/-- The initial family consists of the consecutive prefix blocks. -/
noncomputable def EMFamily.base (p : ℕ) : EMFamily p where
  embedding v := rawLevelPrefixEmbedding p (p + 1) v
  separated hvw x y := rawLevelPrefixEmbedding_separated hvw x y

/-- A point, viewed as the unique zero-dimensional pure component. -/
noncomputable def PureComponent.singleton {p : ℕ} (v : RawLevel p) :
    PureComponent p where
  exponent := 0
  embedding := RelEmbedding.ofMonotone (fun _ : RawLevel 0 ↦ v) (by
    intro x y hxy
    have h : x = y := by
      apply Subtype.ext
      rw [List.length_eq_zero_iff.mp x.2, List.length_eq_zero_iff.mp y.2]
    subst y
    exact (RawLevelLex.irrefl x hxy).elim)

theorem PureComponent.singleton_good_iff {p : ℕ} (v : RawLevel p)
    (S : Set (RawLevel p)) : (PureComponent.singleton v).Good S ↔ v ∈ S := by
  constructor
  · rintro ⟨e, he⟩
    have h := he (rawLevelZero 0)
    change v ∈ S at h
    exact h
  · intro hv
    refine ⟨RelEmbedding.refl _, ?_⟩
    intro x
    change v ∈ S
    exact hv

/-- A vertex has a full red neighbourhood inside the displayed copy of
`ω^(p+1)`. -/
def EMRedLarge {p : ℕ}
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (x : RawLevel (p + (p + 1)))
    (E : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + (p + 1)))) : Prop :=
  ∃ e : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1)),
    ∀ z, color x (E (e z)) = false

/-- The Erdős--Milner one-component refinement.  If no red copy of
`ω^(p+1)` exists, then inside any current copy one can find a subcopy all
of whose vertices have a component-large set of red-neighbour blocks. -/
theorem em_component_filter (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (A : EMFamily p) (C : PureComponent p)
    (E : (@RawLevelLex (p + 1)) ↪r
      (@RawLevelLex (p + (p + 1)))) :
    ∃ e : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1)),
      ∀ x, C.Good {v | EMRedLarge color (E (e x)) (A.embedding v)} := by
  classical
  let good : Set (RawLevel (p + 1)) :=
    {x | C.Good {v | EMRedLarge color (E x) (A.embedding v)}}
  let c : RawLevel (p + 1) → Fin 2 := fun x ↦
    if x ∈ good then 0 else 1
  obtain ⟨i, e, he⟩ := rawLevel_finite_partition (p + 1) 1 c
  rcases i with ⟨i, hi⟩
  have hi01 : i = 0 ∨ i = 1 := by omega
  rcases hi01 with rfl | rfl
  · refine ⟨e, ?_⟩
    intro x
    have hx := he x
    simpa [c, good] using hx
  · let Ebad := e.trans E
    obtain ⟨u, v, huv, huvBlue⟩ := hno Ebad
    have huBad : ¬ C.Good
        {a | EMRedLarge color (E (e u)) (A.embedding a)} := by
      have hu := he u
      simpa [c, good] using hu
    have hvBad : ¬ C.Good
        {a | EMRedLarge color (E (e v)) (A.embedding a)} := by
      have hv := he v
      simpa [c, good] using hv
    obtain ⟨z, hzU, hzV⟩ : ∃ z,
        ¬ EMRedLarge color (E (e u)) (A.embedding (C.embedding z)) ∧
        ¬ EMRedLarge color (E (e v)) (A.embedding (C.embedding z)) := by
      by_contra hn
      have hcover : ∀ z,
          C.embedding z ∈
              {a | EMRedLarge color (E (e u)) (A.embedding a)} ∨
            C.embedding z ∈
              {a | EMRedLarge color (E (e v)) (A.embedding a)} := by
        intro z
        by_cases hz : EMRedLarge color (E (e u))
            (A.embedding (C.embedding z))
        · exact Or.inl hz
        · apply Or.inr
          by_contra hz'
          exact hn ⟨z, hz, hz'⟩
      exact (C.good_or_good_of_cover _ _ hcover).elim huBad hvBad
    let x₀ := E (e u)
    let x₁ := E (e v)
    let B := A.embedding (C.embedding z)
    let d : RawLevel (p + 1) → Fin 4 := fun y ↦
      if color x₀ (B y) = false then 0
      else if color x₁ (B y) = false then 1
      else if B y = x₀ then 2 else 3
    obtain ⟨j, f, hf⟩ := rawLevel_finite_partition (p + 1) 3 d
    rcases j with ⟨j, hj⟩
    have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjCases with rfl | rfl | rfl | rfl
    · exfalso
      apply hzU
      refine ⟨f, ?_⟩
      intro y
      have hy := hf y
      by_contra hr
      have hb : color x₀ (B (f y)) = true :=
        Bool.eq_true_of_not_eq_false hr
      have hyval := congrArg Fin.val hy
      simp [d, hb] at hyval
      split at hyval
      · simp at hyval
      · split at hyval <;> simp at hyval
    · exfalso
      apply hzV
      refine ⟨f, ?_⟩
      intro y
      have hy := hf y
      by_cases hr₀ : color x₀ (B (f y)) = false
      · simp [d, hr₀] at hy
      by_contra hr₁
      have hb₀ : color x₀ (B (f y)) = true :=
        Bool.eq_true_of_not_eq_false hr₀
      have hb₁ : color x₁ (B (f y)) = true :=
        Bool.eq_true_of_not_eq_false hr₁
      have hyval := congrArg Fin.val hy
      simp [d, hb₀, hb₁] at hyval
      split at hyval <;> simp at hyval
    · exfalso
      have hzero := hf (rawLevelZero (p + 1))
      have hone := hf (rawLevelOne p)
      have hzeroEq : B (f (rawLevelZero (p + 1))) = x₀ := by
        simp only [d] at hzero
        split at hzero
        · simp at hzero
        · split at hzero
          · simp at hzero
          · split at hzero
            · assumption
            · simp at hzero
      have honeEq : B (f (rawLevelOne p)) = x₀ := by
        simp only [d] at hone
        split at hone
        · simp at hone
        · split at hone
          · simp at hone
          · split at hone
            · assumption
            · simp at hone
      have : rawLevelZero (p + 1) = rawLevelOne p :=
        f.injective (B.injective (hzeroEq.trans honeEq.symm))
      exact rawLevelZero_ne_one p this
    · exfalso
      have hx₀x₁ : x₀ ≠ x₁ := by
        intro h
        exact huv (e.injective (E.injective h))
      have hblue : color x₀ x₁ = true := huvBlue
      have hall : ∀ y, B (f y) = x₁ := by
        intro y
        have hy := hf y
        have hred₀ : color x₀ (B (f y)) ≠ false := by
          intro hr
          have hd : d (f y) = 0 := by simp [d, hr]
          rw [hy] at hd
          simp at hd
        have hred₁ : color x₁ (B (f y)) ≠ false := by
          intro hr
          have hd : d (f y) = 1 := by simp [d, hred₀, hr]
          rw [hy] at hd
          simp at hd
        have hne₀ : B (f y) ≠ x₀ := by
          intro heq
          have hd : d (f y) = 2 := by
            change (if color x₀ (B (f y)) = false then 0
              else if color x₁ (B (f y)) = false then 1
              else if B (f y) = x₀ then 2 else 3) = 2
            rw [if_neg hred₀, if_neg hred₁, if_pos heq]
          rw [hy] at hd
          simp at hd
        by_contra hne₁
        apply htri x₀ x₁ (B (f y)) hx₀x₁ hne₀.symm (Ne.symm hne₁)
        exact ⟨hblue, Bool.eq_true_of_not_eq_false hred₀,
          Bool.eq_true_of_not_eq_false hred₁⟩
      have hzero := hall (rawLevelZero (p + 1))
      have hone := hall (rawLevelOne p)
      have : rawLevelZero (p + 1) = rawLevelOne p :=
        f.injective (B.injective (hzero.trans hone.symm))
      exact rawLevelZero_ne_one p this

/-- Iterating the preceding refinement over finitely many components. -/
theorem em_list_filter (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (A : EMFamily p) (L : List (PureComponent p))
    (E : (@RawLevelLex (p + 1)) ↪r
      (@RawLevelLex (p + (p + 1)))) :
    ∃ e : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1)),
      ∀ x C, C ∈ L →
        C.Good {v | EMRedLarge color (E (e x)) (A.embedding v)} := by
  induction L generalizing E with
  | nil =>
      refine ⟨RelEmbedding.refl _, ?_⟩
      simp
  | cons C L ih =>
      obtain ⟨e₁, he₁⟩ := em_component_filter p color htri hno A C E
      obtain ⟨e₂, he₂⟩ := ih (e₁.trans E)
      refine ⟨e₂.trans e₁, ?_⟩
      intro x D hD
      simp only [List.mem_cons] at hD
      rcases hD with rfl | hD
      · exact he₁ (e₂ x)
      · exact he₂ x D hD

/-- A simultaneous Erdős--Milner refinement: choose a point in a specified
block and reindex the family by a self-embedding fixing `F`, so that every
new block has a full red subcopy in the neighbourhood of the point. -/
theorem em_point_and_reindex (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (A : EMFamily p) (F : Finset (RawLevel p)) (μ : RawLevel p) :
    ∃ x : RawLevel (p + (p + 1)),
      ∃ g : (@RawLevelLex p) ↪r (@RawLevelLex p),
        x ∈ Set.range (A.embedding μ) ∧
        (∀ v ∈ F, g v = v) ∧
        ∀ v, EMRedLarge color x (A.embedding (g v)) := by
  classical
  let D := strongDecomp p F
  let L := D.components ++ F.toList.map PureComponent.singleton
  obtain ⟨e, he⟩ := em_list_filter p color htri hno A L (A.embedding μ)
  let x := A.embedding μ (e (rawLevelZero (p + 1)))
  let S : Set (RawLevel p) :=
    {v | EMRedLarge color x (A.embedding v)}
  have hF : ∀ v ∈ F, v ∈ S := by
    intro v hv
    have hmem : PureComponent.singleton v ∈ L := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨v, by simpa using hv, rfl⟩
    have hgood := he (rawLevelZero (p + 1)) (PureComponent.singleton v) hmem
    exact (PureComponent.singleton_good_iff v S).mp hgood
  have hcomponents : ∀ C ∈ D.components, C.Good S := by
    intro C hC
    apply he (rawLevelZero (p + 1)) C
    simp [L, hC]
  obtain ⟨g, hgfix, hgmem⟩ := D.assemble S hF hcomponents
  refine ⟨x, g, ?_, hgfix, ?_⟩
  · exact ⟨e (rawLevelZero (p + 1)), rfl⟩
  · exact hgmem

/-- Every embedded copy of a nonzero raw level has a further full subcopy
strictly above any prescribed point. -/
theorem rawLevel_embedding_has_tail (p : ℕ) (a : RawLevel (p + 1))
    (e : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1))) :
    ∃ f : (@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1)),
      ∀ x, RawLevelLex a (e (f x)) := by
  classical
  let c : RawLevel (p + 1) → Fin 2 := fun x ↦
    if RawLevelLex a (e x) then 0 else 1
  obtain ⟨i, f, hf⟩ := rawLevel_finite_partition (p + 1) 1 c
  rcases i with ⟨i, hi⟩
  have hi01 : i = 0 ∨ i = 1 := by omega
  rcases hi01 with rfl | rfl
  · refine ⟨f, ?_⟩
    intro x
    have hx := hf x
    simpa [c] using hx
  · let d : RawLevel (p + 1) → Fin 2 := fun x ↦
      if e (f x) = a then 0 else 1
    obtain ⟨j, g, hg⟩ := rawLevel_finite_partition (p + 1) 1 d
    rcases j with ⟨j, hj⟩
    have hj01 : j = 0 ∨ j = 1 := by omega
    rcases hj01 with rfl | rfl
    · exfalso
      have hzero := hg (rawLevelZero (p + 1))
      have hone := hg (rawLevelOne p)
      have hzeroEq : e (f (g (rawLevelZero (p + 1)))) = a := by
        simpa [d] using hzero
      have honeEq : e (f (g (rawLevelOne p))) = a := by
        simpa [d] using hone
      have : rawLevelZero (p + 1) = rawLevelOne p :=
        g.injective (f.injective (e.injective (hzeroEq.trans honeEq.symm)))
      exact rawLevelZero_ne_one p this
    · have hlt : ∀ x, RawLevelLex (e (f (g x))) a := by
        intro x
        have hnotAbove : ¬ RawLevelLex a (e (f (g x))) := by
          have hx := hf (g x)
          simpa [c] using hx
        have hne : e (f (g x)) ≠ a := by
          have hx := hg x
          simpa [d] using hx
        rcases RawLevelLex.trichotomous (e (f (g x))) a with h | h | h
        · exact h
        · exact (hne h).elim
        · exact (hnotAbove h).elim
      let into : (@RawLevelLex (p + 1)) ↪r
          ((· < ·) : Set.Iio a → Set.Iio a → Prop) :=
        RelEmbedding.ofMonotone
          (fun x ↦ ⟨e (f (g x)), by change RawLevelLex _ _; exact hlt x⟩) (by
            intro x y hxy
            change RawLevelLex (e (f (g x))) (e (f (g y)))
            exact e.map_rel_iff.mpr (f.map_rel_iff.mpr (g.map_rel_iff.mpr hxy)))
      have hle := into.ordinal_type_le
      rw [rawLevel_type, Ordinal.type_Iio_lt] at hle
      have hltType := Ordinal.typein_lt_type RawLevelLex a
      rw [rawLevel_type] at hltType
      exact (not_lt_of_ge hle hltType).elim

/-- Data produced at one fusion step. -/
structure EMStepResult (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (A : EMFamily p) (F : Finset (RawLevel p)) (μ : RawLevel p) where
  point : RawLevel (p + (p + 1))
  reindex : (@RawLevelLex p) ↪r (@RawLevelLex p)
  fixes : ∀ v ∈ F, reindex v = v
  point_mem : point ∈ Set.range (A.embedding μ)
  next : EMFamily p
  next_sub : ∀ v y, ∃ z, next.embedding v y = A.embedding (reindex v) z
  red : ∀ v y, color point (next.embedding v y) = false
  point_below : ∀ y, RawLevelLex point (next.embedding μ y)

theorem em_step_exists (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (A : EMFamily p) (F : Finset (RawLevel p)) (μ : RawLevel p)
    (hμ : μ ∈ F) : Nonempty (EMStepResult p color A F μ) := by
  classical
  obtain ⟨x, g, hx, hgfix, hlarge⟩ :=
    em_point_and_reindex p color htri hno A F μ
  rcases hx with ⟨a, rfl⟩
  choose e he using hlarge
  have hgμ : g μ = μ := hgfix μ hμ
  obtain ⟨tail, htail⟩ := rawLevel_embedding_has_tail p a (e μ)
  let e' : RawLevel p →
      ((@RawLevelLex (p + 1)) ↪r (@RawLevelLex (p + 1))) := fun v ↦
    if v = μ then tail.trans (e μ) else e v
  let next : EMFamily p := {
    embedding := fun v ↦ (e' v).trans (A.embedding (g v))
    separated := by
      intro v w hvw y z
      exact A.separated (g.map_rel_iff.mpr hvw) (e' v y) (e' w z) }
  refine ⟨{
    point := A.embedding μ a
    reindex := g
    fixes := hgfix
    point_mem := ⟨a, rfl⟩
    next := next
    next_sub := ?_
    red := ?_
    point_below := ?_ }⟩
  · intro v y
    exact ⟨e' v y, rfl⟩
  · intro v y
    by_cases hv : v = μ
    · subst v
      simpa [next, e'] using he μ (tail y)
    · simpa [next, e', hv] using he v y
  · intro y
    change RawLevelLex (A.embedding μ a)
      (A.embedding (g μ) (e' μ y))
    rw [hgμ]
    apply (A.embedding μ).map_rel_iff.mpr
    simpa [e'] using htail y

/-- A concrete surjection from naturals onto a fixed raw level. -/
noncomputable def rawLevelEnum : (p : ℕ) → ℕ → RawLevel p
  | 0, _ => rawLevelZero 0
  | p + 1, n => rawLevelFixedHeadEmbedding p (Nat.unpair n).1
      (rawLevelEnum p (Nat.unpair n).2)

theorem rawLevelEnum_surjective (p : ℕ) : Function.Surjective (rawLevelEnum p) := by
  induction p with
  | zero =>
      intro x
      refine ⟨0, ?_⟩
      apply Subtype.ext
      exact (List.length_eq_zero_iff.mp x.2).symm
  | succ p ih =>
      intro x
      let iso := rawLevelSuccRelIso p
      obtain ⟨n, hn⟩ := ih (iso x).2
      refine ⟨Nat.pair (iso x).1 n, ?_⟩
      simp only [rawLevelEnum, Nat.unpair_pair]
      apply iso.injective
      change ((iso x).1, rawLevelEnum p n) = iso x
      exact Prod.ext rfl hn

/-- The repeatedly occurring index used by the fusion. -/
noncomputable def emIndex (p n : ℕ) : RawLevel p :=
  rawLevelEnum p (Nat.unpair n).1

/-- All indices encountered through stage `n`. -/
noncomputable def emPast (p n : ℕ) : Finset (RawLevel p) :=
  (Finset.range (n + 1)).image (emIndex p)

theorem emIndex_mem_past (p n : ℕ) : emIndex p n ∈ emPast p n := by
  apply Finset.mem_image.mpr
  exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩

theorem emIndex_mem_past_of_le (p : ℕ) {i n : ℕ} (hin : i ≤ n) :
    emIndex p i ∈ emPast p n := by
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hin), rfl⟩

noncomputable def emStepChoice (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (A : EMFamily p) (n : ℕ) :
    EMStepResult p color A (emPast p n) (emIndex p n) :=
  Classical.choice (em_step_exists p color htri hno A _ _
    (emIndex_mem_past p n))

/-- The descending reservoir family at fusion stage `n`. -/
noncomputable def emFamilySeq (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true) :
    ℕ → EMFamily p
  | 0 => EMFamily.base p
  | n + 1 => (emStepChoice p color htri hno
      (emFamilySeq p color htri hno n) n).next

noncomputable def emStepSeq (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (n : ℕ) :=
  emStepChoice p color htri hno (emFamilySeq p color htri hno n) n

noncomputable def emPointSeq (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (n : ℕ) : RawLevel (p + (p + 1)) :=
  (emStepSeq p color htri hno n).point

/-- Transport an index from stage `start+k` back to stage `start`. -/
noncomputable def emBackIndex (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true) :
    ℕ → ℕ → RawLevel p → RawLevel p
  | _, 0, v => v
  | start, k + 1, v =>
      (emStepSeq p color htri hno start).reindex
        (emBackIndex p color htri hno (start + 1) k v)

theorem emFamilySeq_range_back (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (start k : ℕ) (v : RawLevel p) (y : RawLevel (p + 1)) :
    ∃ z, (emFamilySeq p color htri hno (start + k)).embedding v y =
      (emFamilySeq p color htri hno start).embedding
        (emBackIndex p color htri hno start k v) z := by
  induction k generalizing start v y with
  | zero =>
      exact ⟨y, rfl⟩
  | succ k ih =>
      obtain ⟨z, hz⟩ := ih (start + 1) v y
      have hz' : (emFamilySeq p color htri hno (start + (k + 1))).embedding v y =
          (emFamilySeq p color htri hno (start + 1)).embedding
            (emBackIndex p color htri hno (start + 1) k v) z := by
        simpa [Nat.add_assoc, Nat.add_comm k 1] using hz
      have hs := (emStepSeq p color htri hno start).next_sub
        (emBackIndex p color htri hno (start + 1) k v) z
      rcases hs with ⟨w, hw⟩
      refine ⟨w, hz'.trans ?_⟩
      simpa [emFamilySeq, emStepSeq, emBackIndex] using hw

theorem emBackIndex_fix (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    {i start : ℕ} (his : i ≤ start) (k : ℕ) :
    emBackIndex p color htri hno start k (emIndex p i) = emIndex p i := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
      rw [emBackIndex, ih (start := start + 1) (by omega)]
      exact (emStepSeq p color htri hno start).fixes _
        (emIndex_mem_past_of_le p his)

theorem emBackIndex_rel_left (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    {i start : ℕ} (his : i ≤ start) {v : RawLevel p}
    (hiv : RawLevelLex (emIndex p i) v) (k : ℕ) :
    RawLevelLex (emIndex p i)
      (emBackIndex p color htri hno start k v) := by
  induction k generalizing start v with
  | zero => exact hiv
  | succ k ih =>
      have hrel := (emStepSeq p color htri hno start).reindex.map_rel_iff.mpr
        (ih (start := start + 1) (by omega) hiv)
      rw [(emStepSeq p color htri hno start).fixes _
        (emIndex_mem_past_of_le p his)] at hrel
      exact hrel

theorem emBackIndex_rel_right (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    {i start : ℕ} (his : i ≤ start) {v : RawLevel p}
    (hvi : RawLevelLex v (emIndex p i)) (k : ℕ) :
    RawLevelLex (emBackIndex p color htri hno start k v)
      (emIndex p i) := by
  induction k generalizing start v with
  | zero => exact hvi
  | succ k ih =>
      have hrel := (emStepSeq p color htri hno start).reindex.map_rel_iff.mpr
        (ih (start := start + 1) (by omega) hvi)
      rw [(emStepSeq p color htri hno start).fixes _
        (emIndex_mem_past_of_le p his)] at hrel
      exact hrel

theorem emPoint_lt_next (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (n : ℕ) {v : RawLevel p} (hiv : RawLevelLex (emIndex p n) v)
    (y : RawLevel (p + 1)) :
    RawLevelLex (emPointSeq p color htri hno n)
      ((emFamilySeq p color htri hno (n + 1)).embedding v y) := by
  let S := emStepSeq p color htri hno n
  rcases S.point_mem with ⟨a, ha⟩
  rcases S.next_sub v y with ⟨z, hz⟩
  have hgμ := S.fixes (emIndex p n) (emIndex_mem_past p n)
  have hrel := (emFamilySeq p color htri hno n).separated
    (S.reindex.map_rel_iff.mpr hiv) a z
  rw [hgμ] at hrel
  rw [ha] at hrel
  change RawLevelLex S.point (S.next.embedding v y)
  rw [hz]
  exact hrel

theorem emNext_lt_point (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (n : ℕ) {v : RawLevel p} (hvi : RawLevelLex v (emIndex p n))
    (y : RawLevel (p + 1)) :
    RawLevelLex ((emFamilySeq p color htri hno (n + 1)).embedding v y)
      (emPointSeq p color htri hno n) := by
  let S := emStepSeq p color htri hno n
  rcases S.point_mem with ⟨a, ha⟩
  rcases S.next_sub v y with ⟨z, hz⟩
  have hgμ := S.fixes (emIndex p n) (emIndex_mem_past p n)
  have hrel := (emFamilySeq p color htri hno n).separated
    (S.reindex.map_rel_iff.mpr hvi) z a
  rw [hgμ] at hrel
  rw [ha] at hrel
  change RawLevelLex (S.next.embedding v y) S.point
  rw [hz]
  exact hrel

theorem emPoint_later_representation (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (start k : ℕ) :
    ∃ z, emPointSeq p color htri hno (start + k) =
      (emFamilySeq p color htri hno start).embedding
        (emBackIndex p color htri hno start k
          (emIndex p (start + k))) z := by
  let n := start + k
  rcases (emStepSeq p color htri hno n).point_mem with ⟨a, ha⟩
  obtain ⟨z, hz⟩ := emFamilySeq_range_back p color htri hno start k
    (emIndex p n) a
  refine ⟨z, ?_⟩
  exact ha.symm.trans hz

theorem emPoint_lt_later_of_index_lt (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (m k : ℕ)
    (hidx : RawLevelLex (emIndex p m) (emIndex p (m + 1 + k))) :
    RawLevelLex (emPointSeq p color htri hno m)
      (emPointSeq p color htri hno (m + 1 + k)) := by
  obtain ⟨z, hz⟩ := emPoint_later_representation p color htri hno (m + 1) k
  have hback := emBackIndex_rel_left p color htri hno
    (i := m) (start := m + 1) (by omega) hidx k
  have h := emPoint_lt_next p color htri hno m hback z
  rw [hz]
  exact h

theorem emLater_lt_point_of_index_lt (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (m k : ℕ)
    (hidx : RawLevelLex (emIndex p (m + 1 + k)) (emIndex p m)) :
    RawLevelLex (emPointSeq p color htri hno (m + 1 + k))
      (emPointSeq p color htri hno m) := by
  obtain ⟨z, hz⟩ := emPoint_later_representation p color htri hno (m + 1) k
  have hback := emBackIndex_rel_right p color htri hno
    (i := m) (start := m + 1) (by omega) hidx k
  have h := emNext_lt_point p color htri hno m hback z
  rw [hz]
  exact h

theorem emPoint_lt_later_of_index_eq (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (m k : ℕ)
    (hidx : emIndex p (m + 1 + k) = emIndex p m) :
    RawLevelLex (emPointSeq p color htri hno m)
      (emPointSeq p color htri hno (m + 1 + k)) := by
  obtain ⟨z, hz⟩ := emPoint_later_representation p color htri hno (m + 1) k
  have hfix := emBackIndex_fix p color htri hno
    (i := m) (start := m + 1) (by omega) k
  rw [hidx, hfix] at hz
  have h := (emStepSeq p color htri hno m).point_below z
  change RawLevelLex (emPointSeq p color htri hno m)
    ((emFamilySeq p color htri hno (m + 1)).embedding (emIndex p m) z) at h
  rw [hz]
  exact h

theorem emPoint_red_later (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    (m k : ℕ) :
    color (emPointSeq p color htri hno m)
      (emPointSeq p color htri hno (m + 1 + k)) = false := by
  obtain ⟨z, hz⟩ := emPoint_later_representation p color htri hno (m + 1) k
  have h := (emStepSeq p color htri hno m).red
    (emBackIndex p color htri hno (m + 1) k
      (emIndex p (m + 1 + k))) z
  change color (emPointSeq p color htri hno m)
    ((emFamilySeq p color htri hno (m + 1)).embedding _ z) = false at h
  rw [hz]
  exact h

noncomputable def rawLevelCode (p : ℕ) (v : RawLevel p) : ℕ :=
  Classical.choose (rawLevelEnum_surjective p v)

@[simp] theorem rawLevelEnum_code (p : ℕ) (v : RawLevel p) :
    rawLevelEnum p (rawLevelCode p v) = v :=
  Classical.choose_spec (rawLevelEnum_surjective p v)

theorem rawLevelCode_injective (p : ℕ) : Function.Injective (rawLevelCode p) := by
  intro v w h
  rw [← rawLevelEnum_code p v, ← rawLevelEnum_code p w, h]

noncomputable def emOccurrence (p : ℕ) (v : RawLevel p) (k : ℕ) : ℕ :=
  Nat.pair (rawLevelCode p v) k

theorem emOccurrence_strictMono (p : ℕ) (v : RawLevel p) :
    StrictMono (emOccurrence p v) := by
  intro k l hkl
  exact Nat.pair_lt_pair_right _ hkl

@[simp] theorem emIndex_occurrence (p : ℕ) (v : RawLevel p) (k : ℕ) :
    emIndex p (emOccurrence p v k) = v := by
  simp [emIndex, emOccurrence]

theorem emOccurrence_injective (p : ℕ) :
    Function.Injective (fun q : RawLevel p × ℕ ↦ emOccurrence p q.1 q.2) := by
  rintro ⟨v, k⟩ ⟨w, l⟩ h
  simp only [emOccurrence, Nat.pair_eq_pair] at h
  exact Prod.ext (rawLevelCode_injective p h.1) h.2

/-- Lexicographic `ω`-fibres over the index order `ω^p`. -/
def EMFiberLex (p : ℕ) : RawLevel p × ℕ → RawLevel p × ℕ → Prop :=
  Prod.Lex (@RawLevelLex p) ((· < ·) : ℕ → ℕ → Prop)

instance emFiberLexStrictTotal (p : ℕ) :
    IsStrictTotalOrder (RawLevel p × ℕ) (EMFiberLex p) := by
  change IsStrictTotalOrder (RawLevel p × ℕ)
    (Prod.Lex (@RawLevelLex p) ((· < ·) : ℕ → ℕ → Prop))
  infer_instance

instance emFiberLexIsWellOrder (p : ℕ) :
    IsWellOrder (RawLevel p × ℕ) (EMFiberLex p) := by
  change IsWellOrder (RawLevel p × ℕ)
    (Prod.Lex (@RawLevelLex p) ((· < ·) : ℕ → ℕ → Prop))
  infer_instance

theorem emFiber_type (p : ℕ) :
    Ordinal.type (EMFiberLex p) = ω ^ (p + 1) := by
  change Ordinal.type
    (Prod.Lex (@RawLevelLex p) ((· < ·) : ℕ → ℕ → Prop)) = _
  rw [Ordinal.type_prod_lex, Ordinal.type_nat_lt, rawLevel_type]
  rw [← Ordinal.opow_natCast ω p, ← Ordinal.opow_natCast ω (p + 1)]
  calc
    ω * ω ^ (p : Ordinal) = ω ^ (1 : Ordinal) * ω ^ (p : Ordinal) := by simp
    _ = ω ^ ((1 : Ordinal) + (p : Ordinal)) :=
      (Ordinal.opow_add ω 1 p).symm
    _ = ω ^ ((p + 1 : ℕ) : Ordinal) := by
      apply congrArg (fun z : Ordinal ↦ ω ^ z)
      exact (Nat.cast_add_one_comm p).symm.trans (Nat.cast_add_one p).symm

theorem emPoint_of_occurrence_order (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    {q r : RawLevel p × ℕ} (hqr : EMFiberLex p q r) :
    RawLevelLex
      (emPointSeq p color htri hno (emOccurrence p q.1 q.2))
      (emPointSeq p color htri hno (emOccurrence p r.1 r.2)) := by
  rcases q with ⟨v, k⟩
  rcases r with ⟨w, l⟩
  change RawLevelLex
    (emPointSeq p color htri hno (emOccurrence p v k))
    (emPointSeq p color htri hno (emOccurrence p w l))
  simp only [EMFiberLex, Prod.lex_def] at hqr
  rcases hqr with hvw | ⟨rfl, hkl⟩
  · let m := emOccurrence p v k
    let n := emOccurrence p w l
    change RawLevelLex (emPointSeq p color htri hno m)
      (emPointSeq p color htri hno n)
    rcases lt_trichotomy m n with hmn | hmn | hnm
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hmn
      have hd' : n = m + 1 + d := by omega
      have hidx : RawLevelLex (emIndex p m) (emIndex p n) := by
        simpa [m, n] using hvw
      rw [hd'] at hidx ⊢
      exact emPoint_lt_later_of_index_lt p color htri hno m d hidx
    · have hidx : emIndex p m = emIndex p n := congrArg (emIndex p) hmn
      have : v = w := by simpa [m, n] using hidx
      exact (RawLevelLex.irrefl v (this ▸ hvw)).elim
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hnm
      have hd' : m = n + 1 + d := by omega
      have hidx : RawLevelLex (emIndex p m) (emIndex p n) := by
        simpa [m, n] using hvw
      rw [hd'] at hidx ⊢
      exact emLater_lt_point_of_index_lt p color htri hno n d hidx
  · have hmn := emOccurrence_strictMono p v hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hmn
    have hd' : emOccurrence p v l = emOccurrence p v k + 1 + d := by omega
    rw [hd']
    apply emPoint_lt_later_of_index_eq p color htri hno
      (emOccurrence p v k) d
    rw [← hd']
    exact (emIndex_occurrence p v l).trans (emIndex_occurrence p v k).symm

noncomputable def emFiniteEmbedding (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true) :
    (EMFiberLex p) ↪r (@RawLevelLex (p + (p + 1))) :=
  RelEmbedding.ofMonotone
    (fun q ↦ emPointSeq p color htri hno (emOccurrence p q.1 q.2))
    (fun _ _ h ↦ emPoint_of_occurrence_order p color htri hno h)

theorem emFiniteEmbedding_red (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true)
    {q r : RawLevel p × ℕ} (hqr : q ≠ r) :
    color (emFiniteEmbedding p color htri hno q)
      (emFiniteEmbedding p color htri hno r) = false := by
  have hocc : emOccurrence p q.1 q.2 ≠ emOccurrence p r.1 r.2 := by
    exact fun h ↦ hqr (emOccurrence_injective p h)
  rcases lt_trichotomy (emOccurrence p q.1 q.2)
      (emOccurrence p r.1 r.2) with hlt | heq | hgt
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
    have hd' : emOccurrence p r.1 r.2 =
        emOccurrence p q.1 q.2 + 1 + d := by omega
    change color (emPointSeq p color htri hno (emOccurrence p q.1 q.2))
      (emPointSeq p color htri hno (emOccurrence p r.1 r.2)) = false
    rw [hd']
    exact emPoint_red_later p color htri hno (emOccurrence p q.1 q.2) d
  · exact (hocc heq).elim
  · rw [hcomm]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
    have hd' : emOccurrence p q.1 q.2 =
        emOccurrence p r.1 r.2 + 1 + d := by omega
    change color (emPointSeq p color htri hno (emOccurrence p r.1 r.2))
      (emPointSeq p color htri hno (emOccurrence p q.1 q.2)) = false
    rw [hd']
    exact emPoint_red_later p color htri hno (emOccurrence p r.1 r.2) d

noncomputable def rawLevelFiberRelIso (p : ℕ) :
    (@RawLevelLex (p + 1)) ≃r (EMFiberLex p) := by
  apply Classical.choice
  apply Ordinal.type_eq.mp
  rw [rawLevel_type, emFiber_type]

/-- The specialized finite Erdős--Milner theorem needed by Larson's
argument: a triangle-free blue graph on `ω^(2p+1)` contains a red copy of
`ω^(p+1)`. -/
theorem rawLevel_erdos_milner (p : ℕ)
    (color : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true)) :
    ∃ E : (@RawLevelLex (p + 1)) ↪r
        (@RawLevelLex (p + (p + 1))),
      ∀ x y, x ≠ y → color (E x) (E y) = false := by
  classical
  by_cases hred : ∃ E : (@RawLevelLex (p + 1)) ↪r
      (@RawLevelLex (p + (p + 1))),
      ∀ x y, x ≠ y → color (E x) (E y) = false
  · exact hred
  have hno : ∀ E : (@RawLevelLex (p + 1)) ↪r
      (@RawLevelLex (p + (p + 1))),
      ∃ x y, x ≠ y ∧ color (E x) (E y) = true := by
    intro E
    by_contra hn
    apply hred
    refine ⟨E, ?_⟩
    intro x y hxy
    apply Bool.eq_false_of_not_eq_true
    intro hblue
    exact hn ⟨x, y, hxy, hblue⟩
  let E := (rawLevelFiberRelIso p).toRelEmbedding.trans
    (emFiniteEmbedding p color htri hno)
  refine ⟨E, ?_⟩
  intro x y hxy
  apply emFiniteEmbedding_red p color hcomm htri hno
  exact fun h ↦ hxy ((rawLevelFiberRelIso p).injective h)

/-- The gap decoder is also a right inverse on an already increasing list,
provided all entries lie above its current offset. -/
theorem intoInc_fromInc_of_pairwise_ge (k : ℕ) {s : List ℕ}
    (hs : s.Pairwise (· < ·)) (hge : ∀ x ∈ s, k ≤ x) :
    intoInc k (fromInc k s) = s := by
  induction s generalizing k with
  | nil => simp [intoInc, fromInc]
  | cons n ns ih =>
      rw [List.pairwise_cons] at hs
      have hkn : k ≤ n := hge n (by simp)
      have htail : ∀ x ∈ ns, n + 1 ≤ x := by
        intro x hx
        exact Nat.succ_le_iff.mpr (hs.1 x hx)
      have hsum : k + (n - k) = n := by omega
      simp only [fromInc, intoInc]
      rw [hsum, ih (n + 1) hs.2 htail]

theorem encodeInc_decode (x : IncList) : encodeInc (fromInc 0 x.1) = x := by
  apply IncList.ext
  exact intoInc_fromInc_of_pairwise_ge 0 x.2 (fun _ _ ↦ Nat.zero_le _)

@[simp] theorem length_fromInc (k : ℕ) (s : List ℕ) :
    (fromInc k s).length = s.length := by
  induction s generalizing k with
  | nil => rfl
  | cons a s ih => simp [fromInc, ih]

/-- Length of the ambient finite level used for a source level. -/
def emTargetLength : ℕ → ℕ
  | 0 => 0
  | p + 1 => p + (p + 1)

theorem emTargetLength_strictMono : StrictMono emTargetLength := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => simp [emTargetLength]
  | succ n => simp [emTargetLength]; omega

def incListToRaw (x : IncList) : RawLevel x.1.length :=
  ⟨fromInc 0 x.1, length_fromInc 0 x.1⟩

theorem incListToRaw_val_injective {x y : IncList}
    (hraw : (incListToRaw x).1 = (incListToRaw y).1) : x = y := by
  rw [← encodeInc_decode x, ← encodeInc_decode y]
  exact congrArg encodeInc hraw

theorem lex_incListToRaw_iff {x y : IncList} :
    List.Lex (· < ·) (incListToRaw x).1 (incListToRaw y).1 ↔
      List.Lex (· < ·) x.1 y.1 := by
  rw [← lex_intoInc_iff 0]
  change List.Lex (· < ·)
    (intoInc 0 (fromInc 0 x.1)) (intoInc 0 (fromInc 0 y.1)) ↔ _
  rw [intoInc_fromInc_of_pairwise_ge 0 x.2 (fun _ _ ↦ Nat.zero_le _),
    intoInc_fromInc_of_pairwise_ge 0 y.2 (fun _ _ ↦ Nat.zero_le _)]

noncomputable def levelRawEmbedding
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true)) :
    (n : ℕ) → (@RawLevelLex n) ↪r (@RawLevelLex (emTargetLength n))
  | 0 => RelEmbedding.refl _
  | p + 1 => by
      let c : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool :=
        fun x y ↦ color (encodeInc x.1) (encodeInc y.1)
      have hccomm : ∀ x y, c x y = c y x := by
        intro x y
        exact hcomm _ _
      have hctri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
          ¬ (c x y = true ∧ c x z = true ∧ c y z = true) := by
        intro x y z hxy hxz hyz
        apply htri (encodeInc x.1) (encodeInc y.1) (encodeInc z.1)
        · intro h
          exact hxy (Subtype.ext (encodeInc_injective h))
        · intro h
          exact hxz (Subtype.ext (encodeInc_injective h))
        · intro h
          exact hyz (Subtype.ext (encodeInc_injective h))
      exact Classical.choose (rawLevel_erdos_milner p c hccomm hctri)

theorem rawLevel_cast_val {n m : ℕ} (h : n = m) (x : RawLevel m) :
    (cast (congrArg RawLevel h.symm) x : RawLevel n).1 = x.1 := by
  cases h
  rfl

theorem levelRawEmbedding_cast_val
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {n m : ℕ} (h : n = m) (x : RawLevel m) :
    ((levelRawEmbedding color hcomm htri n)
      (cast (congrArg RawLevel h.symm) x)).1 =
      (levelRawEmbedding color hcomm htri m x).1 := by
  cases h
  rfl

theorem levelRawEmbedding_red
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (n : ℕ) (x y : RawLevel n) (hxy : x ≠ y) :
    color (encodeInc ((levelRawEmbedding color hcomm htri n x).1))
      (encodeInc ((levelRawEmbedding color hcomm htri n y).1)) = false := by
  cases n with
  | zero =>
      exfalso
      apply hxy
      apply Subtype.ext
      rw [List.length_eq_zero_iff.mp x.2, List.length_eq_zero_iff.mp y.2]
  | succ p =>
      let c : RawLevel (p + (p + 1)) → RawLevel (p + (p + 1)) → Bool :=
        fun x y ↦ color (encodeInc x.1) (encodeInc y.1)
      have hccomm : ∀ x y, c x y = c y x := by
        intro x y
        exact hcomm _ _
      have hctri : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
          ¬ (c x y = true ∧ c x z = true ∧ c y z = true) := by
        intro a b d hab had hbd
        apply htri (encodeInc a.1) (encodeInc b.1) (encodeInc d.1)
        · intro h
          exact hab (Subtype.ext (encodeInc_injective h))
        · intro h
          exact had (Subtype.ext (encodeInc_injective h))
        · intro h
          exact hbd (Subtype.ext (encodeInc_injective h))
      exact Classical.choose_spec (rawLevel_erdos_milner p c hccomm hctri) x y hxy

/-- Arbitrary finite lists and increasing finite lists are the same
length--lex well order via gap encoding. -/
def encodeIncEquiv : List ℕ ≃ IncList where
  toFun := encodeInc
  invFun x := fromInc 0 x.1
  left_inv := fromInc_intoInc 0
  right_inv := encodeInc_decode

@[simp] theorem encodeIncEquiv_apply (s : List ℕ) :
    encodeIncEquiv s = encodeInc s := rfl

def encodeIncRelIso :
    List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ≃r LL where
  toEquiv := encodeIncEquiv
  map_rel_iff' := by
    intro a b
    change LL (encodeInc a) (encodeInc b) ↔ List.Shortlex (· < ·) a b
    exact encodeInc_LL_iff a b

/-- The ordinal code of a raw list: its fixed-length lexicographic rank,
placed immediately after the leading term `ω^length`. -/
noncomputable def rawListCode (s : List ℕ) : Ordinal :=
  ω ^ (s.length : Ordinal) +
    Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩

theorem rawListRank_lt (s : List ℕ) :
    Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩ <
      ω ^ (s.length : Ordinal) := by
  have h := Ordinal.typein_lt_type (@RawLevelLex s.length) ⟨s, rfl⟩
  rw [rawLevel_type, ← Ordinal.opow_natCast] at h
  exact h

theorem rawLevelRank_transport {n m : ℕ} (h : n = m) (t : List ℕ)
    (ht : t.length = m) :
    Ordinal.typein (@RawLevelLex m) (⟨t, ht⟩ : RawLevel m) =
      Ordinal.typein (@RawLevelLex n) (⟨t, ht.trans h.symm⟩ : RawLevel n) := by
  subst m
  rfl

theorem rawListCode_lt_omegaOmega (s : List ℕ) :
    rawListCode s < ω ^ ω := by
  have h := Ordinal.opow_mul_add_lt_opow
    (b := ω) (u := (s.length : Ordinal)) (v := 1)
    (w := Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩) (x := ω)
    Ordinal.one_lt_omega0 (rawListRank_lt s)
    (Ordinal.natCast_lt_omega0 s.length)
  simpa [rawListCode] using h

theorem rawListCode_strictMono {s t : List ℕ}
    (hst : List.Shortlex (· < ·) s t) :
    rawListCode s < rawListCode t := by
  rcases (List.shortlex_def.mp hst) with hlen | ⟨hlen, hlex⟩
  · have hbelow : rawListCode s < ω ^ (t.length : Ordinal) := by
      have h := Ordinal.opow_mul_add_lt_opow
        (b := ω) (u := (s.length : Ordinal)) (v := 1)
        (w := Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩)
        (x := (t.length : Ordinal)) Ordinal.one_lt_omega0
        (rawListRank_lt s) (by exact_mod_cast hlen)
      simpa [rawListCode] using h
    exact hbelow.trans_le (by simp [rawListCode])
  · unfold rawListCode
    have hrank := rawLevelRank_transport hlen t rfl
    rw [hrank]
    have hexp : ω ^ (t.length : Ordinal) = ω ^ (s.length : Ordinal) := by
      rw [hlen]
    rw [hexp]
    rw [add_lt_add_iff_left]
    exact (Ordinal.typein_lt_typein (@RawLevelLex s.length)).2 hlex

noncomputable def rawListCodeEmbedding :
    List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ↪r
      ((· < ·) : (ω ^ ω).ToType → (ω ^ ω).ToType → Prop) :=
  RelEmbedding.ofMonotone
    (fun s ↦ Ordinal.ToType.mk ⟨rawListCode s, rawListCode_lt_omegaOmega s⟩)
    (fun _ _ h ↦ Ordinal.ToType.mk.strictMono (rawListCode_strictMono h))

instance rawShortlexIsWellOrder :
    IsWellOrder (List ℕ) (List.Shortlex ((· < ·) : ℕ → ℕ → Prop)) where
  wf := List.Shortlex.wf Nat.lt_wfRel.wf

theorem rawShortlex_type :
    Ordinal.type (List.Shortlex ((· < ·) : ℕ → ℕ → Prop)) = ω ^ ω := by
  apply le_antisymm
  · have h := rawListCodeEmbedding.ordinal_type_le
    simpa [Ordinal.type_toType] using h
  · rw [← Ordinal.iSup_pow_natCast Ordinal.omega0_pos]
    apply Ordinal.iSup_le
    intro n
    rw [← rawLevel_type n]
    exact (RelEmbedding.ofMonotone
      (r := @RawLevelLex n)
      (s := List.Shortlex ((· < ·) : ℕ → ℕ → Prop))
      (fun x : RawLevel n ↦ x.1)
      (fun a b hab ↦ (List.shortlex_def).2
        (Or.inr ⟨a.2.trans b.2.symm, hab⟩))).ordinal_type_le

theorem incList_type : typeLT IncList = ω ^ ω := by
  change Ordinal.type LL = ω ^ ω
  rw [← (encodeIncRelIso.ordinalType_congr)]
  exact rawShortlex_type

/-! ## Larson blocks, forms, and interaction schemes -/

/-- Endpoints of consecutive nonempty blocks, measured from an initial
offset.  Thus the entries are the successive partial sums of block lengths. -/
def accLengths : ℕ → List (List α) → List ℕ
  | _, [] => []
  | n, a :: as => (n + a.length) :: accLengths (n + a.length) as

@[simp]
theorem length_accLengths (n : ℕ) (as : List (List α)) :
    (accLengths n as).length = as.length := by
  induction as generalizing n <;> simp [accLengths, *]

@[simp]
theorem accLengths_append (n : ℕ) (as bs : List (List α)) :
    accLengths n (as ++ bs) =
      accLengths n as ++ accLengths (n + (as.map List.length).sum) bs := by
  induction as generalizing n with
  | nil => simp [accLengths]
  | cons a as ih =>
      simp [accLengths, ih, Nat.add_assoc]

@[simp]
theorem getLast_accLengths_cons (n : ℕ) (a : List α) (as : List (List α)) :
    (accLengths n (a :: as)).getLast (by simp [accLengths]) =
      n + ((a :: as).map List.length).sum := by
  induction as generalizing n a with
  | nil => simp [accLengths]
  | cons b bs ih =>
      change (((n + a.length) :: accLengths (n + a.length) (b :: bs)).getLast _) = _
      rw [List.getLast_cons (by simp [accLengths]), ih]
      simp only [List.map_cons, List.sum_cons]
      omega

@[simp]
theorem getLast?_accLengths_cons (n : ℕ) (a : List α) (as : List (List α)) :
    (accLengths n (a :: as)).getLast? =
      some (n + ((a :: as).map List.length).sum) := by
  rw [List.getLast?_eq_some_getLast (by simp [accLengths]), getLast_accLengths_cons]

/-- Alternating concatenation of two lists of blocks, with any remaining
blocks appended after one side is exhausted. -/
def interact : List (List α) → List (List α) → List α
  | [], ys => ys.flatten
  | xs, [] => xs.flatten
  | x :: xs, y :: ys => x ++ y ++ interact xs ys

@[simp]
theorem interact_nil_left (ys : List (List α)) : interact [] ys = ys.flatten := rfl

@[simp]
theorem interact_nil_right (xs : List (List α)) : interact xs [] = xs.flatten := by
  cases xs <;> rfl

@[simp]
theorem length_interact (xs ys : List (List α)) :
    (interact xs ys).length = (xs.map List.length).sum + (ys.map List.length).sum := by
  induction xs, ys using interact.induct <;>
    simp [interact, *, Nat.add_assoc, Nat.add_left_comm]

@[simp]
theorem toFinset_interact [DecidableEq α] (xs ys : List (List α)) :
    (interact xs ys).toFinset = xs.flatten.toFinset ∪ ys.flatten.toFinset := by
  induction xs, ys using interact.induct <;>
    simp [interact, *, Finset.union_comm, Finset.union_left_comm]

theorem map_length_eq_of_accLengths_eq (n : ℕ) {as bs : List (List α)}
    (h : accLengths n as = accLengths n bs) :
    as.map List.length = bs.map List.length := by
  induction as generalizing n bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs => simp [accLengths] at h
  | cons a as ih =>
      cases bs with
      | nil => simp [accLengths] at h
      | cons b bs =>
          simp only [accLengths, List.cons.injEq] at h
          rcases h with ⟨hlen, htail⟩
          have hab : a.length = b.length := Nat.add_left_cancel hlen
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨hab, ?_⟩
          exact ih (n + a.length) (by simpa [hab] using htail)

theorem flatten_injective_of_map_length_eq {as bs : List (List α)}
    (hlen : as.map List.length = bs.map List.length)
    (hflat : as.flatten = bs.flatten) : as = bs := by
  induction as generalizing bs with
  | nil => simpa using hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at hlen
          rcases hlen with ⟨hab, hlen⟩
          simp only [List.flatten_cons] at hflat
          have hs := List.append_inj hflat hab
          have habList := hs.1
          have htail := hs.2
          subst b
          exact congrArg (List.cons a) (ih hlen htail)

/-- Alternating concatenation is injective once all block lengths are known. -/
theorem interact_injective_of_map_length_eq {as as' bs bs' : List (List α)}
    (ha : as.map List.length = as'.map List.length)
    (hb : bs.map List.length = bs'.map List.length)
    (hi : interact as bs = interact as' bs') : as = as' ∧ bs = bs' := by
  induction as, bs using interact.induct generalizing as' bs' with
  | case1 bs =>
      cases as' with
      | cons a as => simp at ha
      | nil =>
          exact ⟨rfl, flatten_injective_of_map_length_eq hb hi⟩
  | case2 as =>
      cases bs' with
      | cons b bs => simp at hb
      | nil =>
          exact ⟨flatten_injective_of_map_length_eq ha (by simpa [interact] using hi), rfl⟩
  | case3 a as b bs ih =>
      cases as' with
      | nil => simp at ha
      | cons a' as' =>
          cases bs' with
          | nil => simp at hb
          | cons b' bs' =>
              simp only [List.map_cons, List.cons.injEq] at ha hb
              rcases ha with ⟨haLen, ha⟩
              rcases hb with ⟨hbLen, hb⟩
              simp only [interact] at hi
              have habLen : (a ++ b).length = (a' ++ b').length := by
                simp [haLen, hbLen]
              have hsplit := List.append_inj hi habLen
              have habEq := hsplit.1
              have htail := hsplit.2
              rcases List.append_inj habEq haLen with ⟨haa, hbb⟩
              subst a'
              subst b'
              rcases ih ha hb htail with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩

/-- Larson's numerical interaction schemes form a prefix code when the two
block counts are fixed.  The first scheme entry determines the length of the
first left block.  The corresponding initial segments then determine both
lists of accumulated block lengths, whose last entries are the two total
sequence lengths.  Hence comparable schemes have equal total length. -/
theorem schemeExpression_prefix_rigid (ka kb : ℕ)
    (a a' b b' : List ℕ) (as as' bs bs' : List (List ℕ))
    (hka : (a :: as).length = ka) (hka' : (a' :: as').length = ka)
    (hkb : (b :: bs).length = kb) (hkb' : (b' :: bs').length = kb)
    (hp : accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs <+:
      accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
        interact as' bs') :
    accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs =
      accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
        interact as' bs' := by
  have hne :
      accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs ≠ [] := by
    simp [accLengths]
  have hhead := hp.head hne
  have halen : a.length = a'.length := by
    simpa [accLengths] using hhead
  let p := accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs)
  let p' := accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs')
  have hplen : p.length = p'.length := by
    dsimp [p, p']
    simp [hka, hka', hkb, hkb', halen]
  have htake :
      (accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs).take
          p.length = p := by
    dsimp [p]
    simpa only [List.append_assoc] using
      (List.take_left (l₁ := accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs))
        (l₂ := b ++ interact as bs))
  have htake' :
      (accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
          interact as' bs').take p.length = p' := by
    rw [hplen]
    dsimp [p']
    simpa only [List.append_assoc] using
      (List.take_left
        (l₁ := accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs'))
        (l₂ := b' ++ interact as' bs'))
  have hpp : p <+: p' := by
    simpa only [htake, htake'] using hp.take p.length
  have hpEq : p = p' := hpp.eq_of_length hplen
  have hAa : accLengths 0 (a :: as) ++ a = accLengths 0 (a' :: as') ++ a' := by
    apply List.append_inj_left hpEq
    simp [hka, hka', halen]
  have hB : accLengths 0 (b :: bs) = accLengths 0 (b' :: bs') := by
    apply List.append_inj_right hpEq
    simp [hka, hka', halen]
  have hA : accLengths 0 (a :: as) = accLengths 0 (a' :: as') := by
    apply List.append_inj_left hAa
    simp [hka, hka']
  have hxsum : ((a :: as).map List.length).sum =
      ((a' :: as').map List.length).sum := by
    have hx := congrArg List.getLast? hA
    simpa using hx
  have hysum : ((b :: bs).map List.length).sum =
      ((b' :: bs').map List.length).sum := by
    have hy := congrArg List.getLast? hB
    simpa using hy
  apply hp.eq_of_length
  simp only [List.length_append, length_accLengths, length_interact,
    List.map_cons, List.sum_cons] at hka hka' hkb hkb' hxsum hysum ⊢
  omega

/-- With fixed block counts, an interaction scheme determines both original
sequences. -/
theorem schemeExpression_injective (ka kb : ℕ)
    (a a' b b' : List ℕ) (as as' bs bs' : List (List ℕ))
    (hka : (a :: as).length = ka) (hka' : (a' :: as').length = ka)
    (hkb : (b :: bs).length = kb) (hkb' : (b' :: bs').length = kb)
    (hz : accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs =
      accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
        interact as' bs') :
    (a :: as).flatten = (a' :: as').flatten ∧
      (b :: bs).flatten = (b' :: bs').flatten := by
  have hp :
      accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs <+:
        accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
          interact as' bs' := hz ▸ List.prefix_rfl
  have hne :
      accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs ≠ [] := by
    simp [accLengths]
  have hhead := hp.head hne
  have halen : a.length = a'.length := by
    simpa [accLengths] using hhead
  let p := accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs)
  let p' := accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs')
  have hplen : p.length = p'.length := by
    dsimp [p, p']
    simp [hka, hka', hkb, hkb', halen]
  have htake :
      (accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs).take
          p.length = p := by
    dsimp [p]
    simpa only [List.append_assoc] using
      (List.take_left (l₁ := accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs))
        (l₂ := b ++ interact as bs))
  have htake' :
      (accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
          interact as' bs').take p.length = p' := by
    rw [hplen]
    dsimp [p']
    simpa only [List.append_assoc] using
      (List.take_left
        (l₁ := accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs'))
        (l₂ := b' ++ interact as' bs'))
  have hpEq : p = p' := by
    have hpp : p <+: p' := by simpa only [htake, htake'] using hp.take p.length
    exact hpp.eq_of_length hplen
  have hAa : accLengths 0 (a :: as) ++ a = accLengths 0 (a' :: as') ++ a' := by
    apply List.append_inj_left hpEq
    simp [hka, hka', halen]
  have hB : accLengths 0 (b :: bs) = accLengths 0 (b' :: bs') := by
    apply List.append_inj_right hpEq
    simp [hka, hka', halen]
  have hA : accLengths 0 (a :: as) = accLengths 0 (a' :: as') := by
    apply List.append_inj_left hAa
    simp [hka, hka']
  have haMap := map_length_eq_of_accLengths_eq 0 hA
  have hbMap := map_length_eq_of_accLengths_eq 0 hB
  have haData : a.length = a'.length ∧ as.map List.length = as'.map List.length := by
    simpa only [List.map_cons, List.cons.injEq] using haMap
  have haMap' : as.map List.length = as'.map List.length := haData.2
  have hbData : b.length = b'.length ∧ bs.map List.length = bs'.map List.length := by
    simpa only [List.map_cons, List.cons.injEq] using hbMap
  have haEq : a = a' := by
    apply List.append_inj_right hAa
    simp [hka, hka']
  have hz' : (p ++ b) ++ interact as bs = (p' ++ b') ++ interact as' bs' := by
    simpa [p, p'] using hz
  have hprefixLen : (p ++ b).length = (p' ++ b').length := by
    simp [hplen, hbData.1]
  have hsplit := List.append_inj hz' hprefixLen
  have hpb := hsplit.1
  have hi := hsplit.2
  have hbEq : b = b' := List.append_inj_right hpb hplen
  rcases interact_injective_of_map_length_eq haMap' hbData.2 hi with ⟨hasEq, hbsEq⟩
  subst a'
  subst b'
  subst as'
  subst bs'
  exact ⟨rfl, rfl⟩

/-- The witness data saying that `xs,ys` have Larson block counts
`ka,kb` and interaction scheme `zs`. -/
inductive FormBody (ka kb : ℕ) (xs ys zs : List ℕ) : Prop where
  | intro (a : List ℕ) (as : List (List ℕ)) (b : List ℕ) (bs : List (List ℕ))
      (length_lt : xs.length < ys.length)
      (xs_eq : xs = (a :: as).flatten)
      (ys_eq : ys = (b :: bs).flatten)
      (blocks_a_ne : ∀ q ∈ a :: as, q ≠ [])
      (blocks_b_ne : ∀ q ∈ b :: bs, q ≠ [])
      (blocks_a_length : (a :: as).length = ka)
      (blocks_b_length : (b :: bs).length = kb)
      (scheme_eq :
        zs = accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs)
      (scheme_strict : zs.Pairwise (· < ·)) : FormBody ka kb xs ys zs

theorem FormBody.scheme_inc {ka kb : ℕ} {xs ys zs : List ℕ}
    (h : FormBody ka kb xs ys zs) : zs.Pairwise (· < ·) := by
  cases h
  assumption

theorem FormBody.left_shorter {ka kb : ℕ} {xs ys zs : List ℕ}
    (h : FormBody ka kb xs ys zs) : xs.length < ys.length := by
  cases h
  assumption

/-- The entries added to a scheme besides the two original sequences are
exactly the two lists of block endpoints. -/
theorem FormBody.scheme_length {ka kb : ℕ} {xs ys zs : List ℕ}
    (h : FormBody ka kb xs ys zs) :
    zs.length = ka + kb + xs.length + ys.length := by
  rcases h with ⟨a, as, b, bs, hlt, rfl, rfl, hane, hbne, hka, hkb, rfl, hinc⟩
  simp only [List.length_append, length_accLengths, length_interact,
    List.length_flatten, List.map_cons, List.sum_cons] at hka hkb ⊢
  omega

/-- Two schemes belonging to form bodies with the same block counts cannot
be proper initial segments of one another. -/
theorem FormBody.eq_of_isPrefix {ka kb : ℕ}
    {xs ys xs' ys' zs zs' : List ℕ}
    (h : FormBody ka kb xs ys zs) (h' : FormBody ka kb xs' ys' zs')
    (hp : zs <+: zs') : zs = zs' := by
  rcases h with
    ⟨a, as, b, bs, hlt, hxs, hys, hane, hbne, hka, hkb, hzs, hinc⟩
  rcases h' with
    ⟨a', as', b', bs', hlt', hxs', hys', hane', hbne', hka', hkb', hzs', hinc'⟩
  subst zs
  subst zs'
  exact schemeExpression_prefix_rigid ka kb a a' b b' as as' bs bs'
    hka hka' hkb hkb' hp

/-- For fixed block counts, equality of schemes determines the two ordered
sequences in the orientation used by the form bodies. -/
theorem FormBody.eq_sequences_of_scheme_eq {ka kb : ℕ}
    {xs ys xs' ys' zs : List ℕ}
    (h : FormBody ka kb xs ys zs) (h' : FormBody ka kb xs' ys' zs) :
    xs = xs' ∧ ys = ys' := by
  rcases h with
    ⟨a, as, b, bs, hlt, hxs, hys, hane, hbne, hka, hkb, hzs, hinc⟩
  rcases h' with
    ⟨a', as', b', bs', hlt', hxs', hys', hane', hbne', hka', hkb', hzs', hinc'⟩
  have hz :
      accLengths 0 (a :: as) ++ a ++ accLengths 0 (b :: bs) ++ b ++ interact as bs =
        accLengths 0 (a' :: as') ++ a' ++ accLengths 0 (b' :: bs') ++ b' ++
          interact as' bs' := hzs.symm.trans hzs'
  rcases schemeExpression_injective ka kb a a' b b' as as' bs bs'
      hka hka' hkb hkb' hz with ⟨hx, hy⟩
  exact ⟨hxs.trans (hx.trans hxs'.symm), hys.trans (hy.trans hys'.symm)⟩

theorem formBody_or_unordered_eq {ka kb : ℕ} {x y x' y' : IncList} {zs : List ℕ}
    (h : FormBody ka kb x.1 y.1 zs ∨ FormBody ka kb y.1 x.1 zs)
    (h' : FormBody ka kb x'.1 y'.1 zs ∨ FormBody ka kb y'.1 x'.1 zs) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  rcases h with h | h <;> rcases h' with h' | h'
  · rcases h.eq_sequences_of_scheme_eq h' with ⟨hx, hy⟩
    exact Or.inl ⟨IncList.ext hx, IncList.ext hy⟩
  · rcases h.eq_sequences_of_scheme_eq h' with ⟨hx, hy⟩
    exact Or.inr ⟨IncList.ext hx, IncList.ext hy⟩
  · rcases h.eq_sequences_of_scheme_eq h' with ⟨hy, hx⟩
    exact Or.inr ⟨IncList.ext hx, IncList.ext hy⟩
  · rcases h.eq_sequences_of_scheme_eq h' with ⟨hy, hx⟩
    exact Or.inl ⟨IncList.ext hx, IncList.ext hy⟩

/-- `HasForm l x y` is Larson's form relation.  Form zero consists of
distinct equal-length sequences.  Positive odd forms have equally many
blocks on the two sides; positive even forms have one extra block on the
shorter side. -/
def HasForm (l : ℕ) (x y : IncList) : Prop :=
  (l = 0 ∧ x ≠ y ∧ x.1.length = y.1.length) ∨
    (∃ k zs, 0 < k ∧ l = 2 * k - 1 ∧
      (FormBody k k x.1 y.1 zs ∨ FormBody k k y.1 x.1 zs)) ∨
    ∃ k zs, 0 < k ∧ l = 2 * k ∧
      (FormBody (k + 1) k x.1 y.1 zs ∨ FormBody (k + 1) k y.1 x.1 zs)

theorem HasForm.symm {l : ℕ} {x y : IncList} (h : HasForm l x y) : HasForm l y x := by
  rcases h with ⟨rfl, hxy, hlen⟩ | ⟨k, zs, hk, hl, h⟩ | ⟨k, zs, hk, hl, h⟩
  · exact Or.inl ⟨rfl, hxy.symm, hlen.symm⟩
  · exact Or.inr <| Or.inl ⟨k, zs, hk, hl, h.symm⟩
  · exact Or.inr <| Or.inr ⟨k, zs, hk, hl, h.symm⟩

theorem hasForm_zero {x y : IncList} (hxy : x ≠ y)
    (hlen : x.1.length = y.1.length) : HasForm 0 x y :=
  Or.inl ⟨rfl, hxy, hlen⟩

theorem HasForm.ne {l : ℕ} {x y : IncList} (h : HasForm l x y) : x ≠ y := by
  rcases h with ⟨-, hxy, -⟩ | ⟨k, zs, hk, hl, hbody⟩ | ⟨k, zs, hk, hl, hbody⟩
  · exact hxy
  · intro hxy
    subst y
    rcases hbody with hbody | hbody <;>
      exact (Nat.lt_irrefl _ hbody.left_shorter)
  · intro hxy
    subst y
    rcases hbody with hbody | hbody <;>
      exact (Nat.lt_irrefl _ hbody.left_shorter)

/-- The numerical schemes occurring at one fixed positive form.  This
predicate deliberately forgets the witnessing pair; injectivity is proved
separately, while thinness only needs the block counts. -/
def IsFormScheme (l : ℕ) (zs : List ℕ) : Prop :=
  (∃ (k : ℕ) (x y : IncList), 0 < k ∧ l = 2 * k - 1 ∧
      (FormBody k k x.1 y.1 zs ∨ FormBody k k y.1 x.1 zs)) ∨
    ∃ (k : ℕ) (x y : IncList), 0 < k ∧ l = 2 * k ∧
      (FormBody (k + 1) k x.1 y.1 zs ∨ FormBody (k + 1) k y.1 x.1 zs)

/-- A family of finite lists is thin when comparable members are equal. -/
def Thin (A : Set (List ℕ)) : Prop :=
  ∀ ⦃s⦄, s ∈ A → ∀ ⦃t⦄, t ∈ A → s <+: t → s = t

/-- Larson's Lemma 3.11: the schemes of every fixed positive form are thin. -/
theorem isFormScheme_thin (l : ℕ) : Thin {zs | IsFormScheme l zs} := by
  intro zs hzs zs' hzs' hp
  rcases hzs with ⟨k, x, y, hk, hl, hbody⟩ | ⟨k, x, y, hk, hl, hbody⟩ <;>
    rcases hzs' with ⟨k', x', y', hk', hl', hbody'⟩ |
      ⟨k', x', y', hk', hl', hbody'⟩
  · have hkk : k = k' := by omega
    subst k'
    rcases hbody with hbody | hbody <;>
      rcases hbody' with hbody' | hbody' <;>
      exact hbody.eq_of_isPrefix hbody' hp
  · omega
  · omega
  · have hkk : k = k' := by omega
    subst k'
    rcases hbody with hbody | hbody <;>
      rcases hbody' with hbody' | hbody' <;>
      exact hbody.eq_of_isPrefix hbody' hp

/-- A canonical interaction scheme, chosen from the form witness.  The empty
list is returned off the domain; later lemmas only use this definition under
`HasForm l x y` with `l>0`. -/
noncomputable def interScheme (l : ℕ) (x y : IncList) : List ℕ :=
  by
    classical
    exact if h : ∃ zs, (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
        (FormBody k k x.1 y.1 zs ∨ FormBody k k y.1 x.1 zs)) ∨
        (∃ k, 0 < k ∧ l = 2 * k ∧
        (FormBody (k + 1) k x.1 y.1 zs ∨ FormBody (k + 1) k y.1 x.1 zs))
      then Classical.choose h
      else []

theorem interScheme_spec {l : ℕ} {x y : IncList} (hl : 0 < l)
    (hform : HasForm l x y) :
    (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
      (FormBody k k x.1 y.1 (interScheme l x y) ∨
        FormBody k k y.1 x.1 (interScheme l x y))) ∨
    ∃ k, 0 < k ∧ l = 2 * k ∧
      (FormBody (k + 1) k x.1 y.1 (interScheme l x y) ∨
        FormBody (k + 1) k y.1 x.1 (interScheme l x y)) := by
  rcases hform with ⟨hl0, -, -⟩ | hodd | heven
  · exact (hl.ne' hl0).elim
  · rcases hodd with ⟨k, zs, hk, hlk, hbody⟩
    have hex : ∃ zs, (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
        (FormBody k k x.1 y.1 zs ∨ FormBody k k y.1 x.1 zs)) ∨
        (∃ k, 0 < k ∧ l = 2 * k ∧
        (FormBody (k + 1) k x.1 y.1 zs ∨ FormBody (k + 1) k y.1 x.1 zs)) :=
      ⟨zs, Or.inl ⟨k, hk, hlk, hbody⟩⟩
    rw [interScheme, dif_pos hex]
    exact (Classical.choose_spec hex)
  · rcases heven with ⟨k, zs, hk, hlk, hbody⟩
    have hex : ∃ zs, (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
        (FormBody k k x.1 y.1 zs ∨ FormBody k k y.1 x.1 zs)) ∨
        (∃ k, 0 < k ∧ l = 2 * k ∧
        (FormBody (k + 1) k x.1 y.1 zs ∨ FormBody (k + 1) k y.1 x.1 zs)) :=
      ⟨zs, Or.inr ⟨k, hk, hlk, hbody⟩⟩
    rw [interScheme, dif_pos hex]
    exact (Classical.choose_spec hex)

theorem interScheme_isFormScheme {l : ℕ} {x y : IncList} (hl : 0 < l)
    (hform : HasForm l x y) : IsFormScheme l (interScheme l x y) := by
  rcases interScheme_spec hl hform with ⟨k, hk, hlk, hbody⟩ | ⟨k, hk, hlk, hbody⟩
  · exact Or.inl ⟨k, x, y, hk, hlk, hbody⟩
  · exact Or.inr ⟨k, x, y, hk, hlk, hbody⟩

theorem hasForm_min_max {l : ℕ} {x y : IncList} (hform : HasForm l x y) :
    HasForm l (min x y) (max x y) := by
  rcases le_total x y with hxy | hyx
  · simpa [min_eq_left hxy, max_eq_right hxy] using hform
  · simpa [min_eq_right hyx, max_eq_left hyx] using hform.symm

/-- The canonical scheme of an unordered pair. -/
noncomputable def pairScheme (l : ℕ) (x y : IncList) : List ℕ :=
  interScheme l (min x y) (max x y)

theorem pairScheme_comm (l : ℕ) (x y : IncList) :
    pairScheme l x y = pairScheme l y x := by
  simp [pairScheme, min_comm, max_comm]

theorem pairScheme_isFormScheme {l : ℕ} {x y : IncList} (hl : 0 < l)
    (hform : HasForm l x y) : IsFormScheme l (pairScheme l x y) :=
  interScheme_isFormScheme hl (hasForm_min_max hform)

/-- A positive-form scheme determines its unordered pair. -/
theorem pairScheme_injective_unordered {l : ℕ} {x y x' y' : IncList}
    (hl : 0 < l) (hform : HasForm l x y) (hform' : HasForm l x' y')
    (hscheme : pairScheme l x y = pairScheme l x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have hs :
      (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
        (FormBody k k (min x y).1 (max x y).1 (pairScheme l x y) ∨
          FormBody k k (max x y).1 (min x y).1 (pairScheme l x y))) ∨
      ∃ k, 0 < k ∧ l = 2 * k ∧
        (FormBody (k + 1) k (min x y).1 (max x y).1 (pairScheme l x y) ∨
          FormBody (k + 1) k (max x y).1 (min x y).1 (pairScheme l x y)) := by
    simpa only [pairScheme] using interScheme_spec hl (hasForm_min_max hform)
  have hs' :
      (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
        (FormBody k k (min x' y').1 (max x' y').1 (pairScheme l x' y') ∨
          FormBody k k (max x' y').1 (min x' y').1 (pairScheme l x' y'))) ∨
      ∃ k, 0 < k ∧ l = 2 * k ∧
        (FormBody (k + 1) k (min x' y').1 (max x' y').1 (pairScheme l x' y') ∨
          FormBody (k + 1) k (max x' y').1 (min x' y').1 (pairScheme l x' y')) := by
    simpa only [pairScheme] using interScheme_spec hl (hasForm_min_max hform')
  rw [← hscheme] at hs'
  have hsorted :
      ((min x y = min x' y' ∧ max x y = max x' y') ∨
        (min x y = max x' y' ∧ max x y = min x' y')) := by
    rcases hs with ⟨k, hk, hlk, hbody⟩ | ⟨k, hk, hlk, hbody⟩ <;>
      rcases hs' with ⟨k', hk', hlk', hbody'⟩ | ⟨k', hk', hlk', hbody'⟩
    · have hkk : k = k' := by omega
      subst k'
      exact formBody_or_unordered_eq hbody hbody'
    · omega
    · omega
    · have hkk : k = k' := by omega
      subst k'
      exact formBody_or_unordered_eq hbody hbody'
  have hsortedSet :
      ({min x y, max x y} : Set IncList) = {min x' y', max x' y'} :=
    Set.pair_eq_pair_iff.mpr hsorted
  have hleft : ({min x y, max x y} : Set IncList) = {x, y} := by
    rcases le_total x y with hxy | hyx
    · simp [min_eq_left hxy, max_eq_right hxy]
    · simp [min_eq_right hyx, max_eq_left hyx, Set.pair_comm]
  have hright : ({min x' y', max x' y'} : Set IncList) = {x', y'} := by
    rcases le_total x' y' with hxy | hyx
    · simp [min_eq_left hxy, max_eq_right hxy]
    · simp [min_eq_right hyx, max_eq_left hyx, Set.pair_comm]
  exact Set.pair_eq_pair_iff.mp (hleft.symm.trans (hsortedSet.trans hright))

/-! ## Nash--Williams for thin families -/

namespace NashWilliams

/-- `s` is an initial segment of `t` when `s ⊆ t` and every new member of
`t` lies above every member of `s`. -/
def InitSeg (s t : Finset ℕ) : Prop :=
  s ⊆ t ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ t → y ∉ s → x < y

theorem InitSeg.refl (s : Finset ℕ) : InitSeg s s := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro x hxs y hys hyns
  exact (hyns hys).elim

theorem InitSeg.subset {s t : Finset ℕ} (h : InitSeg s t) : s ⊆ t := h.1

theorem InitSeg.trans {r s t : Finset ℕ} (hrs : InitSeg r s) (hst : InitSeg s t) :
    InitSeg r t := by
  refine ⟨hrs.1.trans hst.1, ?_⟩
  intro x hxr y hyt hyr
  by_cases hys : y ∈ s
  · exact hrs.2 hxr hys hyr
  · exact hst.2 (hrs.1 hxr) hyt hys

theorem initSeg_insert (s : Finset ℕ) {n : ℕ}
    (hn : ∀ x ∈ s, x < n) : InitSeg s (insert n s) := by
  refine ⟨Finset.subset_insert n s, ?_⟩
  intro x hxs y hys hyns
  simp only [Finset.mem_insert] at hys
  rcases hys with rfl | hys
  · exact hn x hxs
  · exact (hyns hys).elim

/-- A family of finite subsets is thin under `InitSeg`. -/
def FinThin (𝓕 : Set (Finset ℕ)) : Prop :=
  ∀ ⦃s⦄, s ∈ 𝓕 → ∀ ⦃t⦄, t ∈ 𝓕 → InitSeg s t → s = t

/-- A member of `𝓕` comparable with `s`, whose part beyond `s` is drawn
from `M`. -/
def ComparableMember (𝓕 : Set (Finset ℕ)) (s : Finset ℕ) (M : Set ℕ) (t : Finset ℕ) : Prop :=
  t ∈ 𝓕 ∧ (InitSeg t s ∨ InitSeg s t ∧ (↑(t \ s) : Set ℕ) ⊆ M)

def Rejects (𝓕 : Set (Finset ℕ)) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  ¬ ∃ t, ComparableMember 𝓕 s M t

def StronglyAccepts (𝓕 : Set (Finset ℕ)) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  ∀ N, N ⊆ M → Rejects 𝓕 s N → N.Finite

def Decides (𝓕 : Set (Finset ℕ)) (s : Finset ℕ) (M : Set ℕ) : Prop :=
  Rejects 𝓕 s M ∨ StronglyAccepts 𝓕 s M

def DecidesSubsets (𝓕 : Set (Finset ℕ)) (M : Set ℕ) : Prop :=
  ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → Decides 𝓕 s M

theorem comparableMember_mono {𝓕 : Set (Finset ℕ)} {s t : Finset ℕ} {N M : Set ℕ}
    (hNM : N ⊆ M) (h : ComparableMember 𝓕 s N t) : ComparableMember 𝓕 s M t := by
  rcases h with ⟨ht, hts | ⟨hst, hdiff⟩⟩
  · exact ⟨ht, Or.inl hts⟩
  · exact ⟨ht, Or.inr ⟨hst, hdiff.trans hNM⟩⟩

theorem Rejects.mono {𝓕 : Set (Finset ℕ)} {s : Finset ℕ} {N M : Set ℕ}
    (h : Rejects 𝓕 s M) (hNM : N ⊆ M) : Rejects 𝓕 s N := by
  intro hex
  rcases hex with ⟨t, ht⟩
  exact h ⟨t, comparableMember_mono hNM ht⟩

theorem StronglyAccepts.mono {𝓕 : Set (Finset ℕ)} {s : Finset ℕ} {N M : Set ℕ}
    (h : StronglyAccepts 𝓕 s M) (hNM : N ⊆ M) : StronglyAccepts 𝓕 s N := by
  intro P hPN hre
  exact h P (hPN.trans hNM) hre

theorem Decides.mono {𝓕 : Set (Finset ℕ)} {s : Finset ℕ} {N M : Set ℕ}
    (h : Decides 𝓕 s M) (hNM : N ⊆ M) : Decides 𝓕 s N := by
  rcases h with h | h
  · exact Or.inl (h.mono hNM)
  · exact Or.inr (h.mono hNM)

theorem StronglyAccepts.accepts {𝓕 : Set (Finset ℕ)} {s : Finset ℕ} {M : Set ℕ}
    (h : StronglyAccepts 𝓕 s M) (hM : M.Infinite) :
    ∃ t, ComparableMember 𝓕 s M t := by
  by_contra hre
  exact hM (h M Set.Subset.rfl hre)

theorem exists_infinite_decides (𝓕 : Set (Finset ℕ)) (s : Finset ℕ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ Decides 𝓕 s N := by
  by_cases h : StronglyAccepts 𝓕 s M
  · exact ⟨M, Set.Subset.rfl, hM, Or.inr h⟩
  · simp only [StronglyAccepts] at h
    push Not at h
    rcases h with ⟨N, hNM, hreject, hNinf⟩
    exact ⟨N, hNM, hNinf, Or.inl hreject⟩

theorem exists_infinite_decides_family (𝓕 : Set (Finset ℕ))
    (Q : Finset (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ ∀ s ∈ Q, Decides 𝓕 s N := by
  induction Q using Finset.induction_on with
  | empty => exact ⟨M, Set.Subset.rfl, hM, by simp⟩
  | @insert s Q hs ih =>
      rcases ih with ⟨N, hNM, hNinf, hNdec⟩
      rcases exists_infinite_decides 𝓕 s hNinf with ⟨P, hPN, hPinf, hPdec⟩
      refine ⟨P, hPN.trans hNM, hPinf, ?_⟩
      intro t ht
      simp only [Finset.mem_insert] at ht
      rcases ht with rfl | ht
      · exact hPdec
      · exact (hNdec t ht).mono hPN

theorem exists_infinite_decides_subsets_of_finset (𝓕 : Set (Finset ℕ))
    (s : Finset ℕ) {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ ∀ t, t ⊆ s → Decides 𝓕 t N := by
  rcases exists_infinite_decides_family 𝓕 s.powerset hM with ⟨N, hNM, hNinf, hdec⟩
  exact ⟨N, hNM, hNinf, fun t ht => hdec t (Finset.mem_powerset.mpr ht)⟩

/-- One stage of the fusion construction.  `marks` is the finite initial
part already selected, and `tail` is an infinite set above it that decides
every subset of `marks`. -/
structure FusionState (𝓕 : Set (Finset ℕ)) (M : Set ℕ) where
  marks : Finset ℕ
  tail : Set ℕ
  tail_infinite : tail.Infinite
  marks_subset : (↑marks : Set ℕ) ⊆ M
  tail_subset : tail ⊆ M
  above : ∀ ⦃x⦄, x ∈ marks → ∀ ⦃y⦄, y ∈ tail → x < y
  decides : ∀ s, s ⊆ marks → Decides 𝓕 s tail

theorem fusionState_nonempty (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    Nonempty (FusionState 𝓕 M) := by
  rcases exists_infinite_decides 𝓕 ∅ hM with ⟨N, hNM, hNinf, hNdec⟩
  refine ⟨{
    marks := ∅
    tail := N
    tail_infinite := hNinf
    marks_subset := by simp
    tail_subset := hNM
    above := by simp
    decides := ?_ }⟩
  intro s hs
  have hsempty : s = ∅ := Finset.Subset.antisymm hs (by simp)
  simpa [hsempty] using hNdec

/-- The data selected when one fusion stage is extended. -/
structure FusionExtension {𝓕 : Set (Finset ℕ)} {M : Set ℕ} (st : FusionState 𝓕 M) where
  pick : ℕ
  next : FusionState 𝓕 M
  pick_mem_tail : pick ∈ st.tail
  marks_eq : next.marks = insert pick st.marks
  tail_subset : next.tail ⊆ st.tail
  pick_below_tail : ∀ ⦃y⦄, y ∈ next.tail → pick < y

theorem fusionExtension_nonempty {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (st : FusionState 𝓕 M) : Nonempty (FusionExtension st) := by
  let n := sInf st.tail
  have hn : n ∈ st.tail := Nat.sInf_mem st.tail_infinite.nonempty
  let B : Set ℕ := st.tail \ Set.Iic n
  have hBinf : B.Infinite := st.tail_infinite.sdiff (Set.finite_Iic n)
  rcases exists_infinite_decides_subsets_of_finset 𝓕 (insert n st.marks) hBinf with
    ⟨C, hCB, hCinf, hCdec⟩
  have hCtail : C ⊆ st.tail := hCB.trans Set.sdiff_subset
  have hnC : ∀ ⦃y⦄, y ∈ C → n < y := by
    intro y hy
    have hyB := hCB hy
    exact Nat.lt_of_not_ge hyB.2
  let st' : FusionState 𝓕 M := {
    marks := insert n st.marks
    tail := C
    tail_infinite := hCinf
    marks_subset := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact st.tail_subset hn
      · exact st.marks_subset hx
    tail_subset := hCtail.trans st.tail_subset
    above := by
      intro x hx y hy
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hnC hy
      · exact st.above hx (hCtail hy)
    decides := hCdec }
  exact ⟨{
    pick := n
    next := st'
    pick_mem_tail := hn
    marks_eq := rfl
    tail_subset := hCtail
    pick_below_tail := hnC }⟩

noncomputable def FusionState.extend {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (st : FusionState 𝓕 M) : FusionExtension st :=
  Classical.choice (fusionExtension_nonempty st)

noncomputable def fusionInitial (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    FusionState 𝓕 M :=
  Classical.choice (fusionState_nonempty 𝓕 hM)

noncomputable def fusionSeq (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    ℕ → FusionState 𝓕 M
  | 0 => fusionInitial 𝓕 hM
  | n + 1 => (fusionSeq 𝓕 hM n).extend.next

noncomputable def fusionPick (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ℕ :=
  (fusionSeq 𝓕 hM n).extend.pick

@[simp]
theorem fusionSeq_zero (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    fusionSeq 𝓕 hM 0 = fusionInitial 𝓕 hM := rfl

theorem fusionSeq_succ (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) (n : ℕ) :
    fusionSeq 𝓕 hM (n + 1) = (fusionSeq 𝓕 hM n).extend.next := rfl

theorem fusionPick_mem_tail (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) (n : ℕ) :
    fusionPick 𝓕 hM n ∈ (fusionSeq 𝓕 hM n).tail :=
  (fusionSeq 𝓕 hM n).extend.pick_mem_tail

theorem fusion_marks_succ (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) (n : ℕ) :
    (fusionSeq 𝓕 hM (n + 1)).marks =
      insert (fusionPick 𝓕 hM n) (fusionSeq 𝓕 hM n).marks := by
  rw [fusionSeq_succ]
  exact (fusionSeq 𝓕 hM n).extend.marks_eq

theorem fusion_tail_succ_subset (𝓕 : Set (Finset ℕ)) {M : Set ℕ}
    (hM : M.Infinite) (n : ℕ) :
    (fusionSeq 𝓕 hM (n + 1)).tail ⊆ (fusionSeq 𝓕 hM n).tail := by
  rw [fusionSeq_succ]
  exact (fusionSeq 𝓕 hM n).extend.tail_subset

theorem fusion_pick_below_next_tail (𝓕 : Set (Finset ℕ)) {M : Set ℕ}
    (hM : M.Infinite) (n : ℕ) :
    ∀ ⦃y⦄, y ∈ (fusionSeq 𝓕 hM (n + 1)).tail → fusionPick 𝓕 hM n < y := by
  rw [fusionSeq_succ]
  exact (fusionSeq 𝓕 hM n).extend.pick_below_tail

theorem fusion_marks_mono (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    (fusionSeq 𝓕 hM i).marks ⊆ (fusionSeq 𝓕 hM j).marks := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact Finset.Subset.rfl
      · have hij' : i ≤ j := by omega
        refine (ih hij').trans ?_
        rw [show j + 1 = j + 1 by rfl, fusion_marks_succ]
        exact Finset.subset_insert _ _

theorem fusion_tail_antitone (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    (fusionSeq 𝓕 hM j).tail ⊆ (fusionSeq 𝓕 hM i).tail := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Set.Subset.rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact Set.Subset.rfl
      · have hij' : i ≤ j := by omega
        exact (fusion_tail_succ_subset 𝓕 hM j).trans (ih hij')

theorem fusionPick_strictMono (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    StrictMono (fusionPick 𝓕 hM) := by
  intro i j hij
  have hmark : fusionPick 𝓕 hM i ∈ (fusionSeq 𝓕 hM j).marks := by
    apply fusion_marks_mono 𝓕 hM (show i + 1 ≤ j by omega)
    rw [fusion_marks_succ]
    simp
  exact (fusionSeq 𝓕 hM j).above hmark (fusionPick_mem_tail 𝓕 hM j)

def fusionSet (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) : Set ℕ :=
  Set.range (fusionPick 𝓕 hM)

theorem fusionSet_infinite (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    (fusionSet 𝓕 hM).Infinite :=
  Set.infinite_range_of_injective (fusionPick_strictMono 𝓕 hM).injective

theorem fusionSet_subset (𝓕 : Set (Finset ℕ)) {M : Set ℕ} (hM : M.Infinite) :
    fusionSet 𝓕 hM ⊆ M := by
  rintro x ⟨n, rfl⟩
  exact (fusionSeq 𝓕 hM n).tail_subset (fusionPick_mem_tail 𝓕 hM n)

theorem fusionPick_mem_earlier_tail (𝓕 : Set (Finset ℕ)) {M : Set ℕ}
    (hM : M.Infinite) {i j : ℕ} (hij : i ≤ j) :
    fusionPick 𝓕 hM j ∈ (fusionSeq 𝓕 hM i).tail :=
  fusion_tail_antitone 𝓕 hM hij (fusionPick_mem_tail 𝓕 hM j)

theorem fusionSet_subset_tail_zero (𝓕 : Set (Finset ℕ)) {M : Set ℕ}
    (hM : M.Infinite) : fusionSet 𝓕 hM ⊆ (fusionSeq 𝓕 hM 0).tail := by
  rintro x ⟨j, rfl⟩
  exact fusionPick_mem_earlier_tail 𝓕 hM (Nat.zero_le j)

theorem fusionSet_sdiff_tail_finite (𝓕 : Set (Finset ℕ)) {M : Set ℕ}
    (hM : M.Infinite) (k : ℕ) :
    (fusionSet 𝓕 hM \ (fusionSeq 𝓕 hM k).tail).Finite := by
  apply (Finset.finite_toSet ((Finset.range k).image (fusionPick 𝓕 hM))).subset
  rintro x ⟨⟨j, rfl⟩, hjnot⟩
  have hjk : j < k := by
    by_contra h
    exact hjnot (fusionPick_mem_earlier_tail 𝓕 hM (by omega))
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  exact ⟨j, hjk, rfl⟩

theorem StronglyAccepts.of_finite_sdiff {𝓕 : Set (Finset ℕ)} {s : Finset ℕ}
    {M N : Set ℕ} (h : StronglyAccepts 𝓕 s M) (hfinite : (N \ M).Finite) :
    StronglyAccepts 𝓕 s N := by
  intro P hPN hPrej
  have hinter_rej : Rejects 𝓕 s (P ∩ M) := hPrej.mono Set.inter_subset_left
  have hinter_fin : (P ∩ M).Finite := h (P ∩ M) Set.inter_subset_right hinter_rej
  have hdiff_fin : (P \ M).Finite := hfinite.subset (fun x hx => ⟨hPN hx.1, hx.2⟩)
  apply (hinter_fin.union hdiff_fin).subset
  intro x hx
  by_cases hxM : x ∈ M
  · exact Or.inl ⟨hx, hxM⟩
  · exact Or.inr ⟨hx, hxM⟩

theorem fusion_rejects {𝓕 : Set (Finset ℕ)} {M : Set ℕ} (hM : M.Infinite)
    {s : Finset ℕ} {k : ℕ} (hpk : fusionPick 𝓕 hM k ∈ s)
    (hrej : Rejects 𝓕 s (fusionSeq 𝓕 hM (k + 1)).tail) :
    Rejects 𝓕 s (fusionSet 𝓕 hM) := by
  intro hex
  rcases hex with ⟨t, htF, hts | ⟨hst, hdiff⟩⟩
  · exact hrej ⟨t, htF, Or.inl hts⟩
  · apply hrej
    refine ⟨t, htF, Or.inr ⟨hst, ?_⟩⟩
    intro y hy
    have hyN := hdiff hy
    rcases hyN with ⟨j, rfl⟩
    have hyts : fusionPick 𝓕 hM j ∈ t ∧ fusionPick 𝓕 hM j ∉ s :=
      Finset.mem_sdiff.mp hy
    have hlt : fusionPick 𝓕 hM k < fusionPick 𝓕 hM j :=
      hst.2 hpk hyts.1 hyts.2
    have hkj : k < j := (fusionPick_strictMono 𝓕 hM).lt_iff_lt.mp hlt
    exact fusionPick_mem_earlier_tail 𝓕 hM (by omega)

/-- The diagonal range produced by fusion decides all of its finite
subsets.  For a nonempty subset, the stage indexed by its last selected
point is the decisive stage; earlier selected points cannot occur beyond
that subset in an initial-segment extension. -/
theorem fusionSet_decidesSubsets (𝓕 : Set (Finset ℕ)) {M : Set ℕ}
    (hM : M.Infinite) : DecidesSubsets 𝓕 (fusionSet 𝓕 hM) := by
  intro s hsN
  by_cases hs0 : s = ∅
  · subst s
    exact ((fusionSeq 𝓕 hM 0).decides ∅ (by simp)).mono
      (fusionSet_subset_tail_zero 𝓕 hM)
  · let f : ℕ → ℕ := fusionPick 𝓕 hM
    let g : ℕ → ℕ := Function.invFun f
    let I : Finset ℕ := s.image g
    have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    have hIne : I.Nonempty := hsne.image g
    let k : ℕ := I.max' hIne
    have hfg : ∀ {x}, x ∈ s → f (g x) = x := by
      intro x hxs
      exact Function.invFun_eq (hsN hxs)
    have hkI : k ∈ I := Finset.max'_mem I hIne
    rcases Finset.mem_image.mp hkI with ⟨x, hxs, hgx⟩
    have hpk : fusionPick 𝓕 hM k ∈ s := by
      have hfx := hfg hxs
      change f k ∈ s
      rw [← hgx, hfx]
      exact hxs
    have hsmarks : s ⊆ (fusionSeq 𝓕 hM (k + 1)).marks := by
      intro y hys
      have hgyI : g y ∈ I := Finset.mem_image.mpr ⟨y, hys, rfl⟩
      have hgyle : g y ≤ k := Finset.le_max' I (g y) hgyI
      have hmem : fusionPick 𝓕 hM (g y) ∈
          (fusionSeq 𝓕 hM (g y + 1)).marks := by
        rw [fusion_marks_succ]
        simp
      have hmem' := fusion_marks_mono 𝓕 hM (Nat.succ_le_succ hgyle) hmem
      change f (g y) ∈ (fusionSeq 𝓕 hM (k + 1)).marks at hmem'
      rw [hfg hys] at hmem'
      exact hmem'
    rcases (fusionSeq 𝓕 hM (k + 1)).decides s hsmarks with hrej | hacc
    · exact Or.inl (fusion_rejects hM hpk hrej)
    · exact Or.inr (hacc.of_finite_sdiff (fusionSet_sdiff_tail_finite 𝓕 hM (k + 1)))

theorem InitSeg.insert_min_sdiff {s t : Finset ℕ} (hst : InitSeg s t)
    (hne : (t \ s).Nonempty) : InitSeg (insert ((t \ s).min' hne) s) t := by
  let n := (t \ s).min' hne
  have hnmem : n ∈ t \ s := Finset.min'_mem (t \ s) hne
  have hnt : n ∈ t := (Finset.mem_sdiff.mp hnmem).1
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hnt
    · exact hst.1 hx
  · intro x hx y hyt hyn
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hxs
    · have hys : y ∉ s := by
        intro hys
        exact hyn (by simp [hys])
      have hymem : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hyt, hys⟩
      have hny : n ≤ y := Finset.min'_le _ _ hymem
      exact lt_of_le_of_ne hny (by
        intro hnyEq
        subst y
        exact hyn (by simp))
    · have hys : y ∉ s := by
        intro hys
        exact hyn (by simp [hys])
      exact hst.2 hxs hyt hys

/-- Points that fail to preserve strong acceptance, subject to lying above
the current finite stem. -/
def BadExtensions (𝓕 : Set (Finset ℕ)) (s : Finset ℕ) (M : Set ℕ) : Set ℕ :=
  {n | n ∈ M ∧ (∀ x ∈ s, x < n) ∧ ¬ StronglyAccepts 𝓕 (insert n s) M}

/-- Todorčević's extension lemma (the form needed here): only finitely many
points above a strongly accepted stem fail to preserve strong acceptance. -/
theorem badExtensions_finite {𝓕 : Set (Finset ℕ)} {s : Finset ℕ} {M : Set ℕ}
    (hsM : (↑s : Set ℕ) ⊆ M)
    (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 s M) :
    (BadExtensions 𝓕 s M).Finite := by
  by_contra hfin
  have hCinf : (BadExtensions 𝓕 s M).Infinite := hfin
  have hCM : BadExtensions 𝓕 s M ⊆ M := fun n hn => hn.1
  have hCreject : ∀ ⦃n⦄, n ∈ BadExtensions 𝓕 s M →
      Rejects 𝓕 (insert n s) M := by
    intro n hn
    have hins : (↑(insert n s) : Set ℕ) ⊆ M := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hn.1
      · exact hsM hx
    rcases hdec (insert n s) hins with hre | hac
    · exact hre
    · exact (hn.2.2 hac).elim
  have hacceptC : ∃ t, ComparableMember 𝓕 s (BadExtensions 𝓕 s M) t :=
    (hacc.mono hCM).accepts hCinf
  rcases hacceptC with ⟨t, htF, hts | ⟨hst, hdiff⟩⟩
  · rcases hCinf.nonempty with ⟨n, hn⟩
    apply hCreject hn
    refine ⟨t, htF, Or.inl (hts.trans (initSeg_insert s hn.2.1))⟩
  · by_cases hne : (t \ s).Nonempty
    · let n := (t \ s).min' hne
      have hnmem : n ∈ t \ s := Finset.min'_mem (t \ s) hne
      have hnC : n ∈ BadExtensions 𝓕 s M := hdiff hnmem
      apply hCreject hnC
      refine ⟨t, htF, Or.inr ⟨hst.insert_min_sdiff hne, ?_⟩⟩
      intro y hy
      have hyt : y ∈ t := (Finset.mem_sdiff.mp hy).1
      have hyns : y ∉ s := by
        intro hys
        exact (Finset.mem_sdiff.mp hy).2 (by simp [hys])
      exact hCM (hdiff (Finset.mem_sdiff.mpr ⟨hyt, hyns⟩))
    · have htsub : t ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp
        (Finset.not_nonempty_iff_eq_empty.mp hne)
      have hteq : t = s := Finset.Subset.antisymm htsub hst.1
      rcases hCinf.nonempty with ⟨n, hn⟩
      apply hCreject hn
      refine ⟨t, htF, Or.inl ?_⟩
      rw [hteq]
      exact initSeg_insert s hn.2.1

structure AcceptState (𝓕 : Set (Finset ℕ)) (M : Set ℕ) where
  marks : Finset ℕ
  marks_subset : (↑marks : Set ℕ) ⊆ M
  allStrong : ∀ s, s ⊆ marks → StronglyAccepts 𝓕 s M

structure AcceptExtension {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (st : AcceptState 𝓕 M) where
  pick : ℕ
  next : AcceptState 𝓕 M
  pick_mem : pick ∈ M
  marks_eq : next.marks = insert pick st.marks
  above : ∀ x ∈ st.marks, x < pick

theorem acceptExtension_nonempty {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (st : AcceptState 𝓕 M) :
    Nonempty (AcceptExtension st) := by
  let Bad : Set ℕ := ⋃ s ∈ (↑st.marks.powerset : Set (Finset ℕ)), BadExtensions 𝓕 s M
  have hBadfin : Bad.Finite := by
    dsimp [Bad]
    apply Set.Finite.biUnion (Finset.finite_toSet st.marks.powerset)
    intro s hs
    have hss : s ⊆ st.marks := Finset.mem_powerset.mp hs
    exact badExtensions_finite (by
      intro x hx
      exact st.marks_subset (hss hx)) hdec (st.allStrong s hss)
  have hGoodinf : (M \ Bad).Infinite := hM.sdiff hBadfin
  rcases hGoodinf.exists_gt (st.marks.sup id) with ⟨n, hnGood, hnbound⟩
  have hnM : n ∈ M := hnGood.1
  have hnabove : ∀ x ∈ st.marks, x < n := by
    intro x hx
    exact (Finset.le_sup (f := id) hx).trans_lt hnbound
  have hnewStrong : ∀ s, s ⊆ st.marks → StronglyAccepts 𝓕 (insert n s) M := by
    intro s hss
    by_contra hnot
    apply hnGood.2
    dsimp [Bad]
    apply Set.mem_iUnion₂.mpr
    exact ⟨s, Finset.mem_powerset.mpr hss, ⟨hnM,
      fun x hxs => hnabove x (hss hxs), hnot⟩⟩
  let st' : AcceptState 𝓕 M := {
    marks := insert n st.marks
    marks_subset := by
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hnM
      · exact st.marks_subset hx
    allStrong := by
      intro t ht
      by_cases hnt : n ∈ t
      · have herase : t.erase n ⊆ st.marks := by
          intro x hx
          have hxn : x ≠ n := (Finset.mem_erase.mp hx).1
          have hxt : x ∈ t := Finset.mem_of_mem_erase hx
          have hxins := ht hxt
          simp only [Finset.mem_insert] at hxins
          rcases hxins with rfl | hxins
          · exact (hxn rfl).elim
          · exact hxins
        simpa [Finset.insert_erase hnt] using hnewStrong (t.erase n) herase
      · apply st.allStrong t
        intro x hxt
        have hxins := ht hxt
        simp only [Finset.mem_insert] at hxins
        rcases hxins with rfl | hxins
        · exact (hnt hxt).elim
        · exact hxins }
  exact ⟨{
    pick := n
    next := st'
    pick_mem := hnM
    marks_eq := rfl
    above := hnabove }⟩

noncomputable def AcceptState.extend {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (st : AcceptState 𝓕 M) :
    AcceptExtension st :=
  Classical.choice (acceptExtension_nonempty hM hdec st)

noncomputable def acceptInitial {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hacc : StronglyAccepts 𝓕 ∅ M) : AcceptState 𝓕 M := {
  marks := ∅
  marks_subset := by simp
  allStrong := by
    intro s hs
    have hsempty : s = ∅ := Finset.Subset.antisymm hs (by simp)
    simpa [hsempty] using hacc }

noncomputable def acceptSeq {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M) :
    ℕ → AcceptState 𝓕 M
  | 0 => acceptInitial hacc
  | n + 1 => ((acceptSeq hM hdec hacc n).extend hM hdec).next

noncomputable def acceptPick {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    (n : ℕ) : ℕ :=
  ((acceptSeq hM hdec hacc n).extend hM hdec).pick

theorem acceptSeq_succ {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    (n : ℕ) :
    acceptSeq hM hdec hacc (n + 1) = ((acceptSeq hM hdec hacc n).extend hM hdec).next :=
  rfl

theorem accept_marks_succ {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    (n : ℕ) :
    (acceptSeq hM hdec hacc (n + 1)).marks =
      insert (acceptPick hM hdec hacc n) (acceptSeq hM hdec hacc n).marks := by
  rw [acceptSeq_succ]
  exact ((acceptSeq hM hdec hacc n).extend hM hdec).marks_eq

theorem acceptPick_mem {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    (n : ℕ) : acceptPick hM hdec hacc n ∈ M :=
  ((acceptSeq hM hdec hacc n).extend hM hdec).pick_mem

theorem acceptPick_above_marks {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    (n : ℕ) : ∀ x ∈ (acceptSeq hM hdec hacc n).marks, x < acceptPick hM hdec hacc n :=
  ((acceptSeq hM hdec hacc n).extend hM hdec).above

theorem accept_marks_mono {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    {i j : ℕ} (hij : i ≤ j) :
    (acceptSeq hM hdec hacc i).marks ⊆ (acceptSeq hM hdec hacc j).marks := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact Finset.Subset.rfl
      · have hij' : i ≤ j := by omega
        refine (ih hij').trans ?_
        rw [accept_marks_succ]
        exact Finset.subset_insert _ _

theorem acceptPick_strictMono {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M) :
    StrictMono (acceptPick hM hdec hacc) := by
  intro i j hij
  have hmark : acceptPick hM hdec hacc i ∈ (acceptSeq hM hdec hacc j).marks := by
    apply accept_marks_mono hM hdec hacc (show i + 1 ≤ j by omega)
    rw [accept_marks_succ]
    simp
  exact acceptPick_above_marks hM hdec hacc j _ hmark

def acceptSet {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M) : Set ℕ :=
  Set.range (acceptPick hM hdec hacc)

theorem acceptSet_infinite {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M) :
    (acceptSet hM hdec hacc).Infinite :=
  Set.infinite_range_of_injective (acceptPick_strictMono hM hdec hacc).injective

theorem acceptSet_subset {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M) :
    acceptSet hM hdec hacc ⊆ M := by
  rintro x ⟨n, rfl⟩
  exact acceptPick_mem hM hdec hacc n

theorem acceptSet_allStrong {𝓕 : Set (Finset ℕ)} {M : Set ℕ}
    (hM : M.Infinite) (hdec : DecidesSubsets 𝓕 M) (hacc : StronglyAccepts 𝓕 ∅ M)
    (s : Finset ℕ) (hs : (↑s : Set ℕ) ⊆ acceptSet hM hdec hacc) :
    StronglyAccepts 𝓕 s (acceptSet hM hdec hacc) := by
  by_cases hs0 : s = ∅
  · subst s
    exact hacc.mono (acceptSet_subset hM hdec hacc)
  · let f : ℕ → ℕ := acceptPick hM hdec hacc
    let g : ℕ → ℕ := Function.invFun f
    let I : Finset ℕ := s.image g
    have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    have hIne : I.Nonempty := hsne.image g
    let k : ℕ := I.max' hIne
    have hfg : ∀ {x}, x ∈ s → f (g x) = x := by
      intro x hxs
      exact Function.invFun_eq (hs hxs)
    have hsmarks : s ⊆ (acceptSeq hM hdec hacc (k + 1)).marks := by
      intro y hys
      have hgyI : g y ∈ I := Finset.mem_image.mpr ⟨y, hys, rfl⟩
      have hgyle : g y ≤ k := Finset.le_max' I (g y) hgyI
      have hmem : acceptPick hM hdec hacc (g y) ∈
          (acceptSeq hM hdec hacc (g y + 1)).marks := by
        rw [accept_marks_succ]
        simp
      have hmem' := accept_marks_mono hM hdec hacc (Nat.succ_le_succ hgyle) hmem
      change f (g y) ∈ (acceptSeq hM hdec hacc (k + 1)).marks at hmem'
      rw [hfg hys] at hmem'
      exact hmem'
    exact ((acceptSeq hM hdec hacc (k + 1)).allStrong s hsmarks).mono
      (acceptSet_subset hM hdec hacc)

/-- Nash--Williams' two-colour theorem for thin families of finite subsets
of `ℕ`. -/
theorem nashWilliams_two (𝓕 : Set (Finset ℕ)) (hthin : FinThin 𝓕)
    (color : Finset ℕ → Bool) {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ ∃ b : Bool,
      ∀ s, s ∈ 𝓕 → (↑s : Set ℕ) ⊆ N → color s = b := by
  let 𝓕₀ : Set (Finset ℕ) := {s | s ∈ 𝓕 ∧ color s = false}
  let D : Set ℕ := fusionSet 𝓕₀ hM
  have hDinf : D.Infinite := fusionSet_infinite 𝓕₀ hM
  have hDM : D ⊆ M := fusionSet_subset 𝓕₀ hM
  have hDdec : DecidesSubsets 𝓕₀ D := fusionSet_decidesSubsets 𝓕₀ hM
  have hempty : Decides 𝓕₀ ∅ D := hDdec ∅ (by simp)
  rcases hempty with hre | hac
  · refine ⟨D, hDM, hDinf, true, ?_⟩
    intro s hsF hsD
    cases hc : color s with
    | true => rfl
    | false =>
        exfalso
        apply hre
        refine ⟨s, ⟨hsF, hc⟩, Or.inr ⟨?_, ?_⟩⟩
        · exact ⟨by simp, by simp⟩
        · simpa using hsD
  · let P : Set ℕ := acceptSet hDinf hDdec hac
    have hPinf : P.Infinite := acceptSet_infinite hDinf hDdec hac
    have hPD : P ⊆ D := acceptSet_subset hDinf hDdec hac
    refine ⟨P, hPD.trans hDM, hPinf, false, ?_⟩
    intro s hsF hsP
    have hsacc : StronglyAccepts 𝓕₀ s P := acceptSet_allStrong hDinf hDdec hac s hsP
    rcases hsacc.accepts hPinf with ⟨t, ht0, hts | ⟨hst, hdiff⟩⟩
    · have htsEq : t = s := hthin ht0.1 hsF hts
      simpa [htsEq] using ht0.2
    · have hstEq : s = t := hthin hsF ht0.1 hst
      simpa [hstEq] using ht0.2

end NashWilliams

theorem sort_toFinset_eq_self_of_pairwise {l : List ℕ} (hl : l.Pairwise (· < ·)) :
    l.toFinset.sort (· ≤ ·) = l :=
  (List.toFinset_sort (r := (· ≤ ·)) hl.nodup).mpr
    (hl.imp fun h => Nat.le_of_lt h)

/-- On strictly increasing lists, list-prefix and finite-set initial-segment
are the same relation. -/
theorem pairwise_isPrefix_iff_initSeg {l m : List ℕ}
    (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·)) :
    l <+: m ↔ NashWilliams.InitSeg l.toFinset m.toFinset := by
  constructor
  · rintro ⟨r, rfl⟩
    have happ := List.pairwise_append.mp hm
    refine ⟨by simp, ?_⟩
    intro x hxl y hym hynl
    have hym' : y ∈ l ∨ y ∈ r := by simpa using hym
    rcases hym' with hyl | hyr
    · exact (hynl (by simpa using hyl)).elim
    · exact happ.2.2 x (by simpa using hxl) y hyr
  · intro hinit
    let r := (m.toFinset \ l.toFinset).sort (· ≤ ·)
    have hcross : ∀ x ∈ l.toFinset.sort (· ≤ ·), ∀ y ∈ r, x < y := by
      intro x hx y hy
      have hxl : x ∈ l.toFinset := by simpa using hx
      have hyr : y ∈ m.toFinset \ l.toFinset := by simpa [r] using hy
      exact hinit.2 hxl (Finset.mem_sdiff.mp hyr).1 (Finset.mem_sdiff.mp hyr).2
    have happ : (l.toFinset.sort (· ≤ ·) ++ r).Pairwise (· < ·) :=
      List.pairwise_append.mpr
        ⟨(Finset.sortedLT_sort _).pairwise, (Finset.sortedLT_sort _).pairwise, hcross⟩
    have hsort := (List.toFinset_sort (r := (· ≤ ·)) happ.nodup).mpr
      (happ.imp fun h => Nat.le_of_lt h)
    have hsort' :
        m.toFinset.sort (· ≤ ·) = l.toFinset.sort (· ≤ ·) ++ r := by
      simpa [r, Finset.union_sdiff_of_subset hinit.1] using hsort
    rw [sort_toFinset_eq_self_of_pairwise hl, sort_toFinset_eq_self_of_pairwise hm] at hsort'
    exact ⟨r, hsort'.symm⟩

theorem IsFormScheme.pairwise {l : ℕ} {z : List ℕ} (h : IsFormScheme l z) :
    z.Pairwise (· < ·) := by
  rcases h with ⟨k, x, y, hk, hl, hbody⟩ | ⟨k, x, y, hk, hl, hbody⟩ <;>
    rcases hbody with hbody | hbody <;> exact hbody.scheme_inc

theorem pairScheme_pairwise {l : ℕ} {x y : IncList} (hl : 0 < l)
    (hform : HasForm l x y) : (pairScheme l x y).Pairwise (· < ·) :=
  (pairScheme_isFormScheme hl hform).pairwise

def PairSchemeFamily (l : ℕ) : Set (Finset ℕ) :=
  {s | ∃ x y : IncList, HasForm l x y ∧ (pairScheme l x y).toFinset = s}

theorem pairSchemeFamily_thin {l : ℕ} (hl : 0 < l) :
    NashWilliams.FinThin (PairSchemeFamily l) := by
  intro s hs t ht hst
  rcases hs with ⟨x, y, hxy, rfl⟩
  rcases ht with ⟨x', y', hxy', rfl⟩
  have hp : pairScheme l x y <+: pairScheme l x' y' :=
    (pairwise_isPrefix_iff_initSeg (pairScheme_pairwise hl hxy)
      (pairScheme_pairwise hl hxy')).mpr hst
  have heq : pairScheme l x y = pairScheme l x' y' :=
    isFormScheme_thin l (pairScheme_isFormScheme hl hxy)
      (pairScheme_isFormScheme hl hxy') hp
  exact congrArg List.toFinset heq

structure PairSchemeWitness (l : ℕ) (s : Finset ℕ) where
  left : IncList
  right : IncList
  form : HasForm l left right
  scheme : (pairScheme l left right).toFinset = s

theorem pairSchemeFamily_iff_nonempty {l : ℕ} {s : Finset ℕ} :
    s ∈ PairSchemeFamily l ↔ Nonempty (PairSchemeWitness l s) := by
  constructor
  · rintro ⟨x, y, hform, hscheme⟩
    exact ⟨⟨x, y, hform, hscheme⟩⟩
  · rintro ⟨w⟩
    exact ⟨w.left, w.right, w.form, w.scheme⟩

noncomputable def schemeColor (color : IncList → IncList → Bool) (l : ℕ)
    (s : Finset ℕ) : Bool := by
  classical
  exact if h : Nonempty (PairSchemeWitness l s) then
      let w := Classical.choice h
      color w.left w.right
    else false

theorem schemeColor_eq (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {l : ℕ} (hl : 0 < l)
    {x y : IncList} (hform : HasForm l x y) :
    schemeColor color l (pairScheme l x y).toFinset = color x y := by
  let w0 : PairSchemeWitness l (pairScheme l x y).toFinset :=
    ⟨x, y, hform, rfl⟩
  have hnonempty : Nonempty (PairSchemeWitness l (pairScheme l x y).toFinset) := ⟨w0⟩
  rw [schemeColor, dif_pos hnonempty]
  let w := Classical.choice hnonempty
  have hlist : pairScheme l x y = pairScheme l w.left w.right := by
    calc
      pairScheme l x y = (pairScheme l x y).toFinset.sort (· ≤ ·) :=
        (sort_toFinset_eq_self_of_pairwise (pairScheme_pairwise hl hform)).symm
      _ = (pairScheme l w.left w.right).toFinset.sort (· ≤ ·) := by rw [w.scheme]
      _ = pairScheme l w.left w.right :=
        sort_toFinset_eq_self_of_pairwise (pairScheme_pairwise hl w.form)
  change color w.left w.right = color x y
  rcases pairScheme_injective_unordered hl hform w.form hlist with h | h
  · exact (congrArg₂ color h.1 h.2).symm
  · exact (hcomm w.left w.right).trans (congrArg₂ color h.1 h.2).symm

/-- One fixed positive Larson form can be canonized on an infinite set of
scheme coordinates. -/
theorem canonize_one_form (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {l : ℕ} (hl : 0 < l)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ ∃ b : Bool,
      ∀ x y, HasForm l x y →
        (↑(pairScheme l x y).toFinset : Set ℕ) ⊆ N → color x y = b := by
  rcases NashWilliams.nashWilliams_two (PairSchemeFamily l)
      (pairSchemeFamily_thin hl) (schemeColor color l) hM with
    ⟨N, hNM, hNinf, b, hb⟩
  refine ⟨N, hNM, hNinf, b, ?_⟩
  intro x y hform hsupport
  have hfamily : (pairScheme l x y).toFinset ∈ PairSchemeFamily l :=
    ⟨x, y, hform, rfl⟩
  rw [← schemeColor_eq color hcomm hl hform]
  exact hb _ hfamily hsupport

structure CanonState (M : Set ℕ) where
  tail : Set ℕ
  tail_infinite : tail.Infinite
  tail_subset : tail ⊆ M

structure CanonExtension (color : IncList → IncList → Bool) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) where
  marker : ℕ
  next : CanonState M
  formColor : Bool
  marker_mem : marker ∈ st.tail
  next_subset : next.tail ⊆ st.tail
  marker_below : ∀ ⦃y⦄, y ∈ next.tail → marker < y
  homogeneous : ∀ x y, HasForm (n + 1) x y →
    (↑(pairScheme (n + 1) x y).toFinset : Set ℕ) ⊆ next.tail →
      color x y = formColor

theorem canonExtension_nonempty (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) : Nonempty (CanonExtension color n st) := by
  let a := sInf st.tail
  have ha : a ∈ st.tail := Nat.sInf_mem st.tail_infinite.nonempty
  let B : Set ℕ := st.tail \ Set.Iic a
  have hBinf : B.Infinite := st.tail_infinite.sdiff (Set.finite_Iic a)
  rcases canonize_one_form color hcomm (show 0 < n + 1 by omega) hBinf with
    ⟨N, hNB, hNinf, b, hb⟩
  have hNtail : N ⊆ st.tail := hNB.trans Set.sdiff_subset
  have haN : ∀ ⦃y⦄, y ∈ N → a < y := by
    intro y hy
    exact Nat.lt_of_not_ge (hNB hy).2
  let st' : CanonState M := {
    tail := N
    tail_infinite := hNinf
    tail_subset := hNtail.trans st.tail_subset }
  exact ⟨{
    marker := a
    next := st'
    formColor := b
    marker_mem := ha
    next_subset := hNtail
    marker_below := haN
    homogeneous := hb }⟩

noncomputable def CanonState.extend (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) : CanonExtension color n st :=
  Classical.choice (canonExtension_nonempty color hcomm n st)

noncomputable def canonInitial {M : Set ℕ} (hM : M.Infinite) : CanonState M := {
  tail := M
  tail_infinite := hM
  tail_subset := Set.Subset.rfl }

noncomputable def canonSeq (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    ℕ → CanonState M
  | 0 => canonInitial hM
  | n + 1 => ((canonSeq color hcomm hM n).extend color hcomm n).next

noncomputable def canonMarker (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ℕ :=
  ((canonSeq color hcomm hM n).extend color hcomm n).marker

noncomputable def canonFormColor (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (l : ℕ) : Bool :=
  if _hl : 0 < l then
    ((canonSeq color hcomm hM (l - 1)).extend color hcomm (l - 1)).formColor
  else false

theorem canonSeq_succ (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) :
    canonSeq color hcomm hM (n + 1) =
      ((canonSeq color hcomm hM n).extend color hcomm n).next := rfl

theorem canonMarker_mem_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : canonMarker color hcomm hM n ∈ (canonSeq color hcomm hM n).tail :=
  ((canonSeq color hcomm hM n).extend color hcomm n).marker_mem

theorem canon_tail_succ_subset (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) :
    (canonSeq color hcomm hM (n + 1)).tail ⊆ (canonSeq color hcomm hM n).tail := by
  rw [canonSeq_succ]
  exact ((canonSeq color hcomm hM n).extend color hcomm n).next_subset

theorem canonMarker_below_next_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ∀ ⦃y⦄, y ∈ (canonSeq color hcomm hM (n + 1)).tail →
      canonMarker color hcomm hM n < y := by
  rw [canonSeq_succ]
  exact ((canonSeq color hcomm hM n).extend color hcomm n).marker_below

theorem canon_tail_antitone (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    (canonSeq color hcomm hM j).tail ⊆ (canonSeq color hcomm hM i).tail := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Set.Subset.rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact Set.Subset.rfl
      · have hij' : i ≤ j := by omega
        exact (canon_tail_succ_subset color hcomm hM j).trans (ih hij')

theorem canonMarker_mem_earlier_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    canonMarker color hcomm hM j ∈ (canonSeq color hcomm hM i).tail :=
  canon_tail_antitone color hcomm hM hij (canonMarker_mem_tail color hcomm hM j)

theorem canonMarker_strictMono (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    StrictMono (canonMarker color hcomm hM) := by
  intro i j hij
  apply canonMarker_below_next_tail color hcomm hM i
  exact canonMarker_mem_earlier_tail color hcomm hM (show i + 1 ≤ j by omega)

def canonSet (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) : Set ℕ :=
  Set.range (canonMarker color hcomm hM)

theorem canonSet_infinite (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    (canonSet color hcomm hM).Infinite :=
  Set.infinite_range_of_injective (canonMarker_strictMono color hcomm hM).injective

theorem canonSet_subset (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    canonSet color hcomm hM ⊆ M := by
  rintro x ⟨n, rfl⟩
  exact (canonSeq color hcomm hM n).tail_subset
    (canonMarker_mem_tail color hcomm hM n)

theorem canonized_of_marker_bound (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {l : ℕ} (hl : 0 < l) {x y : IncList} (hform : HasForm l x y)
    (hsupport : (↑(pairScheme l x y).toFinset : Set ℕ) ⊆ canonSet color hcomm hM)
    (hbound : ∀ z ∈ (pairScheme l x y).toFinset,
      canonMarker color hcomm hM (l - 1) < z) :
    color x y = canonFormColor color hcomm hM l := by
  let n := l - 1
  have hn : n + 1 = l := by dsimp [n]; omega
  have htail : (↑(pairScheme l x y).toFinset : Set ℕ) ⊆
      (canonSeq color hcomm hM (n + 1)).tail := by
    intro z hz
    rcases hsupport hz with ⟨j, hj⟩
    have hlt : canonMarker color hcomm hM n < canonMarker color hcomm hM j := by
      simpa [n, hj] using hbound z hz
    have hnj : n < j := (canonMarker_strictMono color hcomm hM).lt_iff_lt.mp hlt
    rw [← hj]
    exact canonMarker_mem_earlier_tail color hcomm hM (show n + 1 ≤ j by omega)
  have htailN : (↑(pairScheme (n + 1) x y).toFinset : Set ℕ) ⊆
      (canonSeq color hcomm hM (n + 1)).tail := by
    simpa only [hn] using htail
  have hhom := ((canonSeq color hcomm hM n).extend color hcomm n).homogeneous
    x y (hn ▸ hform) (by
      rw [← canonSeq_succ color hcomm hM n]
      exact htailN)
  simpa [canonFormColor, hl, n] using hhom

theorem simultaneous_canonization (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ ∃ formColor : ℕ → Bool,
      ∀ l, 0 < l → ∀ x y, HasForm l x y →
        (↑(pairScheme l x y).toFinset : Set ℕ) ⊆ N →
        (∀ z ∈ (pairScheme l x y).toFinset,
          canonMarker color hcomm hM (l - 1) < z) →
        color x y = formColor l := by
  exact ⟨canonSet color hcomm hM, canonSet_subset color hcomm hM,
    canonSet_infinite color hcomm hM, canonFormColor color hcomm hM,
    fun l hl x y hform hs hb => canonized_of_marker_bound color hcomm hM hl hform hs hb⟩


/-! ## Realizing one positive form by a triangle

The next elementary list primitives are used to give a direct, three-vertex
specialization of Larson's realization lemma.  Enumerating an infinite set
lets us reserve consecutive finite intervals of indices; `enumSlice` is the
corresponding increasing list of actual members of the set. -/

noncomputable def enumOf (N : Set ℕ) : ℕ → ℕ :=
  Nat.nth (fun n ↦ n ∈ N)

theorem enumOf_mem {N : Set ℕ} (hN : N.Infinite) (i : ℕ) : enumOf N i ∈ N := by
  exact Nat.nth_mem_of_infinite hN i

theorem enumOf_strictMono {N : Set ℕ} (hN : N.Infinite) : StrictMono (enumOf N) := by
  exact Nat.nth_strictMono hN

def enumSlice (f : ℕ → ℕ) (start len : ℕ) : List ℕ :=
  (List.range len).map (fun i ↦ f (start + i))

@[simp] theorem length_enumSlice (f : ℕ → ℕ) (start len : ℕ) :
    (enumSlice f start len).length = len := by
  simp [enumSlice]

theorem mem_enumSlice {f : ℕ → ℕ} {start len x : ℕ} :
    x ∈ enumSlice f start len ↔ ∃ i < len, x = f (start + i) := by
  constructor
  · simp only [enumSlice, List.mem_map, List.mem_range]
    rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    simp only [enumSlice, List.mem_map, List.mem_range]
    exact ⟨i, hi, rfl⟩

theorem enumSlice_pairwise (f : ℕ → ℕ) (hf : StrictMono f) (start len : ℕ) :
    (enumSlice f start len).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [enumSlice, List.length_map, List.length_range] at hi hj
  simp only [enumSlice, List.getElem_map, List.getElem_range]
  exact hf (by omega)

theorem enumSlice_subset {N : Set ℕ} (hN : N.Infinite) (start len : ℕ) :
    ↑(enumSlice (enumOf N) start len).toFinset ⊆ N := by
  intro x hx
  have hx' : x ∈ enumSlice (enumOf N) start len := by
    simpa only [Finset.mem_coe, List.mem_toFinset] using hx
  rcases mem_enumSlice.mp hx' with ⟨i, hi, rfl⟩
  exact enumOf_mem hN _

theorem enumSlice_ne_nil (f : ℕ → ℕ) (start len : ℕ) (hlen : 0 < len) :
    enumSlice f start len ≠ [] := by
  intro h
  have hz : len = 0 := by
    simpa using congrArg List.length h
  omega

theorem enumSlice_lt_enumSlice (f : ℕ → ℕ) (hf : StrictMono f)
    {s m t n : ℕ} (hsep : s + m ≤ t) :
    ∀ x ∈ enumSlice f s m, ∀ y ∈ enumSlice f t n, x < y := by
  intro x hx y hy
  rcases mem_enumSlice.mp hx with ⟨i, hi, rfl⟩
  rcases mem_enumSlice.mp hy with ⟨j, hj, rfl⟩
  apply hf
  omega

theorem pairwise_append_of_lt {a b : List ℕ}
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·))
    (hab : ∀ x ∈ a, ∀ y ∈ b, x < y) :
    (a ++ b).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  exact ⟨ha, hb, hab⟩

def blockStart (base : ℕ) (size : ℕ → ℕ) : ℕ → ℕ
  | 0 => base
  | n + 1 => blockStart base size n + size n

@[simp] theorem blockStart_zero (base : ℕ) (size : ℕ → ℕ) :
    blockStart base size 0 = base := rfl

@[simp] theorem blockStart_succ (base : ℕ) (size : ℕ → ℕ) (n : ℕ) :
    blockStart base size (n + 1) = blockStart base size n + size n := rfl

theorem blockStart_mono (base : ℕ) (size : ℕ → ℕ) :
    Monotone (blockStart base size) := by
  apply monotone_nat_of_le_succ
  intro n
  simp

theorem blockStart_end_le {base : ℕ} {size : ℕ → ℕ} {i j : ℕ}
    (hij : i < j) : blockStart base size i + size i ≤ blockStart base size j := by
  rw [← blockStart_succ]
  exact blockStart_mono base size (by omega)

noncomputable def allocatedBlock (N : Set ℕ) (base : ℕ) (size : ℕ → ℕ)
    (i : ℕ) : List ℕ :=
  enumSlice (enumOf N) (blockStart base size i) (size i)

@[simp] theorem length_allocatedBlock (N : Set ℕ) (base : ℕ) (size : ℕ → ℕ)
    (i : ℕ) : (allocatedBlock N base size i).length = size i := by
  simp [allocatedBlock]

theorem allocatedBlock_pairwise {N : Set ℕ} (hN : N.Infinite) (base : ℕ)
    (size : ℕ → ℕ) (i : ℕ) :
    (allocatedBlock N base size i).Pairwise (· < ·) := by
  exact enumSlice_pairwise _ (enumOf_strictMono hN) _ _

theorem allocatedBlock_subset {N : Set ℕ} (hN : N.Infinite) (base : ℕ)
    (size : ℕ → ℕ) (i : ℕ) :
    ↑(allocatedBlock N base size i).toFinset ⊆ N := by
  exact enumSlice_subset hN _ _

theorem allocatedBlock_lt {N : Set ℕ} (hN : N.Infinite) (base : ℕ)
    (size : ℕ → ℕ) {i j : ℕ} (hij : i < j) :
    ∀ x ∈ allocatedBlock N base size i,
      ∀ y ∈ allocatedBlock N base size j, x < y := by
  exact enumSlice_lt_enumSlice _ (enumOf_strictMono hN) (blockStart_end_le hij)

theorem allocatedBlock_ne_nil (N : Set ℕ) (base : ℕ) (size : ℕ → ℕ)
    (i : ℕ) (hi : 0 < size i) : allocatedBlock N base size i ≠ [] := by
  exact enumSlice_ne_nil _ _ _ hi

def endpointStart (f : ℕ → ℕ) (ka : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => endpointStart f ka i + ka + f (endpointStart f ka i)

@[simp] theorem endpointStart_zero (f : ℕ → ℕ) (ka : ℕ) :
    endpointStart f ka 0 = 0 := rfl

@[simp] theorem endpointStart_succ (f : ℕ → ℕ) (ka i : ℕ) :
    endpointStart f ka (i + 1) =
      endpointStart f ka i + ka + f (endpointStart f ka i) := rfl

theorem endpointStart_mono (f : ℕ → ℕ) (ka : ℕ) :
    Monotone (endpointStart f ka) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [endpointStart_succ]
  omega

noncomputable def endpoint (N : Set ℕ) (ka i j : ℕ) : ℕ :=
  enumOf N (endpointStart (enumOf N) ka i + j)

@[simp] theorem endpoint_eq (N : Set ℕ) (ka i j : ℕ) :
    endpoint N ka i j = enumOf N (endpointStart (enumOf N) ka i + j) := by
  rfl

noncomputable def endpointList (N : Set ℕ) (ka i : ℕ) : List ℕ :=
  enumSlice (enumOf N) (endpointStart (enumOf N) ka i) ka

noncomputable def firstBlock (N : Set ℕ) (ka i : ℕ) : List ℕ :=
  enumSlice (enumOf N) (endpointStart (enumOf N) ka i + ka) (endpoint N ka i 0)

@[simp] theorem length_endpointList (N : Set ℕ) (ka i : ℕ) :
    (endpointList N ka i).length = ka := by
  simp [endpointList]

@[simp] theorem length_firstBlock (N : Set ℕ) (ka i : ℕ) :
    (firstBlock N ka i).length = endpoint N ka i 0 := by
  simp [firstBlock]

def scheduledVertex (ka k p : ℕ) : ℕ :=
  if ka = k + 1 ∧ p / 3 = k - 1 then 2 - p % 3 else p % 3

def scheduledLevel (p : ℕ) : ℕ := p / 3 + 1

noncomputable def restSize (N : Set ℕ) (ka k p : ℕ) : ℕ :=
  endpoint N ka (scheduledVertex ka k p) (scheduledLevel p) -
    endpoint N ka (scheduledVertex ka k p) (scheduledLevel p - 1)

def restPos (ka k j i : ℕ) : ℕ :=
  3 * (j - 1) + if ka = k + 1 ∧ j = k then 2 - i else i

theorem scheduledLevel_restPos {ka k j i : ℕ} (hj : 0 < j) (hi : i < 3) :
    scheduledLevel (restPos ka k j i) = j := by
  simp only [scheduledLevel, restPos]
  split_ifs <;> omega

theorem scheduledVertex_restPos {ka k j i : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hi : i < 3) :
    scheduledVertex ka k (restPos ka k j i) = i := by
  let q := if ka = k + 1 ∧ j = k then 2 - i else i
  have hq : q < 3 := by
    dsimp [q]
    split_ifs <;> omega
  have hdiv : (3 * (j - 1) + q) / 3 = j - 1 := by omega
  have hmod : (3 * (j - 1) + q) % 3 = q := by omega
  change (if ka = k + 1 ∧ (3 * (j - 1) + q) / 3 = k - 1 then
      2 - (3 * (j - 1) + q) % 3 else (3 * (j - 1) + q) % 3) = i
  rw [hdiv, hmod]
  by_cases hfinal : ka = k + 1 ∧ j = k
  · have hs : ka = k + 1 ∧ j - 1 = k - 1 := by
      exact ⟨hfinal.1, by omega⟩
    simp [hs, q, hfinal]
    omega
  · have hs : ¬ (ka = k + 1 ∧ j - 1 = k - 1) := by
      rintro ⟨hka, hsub⟩
      apply hfinal
      exact ⟨hka, by omega⟩
    simp [hs, q, hfinal]

noncomputable def restBlock (N : Set ℕ) (ka k j i : ℕ) : List ℕ :=
  allocatedBlock N (endpointStart (enumOf N) ka 3) (restSize N ka k)
    (restPos ka k j i)

noncomputable def realizationBlocks (N : Set ℕ) (ka k i : ℕ) : List (List ℕ) :=
  firstBlock N ka i ::
    (List.range (ka - 1)).map (fun r ↦ restBlock N ka k (r + 1) i)

noncomputable def realizationList (N : Set ℕ) (ka k i : ℕ) : List ℕ :=
  (realizationBlocks N ka k i).flatten

@[simp] theorem length_realizationBlocks {N : Set ℕ} {ka k i : ℕ} (hka : 0 < ka) :
    (realizationBlocks N ka k i).length = ka := by
  simp [realizationBlocks]
  omega

@[simp] theorem restSize_restPos {N : Set ℕ} {ka k j i : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hi : i < 3) :
    restSize N ka k (restPos ka k j i) =
      endpoint N ka i j - endpoint N ka i (j - 1) := by
  simp only [restSize, scheduledVertex_restPos hk hj hi,
    scheduledLevel_restPos hj hi]

theorem endpoint_strictMono_right {N : Set ℕ} (hN : N.Infinite) (ka i : ℕ) :
    StrictMono (endpoint N ka i) := by
  intro a b hab
  apply enumOf_strictMono hN
  change endpointStart (enumOf N) ka i + a < endpointStart (enumOf N) ka i + b
  omega

theorem restSize_restPos_pos {N : Set ℕ} (hN : N.Infinite) {ka k j i : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hi : i < 3) :
    0 < restSize N ka k (restPos ka k j i) := by
  rw [restSize_restPos hk hj hi]
  exact Nat.sub_pos_of_lt (endpoint_strictMono_right hN ka i (by omega))

@[simp] theorem length_restBlock {N : Set ℕ} {ka k j i : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hi : i < 3) :
    (restBlock N ka k j i).length =
      endpoint N ka i j - endpoint N ka i (j - 1) := by
  simp [restBlock, restSize_restPos hk hj hi]

theorem restBlock_ne_nil {N : Set ℕ} (hN : N.Infinite) {ka k j i : ℕ}
    (hk : 0 < k) (hj : 0 < j) (hi : i < 3) :
    restBlock N ka k j i ≠ [] := by
  apply allocatedBlock_ne_nil
  exact restSize_restPos_pos hN hk hj hi

theorem restBlock_pairwise {N : Set ℕ} (hN : N.Infinite) (ka k j i : ℕ) :
    (restBlock N ka k j i).Pairwise (· < ·) := by
  exact allocatedBlock_pairwise hN _ _ _

theorem restBlock_subset {N : Set ℕ} (hN : N.Infinite) (ka k j i : ℕ) :
    ↑(restBlock N ka k j i).toFinset ⊆ N := by
  exact allocatedBlock_subset hN _ _ _

theorem restPos_level_lt {ka k j j' i i' : ℕ}
    (hj : 0 < j) (hjj' : j < j') (hi : i < 3) (hi' : i' < 3) :
    restPos ka k j i < restPos ka k j' i' := by
  simp only [restPos]
  split_ifs <;> omega

theorem restPos_same_lt {ka k j i i' : ℕ}
    (hi : i < i') (hi' : i' < 3) (hnot : ¬ (ka = k + 1 ∧ j = k)) :
    restPos ka k j i < restPos ka k j i' := by
  simp [restPos, hnot]
  omega

theorem restPos_final_lt {ka k j i i' : ℕ}
    (hi : i < i') (hi' : i' < 3) (hfinal : ka = k + 1 ∧ j = k) :
    restPos ka k j i' < restPos ka k j i := by
  simp [restPos, hfinal]
  omega

theorem restBlock_lt_of_pos_lt {N : Set ℕ} (hN : N.Infinite)
    {ka k j i j' i' : ℕ} (hpos : restPos ka k j i < restPos ka k j' i') :
    ∀ x ∈ restBlock N ka k j i, ∀ y ∈ restBlock N ka k j' i', x < y := by
  exact allocatedBlock_lt hN _ _ hpos

theorem endpointList_pairwise {N : Set ℕ} (hN : N.Infinite) (ka i : ℕ) :
    (endpointList N ka i).Pairwise (· < ·) := by
  exact enumSlice_pairwise _ (enumOf_strictMono hN) _ _

theorem endpointList_subset {N : Set ℕ} (hN : N.Infinite) (ka i : ℕ) :
    ↑(endpointList N ka i).toFinset ⊆ N := by
  exact enumSlice_subset hN _ _

theorem endpoint_mem_endpointList (N : Set ℕ) {ka i j : ℕ} (hj : j < ka) :
    endpoint N ka i j ∈ endpointList N ka i := by
  exact mem_enumSlice.mpr ⟨j, hj, rfl⟩

theorem firstBlock_pairwise {N : Set ℕ} (hN : N.Infinite) (ka i : ℕ) :
    (firstBlock N ka i).Pairwise (· < ·) := by
  exact enumSlice_pairwise _ (enumOf_strictMono hN) _ _

theorem firstBlock_subset {N : Set ℕ} (hN : N.Infinite) (ka i : ℕ) :
    ↑(firstBlock N ka i).toFinset ⊆ N := by
  exact enumSlice_subset hN _ _

theorem endpointList_lt_firstBlock {N : Set ℕ} (hN : N.Infinite) (ka i : ℕ) :
    ∀ x ∈ endpointList N ka i, ∀ y ∈ firstBlock N ka i, x < y := by
  exact enumSlice_lt_enumSlice _ (enumOf_strictMono hN) (by omega)

theorem firstBlock_lt_endpointList {N : Set ℕ} (hN : N.Infinite)
    {ka i j : ℕ} (hij : i < j) :
    ∀ x ∈ firstBlock N ka i, ∀ y ∈ endpointList N ka j, x < y := by
  apply enumSlice_lt_enumSlice _ (enumOf_strictMono hN)
  change endpointStart (enumOf N) ka i + ka + enumOf N (endpointStart (enumOf N) ka i) ≤
    endpointStart (enumOf N) ka j
  rw [← endpointStart_succ]
  exact endpointStart_mono _ _ (by omega)

theorem firstBlock_lt_restBlock {N : Set ℕ} (hN : N.Infinite)
    {ka k i j i' : ℕ} (hi : i < 3) :
    ∀ x ∈ firstBlock N ka i, ∀ y ∈ restBlock N ka k j i', x < y := by
  apply enumSlice_lt_enumSlice _ (enumOf_strictMono hN)
  calc
    endpointStart (enumOf N) ka i + ka + endpoint N ka i 0 =
        endpointStart (enumOf N) ka (i + 1) := by
          simp only [endpointStart_succ, endpoint]
          congr 2
    _ ≤ endpointStart (enumOf N) ka 3 := endpointStart_mono _ _ (by omega)
    _ ≤ blockStart (endpointStart (enumOf N) ka 3) (restSize N ka k)
        (restPos ka k j i') := blockStart_mono _ _ (Nat.zero_le _)

noncomputable def realizationBlocksPrefix
    (N : Set ℕ) (ka k i n : ℕ) : List (List ℕ) :=
  firstBlock N ka i ::
    (List.range n).map (fun r ↦ restBlock N ka k (r + 1) i)

@[simp] theorem realizationBlocksPrefix_zero (N : Set ℕ) (ka k i : ℕ) :
    realizationBlocksPrefix N ka k i 0 = [firstBlock N ka i] := by
  simp [realizationBlocksPrefix]

theorem realizationBlocksPrefix_succ (N : Set ℕ) (ka k i n : ℕ) :
    realizationBlocksPrefix N ka k i (n + 1) =
      realizationBlocksPrefix N ka k i n ++ [restBlock N ka k (n + 1) i] := by
  simp [realizationBlocksPrefix, List.range_succ, List.map_append]

theorem accLengths_realizationBlocksPrefix {N : Set ℕ} (hN : N.Infinite)
    {ka k i n : ℕ} (hk : 0 < k) (hi : i < 3) (hn : n < ka) :
    accLengths 0 (realizationBlocksPrefix N ka k i n) =
      (List.range (n + 1)).map (endpoint N ka i) := by
  induction n with
  | zero =>
      simp [realizationBlocksPrefix, accLengths]
  | succ n ih =>
      have hn' : n < ka := by omega
      have hih := ih hn'
      have hsum :
          ((realizationBlocksPrefix N ka k i n).map List.length).sum =
            endpoint N ka i n := by
        have hlast := congrArg List.getLast? hih
        have hleft :
            (accLengths 0 (realizationBlocksPrefix N ka k i n)).getLast? =
              some ((realizationBlocksPrefix N ka k i n).map List.length).sum := by
          simpa [realizationBlocksPrefix] using
            (getLast?_accLengths_cons (n := 0) (a := firstBlock N ka i)
              (as := (List.range n).map (fun r ↦ restBlock N ka k (r + 1) i)))
        have hright :
            ((List.range (n + 1)).map (endpoint N ka i)).getLast? =
              some (endpoint N ka i n) := by
          simp [List.getLast?_range]
        rw [hleft, hright] at hlast
        exact Option.some.inj hlast
      rw [realizationBlocksPrefix_succ, accLengths_append, hih]
      simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
        accLengths, List.append_nil, List.range_succ, List.map_append, List.map_singleton]
      rw [hsum, length_restBlock hk (by omega) hi]
      have hle : endpoint N ka i n ≤ endpoint N ka i (n + 1) :=
        (endpoint_strictMono_right hN ka i (by omega)).le
      rw [show n + 1 - 1 = n by omega, Nat.zero_add, Nat.add_sub_of_le hle]

theorem accLengths_realizationBlocks {N : Set ℕ} (hN : N.Infinite)
    {ka k i : ℕ} (hk : 0 < k) (hka : 0 < ka) (hi : i < 3) :
    accLengths 0 (realizationBlocks N ka k i) = endpointList N ka i := by
  have h := accLengths_realizationBlocksPrefix hN hk hi
    (show ka - 1 < ka by omega)
  rw [show realizationBlocks N ka k i = realizationBlocksPrefix N ka k i (ka - 1) by
    rfl, h]
  unfold endpointList enumSlice
  rw [Nat.sub_add_cancel (show 1 ≤ ka by omega)]
  apply List.map_congr_left
  intro j hj
  rfl

theorem realizationBlocks_blocks_pairwise {N : Set ℕ} (hN : N.Infinite)
    {ka k i : ℕ} :
    ∀ b ∈ realizationBlocks N ka k i, b.Pairwise (· < ·) := by
  intro b hb
  simp only [realizationBlocks, List.mem_cons, List.mem_map, List.mem_range] at hb
  rcases hb with rfl | ⟨r, hr, rfl⟩
  · exact firstBlock_pairwise hN _ _
  · exact restBlock_pairwise hN _ _ _ _

theorem realizationBlocks_cross_pairwise {N : Set ℕ} (hN : N.Infinite)
    {ka k i : ℕ} (hi : i < 3) :
    (realizationBlocks N ka k i).Pairwise
      (fun a b ↦ ∀ x ∈ a, ∀ y ∈ b, x < y) := by
  rw [realizationBlocks, List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro b hb
    rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
    exact firstBlock_lt_restBlock hN hi
  · rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.length_map, List.length_range] at ha hb
    simp only [List.getElem_map, List.getElem_range]
    apply restBlock_lt_of_pos_lt hN
    exact restPos_level_lt (by omega) (by omega) hi hi

theorem realizationList_pairwise {N : Set ℕ} (hN : N.Infinite)
    {ka k i : ℕ} (hi : i < 3) :
    (realizationList N ka k i).Pairwise (· < ·) := by
  rw [realizationList, List.pairwise_flatten]
  exact ⟨realizationBlocks_blocks_pairwise hN,
    realizationBlocks_cross_pairwise hN hi⟩

theorem realizationBlocks_ne_nil {N : Set ℕ} (hN : N.Infinite)
    (hposN : ∀ x, x ∈ N → 0 < x)
    {ka k i : ℕ} (hk : 0 < k) (hka : 0 < ka) (hi : i < 3) :
    ∀ b ∈ realizationBlocks N ka k i, b ≠ [] := by
  intro b hb
  simp only [realizationBlocks, List.mem_cons, List.mem_map, List.mem_range] at hb
  rcases hb with rfl | ⟨r, hr, rfl⟩
  · apply enumSlice_ne_nil
    change 0 < endpoint N ka i 0
    apply hposN
    exact enumOf_mem hN _
  · exact restBlock_ne_nil hN hk (by omega) hi

theorem realizationList_subset {N : Set ℕ} (hN : N.Infinite)
    (ka k i : ℕ) : ↑(realizationList N ka k i).toFinset ⊆ N := by
  intro x hx
  have hx' : x ∈ realizationList N ka k i := by
    simpa only [Finset.mem_coe, List.mem_toFinset] using hx
  rcases List.mem_flatten.mp hx' with ⟨b, hb, hxb⟩
  simp only [realizationBlocks, List.mem_cons, List.mem_map, List.mem_range] at hb
  rcases hb with rfl | ⟨r, hr, rfl⟩
  · exact firstBlock_subset hN ka i (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact restBlock_subset hN ka k (r + 1) i
      (by simpa only [Finset.mem_coe, List.mem_toFinset])

noncomputable def restSeq (N : Set ℕ) (ka k j n i : ℕ) : List (List ℕ) :=
  (List.range n).map (fun r ↦ restBlock N ka k (j + r) i)

@[simp] theorem restSeq_zero (N : Set ℕ) (ka k j i : ℕ) :
    restSeq N ka k j 0 i = [] := by simp [restSeq]

theorem restSeq_succ (N : Set ℕ) (ka k j n i : ℕ) :
    restSeq N ka k j (n + 1) i =
      restBlock N ka k j i :: restSeq N ka k (j + 1) n i := by
  simp only [restSeq, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 2
  funext r
  dsimp only [Function.comp_apply]
  rw [show j + r.succ = j + 1 + r by omega]

theorem realizationBlocks_eq_restSeq {N : Set ℕ} {ka k i : ℕ} :
    realizationBlocks N ka k i = firstBlock N ka i :: restSeq N ka k 1 (ka - 1) i := by
  unfold realizationBlocks restSeq
  congr 2
  funext r
  rw [Nat.add_comm r 1]

noncomputable def normalInteractionFrom
    (N : Set ℕ) (ka k j n p q : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | n + 1 => restBlock N ka k j p ++ restBlock N ka k j q ++
      normalInteractionFrom N ka k (j + 1) n p q

@[simp] theorem normalInteractionFrom_zero
    (N : Set ℕ) (ka k j p q : ℕ) :
    normalInteractionFrom N ka k j 0 p q = [] := rfl

@[simp] theorem normalInteractionFrom_succ
    (N : Set ℕ) (ka k j n p q : ℕ) :
    normalInteractionFrom N ka k j (n + 1) p q =
      restBlock N ka k j p ++ restBlock N ka k j q ++
        normalInteractionFrom N ka k (j + 1) n p q := rfl

theorem interact_restSeq (N : Set ℕ) (ka k j n p q : ℕ) :
    interact (restSeq N ka k j n p) (restSeq N ka k j n q) =
      normalInteractionFrom N ka k j n p q := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [restSeq_succ, restSeq_succ]
      simp only [interact, normalInteractionFrom_succ]
      rw [ih]

theorem mem_normalInteractionFrom {N : Set ℕ} {ka k j n p q x : ℕ} :
    x ∈ normalInteractionFrom N ka k j n p q ↔
      ∃ t < n, x ∈ restBlock N ka k (j + t) p ∨
        x ∈ restBlock N ka k (j + t) q := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      simp only [normalInteractionFrom_succ, List.mem_append, ih]
      constructor
      · intro hx
        rcases hx with hx | hx
        · rcases hx with hxp | hxq
          · exact ⟨0, by omega, Or.inl (by simpa using hxp)⟩
          · exact ⟨0, by omega, Or.inr hxq⟩
        · rcases hx with ⟨t, ht, hxpq⟩
          refine ⟨t + 1, by omega, ?_⟩
          have heq : j + (t + 1) = j + 1 + t := by omega
          simpa only [heq] using hxpq
      · rintro ⟨t, ht, hx⟩
        by_cases ht0 : t = 0
        · subst t
          left
          simpa using hx
        · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
          right
          refine ⟨t - 1, by omega, ?_⟩
          have heq : j + 1 + (t - 1) = j + t := by omega
          simpa only [heq] using hx

theorem normalInteractionFrom_pairwise {N : Set ℕ} (hN : N.Infinite)
    {ka k j n p q : ℕ} (hpq : p < q) (hq : q < 3)
    (hj : 0 < j) (hnormal : ∀ t, j ≤ t → t < j + n → ¬ (ka = k + 1 ∧ t = k)) :
    (normalInteractionFrom N ka k j n p q).Pairwise (· < ·) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      have hnot : ¬ (ka = k + 1 ∧ j = k) := hnormal j (by omega) (by omega)
      have hpp := restBlock_pairwise hN ka k j p
      have hqq := restBlock_pairwise hN ka k j q
      have hpqBlocks :
          ∀ x ∈ restBlock N ka k j p, ∀ y ∈ restBlock N ka k j q, x < y :=
        restBlock_lt_of_pos_lt hN (restPos_same_lt hpq hq hnot)
      have htail := ih (j := j + 1) (by omega)
        (fun t h1 h2 ↦ hnormal t (by omega) (by omega))
      have hcurrent :
          (restBlock N ka k j p ++ restBlock N ka k j q).Pairwise (· < ·) :=
        pairwise_append_of_lt hpp hqq hpqBlocks
      apply pairwise_append_of_lt hcurrent htail
      intro x hx y hy
      rcases mem_normalInteractionFrom.mp hy with ⟨t, ht, hyt⟩
      rcases List.mem_append.mp hx with hxp | hxq
      · rcases hyt with hyp | hyq
        · exact restBlock_lt_of_pos_lt hN
            (restPos_level_lt hj (by omega) (by omega) (by omega)) x hxp y hyp
        · exact restBlock_lt_of_pos_lt hN
            (restPos_level_lt hj (by omega) (by omega) hq) x hxp y hyq
      · rcases hyt with hyp | hyq
        · exact restBlock_lt_of_pos_lt hN
            (restPos_level_lt hj (by omega) hq (by omega)) x hxq y hyp
        · exact restBlock_lt_of_pos_lt hN
            (restPos_level_lt hj (by omega) hq hq) x hxq y hyq

theorem endpointList_lt_endpointList {N : Set ℕ} (hN : N.Infinite)
    {ka i j : ℕ} (hij : i < j) :
    ∀ x ∈ endpointList N ka i, ∀ y ∈ endpointList N ka j, x < y := by
  apply enumSlice_lt_enumSlice _ (enumOf_strictMono hN)
  calc
    endpointStart (enumOf N) ka i + ka ≤ endpointStart (enumOf N) ka (i + 1) := by
      simp only [endpointStart_succ]
      omega
    _ ≤ endpointStart (enumOf N) ka j := endpointStart_mono _ _ (by omega)

theorem endpointList_lt_firstBlock_of_le {N : Set ℕ} (hN : N.Infinite)
    {ka i j : ℕ} (hij : i ≤ j) :
    ∀ x ∈ endpointList N ka i, ∀ y ∈ firstBlock N ka j, x < y := by
  apply enumSlice_lt_enumSlice _ (enumOf_strictMono hN)
  calc
    endpointStart (enumOf N) ka i + ka ≤ endpointStart (enumOf N) ka j + ka := by
      exact Nat.add_le_add_right (endpointStart_mono _ _ hij) ka
    _ ≤ endpointStart (enumOf N) ka j + ka := le_rfl

theorem firstBlock_lt_firstBlock {N : Set ℕ} (hN : N.Infinite)
    {ka i j : ℕ} (hij : i < j) :
    ∀ x ∈ firstBlock N ka i, ∀ y ∈ firstBlock N ka j, x < y := by
  apply enumSlice_lt_enumSlice _ (enumOf_strictMono hN)
  calc
    endpointStart (enumOf N) ka i + ka + endpoint N ka i 0 =
        endpointStart (enumOf N) ka (i + 1) := by
          simp only [endpointStart_succ, endpoint_eq, Nat.add_zero]
    _ ≤ endpointStart (enumOf N) ka j := endpointStart_mono _ _ (by omega)
    _ ≤ endpointStart (enumOf N) ka j + ka := Nat.le_add_right _ _

theorem endpointList_lt_restBlock {N : Set ℕ} (hN : N.Infinite)
    {ka k i j i' : ℕ} (hi : i < 3) :
    ∀ x ∈ endpointList N ka i, ∀ y ∈ restBlock N ka k j i', x < y := by
  apply enumSlice_lt_enumSlice _ (enumOf_strictMono hN)
  calc
    endpointStart (enumOf N) ka i + ka ≤ endpointStart (enumOf N) ka (i + 1) := by
      simp only [endpointStart_succ]
      omega
    _ ≤ endpointStart (enumOf N) ka 3 := endpointStart_mono _ _ (by omega)
    _ ≤ blockStart (endpointStart (enumOf N) ka 3) (restSize N ka k)
        (restPos ka k j i') := blockStart_mono _ _ (Nat.zero_le _)

theorem endpoint_strictMono_left {N : Set ℕ} (hN : N.Infinite)
    {ka i j r : ℕ} (hr : r < ka) (hij : i < j) :
    endpoint N ka i r < endpoint N ka j r := by
  apply enumOf_strictMono hN
  calc
    endpointStart (enumOf N) ka i + r < endpointStart (enumOf N) ka i + ka := by omega
    _ ≤ endpointStart (enumOf N) ka (i + 1) := by
      simp only [endpointStart_succ]
      omega
    _ ≤ endpointStart (enumOf N) ka j := endpointStart_mono _ _ (by omega)
    _ ≤ endpointStart (enumOf N) ka j + r := Nat.le_add_right _ _

theorem length_realizationList {N : Set ℕ} (hN : N.Infinite)
    {ka k i : ℕ} (hk : 0 < k) (hka : 0 < ka) (hi : i < 3) :
    (realizationList N ka k i).length = endpoint N ka i (ka - 1) := by
  have hacc := accLengths_realizationBlocks hN hk hka hi
  have hlast := congrArg List.getLast? hacc
  have hleft :
      (accLengths 0 (realizationBlocks N ka k i)).getLast? =
        some (realizationList N ka k i).length := by
    rw [realizationBlocks_eq_restSeq]
    simpa [realizationList, realizationBlocks_eq_restSeq] using
      (getLast?_accLengths_cons (n := 0) (a := firstBlock N ka i)
        (as := restSeq N ka k 1 (ka - 1) i))
  have hright :
      (endpointList N ka i).getLast? = some (endpoint N ka i (ka - 1)) := by
    rw [endpointList, enumSlice, List.getLast?_map, List.getLast?_range]
    have hkane : ka ≠ 0 := by omega
    simp [hkane, endpoint_eq]
  rw [hleft, hright] at hlast
  exact Option.some.inj hlast

noncomputable def oddScheme (N : Set ℕ) (k p q : ℕ) : List ℕ :=
  endpointList N k p ++ firstBlock N k p ++
    endpointList N k q ++ firstBlock N k q ++
      normalInteractionFrom N k k 1 (k - 1) p q

theorem oddScheme_pairwise {N : Set ℕ} (hN : N.Infinite)
    {k p q : ℕ} (hk : 0 < k) (hpq : p < q) (hq : q < 3) :
    (oddScheme N k p q).Pairwise (· < ·) := by
  have hp3 : p < 3 := hpq.trans hq
  let Dp := endpointList N k p
  let Ap := firstBlock N k p
  let Dq := endpointList N k q
  let Aq := firstBlock N k q
  let I := normalInteractionFrom N k k 1 (k - 1) p q
  have hDp : Dp.Pairwise (· < ·) := endpointList_pairwise hN _ _
  have hAp : Ap.Pairwise (· < ·) := firstBlock_pairwise hN _ _
  have hDq : Dq.Pairwise (· < ·) := endpointList_pairwise hN _ _
  have hAq : Aq.Pairwise (· < ·) := firstBlock_pairwise hN _ _
  have hI : I.Pairwise (· < ·) := by
    apply normalInteractionFrom_pairwise hN hpq hq (by omega)
    intro t ht1 ht2
    omega
  have hDpAp : (Dp ++ Ap).Pairwise (· < ·) :=
    pairwise_append_of_lt hDp hAp (endpointList_lt_firstBlock hN _ _)
  have hpreDq : (Dp ++ Ap ++ Dq).Pairwise (· < ·) := by
    apply pairwise_append_of_lt hDpAp hDq
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact endpointList_lt_endpointList hN hpq x hx y hy
    · exact firstBlock_lt_endpointList hN hpq x hx y hy
  have hpreAq : (Dp ++ Ap ++ Dq ++ Aq).Pairwise (· < ·) := by
    apply pairwise_append_of_lt hpreDq hAq
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hxDq
    · rcases List.mem_append.mp hx with hxDp | hxAp
      · exact endpointList_lt_firstBlock_of_le hN (by omega) x hxDp y hy
      · exact firstBlock_lt_firstBlock hN hpq x hxAp y hy
    · exact endpointList_lt_firstBlock hN _ _ x hxDq y hy
  change (Dp ++ Ap ++ Dq ++ Aq ++ I).Pairwise (· < ·)
  apply pairwise_append_of_lt hpreAq hI
  intro x hx y hy
  rcases mem_normalInteractionFrom.mp hy with ⟨t, ht, hyt⟩
  rcases List.mem_append.mp hx with hx | hxAq
  · rcases List.mem_append.mp hx with hx | hxDq
    · rcases List.mem_append.mp hx with hxDp | hxAp
      · rcases hyt with hyt | hyt
        · exact endpointList_lt_restBlock hN hp3 x hxDp y hyt
        · exact endpointList_lt_restBlock hN hp3 x hxDp y hyt
      · rcases hyt with hyt | hyt
        · exact firstBlock_lt_restBlock hN hp3 x hxAp y hyt
        · exact firstBlock_lt_restBlock hN hp3 x hxAp y hyt
    · rcases hyt with hyt | hyt
      · exact endpointList_lt_restBlock hN hq x hxDq y hyt
      · exact endpointList_lt_restBlock hN hq x hxDq y hyt
  · rcases hyt with hyt | hyt
    · exact firstBlock_lt_restBlock hN hq x hxAq y hyt
    · exact firstBlock_lt_restBlock hN hq x hxAq y hyt

theorem oddScheme_subset {N : Set ℕ} (hN : N.Infinite) (k p q : ℕ) :
    ↑(oddScheme N k p q).toFinset ⊆ N := by
  intro x hx
  have hx' : x ∈ oddScheme N k p q := by
    simpa only [Finset.mem_coe, List.mem_toFinset] using hx
  simp only [oddScheme, List.mem_append] at hx'
  rcases hx' with (((hx | hx) | hx) | hx) | hx
  · exact endpointList_subset hN k p (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact firstBlock_subset hN k p (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact endpointList_subset hN k q (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact firstBlock_subset hN k q (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · rcases mem_normalInteractionFrom.mp hx with ⟨t, ht, hxt | hxt⟩
    · exact restBlock_subset hN k k (1 + t) p
        (by simpa only [Finset.mem_coe, List.mem_toFinset])
    · exact restBlock_subset hN k k (1 + t) q
        (by simpa only [Finset.mem_coe, List.mem_toFinset])

theorem oddFormBody {N : Set ℕ} (hN : N.Infinite)
    (hposN : ∀ x, x ∈ N → 0 < x) {k p q : ℕ}
    (hk : 0 < k) (hpq : p < q) (hq : q < 3) :
    FormBody k k (realizationList N k k p) (realizationList N k k q)
      (oddScheme N k p q) := by
  let ap := firstBlock N k p
  let asp := restSeq N k k 1 (k - 1) p
  let aq := firstBlock N k q
  let asq := restSeq N k k 1 (k - 1) q
  apply FormBody.intro ap asp aq asq
  · rw [length_realizationList hN hk hk (hpq.trans hq),
      length_realizationList hN hk hk hq]
    exact endpoint_strictMono_left hN (by omega) hpq
  · unfold realizationList
    rw [realizationBlocks_eq_restSeq]
  · unfold realizationList
    rw [realizationBlocks_eq_restSeq]
  · intro b hb
    have hb' : b ∈ realizationBlocks N k k p := by
      rw [realizationBlocks_eq_restSeq]
      exact hb
    exact realizationBlocks_ne_nil hN hposN hk hk (hpq.trans hq) b hb'
  · intro b hb
    have hb' : b ∈ realizationBlocks N k k q := by
      rw [realizationBlocks_eq_restSeq]
      exact hb
    exact realizationBlocks_ne_nil hN hposN hk hk hq b hb'
  · simp [asp, restSeq]
    omega
  · simp [asq, restSeq]
    omega
  · unfold oddScheme
    have hpacc := accLengths_realizationBlocks hN hk hk (hpq.trans hq)
    have hqacc := accLengths_realizationBlocks hN hk hk hq
    rw [realizationBlocks_eq_restSeq] at hpacc hqacc
    rw [hpacc, hqacc]
    change _ = _ ++ _ ++ _ ++ _ ++ interact asp asq
    rw [interact_restSeq]
  · exact oddScheme_pairwise hN hk hpq hq

/-! The canonicalization theorem above selected one scheme for each pair.
For realization it is more convenient to run the identical Nash--Williams
argument on *all* witnessed schemes.  A fixed scheme still determines its
unordered pair, which is exactly the injectivity fact proved earlier. -/

structure ExactSchemeWitness (l : ℕ) (zs : List ℕ) where
  left : IncList
  right : IncList
  exact :
    (∃ k, 0 < k ∧ l = 2 * k - 1 ∧
      (FormBody k k left.1 right.1 zs ∨ FormBody k k right.1 left.1 zs)) ∨
    ∃ k, 0 < k ∧ l = 2 * k ∧
      (FormBody (k + 1) k left.1 right.1 zs ∨
        FormBody (k + 1) k right.1 left.1 zs)

theorem ExactSchemeWitness.hasForm {l : ℕ} {zs : List ℕ}
    (w : ExactSchemeWitness l zs) : HasForm l w.left w.right := by
  rcases w.exact with ⟨k, hk, hl, hb⟩ | ⟨k, hk, hl, hb⟩
  · exact Or.inr (Or.inl ⟨k, zs, hk, hl, hb⟩)
  · exact Or.inr (Or.inr ⟨k, zs, hk, hl, hb⟩)

theorem ExactSchemeWitness.isFormScheme {l : ℕ} {zs : List ℕ}
    (w : ExactSchemeWitness l zs) : IsFormScheme l zs := by
  rcases w.exact with ⟨k, hk, hl, hb⟩ | ⟨k, hk, hl, hb⟩
  · exact Or.inl ⟨k, w.left, w.right, hk, hl, hb⟩
  · exact Or.inr ⟨k, w.left, w.right, hk, hl, hb⟩

theorem ExactSchemeWitness.unordered_eq {l : ℕ} {zs : List ℕ}
    (w w' : ExactSchemeWitness l zs) :
    (w.left = w'.left ∧ w.right = w'.right) ∨
      (w.left = w'.right ∧ w.right = w'.left) := by
  rcases w.exact with ⟨k, hk, hl, hb⟩ | ⟨k, hk, hl, hb⟩ <;>
    rcases w'.exact with ⟨k', hk', hl', hb'⟩ | ⟨k', hk', hl', hb'⟩
  · have hkk : k = k' := by omega
    subst k'
    exact formBody_or_unordered_eq hb hb'
  · omega
  · omega
  · have hkk : k = k' := by omega
    subst k'
    exact formBody_or_unordered_eq hb hb'

theorem ExactSchemeWitness.left_transport {l : ℕ} {zs zs' : List ℕ}
    (h : zs = zs') (w : ExactSchemeWitness l zs) :
    (h ▸ w).left = w.left := by
  cases h
  rfl

theorem ExactSchemeWitness.right_transport {l : ℕ} {zs zs' : List ℕ}
    (h : zs = zs') (w : ExactSchemeWitness l zs) :
    (h ▸ w).right = w.right := by
  cases h
  rfl

theorem ExactSchemeWitness.left_transport_form {l l' : ℕ} {zs : List ℕ}
    (h : l = l') (w : ExactSchemeWitness l zs) :
    (h ▸ w).left = w.left := by
  cases h
  rfl

theorem ExactSchemeWitness.right_transport_form {l l' : ℕ} {zs : List ℕ}
    (h : l = l') (w : ExactSchemeWitness l zs) :
    (h ▸ w).right = w.right := by
  cases h
  rfl

def ExactSchemeFamily (l : ℕ) : Set (Finset ℕ) :=
  {s | ∃ zs : List ℕ, Nonempty (ExactSchemeWitness l zs) ∧ zs.toFinset = s}

theorem exactSchemeFamily_thin (l : ℕ) :
    NashWilliams.FinThin (ExactSchemeFamily l) := by
  intro s hs t ht hst
  rcases hs with ⟨zs, ⟨w⟩, rfl⟩
  rcases ht with ⟨zs', ⟨w'⟩, rfl⟩
  have hp : zs <+: zs' :=
    (pairwise_isPrefix_iff_initSeg w.isFormScheme.pairwise
      w'.isFormScheme.pairwise).mpr hst
  have heq : zs = zs' := isFormScheme_thin l w.isFormScheme w'.isFormScheme hp
  exact congrArg List.toFinset heq

structure ExactFinWitness (l : ℕ) (s : Finset ℕ) where
  scheme : List ℕ
  witness : ExactSchemeWitness l scheme
  toFinset_eq : scheme.toFinset = s

theorem exactSchemeFamily_iff_nonempty {l : ℕ} {s : Finset ℕ} :
    s ∈ ExactSchemeFamily l ↔ Nonempty (ExactFinWitness l s) := by
  constructor
  · rintro ⟨zs, ⟨w⟩, hs⟩
    exact ⟨⟨zs, w, hs⟩⟩
  · rintro ⟨w⟩
    exact ⟨w.scheme, ⟨w.witness⟩, w.toFinset_eq⟩

noncomputable def exactSchemeColor (color : IncList → IncList → Bool)
    (l : ℕ) (s : Finset ℕ) : Bool := by
  classical
  exact if h : Nonempty (ExactFinWitness l s) then
    let w := Classical.choice h
    color w.witness.left w.witness.right
  else false

theorem exactSchemeColor_eq (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {l : ℕ} {zs : List ℕ}
    (w : ExactSchemeWitness l zs) :
    exactSchemeColor color l zs.toFinset = color w.left w.right := by
  let w0 : ExactFinWitness l zs.toFinset := ⟨zs, w, rfl⟩
  have hn : Nonempty (ExactFinWitness l zs.toFinset) := ⟨w0⟩
  rw [exactSchemeColor, dif_pos hn]
  let v := Classical.choice hn
  have hscheme : v.scheme = zs := by
    calc
      v.scheme = v.scheme.toFinset.sort (· ≤ ·) :=
        (sort_toFinset_eq_self_of_pairwise v.witness.isFormScheme.pairwise).symm
      _ = zs.toFinset.sort (· ≤ ·) := by rw [v.toFinset_eq]
      _ = zs := sort_toFinset_eq_self_of_pairwise w.isFormScheme.pairwise
  let v' : ExactSchemeWitness l zs := hscheme ▸ v.witness
  have hvleft : v'.left = v.witness.left :=
    ExactSchemeWitness.left_transport hscheme v.witness
  have hvright : v'.right = v.witness.right :=
    ExactSchemeWitness.right_transport hscheme v.witness
  change color v.witness.left v.witness.right = color w.left w.right
  rw [← hvleft, ← hvright]
  rcases v'.unordered_eq w with h | h
  · exact congrArg₂ color h.1 h.2
  · exact (congrArg₂ color h.1 h.2).trans (hcomm w.right w.left)

theorem canonize_one_exact_form (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (l : ℕ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N, N ⊆ M ∧ N.Infinite ∧ ∃ b : Bool,
      ∀ (zs : List ℕ) (w : ExactSchemeWitness l zs),
        (↑zs.toFinset : Set ℕ) ⊆ N → color w.left w.right = b := by
  rcases NashWilliams.nashWilliams_two (ExactSchemeFamily l)
      (exactSchemeFamily_thin l) (exactSchemeColor color l) hM with
    ⟨N, hNM, hNinf, b, hb⟩
  refine ⟨N, hNM, hNinf, b, ?_⟩
  intro zs w hsupport
  rw [← exactSchemeColor_eq color hcomm w]
  exact hb zs.toFinset ⟨zs, ⟨w⟩, rfl⟩ hsupport

structure OddCanonExtension (color : IncList → IncList → Bool) (n : ℕ)
    {M : Set ℕ} (st : CanonState M) where
  marker : ℕ
  next : CanonState M
  formColor : Bool
  marker_mem : marker ∈ st.tail
  next_subset : next.tail ⊆ st.tail
  marker_below : ∀ ⦃y⦄, y ∈ next.tail → marker < y
  homogeneous : ∀ (zs : List ℕ)
    (w : ExactSchemeWitness (2 * (n + 1) - 1) zs),
    (↑zs.toFinset : Set ℕ) ⊆ next.tail → color w.left w.right = formColor

theorem oddCanonExtension_nonempty (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) : Nonempty (OddCanonExtension color n st) := by
  let a := sInf st.tail
  have ha : a ∈ st.tail := Nat.sInf_mem st.tail_infinite.nonempty
  let B : Set ℕ := st.tail \ Set.Iic a
  have hBinf : B.Infinite := st.tail_infinite.sdiff (Set.finite_Iic a)
  rcases canonize_one_exact_form color hcomm (2 * (n + 1) - 1) hBinf with
    ⟨N, hNB, hNinf, b, hb⟩
  have hNtail : N ⊆ st.tail := hNB.trans Set.sdiff_subset
  have haN : ∀ ⦃y⦄, y ∈ N → a < y := by
    intro y hy
    exact Nat.lt_of_not_ge (hNB hy).2
  let st' : CanonState M := {
    tail := N
    tail_infinite := hNinf
    tail_subset := hNtail.trans st.tail_subset }
  exact ⟨{
    marker := a
    next := st'
    formColor := b
    marker_mem := ha
    next_subset := hNtail
    marker_below := haN
    homogeneous := hb }⟩

noncomputable def CanonState.oddExtend (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) : OddCanonExtension color n st :=
  Classical.choice (oddCanonExtension_nonempty color hcomm n st)

noncomputable def oddCanonSeq (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    ℕ → CanonState M
  | 0 => canonInitial hM
  | n + 1 => ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).next

noncomputable def oddCanonMarker (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ℕ :=
  ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).marker

noncomputable def oddCanonFormColor (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (k : ℕ) : Bool :=
  if _hk : 0 < k then
    ((oddCanonSeq color hcomm hM (k - 1)).oddExtend color hcomm (k - 1)).formColor
  else false

theorem oddCanonSeq_succ (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) :
    oddCanonSeq color hcomm hM (n + 1) =
      ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).next := rfl

theorem oddCanonMarker_mem_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : oddCanonMarker color hcomm hM n ∈ (oddCanonSeq color hcomm hM n).tail :=
  ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).marker_mem

theorem oddCanon_tail_succ_subset (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) :
    (oddCanonSeq color hcomm hM (n + 1)).tail ⊆
      (oddCanonSeq color hcomm hM n).tail := by
  rw [oddCanonSeq_succ]
  exact ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).next_subset

theorem oddCanonMarker_below_next_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ∀ ⦃y⦄, y ∈ (oddCanonSeq color hcomm hM (n + 1)).tail →
      oddCanonMarker color hcomm hM n < y := by
  rw [oddCanonSeq_succ]
  exact ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).marker_below

theorem oddCanon_tail_antitone (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    (oddCanonSeq color hcomm hM j).tail ⊆ (oddCanonSeq color hcomm hM i).tail := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Set.Subset.rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact Set.Subset.rfl
      · have hij' : i ≤ j := by omega
        exact (oddCanon_tail_succ_subset color hcomm hM j).trans (ih hij')

theorem oddCanonMarker_mem_earlier_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    oddCanonMarker color hcomm hM j ∈ (oddCanonSeq color hcomm hM i).tail :=
  oddCanon_tail_antitone color hcomm hM hij
    (oddCanonMarker_mem_tail color hcomm hM j)

theorem oddCanonMarker_strictMono (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    StrictMono (oddCanonMarker color hcomm hM) := by
  intro i j hij
  apply oddCanonMarker_below_next_tail color hcomm hM i
  exact oddCanonMarker_mem_earlier_tail color hcomm hM (show i + 1 ≤ j by omega)

def oddCanonSet (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) : Set ℕ :=
  Set.range (oddCanonMarker color hcomm hM)

theorem oddCanonSet_infinite (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    (oddCanonSet color hcomm hM).Infinite :=
  Set.infinite_range_of_injective (oddCanonMarker_strictMono color hcomm hM).injective

theorem oddCanonSet_subset (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    oddCanonSet color hcomm hM ⊆ M := by
  rintro x ⟨n, rfl⟩
  exact (oddCanonSeq color hcomm hM n).tail_subset
    (oddCanonMarker_mem_tail color hcomm hM n)

theorem oddCanonized_of_marker_bound (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {k : ℕ} (hk : 0 < k) {zs : List ℕ}
    (w : ExactSchemeWitness (2 * k - 1) zs)
    (hsupport : (↑zs.toFinset : Set ℕ) ⊆ oddCanonSet color hcomm hM)
    (hbound : ∀ z ∈ zs.toFinset, oddCanonMarker color hcomm hM (k - 1) < z) :
    color w.left w.right = oddCanonFormColor color hcomm hM k := by
  let n := k - 1
  have hn : n + 1 = k := by dsimp [n]; omega
  have htail : (↑zs.toFinset : Set ℕ) ⊆
      (oddCanonSeq color hcomm hM (n + 1)).tail := by
    intro z hz
    rcases hsupport hz with ⟨j, hj⟩
    have hlt : oddCanonMarker color hcomm hM n < oddCanonMarker color hcomm hM j := by
      simpa [n, hj] using hbound z hz
    have hnj : n < j := (oddCanonMarker_strictMono color hcomm hM).lt_iff_lt.mp hlt
    rw [← hj]
    exact oddCanonMarker_mem_earlier_tail color hcomm hM (show n + 1 ≤ j by omega)
  have hformeq : 2 * k - 1 = 2 * (n + 1) - 1 := by omega
  let w' : ExactSchemeWitness (2 * (n + 1) - 1) zs := hformeq ▸ w
  have hwleft : w'.left = w.left := ExactSchemeWitness.left_transport_form hformeq w
  have hwright : w'.right = w.right := ExactSchemeWitness.right_transport_form hformeq w
  have hhom := ((oddCanonSeq color hcomm hM n).oddExtend color hcomm n).homogeneous
    zs w' (by
      rw [← oddCanonSeq_succ color hcomm hM n]
      exact htail)
  rw [hwleft, hwright] at hhom
  simpa [oddCanonFormColor, hk, n] using hhom

theorem oddFormColor_false_of_no_triangle (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {k : ℕ} (hk : 0 < k) :
    oddCanonFormColor color hcomm hM k = false := by
  let S := oddCanonSet color hcomm hM
  let a := oddCanonMarker color hcomm hM (k - 1)
  let N : Set ℕ := S \ Set.Iic a
  have hSinf : S.Infinite := oddCanonSet_infinite color hcomm hM
  have hNinf : N.Infinite := hSinf.sdiff (Set.finite_Iic a)
  have hNS : N ⊆ S := Set.sdiff_subset
  have hNa : ∀ ⦃x⦄, x ∈ N → a < x := by
    intro x hx
    exact Nat.lt_of_not_ge hx.2
  have hNpos : ∀ x, x ∈ N → 0 < x := by
    intro x hx
    exact (Nat.zero_le a).trans_lt (hNa hx)
  let v0 : IncList := ⟨realizationList N k k 0, realizationList_pairwise hNinf (by omega)⟩
  let v1 : IncList := ⟨realizationList N k k 1, realizationList_pairwise hNinf (by omega)⟩
  let v2 : IncList := ⟨realizationList N k k 2, realizationList_pairwise hNinf (by omega)⟩
  have hb01 := oddFormBody hNinf hNpos hk (show 0 < 1 by omega) (show 1 < 3 by omega)
  have hb02 := oddFormBody hNinf hNpos hk (show 0 < 2 by omega) (show 2 < 3 by omega)
  have hb12 := oddFormBody hNinf hNpos hk (show 1 < 2 by omega) (show 2 < 3 by omega)
  let w01 : ExactSchemeWitness (2 * k - 1) (oddScheme N k 0 1) := {
    left := v0
    right := v1
    exact := Or.inl ⟨k, hk, rfl, Or.inl hb01⟩ }
  let w02 : ExactSchemeWitness (2 * k - 1) (oddScheme N k 0 2) := {
    left := v0
    right := v2
    exact := Or.inl ⟨k, hk, rfl, Or.inl hb02⟩ }
  let w12 : ExactSchemeWitness (2 * k - 1) (oddScheme N k 1 2) := {
    left := v1
    right := v2
    exact := Or.inl ⟨k, hk, rfl, Or.inl hb12⟩ }
  have canonPair (p q : ℕ) (hpq : p < q) (hq : q < 3)
      (w : ExactSchemeWitness (2 * k - 1) (oddScheme N k p q)) :
      color w.left w.right = oddCanonFormColor color hcomm hM k := by
    apply oddCanonized_of_marker_bound color hcomm hM hk w
    · exact (oddScheme_subset hNinf k p q).trans hNS
    · intro z hz
      exact hNa (oddScheme_subset hNinf k p q hz)
  have hc01 := canonPair 0 1 (by omega) (by omega) w01
  have hc02 := canonPair 0 2 (by omega) (by omega) w02
  have hc12 := canonPair 1 2 (by omega) (by omega) w12
  have hne01 : v0 ≠ v1 := w01.hasForm.ne
  have hne02 : v0 ≠ v2 := w02.hasForm.ne
  have hne12 : v1 ≠ v2 := w12.hasForm.ne
  cases hb : oddCanonFormColor color hcomm hM k with
  | false => rfl
  | true =>
      exfalso
      apply htri v0 v1 v2 hne01 hne02 hne12
      exact ⟨hc01.trans hb, hc02.trans hb, hc12.trans hb⟩

/-! ## Simultaneous exact-scheme canonization

The preceding odd-only fusion is useful for the realization lemma in
isolation.  Larson's final construction also produces even forms.  We
therefore repeat the same fusion while visiting every positive form index,
in the order `1,2,3,…`.  Unlike the first version of simultaneous
canonization above, this version colors *witnessed schemes* and hence does
not need to identify a chosen representative scheme afterwards. -/

structure ExactCanonExtension (color : IncList → IncList → Bool) (n : ℕ)
    {M : Set ℕ} (st : CanonState M) where
  marker : ℕ
  next : CanonState M
  formColor : Bool
  marker_mem : marker ∈ st.tail
  next_subset : next.tail ⊆ st.tail
  marker_below : ∀ {y}, y ∈ next.tail → marker < y
  homogeneous : ∀ (zs : List ℕ) (w : ExactSchemeWitness (n + 1) zs),
    (↑zs.toFinset : Set ℕ) ⊆ next.tail → color w.left w.right = formColor

theorem exactCanonExtension_nonempty (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) : Nonempty (ExactCanonExtension color n st) := by
  let a := sInf st.tail
  have ha : a ∈ st.tail := Nat.sInf_mem st.tail_infinite.nonempty
  let B : Set ℕ := st.tail \ Set.Iic a
  have hBinf : B.Infinite := st.tail_infinite.sdiff (Set.finite_Iic a)
  rcases canonize_one_exact_form color hcomm (n + 1) hBinf with
    ⟨N, hNB, hNinf, b, hb⟩
  have hNtail : N ⊆ st.tail := hNB.trans Set.sdiff_subset
  have haN : ∀ {y}, y ∈ N → a < y := by
    intro y hy
    exact Nat.lt_of_not_ge (hNB hy).2
  let st' : CanonState M := {
    tail := N
    tail_infinite := hNinf
    tail_subset := hNtail.trans st.tail_subset }
  exact ⟨{
    marker := a
    next := st'
    formColor := b
    marker_mem := ha
    next_subset := hNtail
    marker_below := haN
    homogeneous := hb }⟩

noncomputable def CanonState.exactExtend (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) (n : ℕ) {M : Set ℕ}
    (st : CanonState M) : ExactCanonExtension color n st :=
  Classical.choice (exactCanonExtension_nonempty color hcomm n st)

noncomputable def exactCanonSeq (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    ℕ → CanonState M
  | 0 => canonInitial hM
  | n + 1 => ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).next

noncomputable def exactCanonMarker (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ℕ :=
  ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).marker

noncomputable def exactCanonFormColor (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (l : ℕ) : Bool :=
  if _hl : 0 < l then
    ((exactCanonSeq color hcomm hM (l - 1)).exactExtend color hcomm (l - 1)).formColor
  else false

theorem exactCanonSeq_succ (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) :
    exactCanonSeq color hcomm hM (n + 1) =
      ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).next := rfl

theorem exactCanonMarker_mem_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : exactCanonMarker color hcomm hM n ∈ (exactCanonSeq color hcomm hM n).tail :=
  ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).marker_mem

theorem exactCanon_tail_succ_subset (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) :
    (exactCanonSeq color hcomm hM (n + 1)).tail ⊆
      (exactCanonSeq color hcomm hM n).tail := by
  rw [exactCanonSeq_succ]
  exact ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).next_subset

theorem exactCanonMarker_below_next_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (n : ℕ) : ∀ {y}, y ∈ (exactCanonSeq color hcomm hM (n + 1)).tail →
      exactCanonMarker color hcomm hM n < y := by
  rw [exactCanonSeq_succ]
  exact ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).marker_below

theorem exactCanon_tail_antitone (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    (exactCanonSeq color hcomm hM j).tail ⊆ (exactCanonSeq color hcomm hM i).tail := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact Set.Subset.rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact Set.Subset.rfl
      · have hij' : i ≤ j := by omega
        exact (exactCanon_tail_succ_subset color hcomm hM j).trans (ih hij')

theorem exactCanonMarker_mem_earlier_tail (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {i j : ℕ} (hij : i ≤ j) :
    exactCanonMarker color hcomm hM j ∈ (exactCanonSeq color hcomm hM i).tail :=
  exactCanon_tail_antitone color hcomm hM hij
    (exactCanonMarker_mem_tail color hcomm hM j)

theorem exactCanonMarker_strictMono (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    StrictMono (exactCanonMarker color hcomm hM) := by
  intro i j hij
  apply exactCanonMarker_below_next_tail color hcomm hM i
  exact exactCanonMarker_mem_earlier_tail color hcomm hM (show i + 1 ≤ j by omega)

def exactCanonSet (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) : Set ℕ :=
  Set.range (exactCanonMarker color hcomm hM)

theorem exactCanonSet_infinite (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    (exactCanonSet color hcomm hM).Infinite :=
  Set.infinite_range_of_injective (exactCanonMarker_strictMono color hcomm hM).injective

theorem exactCanonSet_subset (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite) :
    exactCanonSet color hcomm hM ⊆ M := by
  rintro x ⟨n, rfl⟩
  exact (exactCanonSeq color hcomm hM n).tail_subset
    (exactCanonMarker_mem_tail color hcomm hM n)

theorem exactCanonized_of_marker_bound (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    {l : ℕ} (hl : 0 < l) {zs : List ℕ} (w : ExactSchemeWitness l zs)
    (hsupport : (↑zs.toFinset : Set ℕ) ⊆ exactCanonSet color hcomm hM)
    (hbound : ∀ z ∈ zs.toFinset, exactCanonMarker color hcomm hM (l - 1) < z) :
    color w.left w.right = exactCanonFormColor color hcomm hM l := by
  let n := l - 1
  have hn : n + 1 = l := by dsimp [n]; omega
  have htail : (↑zs.toFinset : Set ℕ) ⊆
      (exactCanonSeq color hcomm hM (n + 1)).tail := by
    intro z hz
    rcases hsupport hz with ⟨j, hj⟩
    have hlt : exactCanonMarker color hcomm hM n <
        exactCanonMarker color hcomm hM j := by
      simpa [n, hj] using hbound z hz
    have hnj : n < j := (exactCanonMarker_strictMono color hcomm hM).lt_iff_lt.mp hlt
    rw [← hj]
    exact exactCanonMarker_mem_earlier_tail color hcomm hM (show n + 1 ≤ j by omega)
  let w' : ExactSchemeWitness (n + 1) zs := hn.symm ▸ w
  have hwleft : w'.left = w.left := ExactSchemeWitness.left_transport_form hn.symm w
  have hwright : w'.right = w.right := ExactSchemeWitness.right_transport_form hn.symm w
  have hhom := ((exactCanonSeq color hcomm hM n).exactExtend color hcomm n).homogeneous
    zs w' (by
      rw [← exactCanonSeq_succ color hcomm hM n]
      exact htail)
  rw [hwleft, hwright] at hhom
  simpa [exactCanonFormColor, hl, n] using hhom

/-! ## Realizing the positive even forms

For form `2*k`, the shorter sequence uses `k+1` atomic resource blocks,
whereas the longer sequence is presented using only `k` blocks.  The last
two atomic blocks on the longer side are merged.  At the final resource
level the three vertices were deliberately scheduled in reverse order;
this is what leaves the resulting interaction scheme increasing. -/

theorem restSeq_append (N : Set ℕ) (ka k j m n i : ℕ) :
    restSeq N ka k j (m + n) i =
      restSeq N ka k j m i ++ restSeq N ka k (j + m) n i := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, restSeq_succ, restSeq_succ]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm m 1] using (ih (j := j + 1))

noncomputable def evenRightFirst (N : Set ℕ) (k i : ℕ) : List ℕ :=
  if k = 1 then
    firstBlock N (k + 1) i ++ restBlock N (k + 1) k 1 i
  else firstBlock N (k + 1) i

noncomputable def evenRightRest (N : Set ℕ) (k i : ℕ) : List (List ℕ) :=
  if k = 1 then []
  else
    restSeq N (k + 1) k 1 (k - 2) i ++
      [restBlock N (k + 1) k (k - 1) i ++ restBlock N (k + 1) k k i]

theorem realizationBlocks_even_left (N : Set ℕ) (k i : ℕ) :
    realizationBlocks N (k + 1) k i =
      firstBlock N (k + 1) i :: restSeq N (k + 1) k 1 k i := by
  rw [realizationBlocks_eq_restSeq]
  congr 2

theorem realizationList_even_right (N : Set ℕ) {k i : ℕ} (hk : 0 < k) :
    realizationList N (k + 1) k i =
      (evenRightFirst N k i :: evenRightRest N k i).flatten := by
  unfold realizationList
  rw [realizationBlocks_even_left]
  by_cases hk1 : k = 1
  · subst k
    simp [evenRightFirst, evenRightRest, restSeq_succ]
  · have hk2 : 2 ≤ k := by omega
    have hsplit := restSeq_append N (k + 1) k 1 (k - 2) 2 i
    have hsum : k - 2 + 2 = k := by omega
    rw [hsum] at hsplit
    rw [hsplit]
    have hstart : 1 + (k - 2) = k - 1 := by omega
    rw [hstart]
    simp [evenRightFirst, evenRightRest, hk1, restSeq_succ]
    rw [Nat.sub_add_cancel (show 1 ≤ k by omega)]

@[simp] theorem length_evenRightRest {N : Set ℕ} {k i : ℕ} (hk : 0 < k) :
    (evenRightRest N k i).length = k - 1 := by
  by_cases hk1 : k = 1
  · subst k
    simp [evenRightRest]
  · simp [evenRightRest, restSeq, hk1]
    omega

@[simp] theorem length_evenRightBlocks {N : Set ℕ} {k i : ℕ} (hk : 0 < k) :
    (evenRightFirst N k i :: evenRightRest N k i).length = k := by
  simp [length_evenRightRest hk]
  omega

theorem evenRight_blocks_ne_nil {N : Set ℕ} (hN : N.Infinite)
    (hposN : ∀ x, x ∈ N → 0 < x) {k i : ℕ} (hk : 0 < k) (hi : i < 3) :
    ∀ b ∈ evenRightFirst N k i :: evenRightRest N k i, b ≠ [] := by
  intro b hb
  by_cases hk1 : k = 1
  · subst k
    simp only [evenRightRest, if_pos, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst b
    have hfirst : firstBlock N 2 i ≠ [] := by
      apply enumSlice_ne_nil
      apply hposN
      exact enumOf_mem hN _
    simpa [evenRightFirst] using
      (List.append_ne_nil_of_left_ne_nil hfirst (restBlock N 2 1 1 i))
  · simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · rw [evenRightFirst, if_neg hk1]
      apply enumSlice_ne_nil
      apply hposN
      exact enumOf_mem hN _
    · rw [evenRightRest, if_neg hk1] at hb
      rcases List.mem_append.mp hb with hb | hb
      · rw [restSeq] at hb
        rcases List.mem_map.mp hb with ⟨t, ht, rfl⟩
        exact restBlock_ne_nil hN hk (by omega) hi
      · simp only [List.mem_singleton] at hb
        subst b
        exact List.append_ne_nil_of_left_ne_nil
          (restBlock_ne_nil hN hk (by omega) hi) _

theorem interact_restSeq_append (N : Set ℕ) (ka k j n p q : ℕ)
    (xs ys : List (List ℕ)) :
    interact (restSeq N ka k j n p ++ xs) (restSeq N ka k j n q ++ ys) =
      normalInteractionFrom N ka k j n p q ++ interact xs ys := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [restSeq_succ, restSeq_succ]
      simp only [List.cons_append, interact, normalInteractionFrom_succ,
        List.append_assoc]
      rw [ih]

noncomputable def evenInteraction (N : Set ℕ) (k p q : ℕ) : List ℕ :=
  if k = 1 then restBlock N 2 1 1 p
  else
    normalInteractionFrom N (k + 1) k 1 (k - 2) p q ++
      restBlock N (k + 1) k (k - 1) p ++
      restBlock N (k + 1) k (k - 1) q ++
      restBlock N (k + 1) k k q ++
      restBlock N (k + 1) k k p

theorem interact_evenRight (N : Set ℕ) {k p q : ℕ} (hk : 0 < k) :
    interact (restSeq N (k + 1) k 1 k p) (evenRightRest N k q) =
      evenInteraction N k p q := by
  by_cases hk1 : k = 1
  · subst k
    simp [evenRightRest, evenInteraction, restSeq_succ]
  · have hk2 : 2 ≤ k := by omega
    have hsplit := restSeq_append N (k + 1) k 1 (k - 2) 2 p
    rw [show k - 2 + 2 = k by omega] at hsplit
    rw [hsplit, evenRightRest, if_neg hk1, interact_restSeq_append]
    simp [evenInteraction, hk1, restSeq_succ]
    rw [show 1 + (k - 2) = k - 1 by omega,
      show k - 1 + 1 = k by omega]
    simp [interact, List.append_assoc]

theorem evenInteraction_pairwise {N : Set ℕ} (hN : N.Infinite)
    {k p q : ℕ} (hk : 0 < k) (hpq : p < q) (hq : q < 3) :
    (evenInteraction N k p q).Pairwise (· < ·) := by
  have hp3 : p < 3 := hpq.trans hq
  by_cases hk1 : k = 1
  · subst k
    simpa [evenInteraction] using (restBlock_pairwise hN 2 1 1 p)
  · have hk2 : 2 ≤ k := by omega
    let I := normalInteractionFrom N (k + 1) k 1 (k - 2) p q
    let Pm := restBlock N (k + 1) k (k - 1) p
    let Qm := restBlock N (k + 1) k (k - 1) q
    let Qk := restBlock N (k + 1) k k q
    let Pk := restBlock N (k + 1) k k p
    have hI : I.Pairwise (· < ·) := by
      apply normalInteractionFrom_pairwise hN hpq hq (by omega)
      intro t ht1 ht2 hfinal
      omega
    have hI_lt_m (r : ℕ) (hr : r < 3) :
        ∀ x ∈ I, ∀ y ∈ restBlock N (k + 1) k (k - 1) r, x < y := by
      intro x hx y hy
      rcases mem_normalInteractionFrom.mp hx with ⟨t, ht, hxt | hxt⟩
      · exact restBlock_lt_of_pos_lt hN
          (restPos_level_lt (by omega) (by omega) hp3 hr) x hxt y hy
      · exact restBlock_lt_of_pos_lt hN
          (restPos_level_lt (by omega) (by omega) hq hr) x hxt y hy
    have hI_lt_k (r : ℕ) (hr : r < 3) :
        ∀ x ∈ I, ∀ y ∈ restBlock N (k + 1) k k r, x < y := by
      intro x hx y hy
      rcases mem_normalInteractionFrom.mp hx with ⟨t, ht, hxt | hxt⟩
      · exact restBlock_lt_of_pos_lt hN
          (restPos_level_lt (by omega) (by omega) hp3 hr) x hxt y hy
      · exact restBlock_lt_of_pos_lt hN
          (restPos_level_lt (by omega) (by omega) hq hr) x hxt y hy
    have hPmQm : ∀ x ∈ Pm, ∀ y ∈ Qm, x < y := by
      exact restBlock_lt_of_pos_lt hN
        (restPos_same_lt hpq hq (by simp only [not_and_or]; omega))
    have hm_lt_k (r s : ℕ) (hr : r < 3) (hs : s < 3) :
        ∀ x ∈ restBlock N (k + 1) k (k - 1) r,
          ∀ y ∈ restBlock N (k + 1) k k s, x < y := by
      exact restBlock_lt_of_pos_lt hN
        (restPos_level_lt (by omega) (by omega) hr hs)
    have hQkPk : ∀ x ∈ Qk, ∀ y ∈ Pk, x < y := by
      exact restBlock_lt_of_pos_lt hN
        (restPos_final_lt hpq hq ⟨rfl, rfl⟩)
    have hIP : (I ++ Pm).Pairwise (· < ·) :=
      pairwise_append_of_lt hI (restBlock_pairwise hN _ _ _ _) (hI_lt_m p hp3)
    have hIPQm : (I ++ Pm ++ Qm).Pairwise (· < ·) := by
      apply pairwise_append_of_lt hIP (restBlock_pairwise hN _ _ _ _)
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact hI_lt_m q hq x hx y hy
      · exact hPmQm x hx y hy
    have hIPQmQk : (I ++ Pm ++ Qm ++ Qk).Pairwise (· < ·) := by
      apply pairwise_append_of_lt hIPQm (restBlock_pairwise hN _ _ _ _)
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hxQm
      · rcases List.mem_append.mp hx with hxI | hxPm
        · exact hI_lt_k q hq x hxI y hy
        · exact hm_lt_k p q hp3 hq x hxPm y hy
      · exact hm_lt_k q q hq hq x hxQm y hy
    have hAll : (I ++ Pm ++ Qm ++ Qk ++ Pk).Pairwise (· < ·) := by
      apply pairwise_append_of_lt hIPQmQk (restBlock_pairwise hN _ _ _ _)
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hxQk
      · rcases List.mem_append.mp hx with hx | hxQm
        · rcases List.mem_append.mp hx with hxI | hxPm
          · exact hI_lt_k p hp3 x hxI y hy
          · exact hm_lt_k p p hp3 hp3 x hxPm y hy
        · exact hm_lt_k q p hq hp3 x hxQm y hy
      · exact hQkPk x hxQk y hy
    simpa [evenInteraction, hk1, I, Pm, Qm, Qk, Pk] using hAll

noncomputable def evenScheme (N : Set ℕ) (k p q : ℕ) : List ℕ :=
  let left := firstBlock N (k + 1) p :: restSeq N (k + 1) k 1 k p
  let right := evenRightFirst N k q :: evenRightRest N k q
  accLengths 0 left ++ left.headD [] ++
    accLengths 0 right ++ right.headD [] ++ interact left.tail right.tail

theorem accLengths_evenLeft {N : Set ℕ} (hN : N.Infinite)
    {k i : ℕ} (hk : 0 < k) (hi : i < 3) :
    accLengths 0 (firstBlock N (k + 1) i :: restSeq N (k + 1) k 1 k i) =
      endpointList N (k + 1) i := by
  rw [← realizationBlocks_even_left]
  exact accLengths_realizationBlocks hN hk (by omega) hi

theorem lt_of_mem_accLengths {n : ℕ} {as : List (List ℕ)}
    (hne : ∀ a ∈ as, a ≠ []) {z : ℕ} (hz : z ∈ accLengths n as) : n < z := by
  induction as generalizing n with
  | nil => simp [accLengths] at hz
  | cons a as ih =>
      have ha : 0 < a.length := List.length_pos_of_ne_nil (hne a (by simp))
      simp only [accLengths, List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · have htail : ∀ b ∈ as, b ≠ [] := by
          intro b hb
          exact hne b (by simp [hb])
        have := ih htail hz
        omega

theorem accLengths_pairwise_of_ne {n : ℕ} {as : List (List ℕ)}
    (hne : ∀ a ∈ as, a ≠ []) : (accLengths n as).Pairwise (· < ·) := by
  induction as generalizing n with
  | nil => simp [accLengths]
  | cons a as ih =>
      have htail : ∀ b ∈ as, b ≠ [] := by
        intro b hb
        exact hne b (by simp [hb])
      rw [accLengths, List.pairwise_cons]
      exact ⟨fun z hz ↦ lt_of_mem_accLengths htail hz, ih htail⟩

theorem accLengths_evenRight_mem_endpointList {N : Set ℕ} (hN : N.Infinite)
    {k i : ℕ} (hk : 0 < k) (hi : i < 3) :
    ∀ {z}, z ∈ accLengths 0 (evenRightFirst N k i :: evenRightRest N k i) →
      z ∈ endpointList N (k + 1) i := by
  intro z hz
  by_cases hk1 : k = 1
  · subst k
    have hle : endpoint N 2 i 0 ≤ endpoint N 2 i 1 :=
      (endpoint_strictMono_right hN 2 i (by omega)).le
    have hzraw : z = endpoint N 2 i 0 +
        (endpoint N 2 i 1 - endpoint N 2 i 0) := by
      simpa [evenRightFirst, evenRightRest, accLengths, length_firstBlock,
        length_restBlock (N := N) (k := 1) (j := 1) (i := i)
          (by omega) (by omega) hi] using hz
    rw [Nat.add_sub_of_le hle] at hzraw
    rw [hzraw]
    exact endpoint_mem_endpointList N (by omega)
  · have hk2 : 2 ≤ k := by omega
    let P := realizationBlocksPrefix N (k + 1) k i (k - 2)
    let last := restBlock N (k + 1) k (k - 1) i ++
      restBlock N (k + 1) k k i
    have hblocks : evenRightFirst N k i :: evenRightRest N k i = P ++ [last] := by
      simp [P, last, evenRightFirst, evenRightRest, hk1,
        realizationBlocksPrefix, restSeq, Nat.add_comm 1]
    have haccP : accLengths 0 P =
        (List.range (k - 2 + 1)).map (endpoint N (k + 1) i) := by
      simpa [P] using accLengths_realizationBlocksPrefix hN hk hi
        (show k - 2 < k + 1 by omega)
    have hsum :
        ((evenRightFirst N k i :: evenRightRest N k i).map List.length).sum =
          endpoint N (k + 1) i k := by
      calc
        _ = ((evenRightFirst N k i :: evenRightRest N k i).flatten).length := by simp
        _ = (realizationList N (k + 1) k i).length := by
          rw [realizationList_even_right N hk]
        _ = endpoint N (k + 1) i k := by
          have hlen := length_realizationList (N := N) (ka := k + 1)
            (k := k) (i := i) hN hk (by omega) hi
          simpa only [Nat.add_sub_cancel] using hlen
    rw [hblocks, accLengths_append] at hz
    simp only [List.map_singleton, List.sum_singleton, Nat.zero_add,
      accLengths, List.append_nil, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [haccP] at hz
      rcases List.mem_map.mp hz with ⟨r, hr, rfl⟩
      exact endpoint_mem_endpointList N (by simp only [List.mem_range] at hr; omega)
    · have hzlast : z =
          ((P.map List.length).sum + last.length) := hz
      have htotal : ((P.map List.length).sum + last.length) =
          endpoint N (k + 1) i k := by
        have := hsum
        rw [hblocks] at this
        simpa using this
      rw [hzlast, htotal]
      exact endpoint_mem_endpointList N (by omega)

theorem accLengths_evenRight_subset {N : Set ℕ} (hN : N.Infinite)
    {k i : ℕ} (hk : 0 < k) (hi : i < 3) :
    ↑(accLengths 0 (evenRightFirst N k i :: evenRightRest N k i)).toFinset ⊆ N := by
  intro z hz
  apply endpointList_subset hN (k + 1) i
  simpa only [Finset.mem_coe, List.mem_toFinset] using
    (accLengths_evenRight_mem_endpointList hN hk hi
      (by simpa only [Finset.mem_coe, List.mem_toFinset] using hz))

theorem evenRightFirst_subset {N : Set ℕ} (hN : N.Infinite)
    {k i : ℕ} (hk : 0 < k) : ↑(evenRightFirst N k i).toFinset ⊆ N := by
  intro z hz
  by_cases hk1 : k = 1
  · subst k
    simp only [evenRightFirst, if_pos, List.toFinset_append, Finset.mem_coe,
      Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact firstBlock_subset hN 2 i hz
    · exact restBlock_subset hN 2 1 1 i hz
  · rw [evenRightFirst, if_neg hk1] at hz
    exact firstBlock_subset hN (k + 1) i hz

theorem evenRightRest_flatten_subset {N : Set ℕ} (hN : N.Infinite)
    {k i : ℕ} (hk : 0 < k) : ↑(evenRightRest N k i).flatten.toFinset ⊆ N := by
  intro z hz
  have hzList : z ∈ (evenRightRest N k i).flatten := by
    simpa only [Finset.mem_coe, List.mem_toFinset] using hz
  by_cases hk1 : k = 1
  · subst k
    simp [evenRightRest] at hzList
  · rw [evenRightRest, if_neg hk1] at hzList
    simp only [List.flatten_append, List.flatten_singleton,
      List.mem_append] at hzList
    rcases hzList with hz | hz | hz
    · rw [restSeq] at hz
      rcases List.mem_flatten.mp hz with ⟨b, hb, hzb⟩
      rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
      exact restBlock_subset hN (k + 1) k (1 + r) i
        (by simpa only [Finset.mem_coe, List.mem_toFinset])
    · exact restBlock_subset hN (k + 1) k (k - 1) i
        (by simpa only [Finset.mem_coe, List.mem_toFinset])
    · exact restBlock_subset hN (k + 1) k k i
        (by simpa only [Finset.mem_coe, List.mem_toFinset])

theorem evenScheme_subset {N : Set ℕ} (hN : N.Infinite)
    {k p q : ℕ} (hk : 0 < k) (hp : p < 3) (hq : q < 3) :
    ↑(evenScheme N k p q).toFinset ⊆ N := by
  intro z hz
  let left := firstBlock N (k + 1) p :: restSeq N (k + 1) k 1 k p
  let right := evenRightFirst N k q :: evenRightRest N k q
  have hzList : z ∈ evenScheme N k p q := by
    simpa only [Finset.mem_coe, List.mem_toFinset] using hz
  simp only [evenScheme, left, right, List.mem_append] at hzList
  rcases hzList with (((hz | hz) | hz) | hz) | hz
  · rw [accLengths_evenLeft hN hk hp] at hz
    exact endpointList_subset hN (k + 1) p
      (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact firstBlock_subset hN (k + 1) p
      (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact accLengths_evenRight_subset hN hk hq
      (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · exact evenRightFirst_subset hN hk
      (by simpa only [Finset.mem_coe, List.mem_toFinset])
  · have hzFin : z ∈ (interact left.tail right.tail).toFinset := by
      simpa only [Finset.mem_coe, List.mem_toFinset] using hz
    rw [toFinset_interact] at hzFin
    simp only [Finset.mem_union] at hzFin
    rcases hzFin with hz | hz
    · rw [show left.tail = restSeq N (k + 1) k 1 k p by rfl] at hz
      rw [restSeq] at hz
      rcases List.mem_flatten.mp (by simpa only [Finset.mem_coe, List.mem_toFinset] using hz) with
        ⟨b, hb, hzb⟩
      rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
      exact restBlock_subset hN (k + 1) k (1 + r) p
        (by simpa only [Finset.mem_coe, List.mem_toFinset])
    · exact evenRightRest_flatten_subset hN hk hz

theorem mem_evenInteraction_rest {N : Set ℕ} {k p q x : ℕ}
    (hk : 0 < k) (hp : p < 3) (hq : q < 3)
    (hx : x ∈ evenInteraction N k p q) :
    ∃ j r, r < 3 ∧ x ∈ restBlock N (k + 1) k j r := by
  by_cases hk1 : k = 1
  · subst k
    exact ⟨1, p, hp, by simpa [evenInteraction] using hx⟩
  · simp only [evenInteraction, if_neg hk1, List.mem_append] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx)
    · rcases mem_normalInteractionFrom.mp hx with ⟨t, ht, hxt | hxt⟩
      · exact ⟨1 + t, p, hp, hxt⟩
      · exact ⟨1 + t, q, hq, hxt⟩
    · exact ⟨k - 1, p, hp, hx⟩
    · exact ⟨k - 1, q, hq, hx⟩
    · exact ⟨k, q, hq, hx⟩
    · exact ⟨k, p, hp, hx⟩

theorem evenScheme_pairwise {N : Set ℕ} (hN : N.Infinite)
    (hposN : ∀ x, x ∈ N → 0 < x) {k p q : ℕ}
    (hk : 0 < k) (hpq : p < q) (hq : q < 3) :
    (evenScheme N k p q).Pairwise (· < ·) := by
  have hp3 : p < 3 := hpq.trans hq
  let Dp := endpointList N (k + 1) p
  let Ap := firstBlock N (k + 1) p
  let Rq := evenRightFirst N k q :: evenRightRest N k q
  let Dq := accLengths 0 Rq
  let Aq := evenRightFirst N k q
  let I := evenInteraction N k p q
  have hDp : Dp.Pairwise (· < ·) := endpointList_pairwise hN _ _
  have hAp : Ap.Pairwise (· < ·) := firstBlock_pairwise hN _ _
  have hDq : Dq.Pairwise (· < ·) := by
    apply accLengths_pairwise_of_ne
    exact evenRight_blocks_ne_nil hN hposN hk hq
  have hAq : Aq.Pairwise (· < ·) := by
    by_cases hk1 : k = 1
    · subst k
      simpa [Aq, evenRightFirst] using (pairwise_append_of_lt
        (firstBlock_pairwise hN 2 q) (restBlock_pairwise hN 2 1 1 q)
        (firstBlock_lt_restBlock hN hq))
    · simpa [Aq, evenRightFirst, hk1] using firstBlock_pairwise hN (k + 1) q
  have hI : I.Pairwise (· < ·) := evenInteraction_pairwise hN hk hpq hq
  have hDpAp : (Dp ++ Ap).Pairwise (· < ·) :=
    pairwise_append_of_lt hDp hAp (endpointList_lt_firstBlock hN _ _)
  have hpreDq : (Dp ++ Ap ++ Dq).Pairwise (· < ·) := by
    apply pairwise_append_of_lt hDpAp hDq
    intro x hx y hy
    have hyD : y ∈ endpointList N (k + 1) q := by
      apply accLengths_evenRight_mem_endpointList hN hk hq
      exact hy
    rcases List.mem_append.mp hx with hx | hx
    · exact endpointList_lt_endpointList hN hpq x hx y hyD
    · exact firstBlock_lt_endpointList hN hpq x hx y hyD
  have hpreAq : (Dp ++ Ap ++ Dq ++ Aq).Pairwise (· < ·) := by
    apply pairwise_append_of_lt hpreDq hAq
    intro x hx y hy
    have hxCases : x ∈ Dp ∨ x ∈ Ap ∨ x ∈ Dq := by
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    have hxDq (hxq : x ∈ Dq) : x ∈ endpointList N (k + 1) q :=
      accLengths_evenRight_mem_endpointList hN hk hq hxq
    by_cases hk1 : k = 1
    · subst k
      simp only [Aq, evenRightFirst, if_pos, List.mem_append] at hy
      rcases hy with hy | hy
      · rcases hxCases with hx | hx | hx
        · exact endpointList_lt_firstBlock_of_le hN hpq.le x hx y hy
        · exact firstBlock_lt_firstBlock hN hpq x hx y hy
        · exact endpointList_lt_firstBlock hN 2 q x (hxDq hx) y hy
      · rcases hxCases with hx | hx | hx
        · exact endpointList_lt_restBlock hN hp3 x hx y hy
        · exact firstBlock_lt_restBlock hN hp3 x hx y hy
        · exact endpointList_lt_restBlock hN hq x (hxDq hx) y hy
    · have hy' : y ∈ firstBlock N (k + 1) q := by
        simpa [Aq, evenRightFirst, hk1] using hy
      rcases hxCases with hx | hx | hx
      · exact endpointList_lt_firstBlock_of_le hN hpq.le x hx y hy'
      · exact firstBlock_lt_firstBlock hN hpq x hx y hy'
      · exact endpointList_lt_firstBlock hN (k + 1) q x (hxDq hx) y hy'
  have hAll : (Dp ++ Ap ++ Dq ++ Aq ++ I).Pairwise (· < ·) := by
    apply pairwise_append_of_lt hpreAq hI
    intro x hx y hy
    have hxCases : x ∈ Dp ∨ x ∈ Ap ∨ x ∈ Dq ∨ x ∈ Aq := by
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx))
    have hxDq (hxq : x ∈ Dq) : x ∈ endpointList N (k + 1) q :=
      accLengths_evenRight_mem_endpointList hN hk hq hxq
    by_cases hk1 : k = 1
    · subst k
      have hy' : y ∈ restBlock N 2 1 1 p := by
        simpa [I, evenInteraction] using hy
      rcases hxCases with hx | hx | hx | hx
      · exact endpointList_lt_restBlock hN hp3 x hx y hy'
      · exact firstBlock_lt_restBlock hN hp3 x hx y hy'
      · exact endpointList_lt_restBlock hN hq x (hxDq hx) y hy'
      · simp only [Aq, evenRightFirst, if_pos, List.mem_append] at hx
        rcases hx with hx | hx
        · exact firstBlock_lt_restBlock hN hq x hx y hy'
        · exact restBlock_lt_of_pos_lt hN
            (restPos_final_lt hpq hq ⟨rfl, rfl⟩) x hx y hy'
    · rcases mem_evenInteraction_rest hk hp3 hq hy with ⟨j, r, hr, hyr⟩
      rcases hxCases with hx | hx | hx | hx
      · exact endpointList_lt_restBlock hN hp3 x hx y hyr
      · exact firstBlock_lt_restBlock hN hp3 x hx y hyr
      · exact endpointList_lt_restBlock hN hq x (hxDq hx) y hyr
      · have hx' : x ∈ firstBlock N (k + 1) q := by
          simpa [Aq, evenRightFirst, hk1] using hx
        exact firstBlock_lt_restBlock hN hq x hx' y hyr
  unfold evenScheme
  simp only [List.headD_cons, List.tail_cons]
  rw [accLengths_evenLeft hN hk hp3, interact_evenRight N hk]
  exact hAll

theorem evenFormBody {N : Set ℕ} (hN : N.Infinite)
    (hposN : ∀ x, x ∈ N → 0 < x) {k p q : ℕ}
    (hk : 0 < k) (hpq : p < q) (hq : q < 3) :
    FormBody (k + 1) k
      (realizationList N (k + 1) k p) (realizationList N (k + 1) k q)
      (evenScheme N k p q) := by
  have hp3 : p < 3 := hpq.trans hq
  let ap := firstBlock N (k + 1) p
  let asp := restSeq N (k + 1) k 1 k p
  let aq := evenRightFirst N k q
  let asq := evenRightRest N k q
  apply FormBody.intro ap asp aq asq
  · rw [length_realizationList (N := N) (ka := k + 1) (k := k)
        (i := p) hN hk (by omega) hp3,
      length_realizationList (N := N) (ka := k + 1) (k := k)
        (i := q) hN hk (by omega) hq]
    exact endpoint_strictMono_left hN (by omega) hpq
  · unfold realizationList
    rw [realizationBlocks_even_left]
  · exact realizationList_even_right N hk
  · intro b hb
    have hb' : b ∈ realizationBlocks N (k + 1) k p := by
      rw [realizationBlocks_even_left]
      exact hb
    exact realizationBlocks_ne_nil hN hposN hk (by omega) hp3 b hb'
  · exact evenRight_blocks_ne_nil hN hposN hk hq
  · simp [asp, restSeq]
  · simpa [aq, asq] using length_evenRightBlocks (N := N) (k := k) (i := q) hk
  · rfl
  · exact evenScheme_pairwise hN hposN hk hpq hq

theorem exactOddFormColor_false_of_no_triangle (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {k : ℕ} (hk : 0 < k) :
    exactCanonFormColor color hcomm hM (2 * k - 1) = false := by
  let l := 2 * k - 1
  have hl : 0 < l := by dsimp [l]; omega
  let S := exactCanonSet color hcomm hM
  let a := exactCanonMarker color hcomm hM (l - 1)
  let N : Set ℕ := S \ Set.Iic a
  have hSinf : S.Infinite := exactCanonSet_infinite color hcomm hM
  have hNinf : N.Infinite := hSinf.sdiff (Set.finite_Iic a)
  have hNS : N ⊆ S := Set.sdiff_subset
  have hNa : ∀ ⦃x⦄, x ∈ N → a < x := by
    intro x hx
    exact Nat.lt_of_not_ge hx.2
  have hNpos : ∀ x, x ∈ N → 0 < x := by
    intro x hx
    exact (Nat.zero_le a).trans_lt (hNa hx)
  let v0 : IncList := ⟨realizationList N k k 0, realizationList_pairwise hNinf (by omega)⟩
  let v1 : IncList := ⟨realizationList N k k 1, realizationList_pairwise hNinf (by omega)⟩
  let v2 : IncList := ⟨realizationList N k k 2, realizationList_pairwise hNinf (by omega)⟩
  have hb01 := oddFormBody hNinf hNpos hk (show 0 < 1 by omega) (show 1 < 3 by omega)
  have hb02 := oddFormBody hNinf hNpos hk (show 0 < 2 by omega) (show 2 < 3 by omega)
  have hb12 := oddFormBody hNinf hNpos hk (show 1 < 2 by omega) (show 2 < 3 by omega)
  let w01 : ExactSchemeWitness l (oddScheme N k 0 1) := {
    left := v0
    right := v1
    exact := Or.inl ⟨k, hk, by simp [l], Or.inl hb01⟩ }
  let w02 : ExactSchemeWitness l (oddScheme N k 0 2) := {
    left := v0
    right := v2
    exact := Or.inl ⟨k, hk, by simp [l], Or.inl hb02⟩ }
  let w12 : ExactSchemeWitness l (oddScheme N k 1 2) := {
    left := v1
    right := v2
    exact := Or.inl ⟨k, hk, by simp [l], Or.inl hb12⟩ }
  have canonPair (p q : ℕ) (w : ExactSchemeWitness l (oddScheme N k p q)) :
      color w.left w.right = exactCanonFormColor color hcomm hM l := by
    apply exactCanonized_of_marker_bound color hcomm hM hl w
    · exact (oddScheme_subset hNinf k p q).trans hNS
    · intro z hz
      exact hNa (oddScheme_subset hNinf k p q hz)
  have hc01 := canonPair 0 1 w01
  have hc02 := canonPair 0 2 w02
  have hc12 := canonPair 1 2 w12
  have hne01 : v0 ≠ v1 := w01.hasForm.ne
  have hne02 : v0 ≠ v2 := w02.hasForm.ne
  have hne12 : v1 ≠ v2 := w12.hasForm.ne
  cases hb : exactCanonFormColor color hcomm hM l with
  | false => rfl
  | true =>
      exfalso
      apply htri v0 v1 v2 hne01 hne02 hne12
      exact ⟨hc01.trans hb, hc02.trans hb, hc12.trans hb⟩

theorem exactEvenFormColor_false_of_no_triangle (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {k : ℕ} (hk : 0 < k) :
    exactCanonFormColor color hcomm hM (2 * k) = false := by
  let l := 2 * k
  have hl : 0 < l := by dsimp [l]; omega
  let S := exactCanonSet color hcomm hM
  let a := exactCanonMarker color hcomm hM (l - 1)
  let N : Set ℕ := S \ Set.Iic a
  have hSinf : S.Infinite := exactCanonSet_infinite color hcomm hM
  have hNinf : N.Infinite := hSinf.sdiff (Set.finite_Iic a)
  have hNS : N ⊆ S := Set.sdiff_subset
  have hNa : ∀ ⦃x⦄, x ∈ N → a < x := by
    intro x hx
    exact Nat.lt_of_not_ge hx.2
  have hNpos : ∀ x, x ∈ N → 0 < x := by
    intro x hx
    exact (Nat.zero_le a).trans_lt (hNa hx)
  let v0 : IncList := ⟨realizationList N (k + 1) k 0,
    realizationList_pairwise hNinf (by omega)⟩
  let v1 : IncList := ⟨realizationList N (k + 1) k 1,
    realizationList_pairwise hNinf (by omega)⟩
  let v2 : IncList := ⟨realizationList N (k + 1) k 2,
    realizationList_pairwise hNinf (by omega)⟩
  have hb01 := evenFormBody hNinf hNpos hk (show 0 < 1 by omega) (show 1 < 3 by omega)
  have hb02 := evenFormBody hNinf hNpos hk (show 0 < 2 by omega) (show 2 < 3 by omega)
  have hb12 := evenFormBody hNinf hNpos hk (show 1 < 2 by omega) (show 2 < 3 by omega)
  let w01 : ExactSchemeWitness l (evenScheme N k 0 1) := {
    left := v0
    right := v1
    exact := Or.inr ⟨k, hk, by simp [l], Or.inl hb01⟩ }
  let w02 : ExactSchemeWitness l (evenScheme N k 0 2) := {
    left := v0
    right := v2
    exact := Or.inr ⟨k, hk, by simp [l], Or.inl hb02⟩ }
  let w12 : ExactSchemeWitness l (evenScheme N k 1 2) := {
    left := v1
    right := v2
    exact := Or.inr ⟨k, hk, by simp [l], Or.inl hb12⟩ }
  have canonPair (p q : ℕ) (hp : p < 3) (hq : q < 3)
      (w : ExactSchemeWitness l (evenScheme N k p q)) :
      color w.left w.right = exactCanonFormColor color hcomm hM l := by
    apply exactCanonized_of_marker_bound color hcomm hM hl w
    · exact (evenScheme_subset hNinf hk hp hq).trans hNS
    · intro z hz
      exact hNa (evenScheme_subset hNinf hk hp hq hz)
  have hc01 := canonPair 0 1 (by omega) (by omega) w01
  have hc02 := canonPair 0 2 (by omega) (by omega) w02
  have hc12 := canonPair 1 2 (by omega) (by omega) w12
  have hne01 : v0 ≠ v1 := w01.hasForm.ne
  have hne02 : v0 ≠ v2 := w02.hasForm.ne
  have hne12 : v1 ≠ v2 := w12.hasForm.ne
  cases hb : exactCanonFormColor color hcomm hM l with
  | false => rfl
  | true =>
      exfalso
      apply htri v0 v1 v2 hne01 hne02 hne12
      exact ⟨hc01.trans hb, hc02.trans hb, hc12.trans hb⟩

theorem exactPositiveFormColor_false_of_no_triangle
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x) {M : Set ℕ} (hM : M.Infinite)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {l : ℕ} (hl : 0 < l) : exactCanonFormColor color hcomm hM l = false := by
  obtain ⟨k, h | h⟩ := Nat.even_or_odd' l
  · rw [h]
    apply exactEvenFormColor_false_of_no_triangle color hcomm hM htri
    omega
  · have hform : l = 2 * (k + 1) - 1 := by omega
    rw [hform]
    exact exactOddFormColor_false_of_no_triangle color hcomm hM htri (by omega)

/-! ## A stage-allocated universal family

The remaining construction allocates every finite resource at a finite
stage.  `universalStarts m k` records the starts of stages `0,...,k`; using
a list here makes the course-of-values dependency of a stage on all earlier
endpoint gaps completely explicit and structurally recursive. -/

def universalStartAt (ss : List ℕ) (j : ℕ) : ℕ := ss.getD j 2

def universalDiffFrom (m : ℕ → ℕ) (ss : List ℕ) (j i : ℕ) : ℕ :=
  m (universalStartAt ss j + i + 1) - m (universalStartAt ss j + i)

def universalSlotSizeFrom (m : ℕ → ℕ) (k : ℕ) (ss : List ℕ) (p : ℕ) : ℕ :=
  if hk : k = 0 then 0
  else
    let j := p / k
    let i := p % k
    if i < j then universalDiffFrom m ss j i else 0

def universalBlockBaseFrom (m : ℕ → ℕ) (k : ℕ) (ss : List ℕ) : ℕ :=
  universalStartAt ss k + (k + 1) + m (universalStartAt ss k)

def universalStageEndFrom (m : ℕ → ℕ) (k : ℕ) (ss : List ℕ) : ℕ :=
  blockStart (universalBlockBaseFrom m k ss)
    (universalSlotSizeFrom m k ss) (k * k)

def universalStarts (m : ℕ → ℕ) : ℕ → List ℕ
  | 0 => [2]
  | k + 1 =>
      let ss := universalStarts m k
      ss ++ [universalStageEndFrom m k ss + 2]

@[simp] theorem length_universalStarts (m : ℕ → ℕ) (k : ℕ) :
    (universalStarts m k).length = k + 1 := by
  induction k with
  | zero => simp [universalStarts]
  | succ k ih => simp [universalStarts, ih]

def universalStageStart (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  universalStartAt (universalStarts m k) k

noncomputable def universalD (m : ℕ → ℕ) (k : ℕ) : List ℕ :=
  enumSlice m (universalStageStart m k) (k + 1)

noncomputable def universalA (m : ℕ → ℕ) (k : ℕ) : List ℕ :=
  enumSlice m (universalStageStart m k + (k + 1))
    (m (universalStageStart m k))

def universalDiff (m : ℕ → ℕ) (j i : ℕ) : ℕ :=
  m (universalStageStart m j + i + 1) -
    m (universalStageStart m j + i)

def universalSlotSize (m : ℕ → ℕ) (k p : ℕ) : ℕ :=
  if hk : k = 0 then 0
  else
    let j := p / k
    let i := p % k
    if i < j then universalDiff m j i else 0

def universalBlockBase (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  universalStageStart m k + (k + 1) + m (universalStageStart m k)

noncomputable def universalB (m : ℕ → ℕ) (k j i : ℕ) : List ℕ :=
  enumSlice m
    (blockStart (universalBlockBase m k) (universalSlotSize m k) (j * k + i))
    (universalDiff m j i)

theorem universalStartAt_starts_eq (m : ℕ → ℕ) {j k : ℕ} (hjk : j ≤ k) :
    universalStartAt (universalStarts m k) j = universalStageStart m j := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst j
      rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst j
        rfl
      · have hjk' : j ≤ k := by omega
        change (universalStarts m (k + 1)).getD j 2 =
          (universalStarts m j).getD j 2
        rw [universalStarts, List.getD_append]
        · exact ih hjk'
        · simpa using hjk'.trans_lt (by omega : k < k + 1)

theorem universalDiffFrom_starts_eq (m : ℕ → ℕ) {j k i : ℕ} (hjk : j ≤ k) :
    universalDiffFrom m (universalStarts m k) j i = universalDiff m j i := by
  simp only [universalDiffFrom, universalDiff,
    universalStartAt_starts_eq m hjk]

theorem blockStart_congr_prefix {base : ℕ} {f g : ℕ → ℕ} {n : ℕ}
    (hfg : ∀ i < n, f i = g i) : blockStart base f n = blockStart base g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [blockStart_succ, blockStart_succ, ih (fun i hi ↦ hfg i (by omega)), hfg n (by omega)]

theorem universalSlotSizeFrom_starts_eq (m : ℕ → ℕ) {k p : ℕ}
    (hp : p < k * k) :
    universalSlotSizeFrom m k (universalStarts m k) p = universalSlotSize m k p := by
  have hk : k ≠ 0 := by rintro rfl; simp at hp
  have hj : p / k ≤ k := by
    have hlt : p / k < k := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_ne_zero hk)).2 hp
    omega
  simp only [universalSlotSizeFrom, universalSlotSize, dif_neg hk]
  split_ifs with h
  · exact universalDiffFrom_starts_eq m hj
  · rfl

theorem universalStageStart_succ (m : ℕ → ℕ) (k : ℕ) :
    universalStageStart m (k + 1) =
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) + 2 := by
  have hend : universalStageEndFrom m k (universalStarts m k) =
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) := by
    unfold universalStageEndFrom universalBlockBase universalBlockBaseFrom
    rw [universalStartAt_starts_eq m (le_refl k)]
    apply blockStart_congr_prefix
    intro p hp
    exact universalSlotSizeFrom_starts_eq m hp
  unfold universalStageStart universalStartAt
  rw [universalStarts]
  rw [List.getD_append_right]
  · simp [length_universalStarts, hend]
  · simp [length_universalStarts]

theorem universalStageStart_strictMono (m : ℕ → ℕ) :
    StrictMono (universalStageStart m) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [universalStageStart_succ]
  have hbase : universalBlockBase m k ≤
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) :=
    blockStart_mono _ _ (Nat.zero_le _)
  have hsbase : universalStageStart m k < universalBlockBase m k := by
    simp only [universalBlockBase]
    omega
  exact (hsbase.trans_le hbase).trans (Nat.lt_add_of_pos_right (by omega))

theorem universalStageStart_bound (m : ℕ → ℕ) (k : ℕ) :
    2 * k + 1 < universalStageStart m k := by
  induction k with
  | zero => simp [universalStageStart, universalStartAt, universalStarts]
  | succ k ih =>
      rw [universalStageStart_succ]
      have hbase : universalBlockBase m k ≤
          blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) :=
        blockStart_mono _ _ (Nat.zero_le _)
      have hlt : 2 * (k + 1) + 1 < universalBlockBase m k + 2 := by
        simp only [universalBlockBase]
        omega
      exact hlt.trans_le (Nat.add_le_add_right hbase 2)

theorem universalSlotSize_valid (m : ℕ → ℕ) {k j i : ℕ}
    (hjk : j < k) (hij : i < j) :
    universalSlotSize m k (j * k + i) = universalDiff m j i := by
  have hk : 0 < k := by omega
  have hik : i < k := hij.trans hjk
  simp only [universalSlotSize, dif_neg (Nat.ne_of_gt hk)]
  rw [Nat.mul_comm j k]
  rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hik, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hik]
  simp [hij]

theorem universalSlot_lt_square {k j i : ℕ} (hjk : j < k) (hij : i < j) :
    j * k + i < k * k := by
  have hik : i < k := hij.trans hjk
  calc
    j * k + i < j * k + k := Nat.add_lt_add_left hik _
    _ = (j + 1) * k := by rw [Nat.add_mul, one_mul]
    _ ≤ k * k := Nat.mul_le_mul_right k (by omega)

@[simp] theorem length_universalD (m : ℕ → ℕ) (k : ℕ) :
    (universalD m k).length = k + 1 := by simp [universalD]

@[simp] theorem length_universalA (m : ℕ → ℕ) (k : ℕ) :
    (universalA m k).length = m (universalStageStart m k) := by simp [universalA]

@[simp] theorem length_universalB (m : ℕ → ℕ) (k j i : ℕ) :
    (universalB m k j i).length = universalDiff m j i := by simp [universalB]

theorem universalDiff_pos {m : ℕ → ℕ} (hm : StrictMono m) (j i : ℕ) :
    0 < universalDiff m j i := by
  unfold universalDiff
  exact Nat.sub_pos_of_lt (hm (by omega))

theorem universalA_ne_nil {m : ℕ → ℕ} (hm : StrictMono m) (k : ℕ) :
    universalA m k ≠ [] := by
  apply enumSlice_ne_nil
  have hs : 0 < universalStageStart m k := by
    have := universalStageStart_bound m k
    omega
  exact (Nat.zero_le (m 0)).trans_lt (hm hs)

theorem universalB_ne_nil {m : ℕ → ℕ} (hm : StrictMono m) (k j i : ℕ) :
    universalB m k j i ≠ [] := by
  exact enumSlice_ne_nil _ _ _ (universalDiff_pos hm j i)

theorem universalD_pairwise {m : ℕ → ℕ} (hm : StrictMono m) (k : ℕ) :
    (universalD m k).Pairwise (· < ·) := enumSlice_pairwise m hm _ _

theorem universalA_pairwise {m : ℕ → ℕ} (hm : StrictMono m) (k : ℕ) :
    (universalA m k).Pairwise (· < ·) := enumSlice_pairwise m hm _ _

theorem universalB_pairwise {m : ℕ → ℕ} (hm : StrictMono m) (k j i : ℕ) :
    (universalB m k j i).Pairwise (· < ·) := enumSlice_pairwise m hm _ _

theorem universalBlockBase_lt_nextStage (m : ℕ → ℕ) (k : ℕ) :
    universalBlockBase m k < universalStageStart m (k + 1) := by
  rw [universalStageStart_succ]
  have hbase : universalBlockBase m k ≤
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) :=
    blockStart_mono _ _ (Nat.zero_le _)
  omega

theorem universalB_end_le_stageEnd (m : ℕ → ℕ) {k j i : ℕ}
    (hjk : j < k) (hij : i < j) :
    blockStart (universalBlockBase m k) (universalSlotSize m k) (j * k + i) +
        universalDiff m j i ≤
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) := by
  rw [← universalSlotSize_valid m hjk hij]
  calc
    _ = blockStart (universalBlockBase m k) (universalSlotSize m k)
        (j * k + i + 1) := by rw [blockStart_succ]
    _ ≤ _ := blockStart_mono _ _ (by
      exact Nat.succ_le_iff.mpr (universalSlot_lt_square hjk hij))

theorem universalA_lt_B {m : ℕ → ℕ} (hm : StrictMono m)
    {j k r i : ℕ} (hjk : j < k) :
    ∀ x ∈ universalA m j, ∀ y ∈ universalB m k r i, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hnext : universalBlockBase m j < universalStageStart m (j + 1) :=
    universalBlockBase_lt_nextStage m j
  have hstages : universalStageStart m (j + 1) ≤ universalStageStart m k :=
    (universalStageStart_strictMono m).monotone (by omega)
  have hblock : universalBlockBase m k ≤
      blockStart (universalBlockBase m k) (universalSlotSize m k) (r * k + i) :=
    blockStart_mono _ _ (Nat.zero_le _)
  have hsbase : universalStageStart m k ≤ universalBlockBase m k := by
    unfold universalBlockBase
    omega
  simpa only [universalA, universalB, universalBlockBase] using
    hnext.le.trans (hstages.trans (by
      exact hsbase.trans hblock))

theorem universalB_lt_B_stage {m : ℕ → ℕ} (hm : StrictMono m)
    {k r j i j' i' : ℕ} (hjk : j < k) (hij : i < j) (hkr : k < r) :
    ∀ x ∈ universalB m k j i, ∀ y ∈ universalB m r j' i', x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hend := universalB_end_le_stageEnd m hjk hij
  have hnext :
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) <
        universalStageStart m (k + 1) := by
    rw [universalStageStart_succ]
    omega
  have hstages : universalStageStart m (k + 1) ≤ universalStageStart m r :=
    (universalStageStart_strictMono m).monotone (by omega)
  have hblock : universalStageStart m r ≤
      blockStart (universalBlockBase m r) (universalSlotSize m r) (j' * r + i') := by
    have hsbase : universalStageStart m r ≤ universalBlockBase m r := by
      unfold universalBlockBase
      omega
    exact hsbase.trans (blockStart_mono _ _ (Nat.zero_le _))
  exact hend.trans (hnext.le.trans (hstages.trans hblock))

theorem universalB_lt_B_sameStage {m : ℕ → ℕ} (hm : StrictMono m)
    {k j i j' i' : ℕ} (hjk : j < k) (hij : i < j)
    (hj'k : j' < k) (hi'j' : i' < j')
    (hslot : j * k + i < j' * k + i') :
    ∀ x ∈ universalB m k j i, ∀ y ∈ universalB m k j' i', x < y := by
  apply enumSlice_lt_enumSlice m hm
  rw [← universalSlotSize_valid m hjk hij]
  exact blockStart_end_le hslot

noncomputable def universalBSeq (m : ℕ → ℕ) (j i : ℕ) :
    List ℕ → List (List ℕ)
  | [] => []
  | k :: ks => universalB m k j i :: universalBSeq m j (i + 1) ks

noncomputable def universalBlocks (m : ℕ → ℕ) (s : List ℕ) : List (List ℕ) :=
  universalA m s.length ::
    universalBSeq m s.length 0 (intoInc (s.length + 1) s)

noncomputable def universalVertexList (m : ℕ → ℕ) (s : List ℕ) : List ℕ :=
  (universalBlocks m s).flatten

@[simp] theorem length_universalBSeq (m : ℕ → ℕ) (j i : ℕ) (ks : List ℕ) :
    (universalBSeq m j i ks).length = ks.length := by
  induction ks generalizing i with
  | nil => rfl
  | cons k ks ih => simp [universalBSeq, ih]

@[simp] theorem getElem_universalBSeq (m : ℕ → ℕ) (j i : ℕ)
    (ks : List ℕ) (r : ℕ) (hr : r < (universalBSeq m j i ks).length) :
    (universalBSeq m j i ks)[r] = universalB m (ks.getD r 0) j (i + r) := by
  induction ks generalizing i r with
  | nil => simp [universalBSeq] at hr
  | cons k ks ih =>
      cases r with
      | zero => simp [universalBSeq]
      | succ r =>
          simpa [universalBSeq, Nat.add_assoc, Nat.add_comm 1 r] using
            (ih (i := i + 1) (r := r) (by simpa [universalBSeq] using hr))

@[simp] theorem length_universalBlocks (m : ℕ → ℕ) (s : List ℕ) :
    (universalBlocks m s).length = s.length + 1 := by
  simp [universalBlocks]

theorem universalBSeq_blocks_ne_nil {m : ℕ → ℕ} (hm : StrictMono m)
    (j i : ℕ) (ks : List ℕ) :
    ∀ b ∈ universalBSeq m j i ks, b ≠ [] := by
  intro b hb
  induction ks generalizing i with
  | nil => simp [universalBSeq] at hb
  | cons k ks ih =>
      simp only [universalBSeq, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact universalB_ne_nil hm _ _ _
      · exact ih (i + 1) hb

theorem universalBlocks_ne_nil {m : ℕ → ℕ} (hm : StrictMono m) (s : List ℕ) :
    ∀ b ∈ universalBlocks m s, b ≠ [] := by
  intro b hb
  simp only [universalBlocks, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact universalA_ne_nil hm _
  · exact universalBSeq_blocks_ne_nil hm _ _ _ _ hb

theorem universalBSeq_blocks_pairwise {m : ℕ → ℕ} (hm : StrictMono m)
    (j i : ℕ) (ks : List ℕ) :
    ∀ b ∈ universalBSeq m j i ks, b.Pairwise (· < ·) := by
  intro b hb
  induction ks generalizing i with
  | nil => simp [universalBSeq] at hb
  | cons k ks ih =>
      simp only [universalBSeq, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact universalB_pairwise hm _ _ _
      · exact ih (i + 1) hb

theorem universalBSeq_cross_pairwise {m : ℕ → ℕ} (hm : StrictMono m)
    {j i : ℕ} {ks : List ℕ} (hks : ks.Pairwise (· < ·))
    (hstage : ∀ k ∈ ks, j < k) (hi : i + ks.length ≤ j) :
    (universalBSeq m j i ks).Pairwise
      (fun a b ↦ ∀ x ∈ a, ∀ y ∈ b, x < y) := by
  induction ks generalizing i with
  | nil => simp [universalBSeq]
  | cons k ks ih =>
      rw [List.pairwise_cons] at hks
      simp only [universalBSeq, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb
        have hk : j < k := hstage k (by simp)
        rcases List.mem_iff_getElem.mp hb with ⟨r, hr, rfl⟩
        rw [getElem_universalBSeq]
        have hrks : r < ks.length := by simpa using hr
        rw [List.getD_eq_getElem ks 0 hrks]
        have hkr : k < ks[r] := hks.1 _ (List.getElem_mem hrks)
        have hij : i < j := by
          simp only [List.length_cons] at hi
          omega
        exact universalB_lt_B_stage hm hk hij hkr
      · apply ih hks.2
        · intro r hr
          exact hstage r (by simp [hr])
        · simp at hi ⊢
          omega

theorem universalBlocks_pairwise {m : ℕ → ℕ} (hm : StrictMono m) (s : List ℕ) :
    (universalVertexList m s).Pairwise (· < ·) := by
  rw [universalVertexList, List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [universalBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact universalA_pairwise hm _
    · exact universalBSeq_blocks_pairwise hm _ _ _ b hb
  · rw [universalBlocks, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_iff_getElem.mp hb with ⟨r, hr, rfl⟩
      rw [getElem_universalBSeq]
      simp only [length_universalBSeq, length_intoInc] at hr
      have hrStages : r < (intoInc (s.length + 1) s).length := by
        simpa only [length_intoInc] using hr
      rw [List.getD_eq_getElem (intoInc (s.length + 1) s) 0 hrStages]
      have hkMem : (intoInc (s.length + 1) s)[r]'hrStages ∈
          intoInc (s.length + 1) s := List.getElem_mem hrStages
      have hjk : s.length < (intoInc (s.length + 1) s)[r]'hrStages := by
        have := mem_intoInc_ge hkMem
        omega
      exact universalA_lt_B hm hjk
    · apply universalBSeq_cross_pairwise hm (pairwise_intoInc _ _)
      · intro k hk
        have := mem_intoInc_ge hk
        omega
      · simp

noncomputable def universalVertex (m : ℕ → ℕ) (hm : StrictMono m)
    (s : List ℕ) : IncList :=
  ⟨universalVertexList m s, universalBlocks_pairwise hm s⟩

theorem sum_length_universalBSeq {m : ℕ → ℕ} (hm : StrictMono m)
    (j i : ℕ) (ks : List ℕ) :
    ((universalBSeq m j i ks).map List.length).sum =
      m (universalStageStart m j + i + ks.length) -
        m (universalStageStart m j + i) := by
  induction ks generalizing i with
  | nil => simp [universalBSeq]
  | cons k ks ih =>
      simp only [universalBSeq, List.map_cons, List.sum_cons, length_universalB,
        List.length_cons]
      rw [ih (i + 1)]
      unfold universalDiff
      have h01 : m (universalStageStart m j + i) ≤
          m (universalStageStart m j + i + 1) := (hm (by omega)).le
      have h1n : m (universalStageStart m j + i + 1) ≤
          m (universalStageStart m j + (i + 1) + ks.length) :=
        hm.monotone (by omega)
      have htel := tsub_add_tsub_cancel h1n h01
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htel

@[simp] theorem length_universalVertexList {m : ℕ → ℕ} (hm : StrictMono m)
    (s : List ℕ) :
    (universalVertexList m s).length =
      m (universalStageStart m s.length + s.length) := by
  unfold universalVertexList
  rw [List.length_flatten]
  simp only [universalBlocks, List.map_cons, List.sum_cons, length_universalA]
  rw [sum_length_universalBSeq hm]
  simp only [length_intoInc, Nat.zero_add]
  have hle : m (universalStageStart m s.length) ≤
      m (universalStageStart m s.length + s.length) := hm.monotone (by omega)
  simp only [Nat.add_zero, Nat.zero_add]
  rw [Nat.add_sub_of_le hle]

theorem universalVertex_length_strictMono {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hst : s.length < t.length) :
    (universalVertexList m s).length < (universalVertexList m t).length := by
  rw [length_universalVertexList hm, length_universalVertexList hm]
  apply hm
  have hs := universalStageStart_strictMono m hst
  omega

theorem lex_append_of_forall_lt {a b s t : List ℕ}
    (ha : a ≠ []) (hb : b ≠ [])
    (hab : ∀ x ∈ a, ∀ y ∈ b, x < y) :
    List.Lex (· < ·) (a ++ s) (b ++ t) := by
  cases a with
  | nil => exact (ha rfl).elim
  | cons x xs =>
      cases b with
      | nil => exact (hb rfl).elim
      | cons y ys =>
          exact List.Lex.rel (hab x (by simp) y (by simp))

theorem universalBSeq_flatten_lex {m : ℕ → ℕ} (hm : StrictMono m)
    {j i : ℕ} {ks ls : List ℕ} (hlen : ks.length = ls.length)
    (hks : ks.Pairwise (· < ·))
    (hls : ls.Pairwise (· < ·))
    (hstageK : ∀ k ∈ ks, j < k) (hstageL : ∀ k ∈ ls, j < k)
    (hi : i + ks.length ≤ j) (hlex : List.Lex (· < ·) ks ls) :
    List.Lex (· < ·) (universalBSeq m j i ks).flatten
      (universalBSeq m j i ls).flatten := by
  induction ks generalizing i ls with
  | nil =>
      have hls0 : ls = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ls
      exact (List.lex_irrefl (r := (· < ·)) (by omega) [] hlex).elim
  | cons k ks ih =>
      cases ls with
      | nil => simp at hlen
      | cons l ls =>
          rw [List.pairwise_cons] at hks hls
          have hlenTail : ks.length = ls.length := by simpa using hlen
          simp only [List.cons_lex_cons_iff] at hlex
          rcases hlex with hkl | ⟨rfl, hlex⟩
          · simp only [universalBSeq, List.flatten_cons]
            apply lex_append_of_forall_lt
              (universalB_ne_nil hm k j i) (universalB_ne_nil hm l j i)
            exact universalB_lt_B_stage hm
              (hstageK k (by simp)) (by simp at hi; omega) hkl
          · simp only [universalBSeq, List.flatten_cons]
            apply List.Lex.append_left (R := (· < ·))
            apply ih hlenTail hks.2 hls.2
            · intro r hr
              exact hstageK r (by simp [hr])
            · intro r hr
              exact hstageL r (by simp [hr])
            · simp at hi ⊢
              omega
            · exact hlex

theorem universalVertexList_lex {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length = t.length)
    (hlex : List.Lex (· < ·) s t) :
    List.Lex (· < ·) (universalVertexList m s) (universalVertexList m t) := by
  let ks := intoInc (s.length + 1) s
  let ls := intoInc (s.length + 1) t
  have hksLen : ks.length = s.length := by simp [ks]
  have hlsLen : ls.length = s.length := by simp [ls, hlen]
  have htail : List.Lex (· < ·) (universalBSeq m s.length 0 ks).flatten
      (universalBSeq m s.length 0 ls).flatten := by
    apply universalBSeq_flatten_lex hm (hksLen.trans hlsLen.symm)
      (pairwise_intoInc _ _) (pairwise_intoInc _ _)
    · intro k hk
      have := mem_intoInc_ge hk
      omega
    · intro k hk
      have := mem_intoInc_ge hk
      omega
    · simp [hksLen]
    · exact (lex_intoInc_iff (s.length + 1) s t).2 hlex
  unfold universalVertexList universalBlocks
  simp only [List.flatten_cons]
  rw [show t.length = s.length from hlen.symm]
  exact List.Lex.append_left (R := (· < ·)) htail _

theorem universalVertex_LL {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hst : List.Shortlex (· < ·) s t) :
    LL (universalVertex m hm s) (universalVertex m hm t) := by
  rw [LL_iff]
  rcases List.shortlex_def.mp hst with hlen | ⟨hlen, hlex⟩
  · exact Or.inl (universalVertex_length_strictMono hm hlen)
  · apply Or.inr
    refine ⟨?_, universalVertexList_lex hm hlen hlex⟩
    change (universalVertexList m s).length = (universalVertexList m t).length
    rw [length_universalVertexList hm, length_universalVertexList hm, hlen]

noncomputable def universalVertexEmbedding (m : ℕ → ℕ) (hm : StrictMono m) :
    List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ↪r LL :=
  RelEmbedding.ofMonotone (universalVertex m hm) (fun _ _ h ↦ universalVertex_LL hm h)

def universalSet (m : ℕ → ℕ) (hm : StrictMono m) : Set IncList :=
  Set.range (universalVertex m hm)

noncomputable def universalVertexRangeRelIso (m : ℕ → ℕ) (hm : StrictMono m) :
    List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ≃r
      (fun a b : universalSet m hm ↦ LL a.1 b.1) where
  toEquiv := Equiv.ofInjective (universalVertex m hm)
    (universalVertexEmbedding m hm).injective
  map_rel_iff' := by
    intro a b
    change LL (universalVertex m hm a) (universalVertex m hm b) ↔
      List.Shortlex (· < ·) a b
    exact (universalVertexEmbedding m hm).map_rel_iff

theorem universalSet_type {m : ℕ → ℕ} (hm : StrictMono m) :
    typeLT (universalSet m hm) = ω ^ ω := by
  letI : IsWellOrder (universalSet m hm)
      (fun a b ↦ LL a.1 b.1) := {
    wf := InvImage.wf Subtype.val incListLLIsWellOrder.wf
    trichotomous a b hab hba := by
      rcases LL.trichotomous a.1 b.1 with h | h | h
      · exact (hab h).elim
      · exact Subtype.ext h
      · exact (hba h).elim }
  have htype : Ordinal.type (List.Shortlex ((· < ·) : ℕ → ℕ → Prop)) =
      typeLT (Set.range (universalVertex m hm)) :=
    (universalVertexRangeRelIso m hm).ordinalType_congr
  rw [rawShortlex_type] at htype
  exact htype.symm

/-! ### Merging the atomic schedules

Each atomic block is tagged by its side and by the stage/slot at which its
resource was allocated.  The lexicographic key is only an accounting device;
the separation lemmas above say that key order is exactly data order. -/

structure UniversalAtom where
  side : Bool
  stage : ℕ
  slot : ℕ
  data : List ℕ

def UniversalAtom.KeyLT (a b : UniversalAtom) : Prop :=
  a.stage < b.stage ∨ (a.stage = b.stage ∧ a.slot < b.slot)

def UniversalAtom.KeyLE (a b : UniversalAtom) : Prop :=
  a.stage < b.stage ∨ (a.stage = b.stage ∧ a.slot ≤ b.slot)

noncomputable instance : DecidableRel UniversalAtom.KeyLE := Classical.decRel _

theorem UniversalAtom.keyLT_iff_not_ge (a b : UniversalAtom) :
    a.KeyLT b ↔ ¬ b.KeyLE a := by
  simp only [UniversalAtom.KeyLT, UniversalAtom.KeyLE]
  omega

theorem UniversalAtom.keyLT_trans {a b c : UniversalAtom}
    (hab : a.KeyLT b) (hbc : b.KeyLT c) : a.KeyLT c := by
  simp only [UniversalAtom.KeyLT] at hab hbc ⊢
  omega

theorem UniversalAtom.keyLE_trans {a b c : UniversalAtom}
    (hab : a.KeyLE b) (hbc : b.KeyLE c) : a.KeyLE c := by
  simp only [UniversalAtom.KeyLE] at hab hbc ⊢
  omega

theorem UniversalAtom.keyLE_total (a b : UniversalAtom) : a.KeyLE b ∨ b.KeyLE a := by
  simp only [UniversalAtom.KeyLE]
  omega

noncomputable def universalAAtom (m : ℕ → ℕ) (side : Bool) (j : ℕ) : UniversalAtom :=
  ⟨side, j, 0, universalA m j⟩

noncomputable def universalBAtom (m : ℕ → ℕ) (side : Bool)
    (j i k : ℕ) : UniversalAtom :=
  ⟨side, k, j * k + i + 1, universalB m k j i⟩

noncomputable def universalBAtoms (m : ℕ → ℕ) (side : Bool) (j i : ℕ) :
    List ℕ → List UniversalAtom
  | [] => []
  | k :: ks => universalBAtom m side j i k ::
      universalBAtoms m side j (i + 1) ks

noncomputable def universalAtoms (m : ℕ → ℕ) (side : Bool) (s : List ℕ) :
    List UniversalAtom :=
  universalAAtom m side s.length ::
    universalBAtoms m side s.length 0 (intoInc (s.length + 1) s)

noncomputable def universalMergedAtoms (m : ℕ → ℕ) (s t : List ℕ) :
    List UniversalAtom :=
  List.merge (universalAtoms m false s) (universalAtoms m true t)
    (fun a b ↦ decide (a.KeyLE b))

noncomputable def universalAtomRuns (m : ℕ → ℕ) (s t : List ℕ) :
    List (List UniversalAtom) :=
  (universalMergedAtoms m s t).splitBy
    (fun a b ↦ decide (a.side = b.side))

def universalRunSide (r : List UniversalAtom) : Bool :=
  (r.head?).map (fun a ↦ a.side) |>.getD false

def universalRunData (r : List UniversalAtom) : List ℕ :=
  (r.map UniversalAtom.data).flatten

def universalSideBlocks (side : Bool) (rs : List (List UniversalAtom)) :
    List (List ℕ) :=
  (rs.filter (fun r ↦ universalRunSide r == side)).map universalRunData

noncomputable def universalLeftBlocks (m : ℕ → ℕ) (s t : List ℕ) : List (List ℕ) :=
  universalSideBlocks false (universalAtomRuns m s t)

noncomputable def universalRightBlocks (m : ℕ → ℕ) (s t : List ℕ) : List (List ℕ) :=
  universalSideBlocks true (universalAtomRuns m s t)

@[simp] theorem length_universalBAtoms (m : ℕ → ℕ) (side : Bool)
    (j i : ℕ) (ks : List ℕ) :
    (universalBAtoms m side j i ks).length = ks.length := by
  induction ks generalizing i with
  | nil => rfl
  | cons k ks ih => simp [universalBAtoms, ih]

@[simp] theorem length_universalAtoms (m : ℕ → ℕ) (side : Bool)
    (s : List ℕ) : (universalAtoms m side s).length = s.length + 1 := by
  simp [universalAtoms]

@[simp] theorem getElem_universalBAtoms (m : ℕ → ℕ) (side : Bool)
    (j i : ℕ) (ks : List ℕ) (r : ℕ)
    (hr : r < (universalBAtoms m side j i ks).length) :
    (universalBAtoms m side j i ks)[r] =
      universalBAtom m side j (i + r) (ks.getD r 0) := by
  induction ks generalizing i r with
  | nil => simp [universalBAtoms] at hr
  | cons k ks ih =>
      cases r with
      | zero => simp [universalBAtoms]
      | succ r =>
          simpa [universalBAtoms, Nat.add_assoc, Nat.add_comm 1 r] using
            (ih (i := i + 1) (r := r) (by simpa [universalBAtoms] using hr))

theorem universalBAtoms_stage_mem {m : ℕ → ℕ} {side : Bool}
    {j i : ℕ} {ks : List ℕ} {a : UniversalAtom}
    (ha : a ∈ universalBAtoms m side j i ks) : a.stage ∈ ks := by
  induction ks generalizing i with
  | nil => simp [universalBAtoms] at ha
  | cons k ks ih =>
      simp only [universalBAtoms, List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [universalBAtom]
      · exact List.mem_cons_of_mem _ (ih (i := i + 1) ha)

theorem universalBAtoms_side {m : ℕ → ℕ} {side : Bool}
    {j i : ℕ} {ks : List ℕ} {a : UniversalAtom}
    (ha : a ∈ universalBAtoms m side j i ks) : a.side = side := by
  induction ks generalizing i with
  | nil => simp [universalBAtoms] at ha
  | cons k ks ih =>
      simp only [universalBAtoms, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact ih (i := i + 1) ha

theorem universalAtoms_side {m : ℕ → ℕ} {side : Bool}
    {s : List ℕ} {a : UniversalAtom} (ha : a ∈ universalAtoms m side s) :
    a.side = side := by
  simp only [universalAtoms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  · exact universalBAtoms_side ha

theorem map_data_universalBAtoms (m : ℕ → ℕ) (side : Bool)
    (j i : ℕ) (ks : List ℕ) :
    (universalBAtoms m side j i ks).map UniversalAtom.data =
      universalBSeq m j i ks := by
  induction ks generalizing i with
  | nil => rfl
  | cons k ks ih => simp [universalBAtoms, universalBAtom, universalBSeq, ih]

theorem map_data_universalAtoms (m : ℕ → ℕ) (side : Bool)
    (s : List ℕ) :
    (universalAtoms m side s).map UniversalAtom.data = universalBlocks m s := by
  simp [universalAtoms, universalAAtom, universalBlocks, map_data_universalBAtoms]

theorem universalBAtoms_key_pairwise (m : ℕ → ℕ) (side : Bool)
    (j i : ℕ) {ks : List ℕ} (hks : ks.Pairwise (· < ·)) :
    (universalBAtoms m side j i ks).Pairwise UniversalAtom.KeyLT := by
  induction ks generalizing i with
  | nil => simp [universalBAtoms]
  | cons k ks ih =>
      rw [List.pairwise_cons] at hks
      simp only [universalBAtoms, List.pairwise_cons]
      refine ⟨?_, ih (i := i + 1) hks.2⟩
      intro a ha
      have hstage : a.stage ∈ ks := universalBAtoms_stage_mem ha
      have hka : k < a.stage := hks.1 _ hstage
      exact Or.inl hka

theorem universalAtoms_key_pairwise (m : ℕ → ℕ) (side : Bool)
    (s : List ℕ) :
    (universalAtoms m side s).Pairwise UniversalAtom.KeyLT := by
  rw [universalAtoms, List.pairwise_cons]
  refine ⟨?_, universalBAtoms_key_pairwise m side s.length 0
    (pairwise_intoInc _ _)⟩
  intro a ha
  have hstageMem := universalBAtoms_stage_mem ha
  have hstage : s.length < a.stage := by
    have := mem_intoInc_ge hstageMem
    omega
  exact Or.inl hstage

theorem universalAtoms_data (m : ℕ → ℕ) (side : Bool) (s : List ℕ) :
    ((universalAtoms m side s).map UniversalAtom.data).flatten =
      universalVertexList m s := by
  rw [map_data_universalAtoms]
  rfl

theorem mem_universalBAtoms_iff {m : ℕ → ℕ} {side : Bool}
    {j i : ℕ} {ks : List ℕ} {a : UniversalAtom} :
    a ∈ universalBAtoms m side j i ks ↔
      ∃ r, ∃ hr : r < ks.length,
        a = universalBAtom m side j (i + r) ks[r] := by
  constructor
  · intro ha
    rcases List.mem_iff_getElem.mp ha with ⟨r, hr, rfl⟩
    have hr' : r < ks.length := by simpa using hr
    refine ⟨r, hr', ?_⟩
    rw [getElem_universalBAtoms]
    rw [List.getD_eq_getElem ks 0 hr']
  · rintro ⟨r, hr, rfl⟩
    apply List.mem_iff_getElem.mpr
    refine ⟨r, by simpa, ?_⟩
    rw [getElem_universalBAtoms]
    rw [List.getD_eq_getElem ks 0 hr]

theorem nat_mul_add_injective_of_lt {a b k i j : ℕ}
    (hi : i < k) (hj : j < k) (h : a * k + i = b * k + j) :
    a = b ∧ i = j := by
  have hk : 0 < k := by omega
  have hdiv := congrArg (fun n ↦ n / k) h
  have hmod := congrArg (fun n ↦ n % k) h
  rw [Nat.mul_comm a k, Nat.mul_comm b k,
    Nat.mul_add_div hk, Nat.mul_add_div hk,
    Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] at hdiv
  rw [Nat.mul_comm a k, Nat.mul_comm b k,
    Nat.mul_add_mod, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact ⟨by omega, hmod⟩

theorem universalAtoms_cross_key_ne (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length)
    {a b : UniversalAtom} (ha : a ∈ universalAtoms m false s)
    (hb : b ∈ universalAtoms m true t) :
    a.stage ≠ b.stage ∨ a.slot ≠ b.slot := by
  simp only [universalAtoms, List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact Or.inl (by simp [universalAAtom]; omega)
  · rcases mem_universalBAtoms_iff.mp hb with ⟨v, hv, rfl⟩
    apply Or.inl
    simp only [universalAAtom, universalBAtom]
    have hmem : (intoInc (t.length + 1) t)[v] ∈ intoInc (t.length + 1) t :=
      List.getElem_mem (by simpa using hv)
    have hge := mem_intoInc_ge hmem
    omega
  · rcases mem_universalBAtoms_iff.mp ha with ⟨u, hu, rfl⟩
    simp only [universalBAtom, universalAAtom]
    by_cases hstage : (intoInc (s.length + 1) s)[u] = t.length
    · exact Or.inr (by omega)
    · exact Or.inl hstage
  · rcases mem_universalBAtoms_iff.mp ha with ⟨u, hu, rfl⟩
    rcases mem_universalBAtoms_iff.mp hb with ⟨v, hv, rfl⟩
    simp only [universalBAtom]
    by_cases hstage : (intoInc (s.length + 1) s)[u] =
        (intoInc (t.length + 1) t)[v]
    · right
      intro hslot
      rw [← hstage] at hslot
      have hu' : u < s.length := by simpa using hu
      have hv' : v < t.length := by simpa using hv
      have hmem : (intoInc (s.length + 1) s)[u] ∈
          intoInc (s.length + 1) s := List.getElem_mem (by simpa using hu)
      have hkge := mem_intoInc_ge hmem
      have hinj := nat_mul_add_injective_of_lt
        (show u < (intoInc (s.length + 1) s)[u] by omega)
        (show v < (intoInc (s.length + 1) s)[u] by
          have hmem' : (intoInc (t.length + 1) t)[v] ∈
              intoInc (t.length + 1) t := List.getElem_mem (by simpa using hv)
          have := mem_intoInc_ge hmem'
          omega)
        (show s.length * (intoInc (s.length + 1) s)[u] + u =
            t.length * (intoInc (s.length + 1) s)[u] + v by omega)
      omega
    · exact Or.inl hstage

theorem universalAtoms_key_nodup (m : ℕ → ℕ) (side : Bool)
    (s : List ℕ) :
    ((universalAtoms m side s).map (fun a ↦ (a.stage, a.slot))).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (universalAtoms_key_pairwise m side s).imp (by
    intro a b hab hkey
    have hstage := congrArg Prod.fst hkey
    have hslot := congrArg Prod.snd hkey
    simp only [UniversalAtom.KeyLT] at hab
    omega)

theorem universalAtoms_cross_key_disjoint (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    List.Disjoint
      ((universalAtoms m false s).map (fun a ↦ (a.stage, a.slot)))
      ((universalAtoms m true t).map (fun a ↦ (a.stage, a.slot))) := by
  rw [List.disjoint_left]
  intro key hleft hright
  rcases List.mem_map.mp hleft with ⟨a, ha, rfl⟩
  rcases List.mem_map.mp hright with ⟨b, hb, hkey⟩
  have hne := universalAtoms_cross_key_ne m hlen ha hb
  have hstage := congrArg Prod.fst hkey
  have hslot := congrArg Prod.snd hkey
  rcases hne with hne | hne
  · exact hne hstage.symm
  · exact hne hslot.symm

theorem UniversalAtom.keyLT_imp_keyLE {a b : UniversalAtom}
    (h : a.KeyLT b) : a.KeyLE b := by
  simp only [UniversalAtom.KeyLT] at h
  simp only [UniversalAtom.KeyLE]
  omega

theorem universalMergedAtoms_key_nodup (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    ((universalMergedAtoms m s t).map (fun a ↦ (a.stage, a.slot))).Nodup := by
  have happ :
      ((universalAtoms m false s).map (fun a ↦ (a.stage, a.slot)) ++
        (universalAtoms m true t).map (fun a ↦ (a.stage, a.slot))).Nodup :=
    List.nodup_append.mpr ⟨universalAtoms_key_nodup m false s,
      universalAtoms_key_nodup m true t, by
        have hdis := universalAtoms_cross_key_disjoint m hlen
        rw [List.disjoint_left] at hdis
        intro a ha b hb hab
        exact hdis ha (hab ▸ hb)⟩
  have hp := (List.merge_perm_append
    (fun a b : UniversalAtom ↦ decide (a.KeyLE b))
    (xs := universalAtoms m false s) (ys := universalAtoms m true t)).map
      (fun a ↦ (a.stage, a.slot))
  apply hp.nodup_iff.mpr
  simpa [List.map_append] using happ

theorem universalMergedAtoms_keyLE_pairwise (m : ℕ → ℕ)
    (s t : List ℕ) :
    (universalMergedAtoms m s t).Pairwise UniversalAtom.KeyLE := by
  unfold universalMergedAtoms
  have hmerge := List.pairwise_merge
    (le := fun a b : UniversalAtom ↦ decide (a.KeyLE b))
    (fun a b c hab hbc ↦ by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact UniversalAtom.keyLE_trans hab hbc)
    (fun a b ↦ by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact UniversalAtom.keyLE_total a b)
    (universalAtoms m false s) (universalAtoms m true t)
    ((universalAtoms_key_pairwise m false s).imp (by
      intro a b h
      simpa only [decide_eq_true_eq] using UniversalAtom.keyLT_imp_keyLE h))
    ((universalAtoms_key_pairwise m true t).imp (by
      intro a b h
      simpa only [decide_eq_true_eq] using UniversalAtom.keyLT_imp_keyLE h))
  simpa only [decide_eq_true_eq] using hmerge

theorem universalMergedAtoms_key_pairwise (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalMergedAtoms m s t).Pairwise UniversalAtom.KeyLT := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hle := (List.pairwise_iff_getElem.mp
    (universalMergedAtoms_keyLE_pairwise m s t)) i j hi hj hij
  have hn := universalMergedAtoms_key_nodup m hlen
  have hkeyne :
      ((universalMergedAtoms m s t)[i].stage,
        (universalMergedAtoms m s t)[i].slot) ≠
      ((universalMergedAtoms m s t)[j].stage,
        (universalMergedAtoms m s t)[j].slot) := by
    intro heq
    have himap : i < ((universalMergedAtoms m s t).map
        (fun a ↦ (a.stage, a.slot))).length := by simpa
    have hjmap : j < ((universalMergedAtoms m s t).map
        (fun a ↦ (a.stage, a.slot))).length := by simpa
    have hij' := (hn.getElem_inj_iff (i := i) (j := j)
      (hi := himap) (hj := hjmap)).mp (by simpa using heq)
    omega
  simp only [UniversalAtom.KeyLE] at hle
  simp only [UniversalAtom.KeyLT]
  by_contra hnot
  push_neg at hnot
  apply hkeyne
  apply Prod.ext <;> simp only
  · omega
  · omega

@[simp] theorem universalMergedAtoms_head (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalMergedAtoms m s t).head? =
      some (universalAAtom m false s.length) := by
  simp [universalMergedAtoms, universalAtoms, List.cons_merge_cons,
    UniversalAtom.KeyLE, universalAAtom, hlen]

theorem universalMergedAtoms_ne_nil (m : ℕ → ℕ) (s t : List ℕ) :
    universalMergedAtoms m s t ≠ [] := by
  intro h
  have hp := List.merge_perm_append
    (fun a b : UniversalAtom ↦ decide (a.KeyLE b))
    (xs := universalAtoms m false s) (ys := universalAtoms m true t)
  have : universalAAtom m false s.length ∈ universalMergedAtoms m s t :=
    List.mem_merge_left _ (by simp [universalAtoms])
  simpa [h] using this

theorem universalRun_side {m : ℕ → ℕ} {s t : List ℕ}
    {r : List UniversalAtom} (hr : r ∈ universalAtomRuns m s t) :
    ∀ a ∈ r, a.side = universalRunSide r := by
  have hne : r ≠ [] := List.ne_nil_of_mem_splitBy hr
  have hc := List.isChain_of_mem_splitBy hr
  have hc' : r.IsChain (fun a b : UniversalAtom ↦ a.side = b.side) :=
    hc.imp (by
      intro a b h
      simpa only [decide_eq_true_eq] using h)
  apply hc'.induction (fun a ↦ a.side = universalRunSide r) r
  · intro a b hab ha
    exact hab.symm ▸ ha
  · intro hrne
    have hh : r.head? = some (r.head hrne) := List.head?_eq_some_head hrne
    simp [universalRunSide, hh]

theorem universalRunSide_head {r : List UniversalAtom} (hr : r ≠ []) :
    universalRunSide r = (r.head hr).side := by
  have hh : r.head? = some (r.head hr) := List.head?_eq_some_head hr
  simp [universalRunSide, hh]

theorem universalAtomRuns_headSide (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    universalRunSide ((universalAtomRuns m s t).head
      ((List.splitBy_ne_nil).2 (universalMergedAtoms_ne_nil m s t))) = false := by
  unfold universalAtomRuns
  let hn : universalMergedAtoms m s t ≠ [] := universalMergedAtoms_ne_nil m s t
  have hrne :
      (universalMergedAtoms m s t).splitBy
        (fun a b : UniversalAtom ↦ decide (a.side = b.side)) ≠ [] :=
    (List.splitBy_ne_nil).2 hn
  have hh := List.head_head_splitBy
    (fun a b : UniversalAtom ↦ decide (a.side = b.side)) hn
  have hm : (universalMergedAtoms m s t).head hn =
      universalAAtom m false s.length := by
    have hopt := universalMergedAtoms_head m hlen
    rw [List.head?_eq_some_head hn] at hopt
    exact Option.some.inj hopt
  rw [universalRunSide_head (List.ne_nil_of_mem_splitBy
    (List.head_mem hrne)), hh, hm]
  rfl

theorem universalMergedAtoms_filter_false (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalMergedAtoms m s t).filter (fun a ↦ a.side == false) =
      universalAtoms m false s := by
  have hp := (List.merge_perm_append
    (fun a b : UniversalAtom ↦ decide (a.KeyLE b))
    (xs := universalAtoms m false s) (ys := universalAtoms m true t)).filter
      (fun a ↦ a.side == false)
  have hleft : (universalAtoms m false s).filter (fun a ↦ a.side == false) =
      universalAtoms m false s := List.filter_eq_self.2 (by
    intro a ha
    simp [universalAtoms_side ha])
  have hright : (universalAtoms m true t).filter (fun a ↦ a.side == false) = [] :=
    List.filter_eq_nil_iff.2 (by
      intro a ha
      simp [universalAtoms_side ha])
  simp only [List.filter_append, hleft, hright, List.append_nil] at hp
  apply hp.eq_of_pairwise
  · intro a b ha hb hab hba
    exact False.elim ((UniversalAtom.keyLT_iff_not_ge a b).1 hab
      (UniversalAtom.keyLT_imp_keyLE hba))
  · exact (universalMergedAtoms_key_pairwise m hlen).filter _
  · exact universalAtoms_key_pairwise m false s

theorem universalMergedAtoms_filter_true (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalMergedAtoms m s t).filter (fun a ↦ a.side == true) =
      universalAtoms m true t := by
  have hp := (List.merge_perm_append
    (fun a b : UniversalAtom ↦ decide (a.KeyLE b))
    (xs := universalAtoms m false s) (ys := universalAtoms m true t)).filter
      (fun a ↦ a.side == true)
  have hleft : (universalAtoms m false s).filter (fun a ↦ a.side == true) = [] :=
    List.filter_eq_nil_iff.2 (by
      intro a ha
      simp [universalAtoms_side ha])
  have hright : (universalAtoms m true t).filter (fun a ↦ a.side == true) =
      universalAtoms m true t := List.filter_eq_self.2 (by
    intro a ha
    simp [universalAtoms_side ha])
  simp only [List.filter_append, hleft, hright, List.nil_append] at hp
  apply hp.eq_of_pairwise
  · intro a b ha hb hab hba
    exact False.elim ((UniversalAtom.keyLT_iff_not_ge a b).1 hab
      (UniversalAtom.keyLT_imp_keyLE hba))
  · exact (universalMergedAtoms_key_pairwise m hlen).filter _
  · exact universalAtoms_key_pairwise m true t

theorem universalRun_filter_side {m : ℕ → ℕ} {s t : List ℕ}
    {r : List UniversalAtom} (hr : r ∈ universalAtomRuns m s t) (side : Bool) :
    r.filter (fun a ↦ a.side == side) =
      if universalRunSide r == side then r else [] := by
  have hall := universalRun_side hr
  cases hs : universalRunSide r <;> cases side
  · change r.filter (fun a ↦ a.side == false) = r
    apply List.filter_eq_self.2
    intro a ha
    simpa [hs] using hall a ha
  · change r.filter (fun a ↦ a.side == true) = []
    apply List.filter_eq_nil_iff.2
    intro a ha
    simpa [hs] using hall a ha
  · change r.filter (fun a ↦ a.side == false) = []
    apply List.filter_eq_nil_iff.2
    intro a ha
    simpa [hs] using hall a ha
  · change r.filter (fun a ↦ a.side == true) = r
    apply List.filter_eq_self.2
    intro a ha
    simpa [hs] using hall a ha

theorem universalAtomRuns_filter_flatten (m : ℕ → ℕ) (s t : List ℕ)
    (side : Bool) :
    ((universalAtomRuns m s t).filter
        (fun r ↦ universalRunSide r == side)).flatten =
      (universalMergedAtoms m s t).filter (fun a ↦ a.side == side) := by
  let rs := universalAtomRuns m s t
  have hflat : rs.flatten = universalMergedAtoms m s t := by
    exact List.flatten_splitBy _ _
  rw [← hflat, List.filter_flatten]
  change (rs.filter (fun r ↦ universalRunSide r == side)).flatten =
    (rs.map fun r ↦ r.filter (fun a ↦ a.side == side)).flatten
  have hsub : ∀ r ∈ rs, r ∈ universalAtomRuns m s t := by
    intro r hr
    simpa [rs] using hr
  revert hsub
  induction rs with
  | nil => intro; rfl
  | cons r rs ih =>
      intro hsub
      have hr : r ∈ universalAtomRuns m s t :=
        hsub r List.mem_cons_self
      have hrs : ∀ q ∈ rs, q ∈ universalAtomRuns m s t := by
        intro q hq
        exact hsub q (List.mem_cons_of_mem r hq)
      simp only [List.filter_cons, List.map_cons, List.flatten_cons]
      rw [universalRun_filter_side hr side]
      split <;> rename_i hside
      · exact congrArg (r ++ ·) (ih hrs)
      · exact ih hrs

theorem map_runData_flatten (rs : List (List UniversalAtom)) :
    (rs.map universalRunData).flatten =
      (rs.flatten.map UniversalAtom.data).flatten := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [List.map_cons, List.flatten_cons, universalRunData,
        List.map_append, List.flatten_append, ih]

theorem universalSideBlocks_flatten (m : ℕ → ℕ) (s t : List ℕ)
    (side : Bool) :
    (universalSideBlocks side (universalAtomRuns m s t)).flatten =
      (((universalMergedAtoms m s t).filter (fun a ↦ a.side == side)).map
        UniversalAtom.data).flatten := by
  unfold universalSideBlocks
  rw [map_runData_flatten, universalAtomRuns_filter_flatten]

theorem universalLeftBlocks_flatten (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalLeftBlocks m s t).flatten = universalVertexList m s := by
  unfold universalLeftBlocks universalVertexList
  rw [universalSideBlocks_flatten, universalMergedAtoms_filter_false m hlen,
    map_data_universalAtoms]

theorem universalRightBlocks_flatten (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalRightBlocks m s t).flatten = universalVertexList m t := by
  unfold universalRightBlocks universalVertexList
  rw [universalSideBlocks_flatten, universalMergedAtoms_filter_true m hlen,
    map_data_universalAtoms]

theorem universalAtomRuns_sides_chain (m : ℕ → ℕ) (s t : List ℕ) :
    ((universalAtomRuns m s t).map universalRunSide).IsChain (· ≠ ·) := by
  have hc := List.isChain_getLast_head_splitBy
    (fun a b : UniversalAtom ↦ decide (a.side = b.side))
    (universalMergedAtoms m s t)
  apply (List.isChain_map universalRunSide).2
  apply hc.imp_of_mem_imp
  intro a b ha hb hab
  rcases hab with ⟨hneA, hneB, hab⟩
  have hlast := universalRun_side ha (a.getLast hneA) (List.getLast_mem hneA)
  have hhead := universalRun_side hb (b.head hneB) (List.head_mem hneB)
  intro hsides
  have heq : (a.getLast hneA).side = (b.head hneB).side :=
    hlast.trans (hsides.trans hhead.symm)
  simp only [decide_eq_false_iff_not] at hab
  exact hab heq

theorem bool_chain_filter_lengths (ss : List Bool) (hc : ss.IsChain (· ≠ ·)) :
    (ss.head? = some false →
      (ss.filter (· == true)).length ≤ (ss.filter (· == false)).length ∧
      (ss.filter (· == false)).length ≤ (ss.filter (· == true)).length + 1) ∧
    (ss.head? = some true →
      (ss.filter (· == false)).length ≤ (ss.filter (· == true)).length ∧
      (ss.filter (· == true)).length ≤ (ss.filter (· == false)).length + 1) := by
  induction ss with
  | nil => simp
  | cons b ss ih =>
      cases ss with
      | nil => cases b <;> simp
      | cons c ss =>
          simp only [List.isChain_cons_cons] at hc
          have hi := ih hc.2
          cases b <;> cases c <;> simp_all

theorem universalBlocks_count_bounds {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) :
    0 < (universalRightBlocks m s t).length ∧
      (universalRightBlocks m s t).length ≤
        (universalLeftBlocks m s t).length ∧
      (universalLeftBlocks m s t).length ≤
        (universalRightBlocks m s t).length + 1 := by
  let rs := universalAtomRuns m s t
  have hrne : rs ≠ [] := by
    dsimp [rs]
    exact (List.splitBy_ne_nil).2 (universalMergedAtoms_ne_nil m s t)
  have hhead : (rs.map universalRunSide).head? = some false := by
    rw [List.head?_map, List.head?_eq_some_head hrne]
    simp only [Option.map_some]
    exact congrArg some (universalAtomRuns_headSide m hlen)
  have hb := (bool_chain_filter_lengths (rs.map universalRunSide)
    (universalAtomRuns_sides_chain m s t)).1 hhead
  have hlenFalse :
      ((rs.map universalRunSide).filter (· == false)).length =
        (universalLeftBlocks m s t).length := by
    dsimp [universalLeftBlocks, universalSideBlocks, rs]
    simp only [List.filter_map, List.length_map]
    change (List.filter (fun r ↦ universalRunSide r == false)
      (universalAtomRuns m s t)).length = _
    rfl
  have hlenTrue :
      ((rs.map universalRunSide).filter (· == true)).length =
        (universalRightBlocks m s t).length := by
    dsimp [universalRightBlocks, universalSideBlocks, rs]
    simp only [List.filter_map, List.length_map]
    change (List.filter (fun r ↦ universalRunSide r == true)
      (universalAtomRuns m s t)).length = _
    rfl
  rw [hlenFalse, hlenTrue] at hb
  refine ⟨Nat.pos_of_ne_zero ?_, hb⟩
  intro hzero
  have hflat := universalRightBlocks_flatten m hlen
  have hvnil : universalVertexList m t = [] := by
    rw [← hflat]
    have hbNil : universalRightBlocks m s t = [] :=
      List.length_eq_zero_iff.mp hzero
    simp [hbNil]
  have hvne : universalVertexList m t ≠ [] := by
    unfold universalVertexList universalBlocks
    simp only [List.flatten_cons]
    exact List.append_ne_nil_of_left_ne_nil (universalA_ne_nil hm _) _
  exact hvne hvnil

theorem universalA_lt_A {m : ℕ → ℕ} (hm : StrictMono m)
    {j k : ℕ} (hjk : j < k) :
    ∀ x ∈ universalA m j, ∀ y ∈ universalA m k, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hnext := universalBlockBase_lt_nextStage m j
  have hstage : universalStageStart m (j + 1) ≤ universalStageStart m k :=
    (universalStageStart_strictMono m).monotone (by omega)
  unfold universalBlockBase at hnext
  omega

theorem universalA_lt_B_of_le {m : ℕ → ℕ} (hm : StrictMono m)
    {j k r i : ℕ} (hjk : j ≤ k) :
    ∀ x ∈ universalA m j, ∀ y ∈ universalB m k r i, x < y := by
  rcases hjk.eq_or_lt with rfl | hjk
  · apply enumSlice_lt_enumSlice m hm
    have hblock : universalBlockBase m j ≤
        blockStart (universalBlockBase m j) (universalSlotSize m j) (r * j + i) :=
      blockStart_mono _ _ (Nat.zero_le _)
    exact hblock
  · exact universalA_lt_B hm hjk

theorem universalB_lt_A {m : ℕ → ℕ} (hm : StrictMono m)
    {k r j i : ℕ} (hjk : j < k) (hij : i < j) (hkr : k < r) :
    ∀ x ∈ universalB m k j i, ∀ y ∈ universalA m r, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hend := universalB_end_le_stageEnd m hjk hij
  have hnext :
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) <
        universalStageStart m (k + 1) := by
    rw [universalStageStart_succ]
    omega
  have hstage : universalStageStart m (k + 1) ≤ universalStageStart m r :=
    (universalStageStart_strictMono m).monotone (by omega)
  omega

theorem universalAtoms_cases {m : ℕ → ℕ} {side : Bool}
    {s : List ℕ} {a : UniversalAtom} (ha : a ∈ universalAtoms m side s) :
    a = universalAAtom m side s.length ∨
      ∃ i, ∃ hi : i < s.length,
        a = universalBAtom m side s.length i
          ((intoInc (s.length + 1) s).getD i 0) := by
  simp only [universalAtoms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact Or.inl rfl
  · right
    rcases mem_universalBAtoms_iff.mp ha with ⟨i, hi, rfl⟩
    have hi' : i < s.length := by simpa only [length_intoInc] using hi
    refine ⟨i, hi', ?_⟩
    rw [List.getD_eq_getElem _ 0 (by simpa only [length_intoInc])]
    simp only [Nat.zero_add]

theorem universalAtom_data_pairwise {m : ℕ → ℕ} (hm : StrictMono m)
    {side : Bool} {s : List ℕ} {a : UniversalAtom}
    (ha : a ∈ universalAtoms m side s) : a.data.Pairwise (· < ·) := by
  rcases universalAtoms_cases ha with rfl | ⟨i, hi, rfl⟩
  · exact universalA_pairwise hm _
  · exact universalB_pairwise hm _ _ _

theorem universalAtom_data_lt {m : ℕ → ℕ} (hm : StrictMono m)
    {side side' : Bool} {s t : List ℕ} {a b : UniversalAtom}
    (ha : a ∈ universalAtoms m side s) (hb : b ∈ universalAtoms m side' t)
    (hab : a.KeyLT b) :
    ∀ x ∈ a.data, ∀ y ∈ b.data, x < y := by
  rcases universalAtoms_cases ha with rfl | ⟨i, hi, rfl⟩ <;>
    rcases universalAtoms_cases hb with rfl | ⟨i', hi', rfl⟩
  · simp only [UniversalAtom.KeyLT, universalAAtom] at hab
    exact universalA_lt_A hm (by omega)
  · simp only [UniversalAtom.KeyLT, universalAAtom, universalBAtom] at hab
    apply universalA_lt_B_of_le hm
    omega
  · simp only [UniversalAtom.KeyLT, universalBAtom, universalAAtom] at hab
    have hiInc : i < (intoInc (s.length + 1) s).length := by simpa
    rw [List.getD_eq_getElem _ 0 hiInc] at hab ⊢
    have hstage :
        (intoInc (s.length + 1) s)[i] < t.length := by omega
    have hmem : (intoInc (s.length + 1) s)[i] ∈
        intoInc (s.length + 1) s := List.getElem_mem (by simpa)
    have hbase : s.length < (intoInc (s.length + 1) s)[i] := by
      have := mem_intoInc_ge hmem
      omega
    exact universalB_lt_A hm hbase hi hstage
  · simp only [UniversalAtom.KeyLT, universalBAtom] at hab
    have hiInc : i < (intoInc (s.length + 1) s).length := by simpa
    have hiInc' : i' < (intoInc (t.length + 1) t).length := by simpa
    rw [List.getD_eq_getElem _ 0 hiInc, List.getD_eq_getElem _ 0 hiInc'] at hab ⊢
    have hmem : (intoInc (s.length + 1) s)[i] ∈
        intoInc (s.length + 1) s := List.getElem_mem (by simpa)
    have hmem' : (intoInc (t.length + 1) t)[i'] ∈
        intoInc (t.length + 1) t := List.getElem_mem (by simpa)
    have hbase : s.length < (intoInc (s.length + 1) s)[i] := by
      have := mem_intoInc_ge hmem
      omega
    have hbase' : t.length < (intoInc (t.length + 1) t)[i'] := by
      have := mem_intoInc_ge hmem'
      omega
    rcases hab with hstage | ⟨hstage, hslot⟩
    · exact universalB_lt_B_stage hm hbase hi hstage
    · rw [← hstage] at hbase' hslot ⊢
      exact universalB_lt_B_sameStage hm hbase hi hbase' hi' (by omega)

theorem universalMergedAtoms_data_pairwise {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) :
    ((universalMergedAtoms m s t).map UniversalAtom.data).flatten.Pairwise
      (· < ·) := by
  rw [List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro d hd
    rcases List.mem_map.mp hd with ⟨a, ha, rfl⟩
    rw [universalMergedAtoms, List.mem_merge] at ha
    rcases ha with ha | ha
    · exact universalAtom_data_pairwise hm ha
    · exact universalAtom_data_pairwise hm ha
  · rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ (universalMergedAtoms_key_pairwise m hlen)
    intro a b ha hb hab
    rw [universalMergedAtoms, List.mem_merge] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact universalAtom_data_lt hm ha hb hab
    · exact universalAtom_data_lt hm ha hb hab
    · exact universalAtom_data_lt hm ha hb hab
    · exact universalAtom_data_lt hm ha hb hab

theorem enumSlice_succ (f : ℕ → ℕ) (start len : ℕ) :
    enumSlice f start (len + 1) =
      f start :: enumSlice f (start + 1) len := by
  simp [enumSlice, List.range_succ_eq_map, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem accLengths_universalBSeq {m : ℕ → ℕ} (hm : StrictMono m)
    (j i : ℕ) (ks : List ℕ) :
    accLengths (m (universalStageStart m j + i))
        (universalBSeq m j i ks) =
      enumSlice m (universalStageStart m j + i + 1) ks.length := by
  induction ks generalizing i with
  | nil => rfl
  | cons k ks ih =>
      simp only [universalBSeq, accLengths, length_universalB,
        List.length_cons]
      have hmono : m (universalStageStart m j + i) ≤
          m (universalStageStart m j + i + 1) := hm.monotone (by omega)
      have hfirst : m (universalStageStart m j + i) + universalDiff m j i =
          m (universalStageStart m j + i + 1) := by
        unfold universalDiff
        omega
      have htail :
          accLengths (m (universalStageStart m j + i + 1))
              (universalBSeq m j (i + 1) ks) =
            enumSlice m (universalStageStart m j + i + 2) ks.length := by
        have hiEq : universalStageStart m j + (i + 1) =
            universalStageStart m j + i + 1 := by omega
        have hiEq' : universalStageStart m j + (i + 1) + 1 =
            universalStageStart m j + i + 2 := by omega
        simpa only [hiEq, hiEq'] using ih (i + 1)
      rw [hfirst, htail, enumSlice_succ]

theorem accLengths_universalBlocks {m : ℕ → ℕ} (hm : StrictMono m)
    (s : List ℕ) :
    accLengths 0 (universalBlocks m s) = universalD m s.length := by
  unfold universalBlocks universalD
  simp only [accLengths, length_universalA, Nat.zero_add]
  have htail := accLengths_universalBSeq hm s.length 0
    (intoInc (s.length + 1) s)
  simp only [Nat.add_zero, length_intoInc] at htail
  rw [htail]
  rw [enumSlice_succ]

theorem length_universalRunData (r : List UniversalAtom) :
    (universalRunData r).length = (r.map (fun a ↦ a.data.length)).sum := by
  simp [universalRunData, List.length_flatten, Function.comp_def]

theorem accLengths_grouped_subset (n : ℕ)
    (gs : List (List UniversalAtom))
    (hne : ∀ g ∈ gs, g ≠ []) :
    ∀ z ∈ accLengths n (gs.map universalRunData),
      z ∈ accLengths n (gs.flatten.map UniversalAtom.data) := by
  induction gs generalizing n with
  | nil => simp [accLengths]
  | cons g gs ih =>
      intro z hz
      have hg : g ≠ [] := hne g (by simp)
      have hgs : ∀ q ∈ gs, q ≠ [] := by
        intro q hq
        exact hne q (by simp [hq])
      simp only [List.map_cons, accLengths, List.mem_cons] at hz
      simp only [List.flatten_cons, List.map_append, accLengths_append,
        List.mem_append]
      rcases hz with rfl | hz
      · left
        cases g with
        | nil => exact (hg rfl).elim
        | cons a as =>
            have hlast := List.getLast_mem
              (l := accLengths n ((a :: as).map UniversalAtom.data))
              (by simp [accLengths])
            rw [show (accLengths n ((a :: as).map UniversalAtom.data)).getLast
                (by simp [accLengths]) =
                n + (((a :: as).map UniversalAtom.data).map List.length).sum by
              simpa using getLast_accLengths_cons n a.data
                (as.map UniversalAtom.data)] at hlast
            simpa [length_universalRunData, universalRunData,
              List.length_flatten, Function.comp_def] using hlast
      · right
        have hz' := ih (n + (g.map (fun a ↦ a.data.length)).sum) hgs z
          (by
            simpa [length_universalRunData] using hz)
        simpa [List.length_flatten, Function.comp_def] using hz'

theorem universalSideBlocks_accLengths_mem (m : ℕ → ℕ) (s t : List ℕ)
    (side : Bool) {z : ℕ}
    (hz : z ∈ accLengths 0
      (universalSideBlocks side (universalAtomRuns m s t))) :
    z ∈ accLengths 0
      ((((universalMergedAtoms m s t).filter (fun a ↦ a.side == side)).map
        UniversalAtom.data)) := by
  let gs := (universalAtomRuns m s t).filter
    (fun r ↦ universalRunSide r == side)
  have hne : ∀ g ∈ gs, g ≠ [] := by
    intro g hg
    have hg' : g ∈ universalAtomRuns m s t := by
      exact List.mem_of_mem_filter hg
    exact List.ne_nil_of_mem_splitBy hg'
  have h := accLengths_grouped_subset 0 gs hne z
  have hsrc : gs.flatten =
      (universalMergedAtoms m s t).filter (fun a ↦ a.side == side) := by
    exact universalAtomRuns_filter_flatten m s t side
  rw [hsrc] at h
  apply h
  simpa [universalSideBlocks, gs] using hz

theorem universalLeftBlocks_accLengths_mem {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {z : ℕ}
    (hz : z ∈ accLengths 0 (universalLeftBlocks m s t)) :
    z ∈ universalD m s.length := by
  have h := universalSideBlocks_accLengths_mem m s t false hz
  rw [universalMergedAtoms_filter_false m hlen, map_data_universalAtoms,
    accLengths_universalBlocks hm] at h
  exact h

theorem universalRightBlocks_accLengths_mem {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {z : ℕ}
    (hz : z ∈ accLengths 0 (universalRightBlocks m s t)) :
    z ∈ universalD m t.length := by
  have h := universalSideBlocks_accLengths_mem m s t true hz
  rw [universalMergedAtoms_filter_true m hlen, map_data_universalAtoms,
    accLengths_universalBlocks hm] at h
  exact h

theorem universalD_lt_A {m : ℕ → ℕ} (hm : StrictMono m) (j : ℕ) :
    ∀ x ∈ universalD m j, ∀ y ∈ universalA m j, x < y := by
  apply enumSlice_lt_enumSlice m hm
  rfl

theorem universalD_lt_B {m : ℕ → ℕ} (hm : StrictMono m)
    {j k r i : ℕ} (hjk : j < k) :
    ∀ x ∈ universalD m j, ∀ y ∈ universalB m k r i, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hnext := universalBlockBase_lt_nextStage m j
  have hstage : universalStageStart m (j + 1) ≤ universalStageStart m k :=
    (universalStageStart_strictMono m).monotone (by omega)
  have hbase : universalStageStart m k ≤ universalBlockBase m k := by
    unfold universalBlockBase
    omega
  have hblock : universalBlockBase m k ≤
      blockStart (universalBlockBase m k) (universalSlotSize m k) (r * k + i) :=
    blockStart_mono _ _ (Nat.zero_le _)
  unfold universalBlockBase at hnext
  omega

theorem universalA_lt_D {m : ℕ → ℕ} (hm : StrictMono m)
    {j k : ℕ} (hjk : j < k) :
    ∀ x ∈ universalA m j, ∀ y ∈ universalD m k, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hnext := universalBlockBase_lt_nextStage m j
  have hstage : universalStageStart m (j + 1) ≤ universalStageStart m k :=
    (universalStageStart_strictMono m).monotone (by omega)
  unfold universalBlockBase at hnext
  omega

theorem universalB_lt_D {m : ℕ → ℕ} (hm : StrictMono m)
    {k r j i : ℕ} (hjk : j < k) (hij : i < j) (hkr : k < r) :
    ∀ x ∈ universalB m k j i, ∀ y ∈ universalD m r, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hend := universalB_end_le_stageEnd m hjk hij
  have hnext :
      blockStart (universalBlockBase m k) (universalSlotSize m k) (k * k) <
        universalStageStart m (k + 1) := by
    rw [universalStageStart_succ]
    omega
  have hstage : universalStageStart m (k + 1) ≤ universalStageStart m r :=
    (universalStageStart_strictMono m).monotone (by omega)
  omega

theorem universalSideBlocks_interact (rs : List (List UniversalAtom))
    (hhead : ∀ b ∈ (rs.map universalRunSide).head?, b = false)
    (hchain : (rs.map universalRunSide).IsChain (· ≠ ·)) :
    interact (universalSideBlocks false rs) (universalSideBlocks true rs) =
      (rs.map universalRunData).flatten := by
  induction rs using List.twoStepInduction with
  | nil => rfl
  | singleton r =>
      have hr : universalRunSide r = false := hhead _ (by simp)
      simp [universalSideBlocks, hr, interact]
  | cons_cons r q rs ih =>
      have hr : universalRunSide r = false := hhead _ (by simp)
      simp only [List.map_cons, List.isChain_cons_cons] at hchain
      have hq : universalRunSide q = true := by
        cases h : universalRunSide q
        · exact (hchain.1 (hr.trans h.symm)).elim
        · rfl
      have hhead' : ∀ b ∈ (rs.map universalRunSide).head?, b = false := by
        intro b hb
        have hrel := hchain.2.rel_head? hb
        cases hbq : b
        · rfl
        · exact (hrel (hq.trans hbq.symm)).elim
      have htail := ih hhead' hchain.2.tail
      have hleft : universalSideBlocks false (r :: q :: rs) =
          universalRunData r :: universalSideBlocks false rs := by
        simp [universalSideBlocks, hr, hq]
      have hright : universalSideBlocks true (r :: q :: rs) =
          universalRunData q :: universalSideBlocks true rs := by
        simp [universalSideBlocks, hr, hq]
      rw [hleft, hright]
      simp only [interact, List.map_cons, List.flatten_cons]
      rw [htail]
      simp only [List.append_assoc]

theorem universalAtom_data_ne_nil {m : ℕ → ℕ} (hm : StrictMono m)
    {side : Bool} {s : List ℕ} {a : UniversalAtom}
    (ha : a ∈ universalAtoms m side s) : a.data ≠ [] := by
  rcases universalAtoms_cases ha with rfl | ⟨i, hi, rfl⟩
  · exact universalA_ne_nil hm _
  · exact universalB_ne_nil hm _ _ _

theorem universalRunData_ne_nil {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} {r : List UniversalAtom}
    (hr : r ∈ universalAtomRuns m s t) : universalRunData r ≠ [] := by
  have hrne : r ≠ [] := List.ne_nil_of_mem_splitBy hr
  let a := r.head hrne
  have haRun : a ∈ r := List.head_mem hrne
  have haMerged : a ∈ universalMergedAtoms m s t := by
    rw [← List.flatten_splitBy
      (fun a b : UniversalAtom ↦ decide (a.side = b.side))
      (universalMergedAtoms m s t)]
    exact List.mem_flatten.2 ⟨r, hr, haRun⟩
  rw [universalMergedAtoms, List.mem_merge] at haMerged
  have hdata : a.data ≠ [] := by
    rcases haMerged with ha | ha
    · exact universalAtom_data_ne_nil hm ha
    · exact universalAtom_data_ne_nil hm ha
  unfold universalRunData
  apply List.flatten_ne_nil_iff.2
  exact ⟨a.data, List.mem_map.2 ⟨a, haRun, rfl⟩, hdata⟩

theorem universalSideBlocks_blocks_ne_nil {m : ℕ → ℕ} (hm : StrictMono m)
    (s t : List ℕ) (side : Bool) :
    ∀ b ∈ universalSideBlocks side (universalAtomRuns m s t), b ≠ [] := by
  intro b hb
  unfold universalSideBlocks at hb
  rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
  exact universalRunData_ne_nil hm (List.mem_of_mem_filter hr)

theorem universalD_lt_A_of_le {m : ℕ → ℕ} (hm : StrictMono m)
    {j k : ℕ} (hjk : j ≤ k) :
    ∀ x ∈ universalD m j, ∀ y ∈ universalA m k, x < y := by
  rcases hjk.eq_or_lt with rfl | hjk
  · exact universalD_lt_A hm _
  · apply enumSlice_lt_enumSlice m hm
    have hnext := universalBlockBase_lt_nextStage m j
    have hstage : universalStageStart m (j + 1) ≤ universalStageStart m k :=
      (universalStageStart_strictMono m).monotone (by omega)
    unfold universalBlockBase at hnext
    omega

theorem universalD_lt_B_of_le {m : ℕ → ℕ} (hm : StrictMono m)
    {j k r i : ℕ} (hjk : j ≤ k) :
    ∀ x ∈ universalD m j, ∀ y ∈ universalB m k r i, x < y := by
  rcases hjk.eq_or_lt with rfl | hjk
  · apply enumSlice_lt_enumSlice m hm
    have hbase : universalStageStart m j + (j + 1) ≤ universalBlockBase m j := by
      unfold universalBlockBase
      omega
    exact hbase.trans (blockStart_mono _ _ (Nat.zero_le _))
  · exact universalD_lt_B hm hjk

theorem universalD_lt_sourceAtom {m : ℕ → ℕ} (hm : StrictMono m)
    {j u : ℕ} (hju : j ≤ u) {side : Bool} {s : List ℕ}
    (hslen : s.length = u) {a : UniversalAtom}
    (ha : a ∈ universalAtoms m side s) :
    ∀ x ∈ universalD m j, ∀ y ∈ a.data, x < y := by
  subst u
  rcases universalAtoms_cases ha with rfl | ⟨i, hi, rfl⟩
  · exact universalD_lt_A_of_le hm hju
  · have hiInc : i < (intoInc (s.length + 1) s).length := by simpa
    rw [List.getD_eq_getElem _ 0 hiInc]
    have hmem : (intoInc (s.length + 1) s)[i] ∈
        intoInc (s.length + 1) s := List.getElem_mem hiInc
    have hstage : j < (intoInc (s.length + 1) s)[i] := by
      have := mem_intoInc_ge hmem
      omega
    exact universalD_lt_B hm hstage

theorem universalAtom_lt_D_of_key {m : ℕ → ℕ} (hm : StrictMono m)
    {side : Bool} {s : List ℕ} {a : UniversalAtom} {r : ℕ}
    (ha : a ∈ universalAtoms m side s)
    (hkey : a.KeyLT (universalAAtom m true r)) :
    ∀ x ∈ a.data, ∀ y ∈ universalD m r, x < y := by
  rcases universalAtoms_cases ha with rfl | ⟨i, hi, rfl⟩
  · simp only [UniversalAtom.KeyLT, universalAAtom] at hkey
    exact universalA_lt_D hm (by omega)
  · have hiInc : i < (intoInc (s.length + 1) s).length := by simpa
    rw [List.getD_eq_getElem _ 0 hiInc] at hkey ⊢
    simp only [UniversalAtom.KeyLT, universalBAtom, universalAAtom] at hkey
    have hmem : (intoInc (s.length + 1) s)[i] ∈
        intoInc (s.length + 1) s := List.getElem_mem hiInc
    have hbase : s.length < (intoInc (s.length + 1) s)[i] := by
      have := mem_intoInc_ge hmem
      omega
    exact universalB_lt_D hm hbase hi (by omega)

theorem universalD_lt_atom_of_key {m : ℕ → ℕ} (hm : StrictMono m)
    {side : Bool} {s : List ℕ} {a : UniversalAtom} {r : ℕ}
    (ha : a ∈ universalAtoms m side s)
    (hkey : (universalAAtom m true r).KeyLT a) :
    ∀ x ∈ universalD m r, ∀ y ∈ a.data, x < y := by
  rcases universalAtoms_cases ha with rfl | ⟨i, hi, rfl⟩
  · simp only [UniversalAtom.KeyLT, universalAAtom] at hkey
    exact universalD_lt_A_of_le hm (by omega)
  · have hiInc : i < (intoInc (s.length + 1) s).length := by simpa
    rw [List.getD_eq_getElem _ 0 hiInc] at hkey ⊢
    simp only [UniversalAtom.KeyLT, universalAAtom, universalBAtom] at hkey
    apply universalD_lt_B_of_le hm
    omega

theorem universalD_lt_D {m : ℕ → ℕ} (hm : StrictMono m)
    {j k : ℕ} (hjk : j < k) :
    ∀ x ∈ universalD m j, ∀ y ∈ universalD m k, x < y := by
  apply enumSlice_lt_enumSlice m hm
  have hnext := universalBlockBase_lt_nextStage m j
  have hstage : universalStageStart m (j + 1) ≤ universalStageStart m k :=
    (universalStageStart_strictMono m).monotone (by omega)
  unfold universalBlockBase at hnext
  omega

theorem universalD_lt_mergedData {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {x y : ℕ}
    (hx : x ∈ universalD m s.length)
    (hy : y ∈ ((universalMergedAtoms m s t).map UniversalAtom.data).flatten) :
    x < y := by
  rcases List.mem_flatten.1 hy with ⟨d, hd, hyd⟩
  rcases List.mem_map.1 hd with ⟨a, ha, rfl⟩
  rw [universalMergedAtoms, List.mem_merge] at ha
  rcases ha with ha | ha
  · exact universalD_lt_sourceAtom hm (le_refl _) rfl ha x hx y hyd
  · exact universalD_lt_sourceAtom hm hlen.le rfl ha x hx y hyd

noncomputable def universalScheme (m : ℕ → ℕ) (s t : List ℕ) : List ℕ :=
  let left := universalLeftBlocks m s t
  let right := universalRightBlocks m s t
  accLengths 0 left ++ left.headD [] ++
    accLengths 0 right ++ right.headD [] ++ interact left.tail right.tail

theorem universalAtom_mem_left_of_merged_of_side_false {m : ℕ → ℕ}
    {s t : List ℕ} {a : UniversalAtom}
    (ha : a ∈ universalMergedAtoms m s t) (hside : a.side = false) :
    a ∈ universalAtoms m false s := by
  rw [universalMergedAtoms, List.mem_merge] at ha
  rcases ha with ha | ha
  · exact ha
  · have := universalAtoms_side ha
    simp_all

theorem universalAtom_mem_right_of_merged_of_side_true {m : ℕ → ℕ}
    {s t : List ℕ} {a : UniversalAtom}
    (ha : a ∈ universalMergedAtoms m s t) (hside : a.side = true) :
    a ∈ universalAtoms m true t := by
  rw [universalMergedAtoms, List.mem_merge] at ha
  rcases ha with ha | ha
  · have := universalAtoms_side ha
    simp_all
  · exact ha

theorem universalRunAtom_mem_merged {m : ℕ → ℕ} {s t : List ℕ}
    {r : List UniversalAtom} (hr : r ∈ universalAtomRuns m s t)
    {a : UniversalAtom} (ha : a ∈ r) : a ∈ universalMergedAtoms m s t := by
  rw [← List.flatten_splitBy
    (fun a b : UniversalAtom ↦ decide (a.side = b.side))
    (universalMergedAtoms m s t)]
  exact List.mem_flatten.2 ⟨r, hr, ha⟩

theorem mem_universalRunData {r : List UniversalAtom} {x : ℕ} :
    x ∈ universalRunData r ↔ ∃ a ∈ r, x ∈ a.data := by
  simp [universalRunData, List.mem_flatten]

theorem mem_map_runData_flatten {rs : List (List UniversalAtom)} {x : ℕ} :
    x ∈ (rs.map universalRunData).flatten ↔
      ∃ r ∈ rs, ∃ a ∈ r, x ∈ a.data := by
  simp [List.mem_flatten, mem_universalRunData]

theorem universalScheme_pairwise {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalScheme m s t).Pairwise (· < ·) := by
  let rs := universalAtomRuns m s t
  let left := universalLeftBlocks m s t
  let right := universalRightBlocks m s t
  have hcounts := universalBlocks_count_bounds hm hlen
  have hrsne : rs ≠ [] := by
    dsimp [rs]
    exact (List.splitBy_ne_nil).2 (universalMergedAtoms_ne_nil m s t)
  cases hrs : rs with
  | nil => exact (hrsne hrs).elim
  | cons r₀ rs' =>
      have hr₀ : r₀ ∈ universalAtomRuns m s t := by
        change r₀ ∈ rs
        simp [hrs]
      have hside₀ : universalRunSide r₀ = false := by
        simpa [rs, hrs] using universalAtomRuns_headSide m hlen
      cases hrs' : rs' with
      | nil =>
          have hright : right = [] := by
            dsimp [right, universalRightBlocks]
            change universalSideBlocks true rs = []
            rw [hrs, hrs']
            simp [universalSideBlocks, hside₀]
          have : right.length = 0 := by simp [hright]
          exact ((Nat.ne_of_gt hcounts.1) this).elim
      | cons r₁ rest =>
          have hr₁ : r₁ ∈ universalAtomRuns m s t := by
            change r₁ ∈ rs
            simp [hrs, hrs']
          have hside₁ : universalRunSide r₁ = true := by
            have hc := universalAtomRuns_sides_chain m s t
            change (rs.map universalRunSide).IsChain (· ≠ ·) at hc
            rw [hrs, hrs'] at hc
            simp only [List.map_cons, List.isChain_cons_cons] at hc
            cases h : universalRunSide r₁
            · exact (hc.1 (hside₀.trans h.symm)).elim
            · rfl
          have hr₀ne : r₀ ≠ [] := List.ne_nil_of_mem_splitBy hr₀
          have hr₁ne : r₁ ≠ [] := List.ne_nil_of_mem_splitBy hr₁
          have hleft : left = universalRunData r₀ ::
              universalSideBlocks false rest := by
            dsimp [left, universalLeftBlocks]
            change universalSideBlocks false rs = _
            rw [hrs, hrs']
            simp [universalSideBlocks, hside₀, hside₁]
          have hright : right = universalRunData r₁ ::
              universalSideBlocks true rest := by
            dsimp [right, universalRightBlocks]
            change universalSideBlocks true rs = _
            rw [hrs, hrs']
            simp [universalSideBlocks, hside₀, hside₁]
          have hflat : rs.flatten = universalMergedAtoms m s t := by
            dsimp [rs]
            exact List.flatten_splitBy _ _
          have hmerge : universalMergedAtoms m s t =
              r₀ ++ r₁ ++ rest.flatten := by
            rw [← hflat, hrs, hrs']
            simp only [List.flatten_cons, List.append_assoc]
          have hfilter₀ : r₀.filter (fun a ↦ a.side == true) = [] := by
            have h := universalRun_filter_side hr₀ true
            simpa [hside₀] using h
          have hfilter₁ : r₁.filter (fun a ↦ a.side == true) = r₁ := by
            have h := universalRun_filter_side hr₁ true
            simpa [hside₁] using h
          have hfirst₁ : r₁.head hr₁ne = universalAAtom m true t.length := by
            have hf := universalMergedAtoms_filter_true m hlen
            rw [hmerge, List.filter_append, List.filter_append,
              hfilter₀, hfilter₁, List.nil_append, universalAtoms] at hf
            have hh := congrArg List.head? hf
            rw [List.head?_append_of_ne_nil r₁ hr₁ne] at hh
            rw [List.head?_eq_some_head hr₁ne] at hh
            exact Option.some.inj hh
          have hkey := universalMergedAtoms_key_pairwise m hlen
          rw [hmerge] at hkey
          have hnum := universalMergedAtoms_data_pairwise hm hlen
          rw [hmerge, List.map_append, List.map_append,
            List.flatten_append, List.flatten_append] at hnum
          rw [← map_runData_flatten rest] at hnum
          let a := universalRunData r₀
          let b := universalRunData r₁
          let tail := (rest.map universalRunData).flatten
          change (a ++ b ++ tail).Pairwise (· < ·) at hnum
          have hchain := universalAtomRuns_sides_chain m s t
          change (rs.map universalRunSide).IsChain (· ≠ ·) at hchain
          rw [hrs, hrs'] at hchain
          simp only [List.map_cons, List.isChain_cons_cons] at hchain
          have hheadRest : ∀ q ∈ (rest.map universalRunSide).head?, q = false := by
            intro q hq
            have hrel := hchain.2.rel_head? hq
            cases hqv : q
            · rfl
            · exact (hrel (hside₁.trans hqv.symm)).elim
          have hinteract : interact (universalSideBlocks false rest)
              (universalSideBlocks true rest) = tail := by
            exact universalSideBlocks_interact rest hheadRest hchain.2.tail
          have hleftNe := universalSideBlocks_blocks_ne_nil hm s t false
          have hrightNe := universalSideBlocks_blocks_ne_nil hm s t true
          have heLeft : (accLengths 0 left).Pairwise (· < ·) :=
            accLengths_pairwise_of_ne hleftNe
          have heRight : (accLengths 0 right).Pairwise (· < ·) :=
            accLengths_pairwise_of_ne hrightNe
          rw [List.pairwise_append] at hnum
          have hAB := hnum.1
          have hTail := hnum.2.1
          have hABTail := hnum.2.2
          rw [List.pairwise_append] at hAB
          have haPair := hAB.1
          have hbPair := hAB.2.1
          have hab := hAB.2.2
          have hA_lt_tail : ∀ x ∈ a, ∀ y ∈ tail, x < y := by
            intro x hx y hy
            exact hABTail x (by simp [hx]) y hy
          have hB_lt_tail : ∀ x ∈ b, ∀ y ∈ tail, x < y := by
            intro x hx y hy
            exact hABTail x (by simp [hx]) y hy
          have heLeft_lt_all : ∀ x ∈ accLengths 0 left,
              ∀ y ∈ a ++ b ++ tail, x < y := by
            intro x hx y hy
            have hxD := universalLeftBlocks_accLengths_mem hm hlen hx
            have hyMerged : y ∈
                ((universalMergedAtoms m s t).map UniversalAtom.data).flatten := by
              rw [hmerge, List.map_append, List.map_append,
                List.flatten_append, List.flatten_append,
                ← map_runData_flatten rest]
              exact hy
            exact universalD_lt_mergedData hm hlen hxD hyMerged
          have hA_lt_eRight : ∀ x ∈ a, ∀ y ∈ accLengths 0 right, x < y := by
            intro x hx y hy
            rcases mem_universalRunData.mp hx with ⟨atom, hatom, hxData⟩
            have hatomMerged := universalRunAtom_mem_merged hr₀ hatom
            have hatomLeft := universalAtom_mem_left_of_merged_of_side_false
              hatomMerged ((universalRun_side hr₀ atom hatom).trans hside₀)
            have hkeyAB := (List.pairwise_append.mp hkey).1
            have hkeyAB' := (List.pairwise_append.mp hkeyAB).2.2
              atom hatom (r₁.head hr₁ne) (List.head_mem hr₁ne)
            rw [hfirst₁] at hkeyAB'
            exact universalAtom_lt_D_of_key hm hatomLeft hkeyAB' x hxData y
              (universalRightBlocks_accLengths_mem hm hlen hy)
          have heRight_lt_b : ∀ x ∈ accLengths 0 right, ∀ y ∈ b, x < y := by
            intro x hx y hy
            rcases mem_universalRunData.mp hy with ⟨atom, hatom, hyData⟩
            have hatomMerged := universalRunAtom_mem_merged hr₁ hatom
            have hatomRight := universalAtom_mem_right_of_merged_of_side_true
              hatomMerged ((universalRun_side hr₁ atom hatom).trans hside₁)
            exact universalD_lt_sourceAtom hm (le_refl _) rfl hatomRight x
              (universalRightBlocks_accLengths_mem hm hlen hx) y hyData
          have heRight_lt_tail : ∀ x ∈ accLengths 0 right,
              ∀ y ∈ tail, x < y := by
            intro x hx y hy
            rcases mem_map_runData_flatten.mp hy with
              ⟨run, hrun, atom, hatom, hyData⟩
            have hrunAll : run ∈ universalAtomRuns m s t := by
              change run ∈ rs
              simp [hrs, hrs', hrun]
            have hatomMerged := universalRunAtom_mem_merged hrunAll hatom
            have hkeyRest := (List.pairwise_append.mp hkey).2.2
              (r₁.head hr₁ne) (by simp [List.head_mem hr₁ne]) atom
              (List.mem_flatten.2 ⟨run, hrun, hatom⟩)
            rw [hfirst₁] at hkeyRest
            rw [universalMergedAtoms, List.mem_merge] at hatomMerged
            rcases hatomMerged with hatomSource | hatomSource
            · exact universalD_lt_atom_of_key hm hatomSource hkeyRest x
                (universalRightBlocks_accLengths_mem hm hlen hx) y hyData
            · exact universalD_lt_atom_of_key hm hatomSource hkeyRest x
                (universalRightBlocks_accLengths_mem hm hlen hx) y hyData
          have p₁ : (accLengths 0 left ++ a).Pairwise (· < ·) :=
            pairwise_append_of_lt heLeft haPair (by
              intro x hx y hy
              exact heLeft_lt_all x hx y (by simp [hy]))
          have p₂ : (accLengths 0 left ++ a ++ accLengths 0 right).Pairwise
              (· < ·) := pairwise_append_of_lt p₁ heRight (by
            intro x hx y hy
            rw [List.mem_append] at hx
            rcases hx with hx | hx
            · have hyD := universalRightBlocks_accLengths_mem hm hlen hy
              have hxD := universalLeftBlocks_accLengths_mem hm hlen hx
              exact universalD_lt_D hm hlen x hxD y hyD
            · exact hA_lt_eRight x hx y hy)
          have p₃ : (accLengths 0 left ++ a ++ accLengths 0 right ++ b).Pairwise
              (· < ·) := pairwise_append_of_lt p₂ hbPair (by
            intro x hx y hy
            rw [List.mem_append, List.mem_append] at hx
            rcases hx with (hx | hx) | hx
            · exact heLeft_lt_all x hx y (by simp [hy])
            · exact hab x hx y hy
            · exact heRight_lt_b x hx y hy)
          have p₄ : (accLengths 0 left ++ a ++ accLengths 0 right ++ b ++ tail).Pairwise
              (· < ·) := pairwise_append_of_lt p₃ hTail (by
            intro x hx y hy
            rw [List.mem_append, List.mem_append, List.mem_append] at hx
            rcases hx with ((hx | hx) | hx) | hx
            · exact heLeft_lt_all x hx y (by simp [hy])
            · exact hA_lt_tail x hx y hy
            · exact heRight_lt_tail x hx y hy
            · exact hB_lt_tail x hx y hy)
          unfold universalScheme
          dsimp only
          rw [show universalLeftBlocks m s t = left from rfl,
            show universalRightBlocks m s t = right from rfl,
            hleft, hright]
          simp only [List.headD_cons, List.tail_cons]
          rw [hinteract]
          rw [hleft, hright] at p₄
          exact p₄

theorem length_le_flatten_length_of_blocks_ne_nil {α : Type*}
    (blocks : List (List α)) (hne : ∀ b ∈ blocks, b ≠ []) :
    blocks.length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => simp
  | cons b blocks ih =>
      have hb : 0 < b.length := by
        cases b with
        | nil => exact ((hne [] (by simp)) rfl).elim
        | cons x xs => simp
      have htail : ∀ q ∈ blocks, q ≠ [] := by
        intro q hq
        exact hne q (by simp [hq])
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      have := ih htail
      omega

theorem universalSideBlocks_length_le_source (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) (side : Bool) :
    (universalSideBlocks side (universalAtomRuns m s t)).length ≤
      if side then t.length + 1 else s.length + 1 := by
  let selected := (universalAtomRuns m s t).filter
    (fun r ↦ universalRunSide r == side)
  have hselected : ∀ r ∈ selected, r ≠ [] := by
    intro r hr
    exact List.ne_nil_of_mem_splitBy (List.mem_of_mem_filter hr)
  have hlenSelected := length_le_flatten_length_of_blocks_ne_nil selected hselected
  have hflat := universalAtomRuns_filter_flatten m s t side
  change selected.flatten =
      (universalMergedAtoms m s t).filter (fun a ↦ a.side == side) at hflat
  unfold universalSideBlocks
  change (selected.map universalRunData).length ≤ _
  simp only [List.length_map]
  rw [hflat] at hlenSelected
  cases side
  · rw [universalMergedAtoms_filter_false m hlen] at hlenSelected
    simpa using hlenSelected
  · rw [universalMergedAtoms_filter_true m hlen] at hlenSelected
    simpa using hlenSelected

theorem universalLeftBlocks_length_le (m : ℕ → ℕ)
    {s t : List ℕ} (hlen : s.length < t.length) :
    (universalLeftBlocks m s t).length ≤ s.length + 1 := by
  exact universalSideBlocks_length_le_source m hlen false

/-- The stage-allocated pair has a positive Larson form, with a form number
bounded solely by the source level of the shorter sequence. -/
theorem universalPair_exactScheme {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) :
    ∃ l, ∃ w : ExactSchemeWitness l (universalScheme m s t),
      0 < l ∧ l ≤ 2 * (s.length + 1) ∧
      w.left = universalVertex m hm s ∧ w.right = universalVertex m hm t := by
  let left := universalLeftBlocks m s t
  let right := universalRightBlocks m s t
  have hcounts := universalBlocks_count_bounds hm hlen
  have hq : 0 < right.length := by simpa [right] using hcounts.1
  have hp : 0 < left.length := lt_of_lt_of_le hq (by
    simpa [left, right] using hcounts.2.1)
  have hpq : left.length ≤ right.length + 1 := by
    simpa [left, right] using hcounts.2.2
  have hqp : right.length ≤ left.length := by
    simpa [left, right] using hcounts.2.1
  have hpBound : left.length ≤ s.length + 1 := by
    simpa [left] using universalLeftBlocks_length_le m hlen
  cases hleft : left with
  | nil => simp [hleft] at hp
  | cons a as =>
    cases hright : right with
    | nil => simp [hright] at hq
    | cons b bs =>
      have hbody : FormBody left.length right.length
          (universalVertexList m s) (universalVertexList m t)
          (universalScheme m s t) := by
        apply FormBody.intro a as b bs
        · exact universalVertex_length_strictMono hm hlen
        · rw [← hleft]
          simpa [left] using (universalLeftBlocks_flatten m hlen).symm
        · rw [← hright]
          simpa [right] using (universalRightBlocks_flatten m hlen).symm
        · rw [← hleft]
          change ∀ q ∈ universalSideBlocks false (universalAtomRuns m s t), q ≠ []
          exact universalSideBlocks_blocks_ne_nil hm s t false
        · rw [← hright]
          change ∀ q ∈ universalSideBlocks true (universalAtomRuns m s t), q ≠ []
          exact universalSideBlocks_blocks_ne_nil hm s t true
        · rw [← hleft]
        · rw [← hright]
        · simp [universalScheme, left, right, hleft, hright]
        · exact universalScheme_pairwise hm hlen
      have hcases : left.length = right.length ∨
          left.length = right.length + 1 := by omega
      rcases hcases with heq | heq
      · refine ⟨2 * right.length - 1,
          ⟨universalVertex m hm s, universalVertex m hm t, Or.inl ?_⟩,
          ?_, ?_, rfl, rfl⟩
        · refine ⟨right.length, hq, rfl, Or.inl ?_⟩
          change FormBody right.length right.length
            (universalVertexList m s) (universalVertexList m t) _
          simpa [heq] using hbody
        · omega
        · omega
      · refine ⟨2 * right.length,
          ⟨universalVertex m hm s, universalVertex m hm t, Or.inr ?_⟩,
          ?_, ?_, rfl, rfl⟩
        · refine ⟨right.length, hq, rfl, Or.inl ?_⟩
          change FormBody (right.length + 1) right.length
            (universalVertexList m s) (universalVertexList m t) _
          simpa [heq] using hbody
        · omega
        · omega

theorem mem_enumSlice_range {m : ℕ → ℕ} {start len z : ℕ}
    (hz : z ∈ enumSlice m start len) : z ∈ Set.range m := by
  rcases mem_enumSlice.mp hz with ⟨i, hi, rfl⟩
  exact ⟨start + i, rfl⟩

theorem mem_universalBSeq_range {m : ℕ → ℕ} {j i : ℕ}
    {ks : List ℕ} {z : ℕ} (hz : z ∈ (universalBSeq m j i ks).flatten) :
    z ∈ Set.range m := by
  induction ks generalizing i with
  | nil => simp [universalBSeq] at hz
  | cons k ks ih =>
      simp only [universalBSeq, List.flatten_cons, List.mem_append] at hz
      rcases hz with hz | hz
      · exact mem_enumSlice_range hz
      · exact ih (i := i + 1) hz

theorem universalVertexList_mem_range {m : ℕ → ℕ} {s : List ℕ} {z : ℕ}
    (hz : z ∈ universalVertexList m s) : z ∈ Set.range m := by
  simp only [universalVertexList, universalBlocks, List.flatten_cons,
    List.mem_append] at hz
  rcases hz with hz | hz
  · exact mem_enumSlice_range hz
  · exact mem_universalBSeq_range hz

theorem mem_universalBSeq_gt_stage {m : ℕ → ℕ} (hm : StrictMono m)
    {j i : ℕ} {ks : List ℕ} (hstage : ∀ k ∈ ks, j < k)
    {z : ℕ} (hz : z ∈ (universalBSeq m j i ks).flatten) :
    m (universalStageStart m j) < z := by
  induction ks generalizing i with
  | nil => simp [universalBSeq] at hz
  | cons k ks ih =>
      simp only [universalBSeq, List.flatten_cons, List.mem_append] at hz
      rcases hz with hz | hz
      · rcases mem_enumSlice.mp hz with ⟨r, hr, rfl⟩
        apply hm
        have hjk : j < k := hstage k (by simp)
        have hst := universalStageStart_strictMono m hjk
        have hbase : universalStageStart m k < universalBlockBase m k := by
          unfold universalBlockBase
          omega
        have hblock : universalBlockBase m k ≤
            blockStart (universalBlockBase m k) (universalSlotSize m k)
              (j * k + i) := blockStart_mono _ _ (Nat.zero_le _)
        exact hst.trans (hbase.trans_le (hblock.trans (Nat.le_add_right _ _)))
      · apply ih (i := i + 1)
        · intro r hr
          exact hstage r (by simp [hr])
        · exact hz

theorem universalVertexList_gt_stage {m : ℕ → ℕ} (hm : StrictMono m)
    {s : List ℕ} {z : ℕ} (hz : z ∈ universalVertexList m s) :
    m (universalStageStart m s.length) < z := by
  simp only [universalVertexList, universalBlocks, List.flatten_cons,
    List.mem_append] at hz
  rcases hz with hz | hz
  · rcases mem_enumSlice.mp hz with ⟨i, hi, rfl⟩
    apply hm
    omega
  · apply mem_universalBSeq_gt_stage (i := 0)
      (ks := intoInc (s.length + 1) s) hm
    · intro k hk
      have hge : s.length + 1 ≤ k :=
        mem_intoInc_ge (k := s.length + 1) (s := s) hk
      omega
    · exact hz

theorem mem_accLengths_range {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {side : Bool} {z : ℕ}
    (hz : z ∈ accLengths 0
      (universalSideBlocks side (universalAtomRuns m s t))) :
    z ∈ Set.range m := by
  cases side
  · exact mem_enumSlice_range (universalLeftBlocks_accLengths_mem hm hlen hz)
  · exact mem_enumSlice_range (universalRightBlocks_accLengths_mem hm hlen hz)

theorem mem_accLengths_ge_left_stage {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {side : Bool} {z : ℕ}
    (hz : z ∈ accLengths 0
      (universalSideBlocks side (universalAtomRuns m s t))) :
    m (universalStageStart m s.length) ≤ z := by
  cases side
  · rcases mem_enumSlice.mp
        (universalLeftBlocks_accLengths_mem hm hlen hz) with ⟨i, hi, rfl⟩
    exact hm.monotone (Nat.le_add_right _ _)
  · rcases mem_enumSlice.mp
        (universalRightBlocks_accLengths_mem hm hlen hz) with ⟨i, hi, rfl⟩
    apply hm.monotone
    have hst := (universalStageStart_strictMono m).monotone hlen.le
    exact hst.trans (Nat.le_add_right _ _)

theorem mem_headD_mem_flatten {α : Type*} {blocks : List (List α)} {z : α}
    (hz : z ∈ blocks.headD []) : z ∈ blocks.flatten := by
  cases blocks with
  | nil => simp at hz
  | cons b bs => simp only [List.headD_cons, List.flatten_cons, List.mem_append]; exact Or.inl hz

theorem mem_interact_mem_flatten {α : Type*} {as bs : List (List α)} {z : α}
    (hz : z ∈ interact as bs) : z ∈ as.flatten ∨ z ∈ bs.flatten := by
  classical
  have hz' : z ∈ (interact as bs).toFinset := List.mem_toFinset.mpr hz
  rw [toFinset_interact] at hz'
  rcases Finset.mem_union.mp hz' with hz' | hz'
  · exact Or.inl (by simpa using hz')
  · exact Or.inr (by simpa using hz')

theorem mem_tail_flatten_mem_flatten {α : Type*} {blocks : List (List α)} {z : α}
    (hz : z ∈ blocks.tail.flatten) : z ∈ blocks.flatten := by
  cases blocks with
  | nil => simp at hz
  | cons b bs =>
      simp only [List.tail_cons, List.flatten_cons, List.mem_append]
      exact Or.inr hz

theorem universalScheme_mem_range {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {z : ℕ}
    (hz : z ∈ universalScheme m s t) : z ∈ Set.range m := by
  let left := universalLeftBlocks m s t
  let right := universalRightBlocks m s t
  simp only [universalScheme, List.mem_append] at hz
  rcases hz with (((hz | hz) | hz) | hz) | hz
  · exact mem_accLengths_range hm hlen hz
  · apply universalVertexList_mem_range
    rw [← universalLeftBlocks_flatten m hlen]
    exact mem_headD_mem_flatten hz
  · exact mem_accLengths_range hm hlen hz
  · apply universalVertexList_mem_range
    rw [← universalRightBlocks_flatten m hlen]
    exact mem_headD_mem_flatten hz
  · rcases mem_interact_mem_flatten hz with hz | hz
    · apply universalVertexList_mem_range
      rw [← universalLeftBlocks_flatten m hlen]
      exact mem_tail_flatten_mem_flatten hz
    · apply universalVertexList_mem_range
      rw [← universalRightBlocks_flatten m hlen]
      exact mem_tail_flatten_mem_flatten hz

theorem universalScheme_mem_ge_left_stage {m : ℕ → ℕ} (hm : StrictMono m)
    {s t : List ℕ} (hlen : s.length < t.length) {z : ℕ}
    (hz : z ∈ universalScheme m s t) :
    m (universalStageStart m s.length) ≤ z := by
  simp only [universalScheme, List.mem_append] at hz
  rcases hz with (((hz | hz) | hz) | hz) | hz
  · exact mem_accLengths_ge_left_stage hm hlen hz
  · exact (universalVertexList_gt_stage hm (by
      rw [← universalLeftBlocks_flatten m hlen]
      exact mem_headD_mem_flatten hz)).le
  · exact mem_accLengths_ge_left_stage hm hlen hz
  · have hgt := universalVertexList_gt_stage hm (by
      rw [← universalRightBlocks_flatten m hlen]
      exact mem_headD_mem_flatten hz)
    exact (hm (universalStageStart_strictMono m hlen)).le.trans hgt.le
  · rcases mem_interact_mem_flatten hz with hz | hz
    · exact (universalVertexList_gt_stage hm (by
        rw [← universalLeftBlocks_flatten m hlen]
        exact mem_tail_flatten_mem_flatten hz)).le
    · have hgt := universalVertexList_gt_stage hm (by
        rw [← universalRightBlocks_flatten m hlen]
        exact mem_tail_flatten_mem_flatten hz)
      exact (hm (universalStageStart_strictMono m hlen)).le.trans hgt.le

/-- Canonicalization plus the universal scheme makes every pair whose source
levels differ red in the absence of a blue triangle. -/
theorem universalPair_color_false
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {s t : List ℕ} (hlen : s.length < t.length) :
    color
      (universalVertex (exactCanonMarker color hcomm Set.infinite_univ)
        (exactCanonMarker_strictMono color hcomm Set.infinite_univ) s)
      (universalVertex (exactCanonMarker color hcomm Set.infinite_univ)
        (exactCanonMarker_strictMono color hcomm Set.infinite_univ) t) = false := by
  let m := exactCanonMarker color hcomm Set.infinite_univ
  have hm : StrictMono m := exactCanonMarker_strictMono color hcomm Set.infinite_univ
  obtain ⟨l, w, hl, hlBound, hwleft, hwright⟩ := universalPair_exactScheme hm hlen
  have hsupport : (↑(universalScheme m s t).toFinset : Set ℕ) ⊆
      exactCanonSet color hcomm Set.infinite_univ := by
    intro z hz
    change z ∈ exactCanonSet color hcomm Set.infinite_univ
    have hzList : z ∈ universalScheme m s t := by simpa using hz
    exact universalScheme_mem_range hm hlen hzList
  have hbound : ∀ z ∈ (universalScheme m s t).toFinset,
      exactCanonMarker color hcomm Set.infinite_univ (l - 1) < z := by
    intro z hz
    have hzList : z ∈ universalScheme m s t := by simpa using hz
    have hindex : l - 1 < universalStageStart m s.length := by
      have hstage := universalStageStart_bound m s.length
      omega
    exact (hm hindex).trans_le
      (universalScheme_mem_ge_left_stage hm hlen hzList)
  have hcanon := exactCanonized_of_marker_bound color hcomm Set.infinite_univ
    hl w hsupport hbound
  change color (universalVertex m hm s) (universalVertex m hm t) = false
  rw [← hwleft, ← hwright, hcanon]
  exact exactPositiveFormColor_false_of_no_triangle color hcomm
    Set.infinite_univ htri hl

structure LevelRedEmbedding (color : IncList → IncList → Bool) where
  embedding : LL ↪r LL
  preserves_level : ∀ x y : IncList,
    x.1.length = y.1.length →
      (embedding x).1.length = (embedding y).1.length
  same_level_red : ∀ x y : IncList, x ≠ y →
    x.1.length = y.1.length → color (embedding x) (embedding y) = false

noncomputable def levelMap
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (x : IncList) : IncList :=
  encodeInc ((levelRawEmbedding color hcomm htri x.1.length
    (incListToRaw x)).1)

@[simp] theorem levelMap_length
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (x : IncList) :
    (levelMap color hcomm htri x).1.length = emTargetLength x.1.length := by
  rw [levelMap]
  simp only [encodeInc_val, length_intoInc]
  exact (levelRawEmbedding color hcomm htri x.1.length (incListToRaw x)).2

theorem levelMap_mono
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    {x y : IncList} (hxy : LL x y) :
    LL (levelMap color hcomm htri x) (levelMap color hcomm htri y) := by
  apply LL_iff.mpr
  rcases LL_iff.mp hxy with hlen | ⟨hlen, hlex⟩
  · apply Or.inl
    simpa using emTargetLength_strictMono hlen
  · apply Or.inr
    have htarget : emTargetLength x.1.length = emTargetLength y.1.length :=
      congrArg emTargetLength hlen
    refine ⟨by simpa using htarget, ?_⟩
    let yr : RawLevel x.1.length :=
      cast (congrArg RawLevel hlen.symm) (incListToRaw y)
    have hraw : RawLevelLex (incListToRaw x) yr := by
      change List.Lex (· < ·) (incListToRaw x).1 yr.1
      rw [show yr.1 = (incListToRaw y).1 from
        rawLevel_cast_val hlen (incListToRaw y)]
      exact lex_incListToRaw_iff.mpr hlex
    have hout := (levelRawEmbedding color hcomm htri x.1.length).map_rel_iff.mpr hraw
    change List.Lex (· < ·)
      ((levelRawEmbedding color hcomm htri x.1.length (incListToRaw x)).1)
      ((levelRawEmbedding color hcomm htri x.1.length yr).1) at hout
    rw [levelRawEmbedding_cast_val color hcomm htri hlen (incListToRaw y)] at hout
    change List.Lex (· < ·)
      (intoInc 0 ((levelRawEmbedding color hcomm htri x.1.length
        (incListToRaw x)).1))
      (intoInc 0 ((levelRawEmbedding color hcomm htri y.1.length
        (incListToRaw y)).1))
    exact (lex_intoInc_iff 0 _ _).mpr hout

noncomputable def levelRedEmbedding
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true)) :
    LevelRedEmbedding color := by
  let E : LL ↪r LL := RelEmbedding.ofMonotone
    (levelMap color hcomm htri) (fun _ _ h ↦ levelMap_mono color hcomm htri h)
  refine {
    embedding := E
    preserves_level := ?_
    same_level_red := ?_ }
  · intro x y hlen
    simpa [E, hlen]
  · intro x y hxy hlen
    change color (levelMap color hcomm htri x)
      (levelMap color hcomm htri y) = false
    let yr : RawLevel x.1.length :=
      cast (congrArg RawLevel hlen.symm) (incListToRaw y)
    have hrawNe : incListToRaw x ≠ yr := by
      intro hraw
      apply hxy
      apply incListToRaw_val_injective
      rw [hraw]
      exact rawLevel_cast_val hlen (incListToRaw y)
    have hred := levelRawEmbedding_red color hcomm htri x.1.length
      (incListToRaw x) yr hrawNe
    rw [levelRawEmbedding_cast_val color hcomm htri hlen (incListToRaw y)] at hred
    exact hred

noncomputable def larsonEmbedding
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (level : LevelRedEmbedding color) :
    List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ↪r LL := by
  let pulled : IncList → IncList → Bool := fun x y ↦
    color (level.embedding x) (level.embedding y)
  have hpulledComm : ∀ x y, pulled x y = pulled y x := by
    intro x y
    exact hcomm _ _
  have hpulledTri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (pulled x y = true ∧ pulled x z = true ∧ pulled y z = true) := by
    intro x y z hxy hxz hyz
    exact htri _ _ _ (fun h ↦ hxy (level.embedding.injective h))
      (fun h ↦ hxz (level.embedding.injective h))
      (fun h ↦ hyz (level.embedding.injective h))
  let m := exactCanonMarker pulled hpulledComm Set.infinite_univ
  let hm : StrictMono m := exactCanonMarker_strictMono pulled hpulledComm Set.infinite_univ
  exact (universalVertexEmbedding m hm).trans level.embedding

theorem larsonEmbedding_color_false
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (level : LevelRedEmbedding color) {s t : List ℕ} (hst : s ≠ t) :
    color (larsonEmbedding color hcomm htri level s)
      (larsonEmbedding color hcomm htri level t) = false := by
  let pulled : IncList → IncList → Bool := fun x y ↦
    color (level.embedding x) (level.embedding y)
  have hpulledComm : ∀ x y, pulled x y = pulled y x := by
    intro x y
    exact hcomm _ _
  have hpulledTri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (pulled x y = true ∧ pulled x z = true ∧ pulled y z = true) := by
    intro x y z hxy hxz hyz
    exact htri _ _ _ (fun h ↦ hxy (level.embedding.injective h))
      (fun h ↦ hxz (level.embedding.injective h))
      (fun h ↦ hyz (level.embedding.injective h))
  let m := exactCanonMarker pulled hpulledComm Set.infinite_univ
  let hm : StrictMono m := exactCanonMarker_strictMono pulled hpulledComm Set.infinite_univ
  change pulled (universalVertex m hm s) (universalVertex m hm t) = false
  rcases lt_trichotomy s.length t.length with hlen | hlen | hlen
  · exact universalPair_color_false pulled hpulledComm hpulledTri hlen
  · apply level.same_level_red
    · intro huv
      apply hst
      apply (universalVertexEmbedding m hm).injective
      exact huv
    · change (universalVertexList m s).length = (universalVertexList m t).length
      rw [length_universalVertexList hm, length_universalVertexList hm, hlen]
  · rw [hpulledComm]
    exact universalPair_color_false pulled hpulledComm hpulledTri hlen

noncomputable def relEmbeddingRangeRelIso {α β : Type*}
    {r : α → α → Prop} {s : β → β → Prop} (e : r ↪r s) :
    r ≃r (fun x y : Set.range e ↦ s x.1 y.1) where
  toEquiv := Equiv.ofInjective e e.injective
  map_rel_iff' := e.map_rel_iff

theorem larsonEmbedding_range_type
    (color : IncList → IncList → Bool)
    (hcomm : ∀ x y, color x y = color y x)
    (htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
      ¬ (color x y = true ∧ color x z = true ∧ color y z = true))
    (level : LevelRedEmbedding color) :
    typeLT (Set.range (larsonEmbedding color hcomm htri level)) = ω ^ ω := by
  letI : IsWellOrder (Set.range (larsonEmbedding color hcomm htri level))
      (fun x y ↦ LL x.1 y.1) := {
    wf := InvImage.wf Subtype.val incListLLIsWellOrder.wf
    trichotomous a b hab hba := by
      rcases LL.trichotomous a.1 b.1 with h | h | h
      · exact (hab h).elim
      · exact Subtype.ext h
      · exact (hba h).elim }
  have htype :=
    (relEmbeddingRangeRelIso (larsonEmbedding color hcomm htri level)).ordinalType_congr
  rw [rawShortlex_type] at htype
  exact htype.symm

def LiftLL : ULift.{u} IncList → ULift.{u} IncList → Prop :=
  ULift.down ⁻¹'o LL

instance liftLLIsWellOrder : IsWellOrder (ULift.{u} IncList) LiftLL :=
  RelIso.IsWellOrder.preimage LL Equiv.ulift

theorem lift_omega_npow (n : ℕ) :
    Ordinal.lift.{u, 0} ((ω : Ordinal.{0}) ^ n) =
      ((ω : Ordinal.{u}) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Lifting the countable ordinal `ω ^ ω` does not change its expression.
This universe bookkeeping lemma is needed to transport the concrete list
model (which lives in `Type`) into the universe of the public statement. -/
theorem lift_omega_omega :
    Ordinal.lift.{u, 0} ((ω : Ordinal.{0}) ^ (ω : Ordinal.{0})) =
      ((ω : Ordinal.{u}) ^ (ω : Ordinal.{u})) := by
  apply le_antisymm
  · apply le_of_forall_lt
    intro a ha
    rcases Ordinal.lt_lift_iff.mp ha with ⟨a', ha', rfl⟩
    rcases (Ordinal.lt_omega0_opow Ordinal.omega0_ne_zero).mp ha' with
      ⟨c, hc, n, hn⟩
    rcases Ordinal.lt_omega0.mp hc with ⟨k, rfl⟩
    rw [← Ordinal.lift_lt] at hn
    refine hn.trans ?_
    simp only [Ordinal.lift_mul, Ordinal.lift_natCast,
      Ordinal.opow_natCast, lift_omega_npow]
    simpa [Ordinal.opow_natCast] using
      (Ordinal.opow_mul_lt_opow
        (b := (ω : Ordinal.{u})) (u := (k : Ordinal.{u}))
        (v := (n : Ordinal.{u})) (x := (ω : Ordinal.{u}))
        (Ordinal.natCast_lt_omega0 n) (Ordinal.natCast_lt_omega0 k))
  · apply le_of_forall_lt
    intro a ha
    rcases (Ordinal.lt_omega0_opow Ordinal.omega0_ne_zero).mp ha with
      ⟨c, hc, n, hn⟩
    rcases Ordinal.lt_omega0.mp hc with ⟨k, rfl⟩
    refine hn.trans ?_
    rw [Ordinal.opow_natCast]
    rw [← lift_omega_npow k, ← Ordinal.lift_natCast.{u, 0} n,
      ← Ordinal.lift_mul.{u, 0}, Ordinal.lift_lt]
    simpa [Ordinal.opow_natCast] using
      (Ordinal.opow_mul_lt_opow
        (b := (ω : Ordinal.{0})) (u := (k : Ordinal.{0}))
        (v := (n : Ordinal.{0})) (x := (ω : Ordinal.{0}))
        (Ordinal.natCast_lt_omega0 n) (Ordinal.natCast_lt_omega0 k))

noncomputable def incListOrdinalRelIso :
    LiftLL ≃r ((· < ·) : (ω ^ ω : Ordinal.{u}).ToType →
      (ω ^ ω : Ordinal.{u}).ToType → Prop) := by
  apply Classical.choice
  apply Ordinal.type_eq.mp
  change Ordinal.type (ULift.down ⁻¹'o LL) = _
  rw [Ordinal.type_ulift]
  have hi : Ordinal.type LL = (ω ^ ω : Ordinal) := incList_type
  rw [hi, Ordinal.type_toType]
  exact lift_omega_omega

theorem three_point_set_cardinal {α : Type*} {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    #(Set.insert x (Set.insert y {z})) = 3 := by
  classical
  rw [show Set.insert x (Set.insert y {z}) = (↑({x, y, z} : Finset α) : Set α) by
    ext a
    constructor
    · intro ha
      rcases Set.mem_insert_iff.mp ha with h | ha
      · simp [h]
      · rcases Set.mem_insert_iff.mp ha with h | ha
        · simp [h]
        · simp only [Set.mem_singleton_iff] at ha
          simp [ha]
    · intro ha
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with h | h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_insert_iff.mpr (Or.inl h)))
      · exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton_iff.mpr h))))]
  simp [hxy, hxz, hyz]

theorem isClique_three {V : Type*} (G : SimpleGraph V) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.IsClique (Set.insert x (Set.insert y {z})) := by
  intro a ha b hb hab
  change a = x ∨ a = y ∨ a = z at ha
  change b = x ∨ b = y ∨ b = z at hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (hab rfl).elim
  · exact hxy
  · exact hxz
  · exact hxy.symm
  · exact (hab rfl).elim
  · exact hyz
  · exact hxz.symm
  · exact hyz.symm
  · exact (hab rfl).elim

theorem erdos_590_of_levelRed
    (hlevel : ∀ (color : IncList → IncList → Bool),
      (∀ x y, color x y = color y x) →
      (∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
        ¬ (color x y = true ∧ color x z = true ∧ color y z = true)) →
      Nonempty (LevelRedEmbedding color)) :
    OrdinalCardinalRamsey (ω ^ ω : Ordinal.{u})
      (ω ^ ω : Ordinal.{u}) (3 : Cardinal.{u}) := by
  classical
  intro red blue hcompl
  by_cases hblue : ∃ s, blue.IsClique s ∧ #s = 3
  · exact Or.inr hblue
  · apply Or.inl
    let e := incListOrdinalRelIso.{u}
    let color : IncList → IncList → Bool := fun x y ↦
      if blue.Adj (e (ULift.up x)) (e (ULift.up y)) then true else false
    have hcomm : ∀ x y, color x y = color y x := by
      intro x y
      simp only [color]
      rw [blue.adj_comm]
    have htri : ∀ x y z : IncList, x ≠ y → x ≠ z → y ≠ z →
        ¬ (color x y = true ∧ color x z = true ∧ color y z = true) := by
      intro x y z hxy hxz hyz h
      have hxy' : blue.Adj (e (ULift.up x)) (e (ULift.up y)) := by
        simpa [color] using h.1
      have hxz' : blue.Adj (e (ULift.up x)) (e (ULift.up z)) := by
        simpa [color] using h.2.1
      have hyz' : blue.Adj (e (ULift.up y)) (e (ULift.up z)) := by
        simpa [color] using h.2.2
      apply hblue
      refine ⟨Set.insert (e (ULift.up x))
        (Set.insert (e (ULift.up y)) {e (ULift.up z)}),
        isClique_three blue hxy' hxz' hyz', ?_⟩
      exact three_point_set_cardinal
        (fun h' ↦ hxy (ULift.up_injective (e.injective h')))
        (fun h' ↦ hxz (ULift.up_injective (e.injective h')))
        (fun h' ↦ hyz (ULift.up_injective (e.injective h')))
    let level := Classical.choice (hlevel color hcomm htri)
    let upEmb : LL ↪r LiftLL :=
      RelEmbedding.ofMonotone ULift.up (fun _ _ h ↦ h)
    let emb := (larsonEmbedding color hcomm htri level).trans
      (upEmb.trans e.toRelEmbedding)
    let S : Set (ω ^ ω).ToType := Set.range emb
    refine ⟨S, ?_, ?_⟩
    · intro x hx y hy hxy
      rcases hx with ⟨s, rfl⟩
      rcases hy with ⟨t, rfl⟩
      have hst : s ≠ t := fun h ↦ hxy (congrArg emb h)
      have hc := larsonEmbedding_color_false color hcomm htri level hst
      have hnot : ¬ blue.Adj (emb s) (emb t) := by
        change ¬ blue.Adj
          (e (ULift.up (larsonEmbedding color hcomm htri level s)))
          (e (ULift.up (larsonEmbedding color hcomm htri level t)))
        simpa [color] using hc
      rw [hcompl.eq_compl]
      exact (blue.compl_adj _ _).2 ⟨hxy, hnot⟩
    · letI : IsWellOrder S (fun x y ↦ x.1 < y.1) := {
        wf := InvImage.wf Subtype.val
          (inferInstance : IsWellOrder (ω ^ ω : Ordinal.{u}).ToType (· < ·)).wf
        trichotomous a b hab hba := by
          rcases lt_trichotomy a.1 b.1 with h | h | h
          · exact (hab h).elim
          · exact Subtype.ext h
          · exact (hba h).elim }
      have htype := (relEmbeddingRangeRelIso emb).ordinal_lift_type_eq
      rw [rawShortlex_type] at htype
      change Ordinal.type (fun x y : S ↦ x.1 < y.1) =
        (ω ^ ω : Ordinal.{u})
      calc
        _ = Ordinal.lift.{0, u}
            (Ordinal.type (fun x y : S ↦ x.1 < y.1)) :=
          (Ordinal.lift_uzero _).symm
        _ = Ordinal.lift.{u, 0} (ω ^ ω : Ordinal.{0}) := htype.symm
        _ = (ω ^ ω : Ordinal.{u}) := lift_omega_omega

/-- **Erdős Problem 590 (Chang).**  Every red/blue coloring of the pairs of
`ω^ω` has either a red subset of order type `ω^ω` or a blue triangle. -/
theorem erdos_590 :
    OrdinalCardinalRamsey (ω ^ ω : Ordinal.{u})
      (ω ^ ω : Ordinal.{u}) (3 : Cardinal.{u}) :=
  erdos_590_of_levelRed (fun color hcomm htri ↦
    Nonempty.intro (levelRedEmbedding color hcomm htri))


/-! ## Elementary graph translation -/

theorem clique_of_no_blue_triangle
    {V : Type*} (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    {s : Set V} (hs : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ¬ blue.Adj x y) :
    red.IsClique s := by
  intro x hx y hy hxy
  have hnot : ¬ blue.Adj x y := hs hx hy hxy
  rw [hcompl.eq_compl]
  exact (blue.compl_adj x y).2 ⟨hxy, hnot⟩

end Larson

/-- **Erdős Problem 590 (Chang), in the namespace and type of the published
Formal Conjectures specification.** -/
theorem erdos_590 :
    OrdinalCardinalRamsey (ω ^ ω : Ordinal.{u})
      (ω ^ ω : Ordinal.{u}) (3 : Cardinal.{u}) :=
  Larson.erdos_590

end Erdos590
