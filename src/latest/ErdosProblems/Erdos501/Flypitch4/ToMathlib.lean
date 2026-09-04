/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/to_mathlib.lean -/

import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.Sets.Opens
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Basic

set_option relaxedAutoImplicit true

universe u v w w'

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Renames (for downstream file porters, search counts in src/)

1. `imp_self` → `ba_imp_self` (renamed to avoid collision with Lean 4 core `imp_self`)
   - Call sites: `src/henkin.lean:210`, `src/fol.lean:2097` (2 sites)

2. `le_trans'` → `le_trans_inf` (renamed to avoid collision with mathlib4 `ge_trans` alias and
   Lean 4 core `le_trans'` for lists)
   - Call sites: `src/bfol.lean:706`, `src/bvm.lean:64`, `:2475`, `:2481`,
   `src/bvm_extras.lean:2121`, `:2124` (6 sites)

3. `mk_union_le` → `mk_union_le_impl` (kept as wrapper; mathlib4 has `Cardinal.mk_union_le`)
   - Call site: `src/collapse.lean:570` — when collapse is ported, prefer
   `Cardinal.mk_union_le` over our wrapper

4. `nontrivial.bot_lt_top` → `nontrivial_bot_lt_top` (flattened from sub-namespace dot notation;
   class accessor pattern changes in Lean 4)
   - Call sites: `src/bfol.lean:790`, `src/bvm.lean:1596`, `src/zfc.lean:519`, `:534` (4 sites)

### Drops (declarations removed because they exist in mathlib4)

1. `congr1` and `rexact` tactics (src/to_mathlib.lean:492-510)
   - `congr1` was a custom tactic used in ~10 downstream Lean 3 proof sites
   - In Lean 4, `congr 1` (with a space) is a built-in tactic
   - When porting `fol`, `henkin`, `language_extension`, etc., translate `congr1` (no space) to
   `congr 1` (with space) inline rather than re-implementing

2. `complete_degenerate_boolean_algebra` (src/to_mathlib.lean:756)
   - Replaced by mathlib4's `PUnit.instCompleteBooleanAlgebra` in
   `Mathlib/Order/CompleteBooleanAlgebra.lean`
   - No downstream `src/` file uses this directly
-/

/-!
## function namespace

`Function.Injective.ne_iff` already exists in mathlib4. No redeclaration needed.
-/

/-! ## dvector type and namespace -/

/-- Dependent-length vector: a list of exactly `n` elements of type `α`. -/
inductive DVec (α : Type u) : ℕ → Type u
  | nil  : DVec α 0
  | cons : ∀ {n} (x : α) (xs : DVec α n), DVec α (n + 1)

/-- Finite type with `n` elements, used with `DVec`. -/
inductive DFin : ℕ → Type
  | fz {n} : DFin (n + 1)
  | fs {n} : DFin n → DFin (n + 1)

instance haszeroDFin {n} : Zero (DFin (n + 1)) := ⟨DFin.fz⟩

namespace DVec

variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected theorem zero_eq : ∀ (xs : DVec α 0), xs = DVec.nil
  | DVec.nil => rfl

@[simp] protected def concat : ∀ {n : ℕ}, DVec α n → α → DVec α (n + 1)
  | _, DVec.nil, x' => DVec.cons x' DVec.nil
  | _, DVec.cons x xs, x' => DVec.cons x (DVec.concat xs x')

@[simp] protected def nth : ∀ {n : ℕ}, DVec α n → (m : ℕ) → m < n → α
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons x _, 0, _ => x
  | _, DVec.cons _ xs, m + 1, h => DVec.nth xs m (Nat.lt_of_succ_lt_succ h)

protected theorem nth_cons {n : ℕ} (x : α) (xs : DVec α n) (m : ℕ) (h : m < n) :
    DVec.nth (DVec.cons x xs) (m + 1) (Nat.succ_lt_succ h) = DVec.nth xs m h := rfl

@[reducible, simp] protected def last {n : ℕ} (xs : DVec α (n + 1)) : α :=
  xs.nth n (Nat.lt_succ_self n)

protected def nth' {n : ℕ} (xs : DVec α n) (m : Fin n) : α := xs.nth m.1 m.2

protected def nth'' : ∀ {n : ℕ}, DVec α n → DFin n → α
  | _, DVec.cons x _, DFin.fz => x
  | _, DVec.cons _ xs, DFin.fs m => DVec.nth'' xs m

protected def mem : ∀ {n : ℕ}, α → DVec α n → Prop
  | _, _, DVec.nil => False
  | _, x, DVec.cons x' xs => x = x' ∨ DVec.mem x xs

instance membershipDVec {n : ℕ} : Membership α (DVec α n) :=
  ⟨fun xs a => DVec.mem a xs⟩

protected def pmem : ∀ {n : ℕ}, α → DVec α n → Type
  | _, _, DVec.nil => Empty
  | _, x, DVec.cons x' xs => PSum (x = x') (DVec.pmem x xs)

protected theorem mem_of_pmem : ∀ {n : ℕ} {x : α} {xs : DVec α n}, DVec.pmem x xs → x ∈ xs
  | _, _, DVec.nil, hx => hx.elim
  | _, x, DVec.cons x' xs, hx => by
    -- x ∈ DVec.cons x' xs = DVec.mem x (DVec.cons x' xs) = x = x' ∨ DVec.mem x xs
    show DVec.mem x (DVec.cons x' xs)
    exact hx.casesOn (fun h => Or.inl h) (fun h => Or.inr (DVec.mem_of_pmem h))

@[simp] protected def map (f : α → β) : ∀ {n : ℕ}, DVec α n → DVec β n
  | _, DVec.nil => DVec.nil
  | _, DVec.cons x xs => DVec.cons (f x) (DVec.map f xs)

@[simp] protected def map2 (f : α → β → γ) : ∀ {n : ℕ}, DVec α n → DVec β n → DVec γ n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (f x y) (DVec.map2 f xs ys)

@[simp] protected theorem map_id : ∀ {n : ℕ} (xs : DVec α n), DVec.map (fun x => x) xs = xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_id xs]

@[simp] protected theorem map_congr_pmem {f g : α → β} :
    ∀ {n : ℕ} {xs : DVec α n}, (∀ x, DVec.pmem x xs → f x = g x) →
      DVec.map f xs = DVec.map g xs
  | _, DVec.nil, _ => rfl
  | _, DVec.cons x xs, h => by
    simp only [DVec.map]
    congr 1
    · exact h x (PSum.inl rfl)
    · exact DVec.map_congr_pmem (fun x' hx' => h x' (PSum.inr hx'))

@[simp] protected theorem map_congr_mem {f g : α → β} {n : ℕ} {xs : DVec α n}
    (h : ∀ x, x ∈ xs → f x = g x) : DVec.map f xs = DVec.map g xs :=
  DVec.map_congr_pmem (fun x hx => h x (DVec.mem_of_pmem hx))

@[simp] protected theorem map_congr {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ {n : ℕ} (xs : DVec α n), DVec.map f xs = DVec.map g xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, h, DVec.map_congr h xs]

@[simp] protected theorem map_map (g : β → γ) (f : α → β) : ∀ {n : ℕ} (xs : DVec α n),
    DVec.map g (DVec.map f xs) = DVec.map (fun x => g (f x)) xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_map g f xs]

protected theorem map_inj {f : α → β} (hf : ∀ {x x'}, f x = f x' → x = x') {n : ℕ}
    {xs xs' : DVec α n} (h : DVec.map f xs = DVec.map f xs') : xs = xs' := by
  induction xs with
  | nil => exact (DVec.zero_eq xs').symm
  | cons x xs ih =>
    cases xs' with
    | cons x' xs' =>
      simp only [DVec.map] at h
      congr 1
      · exact hf (DVec.cons.inj h).1
      · exact ih (DVec.cons.inj h).2

@[simp] protected theorem map_concat (f : α → β) : ∀ {n : ℕ} (xs : DVec α n) (x : α),
    DVec.map f (DVec.concat xs x) = DVec.concat (DVec.map f xs) (f x)
  | _, DVec.nil, _ => rfl
  | _, DVec.cons _ xs, x' => by simp [DVec.map, DVec.concat, DVec.map_concat f xs x']

@[simp] protected theorem map_nth (f : α → β) : ∀ {n : ℕ} (xs : DVec α n) (m : ℕ) (h : m < n),
    DVec.nth (DVec.map f xs) m h = f (DVec.nth xs m h)
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons _ _, 0, _ => rfl
  | _, DVec.cons _ xs, m + 1, h => DVec.map_nth f xs m _

protected theorem concat_nth : ∀ {n : ℕ} (xs : DVec α n) (x : α) (m : ℕ) (h' : m < n + 1)
    (h : m < n), DVec.nth (DVec.concat xs x) m h' = DVec.nth xs m h
  | _, DVec.nil, _, m, _, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons _ _, _, 0, _, _ => rfl
  | _, DVec.cons _ xs, x', m + 1, h', h => by
    simp only [DVec.concat, DVec.nth]
    exact DVec.concat_nth xs x' m _ _

@[simp] protected theorem concat_nth_last : ∀ {n : ℕ} (xs : DVec α n) (x : α) (h : n < n + 1),
    DVec.nth (DVec.concat xs x) n h = x
  | _, DVec.nil, _, _ => rfl
  | _, DVec.cons _ xs, x', h => by simp [DVec.concat, DVec.nth, DVec.concat_nth_last xs x']

@[simp] protected theorem concat_nth_last' : ∀ {n : ℕ} (xs : DVec α n) (x : α) (h : n < n + 1),
    DVec.last (DVec.concat xs x) = x := DVec.concat_nth_last

@[simp] protected def append : ∀ {n m : ℕ}, DVec α n → DVec α m → DVec α (m + n)
  | _, _, DVec.nil, xs => xs
  | _, _, DVec.cons x' xs, xs' => DVec.cons x' (DVec.append xs xs')

@[simp] protected def insert : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α (n + 1)
  | n, x, 0, xs => DVec.cons x xs
  | 0, x, _, _ => DVec.cons x DVec.nil
  | n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.insert x k ys)

@[simp] protected theorem insert_at_zero : ∀ {n : ℕ} (x : α) (xs : DVec α n),
    DVec.insert x 0 xs = DVec.cons x xs := by
  intro n; cases n <;> intros <;> rfl

@[simp] protected theorem insert_nth : ∀ {n : ℕ} (x : α) (k : ℕ) (xs : DVec α n) (h : k < n + 1),
    DVec.nth (DVec.insert x k xs) k h = x
  | 0, x, 0, _, _ => rfl
  | 0, x, k + 1, _, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | n + 1, x, 0, _, _ => by simp [DVec.insert, DVec.nth]
  | n + 1, x, k + 1, DVec.cons _ ys, h => by
    simp only [DVec.insert, DVec.nth]
    exact DVec.insert_nth x k ys _

protected theorem insert_cons {n k} {x y : α} {v : DVec α n} :
    DVec.cons x (DVec.insert y k v) = DVec.insert y (k + 1) (DVec.cons x v) := by
  induction v with
  | nil => rfl
  | cons _ _ _ => simp [DVec.insert]

/-- The n-th initial segment of a vector, given a proof that n ≤ m. -/
@[simp] protected def trunc : ∀ (n) {m : ℕ}, n ≤ m → DVec α m → DVec α n
  | 0, 0, _, _ => DVec.nil
  | 0, _ + 1, _, _ => DVec.nil
  | n + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero n)
  | n + 1, m + 1, h, DVec.cons x xs =>
    DVec.cons x (DVec.trunc n (Nat.lt_succ_iff.mp (Nat.lt_of_succ_le h)) xs)

@[simp] protected theorem trunc_n_n {n : ℕ} {h : n ≤ n} {v : DVec α n} :
    DVec.trunc n h v = v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [DVec.trunc, ih]

@[simp] protected theorem trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : DVec α n} :
    DVec.trunc 0 h v = DVec.nil := by cases v <;> rfl

@[simp] protected theorem trunc_nth {n m l : ℕ} {h : n ≤ m} {h' : l < n} {v : DVec α m} :
    DVec.nth (DVec.trunc n h v) l h' = DVec.nth v l (Nat.lt_of_lt_of_le h' h) := by
  induction m generalizing n l with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero h
    subst this; exact absurd h' (Nat.not_lt_zero _)
  | succ m ih =>
    cases n with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ n =>
      cases l with
      | zero =>
        cases v with
        | cons _ _ => rfl
      | succ l =>
        cases v with
        | cons _ vs =>
          show DVec.nth (DVec.trunc n _ vs) l _ = DVec.nth vs l _
          apply ih

protected theorem nth_irrel1 {n k : ℕ} {h : k < n + 1} {h' : k < n + 1 + 1}
    (v : DVec α (n + 1)) (x : α) :
    DVec.nth (DVec.cons x (DVec.trunc n (Nat.le_succ n) v)) k h =
    DVec.nth (DVec.cons x v) k h' := by
  cases k with
  | zero => rfl
  | succ k =>
    show DVec.nth (DVec.trunc n _ v) k _ = DVec.nth v k _
    rw [DVec.trunc_nth]

protected def cast {n m} (p : n = m) (v : DVec α n) : DVec α m := p ▸ v

@[simp] protected theorem cast_irrel {n m} {p p' : n = m} {v : DVec α n} :
    DVec.cast p v = DVec.cast p' v := rfl

@[simp] protected theorem cast_rfl {n m} {p : n = m} {q : m = n} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = v := by subst p; rfl

protected theorem cast_hrfl {n m} {p : n = m} {v : DVec α n} : HEq (DVec.cast p v) v := by
  subst p; rfl

@[simp] protected theorem cast_trans {n m o} {p : n = m} {q : m = o} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = DVec.cast (p.trans q) v := by subst p; subst q; rfl

@[simp] theorem cast_cons {n m} (h : n + 1 = m + 1) (x : α) (v : DVec α n) :
    DVec.cast h (DVec.cons x v) = DVec.cons x (DVec.cast (Nat.succ_injective h) v) := by
  cases h; rfl

@[simp] theorem cast_append_nil : ∀ {n} (v : DVec α n) (h : 0 + n = n),
    DVec.cast h (DVec.append v DVec.nil) = v
  | _, DVec.nil, _ => rfl
  | _, DVec.cons x v, h => by
    simp only [DVec.append, cast_cons]
    congr 1
    exact cast_append_nil v (by omega)

@[simp] protected def remove_mth : ∀ {n : ℕ}, ℕ → DVec α (n + 1) → DVec α n
  | 0, _, _ => DVec.nil
  | n, 0, DVec.cons _ ys => ys
  | n + 1, k + 1, DVec.cons y ys => DVec.cons y (DVec.remove_mth k ys)

@[simp] protected def replace : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α n
  | _, x, 0, DVec.cons _ ys => DVec.cons x ys
  | 0, _, _, ys => ys
  | n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.replace x k ys)

protected theorem insert_nth_lt {n k l : ℕ} (x : α) (xs : DVec α n) (h : l < n)
    (h' : l < n + 1) (h2 : l < k) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs l h := by
  induction xs generalizing k l with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x' xs ih =>
    cases k with
    | zero => exact absurd h2 (Nat.not_lt_zero _)
    | succ k =>
      cases l with
      | zero => rfl
      | succ l =>
        simp only [DVec.insert, DVec.nth]
        exact ih (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')
          (Nat.lt_of_succ_lt_succ h2)

protected theorem insert_nth_gt' {n k l : ℕ} (x : α) (xs : DVec α n)
    (h : l - 1 < n) (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) h := by
  induction xs generalizing k l with
  | nil =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h (Nat.not_lt_zero _)
      | succ l => exact absurd h' (by omega)
  | cons x' xs ih =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l =>
        cases l with
        | zero => exact absurd h2 (by omega)
        | succ l =>
          simp only [DVec.insert, DVec.nth, add_tsub_cancel_right]
          have := ih (k := k) (l := l + 1) (by omega) (Nat.lt_of_succ_lt_succ h') (by omega)
          simp at this ⊢
          convert this using 2 <;> omega

@[simp] protected theorem insert_nth_gt_simp {n k l : ℕ} (x : α) (xs : DVec α n)
    (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) (by omega) :=
  DVec.insert_nth_gt' x xs (by omega) h' h2

protected theorem insert_nth_gt {n k l : ℕ} (x : α) (xs : DVec α n) (h : l < n)
    (h' : l + 1 < n + 1) (h2 : k < l + 1) :
    DVec.nth (DVec.insert x k xs) (l + 1) h' = DVec.nth xs l h :=
  DVec.insert_nth_gt' x xs h h' h2

@[simp] lemma replace_head {n x z} {xs : DVec α n} :
    DVec.replace z 0 (DVec.cons x xs) = DVec.cons z xs := rfl

@[simp] lemma replace_neck {n x y z} {xs : DVec α n} :
    DVec.replace z 1 (DVec.cons x (DVec.cons y xs)) = DVec.cons x (DVec.cons z xs) := rfl

@[simp] def foldr (f : α → β → β) (b : β) : ∀ {n}, DVec α n → β
  | _, DVec.nil => b
  | _, DVec.cons a l => f a (DVec.foldr f b l)

@[simp] def zip : ∀ {n}, DVec α n → DVec β n → DVec (α × β) n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (x, y) (DVec.zip xs ys)

/-- The finitary infimum -/
def fInf [SemilatticeInf α] [OrderTop α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊓ b) ⊤ xs

@[simp] lemma fInf_nil [SemilatticeInf α] [OrderTop α] : fInf (DVec.nil (α := α)) = ⊤ := rfl

@[simp] lemma fInf_cons [SemilatticeInf α] [OrderTop α] (x : α) (xs : DVec α n) :
    fInf (DVec.cons x xs) = x ⊓ fInf xs := rfl

/-- The finitary supremum -/
def fSup [SemilatticeSup α] [OrderBot α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊔ b) ⊥ xs

@[simp] lemma fSup_nil [SemilatticeSup α] [OrderBot α] : fSup (DVec.nil (α := α)) = ⊥ := rfl

@[simp] lemma fSup_cons [SemilatticeSup α] [OrderBot α] (x : α) (xs : DVec α n) :
    fSup (DVec.cons x xs) = x ⊔ fSup xs := rfl

/-- Pointwise relation on DVec, given a setoid on the element type -/
inductive DVecRel {α : Type u} [Setoid α] : ∀ {n : ℕ}, DVec α n → DVec α n → Prop
  | rnil : DVecRel DVec.nil DVec.nil
  | rcons {x x' : α} {n : ℕ} {xs xs' : DVec α n} (hx : x ≈ x') (hxs : DVecRel xs xs') :
      DVecRel (DVec.cons x xs) (DVec.cons x' xs')

protected theorem rel_refl {α : Type u} [Setoid α] {n} (xs : DVec α n) : DVecRel xs xs := by
  induction xs with
  | nil => exact DVecRel.rnil
  | cons _ _ ih => exact DVecRel.rcons (Setoid.refl _) ih

protected theorem rel_symm {α : Type u} [Setoid α] {n} {xs xs' : DVec α n}
    (h : DVecRel xs xs') : DVecRel xs' xs := by
  induction h with
  | rnil => exact DVecRel.rnil
  | rcons hx _ ih => exact DVecRel.rcons (Setoid.symm hx) ih

protected theorem rel_trans {α : Type u} [Setoid α] {n} {xs₁ xs₂ xs₃ : DVec α n}
    (h₁ : DVecRel xs₁ xs₂) (h₂ : DVecRel xs₂ xs₃) : DVecRel xs₁ xs₃ := by
  induction h₁ with
  | rnil => exact h₂
  | rcons hx _ ih =>
    cases h₂ with
    | rcons hx₂ hxs₂ => exact DVecRel.rcons (Setoid.trans hx hx₂) (ih hxs₂)

instance setoidInst {α : Type u} [Setoid α] {n : ℕ} : Setoid (DVec α n) :=
  ⟨DVecRel, DVec.rel_refl, DVec.rel_symm, DVec.rel_trans⟩

noncomputable def quotient_lift {α : Type u} {β : Sort v} {R : Setoid α} :
    ∀ {n} (f : DVec α n → β)
    (_h : ∀ {xs xs' : DVec α n}, xs ≈ xs' → f xs = f xs')
    (qs : DVec (Quotient R) n), β
  | 0, f, _, DVec.nil => f DVec.nil
  | n + 1, f, h, DVec.cons q qs =>
    Quotient.lift
      (fun x => DVec.quotient_lift
        (fun xs => f (DVec.cons x xs))
        (fun hxs => h (DVecRel.rcons (Setoid.refl x) hxs))
        qs)
      (fun x x' hx => by
        try simp only
        congr 1; apply funext; intro xs
        apply h; exact DVecRel.rcons hx (DVec.rel_refl xs))
      q

theorem quotient_beta {α : Type u} {β : Sort v} {R : Setoid α} :
    ∀ {n} (f : DVec α n → β)
    (h : ∀ {xs xs' : DVec α n}, xs ≈ xs' → f xs = f xs') (xs : DVec α n),
    DVec.quotient_lift f h (DVec.map Quotient.mk'' xs) = f xs
  | 0, f, h, DVec.nil => rfl
  | n + 1, f, h, DVec.cons x xs => by
    simp only [DVec.map, DVec.quotient_lift, Quotient.lift_mk]
    exact quotient_beta
      (fun xs' => f (DVec.cons x xs'))
      (fun hxs => h (DVecRel.rcons (Setoid.refl x) hxs))
      xs

end DVec

/-! ## set namespace -/

namespace Set

theorem disjoint_iff_eq_empty {α} {s t : Set α} : Disjoint s t ↔ s ∩ t = ∅ := by
  rw [Set.disjoint_iff_inter_eq_empty]

@[simp] theorem not_nonempty_iff {α} {s : Set α} : ¬Nonempty s ↔ s = ∅ := by
  rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty]

theorem neq_neg_of_nonempty {α : Type*} {P : Set α} (H_nonempty : Nonempty α) : P ≠ Pᶜ := by
  intro H_eq
  obtain ⟨a⟩ := H_nonempty
  by_cases HP : a ∈ P
  · -- a ∈ P, so by H_eq, a ∈ Pᶜ, i.e., a ∉ P — contradiction
    have : a ∈ Pᶜ := H_eq ▸ HP
    exact this HP
  · -- a ∉ P, so a ∈ Pᶜ, so by H_eq, a ∈ P — contradiction
    have : a ∈ Pᶜ := HP
    rw [← H_eq] at this
    exact HP this

@[simp] theorem subset_biInter_iff {α β} {s : Set α} {t : Set β} {u : α → Set β} :
    t ⊆ ⋂ x ∈ s, u x ↔ ∀ x ∈ s, t ⊆ u x :=
  Set.subset_iInter₂_iff

-- subset_sInter_iff is already in Mathlib as Set.subset_sInter_iff

theorem ne_empty_of_subset {α} {s t : Set α} (h : s ⊆ t) (hs : s ≠ ∅) : t ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp ((Set.nonempty_iff_ne_empty.mpr hs).mono h)

end Set

/-! ## topological_space section -/

section TopologicalSpace

open TopologicalSpace Set Filter

variable {α : Type u} {β : Type v}
variable [t : TopologicalSpace α] [TopologicalSpace β]

theorem subbasis_subset_basis {s : Set (Set α)} :
    s \ {∅} ⊆ (fun f => ⋂₀ f) '' {f : Set (Set α) | f.Finite ∧ f ⊆ s ∧ ⋂₀ f ≠ ∅} := by
  intro o ho
  refine ⟨{o}, ⟨Set.finite_singleton o, ?_, ?_⟩, ?_⟩
  · rw [Set.singleton_subset_iff]; exact ho.1
  · rw [Set.sInter_singleton]; exact mt Set.mem_singleton_iff.mpr ho.2
  · simp

theorem mem_opens {x : α} {o : TopologicalSpace.Opens α} : x ∈ o ↔ x ∈ o.1 := Iff.rfl

theorem isOpenMap_of_isTopologicalBasis {s : Set (Set α)}
    (hs : IsTopologicalBasis s) (f : α → β) (hf : ∀ x ∈ s, IsOpen (f '' x)) :
    IsOpenMap f := by
  intro o ho
  obtain ⟨t, ht, rfl⟩ := hs.open_eq_sUnion ho
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro i ⟨j, hj, rfl⟩
  exact hf j (ht hj)

theorem interior_biInter_subset {ι : Type*} {s : Set ι} (f : ι → Set α) :
    interior (⋂ i ∈ s, f i) ⊆ ⋂ i ∈ s, interior (f i) := by
  intro x hx
  simp only [Set.mem_iInter]
  intro y hy
  exact interior_mono (Set.iInter₂_subset y hy) hx

theorem nonempty_basis_subset {b : Set (Set α)}
    (hb : IsTopologicalBasis b) {u : Set α} (hu : u ≠ ∅) (ou : IsOpen u) :
    ∃ v ∈ b, v ≠ ∅ ∧ v ⊆ u := by
  rw [ne_eq, ← Set.not_nonempty_iff_eq_empty, not_not] at hu
  obtain ⟨x, hx⟩ := hu
  obtain ⟨v, hv, hvx, hvu⟩ := hb.mem_nhds_iff.mp (ou.mem_nhds hx)
  exact ⟨v, hv, Set.nonempty_iff_ne_empty.mp ⟨x, hvx⟩, hvu⟩

end TopologicalSpace

/-! ## ordinal namespace -/

namespace Ordinal

variable {σ : Type*}

theorem well_ordering_thm : ∃ (r : σ → σ → Prop), IsWellOrder σ r :=
  ⟨WellOrderingRel, WellOrderingRel.isWellOrder⟩

theorem enum_typein' {α : Type u} (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    Ordinal.enum r ⟨typein r a, typein_lt_type r a⟩ = a :=
  Ordinal.enum_typein r a

end Ordinal

/-! ## cardinal namespace -/

namespace Cardinal

open scoped Cardinal

-- Note: Cardinal.mk_union_le already exists in mathlib4 (explicit args version).
-- Downstream files use `mk_union_le` with implicit args; that's directly served
-- by the mathlib4 version since Lean can infer the args. No redeclaration needed.
-- The alias below makes it available for direct call without name conflicts:
theorem mk_union_le_impl {α : Type u} {S T : Set α} : #(S ∪ T : Set α) ≤ #S + #T :=
  Cardinal.mk_union_le S T

theorem exists_mem_compl_of_mk_lt_mk {α} (P : Set α) (H_lt : #P < #α) : ∃ x : α, x ∈ Pᶜ := by
  by_contra h
  push_neg at h
  have ha : ∀ x, x ∈ P := fun x => by_contra (fun hx => h x hx)
  have : #α ≤ #P := Cardinal.mk_le_of_injective (f := fun x => (⟨x, ha x⟩ : P))
    (fun x y hxy => Subtype.mk.inj hxy)
  exact absurd H_lt (not_lt.mpr this)

@[simp] theorem mk_union_countable_of_countable {α} {P Q : Set α}
    (HP : #P ≤ ℵ₀) (HQ : #Q ≤ ℵ₀) : #(P ∪ Q : Set α) ≤ ℵ₀ :=
  (Cardinal.mk_union_le P Q).trans (Cardinal.add_le_aleph0.mpr ⟨HP, HQ⟩)

theorem nonzero_of_regular {κ : Cardinal} (H_reg : Cardinal.IsRegular κ) : 0 < κ.ord :=
  H_reg.ord_pos

theorem injection_of_mk_le {α β : Type u} (H_le : #α ≤ #β) : ∃ f : α → β, Function.Injective f :=
  let ⟨⟨f, hf⟩⟩ := (Cardinal.le_def α β).mp H_le
  ⟨f, hf⟩

end Cardinal

/-! ## nat namespace -/

namespace Nat

protected theorem pred_lt_iff_lt_succ {m n : ℕ} (H : 1 ≤ m) :
    Nat.pred m < n ↔ m < Nat.succ n := by
  simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one]
  omega

@[simp] theorem le_of_le_and_ne_succ {x y : ℕ} (H : x ≤ y + 1) (H' : x ≠ y + 1) : x ≤ y :=
  Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H H')

end Nat

/-! ## classical namespace (logic helpers) -/

namespace Classical

noncomputable def psigma_of_exists {α : Type u} {p : α → Prop} (h : ∃ x, p x) : Σ' x, p x :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

theorem some_eq {α : Type u} {p : α → Prop} {h : ∃ (a : α), p a} (x : α)
    (hx : ∀ y, p y → y = x) : Classical.choose h = x :=
  hx _ (Classical.choose_spec h)

theorem or_not_iff_true (p : Prop) : (p ∨ ¬p) ↔ True :=
  ⟨fun _ => trivial, fun _ => Classical.em p⟩

theorem nonempty_of_not_empty {α : Type u} (s : Set α) (h : ¬s = ∅) : Nonempty s :=
  Set.Nonempty.coe_sort (Set.nonempty_iff_ne_empty.mpr h)

theorem nonempty_of_not_empty_finset {α : Type u} (s : Finset α) (h : ¬s = ∅) :
    Nonempty (s : Set α) :=
  Set.Nonempty.coe_sort (Finset.nonempty_iff_ne_empty.mpr h)

end Classical

/-! ## list namespace -/

namespace List

@[simp] protected def toSet {α : Type u} (l : List α) : Set α := {x | x ∈ l}

theorem toSet_map {α : Type u} {β : Type v} (f : α → β) (l : List α) :
    (l.map f).toSet = f '' l.toSet := by
  apply Set.ext; intro b; simp [List.toSet, Set.mem_image]

theorem exists_of_toSet_subset_image {α : Type u} {β : Type v} {f : α → β} {l : List β}
    {t : Set α} (h : l.toSet ⊆ f '' t) : ∃ (l' : List α), l'.toSet ⊆ t ∧ l'.map f = l := by
  induction l with
  | nil => exact ⟨[], by simp [List.toSet], rfl⟩
  | cons hd tl ih =>
    have h_hd : hd ∈ f '' t := h (by simp [List.toSet])
    obtain ⟨x, hx, rfl⟩ := h_hd
    have h_tl : ∀ y ∈ tl.toSet, y ∈ f '' t := fun y hy => h (by
      simp only [List.toSet, Set.mem_setOf_eq, List.mem_cons]
      exact Or.inr (hy))
    obtain ⟨xs, hxs, hxs'⟩ := ih (fun y hy => h_tl y hy)
    exact ⟨x :: xs, fun y hy => by
      simp [List.toSet] at hy
      cases hy with
      | inl h => exact h ▸ hx
      | inr h => exact hxs h,
      by simp [hxs']⟩

end List

/-! ## additional nat lemmas -/

namespace Nat

theorem add_sub_swap {n k : ℕ} (h : k ≤ n) (m : ℕ) : n + m - k = n - k + m := by omega

end Nat

/-! ## misc prop lemmas -/

theorem imp_eq_congr {a b c d : Prop} (h₁ : a = b) (h₂ : c = d) : (a → c) = (b → d) := by
  subst h₁; subst h₂; rfl

theorem forall_eq_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) :
    (∀ a, p a) = ∀ a, q a := by
  have h' : p = q := funext h; subst h'; rfl

/-! ## additional set lemmas -/

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

theorem ne_empty_of_exists_mem {s : Set α} : ∀ (_ : ∃ x, x ∈ s), s ≠ ∅
  | ⟨x, hx⟩ => Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩

theorem inter_sUnion_ne_empty_of_exists_mem {b : Set α} {𝓕 : Set (Set α)}
    (H : ∃ f ∈ 𝓕, b ∩ f ≠ ∅) : b ∩ ⋃₀ 𝓕 ≠ ∅ := by
  apply ne_empty_of_exists_mem
  obtain ⟨f, hf, h⟩ := H
  rw [ne_eq, ← Set.not_nonempty_iff_eq_empty, not_not] at h
  obtain ⟨x, hx1, hx2⟩ := h
  exact ⟨x, hx1, Set.mem_sUnion.mpr ⟨f, hf, hx2⟩⟩

@[simp] theorem mem_image_univ {f : α → β} {x} : f x ∈ f '' Set.univ :=
  ⟨x, Set.mem_univ x, rfl⟩

theorem image_preimage_eq_of_subset_image {f : α → β} {s : Set β} {t : Set α}
    (h : s ⊆ f '' t) : f '' (f ⁻¹' s) = s :=
  Set.Subset.antisymm (Set.image_preimage_subset f s)
    (fun x hx => by obtain ⟨a, ha, rfl⟩ := h hx; exact Set.mem_image_of_mem f hx)

theorem subset_union_left_of_subset {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  h.trans Set.subset_union_left

theorem subset_union_right_of_subset {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  h.trans Set.subset_union_right

theorem subset_sUnion {s : Set α} {t : Set (Set α)} (h : s ∈ t) : s ⊆ ⋃₀ t :=
  Set.subset_sUnion_of_mem h

theorem subset_union2_left {s t u : Set α} : s ⊆ s ∪ t ∪ u :=
  Set.subset_union_left.trans Set.subset_union_left

theorem subset_union2_middle {s t u : Set α} : t ⊆ s ∪ t ∪ u :=
  Set.subset_union_right.trans Set.subset_union_left

def change {π : α → Type*} [DecidableEq α] (f : ∀ a, π a) {x : α} (z : π x) (y : α) : π y :=
  if h : x = y then h ▸ z else f y

theorem dif_mem_pi {π : α → Type*} (i : Set α) (s : ∀ a, Set (π a)) [DecidableEq α]
    (f : ∀ a, π a) (hf : f ∈ Set.pi i s) {x : α} (z : π x) (h : x ∈ i → z ∈ s x) :
    Set.change f z ∈ Set.pi i s := by
  intro y hy
  simp only [Set.change]
  by_cases hxy : x = y
  · rw [dif_pos hxy]; subst hxy; exact h hy
  · rw [dif_neg hxy]; exact hf y hy

theorem image_pi_pos {π : α → Type*} (i : Set α) (s : ∀ a, Set (π a)) [DecidableEq α]
    (hp : (Set.pi i s).Nonempty) (x : α) (hx : x ∈ i) :
    (fun (f : ∀ a, π a) => f x) '' Set.pi i s = s x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩; exact hf x hx
  · intro z hz
    obtain ⟨f, hf⟩ := hp
    exact ⟨Set.change f z, Set.dif_mem_pi i s f hf z (fun _ => hz),
           by simp [Set.change, dif_pos rfl]⟩

theorem image_pi_neg {π : α → Type*} (i : Set α) (s : ∀ a, Set (π a)) [DecidableEq α]
    (hp : (Set.pi i s).Nonempty) (x : α) (hx : x ∉ i) :
    (fun (f : ∀ a, π a) => f x) '' Set.pi i s = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro z
  obtain ⟨f, hf⟩ := hp
  exact ⟨Set.change f z, Set.dif_mem_pi i s f hf z (fun hxi => absurd hxi hx),
         by simp [Set.change, dif_pos rfl]⟩

end Set

/-! ## nonempty namespace -/

namespace Nonempty

variable {α : Sort u} {β : Sort v}

protected theorem iff (mp : α → β) (mpr : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map mp, Nonempty.map mpr⟩

end Nonempty

/-! ## arity' type and namespace -/

/-- The type α → (α → ... (α → β)...) with n α's. -/
def Arity' (α β : Type u) : ℕ → Type u
  | 0 => β
  | n + 1 => α → Arity' α β n

namespace Arity'

def arity'_constant {α β : Type u} : ∀ {n : ℕ}, β → Arity' α β n
  | 0, b => b
  | _ + 1, b => fun _ => arity'_constant b

@[simp] def of_dvector_map {α β : Type u} : ∀ {l} (f : DVec α l → β), Arity' α β l
  | 0, f => f DVec.nil
  | l + 1, f => fun x => of_dvector_map (fun xs => f (DVec.cons x xs))

@[simp] def arity'_app {α β : Type u} : ∀ {l}, Arity' α β l → DVec α l → β
  | _, b, DVec.nil => b
  | _, f, DVec.cons x xs => arity'_app (f x) xs

@[simp] theorem arity'_app_zero {α β : Type u} (f : Arity' α β 0) (xs : DVec α 0) :
    arity'_app f xs = f := by cases xs; rfl

def arity'_postcompose {α β γ : Type u} (g : β → γ) : ∀ {n} (f : Arity' α β n), Arity' α γ n
  | 0, b => g b
  | n + 1, f => fun x => arity'_postcompose g (f x)

def arity'_postcompose2 {α β γ δ : Type u} (h : β → γ → δ) :
    ∀ {n} (f : Arity' α β n) (g : Arity' α γ n), Arity' α δ n
  | 0, b, c => h b c
  | n + 1, f, g => fun x => arity'_postcompose2 h (f x) (g x)

def arity'_precompose {α β γ : Type u} : ∀ {n} (g : Arity' β γ n) (f : α → β), Arity' α γ n
  | 0, c, _ => c
  | n + 1, g, f => fun x => arity'_precompose (g (f x)) f

inductive arity'_respect_setoid {α β : Type u} [R : Setoid α] : ∀ {n}, Arity' α β n → Type u
  | r_zero (b : β) : @arity'_respect_setoid _ _ _ 0 b
  | r_succ (n : ℕ) (f : Arity' α β (n + 1)) (h₁ : ∀ {a a'}, a ≈ a' → f a = f a')
    (h₂ : ∀ a, arity'_respect_setoid (f a)) : arity'_respect_setoid f

instance subsingleton_arity'_respect_setoid {α β : Type u} [R : Setoid α] {n} (f : Arity' α β n) :
    Subsingleton (arity'_respect_setoid f) := by
  constructor
  intro h h'
  induction h with
  | r_zero => cases h'; rfl
  | r_succ n f _ _ ih =>
    cases h' with
    | r_succ => congr; funext x; exact ih x _

def for_all {α : Type u} (P : α → Prop) : Prop := ∀ x, P x

@[simp] def arity'_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) :
    ∀ {n}, Arity' α β n → Arity' α β n → β
  | 0, x, y => f x y
  | n + 1, x, y => q (fun z => arity'_map2 q f (x z) (y z))

@[simp] theorem arity'_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ∀ A, f A A) :
    ∀ {n} (x : Arity' α Prop n), arity'_map2 for_all f x x
  | 0, x => r x
  | n + 1, x => fun y => arity'_map2_refl r (x y)

def arity'_imp {α : Type} {n : ℕ} (f₁ f₂ : Arity' α Prop n) : Prop :=
  arity'_map2 for_all (fun P Q => P → Q) f₁ f₂

def arity'_iff {α : Type} {n : ℕ} (f₁ f₂ : Arity' α Prop n) : Prop :=
  arity'_map2 for_all Iff f₁ f₂

theorem arity'_iff_refl {α : Type} {n : ℕ} (f : Arity' α Prop n) : arity'_iff f f :=
  arity'_map2_refl Iff.refl f

theorem arity'_iff_rfl {α : Type} {n : ℕ} {f : Arity' α Prop n} : arity'_iff f f :=
  arity'_iff_refl f

end Arity'

/-! ## Miscellaneous lemmas -/

@[simp] theorem lt_irrefl' {α} [Preorder α] {Γ : α} (H_lt : Γ < Γ) : False :=
  lt_irrefl _ H_lt

/-! ## Boolean algebra / lattice helpers -/

/-- A nontrivial complete Boolean algebra has ⊥ < ⊤ -/
class NontrivialCompleteBooleanAlgebra (α : Type*) extends CompleteBooleanAlgebra α where
  bot_lt_top : (⊥ : α) < (⊤ : α)

@[simp] theorem nontrivial_bot_lt_top {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : (⊥ : α) < ⊤ :=
  H.bot_lt_top

@[simp] theorem nontrivial_bot_neq_top {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : ¬(⊥ = (⊤ : α)) :=
  ne_of_lt H.bot_lt_top

@[simp] theorem nontrivial_top_neq_bot {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : ¬(⊤ = (⊥ : α)) :=
  fun h => nontrivial_bot_neq_top h.symm

/-- Every NontrivialCompleteBooleanAlgebra is Nontrivial (witnesses: ⊥ ≠ ⊤). -/
instance (priority := 100) NontrivialCompleteBooleanAlgebra.toNontrivial {α : Type*}
    [H : NontrivialCompleteBooleanAlgebra α] : Nontrivial α :=
  ⟨⊥, ⊤, ne_of_lt H.bot_lt_top⟩

def antichain {β : Type*} [Lattice β] [OrderBot β] (s : Set β) :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x ⊓ y = (⊥ : β)

-- iSup/iInf distributivity (aliases for Lean 4 mathlib names)
theorem inf_iSup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊓ (⨆ (i : ι), s i) = ⨆ (i : ι), a ⊓ s i :=
  inf_iSup_eq a s

theorem iSup_inf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨆ (i : ι), s i) ⊓ a = ⨆ (i : ι), (s i ⊓ a) := by
  rw [inf_comm, inf_iSup_eq']; simp_rw [inf_comm]

theorem sup_iInf_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    a ⊔ (⨅ (i : ι), s i) = ⨅ (i : ι), a ⊔ s i :=
  sup_iInf_eq a s

theorem iInf_sup_eq' {α ι : Type*} [CompleteDistribLattice α] {a : α} {s : ι → α} :
    (⨅ (i : ι), s i) ⊔ a = ⨅ (i : ι), s i ⊔ a := by
  rw [sup_comm, sup_iInf_eq']; simp_rw [sup_comm]

-- Aliases without `@[simp]`: mathlib4's `inf_idem`/`sup_idem` already carry `@[simp]`,
-- so adding `@[simp]` here would create duplicate rewrite rules.
theorem inf_self {α : Type*} [Lattice α] {a : α} : a ⊓ a = a := inf_idem a

theorem sup_self {α : Type*} [Lattice α] {a : α} : a ⊔ a = a := sup_idem a

-- Note: bot_lt_iff_not_le_bot and lt_top_iff_not_top_le already exist in mathlib4

theorem false_of_bot_lt_and_le_bot {α} [Preorder α] [OrderBot α] {a : α}
    (H_lt : ⊥ < a) (H_le : a ≤ ⊥) : False :=
  absurd H_le (bot_lt_iff_not_le_bot.mp H_lt)

theorem bot_lt_resolve_left {𝔹} [Lattice 𝔹] [OrderBot 𝔹] {a b : 𝔹} (H_lt' : ⊥ < a ⊓ b) :
    ⊥ < b := by
  by_contra H
  rw [bot_lt_iff_not_le_bot] at H H_lt'
  push_neg at H
  exact H_lt' (le_trans inf_le_right H)

theorem bot_lt_resolve_right {𝔹} [Lattice 𝔹] [OrderBot 𝔹] {a b : 𝔹} (H_lt : ⊥ < b)
    (H_lt' : ⊥ < a ⊓ b) : ⊥ < a := by
  rw [inf_comm] at H_lt'; exact bot_lt_resolve_left H_lt'

theorem le_bot_iff_not_bot_lt {𝔹} [Preorder 𝔹] [OrderBot 𝔹] {a : 𝔹} : ¬⊥ < a ↔ a ≤ ⊥ := by
  rw [bot_lt_iff_not_le_bot]; tauto

/-- Material implication in a Boolean algebra -/
def imp {α : Type*} [BooleanAlgebra α] (a₁ a₂ : α) : α := a₁ᶜ ⊔ a₂

scoped[Flypitch] infixl:65 " ⟹ " => imp
open scoped Flypitch

@[reducible, simp] def biimp {α : Type*} [BooleanAlgebra α] (a₁ a₂ : α) : α :=
  imp a₁ a₂ ⊓ imp a₂ a₁

scoped[Flypitch] infixl:50 " ⇔ " => biimp

theorem biimp_mp {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} : biimp a₁ a₂ ≤ imp a₁ a₂ :=
  inf_le_left

theorem biimp_mpr {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} : biimp a₁ a₂ ≤ imp a₂ a₁ :=
  inf_le_right

theorem biimp_comm {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} : biimp a₁ a₂ = biimp a₂ a₁ := by
  unfold biimp; rw [inf_comm]

theorem biimp_symm {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} {Γ : α} :
    Γ ≤ biimp a₁ a₂ ↔ Γ ≤ biimp a₂ a₁ := by rw [biimp_comm]

@[simp] theorem imp_le_of_right_le {α : Type*} [BooleanAlgebra α] {a a₁ a₂ : α} {h : a₁ ≤ a₂} :
    imp a a₁ ≤ imp a a₂ := sup_le_sup_left h _

@[simp] theorem imp_le_of_left_le {α : Type*} [BooleanAlgebra α] {a a₁ a₂ : α} {h : a₂ ≤ a₁} :
    imp a₁ a ≤ imp a₂ a := sup_le_sup_right (compl_le_compl h) _

@[simp] theorem imp_le_of_left_right_le {α : Type*} [BooleanAlgebra α] {a₁ a₂ b₁ b₂ : α}
    {h₁ : b₁ ≤ a₁} {h₂ : a₂ ≤ b₂} : imp a₁ a₂ ≤ imp b₁ b₂ :=
  sup_le_sup (compl_le_compl h₁) h₂

theorem neg_le_neg' {α : Type*} [BooleanAlgebra α] {a b : α} : b ≤ aᶜ → a ≤ bᶜ := by
  intro H; simpa using compl_le_compl H

theorem inf_imp_eq {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ⊓ imp b c = imp (imp a b) (a ⊓ c) := by
  unfold imp
  simp only [compl_sup, compl_compl, inf_sup_left]

@[simp] theorem imp_bot {α : Type*} [BooleanAlgebra α] {a : α} : imp a ⊥ = aᶜ := by simp [imp]

@[simp] theorem top_imp {α : Type*} [BooleanAlgebra α] {a : α} : imp ⊤ a = a := by simp [imp]

@[simp] theorem ba_imp_self {α : Type*} [BooleanAlgebra α] {a : α} : imp a a = ⊤ := by
  simp [imp]
-- Note: Lean 4 already has a `imp_self` in core; use `ba_imp_self` for Boolean algebra version

theorem imp_neg_sub {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} : (imp a₁ a₂)ᶜ = a₁ \ a₂ := by
  rw [sdiff_eq, imp]; simp

theorem inf_eq_of_le {α : Type*} [DistribLattice α] {a b : α} (h : a ≤ b) : a ⊓ b = a :=
  le_antisymm inf_le_left (le_inf le_rfl h)

theorem imp_inf_le {α : Type*} [BooleanAlgebra α] (a b : α) : imp a b ⊓ a ≤ b := by
  unfold imp; rw [inf_sup_right]; simp

theorem le_of_sub_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : bᶜ ⊓ a = ⊥) : a ≤ b := by
  rw [inf_comm] at h
  exact disjoint_compl_right_iff.mp (disjoint_iff.mpr h)

theorem le_neg_of_inf_eq_bot {α : Type*} [BooleanAlgebra α] {a b : α} (h : b ⊓ a = ⊥) :
    a ≤ bᶜ := by
  apply le_of_sub_eq_bot; rwa [compl_compl]

theorem sub_eq_bot_of_le {α : Type*} [BooleanAlgebra α] {a b : α} (h : a ≤ b) : bᶜ ⊓ a = ⊥ := by
  rw [← inf_eq_of_le h, inf_comm, inf_assoc, inf_compl_eq_bot, inf_bot_eq]

theorem inf_eq_bot_of_le_neg {α : Type*} [BooleanAlgebra α] {a b : α} (h : a ≤ bᶜ) :
    b ⊓ a = ⊥ := by rw [← compl_compl b]; exact sub_eq_bot_of_le h

@[simp] theorem imp_top_iff_le {α : Type*} [BooleanAlgebra α] {a₁ a₂ : α} :
    imp a₁ a₂ = ⊤ ↔ a₁ ≤ a₂ := by
  rw [imp, sup_comm, ← himp_eq]
  exact himp_eq_top_iff

theorem curry_uncurry {α : Type*} [BooleanAlgebra α] {a b c : α} :
    imp (a ⊓ b) c = imp a (imp b c) := by simp [imp]; ac_rfl

theorem deduction {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ⊓ b ≤ c ↔ a ≤ imp b c := by
  rw [← imp_top_iff_le, curry_uncurry, imp_top_iff_le]

theorem deduction_simp {α : Type*} [BooleanAlgebra α] {a b c : α} :
    a ≤ imp b c ↔ a ⊓ b ≤ c := deduction.symm

theorem imp_top {α : Type*} [CompleteBooleanAlgebra α] (a : α) : a ≤ imp a ⊤ := by
  rw [← deduction]; simp

-- Aliases without `@[simp]`: mathlib4's `iSup_option`/`iInf_option` already carry `@[simp]`.
theorem supr_option {α β : Type*} [CompleteLattice β] {η : Option α → β} :
    (⨆ (x : Option α), η x) = η none ⊔ ⨆ (a : α), η (some a) :=
  iSup_option η

theorem infi_option {α β : Type*} [CompleteLattice β] {η : Option α → β} :
    (⨅ (x : Option α), η x) = η none ⊓ ⨅ (a : α), η (some a) :=
  iInf_option η

theorem supr_option' {α β : Type*} [CompleteLattice β] {η : α → β} {b : β} :
    (⨆ (x : Option α), (Option.rec b η x : β) : β) = b ⊔ ⨆ (a : α), η a := by
  rw [supr_option]

theorem infi_option' {α β : Type*} [CompleteLattice β] {η : α → β} {b : β} :
    (⨅ (x : Option α), (Option.rec b η x : β) : β) = b ⊓ ⨅ (a : α), η a := by
  rw [infi_option]

theorem supr_max_of_bounded {α β : Type*} [CompleteLattice β] {A : α → β} {b c : β}
    {h : b = ⨆ (a : α), A a} {h_lt : c < b} {h_bounded : ∀ a : α, A a ≠ b → A a ≤ c} :
    ∃ x : α, A x = b := by
  by_contra h'
  push_neg at h'
  have : b ≤ c := by rw [h]; exact iSup_le (fun a => h_bounded a (h' a))
  exact absurd (lt_of_lt_of_le h_lt this) (lt_irrefl c)

theorem supr_max_of_bounded' {α β : Type*} [CompleteLattice β] {A : α → β} {b c : β}
    {h : b ≤ ⨆ (a : α), A a} {h_lt : c < b} {h_bounded : ∀ a : α, ¬b ≤ A a → A a ≤ c} :
    ∃ x : α, b ≤ A x := by
  by_contra h'
  push_neg at h'
  have : b ≤ c := le_trans h (iSup_le (fun a => h_bounded a (h' a)))
  exact absurd (lt_of_lt_of_le h_lt this) (lt_irrefl c)

theorem supr_eq_top_max {α β : Type*} [CompleteLattice β] {A : α → β}
    {h_nondeg : ⊥ < (⊤ : β)} {h_top : (⨆ (a : α), A a) = ⊤}
    {h_bounded : ∀ a : α, A a ≠ ⊤ → A a = ⊥} : ∃ x : α, A x = ⊤ :=
  supr_max_of_bounded (h := h_top.symm) (h_lt := h_nondeg)
    (h_bounded := fun a ha => (h_bounded a ha).symm ▸ le_refl ⊥)

theorem supr_eq_Gamma_max {α β : Type*} [CompleteLattice β] {A : α → β} {Γ : β}
    (h_nonzero : ⊥ < Γ) (h_Γ : Γ ≤ ⨆ a, A a)
    (h_bounded : ∀ a, ¬Γ ≤ A a → A a = ⊥) : ∃ x : α, Γ ≤ A x := by
  apply supr_max_of_bounded' (h := h_Γ) (h_lt := h_nonzero)
  intro a H; exact (h_bounded a H).symm ▸ bot_le

theorem eoc_supr {ι β : Type*} {s : ι → β} [CompleteLattice β] {X : Set ι} :
    (⨆ (i : X), s i) = ⨆ i ∈ X, s i := by
  apply le_antisymm
  · apply iSup_le; intro ⟨i, hi⟩; exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  · apply iSup_le; intro i; apply iSup_le; intro hi
    exact le_iSup_of_le ⟨i, hi⟩ le_rfl

theorem supr_all_sets {ι β : Type*} {s : ι → β} [CompleteLattice β] :
    (⨆ (i : ι), s i) = ⨆ (X : Set ι), (⨆ (x : X), s x) := by
  apply le_antisymm
  · apply iSup_le; intro i
    exact le_iSup_of_le {i} (le_iSup_of_le ⟨i, Set.mem_singleton i⟩ le_rfl)
  · apply iSup_le; intro X; apply iSup_le; intro i; exact le_iSup _ _

theorem supr_all_sets' {ι β : Type*} {s : ι → β} [CompleteLattice β] :
    (⨆ (i : ι), s i) = ⨆ (X : Set ι), (⨆ x ∈ X, s x) := by
  conv_lhs => rw [supr_all_sets]
  simp_rw [← eoc_supr]

theorem le_supr_of_le' {ι β : Type*} {s : ι → β} {b : β} [CompleteLattice β]
    (H : ∃ X : Set ι, b ≤ ⨆ (x : X), s x) : b ≤ ⨆ (i : ι), s i := by
  obtain ⟨X, hX⟩ := H
  calc b ≤ ⨆ (x : X), s x := hX
    _ ≤ ⨆ (i : ι), s i := by
        apply iSup_le; intro ⟨i, _⟩; exact le_iSup s i

theorem le_supr_of_le'' {ι β : Type*} {s : ι → β} {b : β} [CompleteLattice β]
    (H : ∃ X : Set ι, b ≤ ⨆ x ∈ X, s x) : b ≤ ⨆ (i : ι), s i := by
  obtain ⟨X, hX⟩ := H
  apply le_supr_of_le' (β := β) (s := s)
  refine ⟨X, ?_⟩
  rwa [eoc_supr]

theorem infi_congr {ι β : Type*} {s₁ s₂ : ι → β} [CompleteLattice β]
    {h : ∀ i : ι, s₁ i = s₂ i} : (⨅ (i : ι), s₁ i) = ⨅ (i : ι), s₂ i :=
  iInf_congr (fun i => h i)

@[simp] theorem supr_congr {ι β : Type*} {s₁ s₂ : ι → β} [CompleteLattice β]
    {h : ∀ i : ι, s₁ i = s₂ i} : (⨆ (i : ι), s₁ i) = ⨆ (i : ι), s₂ i :=
  iSup_congr (fun i => h i)

theorem imp_iff {β : Type*} {a b : β} [CompleteBooleanAlgebra β] : imp a b = aᶜ ⊔ b := rfl

theorem sup_inf_left_right_eq {β} [DistribLattice β] {a b c d : β} :
    (a ⊓ b) ⊔ (c ⊓ d) = (a ⊔ c) ⊓ (a ⊔ d) ⊓ (b ⊔ c) ⊓ (b ⊔ d) := by
  rw [sup_inf_right, sup_inf_left, sup_inf_left]; ac_rfl

theorem inf_sup_right_left_eq {β} [DistribLattice β] {a b c d : β} :
    (a ⊔ b) ⊓ (c ⊔ d) = (a ⊓ c) ⊔ (a ⊓ d) ⊔ (b ⊓ c) ⊔ (b ⊓ d) := by
  rw [inf_sup_right, inf_sup_left, inf_sup_left]; ac_rfl

theorem eq_neg_of_partition {β} [BooleanAlgebra β] {a₁ a₂ : β}
    (h_anti : a₁ ⊓ a₂ = ⊥) (h_partition : a₁ ⊔ a₂ = ⊤) : a₂ = a₁ᶜ := by
  have hd : Disjoint a₁ a₂ := disjoint_iff.mpr h_anti
  have hc : Codisjoint a₁ a₂ := codisjoint_iff.mpr h_partition
  exact (IsCompl.compl_eq ⟨hd, hc⟩).symm

theorem le_trans_inf {β} [Lattice β] {a₁ a₂ a₃ : β} (h₁ : a₁ ≤ a₂) {h₂ : a₁ ⊓ a₂ ≤ a₃} :
    a₁ ≤ a₃ :=
  calc a₁ = a₁ ⊓ a₁ := (inf_idem a₁).symm
    _ ≤ a₁ ⊓ a₂ := inf_le_inf le_rfl h₁
    _ ≤ a₃ := h₂

-- Note: le_trans' already exists in Mathlib (as alias for ge_trans)
-- Use le_trans_inf for our version

@[simp] theorem top_le_imp_top {β : Type*} {b : β} [BooleanAlgebra β] : ⊤ ≤ imp b ⊤ := by
  rw [← deduction]; simp

theorem poset_yoneda_iff {β : Type*} [PartialOrder β] {a b : β} :
    a ≤ b ↔ ∀ {Γ : β}, Γ ≤ a → Γ ≤ b :=
  ⟨fun h _ hΓ => le_trans hΓ h, fun H => H le_rfl⟩

theorem poset_yoneda_top {β : Type*} [Preorder β] [OrderTop β] {b : β} :
    ⊤ ≤ b ↔ ∀ {Γ : β}, Γ ≤ b :=
  ⟨fun h _ => le_trans le_top h, fun H => H⟩

theorem poset_yoneda {β : Type*} [PartialOrder β] {a b : β}
    (H : ∀ Γ : β, Γ ≤ a → Γ ≤ b) : a ≤ b := poset_yoneda_iff.mpr (fun {Γ} => H Γ)

theorem poset_yoneda_inv {β : Type*} [PartialOrder β] {a b : β} (Γ : β) (H : a ≤ b) :
    Γ ≤ a → Γ ≤ b := poset_yoneda_iff.mp H

theorem split_context {β : Type*} [Lattice β] {a₁ a₂ b : β}
    {H : ∀ Γ : β, Γ ≤ a₁ ∧ Γ ≤ a₂ → Γ ≤ b} : a₁ ⊓ a₂ ≤ b :=
  poset_yoneda_iff.mpr (fun {Γ} H' => H Γ ⟨le_trans H' inf_le_left, le_trans H' inf_le_right⟩)

theorem context_Or_elim {β : Type*} [CompleteBooleanAlgebra β] {ι : Type*} {s : ι → β} {Γ b : β}
    (h : Γ ≤ ⨆ (i : ι), s i) {h' : ∀ i, s i ⊓ Γ ≤ s i → s i ⊓ Γ ≤ b} : Γ ≤ b := by
  apply le_trans_inf h
  rw [inf_comm, deduction]
  apply iSup_le; intro i
  rw [← deduction]
  exact h' i inf_le_left

theorem context_or_elim {β : Type*} [CompleteBooleanAlgebra β] {Γ a₁ a₂ b : β}
    (H : Γ ≤ a₁ ⊔ a₂) {H₁ : a₁ ⊓ Γ ≤ a₁ → a₁ ⊓ Γ ≤ b}
    {H₂ : a₂ ⊓ Γ ≤ a₂ → a₂ ⊓ Γ ≤ b} : Γ ≤ b := by
  apply le_trans_inf H
  rw [inf_comm, deduction]
  apply sup_le <;> rw [← deduction] <;> [exact H₁ inf_le_left; exact H₂ inf_le_left]

theorem bv_em_aux {β : Type*} [CompleteBooleanAlgebra β] (Γ : β) (b : β) : Γ ≤ b ⊔ bᶜ :=
  le_trans le_top (by simp)

theorem bv_em {β : Type*} [CompleteBooleanAlgebra β] {Γ : β} (b : β) : Γ ≤ b ⊔ bᶜ :=
  bv_em_aux _ _

theorem diagonal_supr_le_supr {α : Type*} [CompleteLattice α] {ι : Type*}
    {s : ι → ι → α} {Γ : α}
    (H : Γ ≤ ⨆ i, s i i) : Γ ≤ ⨆ (i : ι), ⨆ (j : ι), s i j :=
  le_trans H (iSup_le fun i => le_iSup_of_le i (le_iSup_of_le i le_rfl))

theorem diagonal_infi_le_infi {α : Type*} [CompleteLattice α] {ι : Type*}
    {s : ι → ι → α} {Γ : α}
    (H : Γ ≤ ⨅ (i : ι), ⨅ (j : ι), s i j) : Γ ≤ ⨅ i, s i i :=
  le_trans H (le_iInf fun i => iInf_le_of_le i (iInf_le_of_le i le_rfl))

theorem context_and_intro {β : Type*} [Lattice β] {Γ} {a₁ a₂ : β}
    (H₁ : Γ ≤ a₁) (H₂ : Γ ≤ a₂) : Γ ≤ a₁ ⊓ a₂ := le_inf H₁ H₂

theorem specialize_context {β : Type*} [PartialOrder β] {Γ b : β} (Γ' : β) {H_le : Γ' ≤ Γ}
    (H : Γ ≤ b) : Γ' ≤ b := le_trans H_le H

theorem context_specialize_aux {β : Type*} [CompleteBooleanAlgebra β] {ι : Type*} {s : ι → β}
    (j : ι) {Γ : β} {H : Γ ≤ ⨅ i, s i} : Γ ≤ imp (⨅ i, s i) (s j) := by
  rw [← deduction]
  exact le_trans (inf_le_inf H le_rfl) (inf_le_right.trans (iInf_le _ j))

theorem context_specialize {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β}
    {Γ : β} (H : Γ ≤ ⨅ i, s i) (j : ι) : Γ ≤ s j :=
  le_trans H (iInf_le _ _)

theorem context_specialize_strict {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β}
    {Γ : β} (H : Γ < ⨅ i, s i) (j : ι) : Γ < s j :=
  lt_of_lt_of_le H (iInf_le _ _)

theorem context_split_inf_left {β : Type*} [CompleteLattice β] {a₁ a₂ Γ : β}
    (H : Γ ≤ a₁ ⊓ a₂) : Γ ≤ a₁ := le_trans H inf_le_left

theorem context_split_inf_right {β : Type*} [CompleteLattice β] {a₁ a₂ Γ : β}
    (H : Γ ≤ a₁ ⊓ a₂) : Γ ≤ a₂ := le_trans H inf_le_right

theorem context_imp_elim {β : Type*} [CompleteBooleanAlgebra β] {a b Γ : β}
    (H₁ : Γ ≤ imp a b) (H₂ : Γ ≤ a) : Γ ≤ b :=
  le_trans (le_inf H₁ H₂) (imp_inf_le a b)

theorem context_imp_intro {β : Type*} [CompleteBooleanAlgebra β] {a b Γ : β}
    (H : a ⊓ Γ ≤ a → a ⊓ Γ ≤ b) : Γ ≤ imp a b := by
  rw [← deduction, inf_comm]; exact H inf_le_left

theorem bv_absurd {β} [BooleanAlgebra β] {Γ : β} (b : β) (H₁ : Γ ≤ b) (H₂ : Γ ≤ bᶜ) :
    Γ ≤ ⊥ :=
  le_trans (le_inf H₁ H₂) inf_compl_eq_bot.le

theorem neg_imp {β : Type*} [BooleanAlgebra β] {a b : β} : (imp a b)ᶜ = a ⊓ bᶜ := by
  simp [imp]

theorem nonzero_wit {β : Type*} [CompleteLattice β] {ι : Type*} {s : ι → β} :
    (⊥ < ⨆ i, s i) → ∃ j, ⊥ < s j := by
  intro H
  by_contra h
  push_neg at h
  simp only [bot_lt_iff_ne_bot, ne_eq, not_not] at h
  have key : ⨆ i, s i = ⊥ :=
    le_antisymm (iSup_le (fun j => (h j).le)) bot_le
  exact absurd (key ▸ H) (lt_irrefl ⊥)

theorem nonzero_inf_of_nonzero_le_supr {α : Type*} [CompleteDistribLattice α] {ι : Type*}
    {s : ι → α} {Γ : α} (H_nonzero : ⊥ < Γ) (H : Γ ≤ ⨆ i, s i) : ∃ i, ⊥ < Γ ⊓ s i := by
  by_contra H'
  push_neg at H'
  simp only [bot_lt_iff_not_le_bot, not_not] at H'
  have H_absorb : Γ ⊓ ⨆ (i : ι), s i = Γ :=
    le_antisymm inf_le_left (le_inf le_rfl H)
  have : Γ ⊓ ⨆ (i : ι), s i ≤ ⊥ := by
    rw [inf_iSup_eq']; exact iSup_le H'
  rw [H_absorb] at this
  exact absurd (lt_of_lt_of_le H_nonzero this) (lt_irrefl ⊥)

theorem nonzero_wit' {β : Type*} [CompleteDistribLattice β] {ι : Type*} {s : ι → β} {Γ : β}
    (H_nonzero : ⊥ < Γ) (H_le : Γ ≤ ⨆ i, s i) : ∃ j, ⊥ < s j ⊓ Γ := by
  obtain ⟨j, hj⟩ := nonzero_inf_of_nonzero_le_supr H_nonzero H_le
  exact ⟨j, by rwa [inf_comm]⟩

open scoped Cardinal in
def CCC (𝔹 : Type u) [BooleanAlgebra 𝔹] : Prop :=
  ∀ ι : Type u, ∀ 𝓐 : ι → 𝔹, (∀ i, ⊥ < 𝓐 i) →
    (∀ i j, i ≠ j → 𝓐 i ⊓ 𝓐 j ≤ ⊥) → (#ι) ≤ Cardinal.aleph0

noncomputable def Prop_to_bot_top {𝔹 : Type u} [Bot 𝔹] [Top 𝔹] : Prop → 𝔹 :=
  fun p => @ite 𝔹 p (Classical.propDecidable p) ⊤ ⊥

@[simp] theorem Prop_to_bot_top_true {𝔹 : Type u} [Bot 𝔹] [Top 𝔹] {p : Prop} (H : p) :
    Prop_to_bot_top p = (⊤ : 𝔹) := by
  simp only [Prop_to_bot_top, @if_pos _ (Classical.propDecidable p) H]

@[simp] theorem Prop_to_bot_top_false {𝔹 : Type u} [Bot 𝔹] [Top 𝔹] {p : Prop} (H : ¬p) :
    Prop_to_bot_top p = (⊥ : 𝔹) := by
  simp only [Prop_to_bot_top, @if_neg _ (Classical.propDecidable p) H]

theorem bv_by_contra {𝔹} [BooleanAlgebra 𝔹] {Γ b : 𝔹} (H : Γ ≤ imp bᶜ ⊥) : Γ ≤ b := by
  simpa [imp] using H

/-! ## tactic.interactive section — DEFERRED

  The tactic extensions (bv_intro, bv_cases_at, bv_or_elim_at, specialize_context,
  bv_split, bv_and_intro, bv_imp_elim_at, bv_mp, bv_imp_intro, bv_split_goal,
  bv_or_inr, bv_or_inl, bv_contradiction, tidy_context, bv_exfalso,
  bv_cases_on, bv_exists_intro, bv_specialize_at, bv_to_pi, bv_to_pi') need
  a complete rewrite for Lean 4's macro/elab system.

  These are deferred until downstream files actually need them.
  - Main block: See src/to_mathlib.lean:1252-1684 for the original definitions.
  - Early block also deferred: src/to_mathlib.lean:492-510 contained `congr1` and `rexact`
    tactics. `congr1` is used in roughly 10 downstream Lean 3 proof sites. In Lean 4,
    `congr 1` (with a space) is a built-in tactic, so when porting `fol`, `henkin`,
    `language_extension`, etc., translate `congr1` (no space) to `congr 1` (with space)
    inline rather than re-implementing the tactic.
-/

-- with_h_asms helper definition
def with_h_asms {𝔹} [Lattice 𝔹] (Γ : 𝔹) : ∀ (_ : List 𝔹) (g : 𝔹), Prop
  | [], x => Γ ≤ x
  | x :: xs, y => Γ ≤ x → with_h_asms Γ xs y

/-! ### Compatibility shims for newer Mathlib (port to Mathlib 355bc1e, 2026-08) -/

/-- `Finset.toSet` is no longer in Mathlib; the port uses it for the coercion
`Finset α → Set α`. -/
abbrev Finset.toSet {α : Type*} (s : Finset α) : Set α := (s : Set α)
