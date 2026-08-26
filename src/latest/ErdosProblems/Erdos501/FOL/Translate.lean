/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# From Mathlib's first-order logic to Flypitch's

The Challenge states the results in Mathlib's `ModelTheory` (language `Erdos501.FOL.L`), while the
proofs live in the Flypitch development (language `L_ZFC`, `Fol.bounded_formula`, `Fol.Structure`).
This file translates:

* `trT`, `tr` — Mathlib terms/formulas over `L` (variables by de Bruijn *level*, `Fin.snoc`-style
  contexts) into Flypitch bounded terms/formulas over `L_ZFC` (variables by de Bruijn *index*,
  `DVec.cons`-style contexts, index `0` innermost): level `ℓ` at depth `n` becomes index `n - 1 - ℓ`;
* `toM S` — a Flypitch structure `S : Fol.Structure L_ZFC` as an `L`-structure on `S.carrier`;
* `realize_tr` — realization commutes with the translation:
  `φ.Realize xs ↔ realize_bounded_formula (dvecOfCtx xs) (tr φ)`.
-/
import ErdosProblems.Erdos501.FOL.Statement
import ErdosProblems.Erdos501.Flypitch4.Zfc

open FirstOrder FirstOrder.Language
open scoped FirstOrder
open Fol

namespace Erdos501.FOL

/-! ### Symbols -/

/-- Function symbols of `L` as function symbols of Flypitch's `L_ZFC`. -/
def funcToF : ∀ {n : ℕ}, Func n → L_ZFC.functions n
  | _, Func.emptyset => ZFC_func.emptyset
  | _, Func.omega => ZFC_func.ω
  | _, Func.powerset => ZFC_func.P
  | _, Func.union => ZFC_func.Union
  | _, Func.pair => ZFC_func.pr

/-- The relation symbol `∈` of `L` as the relation symbol `∈` of `L_ZFC`. -/
def relToF : ∀ {n : ℕ}, Rel n → L_ZFC.relations n
  | _, Rel.mem => ZFC_rel.ε

/-! ### Vectors -/

/-- A `Fin n`-indexed family as a `DVec`, in order (head = index `0`).  Used for the arguments of
function and relation symbols. -/
def dvecOfFn {α : Type*} : ∀ {n : ℕ}, (Fin n → α) → DVec α n
  | 0, _ => DVec.nil
  | _ + 1, xs => DVec.cons (xs 0) (dvecOfFn (xs ∘ Fin.succ))

/-- A variable context `xs : Fin n → α` (Mathlib style, `xs i` = the variable of level `i`) as a
Flypitch context (`DVec.cons`-style, head = the innermost variable): the *reversed* vector
`[xs (n-1), …, xs 0]`. -/
def dvecOfCtx {α : Type*} : ∀ {n : ℕ}, (Fin n → α) → DVec α n
  | 0, _ => DVec.nil
  | n + 1, xs => DVec.cons (xs (Fin.last n)) (dvecOfCtx (xs ∘ Fin.castSucc))

@[simp] lemma dvecOfCtx_zero {α : Type*} (xs : Fin 0 → α) : dvecOfCtx xs = DVec.nil := rfl

@[simp] lemma dvecOfCtx_snoc {α : Type*} {n : ℕ} (xs : Fin n → α) (a : α) :
    dvecOfCtx (Fin.snoc xs a) = DVec.cons a (dvecOfCtx xs) := by
  simp [dvecOfCtx, Fin.snoc_last]

lemma dvecOfCtx_nth {α : Type*} : ∀ {n : ℕ} (xs : Fin n → α) (ℓ : ℕ) (h : ℓ < n),
    (dvecOfCtx xs).nth (n - 1 - ℓ) (by omega) = xs ⟨ℓ, h⟩
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, xs, ℓ, h => by
    rcases Nat.lt_or_ge ℓ n with hℓ | hℓ
    · have e : n + 1 - 1 - ℓ = (n - 1 - ℓ) + 1 := by omega
      simp only [dvecOfCtx, e, DVec.nth]
      rw [dvecOfCtx_nth (xs ∘ Fin.castSucc) ℓ hℓ]
      simp [Fin.castSucc]
    · have e : ℓ = n := by omega
      subst e
      simp [dvecOfCtx, DVec.nth, Fin.last]

@[simp] lemma dvecOfFn_zero {α : Type*} (xs : Fin 0 → α) : dvecOfFn xs = DVec.nil := rfl
@[simp] lemma dvecOfFn_one {α : Type*} (xs : Fin 1 → α) : dvecOfFn xs = DVec.cons (xs 0) DVec.nil :=
  rfl
@[simp] lemma dvecOfFn_two {α : Type*} (xs : Fin 2 → α) :
    dvecOfFn xs = DVec.cons (xs 0) (DVec.cons (xs 1) DVec.nil) := rfl

/-! ### The translation of terms and formulas -/

/-- Translation of terms: variables of level `ℓ` at depth `n` become variables of index `n - 1 - ℓ`;
function symbols are translated symbol by symbol. -/
def trT {n : ℕ} : L.Term (Empty ⊕ Fin n) → bounded_term L_ZFC n
  | Term.var (Sum.inl e) => e.elim
  | Term.var (Sum.inr ⟨ℓ, _⟩) => bd_var ⟨n - 1 - ℓ, by omega⟩
  | Term.func Func.emptyset _ => ∅'
  | Term.func Func.omega _ => ω'
  | Term.func Func.powerset ts => Powerset (trT (ts 0))
  | Term.func Func.union ts => union' (trT (ts 0))
  | Term.func Func.pair ts => pair' (trT (ts 0)) (trT (ts 1))

/-- Translation of formulas (structural). -/
def tr : ∀ {n : ℕ}, L.BoundedFormula Empty n → bounded_formula L_ZFC n
  | _, BoundedFormula.falsum => bd_falsum
  | _, BoundedFormula.equal t₁ t₂ => bd_equal (trT t₁) (trT t₂)
  | _, BoundedFormula.rel Rel.mem ts => mem' (trT (ts 0)) (trT (ts 1))
  | _, BoundedFormula.imp φ ψ => bd_imp (tr φ) (tr ψ)
  | _, BoundedFormula.all φ => bd_all (tr φ)

@[simp] lemma tr_falsum {n : ℕ} : tr (⊥ : L.BoundedFormula Empty n) = bd_falsum := rfl
@[simp] lemma tr_imp {n : ℕ} (φ ψ : L.BoundedFormula Empty n) :
    tr (φ.imp ψ) = bd_imp (tr φ) (tr ψ) := rfl
@[simp] lemma tr_all {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) : tr φ.all = bd_all (tr φ) := rfl
@[simp] lemma tr_not {n : ℕ} (φ : L.BoundedFormula Empty n) : tr φ.not = bd_not (tr φ) := rfl
@[simp] lemma tr_inf {n : ℕ} (φ ψ : L.BoundedFormula Empty n) :
    tr (φ ⊓ ψ) = bd_and (tr φ) (tr ψ) := rfl
@[simp] lemma tr_sup {n : ℕ} (φ ψ : L.BoundedFormula Empty n) :
    tr (φ ⊔ ψ) = bd_or (tr φ) (tr ψ) := rfl
@[simp] lemma tr_iff {n : ℕ} (φ ψ : L.BoundedFormula Empty n) :
    tr (φ.iff ψ) = bd_biimp (tr φ) (tr ψ) := rfl
@[simp] lemma tr_ex {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) : tr φ.ex = bd_ex (tr φ) := rfl
@[simp] lemma tr_equal {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) :
    tr (Term.bdEqual t₁ t₂) = bd_equal (trT t₁) (trT t₂) := rfl
@[simp] lemma tr_mem {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) :
    tr (Relations.boundedFormula₂ (Rel.mem : L.Relations 2) t₁ t₂) = mem' (trT t₁) (trT t₂) := rfl

/-! ### Flypitch structures as `L`-structures -/

/-- A Flypitch structure for `L_ZFC` as an `L`-structure on its carrier. -/
@[reducible] def toM (S : Fol.Structure L_ZFC) : L.Structure S.carrier where
  funMap f xs := S.fun_map (funcToF f) (dvecOfFn xs)
  RelMap r xs := S.rel_map (relToF r) (dvecOfFn xs)

attribute [local instance] toM

variable (S : Fol.Structure L_ZFC)

@[simp] lemma toM_funMap {n : ℕ} (f : Func n) (xs : Fin n → S.carrier) :
    Structure.funMap (L := L) (M := S.carrier) f xs = S.fun_map (funcToF f) (dvecOfFn xs) := rfl
@[simp] lemma toM_RelMap {n : ℕ} (r : Rel n) (xs : Fin n → S.carrier) :
    Structure.RelMap (L := L) (M := S.carrier) r xs = S.rel_map (relToF r) (dvecOfFn xs) := rfl

/-- Realization of translated terms. -/
theorem realize_trT {n : ℕ} (v : Empty → S.carrier) (xs : Fin n → S.carrier) :
    ∀ (t : L.Term (Empty ⊕ Fin n)),
      Term.realize (Sum.elim v xs) t = realize_bounded_term (dvecOfCtx xs) (trT t) DVec.nil
  | Term.var (Sum.inl e) => e.elim
  | Term.var (Sum.inr ⟨ℓ, h⟩) => by
    simp only [Term.realize, Sum.elim_inr, trT, realize_bounded_term]
    exact (dvecOfCtx_nth xs ℓ h).symm
  | Term.func Func.emptyset ts => by
    simp only [Term.realize, trT, toM_funMap, dvecOfFn_zero]
    rfl
  | Term.func Func.omega ts => by
    simp only [Term.realize, trT, toM_funMap, dvecOfFn_zero]
    rfl
  | Term.func Func.powerset ts => by
    simp only [Term.realize, trT, toM_funMap, dvecOfFn_one, realize_trT v xs (ts 0)]
    rfl
  | Term.func Func.union ts => by
    simp only [Term.realize, trT, toM_funMap, dvecOfFn_one, realize_trT v xs (ts 0)]
    rfl
  | Term.func Func.pair ts => by
    simp only [Term.realize, trT, toM_funMap, dvecOfFn_two, realize_trT v xs (ts 0),
      realize_trT v xs (ts 1)]
    rfl

/-- Realization of translated formulas. -/
theorem realize_tr (v : Empty → S.carrier) :
    ∀ {n : ℕ} (φ : L.BoundedFormula Empty n) (xs : Fin n → S.carrier),
      φ.Realize v xs ↔ realize_bounded_formula (dvecOfCtx xs) (tr φ) DVec.nil
  | _, BoundedFormula.falsum, _ => Iff.rfl
  | _, BoundedFormula.equal t₁ t₂, xs => by
    simp only [BoundedFormula.Realize, tr, realize_bounded_formula, realize_trT S v xs]
  | _, BoundedFormula.rel Rel.mem ts, xs => by
    simp only [BoundedFormula.Realize, tr, toM_RelMap, dvecOfFn_two, realize_trT S v xs (ts 0),
      realize_trT S v xs (ts 1)]
    rfl
  | _, BoundedFormula.imp φ ψ, xs => by
    simp only [BoundedFormula.Realize, tr, realize_bounded_formula, realize_tr v φ xs,
      realize_tr v ψ xs]
  | _, BoundedFormula.all φ, xs => by
    simp only [BoundedFormula.Realize, tr, realize_bounded_formula]
    constructor
    · intro h x
      have := (realize_tr v φ (Fin.snoc xs x)).mp (h x)
      rwa [dvecOfCtx_snoc] at this
    · intro h x
      apply (realize_tr v φ (Fin.snoc xs x)).mpr
      rw [dvecOfCtx_snoc]
      exact h x

/-- Realization of translated sentences. -/
theorem realize_sentence_tr (φ : L.Sentence) : (S.carrier ⊨ φ) ↔ (S ⊨ₘ tr φ) := by
  unfold Sentence.Realize Formula.Realize
  exact realize_tr S default φ default

end Erdos501.FOL
