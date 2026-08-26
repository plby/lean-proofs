/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/zfc.lean (552 lines) — Task 22 -/

import ErdosProblems.Erdos501.Flypitch4.Bfol
import ErdosProblems.Erdos501.Flypitch4.Forcing
import ErdosProblems.Erdos501.Flypitch4.ForcingCH

set_option relaxedAutoImplicit true

open Fol bSet

universe u

-- ============================================================
-- The language of ZFC (src/zfc.lean:32-46)
-- ============================================================

/-- Relation symbols of ZFC (just membership ∈). -/
inductive ZFC_rel : ℕ → Type 1
  | ε : ZFC_rel 2

/-- Function symbols of ZFC. -/
inductive ZFC_func : ℕ → Type 1
  | emptyset : ZFC_func 0
  | pr       : ZFC_func 2
  | ω        : ZFC_func 0
  | P        : ZFC_func 1
  | Union    : ZFC_func 1

/-- The language of ZFC set theory. -/
def L_ZFC : Language.{1} :=
  { functions := ZFC_func, relations := ZFC_rel }

-- ============================================================
-- The Boolean-valued V model (src/zfc.lean:48-113)
-- ============================================================

variable {β : Type 0} [NontrivialCompleteBooleanAlgebra β]

/-- Interpret L_ZFC function symbols in bSet β. -/
def bSet_model_fun_map : ∀ {n : ℕ}, L_ZFC.functions n → DVec (bSet β) n → bSet β
  | _, ZFC_func.emptyset, _  => bSet.empty
  | _, ZFC_func.pr, DVec.cons x (DVec.cons y DVec.nil) => pair x y
  | _, ZFC_func.ω, _ => bSet.omega
  | _, ZFC_func.P, DVec.cons x DVec.nil => bv_powerset x
  | _, ZFC_func.Union, DVec.cons x DVec.nil => bv_union x

/-- Interpret L_ZFC relation symbols in bSet β. -/
def bSet_model_rel_map : ∀ {n : ℕ}, L_ZFC.relations n → DVec (bSet β) n → β
  | _, ZFC_rel.ε, DVec.cons x (DVec.cons y DVec.nil) => x ∈ᴮ y

variable (β)

/-- The Boolean-valued model V(β) of ZFC. -/
noncomputable def V : bStructure L_ZFC β :=
  { carrier   := bSet β
    fun_map   := bSet_model_fun_map
    rel_map   := bSet_model_rel_map
    eq        := (· =ᴮ ·)
    eq_refl   := fun x => bv_eq_refl x
    eq_symm   := fun x y => bv_eq_symm
    eq_trans  := fun y => bv_eq_trans
    fun_congr := by
      intro n F
      cases F with
      | emptyset =>
        intro x y
        cases x; cases y
        simp [bSet_model_fun_map, DVec.map2, DVec.fInf]
      | ω =>
        intro x y
        cases x; cases y
        simp [bSet_model_fun_map, DVec.map2, DVec.fInf]
      | P =>
        intro x y
        match x, y with
        | DVec.cons a DVec.nil, DVec.cons b DVec.nil =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact bv_powerset_congr le_rfl
      | Union =>
        intro x y
        match x, y with
        | DVec.cons a DVec.nil, DVec.cons b DVec.nil =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact bv_union_congr le_rfl
      | pr =>
        intro x y
        match x, y with
        | DVec.cons a (DVec.cons b DVec.nil), DVec.cons c (DVec.cons d DVec.nil) =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_fun_map]
          exact pair_congr inf_le_left inf_le_right
    rel_congr := by
      intro n R
      cases R with
      | ε =>
        intro x y
        match x, y with
        | DVec.cons a (DVec.cons b DVec.nil), DVec.cons c (DVec.cons d DVec.nil) =>
          simp only [DVec.map2, DVec.fInf_cons, DVec.fInf_nil, inf_top_eq, bSet_model_rel_map]
          -- goal: a =ᴮ c ⊓ b =ᴮ d ⊓ a ∈ᴮ b ≤ c ∈ᴮ d
          exact mem_congr (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right
  }

@[simp] lemma carrier_V : ↥(V β) = bSet β := rfl
@[simp] lemma V_forall {C : (V β) → β} : (⨅ (x : V β), C x) = ⨅ (x : bSet β), C x := rfl
@[simp] lemma V_exists {C : (V β) → β} : (⨆ (x : V β), C x) = ⨆ (x : bSet β), C x := rfl
@[simp] lemma V_eq {a b : V β} : (V β).eq a b = a =ᴮ b := rfl

instance V_β_nonempty : Nonempty (V β) := ⟨bSet.empty⟩

variable {β}

-- ============================================================
-- Bounded terms/formulas for L_ZFC (src/zfc.lean:115-140)
-- ============================================================

def emptyset' {n} : bounded_term L_ZFC n := bd_const ZFC_func.emptyset
notation "∅'" => emptyset'

def omega' {n} : bounded_term L_ZFC n := bd_const ZFC_func.ω
notation "ω'" => omega'

def Powerset {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.P) t
notation "P'" => Powerset

/-- Boolean membership formula: t₁ ∈ t₂ -/
def mem' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  @bounded_formula_of_relation L_ZFC 2 n ZFC_rel.ε t₁ t₂

/-- Bounded pair term -/
def pair' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  @bounded_term_of_function L_ZFC 2 n ZFC_func.pr t₁ t₂

/-- Bounded union term -/
def union' {n} (t : bounded_term L_ZFC n) : bounded_term L_ZFC n :=
  bd_app (bd_func ZFC_func.Union) t
notation "⋃'" => union'

/-- Subset formula: t₁ ⊆ t₂ -/
def subset'' {n} (t₁ t₂ : bounded_term L_ZFC n) : bounded_formula L_ZFC n :=
  bd_all (bd_imp
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₁ ↑ᵇ' 1 # 0))
    (mem' (bd_var ⟨0, Nat.zero_lt_succ _⟩) (t₂ ↑ᵇ' 1 # 0)))

-- ============================================================
-- Simp lemmas for boolean_realize (src/zfc.lean:142-176)
-- ============================================================

@[simp] lemma boolean_realize_bounded_formula_mem' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (mem' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ∈ᴮ
    boolean_realize_bounded_term v t₂ DVec.nil := by
  rfl

@[simp] lemma boolean_realize_bounded_term_Union' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (⋃' t) DVec.nil =
    bv_union (boolean_realize_bounded_term v t DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_term_Powerset' {n} {v : DVec (V β) n}
    (t : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (P' t) DVec.nil =
    bv_powerset (boolean_realize_bounded_term v t DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_term_omega' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ω' DVec.nil = bSet.omega := by
  rfl

@[simp] lemma boolean_realize_bounded_term_emptyset' {n} {v : DVec (V β) n} :
    boolean_realize_bounded_term v ∅' DVec.nil = bSet.empty := by
  rfl

@[simp] lemma boolean_realize_bounded_term_pair' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_term v (pair' t₁ t₂) DVec.nil =
    pair (boolean_realize_bounded_term v t₁ DVec.nil)
         (boolean_realize_bounded_term v t₂ DVec.nil) := by
  rfl

@[simp] lemma boolean_realize_bounded_formula_subset' {n} {v : DVec (V β) n}
    (t₁ t₂ : bounded_term L_ZFC n) :
    boolean_realize_bounded_formula v (subset'' t₁ t₂) DVec.nil =
    boolean_realize_bounded_term v t₁ DVec.nil ⊆ᴮ boolean_realize_bounded_term v t₂ DVec.nil := by
  simp only [subset'', boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_subst_lift, V_forall]
  -- goal: ⨅ x : bSet β, imp (x ∈ brt t₁) (x ∈ brt t₂) = brt t₁ ⊆ᴮ brt t₂
  -- definitionally `subset_unfold'` (imp = ⟹); stated via `exact` since the
  -- goal mixes `(V β).carrier` and `bSet β` (fine at default transparency).
  exact subset_unfold'.symm

@[simp] lemma fin_0 {n : ℕ} : (0 : Fin (n + 1)).1 = 0 := rfl
@[simp] lemma fin_1 {n : ℕ} : (1 : Fin (n + 2)).1 = 1 := rfl
@[simp] lemma fin_2 {n : ℕ} : (2 : Fin (n + 3)).1 = 2 := rfl
@[simp] lemma fin_3 {n : ℕ} : (3 : Fin (n + 4)).1 = 3 := rfl

-- ============================================================
-- Ordinal predicates (src/zfc.lean:307-327)
-- ============================================================

def is_transitive_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
                 (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))

def epsilon_trichotomy_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
    (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
      (bd_or
        (bd_or (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
               (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))))

def epsilon_well_founded_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_imp (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
    (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
      (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
          (bd_not (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))))))))

def ewo_f : bounded_formula L_ZFC 1 := bd_and epsilon_trichotomy_f epsilon_well_founded_f

def Ord_f : bounded_formula L_ZFC 1 := bd_and ewo_f is_transitive_f

@[simp] lemma Ord_f_is_Ord {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) Ord_f DVec.nil = Ord x := by
  simp only [Ord_f, ewo_f, epsilon_trichotomy_f, epsilon_well_founded_f, is_transitive_f,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_or,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_subset', boolean_realize_bounded_term_emptyset',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq]
  unfold bSet.Ord epsilon_well_orders epsilon_trichotomy epsilon_well_founded is_transitive
  rfl

-- ============================================================
-- The ZFC axioms as sentences (src/zfc.lean:179-382)
-- ============================================================

-- axiom of emptyset: ∀ x, x ∉ ∅
def axiom_of_emptyset : sentence L_ZFC :=
  bd_all (bd_not (mem' (bd_var ⟨0, by omega⟩) ∅'))

lemma bSet_models_emptyset : ⊤ ⊩[V β] axiom_of_emptyset := by
  change ⊤ ≤ _
  simp only [axiom_of_emptyset, boolean_realize_sentence_all,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula,
             V_eq, boolean_realize_bounded_term_emptyset']
  exact le_iInf (fun x => empty_spec)

-- axiom of ordered pairs: ∀ x y z w, pair(x,y) = pair(z,w) ↔ x=z ∧ y=w
def axiom_of_ordered_pairs : sentence L_ZFC :=
  bd_all (bd_all (bd_all (bd_all
    (bd_biimp
      (bd_equal (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))
                (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
      (bd_and
        (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_equal (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)))))))

lemma bSet_models_ordered_pairs : ⊤ ⊩[V β] axiom_of_ordered_pairs := by
  change ⊤ ≤ _
  simp only [axiom_of_ordered_pairs, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term, DVec.nth, V_eq, V_forall]
  apply le_iInf; intro a; apply le_iInf; intro b; apply le_iInf; intro x; apply le_iInf; intro y
  -- goal: ⊤ ≤ bihimp (pair a b =ᴮ pair x y) (a =ᴮ x ⊓ b =ᴮ y)
  have heq : pair a b =ᴮ pair x y = a =ᴮ x ⊓ b =ᴮ y :=
    le_antisymm (le_inf eq_of_eq_pair_left eq_of_eq_pair_right)
                (pair_congr inf_le_left inf_le_right)
  show ⊤ ≤ bihimp (pair a b =ᴮ pair x y) (a =ᴮ x ⊓ b =ᴮ y)
  rw [heq]
  -- Need: ⊤ ≤ bihimp (a =ᴮ x ⊓ b =ᴮ y) (a =ᴮ x ⊓ b =ᴮ y)
  rw [bihimp_self]

-- axiom of extensionality: ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
def axiom_of_extensionality : sentence L_ZFC :=
  bd_all (bd_all
    (bd_imp
      (bd_all (bd_biimp
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))
      (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))))

lemma bSet_models_extensionality : ⊤ ⊩[V β] axiom_of_extensionality := by
  change ⊤ ≤ _
  simp only [axiom_of_extensionality, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]
  apply le_iInf; intro x; apply le_iInf; intro y
  -- goal: ⊤ ≤ (⨅ z, bihimp (z ∈ x) (z ∈ y)) ⟹ (x =ᴮ y)
  rw [← _root_.deduction]
  -- goal: ⊤ ⊓ (⨅ z, bihimp (z ∈ x) (z ∈ y)) ≤ x =ᴮ y
  rw [top_inf_eq]
  -- goal: ⨅ z, bihimp (z ∈ x) (z ∈ y) ≤ x =ᴮ y
  apply le_trans ?_ (bSet_axiom_of_extensionality x y)
  apply le_iInf; intro z
  apply le_trans (iInf_le _ z)
  -- bihimp A B = (B ⇨ A) ⊓ (A ⇨ B); imp A B = Aᶜ ⊔ B; himp_eq: A ⇨ B = B ⊔ Aᶜ
  apply le_inf
  · exact le_trans inf_le_right (by simp [himp_eq, imp, sup_comm])
  · exact le_trans inf_le_left (by simp [himp_eq, imp, sup_comm])

-- axiom schema of strong collection (src/zfc.lean:208-211)
def axiom_of_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) : sentence L_ZFC :=
  bd_alls (n + 1) $
    bd_imp
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_ex (ϕ ↑ᶠᵇ' 1 # 2))))
      (bd_ex
        (bd_and
          (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
              (ϕ ↑ᶠᵇ' 2 # 2)))))
          (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
            (bd_ex (bd_and
              (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
              (subst0_bounded_formula (ϕ ↑ᶠᵇ' 3 # 2) (bd_var ⟨1, by omega⟩))))))))

lemma lift2_helper {n l} (f : bounded_preformula L_ZFC n l) {k} (m : ℕ) :
    (f ↑ᶠᵇ' (k + 2) # m).fst = ((f ↑ᶠᵇ' (k + 1) # m) ↑ᶠᵇ' 1 # m).fst := by
  simp only [lift_bounded_formula_fst]
  rw [lift_formula_at2_medium] <;> omega

lemma B_ext_left_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 1))
    (xs : DVec (V β) n) (x y : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons x xs) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons y xs) ϕ DVec.nil := by
  -- Key: x =ᴮ y = ⨅ m : Fin (n+1), (V β).eq ((x::xs)[m]) ((y::xs)[m])
  -- At m=0: eq(x,y) = x =ᴮ y; at m=succ k: eq(xs[k], xs[k]) = ⊤
  have hkey : x =ᴮ y = ⨅ (m : Fin (n + 1)),
      (V β).eq ((DVec.cons x xs).nth m.1 m.2) ((DVec.cons y xs).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf; intro ⟨m, hm⟩
      simp only [V_eq]
      cases m with
      | zero => simp [DVec.nth]
      | succ k =>
        show x =ᴮ y ≤ xs.nth k (Nat.lt_of_succ_lt_succ hm) =ᴮ xs.nth k (Nat.lt_of_succ_lt_succ hm)
        exact le_top.trans (bv_eq_refl _).symm.le
    · exact iInf_le _ (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  rw [hkey]
  exact boolean_realize_bounded_formula_congr (inferInstance : Nonempty (V β)) _ _ ϕ DVec.nil
lemma B_ext_right_realize_bounded_formula {n : ℕ} (ϕ : bounded_formula L_ZFC (n + 2))
    (xs : DVec (V β) n) (x y z : V β) :
    x =ᴮ y ⊓ boolean_realize_bounded_formula (DVec.cons z (DVec.cons x xs)) ϕ DVec.nil ≤
    boolean_realize_bounded_formula (DVec.cons z (DVec.cons y xs)) ϕ DVec.nil := by
  -- Key: x =ᴮ y = ⨅ m : Fin (n+2), eq((z::x::xs)[m], (z::y::xs)[m])
  -- At m=0: eq(z,z)=⊤; at m=1: eq(x,y)=x=ᴮy; at m=succ(succ k): eq(xs[k],xs[k])=⊤
  have hkey : x =ᴮ y = ⨅ (m : Fin (n + 2)),
      (V β).eq ((DVec.cons z (DVec.cons x xs)).nth m.1 m.2)
               ((DVec.cons z (DVec.cons y xs)).nth m.1 m.2) := by
    apply le_antisymm
    · apply le_iInf; intro ⟨m, hm⟩
      simp only [V_eq]
      cases m with
      | zero =>
        show x =ᴮ y ≤ z =ᴮ z
        exact le_top.trans (bv_eq_refl _).symm.le
      | succ k =>
        cases k with
        | zero => simp [DVec.nth]
        | succ k' =>
          show x =ᴮ y ≤ xs.nth k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm)) =ᴮ
               xs.nth k' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm))
          exact le_top.trans (bv_eq_refl _).symm.le
    · exact iInf_le _ (⟨1, by omega⟩ : Fin (n + 2))
  rw [hkey]
  exact boolean_realize_bounded_formula_congr (inferInstance : Nonempty (V β)) _ _ ϕ DVec.nil
private lemma realize_lift2_at2 {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec (V β) n) (x y z₁ z₂ : V β) :
    boolean_realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ v)))) (ϕ ↑ᶠᵇ' 2 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper ϕ (k := 0) 2)]
  rw [boolean_realize_formula_insert_lift2 (DVec.cons z₂ v) x y z₁ (ϕ ↑ᶠᵇ' 1 # 2)]
  exact boolean_realize_formula_insert_lift2 v x y z₂ ϕ

private lemma realize_lift3_at2 {n} (ϕ : bounded_formula L_ZFC (n + 2))
    (v : DVec (V β) n) (x y z₁ z₂ z₃ : V β) :
    boolean_realize_bounded_formula
      (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ (DVec.cons z₃ v))))) (ϕ ↑ᶠᵇ' 3 # 2) DVec.nil =
    boolean_realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper ϕ (k := 1) 2)]
  rw [boolean_realize_formula_insert_lift2 (DVec.cons z₂ (DVec.cons z₃ v)) x y z₁ (ϕ ↑ᶠᵇ' 2 # 2)]
  exact realize_lift2_at2 ϕ v x y z₂ z₃

lemma bSet_models_collection {n} (ϕ : bounded_formula L_ZFC (n + 2)) :
    ⊤ ⊩[V β] axiom_of_collection ϕ := by
  change ⊤ ≤ _
  simp only [axiom_of_collection, boolean_realize_sentence_bd_alls]
  apply le_iInf
  intro xs
  match xs with
  | DVec.cons u xs' =>
    simp only [boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
               boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
               boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq,
               boolean_realize_formula_insert_lift2, realize_lift2_at2, realize_lift3_at2,
               boolean_realize_subst_formula0]
    -- After simp, goal should be `⊤ ≤ realize (cons u xs') (imp ... (∃ ...))`
    -- with the formula bodies being  ϕ.eval at appropriate env
    -- ψ a b := boolean_realize (b :: a :: xs') ϕ  matches the role of ϕ in bSet_axiom_of_collection
    have hcoll := bSet_axiom_of_collection
        (fun a b : bSet β =>
          boolean_realize_bounded_formula (DVec.cons b (DVec.cons a xs')) ϕ DVec.nil)
        (fun x y z => by
          -- need: x =ᴮ y ⊓ realize (x :: z :: xs') ϕ ≤ realize (y :: z :: xs') ϕ
          -- (ψ z x → ψ z y means varying position 0 of cons-cons)
          exact B_ext_left_realize_bounded_formula ϕ (DVec.cons z xs') x y)
        (fun x y z => by
          -- need: x =ᴮ y ⊓ realize (z :: x :: xs') ϕ ≤ realize (z :: y :: xs') ϕ
          exact B_ext_right_realize_bounded_formula ϕ xs' x y z)
    have hu := hcoll.trans (iInf_le _ u)
    -- Try to match goal
    convert hu using 0
-- axiom of union: ∀ u x, x ∈ ⋃u ↔ ∃ y ∈ u, x ∈ y
def axiom_of_union : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, by omega⟩) (union' (bd_var ⟨1, by omega⟩)))
      (bd_ex (bd_and
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))))))

lemma bSet_models_union : ⊤ ⊩[V β] axiom_of_union := by
  change ⊤ ≤ _
  simp only [axiom_of_union, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_Union', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]
  apply le_iInf; intro u; apply le_iInf; intro x
  -- goal: ⊤ ≤ bihimp (x ∈ bv_union u) (⨆ y, y ∈ u ⊓ x ∈ y)
  have heq : x ∈ᴮ bv_union u = ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y :=
    le_antisymm ((bv_union_spec_split u (Γ := x ∈ᴮ bv_union u) x).mp le_rfl)
                ((bv_union_spec_split u (Γ := ⨆ y, y ∈ᴮ u ⊓ x ∈ᴮ y) x).mpr le_rfl)
  rw [heq, bihimp_self]
-- axiom of powerset: ∀ z y, y ∈ P(z) ↔ ∀ x ∈ y, x ∈ z
def axiom_of_powerset : sentence L_ZFC :=
  bd_all (bd_all
    (bd_biimp
      (mem' (bd_var ⟨0, by omega⟩) (Powerset (bd_var ⟨1, by omega⟩)))
      (bd_all (bd_imp
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))))))

lemma bSet_models_powerset : ⊤ ⊩[V β] axiom_of_powerset := by
  change ⊤ ≤ _
  simp only [axiom_of_powerset, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_biimp, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_Powerset', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_eq]
  apply le_iInf; intro z; apply le_iInf; intro y
  -- goal: ⊤ ≤ bihimp (y ∈ bv_powerset z) (⨅ x, x ∈ y ⟹ x ∈ z)
  rw [← subset_unfold']
  -- goal: ⊤ ≤ bihimp (y ∈ bv_powerset z) (y ⊆ z)
  have heq : y ∈ᴮ bv_powerset z = y ⊆ᴮ z :=
    le_antisymm (bv_powerset_spec.mpr le_rfl) (bv_powerset_spec.mp le_rfl)
  rw [heq, bihimp_self]
-- axiom of infinity (src/zfc.lean:332-347)
def axiom_of_infinity : sentence L_ZFC :=
  bd_and
    (bd_and
      (bd_and
        (mem' ∅' ω')
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) ω')
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, by omega⟩) ω')
            (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))
      (bd_ex (bd_and Ord_f (bd_equal ω' (bd_var ⟨0, by omega⟩)))))
    (bd_all (bd_imp Ord_f (bd_imp
      (bd_and (mem' ∅' (bd_var ⟨0, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
          (bd_ex (bd_and
            (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
            (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))
      (subset'' ω' (bd_var ⟨0, by omega⟩)))))

lemma bSet_models_infinity : ⊤ ⊩[V β] axiom_of_infinity := by
  change ⊤ ≤ _
  simp only [axiom_of_infinity, boolean_realize_sentence_all,
             boolean_realize_bounded_formula, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_formula_subset',
             boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term_omega',
             boolean_realize_bounded_term, DVec.nth, Ord_f_is_Ord,
             V_forall, V_exists, V_eq]
  -- Goal: ⊤ ≤ ((∅ ∈ᴮ ω ⊓ ⨅ x, x ∈ᴮ ω ⟹ ⨆ y, y ∈ᴮ ω ⊓ x ∈ᴮ y) ⊓
  --            (⨆ α, Ord α ⊓ ω =ᴮ α)) ⊓
  --           (⨅ α, Ord α ⟹ ((∅ ∈ᴮ α ⊓ ⨅ x, x ∈ᴮ α ⟹ ⨆ y, y ∈ᴮ α ⊓ x ∈ᴮ y) ⟹ ω ⊆ α))
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · -- ∅ ∈ᴮ ω
    exact le_trans bSet_axiom_of_infinity' inf_le_left
  · -- ⨅ x, x ∈ᴮ ω ⟹ ⨆ y, y ∈ᴮ ω ⊓ x ∈ᴮ y
    exact le_trans bSet_axiom_of_infinity' inf_le_right
  · -- ⨆ α, Ord α ⊓ ω =ᴮ α
    apply le_iSup_of_le bSet.omega
    exact le_inf Ord_omega (bv_eq_refl _).symm.le
  · -- ⨅ α, Ord α ⟹ (is_limit α ⟹ ω ⊆ α)
    -- This is omega_least_is_limit
    -- is_limit α = ∅ ∈ᴮ α ⊓ ⨅ x, x ∈ᴮ α ⟹ ⨆ y, y ∈ᴮ α ⊓ x ∈ᴮ y
    -- The goal matches omega_least_is_limit directly
    exact le_trans le_top omega_least_is_limit
-- axiom of regularity: ∀ x, x ≠ ∅ → ∃ y ∈ x, ∀ z ∈ x, z ∉ y
def axiom_of_regularity : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
    (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
        (bd_not (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))))))))

lemma bSet_models_regularity : ⊤ ⊩[V β] axiom_of_regularity := by
  change ⊤ ≤ _
  simp only [axiom_of_regularity, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_mem', boolean_realize_bounded_term_emptyset',
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]
  apply le_iInf; intro x
  rw [← _root_.deduction]
  -- goal: ⊤ ⊓ (x =ᴮ ∅)ᶜ ≤ ⨆ y, y ∈ x ⊓ (⨅ z, z ∈ x ⟹ (z ∈ y)ᶜ)
  rw [top_inf_eq]
  -- goal: (x =ᴮ ∅)ᶜ ≤ ⨆ y, y ∈ x ⊓ (⨅ z, z ∈ x ⟹ (z ∈ y)ᶜ)
  exact bSet_axiom_of_regularity x le_rfl
-- Zorn's lemma (src/zfc.lean:363-376)
def zorns_lemma : sentence L_ZFC :=
  bd_all (bd_imp (bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅'))
    (bd_imp
      (bd_all (bd_imp
        (bd_and (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
          (bd_all (bd_all (bd_imp
            (bd_and (mem' (bd_var ⟨1, by omega⟩) (bd_var ⟨2, by omega⟩))
                    (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩)))
            (bd_or (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
                   (subset'' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)))))))
        (mem' (union' (bd_var ⟨0, by omega⟩)) (bd_var ⟨1, by omega⟩))))
      (bd_ex (bd_and (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩))
        (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
          (bd_imp (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩))
            (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))))

lemma bSet_models_Zorn : ⊤ ⊩[V β] zorns_lemma := by
  change ⊤ ≤ _
  simp only [zorns_lemma, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_not, boolean_realize_bounded_formula_and,
             boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_or,
             boolean_realize_bounded_formula_subset', boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_term_emptyset', boolean_realize_bounded_term_Union',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_exists, V_eq]
  -- After simp, goal should match bSet_zorns_lemma' exactly
  exact bSet_zorns_lemma'
-- ============================================================
-- The ZFC theory (src/zfc.lean:378-399)
-- ============================================================

/-- The theory ZFC: a set of L_ZFC-sentences. -/
def ZFC : SentTheory L_ZFC :=
  {axiom_of_emptyset, axiom_of_ordered_pairs, axiom_of_extensionality, axiom_of_union,
   axiom_of_powerset, axiom_of_infinity, axiom_of_regularity, zorns_lemma} ∪
  ⋃ (n : ℕ), axiom_of_collection '' (Set.univ : Set (bounded_formula L_ZFC (n + 2)))

/-- The fundamental theorem of forcing: bSet β models all of ZFC. -/
theorem bSet_models_ZFC : ⊤ ⊩ₜ[V β] ZFC := by
  simp only [all_forced_in]
  apply le_iInf; intro f; apply le_iInf; intro hf
  simp only [ZFC, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
             Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and] at hf
  rcases hf with (hf | ⟨n, ϕ, rfl⟩)
  · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bSet_models_emptyset
    · exact bSet_models_ordered_pairs
    · exact bSet_models_extensionality
    · exact bSet_models_union
    · exact bSet_models_powerset
    · exact bSet_models_infinity
    · exact bSet_models_regularity
    · exact bSet_models_Zorn
  · exact bSet_models_collection _

/-- ZFC is consistent. -/
theorem ZFC_consistent {β : Type 0} [NontrivialCompleteBooleanAlgebra β] :
    SentTheory.is_consistent ZFC :=
  consis_of_exists_bmodel (β := β) (S := V β) bSet_models_ZFC

-- ============================================================
-- Functional-relation formulas (src/zfc.lean:402-470)
-- ============================================================

def is_func_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (mem' (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨4, by omega⟩))
        (mem' (pair' (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨4, by omega⟩)))
      (bd_imp (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))
              (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))))))

@[simp] lemma realize_is_func_f {f : V β} :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_func_f DVec.nil = is_func f := by
  simp only [is_func_f, is_func, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term_pair',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]

def is_total'_f : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f DVec.nil =
    is_total x y f := by
  simp only [is_total'_f, is_total, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]

def is_total'_f₂ : bounded_formula L_ZFC 3 :=
  bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨2, by omega⟩))
    (bd_ex (bd_and
      (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨4, by omega⟩))
      (mem' (pair' (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨2, by omega⟩)))))

@[simp] lemma realize_is_total'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_total'_f₂ DVec.nil =
    is_total y x f := by
  simp only [is_total'_f₂, is_total, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term, DVec.nth,
             V_forall, V_exists, V_eq]

def is_func'_f : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f

def is_func'_f₂ : bounded_formula L_ZFC 3 :=
  bd_and (is_func_f.cast (by omega)) is_total'_f₂

@[simp] lemma realize_is_func'_f {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f DVec.nil =
    is_func' x y f := by
  simp only [is_func'_f, is_func', boolean_realize_bounded_formula_and,
             boolean_realize_cast_bounded_formula, DVec.trunc, realize_is_func_f,
             realize_is_total'_f]

@[simp] lemma realize_is_func'_f₂ {x y f : V β} :
    boolean_realize_bounded_formula
      (DVec.cons f (DVec.cons y (DVec.cons x DVec.nil))) is_func'_f₂ DVec.nil =
    is_func' y x f := by
  simp only [is_func'_f₂, is_func', boolean_realize_bounded_formula_and,
             boolean_realize_cast_bounded_formula, DVec.trunc, realize_is_func_f,
             realize_is_total'_f₂]

/-- at_most_f [y, x] ↔ larger_than x y (surjection from subset of y onto x) -/
def at_most_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_ex
    (bd_and
      (bd_and
        (subset'' (bd_var ⟨1, by omega⟩) (bd_var ⟨3, by omega⟩))
        (is_func'_f₂.cast (by omega)))
      (bd_all (bd_imp (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
        (bd_ex (bd_and
          (mem' (bd_var ⟨0, by omega⟩) (bd_var ⟨3, by omega⟩))
          (mem' (pair' (bd_var ⟨0, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨2, by omega⟩))))))))

@[simp] lemma realize_at_most_f {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) at_most_f DVec.nil =
    larger_than x y := by
  simp only [at_most_f, boolean_realize_bounded_formula, boolean_realize_bounded_formula_ex,
             boolean_realize_bounded_formula_and, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_subset', boolean_realize_cast_bounded_formula,
             boolean_realize_bounded_term_pair', boolean_realize_bounded_term,
             DVec.trunc, DVec.nth, V_forall, V_exists, V_eq, realize_is_func'_f₂]
  unfold larger_than is_surj
  -- LHS and RHS are α-equivalent (bound var name difference only)
  rfl

def is_inj_f : bounded_formula L_ZFC 1 :=
  bd_all (bd_all (bd_all (bd_all
    (bd_imp
      (bd_and
        (bd_and
          (mem' (pair' (bd_var ⟨3, by omega⟩) (bd_var ⟨1, by omega⟩)) (bd_var ⟨4, by omega⟩))
          (mem' (pair' (bd_var ⟨2, by omega⟩) (bd_var ⟨0, by omega⟩)) (bd_var ⟨4, by omega⟩)))
        (bd_equal (bd_var ⟨1, by omega⟩) (bd_var ⟨0, by omega⟩)))
      (bd_equal (bd_var ⟨3, by omega⟩) (bd_var ⟨2, by omega⟩))))))

@[simp] lemma realize_is_inj_f (f : V β) :
    boolean_realize_bounded_formula (DVec.cons f DVec.nil) is_inj_f DVec.nil = is_inj f := by
  simp only [is_inj_f, is_inj, boolean_realize_bounded_formula, boolean_realize_bounded_formula_mem',
             boolean_realize_bounded_formula_and, boolean_realize_bounded_term_pair',
             boolean_realize_bounded_term, DVec.nth, V_forall, V_eq]

def injects_into_f : bounded_formula L_ZFC 2 :=
  bd_ex (bd_and is_func'_f (is_inj_f.cast (by omega)))

@[simp] lemma realize_injects_into {x y : V β} :
    boolean_realize_bounded_formula (DVec.cons y (DVec.cons x DVec.nil)) injects_into_f DVec.nil =
    injects_into x y := by
  simp only [injects_into_f, boolean_realize_bounded_formula_ex, boolean_realize_bounded_formula_and,
             boolean_realize_cast_bounded_formula, DVec.trunc, realize_is_func'_f,
             realize_is_inj_f, V_exists]
  unfold injects_into
  rfl

def non_empty_f : bounded_formula L_ZFC 1 := bd_not (bd_equal (bd_var ⟨0, by omega⟩) ∅')

@[simp] lemma non_empty_f_is_non_empty {x : V β} :
    boolean_realize_bounded_formula (DVec.cons x DVec.nil) non_empty_f DVec.nil = not_empty x := by
  simp only [non_empty_f, not_empty, boolean_realize_bounded_formula_not,
             boolean_realize_bounded_formula, boolean_realize_bounded_term_emptyset',
             boolean_realize_bounded_term, DVec.nth, V_eq]
  rfl

-- ============================================================
-- The CH formula (src/zfc.lean:481-502)
-- ============================================================

/-- The continuum hypothesis as an L_ZFC sentence. -/
def CH_f : sentence L_ZFC :=
  bd_all (bd_imp Ord_f
    (bd_or
      (substmax_bounded_formula at_most_f ω')
      (subst0_bounded_formula at_most_f (Powerset omega'))))

lemma CH_f_is_CH : ⟦CH_f⟧[V β] = CH₂ := by
  -- L3 proof: simp [-substmax_bounded_formula, CH_f, CH₂, neg_supr, sup_assoc, h1, h2, lattice.imp]
  -- where h1, h2 reduce substmax/subst0 by refl.
  have h1 : ∀ x : V β, boolean_realize_bounded_formula (DVec.cons x DVec.nil)
      (substmax_bounded_formula at_most_f ω') DVec.nil =
      boolean_realize_bounded_formula
        (DVec.cons x (DVec.cons (bSet.omega : V β) DVec.nil)) at_most_f DVec.nil := by
    intro x; rfl
  have h2 : ∀ x : V β, boolean_realize_bounded_formula (DVec.cons x DVec.nil)
      (subst0_bounded_formula at_most_f (Powerset omega')) DVec.nil =
      boolean_realize_bounded_formula
        (DVec.cons (bv_powerset (bSet.omega : V β)) (DVec.cons x DVec.nil)) at_most_f DVec.nil := by
    intro x; rfl
  simp only [CH_f, boolean_realize_sentence_all, boolean_realize_bounded_formula,
             boolean_realize_bounded_formula_or, Ord_f_is_Ord, h1, h2, realize_at_most_f,
             imp, CH₂, compl_iSup, compl_inf, compl_compl, sup_assoc]
  -- `realize_at_most_f` is stated for `x y : V β`; the terms here mix
  -- `(V β).carrier` and `bSet β`, so rewrite at default transparency.
  refine iInf_congr fun x => ?_
  erw [realize_at_most_f, realize_at_most_f]

lemma CH_f_sound {Γ : β} : (Γ ⊩[V β] CH_f) ↔ Γ ≤ CH₂ := by
  change _ ≤ _ ↔ _ ≤ _
  rw [CH_f_is_CH]

lemma neg_CH_f_sound {Γ : β} : (Γ ⊩[V β] (bd_not CH_f : sentence L_ZFC)) ↔ Γ ≤ CH₂ᶜ := by
  change _ ≤ _ ↔ _ ≤ _
  rw [boolean_realize_sentence_not, CH_f_is_CH]

-- ============================================================
-- CH is unprovable from ZFC (src/zfc.lean:508-536)
-- ============================================================

open PSet Cardinal

section CH_unprovable

local notation "𝔹" => 𝔹_cohen

lemma V_𝔹_cohen_models_neg_CH : ⊤ ⊩[V 𝔹] (bd_not CH_f : sentence L_ZFC) := by
  rw [neg_CH_f_sound]; exact neg_CH₂

instance V_𝔹_nonempty : Nonempty (V 𝔹) := ⟨bSet.empty⟩

theorem CH_f_unprovable : ¬ (ZFC ⊢ₛ' CH_f) :=
  unprovable_of_model_neg (V 𝔹) bSet_models_ZFC nontrivial_bot_lt_top V_𝔹_cohen_models_neg_CH

end CH_unprovable

open collapse_algebra

section neg_CH_unprovable

instance V_𝔹_collapse_nonempty : Nonempty (V 𝔹_collapse) := ⟨bSet.empty⟩

lemma V_𝔹_collapse_models_CH : ⊤ ⊩[V 𝔹_collapse] CH_f := by
  rw [CH_f_sound]; exact CH₂_true

theorem neg_CH_f_unprovable : ¬ (ZFC ⊢ₛ' (bd_not CH_f : sentence L_ZFC)) := by
  apply unprovable_of_model_neg (V 𝔹_collapse) bSet_models_ZFC nontrivial_bot_lt_top
  rw [forced_in_not]
  exact V_𝔹_collapse_models_CH

end neg_CH_unprovable

-- ============================================================
-- CH as a first-order formula (src/zfc.lean:538-552)
-- ============================================================

section CH_formula_sec

def Powerset_t : term L_ZFC → term L_ZFC := preterm.app (preterm.func ZFC_func.P)
def omega_t : term L_ZFC := preterm.func ZFC_func.ω
def leq_f : formula L_ZFC := at_most_f.fst
def is_ordinal : formula L_ZFC := Ord_f.fst

def CH_formula : formula L_ZFC :=
  ∀' (is_ordinal ⟹ or' (leq_f[omega_t // 1]f) (leq_f[Powerset_t omega_t // 0]f))

lemma CH_f_fst : CH_f.fst = CH_formula := by
  simp only [CH_f, CH_formula, bounded_preformula.fst, substmax_bounded_formula_fst,
             subst0_bounded_formula_fst, leq_f, is_ordinal]
  rfl

end CH_formula_sec
