import ErdosProblems.Erdos1188.CrossPairPool

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Closing the sparse frame with empty, singleton, and cross-pair supports
-/

namespace Erdos1188

/-- Codes for the closing supports: empty, a singleton, or a cross pair. -/
abbrev ClosingSupportCode (m h : ℕ) := Option (Fin m ⊕ CrossPair m h)

/-- Convert a closing code to its base-coordinate support. -/
def closingCodeSupport {m h : ℕ} (hle : h ≤ m) :
    ClosingSupportCode m h → Finset (Fin m)
  | none => ∅
  | some (Sum.inl i) => {i}
  | some (Sum.inr c) => crossPairSupport hle c

/-- Closing code supports are injective when both sides of the cross-pair split
are nonempty. -/
theorem closingCodeSupport_injective {m h : ℕ}
    (hhpos : 0 < h) (hhlt : h < m) :
    Function.Injective (closingCodeSupport (Nat.le_of_lt hhlt)) := by
  intro a b hab
  have hle := Nat.le_of_lt hhlt
  have hpair : ∀ c : CrossPair m h, (crossPairSupport hle c).card = 2 := by
    intro c
    exact Finset.card_pair (crossPair_low_ne_high hle c)
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b =>
          cases b with
          | inl j => simpa [closingCodeSupport] using hab
          | inr c =>
              exfalso
              have hc := congrArg (fun s : Finset (Fin m) => s.card) hab
              simp only [closingCodeSupport, Finset.card_empty, hpair c] at hc
              omega
  | some a =>
      cases a with
      | inl i =>
          cases b with
          | none => simpa [closingCodeSupport] using hab
          | some b =>
              cases b with
              | inl j =>
                  simp only [closingCodeSupport, Finset.singleton_inj] at hab
                  exact congrArg (fun x => some (Sum.inl x)) hab
              | inr c =>
                  exfalso
                  have hc := congrArg (fun s : Finset (Fin m) => s.card) hab
                  simp only [closingCodeSupport, Finset.card_singleton, hpair c] at hc
                  omega
      | inr c =>
          cases b with
          | none =>
              exfalso
              have hc := congrArg (fun s : Finset (Fin m) => s.card) hab
              simp only [closingCodeSupport, hpair c, Finset.card_empty] at hc
              omega
          | some b =>
              cases b with
              | inl j =>
                  exfalso
                  have hc := congrArg (fun s : Finset (Fin m) => s.card) hab
                  simp only [closingCodeSupport, hpair c, Finset.card_singleton] at hc
                  omega
              | inr d =>
                  exact congrArg (fun x => some (Sum.inr x))
                    (crossPairSupport_injective hle hab)

/-- `Fin m ⊕ Fin 1` is the empty-or-singleton code type. -/
def finSumOneEquivOption (m : ℕ) : Fin m ⊕ Fin 1 ≃ Option (Fin m) where
  toFun
    | Sum.inl i => some i
    | Sum.inr _ => none
  invFun
    | none => Sum.inr 0
    | some i => Sum.inl i
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr j => simp only; congr; exact Subsingleton.elim _ _
  right_inv x := by cases x <;> rfl

/-- The first `m+1` indices encode all singletons and the empty support. -/
def finSuccEquivOption (m : ℕ) : Fin (m + 1) ≃ Option (Fin m) :=
  (finSumFinEquiv (m := m) (n := 1)).symm.trans (finSumOneEquivOption m)

/-- Reassociate `Option A ⊕ B` as `Option (A ⊕ B)`. -/
def optionSumEquivOptionSum (A B : Type*) : Option A ⊕ B ≃ Option (A ⊕ B) where
  toFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  invFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  left_inv x := by
    cases x with
    | inl x => cases x <;> rfl
    | inr x => rfl
  right_inv x := by
    cases x with
    | none => rfl
    | some x => cases x <;> rfl

/-- Split `Fin P` into the reserved first `m+1` indices and a remainder. -/
def splitClosingFin {m P : ℕ} (hsize : m + 1 ≤ P) :
    Fin P ≃ Fin (m + 1) ⊕ Fin (P - (m + 1)) :=
  (finCongr (Nat.add_sub_of_le hsize).symm).trans
    (finSumFinEquiv (m := m + 1) (n := P - (m + 1))).symm

/-- Embed closing residues into empty/singleton/cross-pair codes, reserving all
singletons and the empty code before using arbitrary cross pairs. -/
noncomputable def closingCodeEmbedding {m h P : ℕ}
    (hsize : m + 1 ≤ P) (hcap : P - (m + 1) ≤ h * (m - h)) :
    Fin P ↪ ClosingSupportCode m h := by
  let rem : Fin (P - (m + 1)) ↪ CrossPair m h :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa [CrossPair, Fintype.card_prod] using hcap))
  exact (splitClosingFin hsize).toEmbedding |>.trans
    (Function.Embedding.sumMap (finSuccEquivOption m).toEmbedding rem) |>.trans
    (optionSumEquivOptionSum (Fin m) (CrossPair m h)).toEmbedding

/-- The closing support map on `ZMod P`. -/
noncomputable def sparseClosingFixed {m h P : ℕ} [NeZero P]
    (hle : h ≤ m) (hsize : m + 1 ≤ P)
    (hcap : P - (m + 1) ≤ h * (m - h)) :
    ZMod P → Finset (Fin m) := fun a =>
  closingCodeSupport hle
    (closingCodeEmbedding hsize hcap ((ZMod.finEquiv P).symm a))

/-- The closing support map is injective. -/
theorem sparseClosingFixed_injective {m h P : ℕ} [NeZero P]
    (hhpos : 0 < h) (hhlt : h < m)
    (hsize : m + 1 ≤ P)
    (hcap : P - (m + 1) ≤ h * (m - h)) :
    Function.Injective
      (sparseClosingFixed (Nat.le_of_lt hhlt) hsize hcap) := by
  exact (closingCodeSupport_injective hhpos hhlt).comp
    ((closingCodeEmbedding hsize hcap).injective.comp (ZMod.finEquiv P).symm.injective)

/-- The reserved closing residue protecting base coordinate `i`. -/
noncomputable def sparseClosingEscape {m h P : ℕ} [NeZero P]
    (hsize : m + 1 ≤ P) (hcap : P - (m + 1) ≤ h * (m - h))
    (i : Fin m) : ZMod P :=
  ZMod.finEquiv P
    ((splitClosingFin hsize).symm
      (Sum.inl ((finSuccEquivOption m).symm (some i))))

/-- Every base coordinate occurs in its reserved singleton closing support. -/
theorem sparseClosing_protects {m h P : ℕ} [NeZero P]
    (hle : h ≤ m) (hsize : m + 1 ≤ P)
    (hcap : P - (m + 1) ≤ h * (m - h)) :
    ClosingProtects (ZMod P)
      (sparseClosingFixed hle hsize hcap)
      (sparseClosingEscape hsize hcap) := by
  intro i
  simp [sparseClosingFixed, sparseClosingEscape, closingCodeEmbedding,
    closingCodeSupport, optionSumEquivOptionSum]

end Erdos1188
