import ErdosProblems.Erdos577.FiniteExchange
import ErdosProblems.Erdos577.PathMasks

/-! Encoding an arbitrary disjoint path and quadrilateral by sixteen cross-edge bits. -/

namespace Erdos577.PathExchange

open Finset Function
open scoped BigOperators

def encode (b : Fin 16 → Bool) : ℕ := (BitVec.ofBoolListLE (List.ofFn b)).toNat

lemma encode_lt (b : Fin 16 → Bool) : encode b < 65536 := by
  have h := (BitVec.ofBoolListLE (List.ofFn b)).isLt
  simpa only [encode, List.length_ofFn, Nat.reducePow] using h

lemma testBit_encode (b : Fin 16 → Bool) (i : Fin 16) :
    (encode b).testBit i.val = b i := by
  change (BitVec.ofBoolListLE (List.ofFn b)).getLsbD i.val = b i
  rw [BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt)]
  exact List.getElem_ofFn _

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The path occupies labels 0--3 and the quadrilateral labels 4--7. -/
def labeling (p : FourPath G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    Fin 8 ↪ V :=
  finSumFinEquiv.symm.toEmbedding.trans {
    toFun := Sum.elim p.vertices q
    inj' := by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (p.vertices.injective hab)
        | inr b =>
          exact False.elim ((disjoint_left.mp hd)
            ((FourPath.mem_support p _).mpr ⟨a, rfl⟩)
            ((Quadrilateral.mem_support q _).mpr ⟨b, hab.symm⟩))
      | inr a =>
        cases b with
        | inl b =>
          exact False.elim ((disjoint_left.mp hd)
            ((FourPath.mem_support p _).mpr ⟨b, hab.symm⟩)
            ((Quadrilateral.mem_support q _).mpr ⟨a, rfl⟩))
        | inr b => exact congrArg Sum.inr (q.injective hab) }

lemma labeling_left (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (i : Fin 4) :
    labeling p q hd (Fin.castAdd 4 i) = p.vertices i := by
  change Sum.elim p.vertices q (finSumFinEquiv.symm (Fin.castAdd 4 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

lemma labeling_right (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (i : Fin 4) :
    labeling p q hd (Fin.natAdd 4 i) = q i := by
  change Sum.elim p.vertices q (finSumFinEquiv.symm (Fin.natAdd 4 i)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

lemma labeling_image (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) :
    univ.image (labeling p q hd) = p.support ∪ q.support := by
  ext v
  simp only [mem_image, mem_univ, true_and, mem_union,
    FourPath.mem_support, Quadrilateral.mem_support]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨a, rfl⟩ := (finSumFinEquiv (m := 4) (n := 4)).surjective i
    cases a with
    | inl a => exact Or.inl ⟨a, (labeling_left p q hd a).symm⟩
    | inr a => exact Or.inr ⟨a, (labeling_right p q hd a).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd 4 i, labeling_left p q hd i⟩
    · exact ⟨Fin.natAdd 4 i, labeling_right p q hd i⟩

variable [DecidableRel G.Adj]

def bits (p : FourPath G) (q : Quadrilateral G) (i : Fin 16) : Bool :=
  decide (G.Adj (p.vertices ⟨i.val / 4, by omega⟩) (q ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩))

def encoded (p : FourPath G) (q : Quadrilateral G) : Fin 65536 :=
  ⟨encode (bits p q), encode_lt (bits p q)⟩

omit [DecidableEq V] in
lemma encoded_bit (p : FourPath G) (q : Quadrilateral G) (i j : Fin 4) :
    (encoded p q).val.testBit (4 * i.val + j.val) = decide (G.Adj (p.vertices i) (q j)) := by
  have h := testBit_encode (bits p q) ⟨4 * i.val + j.val, by omega⟩
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simpa only [encoded, bits, hi, hj, Fin.eta] using h

/-- Every edge retained by the finite model is an edge of the actual graph. -/
def modelCopy (p : FourPath G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (graph (encoded p q).val).Copy G where
  toHom := {
    toFun := labeling p q hd
    map_rel' := by
      have hr {a b : Fin 8} (h : relation (encoded p q).val a b) :
          G.Adj (labeling p q hd a) (labeling p q hd b) := by
        rcases h with h | ⟨ha, hb, hbit⟩
        · simp only [basePairs, mem_insert, mem_singleton] at h
          rcases h with h | h | h | h | h | h | h <;>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          · exact p.adjacent 0
          · exact p.adjacent 1
          · exact p.adjacent 2
          · exact q.adjacent 0
          · exact q.adjacent 1
          · exact q.adjacent 2
          · exact (q.adjacent 3).symm
        · let i : Fin 4 := ⟨a.val, ha⟩
          let j : Fin 4 := ⟨b.val - 4, by omega⟩
          have hea : Fin.castAdd 4 i = a := Fin.ext rfl
          have heb : Fin.natAdd 4 j = b := Fin.ext (by dsimp [j]; omega)
          have hei : 4 * a.val + b.val - 4 = 4 * i.val + j.val := by dsimp [i, j]; omega
          rw [hei, encoded_bit] at hbit
          rw [← hea, ← heb, labeling_left, labeling_right]
          exact of_decide_eq_true hbit
      intro a b hab
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, hab | hba⟩
      · exact hr hab
      · exact (hr hba).symm }
  injective' := (labeling p q hd).injective

lemma modelCopy_image (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) :
    univ.image (modelCopy p q hd) = p.support ∪ q.support := labeling_image p q hd

lemma crossCount_eq_double_sum (m : ℕ) : crossCount m =
    ∑ i : Fin 4, ∑ j : Fin 4, (m.testBit (4 * i.val + j.val)).toNat := by
  simp [crossCount, List.range_succ, Fin.sum_univ_succ, Nat.add_assoc]

lemma crossCount_encoded (p : FourPath G) (q : Quadrilateral G) :
    crossCount (encoded p q).val = contacts G p.support q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  rw [crossCount_eq_double_sum, FourPath.support, Quadrilateral.support,
    contacts_image_left G _ _ p.vertices.injective]
  simp_rw [degreeIn_image G _ _ _ hq, encoded_bit]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases h : G.Adj (p.vertices i) (q j) <;> simp [h]

end Erdos577.PathExchange
