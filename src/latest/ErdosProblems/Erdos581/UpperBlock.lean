import ErdosProblems.Erdos581.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace

/-!
# Erdős 581: the finite-field block for the upper bound

This is Kopparty's characteristic-two Cayley graph.  The analytic Fourier
estimate is developed separately; this file proves the exact cardinalities
and triangle-freeness of the block.
-/

open Finset Set
open scoped BigOperators Matrix

namespace Erdos581.UpperBlock

noncomputable section

abbrev F (t : ℕ) := GaloisField 2 (t + 1)

local instance (t : ℕ) : Fintype (F t) := Fintype.ofFinite _
local instance (t : ℕ) : DecidableEq (F t) := Classical.decEq _

def q (t : ℕ) : ℕ := 2 ^ (t + 1)

lemma card_F (t : ℕ) : Fintype.card (F t) = q t := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card (p := 2) (n := t + 1) (by omega)]
  rfl

def tr (t : ℕ) : F t →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) (F t)

lemma zmod_two_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hlt : z.val < 2 := ZMod.val_lt z
  have hz : z.val = 0 ∨ z.val = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : z.val ≤ 1)
  rcases hz with hz | hz
  · left
    rw [← ZMod.val_eq_zero]
    exact hz
  · right
    apply ZMod.val_injective
    simpa only [ZMod.val_one 2] using hz

lemma exists_trace_one (t : ℕ) : ∃ b : F t, tr t b = 1 := by
  have htr := (traceForm_nondegenerate (ZMod 2) (F t)).1 (1 : F t)
  simp_rw [Algebra.traceForm_apply] at htr
  obtain ⟨b, hb⟩ : ∃ b : F t, tr t (1 * b) ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero (htr h)
  refine ⟨b, ?_⟩
  have hne : tr t b ≠ 0 := by simpa [tr] using hb
  exact (zmod_two_eq_zero_or_one (tr t b)).resolve_left hne

def traceOneFinset (t : ℕ) : Finset (F t) := Finset.univ.filter fun x ↦ tr t x = 1
def traceZeroFinset (t : ℕ) : Finset (F t) := Finset.univ.filter fun x ↦ tr t x = 0
abbrev traceOne (t : ℕ) := ↥(traceOneFinset t)
abbrev traceZero (t : ℕ) := ↥(traceZeroFinset t)

private noncomputable def traceZeroEquivTraceOne (t : ℕ) :
    traceZero t ≃ traceOne t := by
  let b : F t := Classical.choose (exists_trace_one t)
  have hb : tr t b = 1 := Classical.choose_spec (exists_trace_one t)
  refine
    { toFun := fun x ↦ ⟨x.1 + b, by simpa [traceOneFinset, traceZeroFinset,
          map_add, hb] using x.2⟩
      invFun := fun x ↦ ⟨x.1 + b, by
        have hx : tr t x.1 = 1 := by simpa [traceOneFinset] using x.2
        simp only [traceZeroFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [map_add, hx, hb, CharTwo.add_self_eq_zero]⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        simp only [add_assoc]
        rw [show b + b = 0 by exact CharTwo.add_self_eq_zero b, add_zero]
      right_inv := fun x ↦ by
        apply Subtype.ext
        simp only [add_assoc]
        rw [show b + b = 0 by exact CharTwo.add_self_eq_zero b, add_zero] }

lemma two_mul_card_traceOne (t : ℕ) :
    2 * Fintype.card (traceOne t) = q t := by
  let T : Finset (F t) := traceOneFinset t
  let Z : Finset (F t) := traceZeroFinset t
  have hTZ : T.card = Z.card := by
    have hT : T.card = Fintype.card (traceOne t) := by simp [T]
    have hZ : Z.card = Fintype.card (traceZero t) := by simp [Z]
    rw [hT, hZ, Fintype.card_congr (traceZeroEquivTraceOne t)]
  have hunion : T ∪ Z = Finset.univ := by
    ext x
    simp only [T, Z, traceOneFinset, traceZeroFinset, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro
      trivial
    · intro
      exact (zmod_two_eq_zero_or_one (tr t x)).symm
  have hdisj : Disjoint T Z := by
    simp only [Finset.disjoint_left, T, Z, traceOneFinset, traceZeroFinset,
      Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx1 hx0
    exact zero_ne_one (hx0.symm.trans hx1)
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, card_F] at hcard
  have hT : T.card = Fintype.card (traceOne t) := by simp [T]
  rw [← hT]
  omega

lemma traceOne_ne_zero {t : ℕ} (x : traceOne t) : x.1 ≠ 0 := by
  intro hx
  have hxmem := x.2
  have : tr t x.1 = 1 := by simpa [traceOneFinset] using hxmem
  rw [hx, map_zero] at this
  exact zero_ne_one this

abbrev V (t : ℕ) := Fin 3 → F t

def generator {t : ℕ} (p : traceOne t × (F t)ˣ) : V t :=
  ![p.1.1 * p.2.1, p.1.1 * p.2.1 ^ 2, p.1.1 * p.2.1 ^ 3]

lemma generator_injective {t : ℕ} : Function.Injective (generator (t := t)) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h1 : x.1 * y.1 = x'.1 * y'.1 := congr_fun h 0
  have h2 : x.1 * y.1 ^ 2 = x'.1 * y'.1 ^ 2 := congr_fun h 1
  have hx : x.1 ≠ 0 := traceOne_ne_zero x
  have hx' : x'.1 ≠ 0 := traceOne_ne_zero x'
  have hy : y.1 ≠ 0 := Units.ne_zero y
  have hy' : y'.1 ≠ 0 := Units.ne_zero y'
  have heqY : y.1 = y'.1 := by
    calc
      y.1 = (x.1 * y.1 ^ 2) / (x.1 * y.1) := by field_simp
      _ = (x'.1 * y'.1 ^ 2) / (x'.1 * y'.1) := by rw [h1, h2]
      _ = y'.1 := by field_simp
  have heqX : x.1 = x'.1 := by
    rw [heqY] at h1
    exact mul_right_cancel₀ hy' h1
  congr
  · exact Subtype.ext heqX
  · exact Units.ext heqY

def generators (t : ℕ) : Finset (V t) :=
  Finset.univ.image generator

lemma card_generators (t : ℕ) :
    (generators t).card = Fintype.card (traceOne t) * (q t - 1) := by
  rw [generators, Finset.card_image_of_injective _ generator_injective]
  rw [Finset.card_univ, Fintype.card_prod]
  have hu : Fintype.card (F t)ˣ = q t - 1 := by
    rw [Fintype.card_units]
    simp [card_F]
  rw [hu]

lemma zero_notMem_generators (t : ℕ) : (0 : V t) ∉ generators t := by
  intro h
  obtain ⟨p, _hp, hp0⟩ := Finset.mem_image.mp h
  have hcoord := congr_fun hp0 0
  simp only [generator, Matrix.cons_val_zero, Pi.zero_apply] at hcoord
  exact mul_ne_zero (traceOne_ne_zero p.1) (Units.ne_zero p.2) hcoord

private lemma generator_sum_ne_zero {t : ℕ}
    (p₁ p₂ p₃ : traceOne t × (F t)ˣ) :
    generator p₁ + generator p₂ + generator p₃ ≠ 0 := by
  intro hsum
  let x₁ : F t := p₁.1.1
  let x₂ : F t := p₂.1.1
  let x₃ : F t := p₃.1.1
  let y₁ : F t := p₁.2.1
  let y₂ : F t := p₂.2.1
  let y₃ : F t := p₃.2.1
  have hx₁ : x₁ ≠ 0 := traceOne_ne_zero p₁.1
  have hx₂ : x₂ ≠ 0 := traceOne_ne_zero p₂.1
  have hx₃ : x₃ ≠ 0 := traceOne_ne_zero p₃.1
  have hy₁ : y₁ ≠ 0 := Units.ne_zero p₁.2
  have hy₂ : y₂ ≠ 0 := Units.ne_zero p₂.2
  have hy₃ : y₃ ≠ 0 := Units.ne_zero p₃.2
  have e1 : x₁ * y₁ + x₂ * y₂ + x₃ * y₃ = 0 := congr_fun hsum 0
  have e2 : x₁ * y₁ ^ 2 + x₂ * y₂ ^ 2 + x₃ * y₃ ^ 2 = 0 := congr_fun hsum 1
  have e3 : x₁ * y₁ ^ 3 + x₂ * y₂ ^ 3 + x₃ * y₃ ^ 3 = 0 := congr_fun hsum 2
  change x₁ * y₁ + x₂ * y₂ + x₃ * y₃ = 0 at e1
  change x₁ * y₁ ^ 2 + x₂ * y₂ ^ 2 + x₃ * y₃ ^ 2 = 0 at e2
  change x₁ * y₁ ^ 3 + x₂ * y₂ ^ 3 + x₃ * y₃ ^ 3 = 0 at e3
  by_cases h12 : y₁ = y₂
  · by_cases h13 : y₁ = y₃
    · have hX : x₁ + x₂ + x₃ = 0 := by
        rw [← h12, ← h13] at e1
        apply mul_right_cancel₀ hy₁
        simpa [add_mul] using e1
      have ht := congr_arg (tr t) hX
      have hx1tr : tr t x₁ = 1 := by simpa [x₁, traceOneFinset] using p₁.1.2
      have hx2tr : tr t x₂ = 1 := by simpa [x₂, traceOneFinset] using p₂.1.2
      have hx3tr : tr t x₃ = 1 := by simpa [x₃, traceOneFinset] using p₃.1.2
      simp only [map_add, map_zero, hx1tr, hx2tr, hx3tr] at ht
      have hone : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
      rw [hone, zero_add] at ht
      exact one_ne_zero ht
    · have hfac : x₃ * y₃ * (y₃ - y₁) = 0 := by
        rw [← h12] at e1 e2
        linear_combination e2 - y₁ * e1
      exact mul_ne_zero (mul_ne_zero hx₃ hy₃) (sub_ne_zero.mpr (Ne.symm h13)) hfac
  · by_cases h13 : y₁ = y₃
    · have hfac : x₂ * y₂ * (y₂ - y₁) = 0 := by
        rw [← h13] at e1 e2
        linear_combination e2 - y₁ * e1
      exact mul_ne_zero (mul_ne_zero hx₂ hy₂) (sub_ne_zero.mpr (Ne.symm h12)) hfac
    · by_cases h23 : y₂ = y₃
      · have hfac : x₁ * y₁ * (y₁ - y₂) = 0 := by
          rw [← h23] at e1 e2
          linear_combination e2 - y₂ * e1
        exact mul_ne_zero (mul_ne_zero hx₁ hy₁) (sub_ne_zero.mpr h12) hfac
      · have hfac : x₁ * y₁ * (y₁ - y₂) * (y₁ - y₃) = 0 := by
          linear_combination e3 - (y₂ + y₃) * e2 + (y₂ * y₃) * e1
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero hx₁ hy₁) (sub_ne_zero.mpr h12))
          (sub_ne_zero.mpr h13) hfac

lemma generators_sum_free {t : ℕ} {s₁ s₂ s₃ : V t}
    (h₁ : s₁ ∈ generators t) (h₂ : s₂ ∈ generators t)
    (h₃ : s₃ ∈ generators t) : s₁ + s₂ + s₃ ≠ 0 := by
  obtain ⟨p₁, -, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨p₂, -, rfl⟩ := Finset.mem_image.mp h₂
  obtain ⟨p₃, -, rfl⟩ := Finset.mem_image.mp h₃
  exact generator_sum_ne_zero p₁ p₂ p₃

def graph (t : ℕ) : SimpleGraph (V t) where
  Adj u v := u + v ∈ generators t
  symm := ⟨by intro u v h; simpa [add_comm] using h⟩
  loopless := by
    refine ⟨fun u h ↦ zero_notMem_generators t ?_⟩
    simpa [show u + u = 0 by funext i; exact CharTwo.add_self_eq_zero (u i)] using h

local instance graphAdjDecidable (t : ℕ) : DecidableRel (graph t).Adj :=
  fun _ _ ↦ Finset.decidableMem _ _

lemma graph_adj {t : ℕ} (u v : V t) :
    (graph t).Adj u v ↔ u + v ∈ generators t := Iff.rfl

lemma graph_triangleFree (t : ℕ) : (graph t).CliqueFree 3 := by
  intro s hs
  obtain ⟨u, v, w, huv, huw, hvw, _hs⟩ := SimpleGraph.is3Clique_iff.mp hs
  have hwu : (graph t).Adj w u := ((graph t).adj_comm u w).mp huw
  have hsum := generators_sum_free (graph_adj u v |>.mp huv)
    (graph_adj v w |>.mp hvw)
    (graph_adj w u |>.mp hwu)
  apply hsum
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  linear_combination CharTwo.add_self_eq_zero (u i) +
    CharTwo.add_self_eq_zero (v i) + CharTwo.add_self_eq_zero (w i)

end

end Erdos581.UpperBlock
