import ErdosProblems.Erdos581.UpperBlock
import ErdosProblems.Erdos581.FourierCut
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Polynomial.Roots

/-!
# Erdős 581: spectrum of the characteristic-two block
-/

open Finset Set
open scoped BigOperators ComplexConjugate

namespace Erdos581.UpperBlock

noncomputable section

local instance (t : ℕ) : Fintype (F t) := Fintype.ofFinite _
local instance (t : ℕ) : DecidableEq (F t) := Classical.decEq _

lemma stdAddChar_two_zero : ZMod.stdAddChar (N := 2) 0 = (1 : ℂ) := by simp

lemma stdAddChar_two_one : ZMod.stdAddChar (N := 2) 1 = (-1 : ℂ) := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num,
    ZMod.stdAddChar_coe]
  norm_num
  rw [show (2 : ℂ) * Real.pi * Complex.I / 2 = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

private def traceMulAddHom (t : ℕ) (z : F t) : F t →+ ZMod 2 where
  toFun x := tr t (x * z)
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

def fieldChar (t : ℕ) (z : F t) : AddChar (F t) ℂ :=
  (ZMod.stdAddChar (N := 2)).compAddMonoidHom (traceMulAddHom t z)

@[simp] lemma fieldChar_apply (t : ℕ) (z x : F t) :
    fieldChar t z x = ZMod.stdAddChar (N := 2) (tr t (x * z)) := rfl

private lemma exists_trace_mul_ne_zero {t : ℕ} {z : F t} (hz : z ≠ 0) :
    ∃ x : F t, tr t (x * z) ≠ 0 := by
  have htr := (traceForm_nondegenerate (ZMod 2) (F t)).1 z
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra h
  push Not at h
  apply hz
  apply htr
  intro x
  simpa [mul_comm, tr] using h x

private lemma fieldChar_ne_one {t : ℕ} {z : F t} (hz : z ≠ 0) :
    fieldChar t z ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_trace_mul_ne_zero hz
  intro h
  have hpoint := DFunLike.congr_fun h x
  have htrace : tr t (x * z) = 1 :=
    (zmod_two_eq_zero_or_one _).resolve_left hx
  simp only [fieldChar_apply, htrace, stdAddChar_two_one, Pi.one_apply] at hpoint
  norm_num at hpoint

lemma sum_fieldChar (t : ℕ) (z : F t) :
    ∑ x : F t, fieldChar t z x = if z = 0 then (q t : ℂ) else 0 := by
  classical
  by_cases hz : z = 0
  · subst z
    simp [fieldChar, traceMulAddHom, card_F]
  · rw [if_neg hz]
    exact AddChar.sum_eq_zero_of_ne_one (fieldChar_ne_one hz)

def traceOneCharSum (t : ℕ) (z : F t) : ℂ :=
  ∑ x : traceOne t, fieldChar t z x.1

private lemma sum_filter_traceOne (t : ℕ) (z : F t) :
    (∑ x : F t, if tr t x = 1 then fieldChar t z x else 0) =
      traceOneCharSum t z := by
  classical
  let T := traceOneFinset t
  calc
    (∑ x : F t, if tr t x = 1 then fieldChar t z x else 0) =
        ∑ x ∈ T, fieldChar t z x := by
          rw [← Finset.sum_filter]
          rfl
    _ = ∑ x : traceOne t, fieldChar t z x.1 := by
      apply Finset.sum_subtype T
      intro x
      simp [T, traceOneFinset]

private lemma fieldChar_add_one (t : ℕ) (z x : F t) :
    fieldChar t (z + 1) x = fieldChar t z x -
      2 * if tr t x = 1 then fieldChar t z x else 0 := by
  have harg : tr t (x * (z + 1)) = tr t (x * z) + tr t x := by
    simp [mul_add]
  rw [fieldChar_apply, harg, ZMod.stdAddChar.map_add_eq_mul]
  rcases zmod_two_eq_zero_or_one (tr t x) with hx | hx
  · simp [hx, stdAddChar_two_zero]
  · simp [hx, stdAddChar_two_one]
    ring

private lemma traceOneCharSum_zero_of_ne {t : ℕ} {z : F t}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) : traceOneCharSum t z = 0 := by
  have hzp : z + 1 ≠ 0 := by
    intro h
    have : z = 1 := by
      have := congrArg (fun w : F t ↦ w + 1) h
      simpa [add_assoc, CharTwo.add_self_eq_zero] using this
    exact hz1 this
  have hA := sum_fieldChar t z
  have hB := sum_fieldChar t (z + 1)
  rw [if_neg hz0] at hA
  rw [if_neg hzp] at hB
  have hrel : (∑ x : F t, fieldChar t (z + 1) x) =
      (∑ x : F t, fieldChar t z x) - 2 * traceOneCharSum t z := by
    simp_rw [fieldChar_add_one]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_filter_traceOne]
  rw [hA, hB] at hrel
  have hm : (2 : ℂ) * traceOneCharSum t z = 0 := by
    have hn : -((2 : ℂ) * traceOneCharSum t z) = 0 := by simpa using hrel.symm
    exact neg_eq_zero.mp hn
  exact (mul_eq_zero.mp hm).resolve_left (by norm_num)

lemma traceOneCharSum_eq (t : ℕ) (z : F t) :
    traceOneCharSum t z =
      if z = 0 then (Fintype.card (traceOne t) : ℂ)
      else if z = 1 then -(Fintype.card (traceOne t) : ℂ) else 0 := by
  classical
  by_cases hz0 : z = 0
  · subst z
    simp [traceOneCharSum, fieldChar, traceMulAddHom]
  · rw [if_neg hz0]
    by_cases hz1 : z = 1
    · subst z
      rw [if_pos rfl]
      simp only [traceOneCharSum, fieldChar_apply]
      have hx (x : traceOne t) : tr t (x.1 * (1 : F t)) = 1 := by
        simpa [traceOneFinset] using x.2
      simp_rw [hx, stdAddChar_two_one]
      simp
    · rw [if_neg hz1]
      exact traceOneCharSum_zero_of_ne hz0 hz1

def pairingAddHom (t : ℕ) (a : V t) : V t →+ ZMod 2 where
  toFun v := tr t (∑ i, a i * v i)
  map_zero' := by simp
  map_add' u v := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]

def chi (t : ℕ) (a : V t) : AddChar (V t) ℂ :=
  (ZMod.stdAddChar (N := 2)).compAddMonoidHom (pairingAddHom t a)

@[simp] lemma chi_apply (t : ℕ) (a v : V t) :
    chi t a v = ZMod.stdAddChar (N := 2) (tr t (∑ i, a i * v i)) := rfl

private lemma pairing_single (t : ℕ) (a : V t) (i : Fin 3) (x : F t) :
    tr t (∑ j, a j * (Pi.single i x : V t) j) = tr t (a i * x) := by
  classical
  congr 1
  simp [Pi.single_apply]

lemma chi_injective (t : ℕ) : Function.Injective (chi t) := by
  intro a b hab
  funext i
  have hzero : ∀ x : F t, tr t ((a i - b i) * x) = 0 := by
    intro x
    have hpoint := DFunLike.congr_fun hab (Pi.single i x : V t)
    simp only [chi_apply, pairing_single] at hpoint
    have heq : tr t (a i * x) = tr t (b i * x) :=
      ZMod.injective_stdAddChar hpoint
    rw [sub_mul, map_sub, heq, sub_self]
  have htr := (traceForm_nondegenerate (ZMod 2) (F t)).1 (a i - b i)
  simp_rw [Algebra.traceForm_apply] at htr
  have : a i - b i = 0 := htr hzero
  exact sub_eq_zero.mp this

lemma chi_surjective (t : ℕ) : Function.Surjective (chi t) := by
  have hcard : Fintype.card (V t) = Fintype.card (AddChar (V t) ℂ) :=
    AddChar.card_eq.symm
  exact (Fintype.bijective_iff_injective_and_card (chi t)).2
    ⟨chi_injective t, hcard⟩ |>.2

def cubicValue {t : ℕ} (a : V t) (y : F t) : F t :=
  a (0 : Fin 3) * y + a (1 : Fin 3) * y ^ 2 + a (2 : Fin 3) * y ^ 3

def cubicPolynomial {t : ℕ} (a : V t) : Polynomial (F t) :=
  Polynomial.C (a (2 : Fin 3)) * Polynomial.X ^ 3 +
    Polynomial.C (a (1 : Fin 3)) * Polynomial.X ^ 2 +
      Polynomial.C (a (0 : Fin 3)) * Polynomial.X + Polynomial.C 0

@[simp] lemma eval_cubicPolynomial {t : ℕ} (a : V t) (y : F t) :
    (cubicPolynomial a).eval y = cubicValue a y := by
  simp [cubicPolynomial, cubicValue]
  ring

private lemma cubicPolynomial_sub_one_ne_zero {t : ℕ} (a : V t) :
    cubicPolynomial a - Polynomial.C 1 ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial (F t) ↦ p.coeff 0) h
  simp [cubicPolynomial] at hc

lemma card_units_cubicValue_eq_one_le_three {t : ℕ} (a : V t) :
    (Finset.univ.filter fun y : (F t)ˣ ↦ cubicValue a y.1 = 1).card ≤ 3 := by
  classical
  let Y : Finset (F t)ˣ :=
    Finset.univ.filter fun y : (F t)ˣ ↦ cubicValue a y.1 = 1
  let R : Finset (F t) := (cubicPolynomial a - Polynomial.C 1).roots.toFinset
  have himage : (Y.image fun y : (F t)ˣ ↦ (y.1 : F t)).card = Y.card := by
    rw [Finset.card_image_of_injective]
    intro x y h
    exact Units.ext h
  have hsub : Y.image (fun y : (F t)ˣ ↦ (y.1 : F t)) ⊆ R := by
    intro y hy
    obtain ⟨u, huY, rfl⟩ := Finset.mem_image.mp hy
    have hu : cubicValue a u.1 = 1 := by simpa [Y] using huY
    simp only [R, Multiset.mem_toFinset, Polynomial.mem_roots_sub_C']
    exact ⟨by
      intro heq
      exact cubicPolynomial_sub_one_ne_zero a (sub_eq_zero.mpr heq), by
        simpa using hu⟩
  have hR : R.card ≤ 3 := by
    calc
      R.card ≤ (cubicPolynomial a - Polynomial.C 1).roots.card := by
        exact Multiset.toFinset_card_le _
      _ ≤ (cubicPolynomial a - Polynomial.C 1).natDegree :=
        Polynomial.card_roots' _
      _ ≤ 3 := by
        apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le
        · simpa [cubicPolynomial] using
            (Polynomial.natDegree_cubic_le (a := a (2 : Fin 3))
              (b := a (1 : Fin 3)) (c := a (0 : Fin 3)) (d := (0 : F t)))
        · simp
  change Y.card ≤ 3
  rw [← himage]
  exact (Finset.card_le_card hsub).trans hR

lemma chi_generator {t : ℕ} (a : V t) (p : traceOne t × (F t)ˣ) :
    chi t a (generator p) = fieldChar t (cubicValue a p.2.1) p.1.1 := by
  simp only [chi_apply, fieldChar_apply, generator, cubicValue]
  congr 2
  simp [Fin.sum_univ_succ, generator]
  ring

def eigenvalue (t : ℕ) (ψ : AddChar (V t) ℂ) : ℝ :=
  (∑ s ∈ generators t, ψ s).re

private lemma sum_generators_chi (t : ℕ) (a : V t) :
    ∑ s ∈ generators t, chi t a s =
      ∑ y : (F t)ˣ, traceOneCharSum t (cubicValue a y.1) := by
  classical
  rw [generators, Finset.sum_image]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp_rw [chi_generator]
    rfl
  · exact fun _ _ _ _ h ↦ generator_injective h

lemma eigenvalue_lower (t : ℕ) (ψ : AddChar (V t) ℂ) :
    -(3 * q t : ℝ) ≤ eigenvalue t ψ := by
  classical
  obtain ⟨a, rfl⟩ := chi_surjective t ψ
  rw [eigenvalue, sum_generators_chi, Complex.re_sum]
  let Y : Finset (F t)ˣ :=
    Finset.univ.filter fun y : (F t)ˣ ↦ cubicValue a y.1 = 1
  have hY : Y.card ≤ 3 := by
    simpa [Y] using card_units_cubicValue_eq_one_le_three a
  have hterm (y : (F t)ˣ) :
      -((Fintype.card (traceOne t) : ℝ) *
          if cubicValue a y.1 = 1 then 1 else 0) ≤
        (traceOneCharSum t (cubicValue a y.1)).re := by
    rw [traceOneCharSum_eq]
    by_cases h0 : cubicValue a y.1 = 0
    · simp [h0]
    · by_cases h1 : cubicValue a y.1 = 1
      · simp [h0, h1]
      · simp [h0, h1]
  have hsum := Finset.sum_le_sum fun y (_hy : y ∈ (Finset.univ : Finset (F t)ˣ)) ↦ hterm y
  have hindicator :
      (∑ y : (F t)ˣ, (if cubicValue a y.1 = 1 then (1 : ℝ) else 0)) = Y.card := by
    simp [Y]
  have hleft :
      (∑ y : (F t)ˣ, -((Fintype.card (traceOne t) : ℝ) *
          if cubicValue a y.1 = 1 then 1 else 0)) =
        -(Fintype.card (traceOne t) : ℝ) * Y.card := by
    calc
      _ = ∑ y : (F t)ˣ, -(Fintype.card (traceOne t) : ℝ) *
          (if cubicValue a y.1 = 1 then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = -(Fintype.card (traceOne t) : ℝ) *
          (∑ y : (F t)ˣ, (if cubicValue a y.1 = 1 then 1 else 0)) := by
            rw [Finset.mul_sum]
      _ = _ := by rw [hindicator]
  rw [hleft] at hsum
  have htwo : (2 : ℝ) * Fintype.card (traceOne t) = q t := by
    exact_mod_cast two_mul_card_traceOne t
  have hYreal : (Y.card : ℝ) ≤ 3 := by exact_mod_cast hY
  have hcardnonneg : 0 ≤ (Fintype.card (traceOne t) : ℝ) := by positivity
  calc
    -(3 * q t : ℝ) ≤ -(Fintype.card (traceOne t) : ℝ) * Y.card := by
      nlinarith
    _ ≤ ∑ y : (F t)ˣ, (traceOneCharSum t (cubicValue a y.1)).re := by
      simpa [mul_assoc] using hsum

private lemma addChar_apply_eq_one_or_neg_one {t : ℕ}
    (ψ : AddChar (V t) ℂ) (v : V t) : ψ v = 1 ∨ ψ v = -1 := by
  apply sq_eq_one_iff.mp
  rw [pow_two, ← ψ.map_add_eq_mul]
  rw [show v + v = 0 by
    funext i
    exact CharTwo.add_self_eq_zero (v i)]
  exact ψ.map_zero_eq_one

private lemma sum_generators_eq_ofReal_eigenvalue (t : ℕ)
    (ψ : AddChar (V t) ℂ) :
    ∑ s ∈ generators t, ψ s = (eigenvalue t ψ : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, eigenvalue]
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro s hs
    rcases addChar_apply_eq_one_or_neg_one ψ s with h | h <;> simp [h]

local instance graphAdjDecidable' (t : ℕ) : DecidableRel (graph t).Adj :=
  fun _ _ ↦ Finset.decidableMem _ _

private lemma neighborFinset_graph (t : ℕ) (v : V t) :
    (graph t).neighborFinset v = (generators t).image fun s ↦ v + s := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, graph_adj, Finset.mem_image]
  constructor
  · intro h
    refine ⟨v + w, h, ?_⟩
    funext i
    simp only [Pi.add_apply]
    linear_combination CharTwo.add_self_eq_zero (v i)
  · rintro ⟨s, hs, rfl⟩
    simpa [show v + (v + s) = s by
      funext i
      simp only [Pi.add_apply]
      linear_combination CharTwo.add_self_eq_zero (v i)] using hs

lemma adjacencyOperator_chi_eigen (t : ℕ) (ψ : AddChar (V t) ℂ) :
    adjacencyOperator (graph t) ψ =
      (eigenvalue t ψ : ℂ) • (ψ : V t → ℂ) := by
  ext v
  rw [adjacencyOperator_apply, neighborFinset_graph]
  rw [Finset.sum_image]
  · simp_rw [ψ.map_add_eq_mul]
    rw [← Finset.mul_sum, sum_generators_eq_ofReal_eigenvalue]
    simp [Pi.smul_apply, mul_comm]
  · intro x hx y hy hxy
    exact add_left_cancel hxy

lemma card_V (t : ℕ) : Fintype.card (V t) = q t ^ 3 := by
  simp [V, Fintype.card_fun, card_F]

lemma degree_graph (t : ℕ) (v : V t) :
    (graph t).degree v = Fintype.card (traceOne t) * (q t - 1) := by
  rw [SimpleGraph.degree, neighborFinset_graph, Finset.card_image_of_injective,
    card_generators]
  intro x y h
  exact add_left_cancel h

def blockEdges (t : ℕ) : ℕ := q t ^ 4 * (q t - 1) / 4

lemma card_edgeFinset_graph (t : ℕ) :
    (graph t).edgeFinset.card = blockEdges t := by
  have hhand := (graph t).sum_degrees_eq_twice_card_edges
  simp_rw [degree_graph] at hhand
  rw [Finset.sum_const, Finset.card_univ, card_V] at hhand
  simp only [nsmul_eq_mul] at hhand
  change q t ^ 3 * (Fintype.card (traceOne t) * (q t - 1)) =
    2 * (graph t).edgeFinset.card at hhand
  have htrace := two_mul_card_traceOne t
  have hprod : q t ^ 4 * (q t - 1) = 4 * (graph t).edgeFinset.card := by
    calc
      q t ^ 4 * (q t - 1) =
          2 * (q t ^ 3 * (Fintype.card (traceOne t) * (q t - 1))) := by
            rw [← htrace]
            ring
      _ = 2 * (2 * (graph t).edgeFinset.card) := by rw [hhand]
      _ = 4 * (graph t).edgeFinset.card := by ring
  rw [blockEdges, hprod]
  omega

lemma four_mul_blockEdges (t : ℕ) :
    4 * blockEdges t = q t ^ 4 * (q t - 1) := by
  rw [← card_edgeFinset_graph]
  have hhand := (graph t).sum_degrees_eq_twice_card_edges
  simp_rw [degree_graph] at hhand
  rw [Finset.sum_const, Finset.card_univ, card_V] at hhand
  simp only [nsmul_eq_mul] at hhand
  change q t ^ 3 * (Fintype.card (traceOne t) * (q t - 1)) =
    2 * (graph t).edgeFinset.card at hhand
  have htrace := two_mul_card_traceOne t
  calc
    4 * (graph t).edgeFinset.card =
        2 * (q t ^ 3 * (Fintype.card (traceOne t) * (q t - 1))) := by
          omega
    _ = q t ^ 4 * (q t - 1) := by
          rw [← htrace]
          ring

lemma q_succ (t : ℕ) : q (t + 1) = 2 * q t := by
  simp [q, pow_succ]
  ring

lemma two_le_q (t : ℕ) : 2 ≤ q t := by
  have hp : 0 < 2 ^ t := pow_pos (by omega) _
  simp [q, pow_succ]
  omega

lemma blockEdges_pos (t : ℕ) : 0 < blockEdges t := by
  have hq := two_le_q t
  have hfour := four_mul_blockEdges t
  have hpow : 0 < q t ^ 4 := pow_pos (by omega) _
  have hsub : 0 < q t - 1 := by omega
  have : 0 < q t ^ 4 * (q t - 1) := Nat.mul_pos hpow hsub
  omega

lemma blockEdges_ratio_lower (t : ℕ) :
    32 * blockEdges t ≤ blockEdges (t + 1) := by
  have hq := two_le_q t
  have hs := q_succ t
  have h0 := four_mul_blockEdges t
  have h1 := four_mul_blockEdges (t + 1)
  rw [hs] at h1
  have hb : 32 * (q t - 1) ≤ 16 * (2 * q t - 1) := by omega
  have hmul := Nat.mul_le_mul_left (q t ^ 4) hb
  nlinarith

lemma blockEdges_ratio_upper (t : ℕ) :
    blockEdges (t + 1) ≤ 48 * blockEdges t := by
  have hq := two_le_q t
  have hs := q_succ t
  have h0 := four_mul_blockEdges t
  have h1 := four_mul_blockEdges (t + 1)
  rw [hs] at h1
  have hb : 16 * (2 * q t - 1) ≤ 48 * (q t - 1) := by omega
  have hmul := Nat.mul_le_mul_left (q t ^ 4) hb
  nlinarith

theorem cut_graph_le_raw (t : ℕ) (s : Set (V t)) :
    ((cutGraph (graph t) s).edgeSet.ncard : ℝ) ≤
      ((graph t).edgeFinset.card : ℝ) / 2 +
        (3 * q t : ℝ) * Fintype.card (V t) / 4 := by
  apply cut_le_of_character_eigenvalues (graph t) (eigenvalue t) (3 * q t)
  · exact adjacencyOperator_chi_eigen t
  · exact eigenvalue_lower t

theorem cut_graph_le_q (t : ℕ) (s : Set (V t)) :
    ((cutGraph (graph t) s).edgeSet.ncard : ℝ) ≤
      (blockEdges t : ℝ) / 2 + 3 * (q t : ℝ) ^ 4 / 4 := by
  have h := cut_graph_le_raw t s
  rw [card_edgeFinset_graph, card_V] at h
  norm_num [Nat.cast_pow] at h ⊢
  nlinarith


end

end Erdos581.UpperBlock
