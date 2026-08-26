import ErdosProblems.Erdos4.AnchoredFourierAverage
import ErdosProblems.Erdos4.ArithmeticFibers

/-!
# Arithmetic affine weights and their anchored values

The residue state records which affine form vanishes. For a nonzero
source residue, distinct shifts give distinct roots. At the center
`q - h_j p`, this state agrees with the anchored root state at `p / q`.
The actual weights include the positive-center cutoff and small-prime
coprimality condition explicitly.
-/

open scoped BigOperators

namespace Erdos4.AffineWeights

variable {k : ℕ}

theorem option_eq_of_some_iff {A : Type*} {a b : Option A}
    (h : ∀ i, a = some i ↔ b = some i) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some i =>
      have hx := (h i).mpr rfl
      cases hx
  | some i => exact ((h i).mp rfl).symm

noncomputable def state {F : Type*} [Field F] (h : Fin k → F) (n p : F) : Option (Fin k) :=
  RootStates.rootState Finset.univ (fun i => -h i) (n / p)

theorem state_eq_some_iff {F : Type*} [Field F] (h : Fin k → F)
    (hh : Function.Injective h) (n p : F) (hp : p ≠ 0) (i : Fin k) :
    state h n p = some i ↔ n + h i * p = 0 := by
  have hinj : Function.Injective (fun i : (Finset.univ : Finset (Fin k)) => -h i) := by
    intro a b hab
    exact Subtype.ext (hh (neg_injective hab))
  rw [state, RootStates.rootState_eq_some_iff _ _ hinj]
  simp only [Finset.mem_univ, true_and]
  rw [eq_div_iff hp]
  constructor <;> intro hx <;> linear_combination -hx

theorem state_at_anchor {F : Type*} [Field F] (h : Fin k → F)
    (hh : Function.Injective h) (j : Fin k) (p q : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (t : Fˣ) (ht : (t : F) = p / q) :
    state h (q - h j * p) p =
      RootStates.rootState (Finset.univ.erase j) (AnchorRoots.anchorRoot h j) t := by
  apply option_eq_of_some_iff
  intro i
  rw [state_eq_some_iff h hh _ _ hp,
    AnchorRoots.rootState_eq_some_iff h hh j i t, ht]
  exact AnchorRoots.anchored_form_zero_iff h j i p q hq

def shift (K : ℕ) (i : Fin k) : ℕ := i.val * primorial K

theorem shift_mod_injective (K ell : ℕ) (hell : ell.Prime) (hK : K < ell) (hk : k ≤ K) :
    Function.Injective (fun i : Fin k => (shift K i : ZMod ell)) := by
  let : Fact ell.Prime := ⟨hell⟩
  have hW : (primorial K : ZMod ell) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff (primorial K) ell).mp hz
    exact (not_le_of_gt hK) (hell.dvd_primorial_iff.mp hd)
  intro i j hij
  have hmul : (i.val : ZMod ell) * (primorial K : ZMod ell) =
      (j.val : ZMod ell) * (primorial K : ZMod ell) := by
    simpa only [shift, Nat.cast_mul] using hij
  have heq : (i.val : ZMod ell) = (j.val : ZMod ell) := mul_right_cancel₀ hW hmul
  apply Fin.ext
  exact ((ZMod.natCast_eq_natCast_iff i.val j.val ell).mp heq).eq_of_lt_of_lt
    (i.isLt.trans (hk.trans_lt hK)) (j.isLt.trans (hk.trans_lt hK))

theorem shift_le_bound (K : ℕ) (i : Fin k) : shift K i ≤ k * primorial K :=
  Nat.mul_le_mul_right _ i.isLt.le

theorem center_mem_Icc (K X Y p q : ℕ) (i : Fin k) (hpX : p ≤ X)
    (hq : k * primorial K * X < q) (hqY : q ≤ Y) :
    q - shift K i * p ∈ Finset.Icc 1 Y := by
  have hshift : shift K i * p < q :=
    (Nat.mul_le_mul (shift_le_bound K i) hpX).trans_lt hq
  exact Finset.mem_Icc.mpr ⟨by omega, (Nat.sub_le _ _).trans hqY⟩

theorem center_coprime (K p q : ℕ) (i : Fin k) (hshift : shift K i * p ≤ q)
    (hq : q.Coprime (primorial K)) : (q - shift K i * p).Coprime (primorial K) := by
  have heq : (q - shift K i * p) + primorial K * (i.val * p) = q := by
    have hh := Nat.sub_add_cancel hshift
    simpa only [shift, mul_assoc, mul_left_comm, mul_comm] using hh
  rw [← heq, Nat.coprime_add_mul_left_left] at hq
  exact hq

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def residueState (h : Fin k → ℕ) (n p : ℕ) (l : P) : Option (Fin k) :=
  state (fun i => (h i : ZMod (ell l))) (n : ZMod (ell l)) (p : ZMod (ell l))

noncomputable def amplitude (m : ℝ) (R : ℕ) (h : Fin k → ℕ) (p n : ℕ) : ℝ :=
  ∑ a, DivisorCoefficients.coefficient m R ell a *
    ∏ l, LocalOrthogonality.extendedBasis (ell l : ℝ) (a l) (residueState ell h n p l)

noncomputable def weight (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 1 Y ∧ n.Coprime W then amplitude ell m R h p n ^ 2 else 0

theorem weight_nonneg (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ) (p n : ℕ) :
    0 ≤ weight ell m R Y W h p n := by
  unfold weight
  split_ifs <;> positivity

theorem unitPoint_coe (n : ℕ) (hn : n.Coprime (ProductCharacterEncoding.modulus ell)) (l : P) :
    (AnchoredFourierAverage.unitPoint ell n hn l : ZMod (ell l)) = n := by
  unfold AnchoredFourierAverage.unitPoint
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast (ProductCharacterEncoding.local_dvd_modulus ell l)]

theorem residueState_anchor (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (j : Fin k) (p q : ℕ)
    (hp : p.Coprime (ProductCharacterEncoding.modulus ell))
    (hq : q.Coprime (ProductCharacterEncoding.modulus ell)) (hshift : h j * p ≤ q) (l : P) :
    residueState ell h (q - h j * p) p l =
      RootStates.rootState (Finset.univ.erase j)
        (AnchorRoots.anchorRoot (fun i => (h i : ZMod (ell l))) j)
        ((AnchoredFourierAverage.unitPoint ell p hp / AnchoredFourierAverage.unitPoint ell q hq) l) := by
  have hp0 : (p : ZMod (ell l)) ≠ 0 := by
    rw [← unitPoint_coe ell p hp l]
    exact Units.ne_zero _
  have hq0 : (q : ZMod (ell l)) ≠ 0 := by
    rw [← unitPoint_coe ell q hq l]
    exact Units.ne_zero _
  unfold residueState
  rw [Nat.cast_sub hshift, Nat.cast_mul]
  apply state_at_anchor _ (hh l) j _ _ hp0 hq0
  simp only [Pi.div_apply, Units.val_div_eq_div_val, unitPoint_coe]

theorem amplitude_sq_anchor (m : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (j : Fin k) (p q : ℕ)
    (hp : p.Coprime (ProductCharacterEncoding.modulus ell))
    (hq : q.Coprime (ProductCharacterEncoding.modulus ell)) (hshift : h j * p ≤ q) :
    amplitude ell m R h p (q - h j * p) ^ 2 =
      AnchoredFourierAverage.realSquare ell m R (fun l i => (h i : ZMod (ell l))) j
        (AnchoredFourierAverage.unitPoint ell p hp / AnchoredFourierAverage.unitPoint ell q hq) := by
  unfold amplitude AnchoredFourierAverage.realSquare
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  apply Finset.prod_congr rfl
  intro l _hl
  rw [residueState_anchor ell h hh j p q hp hq hshift l]

theorem weight_anchor (m : ℝ) (R Y W : ℕ) (h : Fin k → ℕ)
    (hh : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (j : Fin k) (p q : ℕ)
    (hp : p.Coprime (ProductCharacterEncoding.modulus ell))
    (hq : q.Coprime (ProductCharacterEncoding.modulus ell)) (hshift : h j * p ≤ q)
    (hcenter : q - h j * p ∈ Finset.Icc 1 Y) (hW : (q - h j * p).Coprime W) :
    weight ell m R Y W h p (q - h j * p) =
      AnchoredFourierAverage.realSquare ell m R (fun l i => (h i : ZMod (ell l))) j
        (AnchoredFourierAverage.unitPoint ell p hp / AnchoredFourierAverage.unitPoint ell q hq) := by
  rw [weight, if_pos ⟨hcenter, hW⟩]
  exact amplitude_sq_anchor ell m R h hh j p q hp hq hshift

end Erdos4.AffineWeights
