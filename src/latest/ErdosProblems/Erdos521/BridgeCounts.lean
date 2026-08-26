/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite bridge and survival counts for Erdős Problem 521.
Formal proof: Codex. The diagonal-coordinate bridge count and the elementary
Wallis estimate are adapted from the verified counting arguments in
ErdosProblems/Erdos1166/Erdos1166Core.lean, without its unrelated dependencies.
-/
import ErdosProblems.Erdos521.Pitman
import Mathlib

namespace Erdos521.Pitman

open scoped BigOperators

def allWords (n : ℕ) : Finset (List Direction) :=
  Finset.univ.image (List.ofFn : (Fin n → Direction) → List Direction)

theorem mem_allWords (n : ℕ) (w : List Direction) : w ∈ allWords n ↔ w.length = n := by
  simp only [allWords, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    simp
  · intro h
    subst n
    exact ⟨w.get, List.ofFn_get w⟩

theorem allWords_card (n : ℕ) : (allWords n).card = 4 ^ n := by
  rw [allWords, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

def returningWords (n : ℕ) : Finset (List Direction) :=
  (allWords n).filter fun w ↦ walk w = 0

noncomputable def survivingWords (n : ℕ) : Finset (List Direction) := by
  classical
  exact (allWords n).filter StaysNonnegative

/-- Every planar bridge has a distinct surviving image under reflection. -/
theorem returningWords_card_le_survivingWords (n : ℕ) :
    (returningWords n).card ≤ (survivingWords n).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun w ↦ (run w).output)
  · intro w hw
    have hw' := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨(mem_allWords _ _).mpr ?_, run_output_staysNonnegative w⟩
    rw [run_output_length]
    exact (mem_allWords _ _).mp hw'.1
  · intro u hu v hv hout
    apply run_injective_at_endpoint u v hout
    rw [run_position, run_position, (Finset.mem_filter.mp hu).2,
      (Finset.mem_filter.mp hv).2]

def finitePosition {n : ℕ} (w : Fin n → Direction) : Site := ∑ i, step (w i)

theorem walk_ofFn {n : ℕ} (w : Fin n → Direction) : walk (List.ofFn w) = finitePosition w := by
  simp [walk, finitePosition, List.map_ofFn, List.sum_ofFn]

def returningTuples (n : ℕ) : Finset (Fin n → Direction) :=
  Finset.univ.filter fun w ↦ finitePosition w = 0

theorem returningWords_card (n : ℕ) : (returningWords n).card = (returningTuples n).card := by
  have heq : returningWords n = (returningTuples n).image List.ofFn := by
    ext w
    simp only [returningWords, allWords, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and, returningTuples]
    constructor
    · rintro ⟨⟨f, rfl⟩, hf⟩
      exact ⟨f, (walk_ofFn f).symm.trans hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, rfl⟩, (walk_ofFn f).trans hf⟩
  rw [heq, Finset.card_image_of_injective _ List.ofFn_injective]

def directionBits (d : Direction) : Bool × Bool :=
  match d.val with
  | 0 => (false, false)
  | 1 => (true, true)
  | 2 => (false, true)
  | _ => (true, false)

def bitsDirection (b : Bool × Bool) : Direction :=
  match b with
  | (false, false) => 0
  | (true, true) => 1
  | (false, true) => 2
  | (true, false) => 3

def directionBitsEquiv : Direction ≃ Bool × Bool where
  toFun := directionBits
  invFun := bitsDirection
  left_inv d := by fin_cases d <;> rfl
  right_inv b := by rcases b with ⟨b₁, b₂⟩; cases b₁ <;> cases b₂ <;> rfl

def tupleBitsEquiv (n : ℕ) : (Fin n → Direction) ≃ ((Fin n → Bool) × (Fin n → Bool)) where
  toFun w := (fun i ↦ (directionBitsEquiv (w i)).1, fun i ↦ (directionBitsEquiv (w i)).2)
  invFun uv i := directionBitsEquiv.symm (uv.1 i, uv.2 i)
  left_inv w := by funext i; simp
  right_inv uv := by rcases uv with ⟨u, v⟩; apply Prod.ext <;> funext i <;> simp

def boolSign (b : Bool) : ℤ := if b then -1 else 1

theorem diagonal_step_one (d : Direction) :
    (step d).1 + (step d).2 = boolSign (directionBitsEquiv d).1 := by
  fin_cases d <;> rfl

theorem diagonal_step_two (d : Direction) :
    (step d).1 - (step d).2 = boolSign (directionBitsEquiv d).2 := by
  fin_cases d <;> rfl

def truePositions {I : Type*} [Fintype I] [DecidableEq I] (u : I → Bool) : Finset I :=
  Finset.univ.filter fun i ↦ u i = true

def boolFunEquivFinset (I : Type*) [Fintype I] [DecidableEq I] : (I → Bool) ≃ Finset I where
  toFun := truePositions
  invFun A i := decide (i ∈ A)
  left_inv u := by funext i; simp [truePositions]
  right_inv A := by ext i; simp [truePositions]

def BalancedBits (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :=
  {u : I → Bool // (truePositions u).card = j}

def balancedBitsEquivPowersetCard (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :
    BalancedBits I j ≃ Set.powersetCard I j :=
  (boolFunEquivFinset I).subtypeEquiv fun _ ↦ Iff.rfl

noncomputable instance (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :
    Fintype (BalancedBits I j) :=
  Fintype.ofEquiv (Set.powersetCard I j) (balancedBitsEquivPowersetCard I j).symm

theorem card_balancedBits (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :
    Fintype.card (BalancedBits I j) = (Fintype.card I).choose j := by
  rw [Fintype.card_congr (balancedBitsEquivPowersetCard I j)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]

theorem sum_boolSign {I : Type*} [Fintype I] [DecidableEq I] (u : I → Bool) :
    ∑ i, boolSign (u i) = (Fintype.card I : ℤ) - 2 * (truePositions u).card := by
  classical
  calc
    ∑ i, boolSign (u i) = ∑ i, ((1 : ℤ) - 2 * if u i = true then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      cases u i <;> rfl
    _ = (Fintype.card I : ℤ) - 2 * (truePositions u).card := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, ← Finset.mul_sum]
      congr 1
      simp [truePositions]

theorem diagonal_sum_one {n : ℕ} (w : Fin n → Direction) :
    ∑ i, boolSign (directionBitsEquiv (w i)).1 = (finitePosition w).1 + (finitePosition w).2 := by
  simp_rw [← diagonal_step_one, Finset.sum_add_distrib]
  simp [finitePosition, Prod.fst_sum, Prod.snd_sum]

theorem diagonal_sum_two {n : ℕ} (w : Fin n → Direction) :
    ∑ i, boolSign (directionBitsEquiv (w i)).2 = (finitePosition w).1 - (finitePosition w).2 := by
  simp_rw [← diagonal_step_two, Finset.sum_sub_distrib]
  simp [finitePosition, Prod.fst_sum, Prod.snd_sum]

theorem finitePosition_eq_zero_iff_balanced (j : ℕ) (w : Fin (2 * j) → Direction) :
    finitePosition w = 0 ↔
      (truePositions (tupleBitsEquiv (2 * j) w).1).card = j ∧
      (truePositions (tupleBitsEquiv (2 * j) w).2).card = j := by
  have h₁ := diagonal_sum_one w
  have h₂ := diagonal_sum_two w
  rw [sum_boolSign] at h₁ h₂
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h₁ h₂
  change finitePosition w = 0 ↔
    (truePositions (fun i ↦ (directionBitsEquiv (w i)).1)).card = j ∧
    (truePositions (fun i ↦ (directionBitsEquiv (w i)).2)).card = j
  constructor
  · intro h
    rw [h] at h₁ h₂
    change _ = (0 : ℤ) + 0 at h₁
    change _ = (0 : ℤ) - 0 at h₂
    constructor <;> omega
  · rintro ⟨h₃, h₄⟩
    rw [h₃] at h₁
    rw [h₄] at h₂
    apply Prod.ext <;> change _ = (0 : ℤ) <;> omega

def returningEquivBalanced (j : ℕ) :
    ↑(returningTuples (2 * j)) ≃ BalancedBits (Fin (2 * j)) j × BalancedBits (Fin (2 * j)) j where
  toFun w := by
    have hw := (finitePosition_eq_zero_iff_balanced j w.1).mp (Finset.mem_filter.mp w.2).2
    exact (⟨(tupleBitsEquiv (2 * j) w.1).1, hw.1⟩, ⟨(tupleBitsEquiv (2 * j) w.1).2, hw.2⟩)
  invFun uv := by
    refine ⟨(tupleBitsEquiv (2 * j)).symm (uv.1.1, uv.2.1), Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
    apply (finitePosition_eq_zero_iff_balanced j _).mpr
    simpa using And.intro uv.1.2 uv.2.2
  left_inv w := by apply Subtype.ext; simp
  right_inv uv := by rcases uv with ⟨u, v⟩; apply Prod.ext <;> apply Subtype.ext <;> simp

/-- Exact enumeration of planar bridges by two balanced sign sequences. -/
theorem returningWords_card_even (j : ℕ) :
    (returningWords (2 * j)).card = ((2 * j).choose j) ^ 2 := by
  rw [returningWords_card, ← Fintype.card_coe,
    Fintype.card_congr (returningEquivBalanced j), Fintype.card_prod,
    card_balancedBits]
  simp [pow_two]

/-- An elementary lower Wallis bound, proved from the central-binomial
recurrence. The index starts at one, as required by the harmonic lower bound. -/
theorem centralBinom_lower (j : ℕ) :
    16 ^ (j + 1) ≤ 4 * (j + 1) * Nat.centralBinom (j + 1) ^ 2 := by
  induction j with
  | zero => norm_num [Nat.centralBinom]
  | succ j ih =>
    have hrec := Nat.succ_mul_centralBinom_succ (j + 1)
    have hsq := congrArg (fun x : ℕ ↦ x ^ 2) hrec
    have hpoly : 4 * (j + 2) * (j + 1) ≤ (2 * j + 3) ^ 2 := by nlinarith
    have hmul : (j + 2) ^ 2 * 16 ^ (j + 2) ≤
        (j + 2) ^ 2 * (4 * (j + 2) * Nat.centralBinom (j + 2) ^ 2) := by
      calc
        (j + 2) ^ 2 * 16 ^ (j + 2) = 16 * (j + 2) ^ 2 * 16 ^ (j + 1) := by
          rw [pow_succ]
          ring
        _ ≤ 16 * (j + 2) ^ 2 * (4 * (j + 1) * Nat.centralBinom (j + 1) ^ 2) :=
          Nat.mul_le_mul_left _ ih
        _ = 16 * (j + 2) * (4 * (j + 2) * (j + 1)) * Nat.centralBinom (j + 1) ^ 2 := by ring
        _ ≤ 16 * (j + 2) * (2 * j + 3) ^ 2 * Nat.centralBinom (j + 1) ^ 2 := by gcongr
        _ = 4 * (j + 2) * ((j + 2) * Nat.centralBinom (j + 2)) ^ 2 := by rw [hsq]; ring
        _ = (j + 2) ^ 2 * (4 * (j + 2) * Nat.centralBinom (j + 2) ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- The lower bound needed for nonsummability, obtained without a ballot
formula: reflect bridges injectively into surviving quadrant paths. -/
theorem survivingWords_card_lower (j : ℕ) :
    16 ^ (j + 1) ≤ 4 * (j + 1) * (survivingWords (2 * (j + 1))).card := by
  calc
    16 ^ (j + 1) ≤ 4 * (j + 1) * Nat.centralBinom (j + 1) ^ 2 := centralBinom_lower j
    _ = 4 * (j + 1) * (returningWords (2 * (j + 1))).card := by
      rw [returningWords_card_even, Nat.centralBinom_eq_two_mul_choose]
    _ ≤ 4 * (j + 1) * (survivingWords (2 * (j + 1))).card :=
      Nat.mul_le_mul_left _ (returningWords_card_le_survivingWords _)

end Erdos521.Pitman
