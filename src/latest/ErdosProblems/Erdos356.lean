/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 356.
https://www.erdosproblems.com/forum/thread/356

Informal authors:
- Adrian Beker

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos356.md
-/
import Mathlib
import ErdosProblems.Erdos356.External.Erdos822.FiniteEnergy

/-!
# Erdős Problem 356

Adrian Beker proved that a strictly increasing sequence in `[n]` can have a
positive quadratic proportion of distinct consecutive sums.  We formalize his
explicit construction.  Its partial sums are

`p t = t ^ 2 + t / b`,

where eventually we take `b = Nat.sqrt N`.  A finite collision-energy estimate
then gives the result.  The accompanying mathematical proof is `tex/356.tex`.
-/

open scoped BigOperators Topology

namespace Erdos356

open Filter Finset

/-- The set of sums of nonempty consecutive pieces of a finite sequence. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  (((Finset.univ : Finset (Fin k)).product Finset.univ).filter fun uv ↦ uv.1 ≤ uv.2).image
    fun uv ↦ ∑ i ∈ Finset.Icc uv.1 uv.2, a i

/-- The exact formal statement of Erdős Problem 356. -/
def Problem356 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∃ k : ℕ, ∃ a : Fin k → ℕ,
      StrictMono a ∧
      (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
      c * (n : ℝ) ^ 2 ≤ ((consecutiveSums a).card : ℝ)

/-! ## Beker's explicit sequence -/

/-- The partial-sum ruler used in Beker's explicit construction. -/
def partialSum (b t : ℕ) : ℕ := t ^ 2 + t / b

/-- The `i`-th, zero-based, term is the next difference of the partial-sum ruler. -/
def bekerTerm (b i : ℕ) : ℕ := partialSum b (i + 1) - partialSum b i

lemma partialSum_mono (b : ℕ) : Monotone (partialSum b) := by
  intro x y hxy
  simp only [partialSum]
  exact Nat.add_le_add (Nat.pow_le_pow_left hxy 2) (Nat.div_le_div_right hxy)

lemma partialSum_le_succ (b i : ℕ) : partialSum b i ≤ partialSum b (i + 1) :=
  partialSum_mono b (Nat.le_succ i)

lemma bekerTerm_eq (b i : ℕ) :
    bekerTerm b i = 2 * i + 1 + ((i + 1) / b - i / b) := by
  rw [bekerTerm, partialSum, partialSum]
  have hsquare : (i + 1) ^ 2 = i ^ 2 + (2 * i + 1) := by ring
  have hdiv : i / b ≤ (i + 1) / b := Nat.div_le_div_right (Nat.le_succ i)
  rw [hsquare]
  omega

lemma div_succ_sub_div_le_one (b i : ℕ) : (i + 1) / b - i / b ≤ 1 := by
  by_cases hb : b = 0
  · simp [hb]
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hle : (i + 1) / b ≤ i / b + 1 := by
    calc
      (i + 1) / b ≤ (i + b) / b := Nat.div_le_div_right (by omega)
      _ = i / b + 1 := Nat.add_div_right i hbpos
  omega

lemma bekerTerm_bounds (b i : ℕ) : 2 * i + 1 ≤ bekerTerm b i ∧ bekerTerm b i ≤ 2 * i + 2 := by
  rw [bekerTerm_eq]
  constructor
  · omega
  · have := div_succ_sub_div_le_one b i
    omega

lemma bekerTerm_pos (b i : ℕ) : 0 < bekerTerm b i := by
  have := (bekerTerm_bounds b i).1
  omega

lemma bekerTerm_strictMono (b : ℕ) : StrictMono (bekerTerm b) := by
  intro i j hij
  have hsucc : i + 1 ≤ j := hij
  have hi := (bekerTerm_bounds b i).2
  have hj := (bekerTerm_bounds b j).1
  omega

/-- Beker's sequence of length `N`, with the parameter specialized to `sqrt N`. -/
def bekerSeq (N : ℕ) : Fin N → ℕ := fun i ↦ bekerTerm (Nat.sqrt N) i

lemma bekerSeq_strictMono (N : ℕ) : StrictMono (bekerSeq N) := by
  intro i j hij
  exact bekerTerm_strictMono (Nat.sqrt N) hij

lemma bekerSeq_bounds (N : ℕ) (i : Fin N) : 1 ≤ bekerSeq N i ∧ bekerSeq N i ≤ 2 * N := by
  constructor
  · exact bekerTerm_pos (Nat.sqrt N) i
  · have hi := (bekerTerm_bounds (Nat.sqrt N) i).2
    have hil := i.isLt
    simp only [bekerSeq]
    omega

/-! ## Telescoping and the rectangular family of intervals -/

lemma sum_bekerTerm_Ico (b u v : ℕ) (huv : u ≤ v) :
    ∑ i ∈ Finset.Ico u v, bekerTerm b i = partialSum b v - partialSum b u := by
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
      rw [Finset.sum_Ico_succ_top huv, ih, bekerTerm]
      have huv' : partialSum b u ≤ partialSum b v := partialSum_mono b huv
      have hv : partialSum b v ≤ partialSum b (v + 1) := partialSum_le_succ b v
      omega

/-- We use a square subfamily of all intervals.  Both the start and `length - 1`
range below `N / 2`, so every represented interval lies in a sequence of length `N`. -/
abbrev boxSide (N : ℕ) : ℕ := N / 2

abbrev BoxInterval (N : ℕ) := Fin (boxSide N) × Fin (boxSide N)

/-- The consecutive sum represented by `(start, length - 1)`. -/
def boxValue (N b : ℕ) (x : BoxInterval N) : ℕ :=
  partialSum b (x.1 + (x.2 + 1)) - partialSum b x.1

lemma box_end_le (N : ℕ) (x : BoxInterval N) : x.1.val + (x.2.val + 1) ≤ N := by
  have h₁ := x.1.isLt
  have h₂ := x.2.isLt
  simp only [boxSide] at h₁ h₂
  have hdiv := Nat.div_mul_le_self N 2
  omega

lemma boxValue_eq_sum_bekerSeq (N : ℕ) (x : BoxInterval N) :
    boxValue N (Nat.sqrt N) x =
      ∑ i ∈ Finset.Icc
        (⟨x.1.val, by have := box_end_le N x; omega⟩ : Fin N)
        (⟨x.1.val + x.2.val, by have := box_end_le N x; omega⟩ : Fin N),
        bekerSeq N i := by
  classical
  rw [boxValue, ← sum_bekerTerm_Ico (Nat.sqrt N) x.1.val
    (x.1.val + (x.2.val + 1)) (by omega)]
  apply Finset.sum_bij (fun i hi ↦
    (⟨i, by
      have hi' := Finset.mem_Ico.mp hi
      have hend := box_end_le N x
      omega⟩ : Fin N))
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext_iff.mp heq
  · intro j hj
    refine ⟨j.val, ?_, Fin.ext rfl⟩
    · simp only [Finset.mem_Icc, Fin.le_iff_val_le_val] at hj
      exact Finset.mem_Ico.mpr (by omega)
  · intro i hi
    rfl

lemma boxValue_mem_consecutiveSums (N : ℕ) (x : BoxInterval N) :
    boxValue N (Nat.sqrt N) x ∈ consecutiveSums (bekerSeq N) := by
  classical
  rw [consecutiveSums, Finset.mem_image]
  let u : Fin N := ⟨x.1.val, by
    have hx := x.1.isLt
    simp only [boxSide] at hx
    have hhalf := Nat.div_le_self N 2
    omega⟩
  let v : Fin N := ⟨x.1.val + x.2.val, by have := box_end_le N x; omega⟩
  refine ⟨(u, v), ?_, ?_⟩
  · simp [u, v]
  · simpa [u, v] using (boxValue_eq_sum_bekerSeq N x).symm

/-! ## The collision equation -/

/-- The carry when adding `u` and `k` before division by `b`. -/
def divCarry (b u k : ℕ) : ℕ := if b ≤ u % b + k % b then 1 else 0

lemma divCarry_le_one (b u k : ℕ) : divCarry b u k ≤ 1 := by
  unfold divCarry
  split <;> omega

lemma add_div_eq (b u k : ℕ) (hb : 0 < b) :
    (u + k) / b = u / b + k / b + divCarry b u k := by
  simpa [divCarry] using Nat.add_div (a := u) (b := k) hb

lemma intervalValue_eq (b u k : ℕ) (hb : 0 < b) :
    partialSum b (u + k) - partialSum b u =
      2 * k * u + k ^ 2 + k / b + divCarry b u k := by
  have hdiv := add_div_eq b u k hb
  simp only [partialSum]
  have hsquare : (u + k) ^ 2 = u ^ 2 + (2 * k * u + k ^ 2) := by ring
  rw [hsquare, hdiv]
  have hrearrange :
      u ^ 2 + (2 * k * u + k ^ 2) + (u / b + k / b + divCarry b u k) =
        (u ^ 2 + u / b) + (2 * k * u + k ^ 2 + k / b + divCarry b u k) := by
    ac_rfl
  rw [hrearrange]
  exact Nat.add_sub_cancel_left _ _

lemma boxValue_eq_formula {N b : ℕ} (hb : 0 < b) (x : BoxInterval N) :
    boxValue N b x =
      2 * (x.2.val + 1) * x.1.val + (x.2.val + 1) ^ 2 +
        (x.2.val + 1) / b + divCarry b x.1.val (x.2.val + 1) := by
  exact intervalValue_eq b x.1.val (x.2.val + 1) hb

/-- Equality of two interval sums gives Beker's linear Diophantine equation.
It is stated over the integers so that no truncated subtraction occurs. -/
lemma collision_linear_equation {N b : ℕ} (hb : 0 < b)
    (x y : BoxInterval N) (hxy : boxValue N b x = boxValue N b y) :
    (2 * (x.2.val + 1) * x.1.val : ℤ) -
        2 * (y.2.val + 1) * y.1.val =
      ((y.2.val + 1) ^ 2 : ℤ) - (x.2.val + 1) ^ 2 +
        (↑((y.2.val + 1) / b) : ℤ) - ↑((x.2.val + 1) / b) +
        (divCarry b y.1.val (y.2.val + 1) : ℤ) -
          divCarry b x.1.val (x.2.val + 1) := by
  rw [boxValue_eq_formula hb, boxValue_eq_formula hb] at hxy
  have hz := congrArg (fun n : ℕ ↦ (n : ℤ)) hxy
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hz
  linear_combination hz

lemma collision_delta_bounds {N b : ℕ} (x y : BoxInterval N) :
    -(1 : ℤ) ≤
        (divCarry b y.1.val (y.2.val + 1) : ℤ) -
          divCarry b x.1.val (x.2.val + 1) ∧
      (divCarry b y.1.val (y.2.val + 1) : ℤ) -
          divCarry b x.1.val (x.2.val + 1) ≤ 1 := by
  have hx := divCarry_le_one b x.1.val (x.2.val + 1)
  have hy := divCarry_le_one b y.1.val (y.2.val + 1)
  omega

/-- If a nonnegative integer is very close to a multiple of `b`, then its
canonical remainder is close to one of the two ends of `[0,b)`. -/
lemma mod_near_end {b q d : ℕ} (hb : 0 < b) (hq : 0 < q) (z : ℤ)
    (hz : |(q : ℤ) * d - (b : ℤ) * q * z| < (2 : ℤ) * b) :
    q * (d % b) < 2 * b ∨ q * (b - d % b) < 2 * b := by
  by_contra h
  push Not at h
  rcases h with ⟨hleft, hright⟩
  let r := d % b
  let w : ℤ := (d / b : ℕ) - z
  have hrlt : r < b := Nat.mod_lt d hb
  have hd : (d : ℤ) = (b : ℤ) * (↑(d / b) : ℤ) + r := by
    exact_mod_cast (Nat.div_add_mod d b).symm
  have hrearrange :
      (q : ℤ) * d - (b : ℤ) * q * z =
        (q : ℤ) * ((b : ℤ) * w + r) := by
    rw [hd]
    simp only [w]
    ring
  rw [hrearrange] at hz
  have hqz : (0 : ℤ) ≤ q := by positivity
  have hbz : (0 : ℤ) ≤ b := by positivity
  have hrz : (0 : ℤ) ≤ r := by positivity
  by_cases hw : 0 ≤ w
  · have hinner : (r : ℤ) ≤ (b : ℤ) * w + r := by
      have : (0 : ℤ) ≤ (b : ℤ) * w := mul_nonneg hbz hw
      omega
    have hprod : (q : ℤ) * r ≤ (q : ℤ) * ((b : ℤ) * w + r) :=
      mul_le_mul_of_nonneg_left hinner hqz
    have hprod0 : (0 : ℤ) ≤ (q : ℤ) * ((b : ℤ) * w + r) :=
      mul_nonneg hqz (hrz.trans hinner)
    rw [abs_of_nonneg hprod0] at hz
    exact (not_lt_of_ge (by exact_mod_cast hleft)) (hprod.trans_lt hz)
  · have hw' : w ≤ -(1 : ℤ) := by omega
    have hbw : (b : ℤ) * w ≤ -(b : ℤ) := by
      have := mul_le_mul_of_nonneg_left hw' hbz
      simpa using this
    have hinner : (b : ℤ) * w + r ≤ -((b : ℤ) - r) := by omega
    have hprod : (q : ℤ) * ((b : ℤ) * w + r) ≤ -((q : ℤ) * ((b : ℤ) - r)) := by
      have := mul_le_mul_of_nonneg_left hinner hqz
      nlinarith
    have hprod0 : (q : ℤ) * ((b : ℤ) * w + r) ≤ 0 := by
      have hbr : (0 : ℤ) ≤ (b : ℤ) - r := by omega
      nlinarith [mul_nonneg hqz hbr]
    rw [abs_of_nonpos hprod0] at hz
    have hrightz : (2 : ℤ) * b ≤ (q : ℤ) * ((b : ℤ) - r) := by
      rw [← Nat.cast_sub (Nat.le_of_lt hrlt)]
      exact_mod_cast hright
    omega

/-- A collision whose first interval is no longer than the second forces the
difference of the reduced lengths into the small end-remainder set. -/
lemma collision_reducedLength_mod_near {N b : ℕ} (hb : 0 < b)
    (x y : BoxInterval N) (hxy : boxValue N b x = boxValue N b y)
    (hkl : x.2.val + 1 ≤ y.2.val + 1) :
    let K := x.2.val + 1
    let L := y.2.val + 1
    let q := Nat.gcd K L
    let d := L / q - K / q
    q * (d % b) < 2 * b ∨ q * (b - d % b) < 2 * b := by
  dsimp only
  let K := x.2.val + 1
  let L := y.2.val + 1
  let q := Nat.gcd K L
  let kp := K / q
  let lp := L / q
  let d := lp - kp
  have hKpos : 0 < K := by simp [K]
  have hLpos : 0 < L := by simp [L]
  have hqpos : 0 < q := by
    exact Nat.gcd_pos_of_pos_left L hKpos
  have hqK : q ∣ K := by exact Nat.gcd_dvd_left K L
  have hqL : q ∣ L := by exact Nat.gcd_dvd_right K L
  have hKfac : q * kp = K := by exact Nat.mul_div_cancel' hqK
  have hLfac : q * lp = L := by exact Nat.mul_div_cancel' hqL
  have hkple : kp ≤ lp := by
    exact Nat.div_le_div_right hkl
  have heq := collision_linear_equation hb x y hxy
  change (2 * K * x.1.val : ℤ) - 2 * L * y.1.val =
      (L ^ 2 : ℤ) - K ^ 2 + (↑(L / b) : ℤ) - ↑(K / b) +
        (divCarry b y.1.val L : ℤ) - divCarry b x.1.val K at heq
  have hKfacZ : (q : ℤ) * kp = K := by exact_mod_cast hKfac
  have hLfacZ : (q : ℤ) * lp = L := by exact_mod_cast hLfac
  have hleftDvd : (q : ℤ) ∣
      (2 * K * x.1.val : ℤ) - 2 * L * y.1.val := by
    refine ⟨2 * (kp : ℤ) * x.1.val - 2 * (lp : ℤ) * y.1.val, ?_⟩
    rw [← hKfacZ, ← hLfacZ]
    ring
  have hsquareDvd : (q : ℤ) ∣ (L ^ 2 : ℤ) - K ^ 2 := by
    refine ⟨(q : ℤ) * ((lp : ℤ) ^ 2 - (kp : ℤ) ^ 2), ?_⟩
    rw [← hKfacZ, ← hLfacZ]
    ring
  have hDdvd : (q : ℤ) ∣
      (↑(L / b) : ℤ) - ↑(K / b) +
        (divCarry b y.1.val L : ℤ) - divCarry b x.1.val K := by
    have heqD :
        (↑(L / b) : ℤ) - ↑(K / b) +
            (divCarry b y.1.val L : ℤ) - divCarry b x.1.val K =
          ((2 * K * x.1.val : ℤ) - 2 * L * y.1.val) -
            ((L ^ 2 : ℤ) - K ^ 2) := by
      linear_combination -heq
    rw [heqD]
    exact dvd_sub hleftDvd hsquareDvd
  rcases hDdvd with ⟨z, hz⟩
  have hfloorK : (b : ℤ) * (↑(K / b) : ℤ) = (K : ℤ) - K % b := by
    have h := Nat.div_add_mod' K b
    have hz : (↑(K / b) : ℤ) * b + (K % b : ℤ) = K := by
      exact_mod_cast h
    linear_combination hz
  have hfloorL : (b : ℤ) * (↑(L / b) : ℤ) = (L : ℤ) - L % b := by
    have h := Nat.div_add_mod' L b
    have hz : (↑(L / b) : ℤ) * b + (L % b : ℤ) = L := by
      exact_mod_cast h
    linear_combination hz
  have hdcast : (d : ℤ) = (lp : ℤ) - kp := by
    simp only [d, Nat.cast_sub hkple]
  have hnearEq :
      (q : ℤ) * d - (b : ℤ) * q * z =
        (L % b : ℤ) - K % b -
          (b : ℤ) * ((divCarry b y.1.val L : ℤ) - divCarry b x.1.val K) := by
    rw [hdcast]
    linear_combination (b : ℤ) * hz - hfloorL + hfloorK + hLfacZ - hKfacZ
  have hrK : K % b < b := Nat.mod_lt K hb
  have hrL : L % b < b := Nat.mod_lt L hb
  have hcx := divCarry_le_one b x.1.val K
  have hcy := divCarry_le_one b y.1.val L
  have habs :
      |(L % b : ℤ) - K % b -
          (b : ℤ) * ((divCarry b y.1.val L : ℤ) - divCarry b x.1.val K)| <
        (2 : ℤ) * b := by
    have hcx_cases : divCarry b x.1.val K = 0 ∨ divCarry b x.1.val K = 1 := by omega
    have hcy_cases : divCarry b y.1.val L = 0 ∨ divCarry b y.1.val L = 1 := by omega
    rcases hcx_cases with hcx0 | hcx1
    · rcases hcy_cases with hcy0 | hcy1
      · simp [hcx0, hcy0]
        rw [abs_lt]
        constructor <;> omega
      · simp [hcx0, hcy1]
        rw [abs_lt]
        constructor <;> omega
    · rcases hcy_cases with hcy0 | hcy1
      · simp [hcx1, hcy0]
        rw [abs_lt]
        constructor <;> omega
      · simp [hcx1, hcy1]
        rw [abs_lt]
        constructor <;> omega
  apply mod_near_end hb hqpos z
  rwa [hnearEq]

/-! ## A finite code space for collisions -/

structure CollisionCode where
  swapped : Bool
  q : ℕ
  long : ℕ
  block : ℕ
  upperEnd : Bool
  offset : ℕ
  carry₁ : ℕ
  carry₂ : ℕ
  startBlock : ℕ
  deriving DecidableEq

/-- A dependent raw code.  The dependencies are used only to make its finite
enumerating set have the sharp product-of-ranges cardinality. -/
abbrev RawCollisionCode :=
  Σ _swapped : Bool, Σ _q : ℕ, Σ _long : ℕ, Σ _block : ℕ, Σ _upperEnd : Bool,
    Σ _offset : ℕ, Σ _carry₁ : Fin 2, Σ _carry₂ : Fin 2, ℕ

def rawCollisionCodes (N b : ℕ) : Finset RawCollisionCode :=
  Finset.univ.sigma fun _swapped : Bool ↦
    (Finset.Icc 1 N).sigma fun q ↦
      (Finset.Icc 1 (N / q)).sigma fun long ↦
        (Finset.range (long / b + 1)).sigma fun _block ↦
          Finset.univ.sigma fun _upperEnd : Bool ↦
            (Finset.range (2 * b / q + 1)).sigma fun _offset ↦
              Finset.univ.sigma fun _carry₁ : Fin 2 ↦
                Finset.univ.sigma fun _carry₂ : Fin 2 ↦
                  Finset.range (N / long + 1)

def rawCollisionCodeToCode : RawCollisionCode → CollisionCode
  | ⟨sw, q, long, block, upper, offset, c₁, c₂, start⟩ =>
      ⟨sw, q, long, block, upper, offset, c₁, c₂, start⟩

def collisionCodeSpace (N b : ℕ) : Finset CollisionCode :=
  (rawCollisionCodes N b).image rawCollisionCodeToCode

lemma collisionCodeSpace_card_le (N b : ℕ) :
    (collisionCodeSpace N b).card ≤
      16 * ∑ q ∈ Finset.Icc 1 N, ∑ long ∈ Finset.Icc 1 (N / q),
        (long / b + 1) * (2 * b / q + 1) * (N / long + 1) := by
  calc
    (collisionCodeSpace N b).card ≤ (rawCollisionCodes N b).card :=
      Finset.card_image_le
    _ = 16 * ∑ q ∈ Finset.Icc 1 N, ∑ long ∈ Finset.Icc 1 (N / q),
        (long / b + 1) * (2 * b / q + 1) * (N / long + 1) := by
      simp [rawCollisionCodes, Finset.card_sigma, Finset.mul_sum]
      ring_nf

/-- Code an already oriented collision, with the shorter length first. -/
def orientedCollisionCode (b : ℕ) (swapped : Bool) {N : ℕ}
    (x y : BoxInterval N) : CollisionCode :=
  let K := x.2.val + 1
  let L := y.2.val + 1
  let q := Nat.gcd K L
  let long := L / q
  let d := long - K / q
  let r := d % b
  let nearLower := q * r < 2 * b
  { swapped := swapped
    q := q
    long := long
    block := d / b
    upperEnd := !nearLower
    offset := if nearLower then r else b - r
    carry₁ := divCarry b x.1.val K
    carry₂ := divCarry b y.1.val L
    startBlock := x.1.val / long }

lemma orientedCollisionCode_mem {N b : ℕ} (hb : 0 < b) (swapped : Bool)
    (x y : BoxInterval N) (hxy : boxValue N b x = boxValue N b y)
    (hkl : x.2.val + 1 ≤ y.2.val + 1) :
    orientedCollisionCode b swapped x y ∈ collisionCodeSpace N b := by
  classical
  let K := x.2.val + 1
  let L := y.2.val + 1
  let q := Nat.gcd K L
  let long := L / q
  let d := long - K / q
  let r := d % b
  let nearLower := q * r < 2 * b
  let offset := if nearLower then r else b - r
  have hKpos : 0 < K := by simp [K]
  have hLpos : 0 < L := by simp [L]
  have hqpos : 0 < q := Nat.gcd_pos_of_pos_left L hKpos
  have hqK : q ∣ K := Nat.gcd_dvd_left K L
  have hqL : q ∣ L := Nat.gcd_dvd_right K L
  have hKfac : q * (K / q) = K := Nat.mul_div_cancel' hqK
  have hLfac : q * long = L := Nat.mul_div_cancel' hqL
  have hlongpos : 0 < long := by
    by_contra h
    have : long = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hLfac
  have hMleN : boxSide N ≤ N := Nat.div_le_self N 2
  have hKleN : K ≤ N := by
    have hx := x.2.isLt
    simp only [boxSide] at hx
    omega
  have hLleN : L ≤ N := by
    have hy := y.2.isLt
    simp only [boxSide] at hy
    omega
  have hqleN : q ≤ N := (Nat.gcd_le_left L hKpos).trans hKleN
  have hlongle : long ≤ N / q := by
    exact Nat.div_le_div_right hLleN
  have hkple : K / q ≤ long := Nat.div_le_div_right hkl
  have hdle : d ≤ long := Nat.sub_le _ _
  have hblock : d / b < long / b + 1 := by
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hdle)
  have hnear := collision_reducedLength_mod_near hb x y hxy hkl
  change q * (d % b) < 2 * b ∨ q * (b - d % b) < 2 * b at hnear
  have hoffset : offset < 2 * b / q + 1 := by
    have hle_of_mul_lt {t : ℕ} (ht : q * t < 2 * b) : t ≤ 2 * b / q := by
      rw [Nat.le_div_iff_mul_le hqpos]
      simpa [Nat.mul_comm] using Nat.le_of_lt ht
    by_cases hlow : nearLower
    · simp only [offset, nearLower, hlow, ↓reduceIte]
      exact Nat.lt_succ_of_le (hle_of_mul_lt hlow)
    · simp only [nearLower] at hlow
      have hupp : q * (b - r) < 2 * b := hnear.resolve_left hlow
      simp only [offset, nearLower, hlow, ↓reduceIte]
      exact Nat.lt_succ_of_le (hle_of_mul_lt hupp)
  have hcarry₁ : divCarry b x.1.val K < 2 := by
    have := divCarry_le_one b x.1.val K
    omega
  have hcarry₂ : divCarry b y.1.val L < 2 := by
    have := divCarry_le_one b y.1.val L
    omega
  have hxstart : x.1.val ≤ N := by
    have hx := x.1.isLt
    simp only [boxSide] at hx
    omega
  have hstart : x.1.val / long < N / long + 1 := by
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hxstart)
  rw [collisionCodeSpace, Finset.mem_image]
  let raw : RawCollisionCode :=
    ⟨swapped, q, long, d / b, !nearLower, offset,
      ⟨divCarry b x.1.val K, hcarry₁⟩,
      ⟨divCarry b y.1.val L, hcarry₂⟩, x.1.val / long⟩
  refine ⟨raw, ?_, ?_⟩
  · simp only [rawCollisionCodes, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_Icc, Finset.mem_range, raw]
    exact ⟨⟨hqpos, hqleN⟩, ⟨hlongpos, hlongle⟩, hblock, hoffset, hstart⟩
  · simp [raw, rawCollisionCodeToCode, orientedCollisionCode, K, L, q, long, d, r,
      nearLower, offset]

lemma orientedCollisionCode_injective {N b : ℕ} (hb : 0 < b) (swapped : Bool)
    {x y x' y' : BoxInterval N}
    (hxy : boxValue N b x = boxValue N b y)
    (hxy' : boxValue N b x' = boxValue N b y')
    (hkl : x.2.val + 1 ≤ y.2.val + 1)
    (hkl' : x'.2.val + 1 ≤ y'.2.val + 1)
    (hcode : orientedCollisionCode b swapped x y =
      orientedCollisionCode b swapped x' y') :
    x = x' ∧ y = y' := by
  let K := x.2.val + 1
  let L := y.2.val + 1
  let K' := x'.2.val + 1
  let L' := y'.2.val + 1
  let q := Nat.gcd K L
  let q' := Nat.gcd K' L'
  let kp := K / q
  let lp := L / q
  let kp' := K' / q'
  let lp' := L' / q'
  let d := lp - kp
  let d' := lp' - kp'
  let r := d % b
  let r' := d' % b
  have hq : q = q' := congrArg CollisionCode.q hcode
  have hlp : lp = lp' := congrArg CollisionCode.long hcode
  have hblock : d / b = d' / b := congrArg CollisionCode.block hcode
  have hupper : (!(q * r < 2 * b)) = (!(q' * r' < 2 * b)) :=
    congrArg CollisionCode.upperEnd hcode
  have hoffset :
      (if q * r < 2 * b then r else b - r) =
        (if q' * r' < 2 * b then r' else b - r') :=
    congrArg CollisionCode.offset hcode
  have hcarry₁ : divCarry b x.1.val K = divCarry b x'.1.val K' :=
    congrArg CollisionCode.carry₁ hcode
  have hcarry₂ : divCarry b y.1.val L = divCarry b y'.1.val L' :=
    congrArg CollisionCode.carry₂ hcode
  have hstart : x.1.val / lp = x'.1.val / lp' :=
    congrArg CollisionCode.startBlock hcode
  have hrlt : r < b := Nat.mod_lt d hb
  have hrlt' : r' < b := Nat.mod_lt d' hb
  have hr : r = r' := by
    rw [hq] at hupper hoffset
    by_cases hlow : q' * r < 2 * b
    · by_cases hlow' : q' * r' < 2 * b
      · simpa [hlow, hlow'] using hoffset
      · simp [hlow, hlow'] at hupper
    · by_cases hlow' : q' * r' < 2 * b
      · simp [hlow, hlow'] at hupper
      · simp [hlow, hlow'] at hoffset
        omega
  have hd : d = d' := by
    have hddecomp := Nat.div_add_mod' d b
    have hddecomp' := Nat.div_add_mod' d' b
    have hrem : d % b = d' % b := by simpa only [r, r'] using hr
    calc
      d = d / b * b + d % b := hddecomp.symm
      _ = d' / b * b + d' % b := by rw [hblock, hrem]
      _ = d' := hddecomp'
  have hKpos : 0 < K := by simp [K]
  have hKpos' : 0 < K' := by simp [K']
  have hqpos : 0 < q := Nat.gcd_pos_of_pos_left L hKpos
  have hqpos' : 0 < q' := Nat.gcd_pos_of_pos_left L' hKpos'
  have hkple : kp ≤ lp := Nat.div_le_div_right hkl
  have hkple' : kp' ≤ lp' := Nat.div_le_div_right hkl'
  have hkp : kp = kp' := by
    dsimp only [d, d'] at hd
    omega
  have hKfac : q * kp = K := Nat.mul_div_cancel' (Nat.gcd_dvd_left K L)
  have hLfac : q * lp = L := Nat.mul_div_cancel' (Nat.gcd_dvd_right K L)
  have hKfac' : q' * kp' = K' := Nat.mul_div_cancel' (Nat.gcd_dvd_left K' L')
  have hLfac' : q' * lp' = L' := Nat.mul_div_cancel' (Nat.gcd_dvd_right K' L')
  have hK : K = K' := by
    calc
      K = q * kp := hKfac.symm
      _ = q' * kp' := by rw [hq, hkp]
      _ = K' := hKfac'
  have hL : L = L' := by
    calc
      L = q * lp := hLfac.symm
      _ = q' * lp' := by rw [hq, hlp]
      _ = L' := hLfac'
  have hxlen : x.2 = x'.2 := by
    apply Fin.ext
    dsimp only [K, K'] at hK
    omega
  have hylen : y.2 = y'.2 := by
    apply Fin.ext
    dsimp only [L, L'] at hL
    omega
  have heq := collision_linear_equation hb x y hxy
  have heq' := collision_linear_equation hb x' y' hxy'
  change (2 * K * x.1.val : ℤ) - 2 * L * y.1.val =
      (L ^ 2 : ℤ) - K ^ 2 + (↑(L / b) : ℤ) - ↑(K / b) +
        (divCarry b y.1.val L : ℤ) - divCarry b x.1.val K at heq
  change (2 * K' * x'.1.val : ℤ) - 2 * L' * y'.1.val =
      (L' ^ 2 : ℤ) - K' ^ 2 + (↑(L' / b) : ℤ) - ↑(K' / b) +
        (divCarry b y'.1.val L' : ℤ) - divCarry b x'.1.val K' at heq'
  simp only [← hK, ← hL] at hcarry₁ hcarry₂ heq'
  rw [← hcarry₁, ← hcarry₂] at heq'
  have hbase :
      (K : ℤ) * x.1.val - (L : ℤ) * y.1.val =
        (K : ℤ) * x'.1.val - (L : ℤ) * y'.1.val := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
    linear_combination heq - heq'
  have hKfacZ : (q : ℤ) * kp = K := by exact_mod_cast hKfac
  have hLfacZ : (q : ℤ) * lp = L := by exact_mod_cast hLfac
  rw [← hKfacZ, ← hLfacZ] at hbase
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hred :
      (kp : ℤ) * x.1.val - (lp : ℤ) * y.1.val =
        (kp : ℤ) * x'.1.val - (lp : ℤ) * y'.1.val := by
    apply mul_left_cancel₀ hqz
    linear_combination hbase
  have hcop : kp.Coprime lp := Nat.coprime_div_gcd_div_gcd hqpos
  have hdvd : (lp : ℤ) ∣ (x.1.val : ℤ) - x'.1.val := by
    have hmul : (lp : ℤ) ∣ (kp : ℤ) * ((x.1.val : ℤ) - x'.1.val) := by
      refine ⟨(y.1.val : ℤ) - y'.1.val, ?_⟩
      linear_combination hred
    exact hcop.symm.isCoprime.dvd_of_dvd_mul_left hmul
  have hmod : Nat.ModEq lp x'.1.val x.1.val := Nat.modEq_iff_dvd.mpr hdvd
  change x'.1.val % lp = x.1.val % lp at hmod
  rw [← hlp] at hstart
  have hxstart : x.1.val = x'.1.val := by
    have hxdecomp := Nat.mod_add_div x.1.val lp
    have hxdecomp' := Nat.mod_add_div x'.1.val lp
    calc
      x.1.val = x.1.val % lp + lp * (x.1.val / lp) := hxdecomp.symm
      _ = x'.1.val % lp + lp * (x'.1.val / lp) := by rw [← hmod, hstart]
      _ = x'.1.val := hxdecomp'
  have hystart : y.1.val = y'.1.val := by
    rw [hxstart] at hred
    have hlpz : (lp : ℤ) ≠ 0 := by
      have hlppos : 0 < lp := by
        by_contra h
        have : lp = 0 := Nat.eq_zero_of_not_pos h
        simp [this] at hLfac
      exact_mod_cast Nat.ne_of_gt hlppos
    have hmul : (lp : ℤ) * y.1.val = (lp : ℤ) * y'.1.val := by
      linarith [hred]
    have hyz : (y.1.val : ℤ) = y'.1.val := mul_left_cancel₀ hlpz hmul
    exact_mod_cast hyz
  constructor <;> apply Prod.ext
  · exact Fin.ext hxstart
  · exact hxlen
  · exact Fin.ext hystart
  · exact hylen

/-- Ordered pairs of box intervals having the same sum. -/
def boxCollisions (N b : ℕ) : Finset (BoxInterval N × BoxInterval N) :=
  Erdos822.collisionPairs Finset.univ (boxValue N b)

/-- Orient a collision by length and then apply `orientedCollisionCode`. -/
def collisionCode (b : ℕ) {N : ℕ} (z : BoxInterval N × BoxInterval N) : CollisionCode :=
  if z.1.2.val + 1 ≤ z.2.2.val + 1 then
    orientedCollisionCode b false z.1 z.2
  else
    orientedCollisionCode b true z.2 z.1

lemma collisionCode_mem {N b : ℕ} (hb : 0 < b) {z : BoxInterval N × BoxInterval N}
    (hz : z ∈ boxCollisions N b) : collisionCode b z ∈ collisionCodeSpace N b := by
  rw [boxCollisions, Erdos822.collisionPairs, Finset.mem_filter, Finset.mem_product] at hz
  by_cases hle : z.1.2.val + 1 ≤ z.2.2.val + 1
  · rw [collisionCode, if_pos hle]
    exact orientedCollisionCode_mem hb false z.1 z.2 hz.2 hle
  · have hrev : z.2.2.val + 1 ≤ z.1.2.val + 1 := by omega
    rw [collisionCode, if_neg hle]
    exact orientedCollisionCode_mem hb true z.2 z.1 hz.2.symm hrev

lemma collisionCode_injOn {N b : ℕ} (hb : 0 < b) :
    Set.InjOn
      (collisionCode b : (BoxInterval N × BoxInterval N) → CollisionCode)
      (↑(boxCollisions N b) : Set (BoxInterval N × BoxInterval N)) := by
  intro z hz w hw hcode
  have hz' : z ∈ boxCollisions N b := hz
  have hw' : w ∈ boxCollisions N b := hw
  rw [boxCollisions, Erdos822.collisionPairs, Finset.mem_filter, Finset.mem_product] at hz' hw'
  by_cases hzle : z.1.2.val + 1 ≤ z.2.2.val + 1
  · by_cases hwle : w.1.2.val + 1 ≤ w.2.2.val + 1
    · simp only [collisionCode, if_pos hzle, if_pos hwle] at hcode
      rcases orientedCollisionCode_injective hb false hz'.2 hw'.2 hzle hwle hcode with ⟨h₁, h₂⟩
      exact Prod.ext h₁ h₂
    · simp only [collisionCode, if_pos hzle, if_neg hwle] at hcode
      have := congrArg CollisionCode.swapped hcode
      simp [orientedCollisionCode] at this
  · have hzrev : z.2.2.val + 1 ≤ z.1.2.val + 1 := by omega
    by_cases hwle : w.1.2.val + 1 ≤ w.2.2.val + 1
    · simp only [collisionCode, if_neg hzle, if_pos hwle] at hcode
      have := congrArg CollisionCode.swapped hcode
      simp [orientedCollisionCode] at this
    · have hwrev : w.2.2.val + 1 ≤ w.1.2.val + 1 := by omega
      simp only [collisionCode, if_neg hzle, if_neg hwle] at hcode
      rcases orientedCollisionCode_injective hb true hz'.2.symm hw'.2.symm hzrev hwrev hcode with
        ⟨h₂, h₁⟩
      exact Prod.ext h₁ h₂

lemma boxCollisions_card_le_codeSpace {N b : ℕ} (hb : 0 < b) :
    (boxCollisions N b).card ≤ (collisionCodeSpace N b).card := by
  exact Finset.card_le_card_of_injOn (collisionCode b)
    (fun _ hz ↦ collisionCode_mem hb hz) (collisionCode_injOn hb)

/-- The elementary parameter sum which bounds the collision-code space. -/
def parameterSum (N b : ℕ) : ℕ :=
  ∑ q ∈ Finset.Icc 1 N, ∑ long ∈ Finset.Icc 1 (N / q),
    (long / b + 1) * (2 * b / q + 1) * (N / long + 1)

lemma boxCollisions_card_le_parameterSum {N b : ℕ} (hb : 0 < b) :
    (boxCollisions N b).card ≤ 16 * parameterSum N b := by
  simpa only [parameterSum] using
    (boxCollisions_card_le_codeSpace hb).trans (collisionCodeSpace_card_le N b)

/-! ## Estimating the collision-code space -/

/-- The positive lattice points below the hyperbola `q * l = N`. -/
def divisorPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter fun p ↦ p.1 * p.2 ≤ N

lemma Icc_div_eq_filter {N q : ℕ} (hq : 0 < q) :
    Finset.Icc 1 (N / q) =
      (Finset.Icc 1 N).filter (fun long ↦ q * long ≤ N) := by
  ext long
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro ⟨hlong, hlongNq⟩
    refine ⟨⟨hlong, ?_⟩, ?_⟩
    · exact hlongNq.trans (Nat.div_le_self N q)
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).1 hlongNq
  · rintro ⟨⟨hlong, hlongN⟩, hmul⟩
    exact ⟨hlong, (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hmul)⟩

lemma sum_divisorPairs_eq_nested {N : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ divisorPairs N, f p.1 p.2 =
      ∑ q ∈ Finset.Icc 1 N, ∑ long ∈ Finset.Icc 1 (N / q), f q long := by
  calc
    (∑ p ∈ divisorPairs N, f p.1 p.2) =
        ∑ q ∈ Finset.Icc 1 N,
          ∑ long ∈ (Finset.Icc 1 N).filter (fun long ↦ q * long ≤ N),
            f q long := by
              rw [divisorPairs, Finset.sum_filter]
              simp_rw [Finset.sum_filter]
              exact Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
                (fun p ↦ if p.1 * p.2 ≤ N then f p.1 p.2 else 0)
    _ = ∑ q ∈ Finset.Icc 1 N, ∑ long ∈ Finset.Icc 1 (N / q), f q long := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Icc_div_eq_filter (by have := (Finset.mem_Icc.mp hq).1; omega)]

/-- The real harmonic sum over the positive integers at most `N`. -/
noncomputable def harmonicReal (N : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 N, (q : ℝ)⁻¹

lemma harmonicReal_nonneg (N : ℕ) : 0 ≤ harmonicReal N := by
  exact Finset.sum_nonneg fun q _ ↦ inv_nonneg.mpr (Nat.cast_nonneg q)

lemma sum_Icc_inv_sq_le_two (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, ((q : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have h := (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))
  have heq : Finset.Ioo 0 (N + 1) = Finset.Icc 1 N := by
    ext q
    simp
    omega
  rw [heq] at h
  norm_num at h ⊢
  exact h

lemma sum_divisorPairs_first_inv_le (N : ℕ) :
    (∑ p ∈ divisorPairs N, (p.1 : ℝ)⁻¹) ≤ 2 * N := by
  rw [sum_divisorPairs_eq_nested (N := N) (fun q _long ↦ (q : ℝ)⁻¹)]
  calc
    (∑ q ∈ Finset.Icc 1 N, ∑ _long ∈ Finset.Icc 1 (N / q), (q : ℝ)⁻¹)
        ≤ ∑ q ∈ Finset.Icc 1 N, (N : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro q hq
          have hqpos : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul]
          have hcard : (Finset.Icc 1 (N / q)).card = N / q := by simp
          rw [hcard]
          have hcast : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
            exact Nat.cast_div_le
          rw [div_eq_mul_inv] at hcast
          calc
            ((N / q : ℕ) : ℝ) * (q : ℝ)⁻¹
                ≤ ((N : ℝ) * (q : ℝ)⁻¹) * (q : ℝ)⁻¹ := by gcongr
            _ = (N : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
              rw [pow_two, mul_inv_rev]
              ring
    _ = (N : ℝ) * ∑ q ∈ Finset.Icc 1 N, ((q : ℝ) ^ 2)⁻¹ := by
      simp_rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * 2 := by
      gcongr
      exact sum_Icc_inv_sq_le_two N
    _ = 2 * N := by ring

lemma sum_divisorPairs_swap (N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ divisorPairs N, f p.1 p.2 = ∑ p ∈ divisorPairs N, f p.2 p.1 := by
  classical
  apply Finset.sum_bij (fun p _ ↦ p.swap)
  · intro p hp
    simpa [divisorPairs, Nat.mul_comm, and_left_comm, and_comm] using hp
  · intro p hp q hq heq
    simpa using congrArg Prod.swap heq
  · intro q hq
    refine ⟨q.swap, ?_, ?_⟩
    · simpa [divisorPairs, Nat.mul_comm, and_left_comm, and_comm] using hq
    · simp
  · intro p hp
    rfl

lemma sum_divisorPairs_second_inv_le (N : ℕ) :
    (∑ p ∈ divisorPairs N, (p.2 : ℝ)⁻¹) ≤ 2 * N := by
  rw [← sum_divisorPairs_swap N (fun q _long ↦ (q : ℝ)⁻¹)]
  exact sum_divisorPairs_first_inv_le N

lemma divisorPairs_card_cast_le (N : ℕ) :
    ((divisorPairs N).card : ℝ) ≤ (N : ℝ) * harmonicReal N := by
  have hcard : ((divisorPairs N).card : ℝ) =
      ∑ p ∈ divisorPairs N, (1 : ℝ) := by simp
  rw [hcard, sum_divisorPairs_eq_nested (N := N) (fun _q _long ↦ (1 : ℝ))]
  calc
    (∑ q ∈ Finset.Icc 1 N, ∑ _long ∈ Finset.Icc 1 (N / q), (1 : ℝ))
        ≤ ∑ q ∈ Finset.Icc 1 N, (N : ℝ) * (q : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul, mul_one]
          have hcardq : (Finset.Icc 1 (N / q)).card = N / q := by simp
          rw [hcardq]
          exact Nat.cast_div_le
    _ = (N : ℝ) * harmonicReal N := by
      rw [harmonicReal]
      exact (Finset.mul_sum (Finset.Icc 1 N) (fun q ↦ (q : ℝ)⁻¹) N).symm

lemma sum_divisorPairs_inv_mul_inv_le (N : ℕ) :
    (∑ p ∈ divisorPairs N, (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) ≤
      (harmonicReal N) ^ 2 := by
  calc
    (∑ p ∈ divisorPairs N, (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) ≤
        ∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
          (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              exact (Finset.mem_filter.mp hp).1
            · intro p hp hnot
              positivity
    _ = ∑ q ∈ Finset.Icc 1 N, ∑ long ∈ Finset.Icc 1 N,
          (q : ℝ)⁻¹ * (long : ℝ)⁻¹ :=
      Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 N)
        (fun p ↦ (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹)
    _ = (harmonicReal N) ^ 2 := by
      simp only [harmonicReal, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

lemma parameterWeight_cast_le {N b q long : ℕ} (hb : 0 < b) (hq : 0 < q)
    (hlong : 0 < long) (hlongN : long ≤ N) :
    (((long / b + 1) * (2 * b / q + 1) * (N / long + 1) : ℕ) : ℝ) ≤
      4 * N / q + 2 * N / b + 4 * N * b / (q * long) + 2 * N / long := by
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hdiv₁ : ((long / b : ℕ) : ℝ) ≤ (long : ℝ) / b := Nat.cast_div_le
  have hdiv₂ : ((2 * b / q : ℕ) : ℝ) ≤ (2 * b : ℕ) / q := Nat.cast_div_le
  have hdiv₃ : ((N / long : ℕ) : ℝ) ≤ (N : ℝ) / long := Nat.cast_div_le
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlongR : (0 : ℝ) < long := by exact_mod_cast hlong
  have hNdiv : (1 : ℝ) ≤ (N : ℝ) / long := by
    rw [le_div_iff₀ hlongR]
    simpa using (show (long : ℝ) ≤ N by exact_mod_cast hlongN)
  calc
    (((long / b : ℕ) : ℝ) + 1) * (((2 * b / q : ℕ) : ℝ) + 1) *
          (((N / long : ℕ) : ℝ) + 1)
        ≤ ((long : ℝ) / b + 1) * ((2 * b : ℕ) / q + 1) *
          ((N : ℝ) / long + 1) := by gcongr
    _ ≤ ((long : ℝ) / b + 1) * ((2 * b : ℕ) / q + 1) *
          (2 * ((N : ℝ) / long)) := by
            gcongr
            linarith
    _ = 4 * N / q + 2 * N / b + 4 * N * b / (q * long) + 2 * N / long := by
      push_cast
      field_simp
      ring

lemma parameterSum_cast_eq (N b : ℕ) :
    (parameterSum N b : ℝ) =
      ∑ p ∈ divisorPairs N,
        (((p.2 / b + 1) * (2 * b / p.1 + 1) * (N / p.2 + 1) : ℕ) : ℝ) := by
  rw [parameterSum]
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    (sum_divisorPairs_eq_nested (N := N) (fun q long ↦
      (((long / b + 1) * (2 * b / q + 1) * (N / long + 1) : ℕ) : ℝ))).symm

lemma parameterSum_cast_le {N b : ℕ} (hb : 0 < b)
    (hH : harmonicReal N ≤ (b : ℝ))
    (hbH : (b : ℝ) * (harmonicReal N) ^ 2 ≤ N) :
    (parameterSum N b : ℝ) ≤ 18 * (N : ℝ) ^ 2 := by
  rw [parameterSum_cast_eq]
  calc
    (∑ p ∈ divisorPairs N,
        (((p.2 / b + 1) * (2 * b / p.1 + 1) * (N / p.2 + 1) : ℕ) : ℝ))
        ≤ ∑ p ∈ divisorPairs N,
          ((4 : ℝ) * N / p.1 + 2 * N / b +
            4 * N * b / ((p.1 : ℝ) * p.2) + 2 * N / p.2) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp' := Finset.mem_filter.mp hp
              have hpIcc := Finset.mem_product.mp hp'.1
              exact parameterWeight_cast_le hb (by
                have := (Finset.mem_Icc.mp hpIcc.1).1
                omega) (by
                  have := (Finset.mem_Icc.mp hpIcc.2).1
                  omega) (Finset.mem_Icc.mp hpIcc.2).2
    _ = (4 : ℝ) * N * (∑ p ∈ divisorPairs N, (p.1 : ℝ)⁻¹) +
          (2 * N / (b : ℝ)) * ((divisorPairs N).card : ℝ) +
          4 * N * b * (∑ p ∈ divisorPairs N, (p.1 : ℝ)⁻¹ * (p.2 : ℝ)⁻¹) +
          2 * N * (∑ p ∈ divisorPairs N, (p.2 : ℝ)⁻¹) := by
            simp only [Finset.sum_add_distrib, div_eq_mul_inv, Finset.mul_sum,
              Finset.sum_const, nsmul_eq_mul]
            ring
    _ ≤ (4 : ℝ) * N * (2 * N) + (2 * N / (b : ℝ)) * (N * harmonicReal N) +
          4 * N * b * (harmonicReal N) ^ 2 + 2 * N * (2 * N) := by
            gcongr
            · exact sum_divisorPairs_first_inv_le N
            · exact divisorPairs_card_cast_le N
            · exact sum_divisorPairs_inv_mul_inv_le N
            · exact sum_divisorPairs_second_inv_le N
    _ ≤ 18 * (N : ℝ) ^ 2 := by
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hHdiv : harmonicReal N / b ≤ 1 := (div_le_one hbR).2 hH
      have hterm₂ : (2 * (N : ℝ) / b) * (N * harmonicReal N) ≤ 2 * N ^ 2 := by
        calc
          (2 * (N : ℝ) / b) * (N * harmonicReal N) =
              2 * N ^ 2 * (harmonicReal N / b) := by ring
          _ ≤ 2 * N ^ 2 * 1 := by gcongr
          _ = 2 * N ^ 2 := by ring
      have hterm₃ : 4 * (N : ℝ) * b * (harmonicReal N) ^ 2 ≤
          (4 : ℝ) * (N : ℝ) ^ 2 := by
        calc
          4 * (N : ℝ) * b * (harmonicReal N) ^ 2 =
              4 * N * ((b : ℝ) * (harmonicReal N) ^ 2) := by ring
          _ ≤ (4 : ℝ) * N * N := by gcongr
          _ = (4 : ℝ) * N ^ 2 := by ring
      nlinarith

lemma boxCollisions_card_cast_le {N b : ℕ} (hb : 0 < b)
    (hH : harmonicReal N ≤ (b : ℝ))
    (hbH : (b : ℝ) * (harmonicReal N) ^ 2 ≤ N) :
    ((boxCollisions N b).card : ℝ) ≤ 288 * (N : ℝ) ^ 2 := by
  calc
    ((boxCollisions N b).card : ℝ) ≤ (16 * parameterSum N b : ℕ) := by
      exact_mod_cast boxCollisions_card_le_parameterSum hb
    _ = (16 : ℝ) * (parameterSum N b : ℝ) := by push_cast; rfl
    _ ≤ 16 * (18 * (N : ℝ) ^ 2) := by
      gcongr
      exact parameterSum_cast_le hb hH hbH
    _ = 288 * (N : ℝ) ^ 2 := by ring

lemma boxImage_quadratic_lower {N b : ℕ} (hN : 2 ≤ N) (hb : 0 < b)
    (hH : harmonicReal N ≤ (b : ℝ))
    (hbH : (b : ℝ) * (harmonicReal N) ^ 2 ≤ N) :
    (N : ℝ) ^ 2 ≤
      23328 * (((Finset.univ : Finset (BoxInterval N)).image (boxValue N b)).card : ℝ) := by
  let A : Finset (BoxInterval N) := Finset.univ
  let X : ℝ := ((A.image (boxValue N b)).card : ℝ)
  let E : ℝ := (Erdos822.collisionEnergy A (boxValue N b) : ℝ)
  have hcardA : A.card = (N / 2) ^ 2 := by
    simp [A, boxSide, pow_two]
  have hCSnat := Erdos822.card_sq_le_image_card_mul_collisionEnergy A (boxValue N b)
  have hCS : (A.card : ℝ) ^ 2 ≤ X * E := by
    dsimp [X, E]
    exact_mod_cast hCSnat
  have hE : E ≤ 288 * (N : ℝ) ^ 2 := by
    dsimp [E]
    rw [← Erdos822.collisionPairs_card_eq_collisionEnergy]
    simpa only [A, boxCollisions] using boxCollisions_card_cast_le hb hH hbH
  have hX : 0 ≤ X := by positivity
  have hM : (N : ℝ) ≤ 3 * (N / 2 : ℕ) := by
    exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hMnonneg : (0 : ℝ) ≤ (N / 2 : ℕ) := by positivity
  have hN2 : (N : ℝ) ^ 2 ≤ 9 * ((N / 2 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((3 : ℝ) * (N / 2 : ℕ) - N)]
  have hN4 : (N : ℝ) ^ 4 ≤ 81 * ((N / 2 : ℕ) : ℝ) ^ 4 := by
    nlinarith [sq_nonneg (9 * (((N / 2 : ℕ) : ℝ) ^ 2) - (N : ℝ) ^ 2)]
  have hAreal : (A.card : ℝ) = ((N / 2 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcardA
  have hM4 : ((N / 2 : ℕ) : ℝ) ^ 4 ≤ X * E := by
    rw [hAreal] at hCS
    nlinarith [hCS]
  have hXE : X * E ≤ X * (288 * (N : ℝ) ^ 2) := by gcongr
  have hlarge : (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 2 * (23328 * X) := by
    calc
      (N : ℝ) ^ 4 ≤ 81 * ((N / 2 : ℕ) : ℝ) ^ 4 := hN4
      _ ≤ 81 * (X * E) := by gcongr
      _ ≤ 81 * (X * (288 * (N : ℝ) ^ 2)) := by gcongr
      _ = (N : ℝ) ^ 2 * (23328 * X) := by ring
  have hN2pos : 0 < (N : ℝ) ^ 2 := by positivity
  have := le_of_mul_le_mul_left (show
      (N : ℝ) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * (23328 * X) by
        calc
          (N : ℝ) ^ 2 * (N : ℝ) ^ 2 = (N : ℝ) ^ 4 := by ring
          _ ≤ (N : ℝ) ^ 2 * (23328 * X) := hlarge) hN2pos
  simpa [X, A] using this

lemma boxImage_subset_consecutiveSums (N : ℕ) :
    (Finset.univ : Finset (BoxInterval N)).image (boxValue N (Nat.sqrt N)) ⊆
      consecutiveSums (bekerSeq N) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact boxValue_mem_consecutiveSums N x

lemma consecutiveSums_quadratic_lower {N : ℕ} (hN : 2 ≤ N)
    (hH : harmonicReal N ≤ (Nat.sqrt N : ℝ))
    (hbH : (Nat.sqrt N : ℝ) * (harmonicReal N) ^ 2 ≤ N) :
    (N : ℝ) ^ 2 ≤ 23328 * ((consecutiveSums (bekerSeq N)).card : ℝ) := by
  have hb : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
  refine (boxImage_quadratic_lower hN hb hH hbH).trans ?_
  gcongr
  exact boxImage_subset_consecutiveSums N

/-! ## The eventual choice `b = floor(sqrt N)` -/

lemma harmonicReal_le_one_add_log (N : ℕ) :
    harmonicReal N ≤ 1 + Real.log (N : ℝ) := by
  simpa only [harmonicReal, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div] using harmonic_le_one_add_log N

lemma eventually_harmonicReal_le_quarter_rpow :
    ∀ᶠ N : ℕ in atTop,
      harmonicReal N ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
        2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have hsmallReal :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 4) (by norm_num)).bound
      (show 0 < (1 / 2 : ℝ) by norm_num)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have hpowTop : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp
      tendsto_natCast_atTop_atTop
  have hpowTwo := hpowTop.eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 1, hsmallNat, hpowTwo] with N hN hsmall hpow
  have hlognonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hrpownonneg : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hsmallAbs : Real.log (N : ℝ) ≤
      (1 / 2 : ℝ) * |(N : ℝ) ^ (1 / 4 : ℝ)| := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlognonneg] using hsmall
  have hsmall' : Real.log (N : ℝ) ≤
      (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [abs_of_nonneg hrpownonneg] at hsmallAbs
    exact hsmallAbs
  refine ⟨(harmonicReal_le_one_add_log N).trans ?_, hpow⟩
  linarith

lemma eventually_sqrt_harmonic_conditions :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 0 < Nat.sqrt N ∧
      harmonicReal N ≤ (Nat.sqrt N : ℝ) ∧
      (Nat.sqrt N : ℝ) * (harmonicReal N) ^ 2 ≤ N := by
  filter_upwards [eventually_ge_atTop 2, eventually_harmonicReal_le_quarter_rpow]
    with N hN hquarter
  let Q : ℝ := (N : ℝ) ^ (1 / 4 : ℝ)
  have hNR : (0 : ℝ) < N := by positivity
  have hQnonneg : 0 ≤ Q := Real.rpow_nonneg hNR.le _
  have hQsq : Q ^ 2 = Real.sqrt (N : ℝ) := by
    dsimp [Q]
    rw [pow_two, ← Real.rpow_add hNR]
    norm_num
    exact (Real.sqrt_eq_rpow (N : ℝ)).symm
  have hsqrtUpper : Real.sqrt (N : ℝ) ≤ (Nat.sqrt N : ℝ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · exact_mod_cast (Nat.le_of_lt (Nat.lt_succ_sqrt' N))
  have hQleSqrtNat : Q ≤ (Nat.sqrt N : ℝ) := by
    have hQadd : Q + 1 ≤ Q ^ 2 := by nlinarith [hquarter.2]
    nlinarith
  have hHle : harmonicReal N ≤ (Nat.sqrt N : ℝ) := hquarter.1.trans hQleSqrtNat
  have hHsq : (harmonicReal N) ^ 2 ≤ Real.sqrt (N : ℝ) := by
    have hHnonneg := harmonicReal_nonneg N
    nlinarith [hquarter.1, hQsq]
  have hbSq : ((Nat.sqrt N : ℝ) : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  have hbLe : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.le_sqrt_of_sq_le hbSq
  have hprod : (Nat.sqrt N : ℝ) * (harmonicReal N) ^ 2 ≤
      Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by
    exact mul_le_mul hbLe hHsq (sq_nonneg _) (by positivity)
  refine ⟨hN, Nat.sqrt_pos.mpr (by omega), hHle, ?_⟩
  simpa [Real.mul_self_sqrt hNR.le] using hprod

/-! ## Resolution of Erdős Problem 356 -/

/-- Erdős Problem 356 has an affirmative answer.  The proof supplies the
absolute constant `c = 1 / 300000`. -/
theorem erdos356 : Problem356 := by
  refine ⟨1 / 300000, by norm_num, ?_⟩
  have hparameters : ∀ᶠ n : ℕ in atTop,
      2 ≤ n / 2 ∧ 0 < Nat.sqrt (n / 2) ∧
      harmonicReal (n / 2) ≤ (Nat.sqrt (n / 2) : ℝ) ∧
      (Nat.sqrt (n / 2) : ℝ) * (harmonicReal (n / 2)) ^ 2 ≤ ((n / 2 : ℕ) : ℝ) :=
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually
      eventually_sqrt_harmonic_conditions
  filter_upwards [hparameters, eventually_ge_atTop 4] with n hparam hn
  let N : ℕ := n / 2
  refine ⟨N, bekerSeq N, bekerSeq_strictMono N, ?_, ?_⟩
  · intro i
    refine ⟨(bekerSeq_bounds N i).1, (bekerSeq_bounds N i).2.trans ?_⟩
    dsimp [N]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n 2
  · have hN : 2 ≤ N := by simpa [N] using hparam.1
    have hsum : (N : ℝ) ^ 2 ≤
        23328 * ((consecutiveSums (bekerSeq N)).card : ℝ) := by
      apply consecutiveSums_quadratic_lower hN
      · simpa [N] using hparam.2.2.1
      · simpa [N] using hparam.2.2.2
    have hNpos : 0 < N := by omega
    have hnN : n ≤ 3 * N := by
      dsimp [N]
      omega
    have hnNR : (n : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast hnN
    have hnSq : (n : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [sq_nonneg (3 * (N : ℝ) - n)]
    have hcombined : (n : ℝ) ^ 2 ≤
        209952 * ((consecutiveSums (bekerSeq N)).card : ℝ) := by
      calc
        (n : ℝ) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := hnSq
        _ ≤ 9 * (23328 * ((consecutiveSums (bekerSeq N)).card : ℝ)) := by gcongr
        _ = 209952 * ((consecutiveSums (bekerSeq N)).card : ℝ) := by ring
    have hcardnonneg : (0 : ℝ) ≤ (consecutiveSums (bekerSeq N)).card := by positivity
    calc
      (1 / 300000 : ℝ) * (n : ℝ) ^ 2 ≤
          (1 / 300000 : ℝ) *
            (209952 * ((consecutiveSums (bekerSeq N)).card : ℝ)) := by gcongr
      _ ≤ ((consecutiveSums (bekerSeq N)).card : ℝ) := by
        norm_num
        nlinarith

#print axioms Erdos356.erdos356

end Erdos356
