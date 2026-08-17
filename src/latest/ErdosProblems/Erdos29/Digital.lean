import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic

/-!
# Mixed-radix gluing for Erdős Problem 29

This file isolates the digital part of the construction.  A `LocalSystem`
consists of bases and a finite set of permitted digits in every position.
The local hypothesis says that every digit, with either possible incoming
carry, is the sum of two permitted digits with an outgoing carry in `{0,1}`.

The global set has permitted digits below its most significant digit and an
unrestricted most significant digit.  The definitions below use an inductive
description of finite digit strings; in particular they do not rely on a
choice of representatives.
-/

namespace Erdos29

namespace MixedRadix

open scoped Pointwise

/-- Finite local data sufficient for the digital gluing argument. -/
structure LocalSystem where
  base : ℕ → ℕ
  digits : ℕ → Finset ℕ
  two_le_base : ∀ i, 2 ≤ base i
  digit_lt : ∀ i d, d ∈ digits i → d < base i
  carryCover : ∀ i r c, r < base i → c ≤ 1 →
    ∃ x ∈ digits i, ∃ y ∈ digits i, ∃ c' ≤ 1,
      x + y + c = r + base i * c'

/-- Package ordinary modular additive coverage into the carry-aware local
system used by the gluing theorem. -/
def LocalSystem.ofModular (base : ℕ → ℕ) (digits : ℕ → Finset ℕ)
    (hbase : ∀ i, 2 ≤ base i)
    (hdigit : ∀ i d, d ∈ digits i → d < base i)
    (hcover : ∀ i r, r < base i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % base i = r) :
    LocalSystem where
  base := base
  digits := digits
  two_le_base := hbase
  digit_lt := hdigit
  carryCover := by
    intro i r c hr hc
    have hB : 0 < base i := lt_of_lt_of_le Nat.zero_lt_two (hbase i)
    let t := (r + base i - c) % base i
    obtain ⟨x, hx, y, hy, hxy⟩ := hcover i t (Nat.mod_lt _ hB)
    have hcr : c ≤ r + base i := by omega
    have hadd : r + base i - c + c = r + base i := Nat.sub_add_cancel hcr
    have hmod : (x + y + c) % base i = r := by
      have hxy' : Nat.ModEq (base i) (x + y) (r + base i - c) := hxy
      have hradd : Nat.ModEq (base i) (r + base i) r := by
        change (r + base i) % base i = r % base i
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
      have hxyc : Nat.ModEq (base i) (x + y + c) (r + base i) := by
        rw [← hadd]
        exact hxy'.add_right c
      have hmodEq := hxyc.trans hradd
      exact (show (x + y + c) % base i = r % base i from hmodEq).trans
        (Nat.mod_eq_of_lt hr)
    refine ⟨x, hx, y, hy, (x + y + c) / base i, ?_, ?_⟩
    · have hxlt := hdigit i x hx
      have hylt := hdigit i y hy
      have hsum : x + y + c < 2 * base i := by omega
      have hdiv : (x + y + c) / base i < 2 :=
        (Nat.div_lt_iff_lt_mul hB).2 (by simpa [Nat.mul_comm] using hsum)
      omega
    · calc
        x + y + c = (x + y + c) % base i +
            base i * ((x + y + c) / base i) :=
          (Nat.mod_add_div _ _).symm
        _ = r + base i * ((x + y + c) / base i) := by rw [hmod]

variable (S : LocalSystem)

/-- Place value of position `k`. -/
def place : ℕ → ℕ
  | 0 => 1
  | k + 1 => place k * S.base k

@[simp] theorem place_zero : place S 0 = 1 := rfl

@[simp] theorem place_succ (k : ℕ) :
    place S (k + 1) = place S k * S.base k := rfl

theorem place_pos (k : ℕ) : 0 < place S k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [place_succ]
      exact Nat.mul_pos ih (lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base k))

/-- A number represented by exactly `k` permitted low digits. -/
inductive LowWord : ℕ → ℕ → Prop
  | zero : LowWord 0 0
  | succ {k n d} : LowWord k n → d ∈ S.digits k →
      LowWord (k + 1) (n + d * place S k)

theorem lowWord_lt_place {k n : ℕ} (h : LowWord S k n) : n < place S k := by
  induction h with
  | zero => simp
  | @succ k n d hn hd ih =>
      rw [place_succ]
      have hdlt := S.digit_lt k d hd
      have hp := place_pos S k
      nlinarith

/-- The global mixed-radix set.  The `top` digit is unrestricted. -/
def basis : Set ℕ :=
  {n | ∃ k low top, LowWord S k low ∧ top < S.base k ∧
      n = low + top * place S k}

theorem zero_mem_basis : 0 ∈ basis S := by
  refine ⟨0, 0, 0, LowWord.zero, ?_, by simp⟩
  exact lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base 0)

/-- The largest occupied mixed-radix position.  The search is bounded by `n`;
`place_ge_succ` below shows that this bound loses no positions. -/
def level (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => place S k ≤ n) n

theorem place_ge_succ (k : ℕ) : k + 1 ≤ place S k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [place_succ]
      have hb := S.two_le_base k
      have hp := place_pos S k
      nlinarith

theorem level_le (n : ℕ) : level S n ≤ n :=
  Nat.findGreatest_le n

@[simp] theorem level_zero : level S 0 = 0 := by
  simp [level]

theorem place_dvd_of_le {i k : ℕ} (hik : i ≤ k) :
    place S i ∣ place S k := by
  induction k with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact dvd_rfl
  | succ k ih =>
      by_cases h : i = k + 1
      · subst i
        exact dvd_rfl
      · have hik' : i ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hik h)
        exact (ih hik').trans (by simp [place_succ])

theorem place_mono : Monotone (place S) := by
  intro i k hik
  exact Nat.le_of_dvd (place_pos S k) (place_dvd_of_le S hik)

theorem place_level_le {n : ℕ} (hn : 0 < n) :
    place S (level S n) ≤ n := by
  unfold level
  exact Nat.findGreatest_spec (P := fun k => place S k ≤ n)
    (Nat.zero_le n) (by simp only [place_zero]; omega)

theorem lt_place_level_succ {n : ℕ} (hn : 0 < n) :
    n < place S (level S n + 1) := by
  apply Nat.lt_of_not_ge
  intro hplace
  have hkn : level S n + 1 ≤ n :=
    (Nat.le_succ (level S n + 1)).trans
      ((place_ge_succ S (level S n + 1)).trans hplace)
  exact Nat.findGreatest_is_greatest (P := fun k => place S k ≤ n)
    (Nat.lt_succ_self _) hkn hplace

theorem level_mono : Monotone (level S) := by
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  · apply Nat.le_findGreatest
    · exact (level_le S m).trans hmn
    · exact (place_level_le S (Nat.pos_of_ne_zero hm)).trans hmn

theorem lowWord_mod {i k n : ℕ} (hik : i ≤ k) (h : LowWord S k n) :
    LowWord S i (n % place S i) := by
  induction h with
  | zero =>
      have : i = 0 := by omega
      subst i
      simpa using LowWord.zero (S := S)
  | @succ k n d hn hd ih =>
      by_cases hi : i = k + 1
      · subst i
        rw [Nat.mod_eq_of_lt (lowWord_lt_place S (LowWord.succ hn hd))]
        exact LowWord.succ hn hd
      · have hik' : i ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne hik hi)
        have hdvd : place S i ∣ place S k := place_dvd_of_le S hik'
        have hmod : place S k % place S i = 0 := Nat.mod_eq_zero_of_dvd hdvd
        simpa [Nat.add_mod, Nat.mul_mod, hmod] using ih hik'

theorem basis_lt_place_succ {n k low top : ℕ}
    (hlow : LowWord S k low) (htop : top < S.base k)
    (hn : n = low + top * place S k) : n < place S (k + 1) := by
  rw [hn, place_succ]
  have hl := lowWord_lt_place S hlow
  have hp := place_pos S k
  nlinarith

/-- Membership gives the permitted canonical prefix below `level n`. -/
theorem lowWord_level_of_mem {n : ℕ} (hn : n ∈ basis S) :
    LowWord S (level S n) (n % place S (level S n)) := by
  rcases hn with ⟨k, low, top, hlow, htop, rfl⟩
  by_cases hz : low + top * place S k = 0
  · rw [hz]
    simpa using LowWord.zero (S := S)
  · have hnpos : 0 < low + top * place S k := Nat.pos_of_ne_zero hz
    have hlevel : level S (low + top * place S k) ≤ k := by
      apply Nat.le_of_not_lt
      intro hk
      have hs : k + 1 ≤ level S (low + top * place S k) := hk
      have hplace : place S (k + 1) ≤ low + top * place S k :=
        (place_mono S hs).trans (place_level_le S hnpos)
      exact (Nat.not_le_of_gt (basis_lt_place_succ S hlow htop rfl)) hplace
    have hprefix := lowWord_mod S hlevel hlow
    have hdvd : place S (level S (low + top * place S k)) ∣ place S k :=
      place_dvd_of_le S hlevel
    have hmod : place S k % place S (level S (low + top * place S k)) = 0 :=
      Nat.mod_eq_zero_of_dvd hdvd
    simpa [Nat.add_mod, Nat.mul_mod, hmod] using hprefix

theorem lowWord_prefix_of_mem {i n : ℕ} (hi : i ≤ level S n)
    (hn : n ∈ basis S) : LowWord S i (n % place S i) := by
  have h := lowWord_mod S hi (lowWord_level_of_mem S hn)
  have hdvd : place S i ∣ place S (level S n) := place_dvd_of_le S hi
  simpa [Nat.mod_mod_of_dvd _ hdvd] using h

/-- Coverage of a finite low block, recording its outgoing carry. -/
theorem lower_cover : ∀ k r, r < place S k →
    ∃ a b c, LowWord S k a ∧ LowWord S k b ∧ c ≤ 1 ∧
      a + b = r + c * place S k := by
  intro k
  induction k with
  | zero =>
      intro r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      exact ⟨0, 0, 0, LowWord.zero, LowWord.zero, by simp, by simp⟩
  | succ k ih =>
      intro r hr
      have hP : 0 < place S k := place_pos S k
      have hr0 : r % place S k < place S k := Nat.mod_lt r hP
      obtain ⟨a, b, c, ha, hb, hc, hab⟩ := ih (r % place S k) hr0
      have hq : r / place S k < S.base k := by
        apply (Nat.div_lt_iff_lt_mul hP).2
        simpa [place_succ, Nat.mul_comm] using hr
      obtain ⟨x, hx, y, hy, c', hc', hxy⟩ :=
        S.carryCover k (r / place S k) c hq hc
      refine ⟨a + x * place S k, b + y * place S k, c', ?_, ?_, hc', ?_⟩
      · exact LowWord.succ ha hx
      · exact LowWord.succ hb hy
      · calc
          (a + x * place S k) + (b + y * place S k) =
              (a + b) + (x + y) * place S k := by ring
          _ = (r % place S k + c * place S k) +
              (x + y) * place S k := by rw [hab]
          _ = r % place S k + (x + y + c) * place S k := by ring
          _ = r % place S k +
              (r / place S k + S.base k * c') * place S k := by rw [hxy]
          _ = (r % place S k + place S k * (r / place S k)) +
              c' * (place S k * S.base k) := by ring
          _ = r + c' * place S (k + 1) := by
            rw [Nat.mod_add_div, place_succ]

/-- Every natural number is a sum of two members of the mixed-radix set. -/
theorem basis_add_basis : basis S + basis S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  rw [Set.mem_add]
  by_cases hn : n = 0
  · subst n
    exact ⟨0, zero_mem_basis S, 0, zero_mem_basis S, by simp⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let k := level S n
    let P := place S k
    let B := S.base k
    have hPle : P ≤ n := by simpa [P, k] using place_level_le S hnpos
    have hnlt : n < P * B := by
      simpa [P, B, k, place_succ] using lt_place_level_succ S hnpos
    have hqpos : 0 < n / P := Nat.div_pos hPle (place_pos S k)
    have hqlt : n / P < B := by
      apply (Nat.div_lt_iff_lt_mul (place_pos S k)).2
      simpa [P, B, Nat.mul_comm] using hnlt
    obtain ⟨a, b, c, ha, hb, hc, hab⟩ :=
      lower_cover S k (n % P) (Nat.mod_lt _ (place_pos S k))
    have hcq : c ≤ n / P := hc.trans hqpos
    let u := n / P - c
    have hult : u < B := lt_of_le_of_lt (Nat.sub_le _ _) hqlt
    have hzeroB : 0 < B := lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base k)
    refine ⟨a + u * P, ?_, b, ?_, ?_⟩
    · exact ⟨k, a, u, ha, hult, rfl⟩
    · exact ⟨k, b, 0, hb, hzeroB, by simp⟩
    · have hsub : u + c = n / P := Nat.sub_add_cancel hcq
      calc
        a + u * P + b = (a + b) + u * P := by ring
        _ = (n % P + c * P) + u * P := by rw [hab]
        _ = n % P + (u + c) * P := by ring
        _ = n % P + (n / P) * P := by rw [hsub]
        _ = n := by rw [Nat.mul_comm, Nat.mod_add_div]

/-! ## Counting representations -/

/-- The finite set of all permitted words of length `k`. -/
def lowWords : ℕ → Finset ℕ
  | 0 => {0}
  | k + 1 => (S.digits k).biUnion fun d =>
      (lowWords k).image fun n => n + d * place S k

@[simp] theorem mem_lowWords_iff {k n : ℕ} :
    n ∈ lowWords S k ↔ LowWord S k n := by
  constructor
  · intro hn
    induction k generalizing n with
    | zero =>
        simp only [lowWords, Finset.mem_singleton] at hn
        subst n
        exact LowWord.zero
    | succ k ih =>
        simp only [lowWords, Finset.mem_biUnion, Finset.mem_image] at hn
        obtain ⟨d, hd, a, ha, rfl⟩ := hn
        exact LowWord.succ (ih ha) hd
  · intro hn
    induction hn with
    | zero => simp [lowWords]
    | @succ k n d hn hd ih =>
        simp only [lowWords, Finset.mem_biUnion, Finset.mem_image]
        exact ⟨d, hd, n, ih, rfl⟩

/-- Ordered permitted low-word pairs which have the prescribed sum modulo
the first `k` bases. -/
def prefixPairs (k r : ℕ) : Finset (ℕ × ℕ) :=
  ((lowWords S k).product (lowWords S k)).filter fun ab =>
    (ab.1 + ab.2) % place S k = r % place S k

/-- Number of ordered representations supplied by the first `k` digits. -/
def prefixRepCount (k r : ℕ) : ℕ := (prefixPairs S k r).card

/-- Ordered local digit pairs with a prescribed residue. -/
def localPairs (i r : ℕ) : Finset (ℕ × ℕ) :=
  ((S.digits i).product (S.digits i)).filter fun xy =>
    (xy.1 + xy.2) % S.base i = r % S.base i

/-- The same local fiber with an incoming carry. -/
def localCarryPairs (i r c : ℕ) : Finset (ℕ × ℕ) :=
  ((S.digits i).product (S.digits i)).filter fun xy =>
    (xy.1 + xy.2 + c) % S.base i = r % S.base i

theorem localCarryPairs_card_le_of_flat {M : ℕ}
    (hflat : ∀ i r, (localPairs S i r).card ≤ M)
    (i r c : ℕ) (hc : c ≤ 1) :
    (localCarryPairs S i r c).card ≤ M := by
  have hbase := S.two_le_base i
  have hcr : c ≤ r + S.base i := by omega
  have hadd : r + S.base i - c + c = r + S.base i := Nat.sub_add_cancel hcr
  have heq : localCarryPairs S i r c =
      localPairs S i (r + S.base i - c) := by
    ext xy
    simp only [localCarryPairs, localPairs, Finset.mem_filter, Finset.mem_product]
    apply and_congr_right
    intro _
    change Nat.ModEq (S.base i) (xy.1 + xy.2 + c) r ↔
      Nat.ModEq (S.base i) (xy.1 + xy.2) (r + S.base i - c)
    have hradd : Nat.ModEq (S.base i) (r + S.base i) r := by
      change (r + S.base i) % S.base i = r % S.base i
      simp
    constructor
    · intro h
      apply Nat.ModEq.add_right_cancel' c
      exact h.trans (by simpa [hadd] using hradd.symm)
    · intro h
      exact h.add_right c |>.trans (by simpa [hadd] using hradd)
  rw [heq]
  exact hflat i (r + S.base i - c)

theorem lowWord_succ_split {k n : ℕ} (h : LowWord S (k + 1) n) :
    LowWord S k (n % place S k) ∧ n / place S k ∈ S.digits k := by
  cases h with
  | @succ _ low d hlow hd =>
      have hlt := lowWord_lt_place S hlow
      have hp := place_pos S k
      constructor
      · simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hlt] using hlow
      · have heq : (low + d * place S k) / place S k = d := by
          rw [Nat.mul_comm d, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt,
            zero_add]
        simpa [heq] using hd

private theorem add_div_eq_div_add_carry (a b P : ℕ) (hP : 0 < P) :
    (a + b) / P = a / P + b / P + (a % P + b % P) / P := by
  rw [Nat.add_div hP]
  by_cases h : P ≤ a % P + b % P
  · have ha := Nat.mod_lt a hP
    have hb := Nat.mod_lt b hP
    have hlt : a % P + b % P < (1 + 1) * P := by omega
    have hdiv : (a % P + b % P) / P = 1 :=
      Nat.div_eq_of_lt_le (by simpa using h) hlt
    simp [h, hdiv]
  · have hlt : a % P + b % P < P := Nat.lt_of_not_ge h
    have hdiv : (a % P + b % P) / P = 0 := Nat.div_eq_of_lt hlt
    simp [h, hdiv]

/-- A finite superset of the length-`k+1` prefix pairs, obtained by extending
each length-`k` pair by one local carry fiber. -/
def prefixExtensions (k r : ℕ) : Finset (ℕ × ℕ) :=
  (prefixPairs S k r).biUnion fun low =>
    (localCarryPairs S k (r / place S k)
      ((low.1 + low.2) / place S k)).image fun top =>
        (low.1 + top.1 * place S k, low.2 + top.2 * place S k)

theorem prefixPairs_succ_subset_extensions (k r : ℕ) :
    prefixPairs S (k + 1) r ⊆ prefixExtensions S k r := by
  intro ab hab
  rw [prefixPairs, Finset.mem_filter] at hab
  rcases hab with ⟨habWords, habMod⟩
  have habWords' := Finset.mem_product.mp habWords
  have haSplit := lowWord_succ_split S ((mem_lowWords_iff (S := S)).1 habWords'.1)
  have hbSplit := lowWord_succ_split S ((mem_lowWords_iff (S := S)).1 habWords'.2)
  let low : ℕ × ℕ := (ab.1 % place S k, ab.2 % place S k)
  let top : ℕ × ℕ := (ab.1 / place S k, ab.2 / place S k)
  have hlow : low ∈ prefixPairs S k r := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (mem_lowWords_iff (S := S)).2 haSplit.1
    · exact (mem_lowWords_iff (S := S)).2 hbSplit.1
    · have hdvd : place S k ∣ place S (k + 1) := by simp [place_succ]
      have := congrArg (fun z => z % place S k) habMod
      simpa [low, Nat.add_mod, Nat.mod_mod_of_dvd _ hdvd] using this
  have htop : top ∈ localCarryPairs S k (r / place S k)
      ((low.1 + low.2) / place S k) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨haSplit.2, hbSplit.2⟩, ?_⟩
    have hquot := congrArg (fun z => z / place S k) habMod
    have hP := place_pos S k
    have hadd := add_div_eq_div_add_carry ab.1 ab.2 (place S k) hP
    rw [place_succ, Nat.mul_comm] at hquot
    rw [Nat.mod_mul_left_div_self, Nat.mod_mul_left_div_self] at hquot
    simpa [top, low, hadd] using hquot
  apply Finset.mem_biUnion.mpr
  refine ⟨low, hlow, Finset.mem_image.mpr ⟨top, htop, ?_⟩⟩
  apply Prod.ext <;> simp only [top, low]
  · simpa [Nat.mul_comm] using Nat.mod_add_div ab.1 (place S k)
  · simpa [Nat.mul_comm] using Nat.mod_add_div ab.2 (place S k)

theorem prefixExtensions_card_le {M : ℕ}
    (hflat : ∀ i r, (localPairs S i r).card ≤ M) (k r : ℕ) :
    (prefixExtensions S k r).card ≤ prefixRepCount S k r * M := by
  classical
  calc
    (prefixExtensions S k r).card ≤
        ∑ low ∈ prefixPairs S k r,
          ((localCarryPairs S k (r / place S k)
            ((low.1 + low.2) / place S k)).image fun top =>
              (low.1 + top.1 * place S k,
                low.2 + top.2 * place S k)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _low ∈ prefixPairs S k r, M := by
      apply Finset.sum_le_sum
      intro low hlow
      apply Finset.card_image_le.trans
      apply localCarryPairs_card_le_of_flat S hflat
      rw [prefixPairs, Finset.mem_filter] at hlow
      have hpairs := Finset.mem_product.mp hlow.1
      have hlow1 := lowWord_lt_place S ((mem_lowWords_iff (S := S)).1 hpairs.1)
      have hlow2 := lowWord_lt_place S ((mem_lowWords_iff (S := S)).1 hpairs.2)
      have hP := place_pos S k
      have hsum : low.1 + low.2 < 2 * place S k := by omega
      have hdiv : (low.1 + low.2) / place S k < 2 :=
        (Nat.div_lt_iff_lt_mul hP).2 (by simpa [Nat.mul_comm] using hsum)
      omega
    _ = prefixRepCount S k r * M := by simp [prefixRepCount]

/-- Uniform flatness of every local ordered sum fiber multiplies across the
mixed-radix prefix. -/
theorem prefixRepCount_le_pow {M : ℕ}
    (hflat : ∀ i r, (localPairs S i r).card ≤ M) :
    ∀ k r, prefixRepCount S k r ≤ M ^ k := by
  intro k
  induction k with
  | zero =>
      intro r
      have hcard := Finset.card_filter_le
        ({(0, 0)} : Finset (ℕ × ℕ))
        (fun ab : ℕ × ℕ => (ab.1 + ab.2) % 1 = r % 1)
      simpa [prefixRepCount, prefixPairs, lowWords, place] using hcard
  | succ k ih =>
      intro r
      calc
        prefixRepCount S (k + 1) r ≤ (prefixExtensions S k r).card :=
          Finset.card_le_card (prefixPairs_succ_subset_extensions S k r)
        _ ≤ prefixRepCount S k r * M := prefixExtensions_card_le S hflat k r
        _ ≤ M ^ k * M := Nat.mul_le_mul_right M (ih r)
        _ = M ^ (k + 1) := by rw [pow_succ]

/-- The ordered convolution of the global set. -/
noncomputable def basisRepFinset (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.antidiagonal n).filter fun ab =>
    ab.1 ∈ basis S ∧ ab.2 ∈ basis S

noncomputable def basisRepCount (n : ℕ) : ℕ := (basisRepFinset S n).card

theorem div_place_level_lt_base (n : ℕ) :
    n / place S (level S n) < S.base (level S n) := by
  by_cases hn : n = 0
  · subst n
    simp only [level_zero, Nat.zero_div]
    exact lt_of_lt_of_le Nat.zero_lt_two (S.two_le_base 0)
  · apply (Nat.div_lt_iff_lt_mul (place_pos S (level S n))).2
    simpa [place_succ, Nat.mul_comm] using lt_place_level_succ S (Nat.pos_of_ne_zero hn)

/-- A code for an oriented representation. -/
structure RepCode where
  level : ℕ
  lowSmall : ℕ
  lowLarge : ℕ
  topSmall : ℕ
  deriving DecidableEq

/-- Codes allowed at one possible level of the smaller summand. -/
def codesAt (n l : ℕ) : Finset RepCode :=
  ((prefixPairs S l n).product (Finset.range (S.base l))).image fun p =>
    { level := l, lowSmall := p.1.1, lowLarge := p.1.2, topSmall := p.2 }

/-- All oriented codes which can occur in a representation of `n`. -/
def codeSpace (n : ℕ) : Finset (Bool × RepCode) :=
  Finset.univ.product <| (Finset.range (level S n + 1)).biUnion (codesAt S n)

/-- The code remembers which summand was smaller, its level, both low
prefixes, and the top digit of the smaller summand. -/
def repCode (ab : ℕ × ℕ) : Bool × RepCode :=
  if ab.1 ≤ ab.2 then
    (false, ⟨level S ab.1,
      ab.1 % place S (level S ab.1),
      ab.2 % place S (level S ab.1),
      ab.1 / place S (level S ab.1)⟩)
  else
    (true, ⟨level S ab.2,
      ab.2 % place S (level S ab.2),
      ab.1 % place S (level S ab.2),
      ab.2 / place S (level S ab.2)⟩)

/-- The natural digital upper bound before inserting a uniform local bound. -/
def digitalBound (n : ℕ) : ℕ :=
  2 * ∑ l ∈ Finset.range (level S n + 1),
    S.base l * prefixRepCount S l n

theorem repCode_mem_codeSpace {n : ℕ × ℕ} {N : ℕ}
    (hn : n ∈ basisRepFinset S N) : repCode S n ∈ codeSpace S N := by
  classical
  rw [basisRepFinset, Finset.mem_filter] at hn
  have hsum : n.1 + n.2 = N := Finset.mem_antidiagonal.mp hn.1
  have hn1 : n.1 ∈ basis S := hn.2.1
  have hn2 : n.2 ∈ basis S := hn.2.2
  by_cases hle : n.1 ≤ n.2
  · rw [repCode, if_pos hle]
    unfold codeSpace
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨level S n.1, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le <| level_mono S (by omega)
    · apply Finset.mem_image.mpr
      refine ⟨((n.1 % place S (level S n.1),
        n.2 % place S (level S n.1)),
        n.1 / place S (level S n.1)), ?_, rfl⟩
      apply Finset.mem_product.mpr
      constructor
      · change (n.1 % place S (level S n.1),
          n.2 % place S (level S n.1)) ∈ prefixPairs S (level S n.1) N
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · simpa using lowWord_level_of_mem S hn1
        · simpa using lowWord_prefix_of_mem S (level_mono S hle) hn2
        · rw [← Nat.add_mod, hsum]
      · exact Finset.mem_range.mpr (div_place_level_lt_base S n.1)
  · have hle' : n.2 ≤ n.1 := Nat.le_of_not_ge hle
    rw [repCode, if_neg hle]
    unfold codeSpace
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨level S n.2, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le <| level_mono S (by omega)
    · apply Finset.mem_image.mpr
      refine ⟨((n.2 % place S (level S n.2),
        n.1 % place S (level S n.2)),
        n.2 / place S (level S n.2)), ?_, rfl⟩
      apply Finset.mem_product.mpr
      constructor
      · change (n.2 % place S (level S n.2),
          n.1 % place S (level S n.2)) ∈ prefixPairs S (level S n.2) N
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · simpa using lowWord_level_of_mem S hn2
        · simpa using lowWord_prefix_of_mem S (level_mono S hle') hn1
        · rw [Nat.add_comm, ← Nat.add_mod, hsum]
      · exact Finset.mem_range.mpr (div_place_level_lt_base S n.2)

private theorem eq_of_level_mod_div_eq {a b : ℕ}
    (hl : level S a = level S b)
    (hm : a % place S (level S a) = b % place S (level S b))
    (hd : a / place S (level S a) = b / place S (level S b)) : a = b := by
  calc
    a = a % place S (level S a) +
        place S (level S a) * (a / place S (level S a)) :=
      (Nat.mod_add_div _ _).symm
    _ = b % place S (level S b) +
        place S (level S b) * (b / place S (level S b)) := by
      rw [hl] at hm hd ⊢
      rw [hm, hd]
    _ = b := Nat.mod_add_div _ _

theorem repCode_injOn (N : ℕ) :
    Set.InjOn (repCode S) (basisRepFinset S N) := by
  classical
  intro a ha b hb hcode
  change a ∈ basisRepFinset S N at ha
  change b ∈ basisRepFinset S N at hb
  rw [basisRepFinset, Finset.mem_filter] at ha hb
  have haSum : a.1 + a.2 = N := Finset.mem_antidiagonal.mp ha.1
  have hbSum : b.1 + b.2 = N := Finset.mem_antidiagonal.mp hb.1
  by_cases haLe : a.1 ≤ a.2 <;> by_cases hbLe : b.1 ≤ b.2
  · rw [repCode, if_pos haLe, repCode, if_pos hbLe] at hcode
    have hp := congrArg Prod.snd hcode
    have hl := congrArg RepCode.level hp
    have hm := congrArg RepCode.lowSmall hp
    have hd := congrArg RepCode.topSmall hp
    have hfirst : a.1 = b.1 := eq_of_level_mod_div_eq S hl hm hd
    apply Prod.ext hfirst
    omega
  · rw [repCode, if_pos haLe, repCode, if_neg hbLe] at hcode
    simp at hcode
  · rw [repCode, if_neg haLe, repCode, if_pos hbLe] at hcode
    simp at hcode
  · rw [repCode, if_neg haLe, repCode, if_neg hbLe] at hcode
    have hp := congrArg Prod.snd hcode
    have hl := congrArg RepCode.level hp
    have hm := congrArg RepCode.lowSmall hp
    have hd := congrArg RepCode.topSmall hp
    have hsecond : a.2 = b.2 := eq_of_level_mod_div_eq S hl hm hd
    apply Prod.ext
    · omega
    · exact hsecond

theorem basisRepCount_le_codeSpace (N : ℕ) :
    basisRepCount S N ≤ (codeSpace S N).card := by
  classical
  unfold basisRepCount
  exact Finset.card_le_card_of_injOn (repCode S)
    (fun _ hn => repCode_mem_codeSpace S hn) (repCode_injOn S N)

theorem codeSpace_card_le_digitalBound (N : ℕ) :
    (codeSpace S N).card ≤ digitalBound S N := by
  classical
  let U := (Finset.range (level S N + 1)).biUnion (codesAt S N)
  calc
    (codeSpace S N).card = 2 * U.card := by
      unfold codeSpace U
      simpa using Finset.card_product (Finset.univ : Finset Bool)
        ((Finset.range (level S N + 1)).biUnion (codesAt S N))
    _ ≤ 2 * ∑ l ∈ Finset.range (level S N + 1),
          S.base l * prefixRepCount S l N := by
      apply Nat.mul_le_mul_left 2
      refine Finset.card_biUnion_le.trans ?_
      apply Finset.sum_le_sum
      intro l hl
      calc
        (codesAt S N l).card ≤
            ((prefixPairs S l N).product (Finset.range (S.base l))).card :=
          Finset.card_image_le
        _ = prefixRepCount S l N * S.base l := by
          simp [prefixRepCount, Finset.card_product]
        _ = S.base l * prefixRepCount S l N := Nat.mul_comm _ _
    _ = digitalBound S N := rfl

/-- The ordered global convolution is controlled by the product of the local
prefix counts, with one unrestricted top digit and two orientations. -/
theorem basisRepCount_le_digitalBound (N : ℕ) :
    basisRepCount S N ≤ digitalBound S N :=
  (basisRepCount_le_codeSpace S N).trans (codeSpace_card_le_digitalBound S N)

/-- A convenient form for applications: once a separate local-to-prefix
argument gives `M^k`, the global count is bounded by the displayed sum. -/
theorem basisRepCount_le_of_prefix_bound (M N : ℕ)
    (hprefix : ∀ k r, prefixRepCount S k r ≤ M ^ k) :
    basisRepCount S N ≤
      2 * ∑ l ∈ Finset.range (level S N + 1), S.base l * M ^ l := by
  apply (basisRepCount_le_digitalBound S N).trans
  rw [digitalBound]
  gcongr with l hl
  exact hprefix l N

/-- Fully local version of the global counting theorem. -/
theorem basisRepCount_le_of_local_flat (M N : ℕ)
    (hflat : ∀ i r, (localPairs S i r).card ≤ M) :
    basisRepCount S N ≤
      2 * ∑ l ∈ Finset.range (level S N + 1), S.base l * M ^ l :=
  basisRepCount_le_of_prefix_bound S M N (prefixRepCount_le_pow S hflat)

/-- If bases up to the active level have a common upper bound, the sum in the
preceding theorem has the standard polynomial-times-exponential form. -/
theorem basisRepCount_le_uniform (M Q N : ℕ) (hM : 1 ≤ M)
    (hflat : ∀ i r, (localPairs S i r).card ≤ M)
    (hbase : ∀ i ≤ level S N, S.base i ≤ Q) :
    basisRepCount S N ≤
      2 * (level S N + 1) * Q * M ^ level S N := by
  apply (basisRepCount_le_of_local_flat S M N hflat).trans
  calc
    2 * ∑ l ∈ Finset.range (level S N + 1), S.base l * M ^ l ≤
        2 * ∑ _l ∈ Finset.range (level S N + 1),
          Q * M ^ level S N := by
      gcongr with l hl
      · exact hbase l (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
      · exact Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    _ = 2 * (level S N + 1) * Q * M ^ level S N := by
      simp [mul_assoc]

theorem tendsto_level : Filter.Tendsto (level S) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro k
  refine ⟨place S k, ?_⟩
  intro n hn
  apply Nat.le_findGreatest
  · exact (Nat.le_succ k).trans ((place_ge_succ S k).trans hn)
  · exact hn

end MixedRadix

end Erdos29
