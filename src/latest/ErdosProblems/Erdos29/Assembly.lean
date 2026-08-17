import ErdosProblems.Erdos29.Schedule
import ErdosProblems.Erdos29.Digital
import ErdosProblems.Erdos29.Analytic

/-!
# Assembly of the mixed-radix construction for Erdős Problem 29

This file is the interface between the three reusable parts of the proof.
The radices and their growth come from `Schedule`, the carry and counting
arguments come from `Digital`, and the final limiting argument comes from
`Analytic`.

The only data still left abstract are the finite permitted digit sets.  The
main theorem below assumes exactly the two properties supplied by the local
modular construction:

* exact coverage with an incoming and outgoing binary carry;
* a uniform bound on every ordered local sum fiber.
-/

namespace Erdos29

namespace Assembly

open Filter
open scoped Pointwise

/-- The actual number of ordered permitted digit pairs in a given residue
class.  This is the local convolution used in the assembly theorem. -/
def localRepCount (digits : ℕ → Finset ℕ) (i r : ℕ) : ℕ :=
  (((digits i).product (digits i)).filter fun xy ↦
    (xy.1 + xy.2) % radix i = r % radix i).card

/-- Install permitted digit sets in the explicit prime-square radix schedule.
The coverage hypothesis is the exact natural-representative form of modular
coverage; `LocalSystem.ofModular` performs the binary-carry bookkeeping. -/
def scheduleSystem (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    MixedRadix.LocalSystem :=
  MixedRadix.LocalSystem.ofModular radix digits
    (fun i ↦ by
      have h := one_hundred_twenty_one_le_radix i
      omega)
    hdigit hcover

/-- The recursive place function of the generic digital construction agrees
with the product place function of the explicit schedule. -/
theorem scheduleSystem_place (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    ∀ k, MixedRadix.place (scheduleSystem digits hdigit hcover) k = place k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [MixedRadix.place_succ, place_succ, ih]
      rfl

/-- The level selected by the scheduled mixed-radix system tends to infinity. -/
theorem scheduleSystem_level_tendsto (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    Tendsto (MixedRadix.level (scheduleSystem digits hdigit hcover)) atTop atTop :=
  MixedRadix.tendsto_level (scheduleSystem digits hdigit hcover)

/-- An integer dominates the superexponential scale associated with its
active scheduled level. -/
theorem scheduleSystem_eventually_superexponential
    (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r) :
    ∀ᶠ n in atTop,
      (MixedRadix.level (scheduleSystem digits hdigit hcover) n / 2) ^
          MixedRadix.level (scheduleSystem digits hdigit hcover) n ≤ n := by
  let S := scheduleSystem digits hdigit hcover
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := by omega
  let k := MixedRadix.level S n
  calc
    (k / 2) ^ k ≤ place k := half_pow_le_place k
    _ = MixedRadix.place S k := (scheduleSystem_place digits hdigit hcover k).symm
    _ ≤ n := MixedRadix.place_level_le S hnpos

/-- The explicit schedule turns a uniform local fiber bound into the concrete
global estimate `2304 * k^3 * M^k`. -/
theorem scheduleSystem_basisRepCount_le
    (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r)
    (M : ℕ) (hM : 1 ≤ M)
    (hflat : ∀ i r, localRepCount digits i r ≤ M)
    (N : ℕ) (hlevel : 1 ≤ MixedRadix.level (scheduleSystem digits hdigit hcover) N) :
    MixedRadix.basisRepCount (scheduleSystem digits hdigit hcover) N ≤
      2304 * MixedRadix.level (scheduleSystem digits hdigit hcover) N ^ 3 *
        M ^ MixedRadix.level (scheduleSystem digits hdigit hcover) N := by
  let S := scheduleSystem digits hdigit hcover
  let k := MixedRadix.level S N
  have hflatS : ∀ i r, (MixedRadix.localPairs S i r).card ≤ M := by
    intro i r
    change localRepCount digits i r ≤ M
    exact hflat i r
  have hbase : ∀ i ≤ MixedRadix.level S N,
      S.base i ≤ 4 * (MixedRadix.level S N + 11) ^ 2 := by
    intro i hi
    change radix i ≤ 4 * (MixedRadix.level S N + 11) ^ 2
    refine (radix_upper i).trans ?_
    gcongr
  have hglobal := MixedRadix.basisRepCount_le_uniform S M
    (4 * (MixedRadix.level S N + 11) ^ 2) N hM hflatS hbase
  have hkpos : 1 ≤ k := by
    simpa [k, S] using hlevel
  have hk1 : k + 1 ≤ 2 * k := by
    omega
  have hk11 : k + 11 ≤ 12 * k := by
    omega
  change MixedRadix.basisRepCount S N ≤ 2304 * k ^ 3 * M ^ k
  calc
    MixedRadix.basisRepCount S N ≤
        2 * (k + 1) * (4 * (k + 11) ^ 2) * M ^ k := by
      simpa [k] using hglobal
    _ ≤ 2 * (2 * k) * (4 * (12 * k) ^ 2) * M ^ k := by
      gcongr
    _ = 2304 * k ^ 3 * M ^ k := by ring

/-- Assemble any family of local digit sets satisfying exact binary-carry
coverage and a positive uniform ordered-fiber bound.

The conclusion simultaneously gives the exact additive-basis identity and
the ordered-antidiagonal little-o estimate required in Problem 29.  The local
construction used by the final file instantiates `M` with `144`.
-/
theorem assemble_schedule
    (digits : ℕ → Finset ℕ)
    (hdigit : ∀ i d, d ∈ digits i → d < radix i)
    (hcover : ∀ i r, r < radix i →
      ∃ x ∈ digits i, ∃ y ∈ digits i, (x + y) % radix i = r)
    (M : ℕ) (hM : 1 ≤ M)
    (hflat : ∀ i r, localRepCount digits i r ≤ M) :
    let S := scheduleSystem digits hdigit hcover
    MixedRadix.basis S + MixedRadix.basis S = Set.univ ∧
      ∀ ε : ℝ, 0 < ε →
        (fun n : ℕ ↦ (MixedRadix.basisRepCount S n : ℝ)) =o[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  dsimp only
  let S := scheduleSystem digits hdigit hcover
  constructor
  · exact MixedRadix.basis_add_basis S
  · intro ε hε
    have hlevel : Tendsto (MixedRadix.level S) atTop atTop :=
      MixedRadix.tendsto_level S
    apply Analytic.isLittleO_rpow_of_level_superexponential
      (fun n : ℕ ↦ (MixedRadix.basisRepCount S n : ℝ)) (MixedRadix.level S)
      3 2304 (M : ℝ) ε (by norm_num) (by exact_mod_cast hM) hε hlevel
      (by
        simpa [S] using
          scheduleSystem_eventually_superexponential digits hdigit hcover)
    filter_upwards [hlevel.eventually_ge_atTop (1 : ℕ)] with n hn
    have hNat := scheduleSystem_basisRepCount_le digits hdigit hcover
      M hM hflat n hn
    have hReal : (MixedRadix.basisRepCount S n : ℝ) ≤
        2304 * (MixedRadix.level S n : ℝ) ^ 3 *
          (M : ℝ) ^ MixedRadix.level S n := by
      exact_mod_cast hNat
    simpa [abs_of_nonneg] using hReal

end Assembly

end Erdos29
