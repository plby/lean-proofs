import ErdosProblems.Erdos888.Foundations
import ErdosProblems.Erdos888.LargestPrimes
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Bool

/-!
# Dyadic blocks and the core-coloured graph for Erdős problem 888

This file contains the finite, combinatorial part of the two-largest-prime
encoding.  The dyadic intervals use the convention `(2^i, 2^(i+1)]`; this is
the convention that makes adjacent blocks literally disjoint.  A generic
finite maximum-cut lemma supplies the bipartition needed when the two prime
scales agree.

The main arithmetic result is `coreGraph_no_double_rectangle`.  Its proof is
worth isolating: the four alternating edges of two alleged rectangles have a
square product.  Sorting them and applying `RequiredCondition` produces one
of the three possible pair-product equalities.  Cancellation then forces the
two cores, the two left endpoints, or the two right endpoints to coincide.
-/

open scoped BigOperators

namespace Erdos888

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Dyadic prime blocks -/

/-- The primes in the half-open dyadic interval `(2^i, 2^(i+1)]`. -/
def dyadicPrimeBlock (i : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 ^ i) (2 ^ (i + 1))).filter Nat.Prime

@[simp] theorem mem_dyadicPrimeBlock {i p : ℕ} :
    p ∈ dyadicPrimeBlock i ↔ Nat.Prime p ∧ 2 ^ i < p ∧ p ≤ 2 ^ (i + 1) := by
  simp only [dyadicPrimeBlock, Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem prime_of_mem_dyadicPrimeBlock {i p : ℕ}
    (hp : p ∈ dyadicPrimeBlock i) : Nat.Prime p :=
  (mem_dyadicPrimeBlock.1 hp).1

theorem lower_lt_of_mem_dyadicPrimeBlock {i p : ℕ}
    (hp : p ∈ dyadicPrimeBlock i) : 2 ^ i < p :=
  (mem_dyadicPrimeBlock.1 hp).2.1

theorem le_upper_of_mem_dyadicPrimeBlock {i p : ℕ}
    (hp : p ∈ dyadicPrimeBlock i) : p ≤ 2 ^ (i + 1) :=
  (mem_dyadicPrimeBlock.1 hp).2.2

/-- With the `(2^i,2^(i+1)]` convention, the correct block index is the
floor binary logarithm of `p - 1`. -/
def dyadicIndex (p : ℕ) : ℕ := Nat.log 2 (p - 1)

theorem prime_mem_dyadicPrimeBlock {p : ℕ} (hp : Nat.Prime p) :
    p ∈ dyadicPrimeBlock (dyadicIndex p) := by
  rw [mem_dyadicPrimeBlock]
  have hp2 : 2 ≤ p := hp.two_le
  have hpred : p - 1 ≠ 0 := by omega
  have hlo : 2 ^ Nat.log 2 (p - 1) ≤ p - 1 :=
    Nat.pow_log_le_self 2 hpred
  have hhi : p - 1 < 2 ^ (Nat.log 2 (p - 1) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
  change Nat.Prime p ∧ 2 ^ Nat.log 2 (p - 1) < p ∧
    p ≤ 2 ^ (Nat.log 2 (p - 1) + 1)
  exact ⟨hp, by omega, by omega⟩

theorem dyadicPrimeBlock_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicPrimeBlock i) (dyadicPrimeBlock j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi := (mem_dyadicPrimeBlock.1 hpi).2
  have hj := (mem_dyadicPrimeBlock.1 hpj).2
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpows : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hpows : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem dyadic_index_unique {p i : ℕ} (hp : p ∈ dyadicPrimeBlock i) :
    dyadicIndex p = i := by
  have hcanonical := prime_mem_dyadicPrimeBlock (prime_of_mem_dyadicPrimeBlock hp)
  by_contra hne
  exact (Finset.disjoint_left.1 (dyadicPrimeBlock_disjoint hne)) hcanonical hp

/-! ## A finite maximum-cut lemma

The edge objects below may carry arbitrary extra data (in the application,
their core/colour).  Only the two endpoint maps are used by the cut.  Thus
parallel endpoint-pairs with different colours are counted separately.
-/

universe u v

variable {V : Type u} {E : Type v}

/-- Edge objects crossing the Boolean bipartition `χ`. -/
def crossingItems [DecidableEq E] (edges : Finset E) (left right : E → V)
    (χ : V → Bool) : Finset E :=
  edges.filter fun e ↦ χ (left e) ≠ χ (right e)

@[simp] theorem mem_crossingItems [DecidableEq E] {edges : Finset E}
    {left right : E → V} {χ : V → Bool} {e : E} :
    e ∈ crossingItems edges left right χ ↔
      e ∈ edges ∧ χ (left e) ≠ χ (right e) := by
  simp [crossingItems]

/-- The zero-one indicator that an edge crosses a Boolean bipartition. -/
def crossingIndicator (left right : E → V) (χ : V → Bool) (e : E) : ℕ :=
  if χ (left e) ≠ χ (right e) then 1 else 0

theorem card_crossingItems [DecidableEq E] (edges : Finset E)
    (left right : E → V) (χ : V → Bool) :
    (crossingItems edges left right χ).card =
      ∑ e ∈ edges, crossingIndicator left right χ e := by
  simp [crossingItems, crossingIndicator, Finset.card_filter]

/-- Flip a single vertex of a Boolean bipartition. -/
def flipAt [DecidableEq V] (v : V) : Equiv.Perm (V → Bool) :=
  Equiv.piCongrRight fun w ↦ if w = v then Equiv.boolNot else Equiv.refl Bool

@[simp] theorem flipAt_apply [DecidableEq V] (v : V) (χ : V → Bool) (w : V) :
    flipAt v χ w = if w = v then !χ w else χ w := by
  by_cases hw : w = v <;> simp [flipAt, hw]

private theorem crossingIndicator_flip_add [DecidableEq V]
    (left right : E → V) (e : E) (hne : left e ≠ right e) (χ : V → Bool) :
    crossingIndicator left right (flipAt (left e) χ) e +
        crossingIndicator left right χ e = 1 := by
  cases hleft : χ (left e) <;> cases hright : χ (right e) <;>
    simp [crossingIndicator, flipAt_apply, hne.symm, hleft, hright]

private theorem twice_sum_crossingIndicator [Fintype V] [DecidableEq V]
    (left right : E → V) (e : E) (hne : left e ≠ right e) :
    2 * ∑ χ : V → Bool, crossingIndicator left right χ e =
      Fintype.card (V → Bool) := by
  calc
    2 * ∑ χ : V → Bool, crossingIndicator left right χ e =
        (∑ χ : V → Bool, crossingIndicator left right (flipAt (left e) χ) e) +
          ∑ χ : V → Bool, crossingIndicator left right χ e := by
            have hperm := Equiv.sum_comp (flipAt (left e))
              (fun χ : V → Bool ↦ crossingIndicator left right χ e)
            rw [hperm]
            omega
    _ = ∑ χ : V → Bool,
        (crossingIndicator left right (flipAt (left e) χ) e +
          crossingIndicator left right χ e) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ _χ : V → Bool, 1 := by
          apply Finset.sum_congr rfl
          intro χ _
          exact crossingIndicator_flip_add left right e hne χ
    _ = Fintype.card (V → Bool) := by simp

/-- Every finite loopless family of edges has a bipartition capturing at
least half of its edge objects.  In the equal-dyadic-scale application the
edge object includes the core, so this statement captures half of the sum
over all colours, not merely half of the distinct endpoint pairs. -/
theorem exists_bipartition_half_crossing [Fintype V] [DecidableEq V]
    [DecidableEq E] (edges : Finset E) (left right : E → V)
    (hloop : ∀ e ∈ edges, left e ≠ right e) :
    ∃ χ : V → Bool,
      edges.card ≤ 2 * (crossingItems edges left right χ).card := by
  classical
  by_contra h
  push Not at h
  have hsum :
      2 * ∑ χ : V → Bool, (crossingItems edges left right χ).card =
        Fintype.card (V → Bool) * edges.card := by
    simp_rw [card_crossingItems]
    calc
      2 * ∑ χ : V → Bool,
          ∑ e ∈ edges, crossingIndicator left right χ e =
          ∑ e ∈ edges,
            2 * ∑ χ : V → Bool, crossingIndicator left right χ e := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
      _ = ∑ _e ∈ edges, Fintype.card (V → Bool) := by
            apply Finset.sum_congr rfl
            intro e he
            exact twice_sum_crossingIndicator left right e (hloop e he)
      _ = Fintype.card (V → Bool) * edges.card := by
            simp [Nat.mul_comm]
  have hstrict :
      (∑ χ : V → Bool, 2 * (crossingItems edges left right χ).card) <
        ∑ _χ : V → Bool, edges.card := by
    refine Finset.sum_lt_sum (fun χ _ ↦ (h χ).le) ?_
    exact ⟨fun _ ↦ false, Finset.mem_univ _, h _⟩
  have heq :
      (∑ χ : V → Bool, 2 * (crossingItems edges left right χ).card) =
        ∑ _χ : V → Bool, edges.card := by
    calc
      (∑ χ : V → Bool, 2 * (crossingItems edges left right χ).card) =
          2 * ∑ χ : V → Bool, (crossingItems edges left right χ).card := by
            rw [Finset.mul_sum]
      _ = Fintype.card (V → Bool) * edges.card := hsum
      _ = ∑ _χ : V → Bool, edges.card := by simp
  exact hstrict.ne heq

/-! ## Core-coloured graphs -/

/-- A prime lies strictly above every prime divisor of a core. -/
def PrimeAboveCore (c p : ℕ) : Prop :=
  Nat.Prime p ∧ ∀ q, Nat.Prime q → q ∣ c → q < p

theorem PrimeAboveCore.prime {c p : ℕ} (h : PrimeAboveCore c p) : Nat.Prime p :=
  h.1

theorem PrimeAboveCore.not_dvd {c p : ℕ} (h : PrimeAboveCore c p) : ¬ p ∣ c := by
  intro hpc
  exact (Nat.lt_irrefl p) (h.2 p h.1 hpc)

/-- The edge of colour/core `c` between endpoint primes `u` and `v`.
The `PrimeAboveCore` clauses say precisely that the endpoints occur after
every prime already present in the core. -/
structure CoreGraph (A : Finset ℕ) (c u v : ℕ) : Prop where
  core_pos : 0 < c
  left_above : PrimeAboveCore c u
  right_above : PrimeAboveCore c v
  endpoint_ne : u ≠ v
  mem : c * u * v ∈ A

theorem CoreGraph.left_prime {A : Finset ℕ} {c u v : ℕ}
    (h : CoreGraph A c u v) : Nat.Prime u :=
  h.left_above.prime

theorem CoreGraph.right_prime {A : Finset ℕ} {c u v : ℕ}
    (h : CoreGraph A c u v) : Nat.Prime v :=
  h.right_above.prime

/-- The finite edge set of one core graph on specified endpoint finsets. -/
def coreEdges (A : Finset ℕ) (c : ℕ) (L R : Finset ℕ) : Finset (ℕ × ℕ) :=
  (L.product R).filter fun e ↦ CoreGraph A c e.1 e.2

@[simp] theorem mem_coreEdges {A : Finset ℕ} {c : ℕ} {L R : Finset ℕ}
    {u v : ℕ} :
    (u, v) ∈ coreEdges A c L R ↔ u ∈ L ∧ v ∈ R ∧ CoreGraph A c u v := by
  simp [coreEdges, and_assoc]

/-- A (labelled) complete `2 × 2` rectangle in a bipartite relation. -/
structure CompleteRectangle (G : ℕ → ℕ → Prop) (p q r s : ℕ) : Prop where
  left_ne : p ≠ q
  right_ne : r ≠ s
  nw : G p r
  ne : G p s
  sw : G q r
  se : G q s

/-- Two ordered pairs represent the same unordered pair. -/
private def SamePair {α : Type*} (a b c d : α) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The first two and last two entries give the same partition into two
unordered pairs as the four entries on the right. -/
private def SamePartition {α : Type*} (a b c d w x y z : α) : Prop :=
  (SamePair a b w x ∧ SamePair c d y z) ∨
  (SamePair a b y z ∧ SamePair c d w x)

private theorem finFour_pairing (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    SamePartition a b c d 0 1 2 3 ∨
    SamePartition a b c d 0 2 1 3 ∨
    SamePartition a b c d 0 3 1 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all [SamePartition, SamePair]

private theorem pairing_of_perm (f : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4))
    (h : f (σ 0) * f (σ 3) = f (σ 1) * f (σ 2)) :
    f 0 * f 1 = f 2 * f 3 ∨
    f 0 * f 2 = f 1 * f 3 ∨
    f 0 * f 3 = f 1 * f 2 := by
  have hne {i j : Fin 4} (hij : i ≠ j) : σ i ≠ σ j :=
    fun hs ↦ hij (σ.injective hs)
  rcases finFour_pairing (σ 0) (σ 3) (σ 1) (σ 2)
      (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) with hp | hp | hp
  · left
    simp [SamePartition, SamePair] at hp
    rcases hp with hp | hp <;> rcases hp with ⟨hp, hq⟩ <;>
      rcases hp with hp | hp <;> rcases hq with hq | hq <;>
      rcases hp with ⟨hp₁, hp₂⟩ <;> rcases hq with ⟨hq₁, hq₂⟩ <;>
      simp_all [Nat.mul_comm]
  · right; left
    simp [SamePartition, SamePair] at hp
    rcases hp with hp | hp <;> rcases hp with ⟨hp, hq⟩ <;>
      rcases hp with hp | hp <;> rcases hq with hq | hq <;>
      rcases hp with ⟨hp₁, hp₂⟩ <;> rcases hq with ⟨hq₁, hq₂⟩ <;>
      simp_all [Nat.mul_comm]
  · right; right
    simp [SamePartition, SamePair] at hp
    rcases hp with hp | hp <;> rcases hp with ⟨hp, hq⟩ <;>
      rcases hp with hp | hp <;> rcases hq with hq | hq <;>
      rcases hp with ⟨hp₁, hp₂⟩ <;> rcases hq with ⟨hq₁, hq₂⟩ <;>
      simp_all [Nat.mul_comm]

/-- The sorted consequence of `RequiredCondition`, in a form independent of
which of the four inputs is smallest. -/
theorem requiredCondition_pairing {A : Finset ℕ} {n a b c d : ℕ}
    (hA : RequiredCondition A n)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsq : IsSquare (a * b * c * d)) :
    a * b = c * d ∨ a * c = b * d ∨ a * d = b * c := by
  let f : Fin 4 → ℕ := ![a, b, c, d]
  let σ : Equiv.Perm (Fin 4) := Tuple.sort f
  have hmem (i : Fin 4) : f i ∈ A := by
    fin_cases i <;> simp [f, ha, hb, hc, hd]
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have h01 : f (σ 0) ≤ f (σ 1) := hmono (by decide)
  have h12 : f (σ 1) ≤ f (σ 2) := hmono (by decide)
  have h23 : f (σ 2) ≤ f (σ 3) := hmono (by decide)
  have hprod : f (σ 0) * f (σ 1) * f (σ 2) * f (σ 3) = a * b * c * d := by
    have hp := Equiv.prod_comp σ f
    calc
      f (σ 0) * f (σ 1) * f (σ 2) * f (σ 3) = ∏ i, f (σ i) := by
        norm_num [Fin.prod_univ_succ]
        rw [show Fin.succ (2 : Fin 3) = (3 : Fin 4) by rfl]
        ring
      _ = ∏ i, f i := hp
      _ = a * b * c * d := by
        norm_num [f, Fin.prod_univ_succ]
        ring
  have hsq' : IsSquare (f (σ 0) * f (σ 1) * f (σ 2) * f (σ 3)) := by
    rw [hprod]
    exact hsq
  have heq := hA.2 (f (σ 0)) (hmem _) (f (σ 1)) (hmem _)
    (f (σ 2)) (hmem _) (f (σ 3)) (hmem _) h01 h12 h23 hsq'
  simpa [f] using pairing_of_perm f σ heq

/-- A rectangle cannot occur in two distinct core colours. -/
theorem coreGraph_no_double_rectangle {A : Finset ℕ} {n c d p q r s : ℕ}
    (hA : RequiredCondition A n)
    (hc : CompleteRectangle (CoreGraph A c) p q r s)
    (hd : CompleteRectangle (CoreGraph A d) p q r s) :
    c = d := by
  let x₁ := c * p * r
  let x₂ := c * q * s
  let x₃ := d * p * s
  let x₄ := d * q * r
  have hx₁ : x₁ ∈ A := hc.nw.mem
  have hx₂ : x₂ ∈ A := hc.se.mem
  have hx₃ : x₃ ∈ A := hd.ne.mem
  have hx₄ : x₄ ∈ A := hd.sw.mem
  have hsq : IsSquare (x₁ * x₂ * x₃ * x₄) := by
    refine ⟨c * d * p * q * r * s, ?_⟩
    dsimp [x₁, x₂, x₃, x₄]
    ring
  rcases requiredCondition_pairing hA hx₁ hx₂ hx₃ hx₄ hsq with h | h | h
  · have hnorm : c ^ 2 * (p * q * r * s) = d ^ 2 * (p * q * r * s) := by
      dsimp [x₁, x₂, x₃, x₄] at h
      calc
        c ^ 2 * (p * q * r * s) = (c * p * r) * (c * q * s) := by ring
        _ = (d * p * s) * (d * q * r) := h
        _ = d ^ 2 * (p * q * r * s) := by ring
    have hcommon : 0 < p * q * r * s := by
      exact mul_pos (mul_pos (mul_pos hc.nw.left_prime.pos hc.se.left_prime.pos)
        hc.nw.right_prime.pos) hc.se.right_prime.pos
    exact Nat.pow_left_injective (by decide) (Nat.mul_right_cancel hcommon hnorm)
  · have hnorm : p ^ 2 * (c * d * r * s) = q ^ 2 * (c * d * r * s) := by
      dsimp [x₁, x₂, x₃, x₄] at h
      calc
        p ^ 2 * (c * d * r * s) = (c * p * r) * (d * p * s) := by ring
        _ = (c * q * s) * (d * q * r) := h
        _ = q ^ 2 * (c * d * r * s) := by ring
    have hcommon : 0 < c * d * r * s := by
      exact mul_pos (mul_pos (mul_pos hc.nw.core_pos hd.nw.core_pos)
        hc.nw.right_prime.pos) hc.ne.right_prime.pos
    exact (hc.left_ne (Nat.pow_left_injective (by decide)
      (Nat.mul_right_cancel hcommon hnorm))).elim
  · have hnorm : r ^ 2 * (c * d * p * q) = s ^ 2 * (c * d * p * q) := by
      dsimp [x₁, x₂, x₃, x₄] at h
      calc
        r ^ 2 * (c * d * p * q) = (c * p * r) * (d * q * r) := by ring
        _ = (c * q * s) * (d * p * s) := h
        _ = s ^ 2 * (c * d * p * q) := by ring
    have hcommon : 0 < c * d * p * q := by
      exact mul_pos (mul_pos (mul_pos hc.nw.core_pos hd.nw.core_pos)
        hc.nw.left_prime.pos) hc.sw.left_prime.pos
    exact (hc.right_ne (Nat.pow_left_injective (by decide)
      (Nat.mul_right_cancel hcommon hnorm))).elim

/-- Negated form of `coreGraph_no_double_rectangle`, convenient for the
coloured graph estimate. -/
theorem no_double_rectangle {A : Finset ℕ} {n c d p q r s : ℕ}
    (hA : RequiredCondition A n) (hcd : c ≠ d) :
    ¬ (CompleteRectangle (CoreGraph A c) p q r s ∧
      CompleteRectangle (CoreGraph A d) p q r s) := by
  rintro ⟨hc, hd⟩
  exact hcd (coreGraph_no_double_rectangle hA hc hd)

/-! ## Canonical finite covering by dyadic core edges

The analytic argument needs a genuinely finite partition, not merely the
existence of a decomposition for each integer.  We choose the unique
two-largest-prime coordinates, store their dyadic indices in an edge object,
and partition those objects by the finite key `(i,j,c)`.
-/

/-- Members of `A` having at least two distinct prime factors. -/
def nonexceptionalElements (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a ↦ 2 ≤ a.primeFactors.card

@[simp] theorem mem_nonexceptionalElements {A : Finset ℕ} {a : ℕ} :
    a ∈ nonexceptionalElements A ↔ a ∈ A ∧ 2 ≤ a.primeFactors.card := by
  simp [nonexceptionalElements]

/-- The core and ordered pair of largest prime factors. -/
structure PrimeCoordinates where
  core : ℕ
  left : ℕ
  right : ℕ
deriving DecidableEq

/-- A total choice of two-largest-prime coordinates.  On exceptional inputs
it is the harmless zero triple; `chosenPrimeCoordinates_spec` is the API used
on nonexceptional squarefree positive inputs. -/
noncomputable def chosenPrimeCoordinates (a : ℕ) : PrimeCoordinates :=
  if h : ∃ x : PrimeCoordinates,
      TwoLargestPrimeDecomposition a x.core x.left x.right then
    Classical.choose h
  else ⟨0, 0, 0⟩

theorem chosenPrimeCoordinates_spec {a : ℕ} (ha : 0 < a)
    (hsf : Squarefree a) (hcard : 2 ≤ a.primeFactors.card) :
    TwoLargestPrimeDecomposition a (chosenPrimeCoordinates a).core
      (chosenPrimeCoordinates a).left (chosenPrimeCoordinates a).right := by
  obtain ⟨c, p, q, hcpq⟩ := exists_twoLargestPrimeDecomposition ha hsf hcard
  have hex : ∃ x : PrimeCoordinates,
      TwoLargestPrimeDecomposition a x.core x.left x.right :=
    ⟨⟨c, p, q⟩, hcpq⟩
  rw [chosenPrimeCoordinates, dif_pos hex]
  exact Classical.choose_spec hex

/-- A valid two-largest-prime decomposition is an edge in the core-coloured
graph as soon as its represented integer is a positive member of `A`. -/
theorem TwoLargestPrimeDecomposition.coreGraph {A : Finset ℕ}
    {a c p q : ℕ} (h : TwoLargestPrimeDecomposition a c p q)
    (ha : a ∈ A) (hapos : 0 < a) : CoreGraph A c p q := by
  rcases h with ⟨hdecomp, hp, hq, hpq, _hcSquarefree, hsmall⟩
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    simp [hc0] at hdecomp
    omega
  refine ⟨hcpos, ⟨hp, ?_⟩, ⟨hq, ?_⟩, hpq.ne, ?_⟩
  · intro r hrprime hrc
    exact hsmall r (Nat.mem_primeFactors.mpr ⟨hrprime, hrc, hcpos.ne'⟩)
  · intro r hrprime hrc
    exact (hsmall r (Nat.mem_primeFactors.mpr
      ⟨hrprime, hrc, hcpos.ne'⟩)).trans hpq
  · simpa [hdecomp] using ha

/-- A canonical edge remembers its endpoints, core, and both dyadic scales. -/
structure DyadicCoreEdge where
  leftScale : ℕ
  rightScale : ℕ
  core : ℕ
  left : ℕ
  right : ℕ
deriving DecidableEq

/-- Encode an integer by its chosen core and two largest prime factors. -/
noncomputable def encodeDyadicCoreEdge (a : ℕ) : DyadicCoreEdge :=
  let x := chosenPrimeCoordinates a
  ⟨dyadicIndex x.left, dyadicIndex x.right, x.core, x.left, x.right⟩

/-- The finite set of canonical dyadic/core edge objects belonging to `A`. -/
noncomputable def encodedDyadicCoreEdges (A : Finset ℕ) : Finset DyadicCoreEdge :=
  (nonexceptionalElements A).image encodeDyadicCoreEdge

/-- The finite key of a dyadic/core edge. -/
def dyadicCoreEdgeKey (e : DyadicCoreEdge) : ℕ × (ℕ × ℕ) :=
  (e.leftScale, (e.rightScale, e.core))

/-- The canonical edges in the block with left scale `i`, right scale `j`,
and core/colour `c`. -/
noncomputable def dyadicBlockCoreEdges (A : Finset ℕ) (i j c : ℕ) :
    Finset DyadicCoreEdge :=
  (encodedDyadicCoreEdges A).filter fun e ↦ dyadicCoreEdgeKey e = (i, (j, c))

@[simp] theorem mem_dyadicBlockCoreEdges {A : Finset ℕ} {i j c : ℕ}
    {e : DyadicCoreEdge} :
    e ∈ dyadicBlockCoreEdges A i j c ↔
      e ∈ encodedDyadicCoreEdges A ∧
        e.leftScale = i ∧ e.rightScale = j ∧ e.core = c := by
  simp [dyadicBlockCoreEdges, dyadicCoreEdgeKey]

/-- Explicit finite ranges for all block keys arising from a set in
`{1,…,n}`. -/
def finiteDyadicCoreKeys (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range (n + 1)).product
    ((Finset.range (n + 1)).product (Finset.Icc 1 n))

@[simp] theorem mem_finiteDyadicCoreKeys {n i j c : ℕ} :
    (i, (j, c)) ∈ finiteDyadicCoreKeys n ↔ i ≤ n ∧ j ≤ n ∧ 1 ≤ c ∧ c ≤ n := by
  simp [finiteDyadicCoreKeys]

private theorem coordinate_bounds {A : Finset ℕ} {n a : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) (ha : a ∈ A)
    (hdec : TwoLargestPrimeDecomposition a (chosenPrimeCoordinates a).core
      (chosenPrimeCoordinates a).left (chosenPrimeCoordinates a).right) :
    dyadicCoreEdgeKey (encodeDyadicCoreEdge a) ∈ finiteDyadicCoreKeys n := by
  let x := chosenPrimeCoordinates a
  have haIoc := Finset.mem_Ioc.mp (hA ha)
  have hp_dvd : x.left ∣ a := by
    refine ⟨x.core * x.right, ?_⟩
    rw [hdec.1]
    ring
  have hq_dvd : x.right ∣ a := by
    refine ⟨x.core * x.left, ?_⟩
    rw [hdec.1]
    ring
  have hc_dvd : x.core ∣ a := by
    exact ⟨x.left * x.right, by simpa [mul_assoc] using hdec.1⟩
  have hp_le : x.left ≤ n := (Nat.le_of_dvd haIoc.1 hp_dvd).trans haIoc.2
  have hq_le : x.right ≤ n := (Nat.le_of_dvd haIoc.1 hq_dvd).trans haIoc.2
  have hc_le : x.core ≤ n := (Nat.le_of_dvd haIoc.1 hc_dvd).trans haIoc.2
  have hcpos : 0 < x.core := by
    by_contra hc
    have hc0 : x.core = 0 := Nat.eq_zero_of_not_pos hc
    have hdecomp : a = x.core * x.left * x.right := hdec.1
    rw [hc0] at hdecomp
    simp at hdecomp
    omega
  rw [mem_finiteDyadicCoreKeys]
  change dyadicIndex x.left ≤ n ∧ dyadicIndex x.right ≤ n ∧ 1 ≤ x.core ∧ x.core ≤ n
  exact ⟨(Nat.log_le_self 2 (x.left - 1)).trans
      ((Nat.sub_le x.left 1).trans hp_le),
    (Nat.log_le_self 2 (x.right - 1)).trans
      ((Nat.sub_le x.right 1).trans hq_le), hcpos, hc_le⟩

/-- Every canonical encoded edge has the advertised dyadic endpoints and is
an edge of its core colour. -/
theorem encodedDyadicCoreEdge_spec {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (hsf : ∀ a ∈ A, Squarefree a)
    {e : DyadicCoreEdge} (he : e ∈ encodedDyadicCoreEdges A) :
    e.left ∈ dyadicPrimeBlock e.leftScale ∧
      e.right ∈ dyadicPrimeBlock e.rightScale ∧
      CoreGraph A e.core e.left e.right := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have ha' := mem_nonexceptionalElements.mp ha
  have haIoc := Finset.mem_Ioc.mp (hA.1 ha'.1)
  let x := chosenPrimeCoordinates a
  have hdec : TwoLargestPrimeDecomposition a x.core x.left x.right :=
    chosenPrimeCoordinates_spec haIoc.1 (hsf a ha'.1) ha'.2
  change x.left ∈ dyadicPrimeBlock (dyadicIndex x.left) ∧
    x.right ∈ dyadicPrimeBlock (dyadicIndex x.right) ∧
      CoreGraph A x.core x.left x.right
  exact ⟨prime_mem_dyadicPrimeBlock hdec.2.1,
    prime_mem_dyadicPrimeBlock hdec.2.2.1,
    hdec.coreGraph ha'.1 haIoc.1⟩

private theorem encodeDyadicCoreEdge_injOn {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (hsf : ∀ a ∈ A, Squarefree a) :
    Set.InjOn encodeDyadicCoreEdge (nonexceptionalElements A) := by
  intro a ha b hb hab
  have ha' := mem_nonexceptionalElements.mp ha
  have hb' := mem_nonexceptionalElements.mp hb
  have haIoc := Finset.mem_Ioc.mp (hA.1 ha'.1)
  have hbIoc := Finset.mem_Ioc.mp (hA.1 hb'.1)
  let x := chosenPrimeCoordinates a
  let y := chosenPrimeCoordinates b
  have hda : TwoLargestPrimeDecomposition a x.core x.left x.right :=
    chosenPrimeCoordinates_spec haIoc.1 (hsf a ha'.1) ha'.2
  have hdb : TwoLargestPrimeDecomposition b y.core y.left y.right :=
    chosenPrimeCoordinates_spec hbIoc.1 (hsf b hb'.1) hb'.2
  have hc : x.core = y.core := congrArg DyadicCoreEdge.core hab
  have hp : x.left = y.left := congrArg DyadicCoreEdge.left hab
  have hq : x.right = y.right := congrArg DyadicCoreEdge.right hab
  rw [hda.1, hdb.1, hc, hp, hq]

/-- Encoding loses no elements: every nonexceptional squarefree member is
counted exactly once as a canonical edge object. -/
theorem card_encodedDyadicCoreEdges {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (hsf : ∀ a ∈ A, Squarefree a) :
    (encodedDyadicCoreEdges A).card = (nonexceptionalElements A).card := by
  classical
  exact Finset.card_image_iff.mpr (encodeDyadicCoreEdge_injOn hA hsf)

/-- Within a fixed dyadic/core block, forgetting the bookkeeping fields is
an injection into the corresponding core graph's ordinary endpoint edges. -/
theorem card_dyadicBlockCoreEdges_le_coreEdges
    {A : Finset ℕ} {n i j c : ℕ} (hA : RequiredCondition A n)
    (hsf : ∀ a ∈ A, Squarefree a) :
    (dyadicBlockCoreEdges A i j c).card ≤
      (coreEdges A c (dyadicPrimeBlock i) (dyadicPrimeBlock j)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun e : DyadicCoreEdge ↦ (e.left, e.right)) ?_ ?_
  · intro e he
    have he' := mem_dyadicBlockCoreEdges.mp he
    have hs := encodedDyadicCoreEdge_spec hA hsf he'.1
    rw [he'.2.1, he'.2.2.1, he'.2.2.2] at hs
    exact mem_coreEdges.mpr ⟨hs.1, hs.2.1, hs.2.2⟩
  · intro e he f hf hef
    have he' := (mem_dyadicBlockCoreEdges.mp he).2
    have hf' := (mem_dyadicBlockCoreEdges.mp hf).2
    cases e
    cases f
    simp_all only [Prod.mk.injEq]

/-- Exact finite block cover.  All ranges are explicit: `0 ≤ i,j ≤ n` and
`1 ≤ c ≤ n`.  Thus every nonexceptional squarefree admissible member is
counted once, in its unique dyadic/core block. -/
theorem card_nonexceptional_eq_sum_dyadicBlockCoreEdges
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : ∀ a ∈ A, Squarefree a) :
    (nonexceptionalElements A).card =
      ∑ k ∈ finiteDyadicCoreKeys n,
        (dyadicBlockCoreEdges A k.1 k.2.1 k.2.2).card := by
  classical
  rw [← card_encodedDyadicCoreEdges hA hsf]
  simpa [dyadicBlockCoreEdges] using
    (Finset.card_eq_sum_card_fiberwise
      (s := encodedDyadicCoreEdges A) (t := finiteDyadicCoreKeys n)
      (f := dyadicCoreEdgeKey) (fun e he ↦ by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
        have ha' := mem_nonexceptionalElements.mp ha
        have haIoc := Finset.mem_Ioc.mp (hA.1 ha'.1)
        have hdec := chosenPrimeCoordinates_spec haIoc.1
          (hsf a ha'.1) ha'.2
        exact coordinate_bounds hA.1 ha'.1 hdec))

/-- The covering inequality in the form consumed by graph estimates: replace
each canonical block by the (possibly larger) full core graph on its two
dyadic prime classes. -/
theorem card_nonexceptional_le_sum_coreEdges
    {A : Finset ℕ} {n : ℕ} (hA : RequiredCondition A n)
    (hsf : ∀ a ∈ A, Squarefree a) :
    (nonexceptionalElements A).card ≤
      ∑ k ∈ finiteDyadicCoreKeys n,
        (coreEdges A k.2.2 (dyadicPrimeBlock k.1)
          (dyadicPrimeBlock k.2.1)).card := by
  rw [card_nonexceptional_eq_sum_dyadicBlockCoreEdges hA hsf]
  exact Finset.sum_le_sum fun k _ ↦
    card_dyadicBlockCoreEdges_le_coreEdges hA hsf

end

end Erdos888
