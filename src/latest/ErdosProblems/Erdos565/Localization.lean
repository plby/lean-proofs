import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.Events
import ErdosProblems.Erdos565.Janson
import ErdosProblems.Erdos565.Numeric
import ErdosProblems.Erdos565.Rounding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Rounded localization for Erdős problem 565

This file contains the finite double-counting argument used to pass from
Janson witnesses on many `sampleThreshold r N`-subsets to one witness on the
whole vertex set.  The integer threshold is the ceiling division
`N ⌈/⌉ r ^ 34`; no divisibility convention is used.

The main algebraic lemma, `Lambda_summedLocalWeight_le`, is deliberately
stated for an arbitrary family of vertex sets.  Its only combinatorial input
is a uniform upper bound for the number of members containing a fixed set of
at least two vertices.  The later lemmas supply that bound for a family of
equal-sized subsets and record the exact coefficient
`2 ^ 11 / r ^ 16` occurring in the induced-Ramsey proof.
-/

open scoped BigOperators NNReal

namespace Erdos565
namespace Localization

open Hypergraph
open Events

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Members of a family which contain the fixed set `L`. -/
def containmentFiber (family : Finset (Finset V)) (L : Finset V) :
    Finset (Finset V) :=
  family.filter (L ⊆ ·)

@[simp] lemma mem_containmentFiber {family : Finset (Finset V)} {L S : Finset V} :
    S ∈ containmentFiber family L ↔ S ∈ family ∧ L ⊆ S := by
  simp [containmentFiber]

/-- Extend each local weight by zero and add the resulting weights. -/
noncomputable def summedLocalWeight (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S)) : EdgeWeight H :=
  fun E ↦ ∑ S ∈ family, zeroExtend (H.restrict_subset S) (mu S) E

lemma mass_summedLocalWeight (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S)) :
    H.mass (summedLocalWeight H family mu) =
      ∑ S ∈ family, (H.restrict S).mass (mu S) := by
  simp only [mass, summedLocalWeight, NNReal.coe_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  exact mass_zeroExtend (H.restrict_subset S) (mu S)

/-- Summing local witnesses normalized to mass one gives total mass equal to
the number of local vertex sets. -/
lemma mass_summedLocalWeight_of_normalized (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S))
    (hmass : ∀ S ∈ family, (H.restrict S).mass (mu S) = 1) :
    H.mass (summedLocalWeight H family mu) = family.card := by
  rw [mass_summedLocalWeight]
  calc
    ∑ S ∈ family, (H.restrict S).mass (mu S) =
        ∑ _S ∈ family, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hmass S hS
    _ = family.card := by simp

lemma weightedDegree_summedLocalWeight (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S)) (L : Finset V) :
    H.weightedDegree (summedLocalWeight H family mu) L =
      ∑ S ∈ family, (H.restrict S).weightedDegree (mu S) L := by
  simp only [weightedDegree, summedLocalWeight, NNReal.coe_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  exact weightedDegree_zeroExtend (H.restrict_subset S) (mu S) L

/-- A local weighted degree vanishes unless the local vertex set contains
`L`.  This is what changes the Cauchy--Schwarz cardinal factor from the size
of the whole family to the size of `containmentFiber family L`. -/
lemma weightedDegree_restrict_eq_zero_of_not_subset (H : Hypergraph V)
    (S L : Finset V) (mu : EdgeWeight (H.restrict S)) (hLS : ¬ L ⊆ S) :
    (H.restrict S).weightedDegree mu L = 0 := by
  simp only [weightedDegree]
  apply Finset.sum_eq_zero
  intro E hE
  have hES : E ⊆ S := (Hypergraph.mem_restrict.mp (Finset.mem_filter.mp hE).1).2
  exact False.elim (hLS ((Finset.mem_filter.mp hE).2.trans hES))

lemma weightedDegree_summedLocalWeight_eq_fiber (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S)) (L : Finset V) :
    H.weightedDegree (summedLocalWeight H family mu) L =
      ∑ S ∈ containmentFiber family L,
        (H.restrict S).weightedDegree (mu S) L := by
  rw [weightedDegree_summedLocalWeight]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro S hSfamily hSnot
  rw [weightedDegree_restrict_eq_zero_of_not_subset]
  simpa [containmentFiber, hSfamily] using hSnot

/-- Cauchy--Schwarz for the weighted degree of the summed local weight. -/
lemma sq_weightedDegree_summedLocalWeight_le (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S)) (L : Finset V) :
    H.weightedDegree (summedLocalWeight H family mu) L ^ 2 ≤
      ((containmentFiber family L).card : ℝ) *
        ∑ S ∈ containmentFiber family L,
          (H.restrict S).weightedDegree (mu S) L ^ 2 := by
  rw [weightedDegree_summedLocalWeight_eq_fiber]
  exact FiniteAnalysis.sq_sum_le_card_mul_sum_sq _ _

/-- The abstract localization inequality.  If no set of size at least two is
contained in more than `K` local vertex sets, the Janson energy of the sum is
at most `K` times the sum of the local energies. -/
theorem Lambda_summedLocalWeight_le (H : Hypergraph V)
    (family : Finset (Finset V))
    (mu : (S : Finset V) → EdgeWeight (H.restrict S))
    {p : ℝ} (hp : 0 < p) {K : ℕ}
    (hK : ∀ L : Finset V, 2 ≤ L.card → (containmentFiber family L).card ≤ K) :
    H.Lambda p (summedLocalWeight H family mu) ≤
      (K : ℝ) * ∑ S ∈ family, (H.restrict S).Lambda p (mu S) := by
  rw [Lambda]
  calc
    ∑ L ∈ jansonSets,
        H.weightedDegree (summedLocalWeight H family mu) L ^ 2 / p ^ L.card
        ≤ ∑ L ∈ jansonSets,
            (K : ℝ) *
              (∑ S ∈ family, (H.restrict S).weightedDegree (mu S) L ^ 2) /
                p ^ L.card := by
          apply Finset.sum_le_sum
          intro L hL
          have hLcard : 2 ≤ L.card := (Finset.mem_filter.mp hL).2
          have hfiber := sq_weightedDegree_summedLocalWeight_le H family mu L
          have hcard : ((containmentFiber family L).card : ℝ) ≤ K := by
            exact_mod_cast hK L hLcard
          have hsum_nonneg :
              0 ≤ ∑ S ∈ containmentFiber family L,
                (H.restrict S).weightedDegree (mu S) L ^ 2 :=
            Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
          have hfiber' :
              H.weightedDegree (summedLocalWeight H family mu) L ^ 2 ≤
                (K : ℝ) *
                  ∑ S ∈ containmentFiber family L,
                    (H.restrict S).weightedDegree (mu S) L ^ 2 :=
            hfiber.trans (mul_le_mul_of_nonneg_right hcard hsum_nonneg)
          have hsubset : containmentFiber family L ⊆ family := Finset.filter_subset _ _
          have hsum :
              ∑ S ∈ containmentFiber family L,
                  (H.restrict S).weightedDegree (mu S) L ^ 2 ≤
                ∑ S ∈ family,
                  (H.restrict S).weightedDegree (mu S) L ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun _ _ _ ↦ sq_nonneg _)
          have hnum := hfiber'.trans
            (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg K))
          exact div_le_div_of_nonneg_right hnum (pow_nonneg hp.le _)
    _ = (K : ℝ) * ∑ S ∈ family, (H.restrict S).Lambda p (mu S) := by
      simp only [Lambda]
      calc
        ∑ L ∈ jansonSets,
              (K : ℝ) *
                (∑ S ∈ family, (H.restrict S).weightedDegree (mu S) L ^ 2) /
                  p ^ L.card =
            ∑ L ∈ jansonSets, ∑ S ∈ family,
              (K : ℝ) * (H.restrict S).weightedDegree (mu S) L ^ 2 /
                p ^ L.card := by
                  apply Finset.sum_congr rfl
                  intro L hL
                  rw [Finset.mul_sum]
                  rw [Finset.sum_div]
        _ = ∑ S ∈ family, ∑ L ∈ jansonSets,
              (K : ℝ) * (H.restrict S).weightedDegree (mu S) L ^ 2 /
                p ^ L.card := by rw [Finset.sum_comm]
        _ = (K : ℝ) * ∑ S ∈ family,
              ∑ L ∈ jansonSets,
                (H.restrict S).weightedDegree (mu S) L ^ 2 / p ^ L.card := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro S hS
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro L hL
                  ring

/-! ## Counting equal-sized local vertex sets -/

/-- A family of `s`-subsets contains a fixed set `L` of size at least two in
at most `choose (N - 2) (s - 2)` members. -/
theorem card_containmentFiber_le_choose_two {s : ℕ}
    (family : Finset (Finset V))
    (hfamily : family ⊆ (Finset.univ : Finset V).powersetCard s)
    (L : Finset V) (hL : 2 ≤ L.card) :
    (containmentFiber family L).card ≤ (Fintype.card V - 2).choose (s - 2) := by
  by_cases hfiber : containmentFiber family L = ∅
  · simp [hfiber]
  obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mpr hfiber
  have hLS : L ⊆ S := (mem_containmentFiber.mp hS).2
  have hScard : S.card = s :=
    (Finset.mem_powersetCard.mp (hfamily (mem_containmentFiber.mp hS).1)).2
  obtain ⟨K, hKpowerset⟩ := (L.powersetCard_nonempty.mpr hL)
  have hKcard : K.card = 2 := (Finset.mem_powersetCard.mp hKpowerset).2
  have hKL : K ⊆ L := (Finset.mem_powersetCard.mp hKpowerset).1
  have hKs : K.card ≤ s := by
    calc
      K.card ≤ S.card := Finset.card_le_card (hKL.trans hLS)
      _ = s := hScard
  have hsub : containmentFiber family L ⊆
      ((Finset.univ : Finset V).powersetCard s).filter (K ⊆ ·) := by
    intro T hT
    exact Finset.mem_filter.mpr ⟨hfamily (mem_containmentFiber.mp hT).1,
      hKL.trans (mem_containmentFiber.mp hT).2⟩
  calc
    (containmentFiber family L).card ≤
        (((Finset.univ : Finset V).powersetCard s).filter (K ⊆ ·)).card :=
      Finset.card_le_card hsub
    _ = (Fintype.card V - 2).choose (s - 2) := by
      rw [Finset.card_filter_powersetCard_subset K Finset.univ s
        (Finset.subset_univ K) hKs]
      simp [hKcard]

/-- Equal-sized local sets give the concrete binomial factor in the energy
bound. -/
theorem Lambda_summedLocalWeight_le_choose_two {s : ℕ}
    (H : Hypergraph V) (family : Finset (Finset V))
    (hfamily : family ⊆ (Finset.univ : Finset V).powersetCard s)
    (mu : (S : Finset V) → EdgeWeight (H.restrict S))
    {p : ℝ} (hp : 0 < p) :
    H.Lambda p (summedLocalWeight H family mu) ≤
      ((Fintype.card V - 2).choose (s - 2) : ℝ) *
        ∑ S ∈ family, (H.restrict S).Lambda p (mu S) := by
  apply Lambda_summedLocalWeight_le H family mu hp
  intro L hL
  exact card_containmentFiber_le_choose_two family hfamily L hL

/-- If every normalized local witness has energy strictly below `B`, their
sum has energy strictly below the containment count times `|family| B`.
The nonemptiness hypothesis is needed only to retain the strict inequality. -/
theorem Lambda_summedLocalWeight_lt_choose_two_mul {s : ℕ}
    (H : Hypergraph V) (family : Finset (Finset V))
    (hfamily : family ⊆ (Finset.univ : Finset V).powersetCard s)
    (hfamily_ne : family.Nonempty)
    (mu : (S : Finset V) → EdgeWeight (H.restrict S))
    {p B : ℝ} (hp : 0 < p)
    (hlocal : ∀ S ∈ family, (H.restrict S).Lambda p (mu S) < B)
    (hchoose : 0 < (Fintype.card V - 2).choose (s - 2)) :
    H.Lambda p (summedLocalWeight H family mu) <
      ((Fintype.card V - 2).choose (s - 2) : ℝ) * (family.card * B) := by
  have hsum :
      ∑ S ∈ family, (H.restrict S).Lambda p (mu S) <
        ∑ _S ∈ family, B :=
    Finset.sum_lt_sum_of_nonempty hfamily_ne hlocal
  have hsum' :
      ∑ S ∈ family, (H.restrict S).Lambda p (mu S) < family.card * B := by
    simpa using hsum
  exact (Lambda_summedLocalWeight_le_choose_two H family hfamily mu hp).trans_lt
    (mul_lt_mul_of_pos_left hsum' (by exact_mod_cast hchoose))

/-- Exact ratio identity for the two-vertex containment count. -/
lemma choose_two_containment_identity {N s : ℕ} (hs : 2 ≤ s) (hsN : s ≤ N) :
    (N - 2).choose (s - 2) * (N * (N - 1)) =
      N.choose s * (s * (s - 1)) := by
  let n := N - 2
  let k := s - 2
  have hN : N = n + 2 := by dsimp [n]; omega
  have hs' : s = k + 2 := by dsimp [k]; omega
  rw [hN, hs']
  simp only [show n + 2 - 2 = n by omega, show 2 + n - 2 = n by omega,
    show k + 2 - 2 = k by omega, show 2 + k - 2 = k by omega,
    show n + 2 - 1 = n + 1 by omega, show 2 + n - 1 = n + 1 by omega,
    show k + 2 - 1 = k + 1 by omega, show 2 + k - 1 = k + 1 by omega]
  change n.choose k * ((n + 2) * (n + 1)) =
    (n + 2).choose (k + 2) * ((k + 2) * (k + 1))
  calc
    n.choose k * ((n + 2) * (n + 1)) =
        (n + 2) * ((n + 1) * n.choose k) := by ring
    _ = (n + 2) * ((n + 1).choose (k + 1) * (k + 1)) := by
      rw [Nat.add_one_mul_choose_eq n k]
    _ = ((n + 2) * (n + 1).choose (k + 1)) * (k + 1) := by ring
    _ = ((n + 2).choose (k + 2) * (k + 2)) * (k + 1) := by
      rw [Nat.add_one_mul_choose_eq (n + 1) (k + 1)]
    _ = (n + 2).choose (k + 2) * ((k + 2) * (k + 1)) := by ring

/-- The ceiling threshold has the exact two-factor estimate needed in the
binomial ratio.  The hypothesis `2 ≤ sampleThreshold r N` is precisely the
nontrivial localization branch. -/
lemma sampleThreshold_product_bound {r N : ℕ} (hr : 2 ≤ r)
    (hs : 2 ≤ sampleThreshold r N) :
    r ^ 68 * (sampleThreshold r N * (sampleThreshold r N - 1)) ≤
      4 * (N * (N - 1)) := by
  let d := r ^ 34
  let s := sampleThreshold r N
  have hd : 0 < d := Nat.pow_pos (by omega)
  have hsd : 0 < s := lt_of_lt_of_le (by omega) hs
  have hNpos : 0 < N := by
    by_contra hN
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simp [s, sampleThreshold] at hs
  have hceil_lower : N ≤ d * s := by
    exact ceilDiv_lower N d hd
  have hpred_lt : d * (s - 1) < N := by
    by_contra h
    have hNpred : N ≤ d * (s - 1) := Nat.le_of_not_gt h
    have hs_pred : s ≤ s - 1 := by
      change N ⌈/⌉ d ≤ s - 1
      exact (ceilDiv_le_iff_le_mul hd).2 hNpred
    omega
  have hdN : d ≤ N - 1 := by
    have hone : 1 ≤ s - 1 := by omega
    have : d ≤ d * (s - 1) := by
      simpa [mul_comm] using Nat.mul_le_mul_left d hone
    omega
  have hds : d * s ≤ 2 * N := by
    have hpred_le : d * (s - 1) ≤ N - 1 := by omega
    calc
      d * s = d * ((s - 1) + 1) := by congr 1 <;> omega
      _ = d * (s - 1) + d := by rw [mul_add, mul_one]
      _ ≤ (N - 1) + (N - 1) := Nat.add_le_add hpred_le hdN
      _ ≤ 2 * N := by omega
  have hdspred : d * (s - 1) ≤ 2 * (N - 1) := by omega
  have hmul := Nat.mul_le_mul hds hdspred
  change r ^ 68 * (s * (s - 1)) ≤ 4 * (N * (N - 1))
  have hrpow : r ^ 68 = d * d := by
    simp [d, ← pow_add]
  rw [hrpow]
  calc
    d * d * (s * (s - 1)) = (d * s) * (d * (s - 1)) := by ring
    _ ≤ (2 * N) * (2 * (N - 1)) := hmul
    _ = 4 * (N * (N - 1)) := by ring

/-- Cross-multiplied form of the rounded containment ratio. -/
theorem rounded_containment_ratio {r N : ℕ} (hr : 2 ≤ r)
    (hs : 2 ≤ sampleThreshold r N)
    (hsN : sampleThreshold r N ≤ N) :
    r ^ 68 * (N - 2).choose (sampleThreshold r N - 2) ≤
      4 * N.choose (sampleThreshold r N) := by
  have hid := choose_two_containment_identity hs hsN
  have hprod := sampleThreshold_product_bound hr hs
  have hmul :
      (r ^ 68 * (N - 2).choose (sampleThreshold r N - 2)) * (N * (N - 1)) ≤
        (4 * N.choose (sampleThreshold r N)) * (N * (N - 1)) := by
    calc
      (r ^ 68 * (N - 2).choose (sampleThreshold r N - 2)) * (N * (N - 1)) =
          r ^ 68 * (N.choose (sampleThreshold r N) *
            (sampleThreshold r N * (sampleThreshold r N - 1))) := by
              rw [mul_assoc, hid]
      _ ≤ N.choose (sampleThreshold r N) * (4 * (N * (N - 1))) := by
        nlinarith [Nat.zero_le (N.choose (sampleThreshold r N))]
      _ = (4 * N.choose (sampleThreshold r N)) * (N * (N - 1)) := by ring
  have hNN : 0 < N * (N - 1) := by
    have hN : 2 ≤ N := hs.trans hsN
    exact Nat.mul_pos (by omega) (by omega)
  exact Nat.le_of_mul_le_mul_right hmul hNN

/-- The containment estimate after the pigeonhole lower bound
`choose N s ≤ r * |family|`.  This is the exact natural-number form of
`|T_L| ≤ 4 r ε² |family|`, with `ε = r⁻³⁴`. -/
theorem rounded_containmentFiber_bound {r N : ℕ} (hr : 2 ≤ r)
    (hs : 2 ≤ sampleThreshold r N)
    (hsN : sampleThreshold r N ≤ N)
    (family : Finset (Finset (Fin N)))
    (hfamily : family ⊆
      (Finset.univ : Finset (Fin N)).powersetCard (sampleThreshold r N))
    (hlower : N.choose (sampleThreshold r N) ≤ r * family.card)
    (L : Finset (Fin N)) (hL : 2 ≤ L.card) :
    r ^ 68 * (containmentFiber family L).card ≤ 4 * r * family.card := by
  calc
    r ^ 68 * (containmentFiber family L).card ≤
        r ^ 68 * (N - 2).choose (sampleThreshold r N - 2) :=
      Nat.mul_le_mul_left _
        (by simpa using card_containmentFiber_le_choose_two family hfamily L hL)
    _ ≤ 4 * N.choose (sampleThreshold r N) := rounded_containment_ratio hr hs hsN
    _ ≤ 4 * (r * family.card) := Nat.mul_le_mul_left 4 hlower
    _ = 4 * r * family.card := by ring

/-- Real division form of `rounded_containmentFiber_bound`. -/
theorem rounded_containmentFiber_bound_real {r N : ℕ} (hr : 2 ≤ r)
    (hs : 2 ≤ sampleThreshold r N)
    (hsN : sampleThreshold r N ≤ N)
    (family : Finset (Finset (Fin N)))
    (hfamily : family ⊆
      (Finset.univ : Finset (Fin N)).powersetCard (sampleThreshold r N))
    (hlower : N.choose (sampleThreshold r N) ≤ r * family.card)
    (L : Finset (Fin N)) (hL : 2 ≤ L.card) :
    ((containmentFiber family L).card : ℝ) ≤
      (4 * r * family.card : ℝ) / (r : ℝ) ^ 68 := by
  have hnat := rounded_containmentFiber_bound hr hs hsN family hfamily hlower L hL
  have hreal :
      (r : ℝ) ^ 68 * (containmentFiber family L).card ≤
        (4 * r * family.card : ℕ) := by
    exact_mod_cast hnat
  exact (le_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < r) 68)).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hreal)

/-- The two factors in the rounded localization calculation simplify to
the advertised coefficient `2^11 / r^16`. -/
lemma localization_coefficient_identity {r : ℕ} (hr : 2 ≤ r) :
    ((4 : ℝ) * r / (r : ℝ) ^ 68) * ((2 : ℝ) ^ 9 * (r : ℝ) ^ 51) =
      (2 : ℝ) ^ 11 / (r : ℝ) ^ 16 := by
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The numerical coefficient in the localization proof is at most `1/32`.
This is the real-valued version used after the Janson estimates have been
assembled. -/
theorem localization_coefficient_real {r : ℕ} (hr : 2 ≤ r) :
    (2 : ℝ) ^ 11 / (r : ℝ) ^ 16 ≤ 1 / 32 := by
  have hpow : (2 : ℝ) ^ 16 ≤ (r : ℝ) ^ 16 := by
    exact_mod_cast Numeric.localization_coefficient hr
  have hrpow : 0 < (r : ℝ) ^ 16 := pow_pos (by positivity) _
  rw [div_le_iff₀ hrpow]
  norm_num at ⊢ hpow
  nlinarith

/-! ## Event-level localization -/

/-- The smaller Janson radius used on the rounded sample set:
`δ p N / (2^9 r) = p N / (512 r^51)`. -/
noncomputable def localJansonRadius (r pNum pDen N : ℕ) : ℝ :=
  jansonRadius pNum pDen N / (512 * (r : ℝ) ^ 51)

lemma localJansonRadius_pos {r pNum pDen N : ℕ}
    (hr : 2 ≤ r) (hpNum : 0 < pNum) (hpDen : 0 < pDen) (hN : 0 < N) :
    0 < localJansonRadius r pNum pDen N := by
  exact div_pos (jansonRadius_pos hpNum hpDen hN) (by positivity)

/-- The numerical final step in the summed-witness argument. -/
private lemma summed_energy_lt_global_radius {r K M : ℕ} {P x : ℝ}
    (hr : 2 ≤ r) (hP : 0 < P) (hM : 0 < M)
    (hKM : r ^ 68 * K ≤ 4 * r * M)
    (hx : x < (K : ℝ) * (M * (1 / (P / (512 * (r : ℝ) ^ 51))))) :
    x < (M : ℝ) ^ 2 / P := by
  have hr68 : 0 < (r : ℝ) ^ 68 := pow_pos (by positivity) _
  have hKMreal : (r : ℝ) ^ 68 * K ≤ (4 * r * M : ℕ) := by
    exact_mod_cast hKM
  have hKdiv : (K : ℝ) ≤ ((4 : ℝ) * r / (r : ℝ) ^ 68) * M := by
    calc
      (K : ℝ) ≤ ((4 : ℝ) * r * M) / (r : ℝ) ^ 68 :=
        (le_div_iff₀ hr68).2 (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hKMreal)
      _ = ((4 : ℝ) * r / (r : ℝ) ^ 68) * M := by ring
  have hBpos : 0 < (M : ℝ) * (1 / (P / (512 * (r : ℝ) ^ 51))) := by
    positivity
  have hcoeff := localization_coefficient_real hr
  calc
    x < (K : ℝ) * (M * (1 / (P / (512 * (r : ℝ) ^ 51)))) := hx
    _ ≤ (((4 : ℝ) * r / (r : ℝ) ^ 68) * M) *
        (M * (1 / (P / (512 * (r : ℝ) ^ 51)))) :=
      mul_le_mul_of_nonneg_right hKdiv hBpos.le
    _ = ((2 : ℝ) ^ 11 / (r : ℝ) ^ 16) * ((M : ℝ) ^ 2 / P) := by
      rw [← localization_coefficient_identity hr]
      field_simp
      ring
    _ ≤ (1 / 32 : ℝ) * ((M : ℝ) ^ 2 / P) := by
      exact mul_le_mul_of_nonneg_right hcoeff (div_nonneg (sq_nonneg _) hP.le)
    _ < (M : ℝ) ^ 2 / P := by
      have hright : 0 < (M : ℝ) ^ 2 / P := div_pos (sq_pos_of_pos (by exact_mod_cast hM)) hP
      nlinarith

/-- Rounded localization (ACDFM Lemma 6.2), stated in the global vertex
coordinates used by the subsequent maximal-seed argument.

If a coloring witnesses `BadForTargets` at radius `pN`, then some vertex set
of size at least `sampleThreshold r N` makes every color-copy hypergraph,
restricted to that set, fail the Janson property at radius
`pN / (512 r^51)`.  The proof chooses one locally Janson color on every
sample set under the contrary assumption, pigeonholes a color, normalizes all
its local witnesses to mass one, and sums them. -/
theorem badForTargetsOn_exists_localized_failure
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    (targets : TargetVector r order) (G : SimpleGraph V)
    (hr : 2 ≤ r) (hpNum : 0 < pNum) (hpDen : 0 < pDen)
    (hscale : 2 * r ^ 34 ≤ Fintype.card V)
    (hbad : BadForTargetsOn pNum pDen targets G) :
    ∃ (coloring : G.EdgeLabeling (Fin r)) (S : Finset V),
      sampleThreshold r (Fintype.card V) ≤ S.card ∧
      ∀ i : Fin r,
        ¬ ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict S).IsJanson
          (rationalParameter pNum pDen)
          (localJansonRadius r pNum pDen (Fintype.card V)) := by
  classical
  let N := Fintype.card V
  change 2 * r ^ 34 ≤ N at hscale
  obtain ⟨coloring, hcoloring⟩ := hbad
  refine ⟨coloring, ?_⟩
  change ∃ S : Finset V, sampleThreshold r N ≤ S.card ∧
    ∀ i : Fin r,
      ¬ ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict S).IsJanson
        (rationalParameter pNum pDen) (localJansonRadius r pNum pDen N)
  by_contra hnone
  push Not at hnone
  let s := sampleThreshold r N
  let allSamples : Finset (Finset V) :=
    (Finset.univ : Finset V).powersetCard s
  have hrpow : 0 < r ^ 34 := Nat.pow_pos (by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 * r ^ 34) hscale
  have hs_ge_two : 2 ≤ s := by
    dsimp [s, sampleThreshold]
    by_contra hnot
    have hceil_le : N ⌈/⌉ r ^ 34 ≤ 1 := by omega
    have hNle : N ≤ r ^ 34 := by
      have := (ceilDiv_le_iff_le_mul hrpow).1 hceil_le
      simpa using this
    omega
  have hsN : s ≤ N := by
    have hrpow_one : 1 ≤ r ^ 34 := by omega
    dsimp [s, sampleThreshold]
    apply (ceilDiv_le_iff_le_mul hrpow).2
    calc
      N = 1 * N := by simp
      _ ≤ r ^ 34 * N := Nat.mul_le_mul_right N hrpow_one
  have hall_nonempty : allSamples.Nonempty := by
    exact Finset.powersetCard_nonempty.mpr (by simpa [N] using hsN)
  have hlocal : ∀ S ∈ allSamples, ∃ i : Fin r,
      ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict S).IsJanson
        (rationalParameter pNum pDen) (localJansonRadius r pNum pDen N) := by
    intro S hS
    have hScard : S.card = s := (Finset.mem_powersetCard.mp hS).2
    exact hnone S (by simpa [s] using hScard.ge)
  let chosenColor : Finset V → Fin r := fun S ↦
    if hS : S ∈ allSamples then Classical.choose (hlocal S hS) else ⟨0, by omega⟩
  have hchosen : ∀ S ∈ allSamples,
      ((copyHypergraph (targets (chosenColor S))
        (colorClassGraph coloring (chosenColor S)) G).restrict S).IsJanson
          (rationalParameter pNum pDen) (localJansonRadius r pNum pDen N) := by
    intro S hS
    have hc : chosenColor S = Classical.choose (hlocal S hS) := by
      simp [chosenColor, hS]
    rw [hc]
    exact Classical.choose_spec (hlocal S hS)
  let colorFamily : Fin r → Finset (Finset V) := fun i ↦
    allSamples.filter fun S ↦ chosenColor S = i
  let i0 : Fin r := ⟨0, by omega⟩
  have hcolors : (Finset.univ : Finset (Fin r)).Nonempty :=
    ⟨i0, Finset.mem_univ i0⟩
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin r))
    (fun j ↦ (colorFamily j).card) hcolors
  have hpartition : allSamples.card = ∑ j : Fin r, (colorFamily j).card := by
    simpa [colorFamily] using
      (Finset.card_eq_sum_card_fiberwise
        (s := allSamples) (t := (Finset.univ : Finset (Fin r)))
        (f := chosenColor) (fun _ _ ↦ Finset.mem_univ _))
  have hlower : N.choose s ≤ r * (colorFamily i).card := by
    have hallcard : allSamples.card = N.choose s := by
      simp [allSamples, N]
    calc
      N.choose s = allSamples.card := hallcard.symm
      _ = ∑ j : Fin r, (colorFamily j).card := hpartition
      _ ≤
          ∑ _j : Fin r, (colorFamily i).card :=
        Finset.sum_le_sum fun j _ ↦ himax j (Finset.mem_univ j)
      _ = r * (colorFamily i).card := by simp
  have hfamily_nonempty : (colorFamily i).Nonempty := by
    have hchoosePos : 0 < N.choose s := Nat.choose_pos hsN
    have hprod : 0 < r * (colorFamily i).card := hchoosePos.trans_le hlower
    apply Finset.card_pos.mp
    by_contra hnot
    have hzero : (colorFamily i).card = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hprod
  let H : Hypergraph V :=
    copyHypergraph (targets i) (colorClassGraph coloring i) G
  have hfamily_subset : colorFamily i ⊆
      (Finset.univ : Finset V).powersetCard s := by
    exact Finset.filter_subset _ _
  have hfamily_chosen : ∀ S ∈ colorFamily i, chosenColor S = i := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hfamily_local : ∀ S ∈ colorFamily i,
      (H.restrict S).IsJanson (rationalParameter pNum pDen)
        (localJansonRadius r pNum pDen N) := by
    intro S hS
    have hSall : S ∈ allSamples := (Finset.mem_filter.mp hS).1
    change ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict S).IsJanson
      (rationalParameter pNum pDen) (localJansonRadius r pNum pDen N)
    rw [← hfamily_chosen S hS]
    exact hchosen S hSall
  let mu : (S : Finset V) → EdgeWeight (H.restrict S) := fun S ↦
    if hS : S ∈ colorFamily i then
      Classical.choose ((hfamily_local S hS).exists_normalized
        (rationalParameter_pos hpNum hpDen)
        (localJansonRadius_pos hr hpNum hpDen hNpos) (by norm_num : (0 : ℝ) < 1))
    else 0
  have hmu_mass : ∀ S ∈ colorFamily i, (H.restrict S).mass (mu S) = 1 := by
    intro S hS
    simpa [mu, hS] using (Classical.choose_spec
      ((hfamily_local S hS).exists_normalized
        (rationalParameter_pos hpNum hpDen)
        (localJansonRadius_pos hr hpNum hpDen hNpos) (by norm_num : (0 : ℝ) < 1))).1
  have hmu_lambda : ∀ S ∈ colorFamily i,
      (H.restrict S).Lambda (rationalParameter pNum pDen) (mu S) <
        1 / localJansonRadius r pNum pDen N := by
    intro S hS
    simpa [mu, hS] using (Classical.choose_spec
      ((hfamily_local S hS).exists_normalized
        (rationalParameter_pos hpNum hpDen)
        (localJansonRadius_pos hr hpNum hpDen hNpos) (by norm_num : (0 : ℝ) < 1))).2
  have hchoosePos : 0 < (N - 2).choose (s - 2) := by
    apply Nat.choose_pos
    omega
  have hlambda := Lambda_summedLocalWeight_lt_choose_two_mul H (colorFamily i)
    hfamily_subset hfamily_nonempty mu (rationalParameter_pos hpNum hpDen)
    hmu_lambda hchoosePos
  have hcross : r ^ 68 * (N - 2).choose (s - 2) ≤
      4 * r * (colorFamily i).card := by
    calc
      r ^ 68 * (N - 2).choose (s - 2) ≤ 4 * N.choose s := by
        simpa [s] using rounded_containment_ratio hr hs_ge_two hsN
      _ ≤ 4 * (r * (colorFamily i).card) := Nat.mul_le_mul_left 4 hlower
      _ = 4 * r * (colorFamily i).card := by ring
  have hglobalLambda :
      H.Lambda (rationalParameter pNum pDen) (summedLocalWeight H (colorFamily i) mu) <
        ((colorFamily i).card : ℝ) ^ 2 / jansonRadius pNum pDen N := by
    apply summed_energy_lt_global_radius hr
      (jansonRadius_pos hpNum hpDen hNpos) (Finset.card_pos.mpr hfamily_nonempty) hcross
    simpa [localJansonRadius] using hlambda
  have hglobalMass : H.mass (summedLocalWeight H (colorFamily i) mu) =
      ((colorFamily i).card : ℝ) :=
    mass_summedLocalWeight_of_normalized H (colorFamily i) mu hmu_mass
  have hglobalJanson : H.IsJanson (rationalParameter pNum pDen)
      (jansonRadius pNum pDen N) := by
    right
    refine ⟨summedLocalWeight H (colorFamily i) mu, ?_⟩
    rw [hglobalMass]
    exact hglobalLambda
  exact hcoloring i (by simpa [H, N] using hglobalJanson)

/-- The labelled-vertex specialization of
`badForTargetsOn_exists_localized_failure`. -/
theorem badForTargets_exists_localized_failure
    {N r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    (targets : TargetVector r order) (G : SimpleGraph (Fin N))
    (hr : 2 ≤ r) (hpNum : 0 < pNum) (hpDen : 0 < pDen)
    (hscale : 2 * r ^ 34 ≤ N)
    (hbad : BadForTargets pNum pDen targets G) :
    ∃ (coloring : G.EdgeLabeling (Fin r)) (S : Finset (Fin N)),
      sampleThreshold r N ≤ S.card ∧
      ∀ i : Fin r,
        ¬ ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict S).IsJanson
          (rationalParameter pNum pDen) (localJansonRadius r pNum pDen N) := by
  simpa using
    (badForTargetsOn_exists_localized_failure targets G hr hpNum hpDen
      (by simpa using hscale) hbad)

end Localization
end Erdos565
