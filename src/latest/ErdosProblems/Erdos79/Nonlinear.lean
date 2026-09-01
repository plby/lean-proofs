/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Probability.Distributions.SetBernoulli

/-!
# A first-moment obstruction to Ramsey size linearity

This file proves the elementary density criterion used in the formalization of Erdős
Problem 79.  If a finite graph has more than five times as many edges as vertices, then it
is not Ramsey size linear.  The proof is the finite first-moment argument with red edge
probability `1 / k`, ambient order `k ^ 5`, and blue target `K_(k ^ 2)`.
-/

open Finset MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal SimpleGraph

noncomputable section

namespace Erdos79
namespace Nonlinear

/-- The required host edges for a fixed injective labelling of a graph. -/
noncomputable def requiredEdges {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N) :
    Finset (Sym2 (Fin N)) := by
  classical
  exact A.edgeSet.toFinite.toFinset.map f.sym2Map

@[simp] theorem card_requiredEdges {a N : ℕ} (A : SimpleGraph (Fin a))
    (f : Fin a ↪ Fin N) :
    (requiredEdges A f).card = Nat.card A.edgeSet := by
  classical
  calc
    (requiredEdges A f).card = A.edgeSet.toFinite.toFinset.card := by
      simp [requiredEdges]
    _ = Fintype.card A.edgeSet := Set.Finite.card_toFinset A.edgeSet.toFinite
    _ = Nat.card A.edgeSet := by rw [Nat.card_eq_fintype_card]

theorem requiredEdges_subset_diagCompl {a N : ℕ} (A : SimpleGraph (Fin a))
    (f : Fin a ↪ Fin N) :
    (↑(requiredEdges A f) : Set (Sym2 (Fin N))) ⊆ Sym2.diagSetᶜ := by
  classical
  intro e he
  rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
  have heA : e' ∈ A.edgeSet := by
    exact A.edgeSet.toFinite.mem_toFinset.mp he'
  exact fun hdiag ↦
    A.not_isDiag_of_mem_edgeSet heA ((Sym2.isDiag_map f.injective).mp hdiag)

/-- Under the Bernoulli edge measure, all edges in a fixed finite set are red with the
expected product probability. -/
theorem setBernoulli_superset_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | (↑t : Set ι) ⊆ s} = toNNReal p ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop ↦ {i | q i}) ⁻¹' {s : Set ι | (↑t : Set ι) ⊆ s}) =
        ((↑t : Set ι).pi fun _ ↦ ({True} : Set Prop)) := by
    ext q
    simp [Set.subset_def]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

/-- Under the Bernoulli edge measure, all edges in a fixed finite set are blue with the
expected product probability. -/
theorem setBernoulli_disjoint_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | Disjoint (↑t : Set ι) s} =
      toNNReal (σ p) ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop ↦ {i | q i}) ⁻¹'
        {s : Set ι | Disjoint (↑t : Set ι) s}) =
        ((↑t : Set ι).pi fun _ ↦ ({False} : Set Prop)) := by
    ext q
    simp [Set.disjoint_left]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

/-- Red-copy bad event for one injective vertex labelling. -/
def redEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N) :
    Set (Set (Sym2 (Fin N))) :=
  { ω | (↑(requiredEdges A f) : Set (Sym2 (Fin N))) ⊆ ω }

/-- Blue-copy bad event for one injective vertex labelling. -/
def blueEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N) :
    Set (Set (Sym2 (Fin N))) :=
  { ω | Disjoint (↑(requiredEdges A f) : Set (Sym2 (Fin N))) ω }

theorem measure_redEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N)
    (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (redEvent A f) =
      toNNReal p ^ Nat.card A.edgeSet := by
  rw [redEvent, setBernoulli_superset_finset _ _ _ (requiredEdges_subset_diagCompl A f),
    card_requiredEdges]

theorem measure_blueEvent {a N : ℕ} (A : SimpleGraph (Fin a)) (f : Fin a ↪ Fin N)
    (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (blueEvent A f) =
      toNNReal (σ p) ^ Nat.card A.edgeSet := by
  rw [blueEvent, setBernoulli_disjoint_finset _ _ _ (requiredEdges_subset_diagCompl A f),
    card_requiredEdges]

/-- The union of all injectively labelled red copies. -/
def badRed {a N : ℕ} (A : SimpleGraph (Fin a)) : Set (Set (Sym2 (Fin N))) :=
  ⋃ f : Fin a ↪ Fin N, redEvent A f

/-- The union of all injectively labelled blue copies. -/
def badBlue {a N : ℕ} (A : SimpleGraph (Fin a)) : Set (Set (Sym2 (Fin N))) :=
  ⋃ f : Fin a ↪ Fin N, blueEvent A f

theorem measure_badRed_le {a N : ℕ} (A : SimpleGraph (Fin a)) (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (badRed (N := N) A) ≤
      (N : ℝ≥0∞) ^ a * (toNNReal p : ℝ≥0∞) ^ Nat.card A.edgeSet := by
  classical
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  calc
    μ (badRed (N := N) A) ≤ ∑ f : Fin a ↪ Fin N, μ (redEvent A f) := by
      simpa [badRed] using measure_iUnion_fintype_le μ (fun f : Fin a ↪ Fin N ↦ redEvent A f)
    _ = (Fintype.card (Fin a ↪ Fin N) : ℝ≥0∞) *
        (toNNReal p : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      simp [μ, measure_redEvent]
    _ ≤ (N : ℝ≥0∞) ^ a *
        (toNNReal p : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      gcongr
      norm_cast
      calc
        Fintype.card (Fin a ↪ Fin N) ≤ Fintype.card (Fin a → Fin N) :=
          Fintype.card_le_of_injective (fun f ↦ f.toFun)
            (fun _ _ h ↦ DFunLike.coe_injective h)
        _ = N ^ a := by simp

theorem measure_badBlue_le {a N : ℕ} (A : SimpleGraph (Fin a)) (p : I) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) (badBlue (N := N) A) ≤
      (N : ℝ≥0∞) ^ a * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card A.edgeSet := by
  classical
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  calc
    μ (badBlue (N := N) A) ≤ ∑ f : Fin a ↪ Fin N, μ (blueEvent A f) := by
      simpa [badBlue] using measure_iUnion_fintype_le μ (fun f : Fin a ↪ Fin N ↦ blueEvent A f)
    _ = (Fintype.card (Fin a ↪ Fin N) : ℝ≥0∞) *
        (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      simp [μ, measure_blueEvent]
    _ ≤ (N : ℝ≥0∞) ^ a *
        (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card A.edgeSet := by
      gcongr
      norm_cast
      calc
        Fintype.card (Fin a ↪ Fin N) ≤ Fintype.card (Fin a → Fin N) :=
          Fintype.card_le_of_injective (fun f ↦ f.toFun)
            (fun _ _ h ↦ DFunLike.coe_injective h)
        _ = N ^ a := by simp

/-- Every actual red copy belongs to one of the labelled red-copy events. -/
theorem mem_badRed_of_isContained {a N : ℕ} (A : SimpleGraph (Fin a))
    (ω : Set (Sym2 (Fin N))) (h : A ⊑ SimpleGraph.fromEdgeSet ω) :
    ω ∈ badRed (N := N) A := by
  classical
  rcases h with ⟨c⟩
  refine Set.mem_iUnion.2 ⟨c.toEmbedding, ?_⟩
  intro e he
  rcases Finset.mem_map.mp he with ⟨e', heA, rfl⟩
  have heA' : e' ∈ A.edgeSet := by
    exact A.edgeSet.toFinite.mem_toFinset.mp heA
  have hmap : A.map c.toEmbedding ≤ SimpleGraph.fromEdgeSet ω := by
    rw [SimpleGraph.map_le_iff_le_comap]
    exact c.toHom.le_comap
  have he' : e'.map c.toEmbedding ∈ (SimpleGraph.fromEdgeSet ω).edgeSet :=
    SimpleGraph.edgeSet_mono hmap (by
      rw [SimpleGraph.edgeSet_map]
      exact ⟨e', heA', rfl⟩)
  rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
  exact he'.1

/-- Every actual blue copy belongs to one of the labelled blue-copy events. -/
theorem mem_badBlue_of_isContained {a N : ℕ} (A : SimpleGraph (Fin a))
    (ω : Set (Sym2 (Fin N))) (h : A ⊑ (SimpleGraph.fromEdgeSet ω)ᶜ) :
    ω ∈ badBlue (N := N) A := by
  classical
  rcases h with ⟨c⟩
  refine Set.mem_iUnion.2 ⟨c.toEmbedding, ?_⟩
  change Disjoint (↑(requiredEdges A c.toEmbedding) : Set (Sym2 (Fin N))) ω
  rw [Set.disjoint_left]
  intro e he hω
  rcases Finset.mem_map.mp he with ⟨e', heA, rfl⟩
  have heA' : e' ∈ A.edgeSet := by
    exact A.edgeSet.toFinite.mem_toFinset.mp heA
  have hmap : A.map c.toEmbedding ≤ (SimpleGraph.fromEdgeSet ω)ᶜ := by
    rw [SimpleGraph.map_le_iff_le_comap]
    exact c.toHom.le_comap
  have heBlue : e'.map c.toEmbedding ∈ (SimpleGraph.fromEdgeSet ω)ᶜ.edgeSet :=
    SimpleGraph.edgeSet_mono hmap (by
      rw [SimpleGraph.edgeSet_map]
      exact ⟨e', heA', rfl⟩)
  have hndiag : ¬ (e'.map c.toEmbedding).IsDiag := by
    exact fun hdiag ↦
      A.not_isDiag_of_mem_edgeSet heA' ((Sym2.isDiag_map c.injective).mp hdiag)
  have heRed : e'.map c.toEmbedding ∈ (SimpleGraph.fromEdgeSet ω).edgeSet := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨hω, by simpa using hndiag⟩
  revert heBlue heRed
  refine Sym2.inductionOn (e'.map c.toEmbedding) ?_
  intro u v hblue hred
  have hnot : ¬ (SimpleGraph.fromEdgeSet ω).Adj u v := by
    simpa [SimpleGraph.mem_edgeSet] using hblue.2
  exact hnot (by simpa [SimpleGraph.mem_edgeSet] using hred)

theorem thirtyTwo_mul_le_two_pow {t : ℕ} (ht : 8 ≤ t) : 32 * t ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ]
      have hthirtyTwo : 32 ≤ 2 ^ t := (by omega : 32 ≤ 32 * t).trans ih
      omega

theorem natCard_edgeSet_top (n : ℕ) :
    Nat.card (⊤ : SimpleGraph (Fin n)).edgeSet = Nat.choose n 2 := by
  classical
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

/-- Numerical core of the first-moment estimate.  Choosing `k` to be a sufficiently large
power of two lets us bound the blue-copy term by grouping the required edges into blocks of
`k`, avoiding any appeal to an unformalized asymptotic estimate. -/
theorem firstMoment_parameters (C a b : ℕ) (hab : 5 * a < b) :
    ∃ t d k s N r : ℕ, ∃ p : I,
      t = C + 8 ∧ d = 2 ^ (C + 7) ∧ k = 2 * d ∧ s = k ^ 2 ∧ N = k ^ 5 ∧
      r = d * (s - 1) ∧
      C * Nat.choose s 2 < N ∧ Nat.choose s 2 = k * r ∧
      (N : ℝ≥0∞) ^ a * (toNNReal p : ℝ≥0∞) ^ b ≤ 1 / 4 ∧
      (N : ℝ≥0∞) ^ s * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose s 2 ≤ 1 / 4 := by
  let t : ℕ := C + 8
  let d : ℕ := 2 ^ (C + 7)
  let k : ℕ := 2 * d
  let s : ℕ := k ^ 2
  let N : ℕ := k ^ 5
  let r : ℕ := d * (s - 1)
  have ht : 8 ≤ t := by simp [t]
  have hkpow : k = 2 ^ t := by
    simp only [k, d, t]
    rw [show C + 8 = (C + 7) + 1 by omega, pow_succ]
    ring
  have h32 : 32 * t ≤ k := by simpa [hkpow] using thirtyTwo_mul_le_two_pow ht
  have h16 : 16 * t ≤ d := by
    dsimp [k] at h32
    omega
  have hkfour : 4 ≤ k := by
    have : 32 * 8 ≤ k := (Nat.mul_le_mul_left 32 ht).trans h32
    omega
  have hCk : C < k := by
    dsimp [t] at h32
    omega
  have hsfour : 4 ≤ s := by
    dsimp [s]
    nlinarith
  have hchoose : Nat.choose s 2 = k * r := by
    rw [Nat.choose_two_right]
    have hnum : s * (s - 1) = 2 * (k * r) := by
      calc
        s * (s - 1) = (k * k) * (s - 1) := by simp [s, pow_two]
        _ = 2 * (k * r) := by simp only [k, r]; ring
    rw [hnum]
    simp
  have hambient : C * Nat.choose s 2 < N := by
    calc
      C * Nat.choose s 2 ≤ C * s ^ 2 :=
        Nat.mul_le_mul_left C (Nat.choose_le_pow s 2)
      _ < k * s ^ 2 := Nat.mul_lt_mul_of_pos_right hCk (pow_pos (by omega) _)
      _ = N := by simp [N, s, pow_succ]; ring
  have hgap : 5 * t * s + 2 ≤ r := by
    have hten : 10 * t + 1 ≤ d := by omega
    have hmul := Nat.mul_le_mul_right s hten
    simp only [add_mul, one_mul] at hmul
    have hleft : 10 * t * s + 4 ≤ d * s := by omega
    have hright : d * s ≤ 2 * r := by
      have hs : s ≤ 2 * (s - 1) := by omega
      simpa [r, mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left d hs
    have : 2 * (5 * t * s + 2) ≤ 2 * r := by
      calc
        2 * (5 * t * s + 2) = 10 * t * s + 4 := by ring
        _ ≤ d * s := hleft
        _ ≤ 2 * r := hright
    omega
  let q : ℝ := 1 / (k : ℝ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (one_div_le (by positivity) zero_lt_one).2
    norm_num
    exact_mod_cast (show 1 ≤ k by omega)
  let p : I := ⟨q, hq0, hq1⟩
  have hp_real : ((toNNReal p : NNReal) : ℝ) = q := by simp [p]
  have hp_blue_real : ((toNNReal (σ p) : NNReal) : ℝ) = 1 - q := by
    simp [p]
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hred_real : (N : ℝ) ^ a * q ^ b ≤ 1 / 4 := by
    have hba : 5 * a + 1 ≤ b := by omega
    have hpow : (k : ℝ) ^ (5 * a + 1) ≤ (k : ℝ) ^ b := by
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k by omega)) hba
    have hratio :
        (N : ℝ) ^ a * q ^ b =
          ((k : ℝ) ^ (5 * a + 1) / (k : ℝ) ^ b) * (1 / (k : ℝ)) := by
      simp only [N, q, Nat.cast_pow, div_pow]
      field_simp
      rw [show 5 * a + 1 = 5 * a + 1 by rfl, pow_succ]
      ring
    rw [hratio]
    calc
      ((k : ℝ) ^ (5 * a + 1) / (k : ℝ) ^ b) * (1 / (k : ℝ))
          ≤ 1 * (1 / (k : ℝ)) := by
            gcongr
            exact (div_le_one (pow_pos hkreal b)).2 hpow
      _ ≤ 1 / 4 := by
        simpa using
          (one_div_le hkreal (by norm_num : (0 : ℝ) < 1 / 4)).2 (by
            norm_num
            exact_mod_cast hkfour)
  have hblue_block : (1 - q) ^ k ≤ (1 / 2 : ℝ) := by
    calc
      (1 - q) ^ k = (1 - (1 : ℝ) / k) ^ k := by rfl
      _ ≤ Real.exp (-1) := Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast (show 1 ≤ k by omega))
      _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le
  have hblue_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hblue_pow : (1 - q) ^ Nat.choose s 2 ≤ (1 / 2 : ℝ) ^ r := by
    rw [hchoose, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hblue_nonneg k) hblue_block r
  have hNpow : (N : ℝ) ^ s = (2 : ℝ) ^ (5 * t * s) := by
    calc
      (N : ℝ) ^ s = ((k : ℝ) ^ 5) ^ s := by simp [N]
      _ = (k : ℝ) ^ (5 * s) := by rw [← pow_mul]
      _ = (((2 : ℝ) ^ t) ^ (5 * s)) := by rw [hkpow]; norm_cast
      _ = (2 : ℝ) ^ (t * (5 * s)) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (5 * t * s) := by
        congr 1
        ring
  have hpowers : (2 : ℝ) ^ (5 * t * s + 2) ≤ (2 : ℝ) ^ r := by
    exact pow_le_pow_right₀ (by norm_num) hgap
  have hblue_real : (N : ℝ) ^ s * (1 - q) ^ Nat.choose s 2 ≤ 1 / 4 := by
    calc
      (N : ℝ) ^ s * (1 - q) ^ Nat.choose s 2
          ≤ (N : ℝ) ^ s * (1 / 2 : ℝ) ^ r := by gcongr
      _ = (2 : ℝ) ^ (5 * t * s) / (2 : ℝ) ^ r := by rw [hNpow, div_pow]; ring
      _ ≤ 1 / 4 := by
        rw [div_le_iff₀ (pow_pos (by norm_num) r)]
        have hfour : 4 * (2 : ℝ) ^ (5 * t * s) ≤ (2 : ℝ) ^ r := by
          rw [pow_add] at hpowers
          norm_num at hpowers
          nlinarith
        nlinarith
  have hred_enn :
      (N : ℝ≥0∞) ^ a * (toNNReal p : ℝ≥0∞) ^ b ≤ 1 / 4 := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top (by simp)))
      (by simp)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, hp_real] using hred_real
  have hblue_enn :
      (N : ℝ≥0∞) ^ s * (toNNReal (σ p) : ℝ≥0∞) ^ Nat.choose s 2 ≤ 1 / 4 := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) (ENNReal.pow_ne_top (by simp)))
      (by simp)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, hp_blue_real] using hblue_real
  exact ⟨t, d, k, s, N, r, p, rfl, rfl, rfl, rfl, rfl, rfl,
    hambient, hchoose, hred_enn, hblue_enn⟩

/-- A graph with more than five edges per vertex is not Ramsey size linear.

The witness against a proposed constant `C` is the complete graph on `k ^ 2` vertices,
where `k` is a sufficiently large power of two.  A finite Bernoulli count on graphs with
`k ^ 5` vertices gives a colouring with neither a red copy of `G` nor a blue `K_(k^2)`.
-/
theorem not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount (G : GraphCode)
    (hG : 5 * G.vertexCount < G.edgeCount) : ¬ RamseySizeLinear G := by
  intro hlinear
  rcases hlinear with ⟨C, hC⟩
  obtain ⟨t, d, k, s, N, r, p, ht, hd, hk, hs, hN, hr, hambient, hchoose,
      hredBound, hblueBound⟩ :=
    firstMoment_parameters C G.vertexCount G.edgeCount hG
  let H : GraphCode := completeCode s
  have hsfour : 4 ≤ s := by
    have hdpos : 0 < d := by rw [hd]; positivity
    have hk2 : 2 ≤ k := by rw [hk]; omega
    rw [hs]
    nlinarith
  have hHNoIsolated : NoIsolated H := by
    have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr (by omega)
    change ∀ v : Fin s, ¬ (⊤ : SimpleGraph (Fin s)).IsIsolated v
    intro v
    apply ((⊤ : SimpleGraph (Fin s)).exists_adj_iff_not_isIsolated).mp
    obtain ⟨w, hw⟩ := exists_ne v
    exact ⟨w, by simpa using hw.symm⟩
  let μ : Measure (Set (Sym2 (Fin N))) :=
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
  have hredMeasure : μ (badRed (N := N) G.graph) ≤ 1 / 4 := by
    calc
      μ (badRed (N := N) G.graph) ≤
          (N : ℝ≥0∞) ^ G.vertexCount *
            (toNNReal p : ℝ≥0∞) ^ Nat.card G.graph.edgeSet := by
              simpa [μ] using measure_badRed_le (N := N) G.graph p
      _ ≤ 1 / 4 := by simpa [GraphCode.edgeCount] using hredBound
  have hblueMeasure : μ (badBlue (N := N) (⊤ : SimpleGraph (Fin s))) ≤ 1 / 4 := by
    calc
      μ (badBlue (N := N) (⊤ : SimpleGraph (Fin s))) ≤
          (N : ℝ≥0∞) ^ s *
            (toNNReal (σ p) : ℝ≥0∞) ^ Nat.card (⊤ : SimpleGraph (Fin s)).edgeSet := by
              simpa [μ] using measure_badBlue_le (N := N) (⊤ : SimpleGraph (Fin s)) p
      _ ≤ 1 / 4 := by
        rw [natCard_edgeSet_top]
        exact hblueBound
  have hbadMeasure :
      μ (badRed (N := N) G.graph ∪ badBlue (N := N) (⊤ : SimpleGraph (Fin s))) < 1 := by
    calc
      μ (badRed (N := N) G.graph ∪ badBlue (N := N) (⊤ : SimpleGraph (Fin s))) ≤
          μ (badRed (N := N) G.graph) +
            μ (badBlue (N := N) (⊤ : SimpleGraph (Fin s))) := measure_union_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hredMeasure hblueMeasure
      _ < 1 := by
        have htr :
            (((1 / 4 : ℝ≥0∞) + 1 / 4).toReal) < (1 : ℝ≥0∞).toReal := by
          norm_num [ENNReal.toReal_add]
        exact (ENNReal.toReal_lt_toReal (by simp) (by simp)).1 htr
  have hbadNeUniv :
      badRed (N := N) G.graph ∪ badBlue (N := N) (⊤ : SimpleGraph (Fin s)) ≠ Set.univ := by
    intro hall
    rw [hall] at hbadMeasure
    simp [μ] at hbadMeasure
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hbadNeUniv
  let X : SimpleGraph (Fin N) := SimpleGraph.fromEdgeSet ω
  have hredFree : ¬ G.graph ⊑ X := by
    intro hcopy
    apply hω
    exact Or.inl (mem_badRed_of_isContained G.graph ω hcopy)
  have hblueFree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ Xᶜ := by
    intro hcopy
    apply hω
    exact Or.inr (mem_badBlue_of_isContained (⊤ : SimpleGraph (Fin s)) ω hcopy)
  have hnotRamsey : ¬ RamseyAt G H N := by
    intro hramsey
    rcases hramsey X with hred | hblue
    · exact hredFree hred
    · exact hblueFree (by simpa [H, completeCode] using hblue)
  apply hnotRamsey
  have hHedges : H.edgeCount = Nat.choose s 2 := by
    change Nat.card (⊤ : SimpleGraph (Fin s)).edgeSet = Nat.choose s 2
    exact natCard_edgeSet_top s
  have hramsey := hC H hHNoIsolated
  rw [hHedges] at hramsey
  exact hramsey.mono_vertices hambient.le

end Nonlinear

/-- Namespace-level form of the elementary first-moment obstruction. -/
theorem not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount (G : GraphCode)
    (hG : 5 * G.vertexCount < G.edgeCount) : ¬ RamseySizeLinear G :=
  Nonlinear.not_ramseySizeLinear_of_five_mul_vertexCount_lt_edgeCount G hG

end Erdos79
