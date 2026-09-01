import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The finite logarithmic-energy bridge for Erdős 991

The product below is indexed by ordered distinct pairs. Thus it is the square
of the usual product over unordered pairs, and has exactly the same maximizers.
This indexing convention makes the logarithmic identity agree literally with
the standard ordered-pair logarithmic energy.
-/

open scoped BigOperators

namespace Check991Fekete

noncomputable section

variable {α : Type*} [MetricSpace α]

/-- A symmetric function of two points, viewed as a function of an unordered
pair. -/
def pairDist : Sym2 α → ℝ :=
  Sym2.lift ⟨dist, dist_comm⟩

@[simp]
lemma pairDist_mk (x y : α) : pairDist s(x, y) = dist x y := rfl

/-- The conventional Fekete product, with every unordered distinct pair
occurring exactly once. -/
def unorderedDistanceProduct (A : Finset α) : ℝ :=
  by
    classical
    exact ∏ p ∈ A.sym2 with ¬p.IsDiag, pairDist p

/-- The ordered off-diagonal distance product of a finite metric
configuration. It is the square of the conventional unordered product. -/
def distanceProduct (A : Finset α) : ℝ :=
  ∏ p ∈ A.offDiag, dist p.1 p.2

/-- The ordered real logarithmic energy of a finite metric configuration. -/
def orderedLogEnergy (A : Finset α) : ℝ :=
  ∑ p ∈ A.offDiag, -Real.log (dist p.1 p.2)

/-- The contribution of a prospective point `z` against a finite
configuration `S`. -/
def pointLogPotential (S : Finset α) (z : α) : ℝ :=
  ∑ x ∈ S, -Real.log (dist z x)

/-- An `n`-point logarithmic Fekete configuration maximizes the conventional
unordered distance product among all `n`-point finite configurations. -/
def IsLogFekete (n : ℕ) (A : Finset α) : Prop :=
  A.card = n ∧
    ∀ B : Finset α, B.card = n →
      unorderedDistanceProduct B ≤ unorderedDistanceProduct A

lemma dist_pos_of_mem_offDiag (A : Finset α) {p : α × α} (hp : p ∈ A.offDiag) :
    0 < dist p.1 p.2 := by
  exact dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2

/-- Every off-diagonal distance product is strictly positive, including the
empty product. -/
theorem distanceProduct_pos (A : Finset α) : 0 < distanceProduct A := by
  rw [distanceProduct]
  exact Finset.prod_pos fun p hp ↦ dist_pos_of_mem_offDiag A hp

theorem distanceProduct_ne_zero (A : Finset α) : distanceProduct A ≠ 0 :=
  ne_of_gt (distanceProduct_pos A)

lemma pairDist_pos_of_mem_sym2_not_isDiag (A : Finset α) {p : Sym2 α}
    (hp : p ∈ A.sym2) (hdiag : ¬p.IsDiag) : 0 < pairDist p := by
  induction p using Sym2.ind with
  | _ x y =>
      rw [pairDist_mk, dist_pos]
      exact Sym2.mk_isDiag_iff.not.mp hdiag

/-- The usual unordered distance product is strictly positive. -/
theorem unorderedDistanceProduct_pos (A : Finset α) :
    0 < unorderedDistanceProduct A := by
  classical
  rw [unorderedDistanceProduct]
  apply Finset.prod_pos
  intro p hp
  rw [Finset.mem_filter] at hp
  exact pairDist_pos_of_mem_sym2_not_isDiag A hp.1 hp.2

/-- Multiplicative counterpart of `Finset.sum_sym2_filter_not_isDiag`. -/
lemma prod_sym2_filter_not_isDiag {ι M : Type*} [LinearOrder ι] [CommMonoid M]
    (s : Finset ι) (f : Sym2 ι → M) :
    ∏ i ∈ s.sym2 with ¬i.IsDiag, f i =
      ∏ i ∈ s.offDiag with i.1 < i.2, f s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.prod_subtype_eq_prod_filter]
  refine (Finset.prod_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  all_goals aesop

lemma unorderedDistanceProduct_eq_prod_lt [LinearOrder α] (A : Finset α) :
    unorderedDistanceProduct A =
      ∏ p ∈ A.offDiag with p.1 < p.2, dist p.1 p.2 := by
  unfold unorderedDistanceProduct
  convert prod_sym2_filter_not_isDiag A pairDist using 1
  · apply Finset.prod_congr
    · ext p
      simp
    · intro p hp
      rfl
  · apply Finset.prod_congr
    · ext p
      simp
    · intro p hp
      rfl

/-- The ordered off-diagonal product is exactly the square of the
conventional unordered distance product. -/
theorem distanceProduct_eq_unorderedDistanceProduct_sq (A : Finset α) :
    distanceProduct A = unorderedDistanceProduct A ^ 2 := by
  let : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  let lo := A.offDiag.filter fun p ↦ p.1 < p.2
  let hi := A.offDiag.filter fun p ↦ p.2 < p.1
  have hunion : lo ∪ hi = A.offDiag := by
    ext p
    simp only [lo, hi, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
      · exact hp
      · exact hp
    · intro hp
      rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
      · exact Or.inl ⟨hp, hlt⟩
      · exact False.elim ((Finset.mem_offDiag.mp hp).2.2 heq)
      · exact Or.inr ⟨hp, hgt⟩
  have hdisj : Disjoint lo hi := by
    rw [Finset.disjoint_left]
    intro p hlo hhi
    exact (Finset.mem_filter.mp hlo).2.asymm (Finset.mem_filter.mp hhi).2
  have hswap :
      (∏ p ∈ hi, dist p.1 p.2) = ∏ p ∈ lo, dist p.1 p.2 := by
    apply Finset.prod_equiv (Equiv.prodComm α α)
    · intro p
      simp only [lo, hi, Finset.mem_filter, Equiv.prodComm_apply,
        Finset.mem_offDiag]
      constructor <;> rintro ⟨⟨hp, hq, hpq⟩, hlt⟩
      · exact ⟨⟨hq, hp, Ne.symm hpq⟩, hlt⟩
      · exact ⟨⟨hq, hp, Ne.symm hpq⟩, hlt⟩
    · intro p hp
      exact dist_comm p.1 p.2
  rw [distanceProduct, ← hunion, Finset.prod_union hdisj, hswap, ← pow_two,
    unorderedDistanceProduct_eq_prod_lt]

/-- Maximizing the conventional unordered product also maximizes the ordered
off-diagonal product. -/
theorem IsLogFekete.maximizes_distanceProduct {n : ℕ} {A : Finset α}
    (hA : IsLogFekete n A) {B : Finset α} (hB : B.card = n) :
    distanceProduct B ≤ distanceProduct A := by
  rw [distanceProduct_eq_unorderedDistanceProduct_sq,
    distanceProduct_eq_unorderedDistanceProduct_sq]
  exact pow_le_pow_left₀ (unorderedDistanceProduct_pos B).le (hA.2 B hB) 2

/-- Taking the logarithm converts the distance product into the sum of the
off-diagonal logarithms. -/
theorem log_distanceProduct (A : Finset α) :
    Real.log (distanceProduct A) =
      ∑ p ∈ A.offDiag, Real.log (dist p.1 p.2) := by
  rw [distanceProduct, Real.log_prod]
  intro p hp
  exact ne_of_gt (dist_pos_of_mem_offDiag A hp)

/-- The ordered logarithmic energy is the negative logarithm of the ordered
distance product. -/
theorem orderedLogEnergy_eq_neg_log_distanceProduct (A : Finset α) :
    orderedLogEnergy A = -Real.log (distanceProduct A) := by
  rw [orderedLogEnergy, Finset.sum_neg_distrib, log_distanceProduct]

/-- Inserting a new point adds its interaction with every old point in both
orders. -/
theorem orderedLogEnergy_insert [DecidableEq α] (S : Finset α) {z : α} (hz : z ∉ S) :
    orderedLogEnergy (insert z S) =
      orderedLogEnergy S + 2 * pointLogPotential S z := by
  classical
  have h₁ : Disjoint S.offDiag ({z} ×ˢ S) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ hab hcross
    have ha : a ∈ S := (Finset.mem_offDiag.mp hab).1
    have haz : a = z := Finset.mem_singleton.mp (Finset.mem_product.mp hcross).1
    exact hz (haz ▸ ha)
  have h₂ : Disjoint (S.offDiag ∪ ({z} ×ˢ S)) (S ×ˢ {z}) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ hab hcross
      have hb : b ∈ S := (Finset.mem_offDiag.mp hab).2.1
      have hbz : b = z := Finset.mem_singleton.mp (Finset.mem_product.mp hcross).2
      exact hz (hbz ▸ hb)
    · rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ hleft hright
      have haz : a = z := Finset.mem_singleton.mp (Finset.mem_product.mp hleft).1
      have ha : a ∈ S := (Finset.mem_product.mp hright).1
      exact hz (haz ▸ ha)
  rw [orderedLogEnergy, Finset.offDiag_insert hz, Finset.sum_union h₂,
    Finset.sum_union h₁]
  simp only [Finset.sum_product, Finset.sum_singleton]
  have hswap :
      (∑ x ∈ S, -Real.log (dist x z)) =
        ∑ x ∈ S, -Real.log (dist z x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [dist_comm]
  rw [hswap]
  simp [pointLogPotential, orderedLogEnergy, Finset.sum_neg_distrib, two_mul, add_assoc]

/-- Replacing `p` by a new point `z` changes only the two ordered stars
centered at the replaced point. -/
theorem orderedLogEnergy_replace [DecidableEq α] (A : Finset α) {p z : α} (hp : p ∈ A)
    (hz : z ∉ A.erase p) :
    orderedLogEnergy (insert z (A.erase p)) + 2 * pointLogPotential (A.erase p) p =
      orderedLogEnergy A + 2 * pointLogPotential (A.erase p) z := by
  have hnew := orderedLogEnergy_insert (A.erase p) hz
  have hold := orderedLogEnergy_insert (A.erase p) (A.notMem_erase p)
  rw [Finset.insert_erase hp] at hold
  rw [hnew, hold]
  ac_rfl

/-- The ordered energy is the sum, over its first endpoint, of the interaction
with all remaining points. -/
theorem orderedLogEnergy_eq_sum_pointLogPotential_erase [DecidableEq α]
    (A : Finset α) :
    orderedLogEnergy A = ∑ p ∈ A, pointLogPotential (A.erase p) p := by
  have hoff :
      A.offDiag = (A ×ˢ A).filter fun p ↦ p.1 ≠ p.2 := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [orderedLogEnergy, hoff, Finset.sum_filter, Finset.sum_product]
  simp_rw [pointLogPotential, ← Finset.filter_ne' A, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpq : p = q
  · simp [hpq]
  · simp [hpq, Ne.symm hpq]

/-- A uniform upper bound for every point's interaction bounds the total
ordered energy by `n` times that bound. -/
theorem orderedLogEnergy_le_of_pointLogPotential_le [DecidableEq α]
    {n : ℕ} {A : Finset α} (hcard : A.card = n) {c : ℝ}
    (hpot : ∀ p ∈ A, pointLogPotential (A.erase p) p ≤ c) :
    orderedLogEnergy A ≤ (n : ℝ) * c := by
  rw [orderedLogEnergy_eq_sum_pointLogPotential_erase]
  calc
    (∑ p ∈ A, pointLogPotential (A.erase p) p) ≤ ∑ _p ∈ A, c := by
      exact Finset.sum_le_sum fun p hp ↦ hpot p hp
    _ = (n : ℝ) * c := by simp [hcard]

/-- Product maximality implies logarithmic-energy minimality among all
equal-cardinality finite configurations. -/
theorem IsLogFekete.minimizes_orderedLogEnergy {n : ℕ} {A : Finset α}
    (hA : IsLogFekete n A) {B : Finset α} (hB : B.card = n) :
    orderedLogEnergy A ≤ orderedLogEnergy B := by
  rw [orderedLogEnergy_eq_neg_log_distanceProduct,
    orderedLogEnergy_eq_neg_log_distanceProduct]
  apply neg_le_neg
  exact Real.strictMonoOn_log.monotoneOn
    (distanceProduct_pos B) (distanceProduct_pos A) (hA.maximizes_distanceProduct hB)

/-- A Fekete point has no larger interaction with the other points than any
admissible replacement point. -/
theorem IsLogFekete.pointLogPotential_le_replacement [DecidableEq α]
    {n : ℕ} {A : Finset α}
    (hA : IsLogFekete n A) {p z : α} (hp : p ∈ A) (hz : z ∉ A.erase p) :
    pointLogPotential (A.erase p) p ≤ pointLogPotential (A.erase p) z := by
  let B := insert z (A.erase p)
  have hcardB : B.card = n := by
    calc
      B.card = (A.erase p).card + 1 := Finset.card_insert_of_notMem hz
      _ = A.card := Finset.card_erase_add_one hp
      _ = n := hA.1
  have hmin : orderedLogEnergy A ≤ orderedLogEnergy B :=
    hA.minimizes_orderedLogEnergy hcardB
  have hreplace := orderedLogEnergy_replace A hp hz
  dsimp [B] at hmin
  linarith

/-- The finite conclusion needed after averaging the uniform spherical
logarithmic potential: if every deleted configuration has an admissible
replacement whose potential is at most `(n - 1) * c`, then the total ordered
energy is at most `n * (n - 1) * c`. -/
theorem IsLogFekete.orderedLogEnergy_le_of_replacement_average [DecidableEq α]
    {n : ℕ} {A : Finset α} (hA : IsLogFekete n A) {c : ℝ}
    (hreplacement : ∀ p ∈ A, ∃ z : α,
      z ∉ A.erase p ∧ pointLogPotential (A.erase p) z ≤ ((n : ℝ) - 1) * c) :
    orderedLogEnergy A ≤ (n : ℝ) * ((n : ℝ) - 1) * c := by
  rw [mul_assoc]
  apply (orderedLogEnergy_le_of_pointLogPotential_le hA.1)
  intro p hp
  obtain ⟨z, hz, hzpot⟩ := hreplacement p hp
  exact (hA.pointLogPotential_le_replacement hp hz).trans hzpot

/-- Specialization to the normalized spherical logarithmic-potential
constant `1 / 2 - log 2`. -/
theorem IsLogFekete.orderedLogEnergy_le_sphere_constant [DecidableEq α]
    {n : ℕ} {A : Finset α} (hA : IsLogFekete n A)
    (hreplacement : ∀ p ∈ A, ∃ z : α,
      z ∉ A.erase p ∧ pointLogPotential (A.erase p) z ≤
        ((n : ℝ) - 1) * (1 / 2 - Real.log 2)) :
    orderedLogEnergy A ≤
      (n : ℝ) * ((n : ℝ) - 1) * (1 / 2 - Real.log 2) :=
  hA.orderedLogEnergy_le_of_replacement_average hreplacement

/-- Probability-measure averaging supplies the replacement point required by
`orderedLogEnergy_le_sphere_constant`.  On the normalized two-sphere, the two
analytic hypotheses below are the rotationally invariant identity
`∫ x, log (dist x y) = log 2 - 1/2` and integrability of the logarithmic
singularity. -/
theorem IsLogFekete.orderedLogEnergy_le_sphere_constant_of_integral
    [MeasurableSpace α] {n : ℕ} {A : Finset α}
    (hA : IsLogFekete n A) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hlogIntegrable : ∀ y : α,
      MeasureTheory.Integrable (fun x : α ↦ Real.log (dist x y)) μ)
    (hlogIntegral : ∀ y : α,
      (∫ x : α, Real.log (dist x y) ∂μ) = Real.log 2 - 1 / 2)
    (hnull : ∀ S : Finset α, μ (S : Set α) = 0) :
    orderedLogEnergy A ≤
      (n : ℝ) * ((n : ℝ) - 1) * (1 / 2 - Real.log 2) := by
  classical
  apply hA.orderedLogEnergy_le_sphere_constant
  intro p hp
  let S := A.erase p
  have hcardNat : S.card + 1 = n := by
    calc
      S.card + 1 = A.card := Finset.card_erase_add_one hp
      _ = n := hA.1
  have hcardReal : (S.card : ℝ) = (n : ℝ) - 1 := by
    have hcast := congrArg (fun k : ℕ ↦ (k : ℝ)) hcardNat
    norm_num at hcast ⊢
    linarith
  have hpotIntegrable :
      MeasureTheory.Integrable (fun z : α ↦ pointLogPotential S z) μ := by
    simpa only [pointLogPotential, Pi.neg_apply] using
      (MeasureTheory.integrable_finsetSum S fun q _hq ↦ (hlogIntegrable q).neg)
  have hpotIntegral :
      (∫ z : α, pointLogPotential S z ∂μ) =
        ((n : ℝ) - 1) * (1 / 2 - Real.log 2) := by
    change (∫ z : α, ∑ q ∈ S, -Real.log (dist z q) ∂μ) = _
    rw [MeasureTheory.integral_finsetSum]
    · simp_rw [MeasureTheory.integral_neg, hlogIntegral]
      rw [Finset.sum_const, nsmul_eq_mul, hcardReal]
      ring
    · intro q hq
      apply (hlogIntegrable q).neg.congr
      exact Filter.Eventually.of_forall fun z ↦ rfl
  obtain ⟨z, hz, hzle⟩ :=
    MeasureTheory.exists_notMem_null_le_integral hpotIntegrable (hnull S)
  refine ⟨z, ?_, ?_⟩
  · exact hz
  · simpa [hpotIntegral] using hzle

end

end Check991Fekete
