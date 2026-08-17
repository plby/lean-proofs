import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.Hypergraph
import ErdosProblems.Erdos565.Janson

/-!
# Turning finite covers into non-Janson containers

This file is the deterministic analytic bridge in the Campos--Samotij
container argument.  Its input is an *ordinary finite cover* `C` of a
hypergraph `H`.  If the members of `C` have at least two vertices, then every
edge measure on `H` satisfies

`mass H nu ^ 2 <= pWeight C p * Lambda H p nu`.

Consequently, a cover of `p`-weight at most `R` proves that `H` is not
`(p,R)`-Janson.  The last theorem packages this implication so that the finite
cover theorem can be supplied as a theorem-valued parameter; no container
statement is postulated.
-/

open scoped BigOperators

namespace Erdos565
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cover counts every unit of edge mass at least once when its weighted
degrees are summed. -/
theorem mass_le_sum_weightedDegree_of_covers {C H : Hypergraph V}
    (hCH : C.Covers H) (nu : EdgeWeight H) :
    mass H nu <= ∑ c ∈ C, weightedDegree H nu c := by
  rw [mass]
  simp_rw [weightedDegree, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E hEH
  obtain ⟨c, hcC, hcE⟩ := hCH E hEH
  calc
    (nu E : ℝ) = if c ⊆ E then (nu E : ℝ) else 0 := by simp [hcE]
    _ <= ∑ c' ∈ C, if c' ⊆ E then (nu E : ℝ) else 0 := by
      apply Finset.single_le_sum (s := C) (f := fun c' ↦ if c' ⊆ E then (nu E : ℝ) else 0)
      · intro c' hc'C
        positivity
      · exact hcC

/-- The summands indexed by a cover with no zero- or one-element edges occur
among the summands defining the Janson energy. -/
theorem sum_cover_energy_le_Lambda {C H : Hypergraph V} {p : ℝ}
    (hp : 0 <= p) (hcard : ∀ c ∈ C, 2 <= c.card) (nu : EdgeWeight H) :
    (∑ c ∈ C, weightedDegree H nu c ^ 2 / p ^ c.card) <= Lambda H p nu := by
  rw [Lambda]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    simp only [jansonSets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    exact hcard c hc
  · intro c hcj hcC
    exact div_nonneg (sq_nonneg _) (pow_nonneg hp _)

/-- Weighted Cauchy--Schwarz in precisely the form used by the cover-to-Janson
conversion. -/
theorem sq_sum_weightedDegree_le_pWeight_mul_cover_energy
    {C H : Hypergraph V} {p : ℝ} (hp : 0 < p) (nu : EdgeWeight H) :
    (∑ c ∈ C, weightedDegree H nu c) ^ 2 <=
      C.pWeight p *
        (∑ c ∈ C, weightedDegree H nu c ^ 2 / p ^ c.card) := by
  have hcs := FiniteAnalysis.weighted_sum_sq_le C
    (fun c ↦ p ^ c.card)
    (fun c ↦ weightedDegree H nu c / p ^ c.card)
    (fun c _ ↦ (pow_pos hp c.card).le)
  have hlinear :
      (∑ c ∈ C, p ^ c.card * (weightedDegree H nu c / p ^ c.card)) =
        ∑ c ∈ C, weightedDegree H nu c := by
    apply Finset.sum_congr rfl
    intro c hc
    field_simp [ne_of_gt (pow_pos hp c.card)]
  have hquadratic :
      (∑ c ∈ C, p ^ c.card * (weightedDegree H nu c / p ^ c.card) ^ 2) =
        ∑ c ∈ C, weightedDegree H nu c ^ 2 / p ^ c.card := by
    apply Finset.sum_congr rfl
    intro c hc
    field_simp [ne_of_gt (pow_pos hp c.card)]
  rw [hlinear, hquadratic] at hcs
  simpa [pWeight, weight] using hcs

/-- The fundamental cover inequality.  Notice that this is valid for every
nonnegative edge measure, including the zero measure and an empty cover. -/
theorem mass_sq_le_pWeight_mul_Lambda_of_covers {C H : Hypergraph V} {p : ℝ}
    (hp : 0 < p) (hCH : C.Covers H) (hcard : ∀ c ∈ C, 2 <= c.card)
    (nu : EdgeWeight H) :
    mass H nu ^ 2 <= C.pWeight p * Lambda H p nu := by
  have hmass := mass_le_sum_weightedDegree_of_covers hCH nu
  have hsum_nonneg : 0 <= ∑ c ∈ C, weightedDegree H nu c :=
    Finset.sum_nonneg fun c _ ↦ weightedDegree_nonneg H nu c
  have hmass_sq : mass H nu ^ 2 <= (∑ c ∈ C, weightedDegree H nu c) ^ 2 :=
    (sq_le_sq₀ (mass_nonneg H nu) hsum_nonneg).2 hmass
  calc
    mass H nu ^ 2 <= (∑ c ∈ C, weightedDegree H nu c) ^ 2 := hmass_sq
    _ <= C.pWeight p *
        (∑ c ∈ C, weightedDegree H nu c ^ 2 / p ^ c.card) :=
      sq_sum_weightedDegree_le_pWeight_mul_cover_energy hp nu
    _ <= C.pWeight p * Lambda H p nu := by
      exact mul_le_mul_of_nonneg_left
        (sum_cover_energy_le_Lambda hp.le hcard nu) (C.pWeight_nonneg hp.le)

/-- A cover of `p`-weight at most the positive radius rules out the strict
inequality required of a Janson witness. -/
theorem not_isJanson_of_covers_of_pWeight_le {C H : Hypergraph V} {p R : ℝ}
    (hp : 0 < p) (hR : 0 < R) (hCH : C.Covers H)
    (hcard : ∀ c ∈ C, 2 <= c.card) (hweight : C.pWeight p <= R) :
    ¬ H.IsJanson p R := by
  intro hJ
  rcases hJ with hRzero | ⟨nu, hnu⟩
  · exact hR.ne' hRzero
  have hfund := mass_sq_le_pWeight_mul_Lambda_of_covers hp hCH hcard nu
  have hLambda : 0 <= Lambda H p nu := Lambda_nonneg H hp.le nu
  have hmul : C.pWeight p * Lambda H p nu <= R * Lambda H p nu :=
    mul_le_mul_of_nonneg_right hweight hLambda
  have hstrict : R * Lambda H p nu < mass H nu ^ 2 := by
    simpa [mul_comm] using (lt_div_iff₀ hR).mp hnu
  exact (not_lt_of_ge (hfund.trans hmul)) hstrict

/-- The exact rescaling used after applying a finite cover theorem at
`q = p / zeta`: if all cover edges have size at least two, their `p`-weight
gains a factor `zeta^2`. -/
theorem pWeight_le_sq_mul_pWeight_div {C : Hypergraph V} {p zeta : ℝ}
    (hp : 0 <= p) (hzeta : 0 < zeta) (hzeta_one : zeta <= 1)
    (hcard : ∀ c ∈ C, 2 <= c.card) :
    C.pWeight p <= zeta ^ 2 * C.pWeight (p / zeta) := by
  rw [pWeight, pWeight, weight, weight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hzeta_nonneg : 0 <= zeta := hzeta.le
  have hzeta_pow : zeta ^ c.card <= zeta ^ 2 := by
    exact pow_le_pow_of_le_one hzeta_nonneg hzeta_one (hcard c hc)
  calc
    p ^ c.card = zeta ^ c.card * (p / zeta) ^ c.card := by
      rw [← mul_pow]
      field_simp
    _ <= zeta ^ 2 * (p / zeta) ^ c.card := by
      exact mul_le_mul_of_nonneg_right hzeta_pow (pow_nonneg (div_nonneg hp hzeta.le) _)

/-- Abstract output type for a finite cover theorem.  It records only the
parts of the theorem needed in the analytic conversion. -/
structure FiniteCoverOutput (H : Hypergraph V) (I : Finset V) (q : ℝ) where
  container : Finset V
  cover : Hypergraph V
  input_subset : I ⊆ container
  covers : cover.Covers (H.restrict container)
  edge_card : ∀ c ∈ cover, 2 <= c.card
  weight_le : cover.pWeight q <= q * container.card

/-- Convert one finite-cover output into a non-Janson certificate whenever
its container is nonempty.  The nonemptiness premise is necessary: the target
radius is zero on the empty container, and every hypergraph is Janson at
radius zero by convention. -/
theorem FiniteCoverOutput.not_isJanson_rescale
    {H : Hypergraph V} {I : Finset V} {p zeta : ℝ}
    (out : FiniteCoverOutput H I (p / zeta))
    (hp : 0 < p) (hzeta : 0 < zeta) (hzeta_one : zeta <= 1)
    (hX : out.container.Nonempty) :
    ¬ (H.restrict out.container).IsJanson p
      (zeta * p * out.container.card) := by
  have hR : 0 < zeta * p * (out.container.card : ℝ) := by
    have hcard_pos : 0 < out.container.card := Finset.card_pos.mpr hX
    positivity
  apply not_isJanson_of_covers_of_pWeight_le hp hR out.covers out.edge_card
  calc
    out.cover.pWeight p <= zeta ^ 2 * out.cover.pWeight (p / zeta) :=
      pWeight_le_sq_mul_pWeight_div hp.le hzeta hzeta_one out.edge_card
    _ <= zeta ^ 2 * ((p / zeta) * out.container.card) := by
      exact mul_le_mul_of_nonneg_left out.weight_le (sq_nonneg zeta)
    _ = zeta * p * out.container.card := by
      field_simp

/-- A theorem-valued finite-cover input yields Janson-form containers.  This
is the formal deduction used by the main argument: the finite cover theorem is
an explicit parameter `finiteCover`, and the conclusion is derived from it. -/
theorem jansonFormContainers_of_finiteCover
    (H : Hypergraph V) {p zeta : ℝ}
    (hp : 0 < p) (hzeta : 0 < zeta) (hzeta_one : zeta <= 1)
    (finiteCover : ∀ I : Finset V, H.IsIndependent I →
      FiniteCoverOutput H I (p / zeta)) :
    ∀ I : Finset V, H.IsIndependent I →
      ∃ X : Finset V, I ⊆ X ∧
        (X.Nonempty → ¬ (H.restrict X).IsJanson p (zeta * p * X.card)) := by
  intro I hI
  let out := finiteCover I hI
  refine ⟨out.container, out.input_subset, ?_⟩
  intro hX
  exact out.not_isJanson_rescale hp hzeta hzeta_one hX

end Hypergraph
end Erdos565
