import ErdosProblems.Erdos565.Janson
import ErdosProblems.Erdos565.FiniteExpectation
import ErdosProblems.Erdos565.BernoulliSubsets
import Mathlib.Tactic

/-!
# Deterministic algebra for the random restriction argument

This file isolates the algebra in Claims 7.10--7.13 of the proof of the
exponential induced-Ramsey bound.  No probability space is needed here: a
random restriction is represented by an arbitrary nonnegative weight which is
pointwise bounded by a scalar multiple of the original weight.
-/

open scoped BigOperators NNReal

namespace Erdos565
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `v` is fresh for `H` when no edge of `H` contains it. -/
def FreshFor (v : V) (H : Hypergraph V) : Prop :=
  ∀ E ∈ H, v ∉ E

/-- Adjoin the fresh vertex `v` to every edge of `H`. -/
def adjoinVertex (v : V) (H : Hypergraph V) : Hypergraph V :=
  H.image (insert v)

/-- Transport an edge weight to `adjoinVertex v H` by deleting `v` again. -/
def adjoinWeight (v : V) {H : Hypergraph V} (ν : EdgeWeight H) :
    EdgeWeight (adjoinVertex v H) :=
  fun F ↦ ν (F.erase v)

@[simp] lemma mem_adjoinVertex {v : V} {H : Hypergraph V} {F : Finset V} :
    F ∈ adjoinVertex v H ↔ ∃ E ∈ H, insert v E = F := by
  simp [adjoinVertex]

lemma insert_injOn_of_fresh {v : V} {H : Hypergraph V} (hFresh : FreshFor v H) :
    Set.InjOn (insert v) (↑H : Set (Finset V)) := by
  intro E hE F hF hEq
  have hEv : v ∉ E := hFresh E hE
  have hFv : v ∉ F := hFresh F hF
  simpa [Finset.erase_insert hEv, Finset.erase_insert hFv] using
    congrArg (fun A : Finset V ↦ A.erase v) hEq

lemma erase_insert_of_fresh {v : V} {H : Hypergraph V} (hFresh : FreshFor v H)
    {E : Finset V} (hE : E ∈ H) : (insert v E).erase v = E := by
  exact Finset.erase_insert (hFresh E hE)

lemma subset_insert_iff_erase_subset {v : V} {E L : Finset V} :
    L ⊆ insert v E ↔ L.erase v ⊆ E := by
  constructor
  · intro h x hx
    have hxL : x ∈ L := Finset.mem_of_mem_erase hx
    have hxne : x ≠ v := Finset.ne_of_mem_erase hx
    simpa [hxne] using h hxL
  · intro h x hx
    by_cases hxv : x = v
    · simpa [hxv]
    · have hxerase : x ∈ L.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
      exact Finset.mem_insert_of_mem (h hxerase)

@[simp] lemma adjoinWeight_insert {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) (ν : EdgeWeight H) {E : Finset V} (hE : E ∈ H) :
    adjoinWeight v ν (insert v E) = ν E := by
  simp [adjoinWeight, Finset.erase_insert (hFresh E hE)]

/-- Adjoining a fresh vertex preserves total mass. -/
lemma mass_adjoinWeight {v : V} {H : Hypergraph V} (hFresh : FreshFor v H)
    (ν : EdgeWeight H) :
    mass (adjoinVertex v H) (adjoinWeight v ν) = mass H ν := by
  rw [mass, mass, adjoinVertex, Finset.sum_image (insert_injOn_of_fresh hFresh)]
  apply Finset.sum_congr rfl
  intro E hE
  simp [adjoinWeight, Finset.erase_insert (hFresh E hE)]

/-- Claim 7.10: after adjoining a fresh vertex, the degree of `L` is the
degree of `L.erase v` in the original measure. -/
lemma weightedDegree_adjoinWeight {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) (ν : EdgeWeight H) (L : Finset V) :
    weightedDegree (adjoinVertex v H) (adjoinWeight v ν) L =
      weightedDegree H ν (L.erase v) := by
  rw [weightedDegree, weightedDegree, adjoinVertex]
  rw [Finset.filter_image]
  have hInj : Set.InjOn (insert v)
      (↑(H.filter fun E ↦ L ⊆ insert v E) : Set (Finset V)) := by
    intro E hE F hF hEq
    exact insert_injOn_of_fresh hFresh (Finset.mem_filter.mp hE).1
      (Finset.mem_filter.mp hF).1 hEq
  rw [Finset.sum_image hInj]
  apply Finset.sum_congr
  · ext E
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hE, hsub⟩
      exact ⟨hE, subset_insert_iff_erase_subset.mp hsub⟩
    · rintro ⟨hE, hsub⟩
      exact ⟨hE, subset_insert_iff_erase_subset.mpr hsub⟩
  · intro E hE
    simp [adjoinWeight, Finset.erase_insert (hFresh E (Finset.mem_filter.mp hE).1)]

/-- The squared singleton-degree sum.  This is named locally so that the
random-restriction algebra depends only on `Janson.lean`. -/
def singletonEnergy (H : Hypergraph V) (ν : EdgeWeight H) : ℝ :=
  ∑ u : V, weightedDegree H ν {u} ^ 2

lemma singletonEnergy_nonneg (H : Hypergraph V) (ν : EdgeWeight H) :
    0 ≤ singletonEnergy H ν := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma weightedDegree_eq_zero_of_fresh_mem {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) (ν : EdgeWeight H) {L : Finset V} (hvL : v ∈ L) :
    weightedDegree H ν L = 0 := by
  rw [weightedDegree]
  apply Finset.sum_eq_zero
  intro E hE
  have hsub : L ⊆ E := (Finset.mem_filter.mp hE).2
  exact (hFresh E (Finset.mem_filter.mp hE).1 (hsub hvL)).elim

lemma singletonDegree_eq_zero_of_fresh {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) (ν : EdgeWeight H) :
    weightedDegree H ν {v} = 0 := by
  exact weightedDegree_eq_zero_of_fresh_mem hFresh ν (Finset.mem_singleton_self v)

private noncomputable def lambdaTerm (H : Hypergraph V) (p : ℝ) (ν : EdgeWeight H)
    (L : Finset V) : ℝ :=
  weightedDegree H ν L ^ 2 / p ^ L.card

private lemma lambda_eq_sum_term (H : Hypergraph V) (p : ℝ) (ν : EdgeWeight H) :
    Lambda H p ν = ∑ L ∈ jansonSets, lambdaTerm H p ν L := by
  rfl

private lemma lambda_sum_without_fresh {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) (p : ℝ) (ν : EdgeWeight H) :
    (∑ L ∈ jansonSets with v ∉ L, lambdaTerm H p ν L) = Lambda H p ν := by
  rw [lambda_eq_sum_term]
  rw [← Finset.sum_filter_add_sum_filter_not jansonSets (fun L ↦ v ∈ L)
    (lambdaTerm H p ν)]
  have hz : (∑ L ∈ jansonSets with v ∈ L, lambdaTerm H p ν L) = 0 := by
    apply Finset.sum_eq_zero
    intro L hL
    have hvL : v ∈ L := (Finset.mem_filter.mp hL).2
    simp [lambdaTerm, weightedDegree_eq_zero_of_fresh_mem hFresh ν hvL]
  rw [hz, zero_add]

private lemma adjoin_sum_without_fresh {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) (p : ℝ) (ν : EdgeWeight H) :
    (∑ L ∈ jansonSets with v ∉ L,
      lambdaTerm (adjoinVertex v H) p (adjoinWeight v ν) L) = Lambda H p ν := by
  rw [← lambda_sum_without_fresh hFresh p ν]
  apply Finset.sum_congr rfl
  intro L hL
  have hvL : v ∉ L := (Finset.mem_filter.mp hL).2
  simp only [lambdaTerm, weightedDegree_adjoinWeight hFresh]
  rw [Finset.erase_eq_self.mpr hvL]

private def positiveSetsWithout (v : V) : Finset (Finset V) :=
  (Finset.univ.erase v).powerset.filter fun K ↦ 1 ≤ K.card

@[simp] private lemma mem_positiveSetsWithout {v : V} {K : Finset V} :
    K ∈ positiveSetsWithout v ↔ K ⊆ Finset.univ.erase v ∧ 1 ≤ K.card := by
  simp [positiveSetsWithout]

private lemma not_mem_of_mem_positiveSetsWithout {v : V} {K : Finset V}
    (hK : K ∈ positiveSetsWithout v) : v ∉ K := by
  intro hvK
  exact Finset.notMem_erase v Finset.univ ((mem_positiveSetsWithout.mp hK).1 hvK)

private lemma adjoin_sum_with_fresh {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) {p : ℝ} (hp : p ≠ 0) (ν : EdgeWeight H) :
    (∑ L ∈ jansonSets with v ∈ L,
      lambdaTerm (adjoinVertex v H) p (adjoinWeight v ν) L) =
      ∑ K ∈ positiveSetsWithout v,
        weightedDegree H ν K ^ 2 / p ^ (K.card + 1) := by
  let source := jansonSets.filter fun L ↦ v ∈ L
  let target := positiveSetsWithout v
  change (∑ L ∈ source,
      lambdaTerm (adjoinVertex v H) p (adjoinWeight v ν) L) =
    ∑ K ∈ target, weightedDegree H ν K ^ 2 / p ^ (K.card + 1)
  apply Finset.sum_bij (fun L _ ↦ L.erase v)
  · intro L hL
    have hs := Finset.mem_filter.mp hL
    have hvL : v ∈ L := hs.2
    have hcard : 2 ≤ L.card := (Finset.mem_filter.mp hs.1).2
    have hsub : L ⊆ Finset.univ := (Finset.mem_powerset.mp
      (Finset.mem_filter.mp hs.1).1)
    rw [mem_positiveSetsWithout]
    constructor
    · intro x hx
      rw [Finset.mem_erase]
      exact ⟨Finset.ne_of_mem_erase hx, Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem hvL]
      omega
  · intro L hL M hM hEq
    have hvL : v ∈ L := (Finset.mem_filter.mp hL).2
    have hvM : v ∈ M := (Finset.mem_filter.mp hM).2
    rw [← Finset.insert_erase hvL, ← Finset.insert_erase hvM, hEq]
  · intro K hK
    have hvK : v ∉ K := not_mem_of_mem_positiveSetsWithout hK
    refine ⟨insert v K, ?_, Finset.erase_insert hvK⟩
    rw [Finset.mem_filter]
    constructor
    · simp only [jansonSets, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact Finset.subset_univ _
      · rw [Finset.card_insert_of_notMem hvK]
        exact Nat.add_le_add_right (mem_positiveSetsWithout.mp hK).2 1
    · exact Finset.mem_insert_self v K
  · intro L hL
    have hvL : v ∈ L := (Finset.mem_filter.mp hL).2
    simp only [lambdaTerm, weightedDegree_adjoinWeight hFresh]
    rw [Finset.card_erase_add_one hvL]

private lemma positive_large_eq_janson_without (v : V) :
    (positiveSetsWithout v).filter (fun K ↦ K.card ≠ 1) =
      jansonSets.filter (fun K ↦ v ∉ K) := by
  ext K
  simp only [Finset.mem_filter, mem_positiveSetsWithout]
  simp only [jansonSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hsub, hpos⟩, hne⟩
    have hvK : v ∉ K := by
      intro hvK
      exact Finset.notMem_erase v Finset.univ (hsub hvK)
    exact ⟨⟨Finset.subset_univ _, by omega⟩, hvK⟩
  · rintro ⟨⟨_, htwo⟩, hvK⟩
    constructor
    · constructor
      · intro x hx
        exact Finset.mem_erase.mpr ⟨fun hxv ↦ hvK (hxv ▸ hx), Finset.mem_univ x⟩
      · omega
    · omega

private lemma positive_large_sum {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) {p : ℝ} (hp : p ≠ 0) (ν : EdgeWeight H) :
    (∑ K ∈ positiveSetsWithout v with K.card ≠ 1,
      weightedDegree H ν K ^ 2 / p ^ (K.card + 1)) =
      p⁻¹ * Lambda H p ν := by
  rw [positive_large_eq_janson_without]
  rw [← lambda_sum_without_fresh hFresh p ν]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  simp only [lambdaTerm]
  rw [pow_succ]
  field_simp
  <;> ring

private lemma positive_singleton_sum {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) {p : ℝ} (hp : p ≠ 0) (ν : EdgeWeight H) :
    (∑ K ∈ positiveSetsWithout v with K.card = 1,
      weightedDegree H ν K ^ 2 / p ^ (K.card + 1)) =
      (p ^ 2)⁻¹ * singletonEnergy H ν := by
  let source := (positiveSetsWithout v).filter fun K ↦ K.card = 1
  let target := Finset.univ.erase v
  have hsum : (∑ K ∈ source,
      weightedDegree H ν K ^ 2 / p ^ (K.card + 1)) =
      ∑ u ∈ target, weightedDegree H ν {u} ^ 2 / p ^ 2 := by
    apply Finset.sum_bij (fun K hK ↦ (Finset.card_eq_one.mp
      (Finset.mem_filter.mp hK).2).choose)
    · intro K hK
      let u := (Finset.card_eq_one.mp (Finset.mem_filter.mp hK).2).choose
      have hKu : K = {u} :=
        (Finset.card_eq_one.mp (Finset.mem_filter.mp hK).2).choose_spec
      have hKpos : K ∈ positiveSetsWithout v := (Finset.mem_filter.mp hK).1
      have hvK : v ∉ K := not_mem_of_mem_positiveSetsWithout hKpos
      rw [Finset.mem_erase]
      exact ⟨fun huv ↦ hvK (hKu ▸ huv ▸ Finset.mem_singleton_self v),
        Finset.mem_univ u⟩
    · intro K hK L hL hEq
      have hKone := (Finset.card_eq_one.mp (Finset.mem_filter.mp hK).2).choose_spec
      have hLone := (Finset.card_eq_one.mp (Finset.mem_filter.mp hL).2).choose_spec
      rw [hKone, hLone, hEq]
    · intro u hu
      have huv : u ≠ v := (Finset.mem_erase.mp hu).1
      refine ⟨{u}, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [mem_positiveSetsWithout]
          exact ⟨by
            intro x hx
            have hxu : x = u := Finset.mem_singleton.mp hx
            simpa [hxu, huv] using hu,
            by simp⟩
        · simp
      · simp
    · intro K hK
      have hKone := (Finset.card_eq_one.mp (Finset.mem_filter.mp hK).2).choose_spec
      have hdegree : weightedDegree H ν K = weightedDegree H ν
          {(Finset.card_eq_one.mp (Finset.mem_filter.mp hK).2).choose} := by
        exact congrArg (weightedDegree H ν) hKone
      have hcard : K.card + 1 = 2 := by
        rw [hKone]
        simp
      rw [hdegree, hcard]
  change (∑ K ∈ source,
      weightedDegree H ν K ^ 2 / p ^ (K.card + 1)) = _
  rw [hsum, singletonEnergy]
  change (∑ u ∈ Finset.univ.erase v,
      weightedDegree H ν {u} ^ 2 / p ^ 2) =
    (p ^ 2)⁻¹ * ∑ u ∈ Finset.univ, weightedDegree H ν {u} ^ 2
  have hzero : weightedDegree H ν {v} ^ 2 / p ^ 2 = 0 := by
    rw [singletonDegree_eq_zero_of_fresh hFresh ν]
    simp
  rw [Finset.sum_erase (s := Finset.univ) (a := v) hzero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  field_simp
  <;> ring

private lemma positive_sum_expansion {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) {p : ℝ} (hp : p ≠ 0) (ν : EdgeWeight H) :
    (∑ K ∈ positiveSetsWithout v,
      weightedDegree H ν K ^ 2 / p ^ (K.card + 1)) =
      p⁻¹ * Lambda H p ν + (p ^ 2)⁻¹ * singletonEnergy H ν := by
  rw [← Finset.sum_filter_add_sum_filter_not (positiveSetsWithout v)
    (fun K ↦ K.card = 1)
    (fun K ↦ weightedDegree H ν K ^ 2 / p ^ (K.card + 1))]
  rw [positive_singleton_sum hFresh hp ν, positive_large_sum hFresh hp ν]
  ring

/-- Claim 7.11: exact Janson-energy expansion after adjoining a fresh
vertex to every edge. -/
theorem Lambda_adjoinWeight {v : V} {H : Hypergraph V}
    (hFresh : FreshFor v H) {p : ℝ} (hp : p ≠ 0) (ν : EdgeWeight H) :
    Lambda (adjoinVertex v H) p (adjoinWeight v ν) =
      (1 + p⁻¹) * Lambda H p ν + (p ^ 2)⁻¹ * singletonEnergy H ν := by
  rw [lambda_eq_sum_term]
  rw [← Finset.sum_filter_add_sum_filter_not jansonSets (fun L ↦ v ∈ L)
    (lambdaTerm (adjoinVertex v H) p (adjoinWeight v ν))]
  rw [adjoin_sum_with_fresh hFresh hp ν, adjoin_sum_without_fresh hFresh p ν]
  rw [positive_sum_expansion hFresh hp ν]
  ring

/-! ## Pointwise domination -/

lemma mass_le_of_pointwise {H : Hypergraph V} {μ ν : EdgeWeight H} {c : ℝ}
    (hpoint : ∀ E ∈ H, (μ E : ℝ) ≤ c * (ν E : ℝ)) :
    mass H μ ≤ c * mass H ν := by
  rw [mass, mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun E hE ↦ hpoint E hE

lemma weightedDegree_le_of_pointwise {H : Hypergraph V} {μ ν : EdgeWeight H} {c : ℝ}
    (hpoint : ∀ E ∈ H, (μ E : ℝ) ≤ c * (ν E : ℝ))
    (L : Finset V) :
    weightedDegree H μ L ≤ c * weightedDegree H ν L := by
  rw [weightedDegree, weightedDegree, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro E hE
  exact hpoint E (Finset.mem_filter.mp hE).1

/-- A pointwise scalar bound squares in the Janson energy. -/
lemma Lambda_le_of_pointwise {H : Hypergraph V} {μ ν : EdgeWeight H} {c p : ℝ}
    (hp : 0 < p) (hc : 0 ≤ c)
    (hpoint : ∀ E ∈ H, (μ E : ℝ) ≤ c * (ν E : ℝ)) :
    Lambda H p μ ≤ c ^ 2 * Lambda H p ν := by
  rw [Lambda, Lambda, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro L hL
  have hdeg := weightedDegree_le_of_pointwise hpoint L
  have hμ0 := weightedDegree_nonneg H μ L
  have hν0 := weightedDegree_nonneg H ν L
  have hsq : weightedDegree H μ L ^ 2 ≤
      c ^ 2 * weightedDegree H ν L ^ 2 := by
    nlinarith
  have hden : 0 < p ^ L.card := pow_pos hp _
  calc
    weightedDegree H μ L ^ 2 / p ^ L.card ≤
        (c ^ 2 * weightedDegree H ν L ^ 2) / p ^ L.card :=
      div_le_div_of_nonneg_right hsq hden.le
    _ = c ^ 2 * (weightedDegree H ν L ^ 2 / p ^ L.card) := by ring

lemma singletonEnergy_le_of_pointwise {H : Hypergraph V}
    {μ ν : EdgeWeight H} {c : ℝ} (hc : 0 ≤ c)
    (hpoint : ∀ E ∈ H, (μ E : ℝ) ≤ c * (ν E : ℝ)) :
    singletonEnergy H μ ≤ c ^ 2 * singletonEnergy H ν := by
  rw [singletonEnergy, singletonEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hdeg := weightedDegree_le_of_pointwise hpoint {u}
  have hμ0 := weightedDegree_nonneg H μ {u}
  have hν0 := weightedDegree_nonneg H ν {u}
  nlinarith

/-! ## Inverse-probability random restriction -/

section Restriction

variable {Omega : Type*} [DecidableEq Omega]

/-- The inverse-probability edge weight at one outcome.  The use of `NNReal`
ensures it is a legitimate `EdgeWeight` without side conditions. -/
noncomputable def inverseProbabilityWeight {H : Hypergraph V}
    (gamma : NNReal) (ν : EdgeWeight H) (probability : Finset V → NNReal)
    (edgeEvent : Finset V → Finset Omega) (omega : Omega) : EdgeWeight H :=
  fun E ↦ gamma * ν E * (if omega ∈ edgeEvent E then 1 else 0) / probability E

@[simp] lemma inverseProbabilityWeight_apply {H : Hypergraph V}
    (gamma : NNReal) (ν : EdgeWeight H) (probability : Finset V → NNReal)
    (edgeEvent : Finset V → Finset Omega) (omega : Omega) (E : Finset V) :
    inverseProbabilityWeight gamma ν probability edgeEvent omega E =
      gamma * ν E * (if omega ∈ edgeEvent E then 1 else 0) / probability E := by
  rfl

/-- Claim 7.12, pointwise form: a uniform lower bound `a` on all inclusion
probabilities gives domination by `gamma / a`. -/
lemma inverseProbabilityWeight_pointwise {H : Hypergraph V}
    {gamma a : NNReal} {ν : EdgeWeight H} {probability : Finset V → NNReal}
    {edgeEvent : Finset V → Finset Omega} {omega : Omega}
    (ha : 0 < a) (hprob : ∀ E ∈ H, a ≤ probability E) :
    ∀ E ∈ H,
      (inverseProbabilityWeight gamma ν probability edgeEvent omega E : ℝ) ≤
        ((gamma : ℝ) / (a : ℝ)) * (ν E : ℝ) := by
  intro E hE
  by_cases hkeep : omega ∈ edgeEvent E
  · simp only [inverseProbabilityWeight_apply, hkeep, if_pos, mul_one,
      NNReal.coe_div, NNReal.coe_mul]
    have haR : 0 < (a : ℝ) := NNReal.coe_pos.mpr ha
    have hpR : (a : ℝ) ≤ (probability E : ℝ) := by exact_mod_cast hprob E hE
    have hnum : 0 ≤ (gamma : ℝ) * (ν E : ℝ) := mul_nonneg
      (NNReal.coe_nonneg gamma) (NNReal.coe_nonneg (ν E))
    calc
      (gamma : ℝ) * (ν E : ℝ) / (probability E : ℝ) ≤
          (gamma : ℝ) * (ν E : ℝ) / (a : ℝ) :=
        div_le_div_of_nonneg_left hnum haR hpR
      _ = ((gamma : ℝ) / (a : ℝ)) * (ν E : ℝ) := by ring
  · have hnonneg : 0 ≤ ((gamma : ℝ) / (a : ℝ)) * (ν E : ℝ) :=
      mul_nonneg (div_nonneg (NNReal.coe_nonneg gamma) (NNReal.coe_nonneg a))
        (NNReal.coe_nonneg (ν E))
    simpa [inverseProbabilityWeight_apply, hkeep] using hnonneg

lemma Lambda_inverseProbabilityWeight_le {H : Hypergraph V}
    {gamma a : NNReal} {ν : EdgeWeight H} {probability : Finset V → NNReal}
    {edgeEvent : Finset V → Finset Omega} {omega : Omega} {p : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hprob : ∀ E ∈ H, a ≤ probability E) :
    Lambda H p (inverseProbabilityWeight gamma ν probability edgeEvent omega) ≤
      ((gamma : ℝ) / (a : ℝ)) ^ 2 * Lambda H p ν := by
  exact Lambda_le_of_pointwise hp (div_nonneg (NNReal.coe_nonneg gamma)
    (NNReal.coe_nonneg a)) (inverseProbabilityWeight_pointwise ha hprob)

lemma singletonEnergy_inverseProbabilityWeight_le {H : Hypergraph V}
    {gamma a : NNReal} {ν : EdgeWeight H} {probability : Finset V → NNReal}
    {edgeEvent : Finset V → Finset Omega} {omega : Omega}
    (ha : 0 < a) (hprob : ∀ E ∈ H, a ≤ probability E) :
    singletonEnergy H (inverseProbabilityWeight gamma ν probability edgeEvent omega) ≤
      ((gamma : ℝ) / (a : ℝ)) ^ 2 * singletonEnergy H ν := by
  exact singletonEnergy_le_of_pointwise
    (div_nonneg (NNReal.coe_nonneg gamma) (NNReal.coe_nonneg a))
    (inverseProbabilityWeight_pointwise ha hprob)

/-- Claim 7.10, edgewise unbiasedness: inverse-probability reweighting
has expected value `gamma * nu E`. -/
theorem conditionalExpectation_inverseProbabilityWeight_apply
    {H : Hypergraph V} (gamma : NNReal) (ν : EdgeWeight H)
    (probability : Finset V → NNReal) (edgeEvent : Finset V → Finset Omega)
    (outcomes given : Finset Omega) (sampleWeight : Omega → ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given sampleWeight ≠ 0)
    (hprob : ∀ E,
      FiniteExpectation.conditionalProbability outcomes given (edgeEvent E) sampleWeight =
        (probability E : ℝ))
    (hprob0 : ∀ E, probability E ≠ 0) (E : Finset V) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega ↦
          (inverseProbabilityWeight gamma ν probability edgeEvent omega E : ℝ)) =
      (gamma : ℝ) * (ν E : ℝ) := by
  have hevent0 : FiniteExpectation.conditionalProbability outcomes given
      (edgeEvent E) sampleWeight ≠ 0 := by
    rw [hprob E]
    exact_mod_cast hprob0 E
  have h := FiniteExpectation.conditionalExpectation_unbiased_indicator
    outcomes given (edgeEvent E) sampleWeight
      ((gamma : ℝ) * (ν E : ℝ)) hmass hevent0
  rw [hprob E] at h
  have hfun : (fun omega ↦
      (inverseProbabilityWeight gamma ν probability edgeEvent omega E : ℝ)) =
      (fun omega ↦ (gamma : ℝ) * (ν E : ℝ) *
        (if omega ∈ edgeEvent E then 1 else 0) / (probability E : ℝ)) := by
    funext omega
    by_cases homega : omega ∈ edgeEvent E <;>
      simp [inverseProbabilityWeight, homega]
  rw [hfun]
  exact h

/-- Expected total mass of the random restriction. -/
theorem conditionalExpectation_mass_inverseProbabilityWeight
    {H : Hypergraph V} (gamma : NNReal) (ν : EdgeWeight H)
    (probability : Finset V → NNReal) (edgeEvent : Finset V → Finset Omega)
    (outcomes given : Finset Omega) (sampleWeight : Omega → ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given sampleWeight ≠ 0)
    (hprob : ∀ E,
      FiniteExpectation.conditionalProbability outcomes given (edgeEvent E) sampleWeight =
        (probability E : ℝ))
    (hprob0 : ∀ E, probability E ≠ 0) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega ↦ mass H
          (inverseProbabilityWeight gamma ν probability edgeEvent omega)) =
      (gamma : ℝ) * mass H ν := by
  simp only [mass]
  rw [FiniteExpectation.conditionalExpectation_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  exact conditionalExpectation_inverseProbabilityWeight_apply gamma ν probability
    edgeEvent outcomes given sampleWeight hmass hprob hprob0 E

/-- Expected weighted degrees are unbiased simultaneously for every finite
set `L`. -/
theorem conditionalExpectation_weightedDegree_inverseProbabilityWeight
    {H : Hypergraph V} (gamma : NNReal) (ν : EdgeWeight H)
    (probability : Finset V → NNReal) (edgeEvent : Finset V → Finset Omega)
    (outcomes given : Finset Omega) (sampleWeight : Omega → ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given sampleWeight ≠ 0)
    (hprob : ∀ E,
      FiniteExpectation.conditionalProbability outcomes given (edgeEvent E) sampleWeight =
        (probability E : ℝ))
    (hprob0 : ∀ E, probability E ≠ 0) (L : Finset V) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega ↦ weightedDegree H
          (inverseProbabilityWeight gamma ν probability edgeEvent omega) L) =
      (gamma : ℝ) * weightedDegree H ν L := by
  simp only [weightedDegree]
  rw [FiniteExpectation.conditionalExpectation_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  exact conditionalExpectation_inverseProbabilityWeight_apply gamma ν probability
    edgeEvent outcomes given sampleWeight hmass hprob hprob0 E

/-- The bilinear term in the expansion of `Lambda (rho + mu)`. -/
noncomputable def lambdaCross (H : Hypergraph V) (p : ℝ)
    (ρ μ : EdgeWeight H) : ℝ :=
  ∑ L ∈ jansonSets,
    (p ^ L.card)⁻¹ * weightedDegree H ρ L * weightedDegree H μ L

/-- Exact quadratic expansion of the Janson energy. -/
lemma Lambda_add_eq (H : Hypergraph V) {p : ℝ} (ρ μ : EdgeWeight H) :
    Lambda H p (ρ + μ) =
      Lambda H p ρ + 2 * lambdaCross H p ρ μ + Lambda H p μ := by
  simp only [Lambda, lambdaCross, weightedDegree_add]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro L hL
  ring

lemma lambdaCross_nonneg (H : Hypergraph V) {p : ℝ} (hp : 0 ≤ p)
    (ρ μ : EdgeWeight H) : 0 ≤ lambdaCross H p ρ μ := by
  apply Finset.sum_nonneg
  intro L hL
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg hp _)) (weightedDegree_nonneg H ρ L))
    (weightedDegree_nonneg H μ L)

/-- Weighted Cauchy--Schwarz for the bilinear part of `Lambda`. -/
lemma lambdaCross_sq_le (H : Hypergraph V) {p : ℝ} (hp : 0 < p)
    (ρ μ : EdgeWeight H) :
    lambdaCross H p ρ μ ^ 2 ≤ Lambda H p ρ * Lambda H p μ := by
  have h := FiniteAnalysis.weighted_cauchy_schwarz jansonSets
    (fun L ↦ (p ^ L.card)⁻¹)
    (fun L ↦ weightedDegree H ρ L)
    (fun L ↦ weightedDegree H μ L)
    (fun L _ ↦ inv_nonneg.mpr (pow_nonneg hp.le _))
  simpa only [lambdaCross, Lambda, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using h

lemma lambdaCross_lt_one (H : Hypergraph V) {p : ℝ} (hp : 0 < p)
    (ρ μ : EdgeWeight H) (hρ : Lambda H p ρ < 1) (hμ : Lambda H p μ < 1) :
    lambdaCross H p ρ μ < 1 := by
  have hρ0 := Lambda_nonneg H hp.le ρ
  have hμ0 := Lambda_nonneg H hp.le μ
  have hcross0 := lambdaCross_nonneg H hp.le ρ μ
  have hsq := lambdaCross_sq_le H hp ρ μ
  have hprod : Lambda H p ρ * Lambda H p μ < 1 := by nlinarith
  nlinarith

/-- Claim 7.13: the expected cross term is obtained simply by replacing
each random degree by its unbiased expectation. -/
theorem conditionalExpectation_lambdaCross_inverseProbabilityWeight
    {H : Hypergraph V} {p : ℝ} (ρ : EdgeWeight H)
    (gamma : NNReal) (ν : EdgeWeight H)
    (probability : Finset V → NNReal) (edgeEvent : Finset V → Finset Omega)
    (outcomes given : Finset Omega) (sampleWeight : Omega → ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given sampleWeight ≠ 0)
    (hprob : ∀ E,
      FiniteExpectation.conditionalProbability outcomes given (edgeEvent E) sampleWeight =
        (probability E : ℝ))
    (hprob0 : ∀ E, probability E ≠ 0) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega ↦ lambdaCross H p ρ
          (inverseProbabilityWeight gamma ν probability edgeEvent omega)) =
      (gamma : ℝ) * lambdaCross H p ρ ν := by
  simp only [lambdaCross]
  apply FiniteExpectation.conditionalExpectation_crossDegree_sum_of_unbiased
    outcomes given sampleWeight jansonSets
      (fun L ↦ (p ^ L.card)⁻¹)
      (fun L ↦ weightedDegree H ρ L)
      (fun L ↦ weightedDegree H ν L)
      (fun omega L ↦ weightedDegree H
        (inverseProbabilityWeight gamma ν probability edgeEvent omega) L)
      (gamma : ℝ)
  intro L hL
  exact conditionalExpectation_weightedDegree_inverseProbabilityWeight gamma ν
    probability edgeEvent outcomes given sampleWeight hmass hprob hprob0 L

/-- Conditional expectation of a constant under nonzero conditioning mass. -/
private lemma conditionalExpectation_const
    (outcomes given : Finset Omega) (sampleWeight : Omega → ℝ) (c : ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given sampleWeight ≠ 0) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
      (fun _ ↦ c) = c := by
  unfold FiniteExpectation.conditionalExpectation FiniteExpectation.expectation
  unfold FiniteExpectation.conditioningMass
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c hmass

/-- Expected version of Claim 7.12. -/
theorem conditionalExpectation_Lambda_inverseProbabilityWeight_le
    {H : Hypergraph V} {gamma a : NNReal} {ν : EdgeWeight H}
    {probability : Finset V → NNReal} {edgeEvent : Finset V → Finset Omega}
    {outcomes given : Finset Omega} {sampleWeight : Omega → ℝ} {p : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hprobLower : ∀ E ∈ H, a ≤ probability E)
    (hweight : ∀ omega ∈ outcomes, 0 ≤ sampleWeight omega)
    (hmass : 0 < FiniteExpectation.conditioningMass outcomes given sampleWeight) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega ↦ Lambda H p
          (inverseProbabilityWeight gamma ν probability edgeEvent omega)) ≤
      ((gamma : ℝ) / (a : ℝ)) ^ 2 * Lambda H p ν := by
  calc
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega ↦ Lambda H p
          (inverseProbabilityWeight gamma ν probability edgeEvent omega)) ≤
        FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun _ ↦ ((gamma : ℝ) / (a : ℝ)) ^ 2 * Lambda H p ν) := by
      apply FiniteExpectation.conditionalExpectation_mono
        outcomes given sampleWeight _ _ hweight hmass
      intro omega homega
      exact Lambda_inverseProbabilityWeight_le hp ha hprobLower
    _ = ((gamma : ℝ) / (a : ℝ)) ^ 2 * Lambda H p ν :=
      conditionalExpectation_const outcomes given sampleWeight _ hmass.ne'

end Restriction

/-! ## The numerical estimate in Claim 7.13 -/

/-- The elementary bracket estimate behind (19i).  The parameter `t` is
`r * s^2` in the application. -/
lemma acdfm_restriction_bracket_le {p t : ℝ}
    (hp : 0 < p) (ht : 1 ≤ t) (hsmall : 2048 * t * p ≤ 1) :
    1 + p⁻¹ + 256 * t * p⁻¹ ≤ (2 * p ^ 2)⁻¹ := by
  have htp : p ≤ t * p := by nlinarith
  have hp2048 : p ≤ 1 / 2048 := by nlinarith
  have hp1 : p ≤ 1 := hp2048.trans (by norm_num)
  have hpsq : p ^ 2 ≤ p := by nlinarith
  have hterm : 256 * t * p ≤ 1 / 8 := by nlinarith
  rw [inv_eq_one_div, inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * p ^ 2)).2
  field_simp [hp.ne']
  nlinarith

/-- The paper's hypothesis `p <= q / (2^11 r s^2)`, with `q <= 1`,
implies the cross-multiplied smallness used above. -/
lemma acdfm_smallness_of_p_le {p q t : ℝ}
    (hp : 0 < p) (hq : q ≤ 1) (ht : 1 ≤ t)
    (hpq : p ≤ q / (2048 * t)) :
    2048 * t * p ≤ 1 := by
  have hden : 0 < 2048 * t := mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) ht)
  have hmul := (le_div_iff₀ hden).mp hpq
  calc
    2048 * t * p = p * (2048 * t) := by ring
    _ ≤ q := hmul
    _ ≤ 1 := hq

/-- Claim 7.13, final deterministic estimate.  It is stated with the exact
inputs produced by the preceding claims: a pointwise inverse-probability
restriction, unit Janson energy, the singleton-degree estimate, and
`sqrtEta = p^2 a^2`. -/
theorem Lambda_adjoin_inverseProbabilityWeight_lt
    {Omega : Type*} [DecidableEq Omega]
    {v : V} {H : Hypergraph V} (hFresh : FreshFor v H)
    {p t sqrtEta : ℝ} {gamma a : NNReal}
    {ν : EdgeWeight H} {probability : Finset V → NNReal}
    {edgeEvent : Finset V → Finset Omega} {omega : Omega}
    (hp : 0 < p) (ht : 1 ≤ t) (hsmall : 2048 * t * p ≤ 1)
    (hgamma : 0 < gamma) (ha : 0 < a) (hsqrtEta : 0 < sqrtEta)
    (hsqrt : sqrtEta = p ^ 2 * (a : ℝ) ^ 2)
    (hLambda : Lambda H p ν < 1)
    (hsingleton : singletonEnergy H ν ≤ 256 * t * p)
    (hprob : ∀ E ∈ H, a ≤ probability E) :
    Lambda (adjoinVertex v H) p
        (adjoinWeight v
          (inverseProbabilityWeight gamma ν probability edgeEvent omega)) <
      (gamma : ℝ) ^ 2 / (2 * sqrtEta) := by
  let μ := inverseProbabilityWeight gamma ν probability edgeEvent omega
  let c : ℝ := (gamma : ℝ) / (a : ℝ)
  have hc : 0 < c := div_pos (NNReal.coe_pos.mpr hgamma) (NNReal.coe_pos.mpr ha)
  have hLle : Lambda H p μ ≤ c ^ 2 * Lambda H p ν := by
    exact Lambda_inverseProbabilityWeight_le hp ha hprob
  have hLlt : Lambda H p μ < c ^ 2 := by
    exact hLle.trans_lt (by
      simpa using mul_lt_mul_of_pos_left hLambda (sq_pos_of_pos hc))
  have hQle : singletonEnergy H μ ≤ c ^ 2 * singletonEnergy H ν := by
    exact singletonEnergy_inverseProbabilityWeight_le ha hprob
  have hQ : singletonEnergy H μ ≤ c ^ 2 * (256 * t * p) :=
    hQle.trans (mul_le_mul_of_nonneg_left hsingleton (sq_nonneg c))
  have hcoef : 0 < 1 + p⁻¹ := by positivity
  have hinvSq : 0 ≤ (p ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg p)
  rw [Lambda_adjoinWeight hFresh hp.ne' μ]
  calc
    (1 + p⁻¹) * Lambda H p μ +
          (p ^ 2)⁻¹ * singletonEnergy H μ <
        (1 + p⁻¹) * c ^ 2 +
          (p ^ 2)⁻¹ * (c ^ 2 * (256 * t * p)) :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hLlt hcoef)
        (mul_le_mul_of_nonneg_left hQ hinvSq)
    _ = c ^ 2 * (1 + p⁻¹ + 256 * t * p⁻¹) := by
      field_simp [hp.ne']
    _ ≤ c ^ 2 * (2 * p ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (acdfm_restriction_bracket_le hp ht hsmall)
        (sq_nonneg c)
    _ = (gamma : ℝ) ^ 2 / (2 * sqrtEta) := by
      rw [hsqrt]
      dsimp [c]
      field_simp [hp.ne', (NNReal.coe_pos.mpr ha).ne']

end Hypergraph
end Erdos565
