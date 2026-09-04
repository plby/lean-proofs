import ErdosProblems.Erdos720.DFS
import Mathlib.Probability.Distributions.SetBernoulli

open Filter Finset
open MeasureTheory ProbabilityTheory unitInterval
open scoped SimpleGraph Topology ENNReal

noncomputable section

namespace Erdos720

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma setBernoulli_superset_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | (↑t : Set ι) ⊆ s} = toNNReal p ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop => {i | q i}) ⁻¹' {s : Set ι | (↑t : Set ι) ⊆ s}) =
        ((↑t : Set ι).pi fun _ => ({True} : Set Prop)) := by
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

lemma setBernoulli_disjoint_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | Disjoint (↑t : Set ι) s} =
      toNNReal (σ p) ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop => {i | q i}) ⁻¹' {s : Set ι |
        Disjoint (↑t : Set ι) s}) =
        ((↑t : Set ι).pi fun _ => ({False} : Set Prop)) := by
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

noncomputable def pairEdgeFinset {α : Type*} [DecidableEq α] (s : Finset α) :
    Finset (Sym2 α) :=
  ((⊤ : SimpleGraph {x // x ∈ (↑s : Set α)}).edgeFinset).map
    (Function.Embedding.subtype (fun x => x ∈ (↑s : Set α))).sym2Map

lemma pairEdgeFinset_card {α : Type*} [DecidableEq α] (s : Finset α) :
    (pairEdgeFinset s).card = Nat.choose s.card 2 := by
  classical
  calc
    (pairEdgeFinset s).card
        = ((⊤ : SimpleGraph {x // x ∈ (↑s : Set α)}).edgeFinset).card := by
          exact Finset.card_map _
    _ = Nat.choose (Fintype.card {x // x ∈ (↑s : Set α)}) 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose s.card 2 := by simp

lemma mem_pairEdgeFinset_iff {α : Type*} [Finite α] [DecidableEq α]
    (s : Finset α) {e : Sym2 α} :
    e ∈ pairEdgeFinset s ↔ e ∈ s.sym2 ∧ ¬ e.IsDiag := by
  classical
  let := Fintype.ofFinite α
  have hmap := SimpleGraph.map_edgeFinset_induce
    (G := (⊤ : SimpleGraph α)) (s := (↑s : Set α))
  have hind : SimpleGraph.induce (↑s : Set α) (⊤ : SimpleGraph α) =
      (⊤ : SimpleGraph {x // x ∈ (↑s : Set α)}) := by
    ext a b
    simp [SimpleGraph.induce]
  have hmem := Finset.ext_iff.mp hmap e
  simpa [and_comm, pairEdgeFinset, hind, SimpleGraph.mem_edgeFinset,
    Finset.mem_inter, Finset.mk_mem_sym2_iff] using hmem

lemma pairEdgeFinset_subset_diagCompl {α : Type*} [Finite α] [DecidableEq α]
    (s : Finset α) :
    (↑(pairEdgeFinset s) : Set (Sym2 α)) ⊆ Sym2.diagSetᶜ := by
  classical
  let := Fintype.ofFinite α
  intro e he
  simpa [Set.compl_ofPred] using (mem_pairEdgeFinset_iff s).1 he |>.2

def crossEdgeFinset (A B : Finset V) : Finset (Sym2 V) :=
  (A ×ˢ B).image fun ab ↦ s(ab.1, ab.2)

lemma mem_crossEdgeFinset_iff {A B : Finset V} {e : Sym2 V} :
    e ∈ crossEdgeFinset A B ↔ ∃ a ∈ A, ∃ b ∈ B, e = s(a, b) := by
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨⟨a, b⟩, hab, heq⟩
    exact ⟨a, (Finset.mem_product.mp hab).1, b, (Finset.mem_product.mp hab).2, heq.symm⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

lemma crossEdgeFinset_card {A B : Finset V} (hAB : Disjoint A B) :
    (crossEdgeFinset A B).card = A.card * B.card := by
  classical
  rw [crossEdgeFinset, Finset.card_image_of_injOn]
  · exact Finset.card_product A B
  · intro x hx y hy hxy
    rcases Finset.mem_product.mp hx with ⟨hxA, hxB⟩
    rcases Finset.mem_product.mp hy with ⟨hyA, hyB⟩
    rcases Sym2.eq_iff.mp hxy with h | h
    · exact Prod.ext h.1 h.2
    · exfalso
      exact Finset.disjoint_left.mp hAB hxA (h.1 ▸ hyB)

lemma crossEdgeFinset_subset_diagCompl {A B : Finset V} (hAB : Disjoint A B) :
    (↑(crossEdgeFinset A B) : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
  intro e he
  rcases mem_crossEdgeFinset_iff.mp he with ⟨a, ha, b, hb, rfl⟩
  have hab : a ≠ b := fun h ↦ Finset.disjoint_left.mp hAB ha (h ▸ hb)
  simpa using hab

def holePairs (N k : ℕ) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  ((univ.powersetCard k) ×ˢ (univ.powersetCard k)).filter fun AB ↦ Disjoint AB.1 AB.2

lemma mem_holePairs_iff {N k : ℕ} {A B : Finset (Fin N)} :
    (A, B) ∈ holePairs N k ↔ A.card = k ∧ B.card = k ∧ Disjoint A B := by
  simp [holePairs, and_assoc, and_left_comm]

def holeCount (N k : ℕ) (ω : Set (Sym2 (Fin N))) : ℕ := by
  classical
  exact ((holePairs N k).filter fun AB : Finset (Fin N) × Finset (Fin N) ↦
    Disjoint (↑(crossEdgeFinset AB.1 AB.2) : Set (Sym2 (Fin N))) ω).card

lemma holeCount_eq_zero_iff (N k : ℕ) (ω : Set (Sym2 (Fin N))) :
    holeCount N k ω = 0 ↔
      ∀ A B : Finset (Fin N), A.card = k → B.card = k → Disjoint A B →
        ∃ a ∈ A, ∃ b ∈ B, s(a, b) ∈ ω := by
  classical
  rw [holeCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h A B hA hB hAB
    have hn := h (mem_holePairs_iff.mpr ⟨hA, hB, hAB⟩)
    rw [Set.not_disjoint_iff] at hn
    obtain ⟨e, hecross, heω⟩ := hn
    rcases mem_crossEdgeFinset_iff.mp hecross with ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, heω⟩
  · intro h AB hAB
    rcases AB with ⟨A, B⟩
    rcases mem_holePairs_iff.mp hAB with ⟨hA, hB, hdisj⟩
    obtain ⟨a, ha, b, hb, he⟩ := h A B hA hB hdisj
    exact Set.not_disjoint_iff.mpr ⟨s(a, b), mem_crossEdgeFinset_iff.mpr ⟨a, ha, b, hb, rfl⟩, he⟩

lemma hole_event_measure (N k : ℕ) (p : I) (A B : Finset (Fin N))
    (hA : A.card = k) (hB : B.card = k) (hAB : Disjoint A B) :
    setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
      {ω : Set (Sym2 (Fin N)) |
        Disjoint (↑(crossEdgeFinset A B) : Set (Sym2 (Fin N))) ω} =
      (toNNReal (σ p) : ℝ≥0∞) ^ (k * k) := by
  rw [setBernoulli_disjoint_finset
    (u := (Sym2.diagSetᶜ : Set (Sym2 (Fin N)))) (p := p)
    (t := crossEdgeFinset A B) (crossEdgeFinset_subset_diagCompl hAB)]
  rw [crossEdgeFinset_card hAB, hA, hB]

lemma holeCount_lintegral_le (N k : ℕ) (p : I) :
    ∫⁻ ω, (holeCount N k ω : ℝ≥0∞) ∂
      setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) ≤
        ((Nat.choose N k : ℝ≥0∞) ^ 2) *
          (toNNReal (σ p) : ℝ≥0∞) ^ (k * k) := by
  classical
  let P := holePairs N k
  have hcount : ∀ ω : Set (Sym2 (Fin N)),
      (holeCount N k ω : ℝ≥0∞) =
        ∑ AB ∈ P, if Disjoint (↑(crossEdgeFinset AB.1 AB.2) : Set (Sym2 (Fin N))) ω
          then 1 else 0 := by
    intro ω
    simp [holeCount, P]
  calc
    ∫⁻ ω, (holeCount N k ω : ℝ≥0∞) ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) =
      ∫⁻ ω, ∑ AB ∈ P,
          if Disjoint (↑(crossEdgeFinset AB.1 AB.2) : Set (Sym2 (Fin N))) ω
          then (1 : ℝ≥0∞) else 0 ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) := by
          apply lintegral_congr
          exact hcount
    _ = ∑ AB ∈ P, ∫⁻ ω,
          if Disjoint (↑(crossEdgeFinset AB.1 AB.2) : Set (Sym2 (Fin N))) ω
          then (1 : ℝ≥0∞) else 0 ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) := by
          simp_rw [MeasureTheory.lintegral_finsetSum _ (fun _ _ ↦ measurable_of_countable _)]
    _ = ∑ AB ∈ P,
          setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
            {ω : Set (Sym2 (Fin N)) |
              Disjoint (↑(crossEdgeFinset AB.1 AB.2) : Set (Sym2 (Fin N))) ω} := by
          apply Finset.sum_congr rfl
          intro AB hAB
          have hm : MeasurableSet {ω : Set (Sym2 (Fin N)) |
              Disjoint (↑(crossEdgeFinset AB.1 AB.2) : Set (Sym2 (Fin N))) ω} :=
            (Set.to_countable _).measurableSet
          simpa [Set.indicator, hm] using
            (MeasureTheory.lintegral_indicator_one
              (μ := setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)) hm)
    _ = ∑ _AB ∈ P, (toNNReal (σ p) : ℝ≥0∞) ^ (k * k) := by
          apply Finset.sum_congr rfl
          intro AB hAB
          rcases AB with ⟨A, B⟩
          rcases mem_holePairs_iff.mp hAB with ⟨hA, hB, hd⟩
          exact hole_event_measure N k p A B hA hB hd
    _ = (P.card : ℝ≥0∞) * (toNNReal (σ p) : ℝ≥0∞) ^ (k * k) := by simp
    _ ≤ ((Nat.choose N k : ℝ≥0∞) ^ 2) *
          (toNNReal (σ p) : ℝ≥0∞) ^ (k * k) := by
      gcongr
      have hP : P.card ≤ (Nat.choose N k) ^ 2 := by
        calc
          P.card ≤ (univ.powersetCard k ×ˢ univ.powersetCard k :
              Finset (Finset (Fin N) × Finset (Fin N))).card := by
                exact Finset.card_filter_le _ _
          _ = (Nat.choose N k) ^ 2 := by simp [P, holePairs, pow_two]
      exact_mod_cast hP

def randomEdgeCount (N : ℕ) (ω : Set (Sym2 (Fin N))) : ℕ := by
  classical
  exact ((pairEdgeFinset (univ : Finset (Fin N))).filter fun e ↦ e ∈ ω).card

lemma randomEdgeCount_lintegral_eq (N : ℕ) (p : I) :
    ∫⁻ ω, (randomEdgeCount N ω : ℝ≥0∞) ∂
      setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) =
        (Nat.choose N 2 : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) := by
  classical
  let E := pairEdgeFinset (univ : Finset (Fin N))
  have hcount : ∀ ω : Set (Sym2 (Fin N)),
      (randomEdgeCount N ω : ℝ≥0∞) =
        ∑ e ∈ E, if e ∈ ω then 1 else 0 := by
    intro ω
    simp [randomEdgeCount, E]
  calc
    ∫⁻ ω, (randomEdgeCount N ω : ℝ≥0∞) ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) =
      ∫⁻ ω, ∑ e ∈ E, if e ∈ ω then (1 : ℝ≥0∞) else 0 ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) := by
          apply lintegral_congr
          exact hcount
    _ = ∑ e ∈ E, ∫⁻ ω, if e ∈ ω then (1 : ℝ≥0∞) else 0 ∂
        setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) := by
          simp_rw [MeasureTheory.lintegral_finsetSum _ (fun _ _ ↦ measurable_of_countable _)]
    _ = ∑ _e ∈ E, (toNNReal p : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro e he
          have heU : e ∈ (Sym2.diagSetᶜ : Set (Sym2 (Fin N))) :=
            pairEdgeFinset_subset_diagCompl _ he
          have hm : MeasurableSet {ω : Set (Sym2 (Fin N)) | e ∈ ω} :=
            (Set.to_countable _).measurableSet
          calc
            ∫⁻ ω, (if e ∈ ω then (1 : ℝ≥0∞) else 0) ∂
                setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p) =
              setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)
                {ω : Set (Sym2 (Fin N)) | e ∈ ω} := by
                  simpa [Set.indicator, hm] using
                    (MeasureTheory.lintegral_indicator_one
                      (μ := setBer((Sym2.diagSetᶜ : Set (Sym2 (Fin N))), p)) hm)
            _ = (toNNReal p : ℝ≥0∞) := by
              simpa using setBernoulli_superset_finset
                (u := (Sym2.diagSetᶜ : Set (Sym2 (Fin N)))) (p := p) (t := {e})
                (by simpa using heU)
    _ = (E.card : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) := by simp
    _ = (Nat.choose N 2 : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) := by
      simp [E, pairEdgeFinset_card]

lemma randomEdgeCount_eq_card_edgeSet (N : ℕ) (ω : Set (Sym2 (Fin N))) :
    randomEdgeCount N ω = Nat.card (SimpleGraph.fromEdgeSet ω).edgeSet := by
  classical
  let := Fintype.ofFinite (SimpleGraph.fromEdgeSet ω).edgeSet
  have hcard : Nat.card (SimpleGraph.fromEdgeSet ω).edgeSet =
      (SimpleGraph.fromEdgeSet ω).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  rw [hcard]
  apply congrArg Finset.card
  ext e
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet]
  simp [randomEdgeCount, mem_pairEdgeFinset_iff, and_comm, and_left_comm]

end Erdos720
