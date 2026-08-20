import ErdosProblems.Erdos526.Core
import ErdosProblems.Erdos526.Weighted

namespace Erdos526

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology
noncomputable section

def centerStateRegion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (length : ℝ) (p : ι → Circle) (S : Finset ι) : Set Circle :=
  ⋂ i : ι, if i ∈ S then arc (p i) length else (arc (p i) length)ᶜ

lemma measurableSet_centerStateRegion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (length : ℝ) (p : ι → Circle) (S : Finset ι) :
    MeasurableSet (centerStateRegion length p S) := by
  unfold centerStateRegion
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact measurableSet_ball
  · exact measurableSet_ball.compl

lemma mem_centerStateRegion_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (length : ℝ) (p : ι → Circle) (S : Finset ι) (z : Circle) :
    z ∈ centerStateRegion length p S ↔
      ∀ i, (p i ∈ arc z length ↔ i ∈ S) := by
  simp only [centerStateRegion, mem_iInter]
  constructor
  · intro h i
    have hi := h i
    by_cases his : i ∈ S
    · simp only [his, if_true] at hi
      constructor
      · intro _
        exact his
      · intro _
        simpa only [arc, Metric.mem_ball, dist_comm] using hi
    · simp only [his, if_false, mem_compl_iff] at hi
      constructor
      · intro hp
        exfalso
        apply hi
        simpa only [arc, Metric.mem_ball, dist_comm] using hp
      · intro him
        exact False.elim (his him)
  · intro h i
    by_cases his : i ∈ S
    · simp only [his, if_true]
      simpa only [arc, Metric.mem_ball, dist_comm] using (h i).2 his
    · simp only [his, if_false, mem_compl_iff]
      intro hz
      apply his
      apply (h i).1
      simpa only [arc, Metric.mem_ball, dist_comm] using hz

lemma pairwiseDisjoint_centerStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι] (length : ℝ) (p : ι → Circle) :
    ∀ ⦃S T : Finset ι⦄, S ≠ T →
      Disjoint (centerStateRegion length p S) (centerStateRegion length p T) := by
  intro S T hST
  have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
    by_contra h
    push Not at h
    apply hST
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  rw [Set.disjoint_left]
  intro z hzS hzT
  have hS := (mem_centerStateRegion_iff length p S z).1 hzS i
  have hT := (mem_centerStateRegion_iff length p T z).1 hzT i
  exact hi (hS.symm.trans hT)

def assignmentRegion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℕ → Finset ι → Set Circle) :
    (K : List ℕ) → StateAssignments ι K.length → ℕ → Set Circle
  | [], _, _ => Set.univ
  | k :: K, q, n => if n = k then R k q.1 else assignmentRegion R K q.2 n

def assignmentAtom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℕ → Finset ι → Set Circle) :
    (K : List ℕ) → StateAssignments ι K.length → Set Sample
  | [], _ => Set.univ
  | k :: K, q => center k ⁻¹' R k q.1 ∩ assignmentAtom R K q.2

lemma measurableSet_assignmentAtom {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ℕ → Finset ι → Set Circle}
    (hR : ∀ k S, MeasurableSet (R k S)) :
    ∀ K q, MeasurableSet (assignmentAtom R K q) := by
  intro K
  induction K with
  | nil => intro q; exact MeasurableSet.univ
  | cons k K ih =>
      intro q
      exact (hR k q.1).preimage (center_measurable k) |>.inter (ih q.2)

lemma pairwiseDisjoint_assignmentAtom {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {R : ℕ → Finset ι → Set Circle}
    (hR : ∀ k ⦃S T : Finset ι⦄, S ≠ T → Disjoint (R k S) (R k T)) :
    ∀ K ⦃q r : StateAssignments ι K.length⦄, q ≠ r →
      Disjoint (assignmentAtom R K q) (assignmentAtom R K r) := by
  intro K
  induction K with
  | nil =>
      intro q r hqr
      change PUnit at q r
      exact False.elim (hqr (Subsingleton.elim q r))
  | cons k K ih =>
      intro q r hqr
      rw [Set.disjoint_left]
      intro ω hq hr
      change ω ∈ center k ⁻¹' R k q.1 ∩ assignmentAtom R K q.2 at hq
      change ω ∈ center k ⁻¹' R k r.1 ∩ assignmentAtom R K r.2 at hr
      by_cases hhead : q.1 = r.1
      · have htail : q.2 ≠ r.2 := by
          intro h
          apply hqr
          exact Prod.ext hhead h
        exact Set.disjoint_left.1 (ih htail) hq.2 hr.2
      · exact Set.disjoint_left.1 (hR k hhead) hq.1 hr.1

lemma assignmentAtom_eq_iInter {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (R : ℕ → Finset ι → Set Circle) :
    ∀ (K : List ℕ) (q : StateAssignments ι K.length), K.Nodup →
      assignmentAtom R K q =
        ⋂ n ∈ K.toFinset, center n ⁻¹' assignmentRegion R K q n := by
  intro K
  induction K with
  | nil =>
      intro q hK
      simp [assignmentAtom]
  | cons k K ih =>
      intro q hK
      have hk : k ∉ K := (List.nodup_cons.1 hK).1
      have hkfin : k ∉ K.toFinset := by simpa using hk
      have hKt : K.Nodup := (List.nodup_cons.1 hK).2
      rw [assignmentAtom, ih q.2 hKt]
      simp only [List.toFinset_cons]
      rw [Finset.set_biInter_insert]
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_iInter, assignmentRegion,
        if_pos]
      constructor
      · rintro ⟨hhead, htail⟩
        refine ⟨hhead, fun n hn ↦ ?_⟩
        rw [if_neg (ne_of_mem_of_not_mem hn hkfin)]
        exact htail n hn
      · rintro ⟨hhead, htail⟩
        refine ⟨hhead, fun n hn ↦ ?_⟩
        have := htail n hn
        rw [if_neg (ne_of_mem_of_not_mem hn hkfin)] at this
        exact this

lemma measurableSet_assignmentRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {R : ℕ → Finset ι → Set Circle}
    (hR : ∀ k S, MeasurableSet (R k S)) :
    ∀ K q n, MeasurableSet (assignmentRegion R K q n) := by
  intro K
  induction K with
  | nil =>
      intro q n
      simp only [assignmentRegion]
      exact MeasurableSet.univ
  | cons k K ih =>
      intro q n
      simp only [assignmentRegion]
      split_ifs
      · exact hR k q.1
      · exact ih q.2 n

lemma measureReal_assignmentAtom {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {R : ℕ → Finset ι → Set Circle}
    (hR : ∀ k S, MeasurableSet (R k S))
    (K : List ℕ) (q : StateAssignments ι K.length) (hK : K.Nodup) :
    sampleMeasure.real (assignmentAtom R K q) =
      ∏ n ∈ K.toFinset, uniformCircle.real (assignmentRegion R K q n) := by
  rw [assignmentAtom_eq_iInter R K q hK]
  have hprod := center_iIndep.measure_inter_preimage_eq_mul K.toFinset
    (sets := assignmentRegion R K q)
    (fun n hn ↦ measurableSet_assignmentRegion hR K q n)
  rw [measureReal_def, hprod, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro n hn
  rw [measureReal_def, ← center_map n,
    Measure.map_apply (center_measurable n)
      (measurableSet_assignmentRegion hR K q n)]

lemma product_assignmentRegion_eq_assignmentWeight {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (R : ℕ → Finset ι → Set Circle) :
    ∀ (K : List ℕ) (q : StateAssignments ι K.length), K.Nodup →
      (∏ n ∈ K.toFinset, uniformCircle.real (assignmentRegion R K q n)) =
        assignmentWeight (fun n S ↦ uniformCircle.real (R n S)) K q := by
  intro K
  induction K with
  | nil => intro q hK; simp [assignmentWeight]
  | cons k K ih =>
      intro q hK
      have hk : k ∉ K.toFinset := by
        simpa using (List.nodup_cons.1 hK).1
      rw [List.toFinset_cons, Finset.prod_insert hk]
      simp only [assignmentRegion, if_pos]
      have htail : (∏ n ∈ K.toFinset,
          uniformCircle.real (if n = k then R k q.1 else assignmentRegion R K q.2 n)) =
          ∏ n ∈ K.toFinset, uniformCircle.real (assignmentRegion R K q.2 n) := by
        apply Finset.prod_congr rfl
        intro n hn
        rw [if_neg]
        exact ne_of_mem_of_not_mem hn hk
      rw [htail, ih q.2 (List.nodup_cons.1 hK).2]
      rfl

def weightedCoverEvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℕ → Finset ι → Set Circle) (K : List ℕ) (U : Finset ι) :
    Set Sample :=
  ⋃ q : StateAssignments ι K.length,
    if U ⊆ assignmentUnion q then assignmentAtom R K q else ∅

lemma measureReal_weightedCoverEvent {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {R : ℕ → Finset ι → Set Circle}
    (hRmeas : ∀ k S, MeasurableSet (R k S))
    (hRdisj : ∀ k ⦃S T : Finset ι⦄, S ≠ T → Disjoint (R k S) (R k T))
    (K : List ℕ) (hK : K.Nodup) (U : Finset ι) :
    sampleMeasure.real (weightedCoverEvent R K U) =
      weightedCover (fun n S ↦ uniformCircle.real (R n S)) K U := by
  let A : StateAssignments ι K.length → Set Sample := fun q ↦
    if U ⊆ assignmentUnion q then assignmentAtom R K q else ∅
  have hAmeas : ∀ q, MeasurableSet (A q) := by
    intro q
    dsimp only [A]
    split_ifs
    · exact measurableSet_assignmentAtom hRmeas K q
    · exact MeasurableSet.empty
  have hAdisj : ∀ ⦃q r : StateAssignments ι K.length⦄, q ≠ r →
      Disjoint (A q) (A r) := by
    intro q r hqr
    dsimp only [A]
    split_ifs
    · exact pairwiseDisjoint_assignmentAtom hRdisj K hqr
    · exact Set.disjoint_left.2 (by simp)
    · exact Set.disjoint_left.2 (by simp)
    · exact Set.disjoint_left.2 (by simp)
  rw [weightedCoverEvent, measureReal_iUnion_fintype hAdisj hAmeas]
  rw [weightedCover_eq_assignmentSum]
  apply Finset.sum_congr rfl
  intro q hq
  dsimp only [A]
  split_ifs with hcov
  · rw [measureReal_assignmentAtom hRmeas K q hK,
      product_assignmentRegion_eq_assignmentWeight R K q hK]
  · simp

lemma iUnion_centerStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι] (length : ℝ) (p : ι → Circle) :
    (⋃ S : Finset ι, centerStateRegion length p S) = Set.univ := by
  classical
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  let S : Finset ι := Finset.univ.filter fun i ↦ p i ∈ arc z length
  refine ⟨S, (mem_centerStateRegion_iff length p S z).2 ?_⟩
  intro i
  simp [S]

def qMissStateRegion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (n : ℕ) (S : Finset ι) :
    Set Circle :=
  centerStateRegion (a n) (fun i ↦ (p i : Circle)) S ∩ (arc (q : Circle) (a n))ᶜ

def qxMissStateRegion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (n : ℕ) (S : Finset ι) :
    Set Circle :=
  qMissStateRegion a p q n S ∩ (arc (x : Circle) (a n))ᶜ

def qMissXHitRegion (a : ℕ → ℝ) (q x : ℝ) (n : ℕ) : Set Circle :=
  (arc (q : Circle) (a n))ᶜ ∩ arc (x : Circle) (a n)

lemma measurableSet_qMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (n : ℕ) (S : Finset ι) :
    MeasurableSet (qMissStateRegion a p q n S) :=
  (measurableSet_centerStateRegion _ _ _).inter measurableSet_ball.compl

lemma measurableSet_qxMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (n : ℕ) (S : Finset ι) :
    MeasurableSet (qxMissStateRegion a p q x n S) :=
  (measurableSet_qMissStateRegion a p q n S).inter measurableSet_ball.compl

lemma measurableSet_qMissXHitRegion
    (a : ℕ → ℝ) (q x : ℝ) (n : ℕ) :
    MeasurableSet (qMissXHitRegion a q x n) :=
  measurableSet_ball.compl.inter measurableSet_ball

lemma pairwiseDisjoint_qMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (n : ℕ) :
    ∀ ⦃S T : Finset ι⦄, S ≠ T →
      Disjoint (qMissStateRegion a p q n S) (qMissStateRegion a p q n T) := by
  intro S T hST
  exact (pairwiseDisjoint_centerStateRegion (a n)
    (fun i ↦ (p i : Circle)) hST).mono inter_subset_left inter_subset_left

lemma pairwiseDisjoint_qxMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (n : ℕ) :
    ∀ ⦃S T : Finset ι⦄, S ≠ T →
      Disjoint (qxMissStateRegion a p q x n S)
        (qxMissStateRegion a p q x n T) := by
  intro S T hST
  exact (pairwiseDisjoint_qMissStateRegion a p q n hST).mono
    inter_subset_left inter_subset_left

lemma qMissStateRegion_inter_xHit_empty {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} {p : ι → ℝ} {q x : ℝ} {n : ℕ}
    (ha₀ : 0 ≤ a n) (ha : a n ≤ 1 / 4)
    (hpq : ∀ i, p i ≤ q) (hqx : q ≤ x) (hxp : ∀ i, x - p i ≤ 1 / 2)
    {S : Finset ι} (hS : S ≠ ∅) :
    qMissStateRegion a p q n S ∩ arc (x : Circle) (a n) = ∅ := by
  ext z
  simp only [mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hzstate, hzq⟩, hzx⟩
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
  have hpi : (p i : Circle) ∈ arc z (a n) :=
    (mem_centerStateRegion_iff (a n) (fun i ↦ (p i : Circle)) S z).1 hzstate i |>.2 hi
  have hxz : (x : Circle) ∈ arc z (a n) := by
    simpa only [arc, Metric.mem_ball, dist_comm] using hzx
  have hqz := arc_interval_convex ha₀ ha (hpq i) hqx (hxp i) hpi hxz
  apply hzq
  simpa only [arc, Metric.mem_ball, dist_comm] using hqz

lemma qMissStateRegion_eq_qxMiss_union {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} {p : ι → ℝ} {q x : ℝ} {n : ℕ}
    (ha₀ : 0 ≤ a n) (ha : a n ≤ 1 / 4)
    (hpq : ∀ i, p i ≤ q) (hqx : q ≤ x) (hxp : ∀ i, x - p i ≤ 1 / 2)
    (S : Finset ι) :
    qMissStateRegion a p q n S =
      qxMissStateRegion a p q x n S ∪
        if S = ∅ then qMissXHitRegion a q x n else ∅ := by
  by_cases hS : S = ∅
  · subst S
    ext z
    simp only [if_true, qxMissStateRegion, qMissStateRegion,
      qMissXHitRegion, mem_union, mem_inter_iff, mem_compl_iff]
    constructor
    · intro hz
      by_cases hxz : z ∈ arc (x : Circle) (a n)
      · exact Or.inr ⟨hz.2, hxz⟩
      · exact Or.inl ⟨hz, hxz⟩
    · rintro (⟨hz, hx⟩ | ⟨hq, hx⟩)
      · exact hz
      · refine ⟨?_, hq⟩
        apply (mem_centerStateRegion_iff (a n)
          (fun i ↦ (p i : Circle)) ∅ z).2
        intro i
        simp
        intro hpi
        have hxz' : (x : Circle) ∈ arc z (a n) := by
          simpa only [arc, Metric.mem_ball, dist_comm] using hx
        have hqz := arc_interval_convex ha₀ ha (hpq i) hqx (hxp i) hpi hxz'
        apply hq
        simpa only [arc, Metric.mem_ball, dist_comm] using hqz
  · rw [if_neg hS, union_empty]
    apply le_antisymm
    · intro z hz
      refine ⟨hz, ?_⟩
      intro hx
      have : z ∈ qMissStateRegion a p q n S ∩ arc (x : Circle) (a n) :=
        ⟨hz, hx⟩
      rw [qMissStateRegion_inter_xHit_empty ha₀ ha hpq hqx hxp hS] at this
      exact this
    · exact inter_subset_left

lemma qxMissStateRegion_disjoint_qMissXHitRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (n : ℕ) (S : Finset ι) :
    Disjoint (qxMissStateRegion a p q x n S) (qMissXHitRegion a q x n) := by
  rw [Set.disjoint_left]
  intro z hz hzx
  exact hz.2 hzx.2

lemma qMissWeight_eq_qxMissWeight_add {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} {p : ι → ℝ} {q x : ℝ} {n : ℕ}
    (ha₀ : 0 ≤ a n) (ha : a n ≤ 1 / 4)
    (hpq : ∀ i, p i ≤ q) (hqx : q ≤ x) (hxp : ∀ i, x - p i ≤ 1 / 2)
    (S : Finset ι) :
    uniformCircle.real (qMissStateRegion a p q n S) =
      uniformCircle.real (qxMissStateRegion a p q x n S) +
        if S = ∅ then uniformCircle.real (qMissXHitRegion a q x n) else 0 := by
  rw [qMissStateRegion_eq_qxMiss_union ha₀ ha hpq hqx hxp]
  split_ifs with hS
  · rw [measureReal_union (μ := uniformCircle)
      (qxMissStateRegion_disjoint_qMissXHitRegion a p q x n S)
      (measurableSet_qMissXHitRegion a q x n)]
  · simp

lemma iUnion_qMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (n : ℕ) :
    (⋃ S : Finset ι, qMissStateRegion a p q n S) =
      (arc (q : Circle) (a n))ᶜ := by
  ext z
  simp only [mem_iUnion, qMissStateRegion, mem_inter_iff]
  constructor
  · rintro ⟨S, hzS, hzq⟩
    exact hzq
  · intro hzq
    have hzstate : z ∈ ⋃ S : Finset ι,
        centerStateRegion (a n) (fun i ↦ (p i : Circle)) S := by
      rw [iUnion_centerStateRegion]
      exact mem_univ z
    obtain ⟨S, hzS⟩ := mem_iUnion.1 hzstate
    exact ⟨S, hzS, hzq⟩

lemma iUnion_qxMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (n : ℕ) :
    (⋃ S : Finset ι, qxMissStateRegion a p q x n S) =
      (arc (q : Circle) (a n))ᶜ ∩ (arc (x : Circle) (a n))ᶜ := by
  ext z
  simp only [mem_iUnion, qxMissStateRegion, mem_inter_iff]
  constructor
  · rintro ⟨S, hz, hzx⟩
    exact ⟨hz.2, hzx⟩
  · rintro ⟨hzq, hzx⟩
    have hzstate : z ∈ ⋃ S : Finset ι,
        centerStateRegion (a n) (fun i ↦ (p i : Circle)) S := by
      rw [iUnion_centerStateRegion]
      exact mem_univ z
    obtain ⟨S, hzS⟩ := mem_iUnion.1 hzstate
    exact ⟨S, ⟨hzS, hzq⟩, hzx⟩

lemma sum_qMissWeight {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} (p : ι → ℝ) (q : ℝ) (n : ℕ)
    (ha₀ : 0 ≤ a n) (ha₁ : a n ≤ 1) :
    (∑ S : Finset ι, uniformCircle.real (qMissStateRegion a p q n S)) =
      1 - a n := by
  have hsum := measureReal_iUnion_fintype (μ := uniformCircle)
    (pairwiseDisjoint_qMissStateRegion a p q n)
    (measurableSet_qMissStateRegion a p q n)
  rw [iUnion_qMissStateRegion] at hsum
  rw [← hsum]
  have hcomp := measureReal_compl (μ := uniformCircle)
    (s := arc (q : Circle) (a n)) measurableSet_ball
  rw [probReal_univ] at hcomp
  have harc : uniformCircle.real (arc (q : Circle) (a n)) = a n := by
    rw [measureReal_def, measure_arc ha₀ ha₁, ENNReal.toReal_ofReal ha₀]
  rw [harc] at hcomp
  exact hcomp

lemma sum_qxMissWeight {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} (p : ι → ℝ) (q x : ℝ) (n : ℕ)
    (ha₀ : 0 ≤ a n) (ha : a n ≤ 1 / 4) (hqx : |q - x| ≤ 1 / 4) :
    (∑ S : Finset ι, uniformCircle.real (qxMissStateRegion a p q x n S)) =
      1 - 2 * a n + max (a n - |q - x|) 0 := by
  have hsum := measureReal_iUnion_fintype (μ := uniformCircle)
    (pairwiseDisjoint_qxMissStateRegion a p q x n)
    (measurableSet_qxMissStateRegion a p q x n)
  rw [iUnion_qxMissStateRegion] at hsum
  rw [← hsum]
  exact measureReal_compl_arc_inter_compl_arc_coe (a n) q x ha₀ ha hqx

lemma weightedTotal_qMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} (p : ι → ℝ) (q : ℝ)
    (K : List ℕ) (hK : K.Nodup) (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) :
    weightedTotal
        (fun n S ↦ uniformCircle.real (qMissStateRegion a p q n S)) K =
      ∏ n ∈ K.toFinset, (1 - a n) := by
  unfold weightedTotal
  rw [← List.prod_toFinset (fun n ↦
    ∑ S : Finset ι, uniformCircle.real (qMissStateRegion a p q n S)) hK]
  apply Finset.prod_congr rfl
  intro n hn
  exact sum_qMissWeight p q n (ha₀ n) (ha₁ n)

lemma weightedTotal_qxMissStateRegion {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} (p : ι → ℝ) (q x : ℝ)
    (K : List ℕ) (hK : K.Nodup) (ha₀ : ∀ n, 0 ≤ a n)
    (ha : ∀ n, a n ≤ 1 / 4) (hqx : |q - x| ≤ 1 / 4) :
    weightedTotal
        (fun n S ↦ uniformCircle.real (qxMissStateRegion a p q x n S)) K =
      ∏ n ∈ K.toFinset,
        (1 - 2 * a n + max (a n - |q - x|) 0) := by
  unfold weightedTotal
  rw [← List.prod_toFinset (fun n ↦
    ∑ S : Finset ι, uniformCircle.real (qxMissStateRegion a p q x n S)) hK]
  apply Finset.prod_congr rfl
  intro n hn
  exact sum_qxMissWeight p q x n (ha₀ n) (ha n) hqx

lemma weightedCoverEvent_correlation {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {a : ℕ → ℝ} {p : ι → ℝ} {q x : ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hpq : ∀ i, p i ≤ q) (hqx : q ≤ x) (hxq : x - q ≤ 1 / 4)
    (hxp : ∀ i, x - p i ≤ 1 / 2)
    (K : List ℕ) (hK : K.Nodup) (U : Finset ι) :
    sampleMeasure.real (weightedCoverEvent (qMissStateRegion a p q) K U) *
        (∏ n ∈ K.toFinset,
          (1 - 2 * a n + max (a n - |q - x|) 0)) ≤
      sampleMeasure.real (weightedCoverEvent (qxMissStateRegion a p q x) K U) *
        ∏ n ∈ K.toFinset, (1 - a n) := by
  let d : ℕ → Finset ι → ℝ := fun n S ↦
    uniformCircle.real (qxMissStateRegion a p q x n S)
  let b : ℕ → Finset ι → ℝ := fun n S ↦
    uniformCircle.real (qMissStateRegion a p q n S)
  let h : ℕ → ℝ := fun n ↦ uniformCircle.real (qMissXHitRegion a q x n)
  have hd : ∀ n S, 0 ≤ d n S := fun n S ↦ measureReal_nonneg
  have hh : ∀ n, 0 ≤ h n := fun n ↦ measureReal_nonneg
  have hb : ∀ n S, b n S = d n S + if S = ∅ then h n else 0 := by
    intro n S
    exact qMissWeight_eq_qxMissWeight_add (ha₀ n) (ha n) hpq hqx hxp S
  have halg := weightedCover_contaminate_empty hd hh hb K U
  have hdist : |q - x| ≤ 1 / 4 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hqx)]
    linarith
  dsimp only [b, d] at halg
  rw [← measureReal_weightedCoverEvent
      (measurableSet_qMissStateRegion a p q)
      (pairwiseDisjoint_qMissStateRegion a p q) K hK U,
    ← measureReal_weightedCoverEvent
      (measurableSet_qxMissStateRegion a p q x)
      (pairwiseDisjoint_qxMissStateRegion a p q x) K hK U,
    weightedTotal_qMissStateRegion p q K hK ha₀ (fun n ↦ (ha n).trans (by norm_num)),
    weightedTotal_qxMissStateRegion p q x K hK ha₀ ha hdist] at halg
  exact halg

def actualAssignment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (K : List ℕ) (ω : Sample) :
    StateAssignments ι K.length :=
  match K with
  | [] => PUnit.unit
  | k :: K =>
      (@Finset.filter ι (fun i ↦ (p i : Circle) ∈ arc (ω k) (a k))
          (Classical.decPred _) Finset.univ,
        actualAssignment a p K ω)

lemma mem_assignmentUnion_actualAssignment_iff {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (ω : Sample) (i : ι) :
    ∀ K : List ℕ, i ∈ assignmentUnion (actualAssignment a p K ω) ↔
      ∃ n ∈ K, (p i : Circle) ∈ arc (ω n) (a n) := by
  classical
  intro K
  induction K with
  | nil => simp [actualAssignment, assignmentUnion]
  | cons k K ih =>
      change i ∈
          (@Finset.filter ι (fun j ↦ (p j : Circle) ∈ arc (ω k) (a k))
            (Classical.decPred _) Finset.univ) ∪
              assignmentUnion (actualAssignment a p K ω) ↔
        ∃ n ∈ k :: K, (p i : Circle) ∈ arc (ω n) (a n)
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, ih, List.mem_cons]
      aesop

lemma actualAssignment_mem_qMissAtom {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (ω : Sample) :
    ∀ K : List ℕ, (∀ n ∈ K, ω n ∉ arc (q : Circle) (a n)) →
      ω ∈ assignmentAtom (qMissStateRegion a p q) K
        (actualAssignment a p K ω) := by
  classical
  intro K
  induction K with
  | nil => intro h; exact mem_univ ω
  | cons k K ih =>
      intro h
      change ω ∈ center k ⁻¹' qMissStateRegion a p q k
          (@Finset.filter ι (fun i ↦ (p i : Circle) ∈ arc (ω k) (a k))
            (Classical.decPred _) Finset.univ) ∩
        assignmentAtom (qMissStateRegion a p q) K (actualAssignment a p K ω)
      constructor
      · refine ⟨(mem_centerStateRegion_iff (a k)
          (fun i ↦ (p i : Circle)) _ (ω k)).2 ?_, h k (by simp)⟩
        intro i
        simp
      · exact ih (fun n hn ↦ h n (by simp [hn]))

lemma actualAssignment_mem_qxMissAtom {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (ω : Sample) :
    ∀ K : List ℕ,
      (∀ n ∈ K, ω n ∉ arc (q : Circle) (a n) ∧
        ω n ∉ arc (x : Circle) (a n)) →
      ω ∈ assignmentAtom (qxMissStateRegion a p q x) K
        (actualAssignment a p K ω) := by
  classical
  intro K
  induction K with
  | nil => intro h; exact mem_univ ω
  | cons k K ih =>
      intro h
      change ω ∈ center k ⁻¹' qxMissStateRegion a p q x k
          (@Finset.filter ι (fun i ↦ (p i : Circle) ∈ arc (ω k) (a k))
            (Classical.decPred _) Finset.univ) ∩
        assignmentAtom (qxMissStateRegion a p q x) K (actualAssignment a p K ω)
      constructor
      · exact ⟨⟨(mem_centerStateRegion_iff (a k)
          (fun i ↦ (p i : Circle)) _ (ω k)).2 (by intro i; simp),
            (h k (by simp)).1⟩, (h k (by simp)).2⟩
      · exact ih (fun n hn ↦ h n (by simp [hn]))

lemma mem_assignmentAtom_qMiss_semantics {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (ω : Sample) (i : ι) :
    ∀ (K : List ℕ) (s : StateAssignments ι K.length),
      ω ∈ assignmentAtom (qMissStateRegion a p q) K s →
      (∀ n ∈ K, ω n ∉ arc (q : Circle) (a n)) ∧
        (i ∈ assignmentUnion s ↔
          ∃ n ∈ K, (p i : Circle) ∈ arc (ω n) (a n)) := by
  intro K
  induction K with
  | nil =>
      intro s h
      change PUnit at s
      simp [assignmentUnion]
  | cons k K ih =>
      intro s h
      change Finset ι × StateAssignments ι K.length at s
      rcases s with ⟨S, s⟩
      change ω ∈ center k ⁻¹' qMissStateRegion a p q k S ∩
        assignmentAtom (qMissStateRegion a p q) K s at h
      have ht := ih s h.2
      have hs := (mem_centerStateRegion_iff (a k)
        (fun i ↦ (p i : Circle)) S (ω k)).1 h.1.1 i
      constructor
      · intro n hn
        simp only [List.mem_cons] at hn
        rcases hn with rfl | hn
        · exact h.1.2
        · exact ht.1 n hn
      · rw [show assignmentUnion (n := K.length + 1) (S, s) =
            S ∪ assignmentUnion s by rfl]
        simp only [Finset.mem_union]
        rw [← hs, ht.2]
        simp only [List.mem_cons]
        aesop

lemma mem_assignmentAtom_qxMiss_semantics {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (ω : Sample) (i : ι) :
    ∀ (K : List ℕ) (s : StateAssignments ι K.length),
      ω ∈ assignmentAtom (qxMissStateRegion a p q x) K s →
      (∀ n ∈ K, ω n ∉ arc (q : Circle) (a n) ∧
        ω n ∉ arc (x : Circle) (a n)) ∧
        (i ∈ assignmentUnion s ↔
          ∃ n ∈ K, (p i : Circle) ∈ arc (ω n) (a n)) := by
  intro K
  induction K with
  | nil =>
      intro s h
      change PUnit at s
      simp [assignmentUnion]
  | cons k K ih =>
      intro s h
      change Finset ι × StateAssignments ι K.length at s
      rcases s with ⟨S, s⟩
      change ω ∈ center k ⁻¹' qxMissStateRegion a p q x k S ∩
        assignmentAtom (qxMissStateRegion a p q x) K s at h
      have ht := ih s h.2
      have hs := (mem_centerStateRegion_iff (a k)
        (fun i ↦ (p i : Circle)) S (ω k)).1 h.1.1.1 i
      constructor
      · intro n hn
        simp only [List.mem_cons] at hn
        rcases hn with rfl | hn
        · exact ⟨h.1.1.2, h.1.2⟩
        · exact ht.1 n hn
      · rw [show assignmentUnion (n := K.length + 1) (S, s) =
            S ∪ assignmentUnion s by rfl]
        simp only [Finset.mem_union]
        rw [← hs, ht.2]
        simp only [List.mem_cons]
        aesop

lemma mem_assignmentAtom_qMiss_allMiss {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ) (ω : Sample) :
    ∀ (K : List ℕ) (s : StateAssignments ι K.length),
      ω ∈ assignmentAtom (qMissStateRegion a p q) K s →
        ∀ n ∈ K, ω n ∉ arc (q : Circle) (a n) := by
  intro K
  induction K with
  | nil => simp
  | cons k K ih =>
      intro s h
      change Finset ι × StateAssignments ι K.length at s
      rcases s with ⟨S, s⟩
      change ω ∈ center k ⁻¹' qMissStateRegion a p q k S ∩
        assignmentAtom (qMissStateRegion a p q) K s at h
      intro n hn
      simp only [List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact h.1.2
      · exact ih s h.2 n hn

lemma mem_assignmentAtom_qxMiss_allMiss {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ) (ω : Sample) :
    ∀ (K : List ℕ) (s : StateAssignments ι K.length),
      ω ∈ assignmentAtom (qxMissStateRegion a p q x) K s →
        ∀ n ∈ K, ω n ∉ arc (q : Circle) (a n) ∧
          ω n ∉ arc (x : Circle) (a n) := by
  intro K
  induction K with
  | nil => simp
  | cons k K ih =>
      intro s h
      change Finset ι × StateAssignments ι K.length at s
      rcases s with ⟨S, s⟩
      change ω ∈ center k ⁻¹' qxMissStateRegion a p q x k S ∩
        assignmentAtom (qxMissStateRegion a p q x) K s at h
      intro n hn
      simp only [List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact ⟨h.1.1.2, h.1.2⟩
      · exact ih s h.2 n hn

lemma mem_weightedCoverEvent_qMiss_iff {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q : ℝ)
    (K : List ℕ) (U : Finset ι) (ω : Sample) :
    ω ∈ weightedCoverEvent (qMissStateRegion a p q) K U ↔
      (∀ n ∈ K, ω n ∉ arc (q : Circle) (a n)) ∧
        ∀ i ∈ U, ∃ n ∈ K, (p i : Circle) ∈ arc (ω n) (a n) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := mem_iUnion.1 h
    by_cases hcov : U ⊆ assignmentUnion s
    · simp only [hcov, if_true] at hs
      constructor
      · exact mem_assignmentAtom_qMiss_allMiss a p q ω K s hs
      · intro i hi
        exact (mem_assignmentAtom_qMiss_semantics a p q ω i K s hs).2.1 (hcov hi)
    · simp [hcov] at hs
  · rintro ⟨hmiss, hcover⟩
    apply mem_iUnion.2
    let s := actualAssignment a p K ω
    refine ⟨s, ?_⟩
    have hcov : U ⊆ assignmentUnion s := by
      intro i hi
      rw [mem_assignmentUnion_actualAssignment_iff]
      exact hcover i hi
    simp only [hcov, if_true]
    exact actualAssignment_mem_qMissAtom a p q ω K hmiss

lemma mem_weightedCoverEvent_qxMiss_iff {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a : ℕ → ℝ) (p : ι → ℝ) (q x : ℝ)
    (K : List ℕ) (U : Finset ι) (ω : Sample) :
    ω ∈ weightedCoverEvent (qxMissStateRegion a p q x) K U ↔
      (∀ n ∈ K, ω n ∉ arc (q : Circle) (a n) ∧
        ω n ∉ arc (x : Circle) (a n)) ∧
        ∀ i ∈ U, ∃ n ∈ K, (p i : Circle) ∈ arc (ω n) (a n) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := mem_iUnion.1 h
    by_cases hcov : U ⊆ assignmentUnion s
    · simp only [hcov, if_true] at hs
      constructor
      · exact mem_assignmentAtom_qxMiss_allMiss a p q x ω K s hs
      · intro i hi
        exact (mem_assignmentAtom_qxMiss_semantics a p q x ω i K s hs).2.1 (hcov hi)
    · simp [hcov] at hs
  · rintro ⟨hmiss, hcover⟩
    apply mem_iUnion.2
    let s := actualAssignment a p K ω
    refine ⟨s, ?_⟩
    have hcov : U ⊆ assignmentUnion s := by
      intro i hi
      rw [mem_assignmentUnion_actualAssignment_iff]
      exact hcover i hi
    simp only [hcov, if_true]
    exact actualAssignment_mem_qxMissAtom a p q x ω K hmiss

lemma measurableSet_weightedCoverEvent {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {R : ℕ → Finset ι → Set Circle}
    (hRmeas : ∀ k S, MeasurableSet (R k S))
    (K : List ℕ) (U : Finset ι) :
    MeasurableSet (weightedCoverEvent R K U) := by
  unfold weightedCoverEvent
  apply MeasurableSet.iUnion
  intro s
  split_ifs
  · exact measurableSet_assignmentAtom hRmeas K s
  · exact MeasurableSet.empty

def firstMissEvent (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) : Set Sample :=
  weightedCoverEvent
    (qMissStateRegion a (fun i : Fin j ↦ (i : ℝ) * δ) ((j : ℝ) * δ))
    (List.range M) Finset.univ

def firstMissAndMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) (x : ℝ) : Set Sample :=
  weightedCoverEvent
    (qxMissStateRegion a (fun i : Fin j ↦ (i : ℝ) * δ) ((j : ℝ) * δ) x)
    (List.range M) Finset.univ

lemma measurableSet_firstMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) :
    MeasurableSet (firstMissEvent a M δ j) :=
  measurableSet_weightedCoverEvent
    (measurableSet_qMissStateRegion a
      (fun i : Fin j ↦ (i : ℝ) * δ) ((j : ℝ) * δ)) _ _

lemma measurableSet_firstMissAndMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) (x : ℝ) :
    MeasurableSet (firstMissAndMissEvent a M δ j x) :=
  measurableSet_weightedCoverEvent
    (measurableSet_qxMissStateRegion a
      (fun i : Fin j ↦ (i : ℝ) * δ) ((j : ℝ) * δ) x) _ _

lemma mem_firstMissEvent_iff
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) (ω : Sample) :
    ω ∈ firstMissEvent a M δ j ↔
      (∀ n < M, ω n ∉ arc (((j : ℝ) * δ : ℝ) : Circle) (a n)) ∧
        ∀ i < j, ∃ n < M,
          (((i : ℝ) * δ : ℝ) : Circle) ∈ arc (ω n) (a n) := by
  rw [firstMissEvent, mem_weightedCoverEvent_qMiss_iff]
  simp only [List.mem_range, Finset.mem_univ, forall_true_left]
  constructor
  · rintro ⟨hmiss, hcover⟩
    refine ⟨hmiss, fun i hi ↦ ?_⟩
    obtain ⟨n, hn, hhit⟩ := hcover ⟨i, hi⟩
    exact ⟨n, hn, hhit⟩
  · rintro ⟨hmiss, hcover⟩
    refine ⟨hmiss, fun i ↦ ?_⟩
    exact hcover i i.isLt

lemma mem_firstMissAndMissEvent_iff
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) (x : ℝ) (ω : Sample) :
    ω ∈ firstMissAndMissEvent a M δ j x ↔
      (∀ n < M,
        (ω n ∉ arc (((j : ℝ) * δ : ℝ) : Circle) (a n) ∧
          ω n ∉ arc (x : Circle) (a n))) ∧
        ∀ i < j, ∃ n < M,
          (((i : ℝ) * δ : ℝ) : Circle) ∈ arc (ω n) (a n) := by
  rw [firstMissAndMissEvent, mem_weightedCoverEvent_qxMiss_iff]
  simp only [List.mem_range, Finset.mem_univ, forall_true_left]
  constructor
  · rintro ⟨hmiss, hcover⟩
    refine ⟨hmiss, fun i hi ↦ ?_⟩
    obtain ⟨n, hn, hhit⟩ := hcover ⟨i, hi⟩
    exact ⟨n, hn, hhit⟩
  · rintro ⟨hmiss, hcover⟩
    refine ⟨hmiss, fun i ↦ ?_⟩
    exact hcover i i.isLt

lemma firstMissAndMissEvent_subset_firstMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) (x : ℝ) :
    firstMissAndMissEvent a M δ j x ⊆ firstMissEvent a M δ j := by
  intro ω hω
  rw [mem_firstMissAndMissEvent_iff] at hω
  rw [mem_firstMissEvent_iff]
  exact ⟨fun n hn ↦ (hω.1 n hn).1, hω.2⟩

lemma firstMissAndMissEvent_subset_allMiss
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (j : ℕ) (x : ℝ) :
    firstMissAndMissEvent a M δ j x ⊆
      ⋂ n ∈ Finset.range M, missEvent a (x : Circle) n := by
  intro ω hω
  rw [mem_firstMissAndMissEvent_iff] at hω
  simp only [mem_iInter, Finset.mem_range]
  intro n hn
  exact (hω.1 n hn).2

lemma pairwiseDisjoint_firstMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) :
    ∀ ⦃j k : ℕ⦄, j ≠ k →
      Disjoint (firstMissEvent a M δ j) (firstMissEvent a M δ k) := by
  intro j k hjk
  rw [Set.disjoint_left]
  intro ω hωj hωk
  rw [mem_firstMissEvent_iff] at hωj hωk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · obtain ⟨n, hn, hhit⟩ := hωk.2 j hjk
    apply hωj.1 n hn
    simpa only [arc, Metric.mem_ball, dist_comm] using hhit
  · obtain ⟨n, hn, hhit⟩ := hωj.2 k hkj
    apply hωk.1 n hn
    simpa only [arc, Metric.mem_ball, dist_comm] using hhit

lemma pairwiseDisjoint_firstMissAndMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ x : ℝ) :
    ∀ ⦃j k : ℕ⦄, j ≠ k →
      Disjoint (firstMissAndMissEvent a M δ j x)
        (firstMissAndMissEvent a M δ k x) := by
  intro j k hjk
  exact (pairwiseDisjoint_firstMissEvent a M δ hjk).mono
    (firstMissAndMissEvent_subset_firstMissEvent a M δ j x)
    (firstMissAndMissEvent_subset_firstMissEvent a M δ k x)

def finiteGridMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (L : ℕ) : Set Sample :=
  ⋃ j : Fin (L + 1), firstMissEvent a M δ j

lemma measurableSet_finiteGridMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (L : ℕ) :
    MeasurableSet (finiteGridMissEvent a M δ L) := by
  unfold finiteGridMissEvent
  exact MeasurableSet.iUnion fun j ↦
    measurableSet_firstMissEvent a M δ j

lemma measureReal_finiteGridMissEvent
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (L : ℕ) :
    sampleMeasure.real (finiteGridMissEvent a M δ L) =
      ∑ j : Fin (L + 1),
        sampleMeasure.real (firstMissEvent a M δ j) := by
  unfold finiteGridMissEvent
  apply measureReal_iUnion_fintype (μ := sampleMeasure)
  · intro j k hjk
    apply pairwiseDisjoint_firstMissEvent a M δ
    intro hjkval
    apply hjk
    exact Fin.ext hjkval
  · exact fun j ↦ measurableSet_firstMissEvent a M δ j

lemma mem_finiteGridMissEvent_iff
    (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (L : ℕ) (ω : Sample) :
    ω ∈ finiteGridMissEvent a M δ L ↔
      ∃ j ≤ L, ∀ n < M,
        ω n ∉ arc ((((j : ℕ) : ℝ) * δ : ℝ) : Circle) (a n) := by
  classical
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    rw [mem_firstMissEvent_iff] at hj
    exact ⟨j, Nat.lt_succ_iff.1 j.isLt, hj.1⟩
  · rintro ⟨j, hjL, hjmiss⟩
    let P : ℕ → Prop := fun k ↦ ∀ n < M,
      ω n ∉ arc ((((k : ℕ) : ℝ) * δ : ℝ) : Circle) (a n)
    have hex : ∃ k, P k := ⟨j, hjmiss⟩
    let k := Nat.find hex
    have hkP : P k := Nat.find_spec hex
    have hkj : k ≤ j := Nat.find_min' hex hjmiss
    have hkL : k < L + 1 := Nat.lt_succ_of_le (hkj.trans hjL)
    apply mem_iUnion.2
    refine ⟨(⟨k, hkL⟩ : Fin (L + 1)), ?_⟩
    rw [mem_firstMissEvent_iff]
    refine ⟨hkP, fun i hi ↦ ?_⟩
    have hik : i < k := by simpa only [Fin.val_mk] using hi
    have hnot : ¬ P i := Nat.find_min hex hik
    dsimp only [P] at hnot
    push Not at hnot
    obtain ⟨n, hnM, hn⟩ := hnot
    have hhit : (((i : ℕ) : ℝ) * δ : Circle) ∈ arc (ω n) (a n) := by
      simpa only [arc, Metric.mem_ball, dist_comm] using hn
    exact ⟨n, hnM, hhit⟩

lemma firstMissEvent_correlation
    {a : ℕ → ℝ} (M : ℕ) {δ t : ℝ} (j : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hδ : 0 ≤ δ) (ht₀ : 0 ≤ t) (ht : t ≤ 1 / 4)
    (hx : (j : ℝ) * δ + t ≤ 1 / 2) :
    sampleMeasure.real (firstMissEvent a M δ j) *
        finiteMissKernel a M t ≤
      sampleMeasure.real
          (firstMissAndMissEvent a M δ j ((j : ℝ) * δ + t)) *
        ∏ n ∈ Finset.range M, (1 - a n) := by
  let p : Fin j → ℝ := fun i ↦ (i : ℝ) * δ
  let q : ℝ := (j : ℝ) * δ
  let x : ℝ := q + t
  have hpq : ∀ i, p i ≤ q := by
    intro i
    dsimp only [p, q]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_of_lt i.isLt)) hδ
  have hqx : q ≤ x := by dsimp only [x]; linarith
  have hxq : x - q ≤ 1 / 4 := by dsimp only [x]; linarith
  have hxp : ∀ i, x - p i ≤ 1 / 2 := by
    intro i
    have hpi : 0 ≤ p i := mul_nonneg (Nat.cast_nonneg _) hδ
    dsimp only [x, q] at hx ⊢
    dsimp only [p] at hpi ⊢
    linarith
  have hcorr := weightedCoverEvent_correlation ha₀ ha hpq hqx hxq hxp
    (List.range M) List.nodup_range Finset.univ
  change sampleMeasure.real (firstMissEvent a M δ j) *
      (∏ n ∈ (List.range M).toFinset,
        (1 - 2 * a n + max (a n - |q - x|) 0)) ≤
    sampleMeasure.real (firstMissAndMissEvent a M δ j x) *
      ∏ n ∈ (List.range M).toFinset, (1 - a n) at hcorr
  have habs : |q - x| = t := by
    dsimp only [x]
    rw [show q - (q + t) = -t by ring, abs_neg, abs_of_nonneg ht₀]
  simpa only [List.toFinset_range, finiteMissKernel, habs, p, q, x] using hcorr

def gridPairSet (L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (L + 1)).product (Finset.range L)

lemma gridPairSet_sum_lt_two_mul {L : ℕ} {jr : ℕ × ℕ}
    (hjr : jr ∈ gridPairSet L) : jr.1 + jr.2 < 2 * L := by
  change jr ∈ (Finset.range (L + 1)).product (Finset.range L) at hjr
  have h := Finset.mem_product.1 hjr
  simp only [Finset.mem_range] at h
  omega

lemma sum_firstMissAndMiss_fiber_le
    {a : ℕ → ℝ} (M : ℕ) {δ : ℝ} (L k : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    (∑ jr ∈ (gridPairSet L).filter (fun jr ↦ jr.1 + jr.2 = k),
        sampleMeasure.real
          (firstMissAndMissEvent a M δ jr.1 ((k : ℝ) * δ))) ≤
      ∏ n ∈ Finset.range M, (1 - a n) := by
  classical
  let J : Finset (ℕ × ℕ) :=
    (gridPairSet L).filter (fun jr ↦ jr.1 + jr.2 = k)
  let E : {jr // jr ∈ J} → Set Sample := fun jr ↦
    firstMissAndMissEvent a M δ (jr : ℕ × ℕ).1 ((k : ℝ) * δ)
  have hdisj : ∀ ⦃u v : {jr // jr ∈ J}⦄, u ≠ v →
      Disjoint (E u) (E v) := by
    intro u v huv
    apply pairwiseDisjoint_firstMissAndMissEvent a M δ ((k : ℝ) * δ)
    intro hj
    apply huv
    apply Subtype.ext
    apply Prod.ext hj
    have hu : (u : ℕ × ℕ).1 + (u : ℕ × ℕ).2 = k := by
      exact (Finset.mem_filter.1 u.2).2
    have hv : (v : ℕ × ℕ).1 + (v : ℕ × ℕ).2 = k := by
      exact (Finset.mem_filter.1 v.2).2
    omega
  have hmeas : ∀ u, MeasurableSet (E u) := fun u ↦
    measurableSet_firstMissAndMissEvent a M δ
      (u : ℕ × ℕ).1 ((k : ℝ) * δ)
  have hsum : sampleMeasure.real (⋃ u, E u) =
      ∑ u, sampleMeasure.real (E u) :=
    measureReal_iUnion_fintype hdisj hmeas
  have hsubset : (⋃ u, E u) ⊆
      ⋂ n ∈ Finset.range M, missEvent a (((k : ℝ) * δ : ℝ) : Circle) n := by
    intro ω hω
    obtain ⟨u, hu⟩ := mem_iUnion.1 hω
    exact firstMissAndMissEvent_subset_allMiss a M δ (u : ℕ × ℕ).1
      ((k : ℝ) * δ) hu
  change (∑ jr ∈ J, sampleMeasure.real
      (firstMissAndMissEvent a M δ jr.1 ((k : ℝ) * δ))) ≤ _
  rw [Finset.sum_subtype J (fun _ ↦ Iff.rfl)]
  change (∑ u, sampleMeasure.real (E u)) ≤ _
  rw [← hsum]
  calc
    sampleMeasure.real (⋃ u, E u) ≤
        sampleMeasure.real
          (⋂ n ∈ Finset.range M,
            missEvent a (((k : ℝ) * δ : ℝ) : Circle) n) :=
      measureReal_mono hsubset
    _ = ∏ n ∈ Finset.range M, (1 - a n) :=
      measureReal_iInter_missEvent M _ ha₀
        (fun n ↦ (ha n).trans (by norm_num))

lemma sum_firstMissAndMiss_gridPairSet_le
    {a : ℕ → ℝ} (M : ℕ) {δ : ℝ} (L : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    (∑ jr ∈ gridPairSet L,
        sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
          (((jr.1 + jr.2 : ℕ) : ℝ) * δ))) ≤
      (2 * L : ℕ) * ∏ n ∈ Finset.range M, (1 - a n) := by
  classical
  let S := gridPairSet L
  let g : ℕ × ℕ → ℕ := fun jr ↦ jr.1 + jr.2
  let f : ℕ × ℕ → ℝ := fun jr ↦
    sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
      ((g jr : ℝ) * δ))
  have hmap : ∀ jr ∈ S, g jr ∈ Finset.range (2 * L) := by
    intro jr hjr
    simp only [Finset.mem_range]
    exact gridPairSet_sum_lt_two_mul hjr
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap f
  change (∑ k ∈ Finset.range (2 * L),
      ∑ jr ∈ S with g jr = k, f jr) = ∑ jr ∈ S, f jr at hfiber
  rw [← hfiber]
  calc
    (∑ k ∈ Finset.range (2 * L), ∑ jr ∈ S with g jr = k, f jr) ≤
        ∑ _k ∈ Finset.range (2 * L),
          ∏ n ∈ Finset.range M, (1 - a n) := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : (∑ jr ∈ S.filter (fun jr ↦ g jr = k), f jr) =
          ∑ jr ∈ (gridPairSet L).filter (fun jr ↦ jr.1 + jr.2 = k),
            sampleMeasure.real
              (firstMissAndMissEvent a M δ jr.1 ((k : ℝ) * δ)) := by
        apply Finset.sum_congr
        · rfl
        · intro jr hjr
          have hsum : g jr = k := (Finset.mem_filter.1 hjr).2
          dsimp only [f]
          rw [hsum]
      rw [hf]
      exact sum_firstMissAndMiss_fiber_le M L k ha₀ ha
    _ = (2 * L : ℕ) * ∏ n ∈ Finset.range M, (1 - a n) := by
      simp

lemma finiteGridMiss_mul_sum_missKernel_le
    {a : ℕ → ℝ} (M : ℕ) {δ : ℝ} (L : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hδ : 0 ≤ δ) (hmesh : (L : ℝ) * δ ≤ 1 / 4) :
    sampleMeasure.real (finiteGridMissEvent a M δ L) *
        (∑ r ∈ Finset.range L, finiteMissKernel a M ((r : ℝ) * δ)) ≤
      (2 * L : ℕ) * (∏ n ∈ Finset.range M, (1 - a n)) ^ 2 := by
  classical
  let S := gridPairSet L
  let one : ℝ := ∏ n ∈ Finset.range M, (1 - a n)
  have hone : 0 ≤ one := by
    dsimp only [one]
    exact Finset.prod_nonneg fun n _ ↦ by linarith [ha n]
  have hcorr : ∀ jr ∈ S,
      sampleMeasure.real (firstMissEvent a M δ jr.1) *
          finiteMissKernel a M ((jr.2 : ℝ) * δ) ≤
        sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
            (((jr.1 + jr.2 : ℕ) : ℝ) * δ)) * one := by
    intro jr hjr
    have hjrmem : jr.1 < L + 1 ∧ jr.2 < L := by
      change jr ∈ (Finset.range (L + 1)).product (Finset.range L) at hjr
      have h := Finset.mem_product.1 hjr
      simpa only [Finset.mem_range] using h
    have hjle : (jr.1 : ℝ) ≤ L := by
      exact_mod_cast Nat.le_of_lt_succ hjrmem.1
    have hrle : (jr.2 : ℝ) ≤ L := by
      exact_mod_cast Nat.le_of_lt hjrmem.2
    have ht₀ : 0 ≤ (jr.2 : ℝ) * δ :=
      mul_nonneg (Nat.cast_nonneg _) hδ
    have hjmul : (jr.1 : ℝ) * δ ≤ (L : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hjle hδ
    have hrmul : (jr.2 : ℝ) * δ ≤ (L : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hrle hδ
    have ht : (jr.2 : ℝ) * δ ≤ 1 / 4 := hrmul.trans hmesh
    have hx : (jr.1 : ℝ) * δ + (jr.2 : ℝ) * δ ≤ 1 / 2 := by
      linarith
    have hc := firstMissEvent_correlation M jr.1 ha₀ ha hδ ht₀ ht hx
    simpa only [one, Nat.cast_add, add_mul] using hc
  have hsum : (∑ jr ∈ S,
      sampleMeasure.real (firstMissEvent a M δ jr.1) *
        finiteMissKernel a M ((jr.2 : ℝ) * δ)) ≤
      ∑ jr ∈ S,
        sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
          (((jr.1 + jr.2 : ℕ) : ℝ) * δ)) * one :=
    Finset.sum_le_sum hcorr
  have hleft : (∑ jr ∈ S,
      sampleMeasure.real (firstMissEvent a M δ jr.1) *
        finiteMissKernel a M ((jr.2 : ℝ) * δ)) =
      sampleMeasure.real (finiteGridMissEvent a M δ L) *
        (∑ r ∈ Finset.range L,
          finiteMissKernel a M ((r : ℝ) * δ)) := by
    have hprod := Finset.sum_product (Finset.range (L + 1))
      (Finset.range L) (fun jr : ℕ × ℕ ↦
        sampleMeasure.real (firstMissEvent a M δ jr.1) *
          finiteMissKernel a M ((jr.2 : ℝ) * δ))
    have hprod' : (∑ jr ∈ S,
        sampleMeasure.real (firstMissEvent a M δ jr.1) *
          finiteMissKernel a M ((jr.2 : ℝ) * δ)) =
        ∑ j ∈ Finset.range (L + 1), ∑ r ∈ Finset.range L,
          sampleMeasure.real (firstMissEvent a M δ j) *
            finiteMissKernel a M ((r : ℝ) * δ) := by
      simpa only [S, gridPairSet, Finset.product_eq_sprod] using hprod
    rw [hprod']
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    congr 1
    rw [measureReal_finiteGridMissEvent]
    symm
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ sampleMeasure.real (firstMissEvent a M δ j)) (L + 1)
  have hright : (∑ jr ∈ S,
      sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
        (((jr.1 + jr.2 : ℕ) : ℝ) * δ)) * one) =
      (∑ jr ∈ S, sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
        (((jr.1 + jr.2 : ℕ) : ℝ) * δ))) * one := by
    rw [Finset.sum_mul]
  rw [hleft, hright] at hsum
  calc
    sampleMeasure.real (finiteGridMissEvent a M δ L) *
        (∑ r ∈ Finset.range L, finiteMissKernel a M ((r : ℝ) * δ)) ≤
        (∑ jr ∈ S, sampleMeasure.real (firstMissAndMissEvent a M δ jr.1
          (((jr.1 + jr.2 : ℕ) : ℝ) * δ))) * one := hsum
    _ ≤ ((2 * L : ℕ) * one) * one := by
      apply mul_le_mul_of_nonneg_right _ hone
      exact sum_firstMissAndMiss_gridPairSet_le M L ha₀ ha
    _ = (2 * L : ℕ) * (∏ n ∈ Finset.range M, (1 - a n)) ^ 2 := by
      dsimp only [one]
      ring

lemma finiteGridMiss_mul_sum_normalizedKernel_le
    {a : ℕ → ℝ} (M : ℕ) {δ : ℝ} (L : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hδ : 0 ≤ δ) (hmesh : (L : ℝ) * δ ≤ 1 / 4) :
    sampleMeasure.real (finiteGridMissEvent a M δ L) *
        (∑ r ∈ Finset.range L,
          finiteNormalizedKernel a M ((r : ℝ) * δ)) ≤
      (2 * L : ℕ) := by
  let one : ℝ := ∏ n ∈ Finset.range M, (1 - a n)
  have hone : 0 < one := by
    dsimp only [one]
    exact Finset.prod_pos fun n _ ↦ by linarith [ha n]
  have hraw := finiteGridMiss_mul_sum_missKernel_le M L ha₀ ha hδ hmesh
  have hsum : (∑ r ∈ Finset.range L,
      finiteMissKernel a M ((r : ℝ) * δ)) =
      one ^ 2 * ∑ r ∈ Finset.range L,
        finiteNormalizedKernel a M ((r : ℝ) * δ) := by
    simp_rw [finiteMissKernel_eq_mul_finiteNormalizedKernel M ha]
    rw [← Finset.mul_sum]
  rw [hsum] at hraw
  have hone2 : 0 < one ^ 2 := sq_pos_of_pos hone
  nlinarith

lemma normalizedFactor_antitone {a s t : ℝ}
    (ha : a ≤ 1 / 4) (hst : s ≤ t) :
    (1 - 2 * a + max (a - t) 0) / (1 - a) ^ 2 ≤
      (1 - 2 * a + max (a - s) 0) / (1 - a) ^ 2 := by
  have hden : 0 < (1 - a) ^ 2 := sq_pos_of_pos (by linarith)
  apply (div_le_div_iff_of_pos_right hden).2
  have hsub : a - t ≤ a - s := by linarith
  linarith [max_le_max hsub (le_refl (0 : ℝ))]

lemma finiteNormalizedKernel_antitone_nonneg
    {a : ℕ → ℝ} (M : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    AntitoneOn (finiteNormalizedKernel a M) (Ici 0) := by
  intro s hs t ht hst
  unfold finiteNormalizedKernel
  apply Finset.prod_le_prod
  · intro n hn
    exact normalizedFactor_nonneg (ha₀ n) (ha n)
  · intro n hn
    exact normalizedFactor_antitone (ha n) hst

lemma integral_finiteNormalizedKernel_le_leftSum
    {a : ℕ → ℝ} (M L : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ), finiteNormalizedKernel a M t) ≤
      δ * ∑ r ∈ Finset.range L,
        finiteNormalizedKernel a M ((r : ℝ) * δ) := by
  let f : ℝ → ℝ := finiteNormalizedKernel a M
  let p : ℕ → ℝ := fun r ↦ (r : ℝ) * δ
  have hpmono : Monotone p := fun i j hij ↦
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hδ
  have hfcont : Continuous f := continuous_finiteNormalizedKernel a M
  have hcell (r : ℕ) : (∫ t in p r..p (r + 1), f t) ≤
      δ * f (p r) := by
    have hpr : p r ≤ p (r + 1) := hpmono (Nat.le_succ r)
    have hfint : IntervalIntegrable f volume (p r) (p (r + 1)) :=
      hfcont.intervalIntegrable _ _
    have hcint : IntervalIntegrable (fun _ : ℝ ↦ f (p r)) volume
        (p r) (p (r + 1)) := intervalIntegrable_const
    calc
      (∫ t in p r..p (r + 1), f t) ≤
          ∫ _t in p r..p (r + 1), f (p r) := by
        apply intervalIntegral.integral_mono_on hpr hfint hcint
        intro t ht
        have hpr0 : p r ∈ Ici (0 : ℝ) := by
          exact mul_nonneg (Nat.cast_nonneg r) hδ
        have ht0 : t ∈ Ici (0 : ℝ) := hpr0.trans ht.1
        exact finiteNormalizedKernel_antitone_nonneg (a := a) M ha₀ ha
          hpr0 ht0 ht.1
      _ = δ * f (p r) := by
        rw [intervalIntegral.integral_const]
        dsimp only [p]
        norm_num only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
        ring
  have hsumint : (∑ r ∈ Finset.range L, ∫ t in p r..p (r + 1), f t) =
      ∫ t in p 0..p L, f t :=
    intervalIntegral.sum_integral_adjacent_intervals
      (fun r hr ↦ hfcont.intervalIntegrable _ _)
  have hsumle : (∑ r ∈ Finset.range L, ∫ t in p r..p (r + 1), f t) ≤
      ∑ r ∈ Finset.range L, δ * f (p r) :=
    Finset.sum_le_sum fun r hr ↦ hcell r
  have hL : 0 ≤ (L : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  rw [hsumint] at hsumle
  dsimp only [p] at hsumle
  norm_num only [Nat.cast_zero, zero_mul] at hsumle
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL]
  calc
    (∫ t in (0 : ℝ)..(L : ℝ) * δ, finiteNormalizedKernel a M t) ≤
        ∑ r ∈ Finset.range L,
          δ * finiteNormalizedKernel a M ((r : ℝ) * δ) := hsumle
    _ = δ * ∑ r ∈ Finset.range L,
        finiteNormalizedKernel a M ((r : ℝ) * δ) := by
      rw [Finset.mul_sum]

lemma finiteGridMiss_mul_integral_normalizedKernel_le
    {a : ℕ → ℝ} (M L : ℕ) {δ : ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hδ : 0 ≤ δ) (hmesh : (L : ℝ) * δ ≤ 1 / 4) :
    sampleMeasure.real (finiteGridMissEvent a M δ L) *
        (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
          finiteNormalizedKernel a M t) ≤
      2 * ((L : ℝ) * δ) := by
  let P := sampleMeasure.real (finiteGridMissEvent a M δ L)
  let R := ∑ r ∈ Finset.range L,
    finiteNormalizedKernel a M ((r : ℝ) * δ)
  have hP : 0 ≤ P := measureReal_nonneg
  have hint := integral_finiteNormalizedKernel_le_leftSum M L hδ ha₀ ha
  have hgrid := finiteGridMiss_mul_sum_normalizedKernel_le M L ha₀ ha hδ hmesh
  change P * R ≤ (2 * L : ℕ) at hgrid
  change (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
    finiteNormalizedKernel a M t) ≤ δ * R at hint
  calc
    P * (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
        finiteNormalizedKernel a M t) ≤ P * (δ * R) :=
      mul_le_mul_of_nonneg_left hint hP
    _ = δ * (P * R) := by ring
    _ ≤ δ * (2 * L : ℕ) := mul_le_mul_of_nonneg_left hgrid hδ
    _ = 2 * ((L : ℝ) * δ) := by push_cast; ring

lemma exists_localGridPoint_dist_lt
    {x δ : ℝ} {L : ℕ} (hx₀ : 0 ≤ x) (hxL : x ≤ (L : ℝ) * δ)
    (hδ : 0 < δ) :
    ∃ j ≤ L, dist (x : Circle) (((j : ℝ) * δ : ℝ) : Circle) < δ := by
  let j : ℕ := ⌊x / δ⌋₊
  have hxdiv : 0 ≤ x / δ := div_nonneg hx₀ hδ.le
  have hjle : (j : ℝ) ≤ x / δ := Nat.floor_le hxdiv
  have hxlt : x / δ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjx : (j : ℝ) * δ ≤ x := by
    apply (le_div_iff₀ hδ).1
    simpa only [mul_comm] using hjle
  have hxj : x < ((j : ℝ) + 1) * δ := by
    exact (div_lt_iff₀ hδ).1 hxlt
  have hjL : j ≤ L := by
    have hmul : (j : ℝ) * δ ≤ (L : ℝ) * δ := hjx.trans hxL
    by_contra hnot
    have hlt : (L : ℝ) < j := by exact_mod_cast Nat.lt_of_not_ge hnot
    have := mul_lt_mul_of_pos_right hlt hδ
    linarith
  refine ⟨j, hjL, ?_⟩
  have habs : |x - (j : ℝ) * δ| < δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hjx)]
    linarith
  calc
    dist (x : Circle) (((j : ℝ) * δ : ℝ) : Circle) =
        ‖((x - (j : ℝ) * δ : ℝ) : Circle)‖ := by
      rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
    _ ≤ ‖x - (j : ℝ) * δ‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |x - (j : ℝ) * δ| := Real.norm_eq_abs _
    _ < δ := habs

def localFiniteCoverEvent
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) : Set Sample :=
  {ω | ∀ x ∈ Icc (0 : ℝ) ε, ∃ n < M,
    (x : Circle) ∈ arc (ω n) (a n)}

def localFiniteMissPairs
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) : Set (Sample × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) ε ∧
    ∀ n ∈ Finset.range M, a n / 2 ≤ dist (p.2 : Circle) (p.1 n)}

lemma isClosed_localFiniteMissPairs
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    IsClosed (localFiniteMissPairs a M ε) := by
  simp only [localFiniteMissPairs, setOf_and, setOf_forall]
  apply IsClosed.inter
  · exact isClosed_Icc.preimage continuous_snd
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro hn
  exact isClosed_le continuous_const
    ((((QuotientAddGroup.continuous_mk.comp continuous_snd).dist
      ((continuous_apply n).comp continuous_fst))))

lemma localFiniteCoverEvent_compl
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    (localFiniteCoverEvent a M ε)ᶜ =
      Prod.fst '' localFiniteMissPairs a M ε := by
  ext ω
  simp only [localFiniteCoverEvent, mem_compl_iff, mem_setOf_eq, mem_image,
    localFiniteMissPairs, Finset.mem_range, arc, Metric.mem_ball,
    not_forall, not_exists, not_and, not_lt]
  constructor
  · rintro ⟨x, hxI, hx⟩
    exact ⟨(ω, x), ⟨hxI, hx⟩, rfl⟩
  · rintro ⟨⟨ω', x⟩, ⟨hxI, hx⟩, hω⟩
    simp only [Prod.fst] at hω
    subst ω'
    exact ⟨x, hxI, hx⟩

lemma measurableSet_localFiniteCoverEvent
    (a : ℕ → ℝ) (M : ℕ) (ε : ℝ) :
    MeasurableSet (localFiniteCoverEvent a M ε) := by
  have hcompact : IsCompact (localFiniteMissPairs a M ε) := by
    apply (isCompact_univ.prod isCompact_Icc).of_isClosed_subset
      (isClosed_localFiniteMissPairs a M ε)
    intro p hp
    exact ⟨mem_univ p.1, hp.1⟩
  have hc : IsClosed ((localFiniteCoverEvent a M ε)ᶜ) := by
    rw [localFiniteCoverEvent_compl]
    exact (hcompact.image continuous_fst).isClosed
  simpa using hc.isOpen_compl.measurableSet

lemma localFiniteCoverEvent_compl_subset_gridMiss_shrunken
    {a : ℕ → ℝ} (M L : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (localFiniteCoverEvent a M ((L : ℝ) * δ))ᶜ ⊆
      finiteGridMissEvent (fun n ↦ a n - 2 * δ) M δ L := by
  intro ω hω
  rw [mem_compl_iff] at hω
  simp only [localFiniteCoverEvent, mem_setOf_eq] at hω
  push Not at hω
  obtain ⟨x, ⟨hx₀, hxL⟩, hxmiss⟩ := hω
  obtain ⟨j, hjL, hxj⟩ :=
    exists_localGridPoint_dist_lt hx₀ hxL hδ
  rw [mem_finiteGridMissEvent_iff]
  refine ⟨j, hjL, fun n hn ↦ ?_⟩
  intro hcenter
  have hgrid : ((((j : ℕ) : ℝ) * δ : ℝ) : Circle) ∈
      arc (ω n) (a n - 2 * δ) := by
    simpa only [arc, Metric.mem_ball, dist_comm] using hcenter
  apply hxmiss n hn
  change dist (x : Circle) (ω n) < a n / 2
  calc
    dist (x : Circle) (ω n) ≤
        dist (x : Circle) ((((j : ℕ) : ℝ) * δ : ℝ) : Circle) +
          dist ((((j : ℕ) : ℝ) * δ : ℝ) : Circle) (ω n) := dist_triangle _ _ _
    _ < δ + (a n - 2 * δ) / 2 := add_lt_add hxj hgrid
    _ = a n / 2 := by ring

lemma finiteNormalizedKernel_nonneg'
    {a : ℕ → ℝ} (M : ℕ) (t : ℝ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1 / 4) :
    0 ≤ finiteNormalizedKernel a M t := by
  unfold finiteNormalizedKernel
  exact Finset.prod_nonneg fun n _ ↦ normalizedFactor_nonneg (ha₀ n) (ha n)

lemma localFiniteCover_compl_mul_integral_shrunken_le
    {a b : ℕ → ℝ} (M L : ℕ) {δ : ℝ}
    (hb₀ : ∀ n, 0 ≤ b n) (hb : ∀ n, b n ≤ 1 / 4)
    (hδ : 0 < δ) (hmesh : (L : ℝ) * δ ≤ 1 / 4)
    (hshrink : ∀ n < M, b n = a n - 2 * δ) :
    sampleMeasure.real
        ((localFiniteCoverEvent a M ((L : ℝ) * δ))ᶜ) *
        (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
          finiteNormalizedKernel b M t) ≤
      2 * ((L : ℝ) * δ) := by
  have hsubset : (localFiniteCoverEvent a M ((L : ℝ) * δ))ᶜ ⊆
      finiteGridMissEvent b M δ L := by
    intro ω hω
    have hs := localFiniteCoverEvent_compl_subset_gridMiss_shrunken M L hδ hω
    rw [mem_finiteGridMissEvent_iff] at hs ⊢
    obtain ⟨j, hj, hmiss⟩ := hs
    refine ⟨j, hj, fun n hn ↦ ?_⟩
    simpa only [hshrink n hn] using hmiss n hn
  have hprob : sampleMeasure.real
      ((localFiniteCoverEvent a M ((L : ℝ) * δ))ᶜ) ≤
      sampleMeasure.real (finiteGridMissEvent b M δ L) :=
    measureReal_mono hsubset
  have hInt : 0 ≤ (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
      finiteNormalizedKernel b M t) := by
    apply integral_nonneg_of_ae
    filter_upwards [] with t
    exact finiteNormalizedKernel_nonneg' M t hb₀ hb
  calc
    sampleMeasure.real
        ((localFiniteCoverEvent a M ((L : ℝ) * δ))ᶜ) *
        (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
          finiteNormalizedKernel b M t) ≤
      sampleMeasure.real (finiteGridMissEvent b M δ L) *
        (∫ t in Icc (0 : ℝ) ((L : ℝ) * δ),
          finiteNormalizedKernel b M t) :=
      mul_le_mul_of_nonneg_right hprob hInt
    _ ≤ 2 * ((L : ℝ) * δ) :=
      finiteGridMiss_mul_integral_normalizedKernel_le M L hb₀ hb hδ.le hmesh

def prefixShrink (a : ℕ → ℝ) (M : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  if n < M then a n - 2 * δ else a n

lemma prefixShrink_eq {a : ℕ → ℝ} {M n : ℕ} {δ : ℝ} (hn : n < M) :
    prefixShrink a M δ n = a n - 2 * δ := by
  simp [prefixShrink, hn]

lemma prefixShrink_nonneg {a : ℕ → ℝ} {M : ℕ} {δ : ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (hsmall : ∀ n < M, 2 * δ ≤ a n) :
    ∀ n, 0 ≤ prefixShrink a M δ n := by
  intro n
  by_cases hn : n < M
  · rw [prefixShrink_eq hn]
    linarith [hsmall n hn]
  · simp [prefixShrink, hn, ha₀ n]

lemma prefixShrink_le {a : ℕ → ℝ} {M : ℕ} {δ : ℝ}
    (ha : ∀ n, a n ≤ 1 / 4) (hδ : 0 ≤ δ) :
    ∀ n, prefixShrink a M δ n ≤ 1 / 4 := by
  intro n
  by_cases hn : n < M
  · rw [prefixShrink_eq hn]
    linarith [ha n]
  · simpa only [prefixShrink, if_neg hn] using ha n

lemma finiteOverlapSum_prefixShrink
    (a : ℕ → ℝ) (M : ℕ) (δ t : ℝ) :
    finiteOverlapSum (prefixShrink a M δ) M t =
      finiteOverlapSum a M (t + 2 * δ) := by
  unfold finiteOverlapSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [prefixShrink_eq (Finset.mem_range.1 hn)]
  apply congrArg (fun x : ℝ ↦ max x 0)
  ring

lemma finiteExponentialKernel_prefixShrink
    (a : ℕ → ℝ) (M : ℕ) (δ t : ℝ) :
    finiteExponentialKernel (prefixShrink a M δ) M t =
      finiteExponentialKernel a M (t + 2 * δ) := by
  rw [finiteExponentialKernel, finiteExponentialKernel,
    finiteOverlapSum_prefixShrink]

lemma finiteExponentialKernel_le_exp_prefix
    {a : ℕ → ℝ} (M : ℕ) {t : ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (ht : 0 ≤ t) :
    finiteExponentialKernel a M t ≤ Real.exp (prefixLength a M) := by
  apply Real.exp_le_exp.mpr
  unfold finiteOverlapSum prefixLength
  apply Finset.sum_le_sum
  intro n hn
  have hsub : a n - t ≤ a n := by linarith
  simpa only [max_eq_left (ha₀ n)] using max_le_max hsub (le_refl (0 : ℝ))

lemma finiteEnergy_set_eq_intervalIntegral
    (a : ℕ → ℝ) (M : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEnergy a ε M =
      ∫ t in (0 : ℝ)..ε, finiteExponentialKernel a M t := by
  unfold finiteEnergy
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hε]

lemma finiteEnergy_prefixShrink_ge
    {a : ℕ → ℝ} (M : ℕ) {ε δ : ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (hδ : 0 ≤ δ) (h2δε : 2 * δ ≤ ε) :
    finiteEnergy a ε M - 2 * δ * Real.exp (prefixLength a M) ≤
      finiteEnergy (prefixShrink a M δ) ε M := by
  have hε : 0 ≤ ε := hδ.trans (by linarith)
  let F : ℝ → ℝ := finiteExponentialKernel a M
  have hFcont : Continuous F := continuous_finiteExponentialKernel a M
  have hshift : finiteEnergy (prefixShrink a M δ) ε M =
      ∫ t in (2 * δ)..(ε + 2 * δ), F t := by
    rw [finiteEnergy_set_eq_intervalIntegral _ M hε]
    simp_rw [finiteExponentialKernel_prefixShrink]
    simpa only [zero_add] using
      (intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := ε) F (2 * δ))
  have htail_nonneg : 0 ≤ ∫ t in ε..(ε + 2 * δ), F t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact (finiteExponentialKernel_pos a M t).le
  have hshift_ge : (∫ t in (2 * δ)..ε, F t) ≤
      ∫ t in (2 * δ)..(ε + 2 * δ), F t := by
    have hfirst : IntervalIntegrable F volume (2 * δ) ε :=
      hFcont.intervalIntegrable _ _
    have hsecond : IntervalIntegrable F volume ε (ε + 2 * δ) :=
      hFcont.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      hfirst hsecond
    linarith
  have hloss : (∫ t in (0 : ℝ)..(2 * δ), F t) ≤
      2 * δ * Real.exp (prefixLength a M) := by
    have horder : (0 : ℝ) ≤ 2 * δ := by linarith
    have hFint : IntervalIntegrable F volume 0 (2 * δ) :=
      hFcont.intervalIntegrable _ _
    have hcint : IntervalIntegrable
        (fun _ : ℝ ↦ Real.exp (prefixLength a M)) volume 0 (2 * δ) :=
      intervalIntegrable_const
    calc
      (∫ t in (0 : ℝ)..(2 * δ), F t) ≤
          ∫ _t in (0 : ℝ)..(2 * δ), Real.exp (prefixLength a M) := by
        apply intervalIntegral.integral_mono_on horder hFint hcint
        intro t ht
        exact finiteExponentialKernel_le_exp_prefix M ha₀ ht.1
      _ = 2 * δ * Real.exp (prefixLength a M) := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
  have hsplit : (∫ t in (0 : ℝ)..ε, F t) =
      (∫ t in (0 : ℝ)..(2 * δ), F t) +
        ∫ t in (2 * δ)..ε, F t := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (hFcont.intervalIntegrable 0 (2 * δ))
      (hFcont.intervalIntegrable (2 * δ) ε)
  rw [finiteEnergy_set_eq_intervalIntegral a M hε, hshift]
  linarith

lemma sum_sq_prefixShrink_le
    {a : ℕ → ℝ} (M : ℕ) {δ : ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (hδ : 0 ≤ δ)
    (hsmall : ∀ n < M, 2 * δ ≤ a n) :
    (∑ n ∈ Finset.range M, (prefixShrink a M δ n) ^ 2) ≤
      ∑ n ∈ Finset.range M, (a n) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  rw [prefixShrink_eq (Finset.mem_range.1 hn)]
  have hb₀ : 0 ≤ a n - 2 * δ := by linarith [hsmall n (Finset.mem_range.1 hn)]
  have hba : a n - 2 * δ ≤ a n := by linarith
  nlinarith [sq_nonneg (a n - 2 * δ), sq_nonneg (a n)]

lemma exists_good_local_mesh
    {a : ℕ → ℝ} (M : ℕ) {ε : ℝ}
    (ha : ∀ n, 0 < a n) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      let δ := ε / (L : ℝ)
      0 < δ ∧ (L : ℝ) * δ = ε ∧ 2 * δ ≤ ε ∧
        (∀ n < M, 2 * δ ≤ a n) ∧
        2 * δ * Real.exp (prefixLength a M) ≤ 1 := by
  let d : ℕ → ℝ := fun L ↦ ε / (L : ℝ)
  have hd : Tendsto d atTop (nhds 0) := by
    dsimp only [d]
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun L ↦ 2 * d L) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hd
  have hloss : Tendsto
      (fun L ↦ 2 * d L * Real.exp (prefixLength a M)) atTop (nhds 0) := by
    simpa using htwo.mul_const (Real.exp (prefixLength a M))
  have hsmall : ∀ᶠ L : ℕ in atTop, ∀ n ∈ Finset.range M, 2 * d L < a n := by
    apply (Finset.range M).eventually_all.2
    intro n hn
    exact htwo.eventually (Iio_mem_nhds (ha n))
  have hloss' : ∀ᶠ L : ℕ in atTop,
      2 * d L * Real.exp (prefixLength a M) < 1 :=
    hloss.eventually (Iio_mem_nhds zero_lt_one)
  have hev : ∀ᶠ L : ℕ in atTop,
      0 < L ∧ 2 ≤ L ∧
        (∀ n ∈ Finset.range M, 2 * d L < a n) ∧
        2 * d L * Real.exp (prefixLength a M) < 1 := by
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop 2,
      hsmall, hloss'] with L hL hLtwo hs hl
    exact ⟨hL, hLtwo, hs, hl⟩
  obtain ⟨L, hL, hLtwo, hs, hl⟩ := hev.exists
  refine ⟨L, hL, ?_⟩
  dsimp only
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hdpos : 0 < ε / (L : ℝ) := div_pos hε hLreal
  refine ⟨hdpos, ?_, ?_, ?_, hl.le⟩
  · field_simp
  · rw [show 2 * (ε / (L : ℝ)) = (2 * ε) / (L : ℝ) by ring,
      div_le_iff₀ hLreal]
    have hLtwoReal : (2 : ℝ) ≤ L := by exact_mod_cast hLtwo
    nlinarith
  · intro n hn
    exact (hs n (Finset.mem_range.2 hn)).le

lemma localFiniteCover_failure_energy_bound
    {a : ℕ → ℝ} (M : ℕ) {ε : ℝ}
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hε₀ : 0 < ε) (hε : ε ≤ 1 / 4)
    (hsq : Summable (fun n ↦ (a n) ^ 2))
    (hEM : 1 ≤ finiteEnergy a ε M) :
    sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) *
        (Real.exp (-10 * ∑' n, (a n) ^ 2) *
          (finiteEnergy a ε M - 1)) ≤
      2 * ε := by
  obtain ⟨L, hL, hmeshData⟩ := exists_good_local_mesh M ha₀ hε₀
  let δ : ℝ := ε / (L : ℝ)
  have hδ : 0 < δ := hmeshData.1
  have hLδ : (L : ℝ) * δ = ε := hmeshData.2.1
  have h2δε : 2 * δ ≤ ε := hmeshData.2.2.1
  have hsmall : ∀ n < M, 2 * δ ≤ a n := hmeshData.2.2.2.1
  have hloss : 2 * δ * Real.exp (prefixLength a M) ≤ 1 :=
    hmeshData.2.2.2.2
  let b : ℕ → ℝ := prefixShrink a M δ
  have hb₀ : ∀ n, 0 ≤ b n :=
    prefixShrink_nonneg (fun n ↦ (ha₀ n).le) hsmall
  have hb : ∀ n, b n ≤ 1 / 4 := prefixShrink_le ha hδ.le
  have hlocal := localFiniteCover_compl_mul_integral_shrunken_le
    (a := a) (b := b) M L hb₀ hb hδ (hLδ.trans_le hε)
      (fun n hn ↦ prefixShrink_eq hn)
  rw [hLδ] at hlocal
  let S : ℝ := ∑' n, (a n) ^ 2
  let C : ℝ := Real.exp (-10 * S)
  let SB : ℝ := ∑ n ∈ Finset.range M, (b n) ^ 2
  have hpartial : (∑ n ∈ Finset.range M, (a n) ^ 2) ≤ S := by
    dsimp only [S]
    exact hsq.sum_le_tsum (Finset.range M) (fun n hn ↦ sq_nonneg (a n))
  have hSBpartial : SB ≤ ∑ n ∈ Finset.range M, (a n) ^ 2 := by
    dsimp only [SB, b]
    exact sum_sq_prefixShrink_le M (fun n ↦ (ha₀ n).le) hδ.le hsmall
  have hSB : SB ≤ S := hSBpartial.trans hpartial
  have hcoef : C ≤ Real.exp (-10 * SB) := by
    dsimp only [C]
    apply Real.exp_le_exp.mpr
    nlinarith
  have henergyB : finiteEnergy a ε M - 1 ≤ finiteEnergy b ε M := by
    have hshift := finiteEnergy_prefixShrink_ge M
      (fun n ↦ (ha₀ n).le) hδ.le h2δε
    dsimp only [b]
    linarith
  have hbase : C * (finiteEnergy a ε M - 1) ≤
      Real.exp (-10 * SB) * finiteEnergy b ε M := by
    exact mul_le_mul hcoef henergyB (sub_nonneg.mpr hEM)
      (Real.exp_pos _).le
  have hnorm : Real.exp (-10 * SB) * finiteEnergy b ε M ≤
      ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel b M t := by
    dsimp only [SB]
    exact integral_exponential_le_finiteNormalizedKernel M ε hb₀ hb
  have hlower : C * (finiteEnergy a ε M - 1) ≤
      ∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel b M t :=
    hbase.trans hnorm
  have hP : 0 ≤ sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) :=
    measureReal_nonneg
  calc
    sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) *
        (Real.exp (-10 * ∑' n, (a n) ^ 2) *
          (finiteEnergy a ε M - 1)) =
        sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) *
          (C * (finiteEnergy a ε M - 1)) := by rfl
    _ ≤ sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) *
        (∫ t in Icc (0 : ℝ) ε, finiteNormalizedKernel b M t) :=
      mul_le_mul_of_nonneg_left hlower hP
    _ ≤ 2 * ε := hlocal

theorem tendsto_localFiniteCover_failure
    {a : ℕ → ℝ} {ε : ℝ}
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hε₀ : 0 < ε) (hε : ε ≤ 1 / 4)
    (hsq : Summable (fun n ↦ (a n) ^ 2))
    (henergy : EnergyCondition a ε) :
    Tendsto (fun M ↦ sampleMeasure.real
      ((localFiniteCoverEvent a M ε)ᶜ)) atTop (nhds 0) := by
  let S : ℝ := ∑' n, (a n) ^ 2
  let C : ℝ := Real.exp (-10 * S)
  let D : ℕ → ℝ := fun M ↦ C * (finiteEnergy a ε M - 1)
  have hC : 0 < C := Real.exp_pos _
  have hD : Tendsto D atTop atTop := by
    rw [tendsto_atTop]
    intro R
    let htarget : ℝ := R / C + 1
    filter_upwards [tendsto_atTop.1 henergy htarget] with M hM
    dsimp only [D]
    dsimp only [htarget] at hM
    have hdiv : R / C * C = R := div_mul_cancel₀ R hC.ne'
    nlinarith
  have hEone : ∀ᶠ M : ℕ in atTop, 1 ≤ finiteEnergy a ε M :=
    tendsto_atTop.1 henergy 1
  have hDpos : ∀ᶠ M : ℕ in atTop, 0 < D M := by
    filter_upwards [tendsto_atTop.1 hD 1] with M hM
    linarith
  let Q : ℕ → ℝ := fun M ↦ 2 * ε / D M
  have hQ : Tendsto Q atTop (nhds 0) := by
    dsimp only [Q]
    simpa using tendsto_const_nhds.div_atTop hD
  have hbound : ∀ᶠ M : ℕ in atTop,
      sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) ≤ Q M := by
    filter_upwards [hEone, hDpos] with M hEM hDM
    have hmul := localFiniteCover_failure_energy_bound M ha₀ ha hε₀ hε hsq hEM
    change sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) * D M ≤
      2 * ε at hmul
    exact (le_div_iff₀ hDM).2 hmul
  apply squeeze_zero'
  · filter_upwards [] with M
    exact measureReal_nonneg
  · exact hbound
  · exact hQ

def sampleShift (c : ℝ) (ω : Sample) : Sample :=
  fun n ↦ ω n + (c : Circle)

lemma measurable_sampleShift (c : ℝ) : Measurable (sampleShift c) := by
  unfold sampleShift
  fun_prop

lemma map_sampleShift_sampleMeasure (c : ℝ) :
    sampleMeasure.map (sampleShift c) = sampleMeasure := by
  have hmap := Measure.infinitePi_map_pi
    (fun _ : ℕ ↦ uniformCircle)
    (f := fun _ z ↦ z + (c : Circle)) (fun _ ↦ by fun_prop)
  calc
    sampleMeasure.map (sampleShift c) =
        Measure.infinitePi (fun _ : ℕ ↦
          uniformCircle.map (fun z ↦ z + (c : Circle))) := by
      change Measure.map (fun ω : ℕ → Circle ↦ fun n ↦ ω n + (c : Circle))
          (Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)) = _
      exact hmap
    _ = Measure.infinitePi (fun _ : ℕ ↦ uniformCircle) := by
      congr 1
      funext n
      rw [uniformCircle_eq_volume]
      exact Measure.IsAddRightInvariant.map_add_right_eq_self (c : Circle)
    _ = sampleMeasure := rfl

def localFiniteCoverEventAt
    (a : ℕ → ℝ) (M : ℕ) (c ε : ℝ) : Set Sample :=
  {ω | ∀ x ∈ Icc c (c + ε), ∃ n < M,
    (x : Circle) ∈ arc (ω n) (a n)}

lemma measurableSet_localFiniteCoverEventAt
    (a : ℕ → ℝ) (M : ℕ) (c ε : ℝ) :
    MeasurableSet (localFiniteCoverEventAt a M c ε) := by
  have hpre : sampleShift (-c) ⁻¹' localFiniteCoverEvent a M ε =
      localFiniteCoverEventAt a M c ε := by
    ext ω
    simp only [mem_preimage, localFiniteCoverEvent, localFiniteCoverEventAt,
      mem_setOf_eq]
    constructor
    · intro h x hx
      have hy : x - c ∈ Icc (0 : ℝ) ε := by
        constructor <;> linarith [hx.1, hx.2]
      obtain ⟨n, hn, hhit⟩ := h (x - c) hy
      refine ⟨n, hn, ?_⟩
      have hxcoe : (x : Circle) =
          ((x - c : ℝ) : Circle) + (c : Circle) := by
        rw [← QuotientAddGroup.mk_add (AddSubgroup.zmultiples (1 : ℝ))]
        congr 1
        ring
      have hcenter : ω n = sampleShift (-c) ω n + (c : Circle) := by
        change ω n = (ω n + ((-c : ℝ) : Circle)) + (c : Circle)
        rw [QuotientAddGroup.mk_neg (AddSubgroup.zmultiples (1 : ℝ))]
        simp
      change dist (x : Circle) (ω n) < a n / 2
      rw [hxcoe, hcenter, dist_add_right]
      exact hhit
    · intro h y hy
      have hx : y + c ∈ Icc c (c + ε) := by
        constructor <;> linarith [hy.1, hy.2]
      obtain ⟨n, hn, hhit⟩ := h (y + c) hx
      refine ⟨n, hn, ?_⟩
      have hycoe : ((y + c : ℝ) : Circle) =
          (y : Circle) + (c : Circle) :=
        QuotientAddGroup.mk_add (AddSubgroup.zmultiples (1 : ℝ)) y c
      have hcenter : ω n = sampleShift (-c) ω n + (c : Circle) := by
        change ω n = (ω n + ((-c : ℝ) : Circle)) + (c : Circle)
        rw [QuotientAddGroup.mk_neg (AddSubgroup.zmultiples (1 : ℝ))]
        simp
      change dist ((y + c : ℝ) : Circle) (ω n) < a n / 2 at hhit
      rw [hycoe, hcenter, dist_add_right] at hhit
      exact hhit
  rw [← hpre]
  exact (measurableSet_localFiniteCoverEvent a M ε).preimage
    (measurable_sampleShift (-c))

lemma sampleShift_preimage_localFiniteCoverEventAt
    (a : ℕ → ℝ) (M : ℕ) (c ε : ℝ) :
    sampleShift c ⁻¹' localFiniteCoverEventAt a M c ε =
      localFiniteCoverEvent a M ε := by
  ext ω
  simp only [mem_preimage, localFiniteCoverEvent, localFiniteCoverEventAt,
    mem_setOf_eq]
  constructor
  · intro h y hy
    have hx : y + c ∈ Icc c (c + ε) := by
      constructor <;> linarith [hy.1, hy.2]
    obtain ⟨n, hn, hhit⟩ := h (y + c) hx
    refine ⟨n, hn, ?_⟩
    change dist (y : Circle) (ω n) < a n / 2
    have hycoe : ((y + c : ℝ) : Circle) = (y : Circle) + (c : Circle) := by
      exact QuotientAddGroup.mk_add (AddSubgroup.zmultiples (1 : ℝ)) y c
    change dist ((y + c : ℝ) : Circle) (sampleShift c ω n) < a n / 2 at hhit
    rw [sampleShift, hycoe, dist_add_right] at hhit
    exact hhit
  · intro h x hx
    have hy : x - c ∈ Icc (0 : ℝ) ε := by
      constructor <;> linarith [hx.1, hx.2]
    obtain ⟨n, hn, hhit⟩ := h (x - c) hy
    refine ⟨n, hn, ?_⟩
    change dist (x : Circle) (sampleShift c ω n) < a n / 2
    have hxcoe : (x : Circle) = ((x - c : ℝ) : Circle) + (c : Circle) := by
      rw [← QuotientAddGroup.mk_add (AddSubgroup.zmultiples (1 : ℝ))]
      congr 1
      ring
    rw [sampleShift, hxcoe, dist_add_right]
    exact hhit

lemma measureReal_localFiniteCoverEventAt_compl
    (a : ℕ → ℝ) (M : ℕ) (c ε : ℝ) :
    sampleMeasure.real ((localFiniteCoverEventAt a M c ε)ᶜ) =
      sampleMeasure.real ((localFiniteCoverEvent a M ε)ᶜ) := by
  have hmeas : MeasurableSet ((localFiniteCoverEventAt a M c ε)ᶜ) :=
    (measurableSet_localFiniteCoverEventAt a M c ε).compl
  have hpre : sampleShift c ⁻¹' ((localFiniteCoverEventAt a M c ε)ᶜ) =
      (localFiniteCoverEvent a M ε)ᶜ := by
    rw [preimage_compl, sampleShift_preimage_localFiniteCoverEventAt]
  rw [measureReal_def]
  calc
    (sampleMeasure ((localFiniteCoverEventAt a M c ε)ᶜ)).toReal =
        ((sampleMeasure.map (sampleShift c))
          ((localFiniteCoverEventAt a M c ε)ᶜ)).toReal := by
      rw [map_sampleShift_sampleMeasure]
    _ = (sampleMeasure
          (sampleShift c ⁻¹' ((localFiniteCoverEventAt a M c ε)ᶜ))).toReal := by
      rw [Measure.map_apply (measurable_sampleShift c) hmeas]
    _ = (sampleMeasure ((localFiniteCoverEvent a M ε)ᶜ)).toReal := by
      rw [hpre]

theorem tendsto_localFiniteCoverAt_failure
    {a : ℕ → ℝ} {ε : ℝ} (c : ℝ)
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hε₀ : 0 < ε) (hε : ε ≤ 1 / 4)
    (hsq : Summable (fun n ↦ (a n) ^ 2))
    (henergy : EnergyCondition a ε) :
    Tendsto (fun M ↦ sampleMeasure.real
      ((localFiniteCoverEventAt a M c ε)ᶜ)) atTop (nhds 0) := by
  convert tendsto_localFiniteCover_failure ha₀ ha hε₀ hε hsq henergy using 1
  ext M
  exact measureReal_localFiniteCoverEventAt_compl a M c ε

/-- Four consecutive real intervals of length `1/4` represent the whole
unit circle. -/
lemma finiteCovers_of_four_quarters
    {a : ℕ → ℝ} {ω : Sample} {M : ℕ}
    (h₀ : ω ∈ localFiniteCoverEventAt a M 0 (1 / 4))
    (h₁ : ω ∈ localFiniteCoverEventAt a M (1 / 4) (1 / 4))
    (h₂ : ω ∈ localFiniteCoverEventAt a M (1 / 2) (1 / 4))
    (h₃ : ω ∈ localFiniteCoverEventAt a M (3 / 4) (1 / 4)) :
    FiniteCovers a ω 0 M := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  let r : ℝ := Int.fract c
  have hr₀ : 0 ≤ r := Int.fract_nonneg c
  have hr₁ : r < 1 := Int.fract_lt_one c
  have hcoe : (c : Circle) = (r : Circle) := by
    rw [QuotientAddGroup.eq]
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨-⌊c⌋, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    change ((-⌊c⌋ : ℤ) : ℝ) = -c + r
    simp only [Int.cast_neg, r, Int.fract]
    ring
  rw [hcoe]
  change (∀ y ∈ Icc (0 : ℝ) (0 + 1 / 4), ∃ n < M,
    (y : Circle) ∈ arc (ω n) (a n)) at h₀
  change (∀ y ∈ Icc (1 / 4 : ℝ) (1 / 4 + 1 / 4), ∃ n < M,
    (y : Circle) ∈ arc (ω n) (a n)) at h₁
  change (∀ y ∈ Icc (1 / 2 : ℝ) (1 / 2 + 1 / 4), ∃ n < M,
    (y : Circle) ∈ arc (ω n) (a n)) at h₂
  change (∀ y ∈ Icc (3 / 4 : ℝ) (3 / 4 + 1 / 4), ∃ n < M,
    (y : Circle) ∈ arc (ω n) (a n)) at h₃
  have finish {n : ℕ} (hn : n < M)
      (hhit : (r : Circle) ∈ arc (ω n) (a n)) :
      ∃ n ∈ Finset.Ico 0 M, (r : Circle) ∈ arc (ω n) (a n) :=
    ⟨n, Finset.mem_Ico.2 ⟨Nat.zero_le n, hn⟩, hhit⟩
  by_cases hquarter : r ≤ 1 / 4
  · obtain ⟨n, hn, hhit⟩ := h₀ r ⟨hr₀, by simpa using hquarter⟩
    exact finish hn hhit
  by_cases hhalf : r ≤ 1 / 2
  · obtain ⟨n, hn, hhit⟩ := h₁ r ⟨by linarith, by norm_num at hhalf ⊢; exact hhalf⟩
    exact finish hn hhit
  by_cases hthree : r ≤ 3 / 4
  · obtain ⟨n, hn, hhit⟩ := h₂ r ⟨by linarith, by norm_num at hthree ⊢; exact hthree⟩
    exact finish hn hhit
  · obtain ⟨n, hn, hhit⟩ := h₃ r ⟨by linarith, by norm_num; exact hr₁.le⟩
    exact finish hn hhit

def fourQuarterFailureEvent (a : ℕ → ℝ) (M : ℕ) : Set Sample :=
  (localFiniteCoverEventAt a M 0 (1 / 4))ᶜ ∪
  (localFiniteCoverEventAt a M (1 / 4) (1 / 4))ᶜ ∪
  (localFiniteCoverEventAt a M (1 / 2) (1 / 4))ᶜ ∪
  (localFiniteCoverEventAt a M (3 / 4) (1 / 4))ᶜ

lemma finiteCoverEvent_compl_subset_fourQuarterFailureEvent
    (a : ℕ → ℝ) (M : ℕ) :
    (finiteCoverEvent a 0 M)ᶜ ⊆ fourQuarterFailureEvent a M := by
  intro ω hω
  by_contra hnot
  apply hω
  apply finiteCovers_of_four_quarters
  all_goals
    simp only [fourQuarterFailureEvent, mem_union, mem_compl_iff,
      not_or, not_not] at hnot
  · exact hnot.1.1.1
  · exact hnot.1.1.2
  · exact hnot.1.2
  · exact hnot.2

lemma measureReal_fourQuarterFailureEvent_le
    (a : ℕ → ℝ) (M : ℕ) :
    sampleMeasure.real (fourQuarterFailureEvent a M) ≤
      4 * sampleMeasure.real ((localFiniteCoverEvent a M (1 / 4))ᶜ) := by
  let E₀ := (localFiniteCoverEventAt a M 0 (1 / 4))ᶜ
  let E₁ := (localFiniteCoverEventAt a M (1 / 4) (1 / 4))ᶜ
  let E₂ := (localFiniteCoverEventAt a M (1 / 2) (1 / 4))ᶜ
  let E₃ := (localFiniteCoverEventAt a M (3 / 4) (1 / 4))ᶜ
  have hU := measureReal_union_le (μ := sampleMeasure) (E₀ ∪ E₁ ∪ E₂) E₃
  have hU₁ := measureReal_union_le (μ := sampleMeasure) (E₀ ∪ E₁) E₂
  have hU₂ := measureReal_union_le (μ := sampleMeasure) E₀ E₁
  have h₀ := measureReal_localFiniteCoverEventAt_compl a M 0 (1 / 4)
  have h₁ := measureReal_localFiniteCoverEventAt_compl a M (1 / 4) (1 / 4)
  have h₂ := measureReal_localFiniteCoverEventAt_compl a M (1 / 2) (1 / 4)
  have h₃ := measureReal_localFiniteCoverEventAt_compl a M (3 / 4) (1 / 4)
  change sampleMeasure.real (E₀ ∪ E₁ ∪ E₂ ∪ E₃) ≤ _
  change sampleMeasure.real E₀ = _ at h₀
  change sampleMeasure.real E₁ = _ at h₁
  change sampleMeasure.real E₂ = _ at h₂
  change sampleMeasure.real E₃ = _ at h₃
  linarith

theorem tendsto_finiteCover_failure
    {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hsq : Summable (fun n ↦ (a n) ^ 2))
    (henergy : EnergyCondition a (1 / 4)) :
    Tendsto (fun M ↦ sampleMeasure.real
      ((finiteCoverEvent a 0 M)ᶜ)) atTop (nhds 0) := by
  have hlocal := tendsto_localFiniteCover_failure ha₀ ha (by norm_num)
    (by norm_num) hsq henergy
  have hupper : Tendsto (fun M ↦
      4 * sampleMeasure.real ((localFiniteCoverEvent a M (1 / 4))ᶜ))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlocal
  apply squeeze_zero'
  · filter_upwards [] with M
    exact measureReal_nonneg
  · filter_upwards [] with M
    exact (measureReal_mono
      (finiteCoverEvent_compl_subset_fourQuarterFailureEvent a M)).trans
        (measureReal_fourQuarterFailureEvent_le a M)
  · exact hupper

theorem measure_onceCoverageEvent_eq_one_of_energy
    {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (hsq : Summable (fun n ↦ (a n) ^ 2))
    (henergy : EnergyCondition a (1 / 4)) :
    sampleMeasure (onceCoverageEvent a) = 1 := by
  have hfailure := tendsto_finiteCover_failure ha₀ ha hsq henergy
  have hsubset (M : ℕ) :
      (onceCoverageEvent a)ᶜ ⊆ (finiteCoverEvent a 0 M)ᶜ := by
    intro ω hω hfinite
    apply hω
    rw [onceCoverageEvent_eq, coversFromEvent_eq_iUnion]
    exact mem_iUnion.2 ⟨M, hfinite⟩
  have hreal : sampleMeasure.real (onceCoverageEvent a)ᶜ = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto hfailure (Eventually.of_forall fun M ↦
        measureReal_mono (hsubset M))
    · exact measureReal_nonneg
  rw [measureReal_eq_zero_iff] at hreal
  have hadd := measure_add_measure_compl (μ := sampleMeasure)
    (measurableSet_onceCoverageEvent a)
  simpa only [hreal, add_zero, measure_univ] using hadd

/-- The sequence obtained by deleting its first `N` terms. -/
def sequenceTail (a : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n ↦ a (n + N)

lemma prefixLength_sequenceTail (a : ℕ → ℝ) (N m : ℕ) :
    prefixLength a (N + m) =
      prefixLength a N + prefixLength (sequenceTail a N) m := by
  unfold prefixLength sequenceTail
  rw [← Finset.sum_range_add_sum_Ico (fun k ↦ a k) (Nat.le_add_right N m),
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.add_comm]

lemma sheppTerm_add_le_mul_tail (a : ℕ → ℝ) (N n : ℕ) :
    sheppTerm a (n + N) ≤
      Real.exp (prefixLength a N) * sheppTerm (sequenceTail a N) n := by
  have hprefix : prefixLength a (n + N + 1) =
      prefixLength a N + prefixLength (sequenceTail a N) (n + 1) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      prefixLength_sequenceTail a N (n + 1)
  have hden : ((n + 1 : ℕ) : ℝ) ^ 2 ≤
      ((n + N + 1 : ℕ) : ℝ) ^ 2 := by
    have hcast : ((n + 1 : ℕ) : ℝ) ≤ (n + N + 1 : ℕ) := by
      exact_mod_cast (by omega : n + 1 ≤ n + N + 1)
    nlinarith [show (0 : ℝ) ≤ n + 1 by positivity]
  unfold sheppTerm
  rw [hprefix, Real.exp_add]
  have hdiv : Real.exp (prefixLength (sequenceTail a N) (n + 1)) /
      ((n + N + 1 : ℕ) : ℝ) ^ 2 ≤
      Real.exp (prefixLength (sequenceTail a N) (n + 1)) /
        ((n + 1 : ℕ) : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
  calc
    Real.exp (prefixLength a N) *
          Real.exp (prefixLength (sequenceTail a N) (n + 1)) /
          ((n + N + 1 : ℕ) : ℝ) ^ 2 =
        Real.exp (prefixLength a N) *
          (Real.exp (prefixLength (sequenceTail a N) (n + 1)) /
            ((n + N + 1 : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ Real.exp (prefixLength a N) *
          (Real.exp (prefixLength (sequenceTail a N) (n + 1)) /
            ((n + 1 : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le
    _ = _ := rfl

lemma sheppCondition_sequenceTail {a : ℕ → ℝ}
    (h : SheppCondition a) (N : ℕ) :
    SheppCondition (sequenceTail a N) := by
  intro htail
  apply h
  have hmajor : Summable (fun n ↦
      Real.exp (prefixLength a N) * sheppTerm (sequenceTail a N) n) :=
    htail.mul_left _
  have hshift : Summable (fun n ↦ sheppTerm a (n + N)) :=
    Summable.of_nonneg_of_le (fun n ↦ sheppTerm_nonneg a (n + N))
      (fun n ↦ sheppTerm_add_le_mul_tail a N n) hmajor
  exact (summable_nat_add_iff N).1 hshift

/-- Delete the first `N` sample coordinates. -/
def sampleTail (N : ℕ) (ω : Sample) : Sample :=
  fun n ↦ ω (n + N)

lemma measurable_sampleTail (N : ℕ) : Measurable (sampleTail N) := by
  unfold sampleTail
  fun_prop

lemma map_sampleTail_sampleMeasure (N : ℕ) :
    sampleMeasure.map (sampleTail N) = sampleMeasure := by
  change (Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)).map
      (fun ω : ℕ → Circle ↦ fun n ↦ ω (n + N)) =
    Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)
  simpa only using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ uniformCircle)
      (f := fun n : ℕ ↦ n + N) (fun _ _ h ↦ Nat.add_right_cancel h))

lemma sampleTail_preimage_onceCoverageEvent (a : ℕ → ℝ) (N : ℕ) :
    sampleTail N ⁻¹' onceCoverageEvent (sequenceTail a N) =
      coversFromEvent a N := by
  ext ω
  simp only [mem_preimage, onceCoverageEvent, coversFromEvent, mem_setOf_eq,
    CoversOnce, CoversFrom]
  constructor
  · intro h x
    obtain ⟨n, _hn, hhit⟩ := h x
    refine ⟨n + N, by omega, ?_⟩
    simpa only [sampleTail, sequenceTail]
  · intro h x
    obtain ⟨k, hk, hhit⟩ := h x
    refine ⟨k - N, Nat.zero_le _, ?_⟩
    simpa only [sampleTail, sequenceTail, Nat.sub_add_cancel hk] using hhit

lemma measure_coversFromEvent_eq_tail_once
    (a : ℕ → ℝ) (N : ℕ) :
    sampleMeasure (coversFromEvent a N) =
      sampleMeasure (onceCoverageEvent (sequenceTail a N)) := by
  have hmeas := measurableSet_onceCoverageEvent (sequenceTail a N)
  calc
    sampleMeasure (coversFromEvent a N) =
        sampleMeasure (sampleTail N ⁻¹'
          onceCoverageEvent (sequenceTail a N)) := by
      rw [sampleTail_preimage_onceCoverageEvent]
    _ = (sampleMeasure.map (sampleTail N))
          (onceCoverageEvent (sequenceTail a N)) := by
      rw [Measure.map_apply (measurable_sampleTail N) hmeas]
    _ = sampleMeasure (onceCoverageEvent (sequenceTail a N)) := by
      rw [map_sampleTail_sampleMeasure]

lemma antitone_sequenceTail {a : ℕ → ℝ} (hanti : Antitone a) (N : ℕ) :
    Antitone (sequenceTail a N) := by
  intro m n hmn
  exact hanti (Nat.add_le_add_right hmn N)

lemma tendsto_sequenceTail_zero {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0)) (N : ℕ) :
    Tendsto (sequenceTail a N) atTop (nhds 0) := by
  change Tendsto (fun n ↦ a (n + N)) atTop (nhds 0)
  exact (tendsto_add_atTop_iff_nat N).2 ha

lemma summable_sq_sequenceTail {a : ℕ → ℝ}
    (hsq : Summable (fun n ↦ (a n) ^ 2)) (N : ℕ) :
    Summable (fun n ↦ (sequenceTail a N n) ^ 2) := by
  simpa only [sequenceTail] using (summable_nat_add_iff N).2 hsq

lemma not_summable_sq_sequenceTail {a : ℕ → ℝ}
    (hsq : ¬ Summable (fun n ↦ (a n) ^ 2)) (N : ℕ) :
    ¬ Summable (fun n ↦ (sequenceTail a N n) ^ 2) := by
  intro htail
  apply hsq
  apply (summable_nat_add_iff N).1
  simpa only [sequenceTail] using htail

theorem measure_fullCoverageEvent_eq_one_of_summable_sq
    {a : ℕ → ℝ} (hanti : Antitone a)
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (halim : Tendsto a atTop (nhds 0))
    (hsq : Summable (fun n ↦ (a n) ^ 2))
    (hshepp : SheppCondition a) :
    sampleMeasure (fullCoverageEvent a) = 1 := by
  rw [measure_fullCoverageEvent_eq_one_iff]
  intro N
  rw [measure_coversFromEvent_eq_tail_once]
  apply measure_onceCoverageEvent_eq_one_of_energy
  · exact fun n ↦ ha₀ (n + N)
  · exact fun n ↦ ha (n + N)
  · exact summable_sq_sequenceTail hsq N
  · apply (energyCondition_iff_sheppCondition
      (antitone_sequenceTail hanti N)
      (fun n ↦ (ha₀ (n + N)).le)
      (fun n ↦ ha (n + N))
      (tendsto_sequenceTail_zero halim N)).2
    exact sheppCondition_sequenceTail hshepp N

theorem measure_fullCoverageEvent_eq_one_of_not_summable_sq
    {a : ℕ → ℝ} (hanti : Antitone a)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hsq : ¬ Summable (fun n ↦ (a n) ^ 2)) :
    sampleMeasure (fullCoverageEvent a) = 1 := by
  rw [measure_fullCoverageEvent_eq_one_iff]
  intro N
  rw [measure_coversFromEvent_eq_tail_once]
  exact measure_onceCoverageEvent_eq_one_of_not_summable_sq
    (antitone_sequenceTail hanti N) (fun n ↦ ha₀ (n + N))
    (fun n ↦ ha₁ (n + N)) (not_summable_sq_sequenceTail hsq N)

/-- Shepp's theorem in the short-length normalization used by the geometric
lemmas above.  Arbitrary lengths below one are reduced to this theorem by
deleting a finite prefix. -/
theorem shepp_criterion_short
    {a : ℕ → ℝ} (hanti : Antitone a)
    (ha₀ : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1 / 4)
    (halim : Tendsto a atTop (nhds 0)) :
    sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition a := by
  constructor
  · intro hcover
    apply (energyCondition_iff_sheppCondition hanti
      (fun n ↦ (ha₀ n).le) ha halim).1
    by_contra henergy
    have hne := measure_onceCoverageEvent_ne_one_of_not_energy
      (a := a) (ε := 1 / 4) (by norm_num) (by norm_num)
      (fun n ↦ (ha₀ n).le) ha
      (summable_sq_of_not_energy (by norm_num) (fun n ↦ (ha₀ n).le) ha henergy)
      henergy
    apply hne
    have hall := (measure_fullCoverageEvent_eq_one_iff a).1 hcover 0
    simpa only [onceCoverageEvent_eq] using hall
  · intro hshepp
    by_cases hsq : Summable (fun n ↦ (a n) ^ 2)
    · exact measure_fullCoverageEvent_eq_one_of_summable_sq hanti ha₀ ha
        halim hsq hshepp
    · exact measure_fullCoverageEvent_eq_one_of_not_summable_sq hanti
        (fun n ↦ (ha₀ n).le) (fun n ↦ (ha n).trans (by norm_num)) hsq

lemma sampleTail_preimage_fullCoverageEvent (a : ℕ → ℝ) (K : ℕ) :
    sampleTail K ⁻¹' fullCoverageEvent (sequenceTail a K) =
      fullCoverageEvent a := by
  ext ω
  simp only [mem_preimage, fullCoverageEvent, mem_setOf_eq,
    CoversInfinitelyOften, CoversFrom]
  constructor
  · intro h N x
    obtain ⟨n, hn, hhit⟩ := h N x
    refine ⟨n + K, by omega, ?_⟩
    simpa only [sampleTail, sequenceTail]
  · intro h N x
    obtain ⟨k, hk, hhit⟩ := h (N + K) x
    refine ⟨k - K, by omega, ?_⟩
    have hKk : K ≤ k := by omega
    simpa only [sampleTail, sequenceTail, Nat.sub_add_cancel hKk] using hhit

lemma measure_fullCoverageEvent_eq_tail_full
    (a : ℕ → ℝ) (K : ℕ) :
    sampleMeasure (fullCoverageEvent a) =
      sampleMeasure (fullCoverageEvent (sequenceTail a K)) := by
  have hmeas := measurableSet_fullCoverageEvent (sequenceTail a K)
  calc
    sampleMeasure (fullCoverageEvent a) =
        sampleMeasure (sampleTail K ⁻¹'
          fullCoverageEvent (sequenceTail a K)) := by
      rw [sampleTail_preimage_fullCoverageEvent]
    _ = (sampleMeasure.map (sampleTail K))
          (fullCoverageEvent (sequenceTail a K)) := by
      rw [Measure.map_apply (measurable_sampleTail K) hmeas]
    _ = sampleMeasure (fullCoverageEvent (sequenceTail a K)) := by
      rw [map_sampleTail_sampleMeasure]

lemma tail_sheppTerm_le_mul_add_sheppTerm (a : ℕ → ℝ) (K n : ℕ) :
    sheppTerm (sequenceTail a K) n ≤
      (Real.exp (-prefixLength a K) * ((K + 1 : ℕ) : ℝ) ^ 2) *
        sheppTerm a (n + K) := by
  have hprefix : prefixLength a (n + K + 1) =
      prefixLength a K + prefixLength (sequenceTail a K) (n + 1) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      prefixLength_sequenceTail a K (n + 1)
  have hexp : Real.exp (prefixLength (sequenceTail a K) (n + 1)) =
      Real.exp (-prefixLength a K) *
        Real.exp (prefixLength a (n + K + 1)) := by
    rw [hprefix, Real.exp_add, ← mul_assoc, ← Real.exp_add]
    simp
  have hnat : n + K + 1 ≤ (K + 1) * (n + 1) := by
    nlinarith [Nat.zero_le (K * n)]
  have hden : (((n + K + 1 : ℕ) : ℝ) ^ 2) ≤
      (((K + 1 : ℕ) : ℝ) ^ 2) * (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have hcast : ((n + K + 1 : ℕ) : ℝ) ≤
        ((K + 1) * (n + 1) : ℕ) := by exact_mod_cast hnat
    norm_num only [Nat.cast_mul] at hcast ⊢
    nlinarith [show (0 : ℝ) ≤ n + K + 1 by positivity,
      show (0 : ℝ) ≤ (K + 1) * (n + 1) by positivity]
  have hfrac : 1 / (((n + 1 : ℕ) : ℝ) ^ 2) ≤
      (((K + 1 : ℕ) : ℝ) ^ 2) /
        (((n + K + 1 : ℕ) : ℝ) ^ 2) := by
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hden)
  unfold sheppTerm
  rw [hexp]
  calc
    (Real.exp (-prefixLength a K) *
          Real.exp (prefixLength a (n + K + 1))) /
          (((n + 1 : ℕ) : ℝ) ^ 2) =
        (Real.exp (-prefixLength a K) *
          Real.exp (prefixLength a (n + K + 1))) *
          (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by ring
    _ ≤ (Real.exp (-prefixLength a K) *
          Real.exp (prefixLength a (n + K + 1))) *
          ((((K + 1 : ℕ) : ℝ) ^ 2) /
            (((n + K + 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (Real.exp (-prefixLength a K) * ((K + 1 : ℕ) : ℝ) ^ 2) *
          (Real.exp (prefixLength a (n + K + 1)) /
            (((n + K + 1 : ℕ) : ℝ) ^ 2)) := by ring

lemma sheppCondition_sequenceTail_iff (a : ℕ → ℝ) (K : ℕ) :
    SheppCondition (sequenceTail a K) ↔ SheppCondition a := by
  constructor
  · intro htail horiginal
    apply htail
    have hshift : Summable (fun n ↦ sheppTerm a (n + K)) :=
      (summable_nat_add_iff K).2 horiginal
    have hmajor : Summable (fun n ↦
        (Real.exp (-prefixLength a K) * ((K + 1 : ℕ) : ℝ) ^ 2) *
          sheppTerm a (n + K)) := hshift.mul_left _
    exact Summable.of_nonneg_of_le
      (fun n ↦ sheppTerm_nonneg (sequenceTail a K) n)
      (fun n ↦ tail_sheppTerm_le_mul_add_sheppTerm a K n) hmajor
  · exact fun h ↦ sheppCondition_sequenceTail h K

/-- Shepp's theorem in its classical form for a decreasing positive sequence
of lengths tending to zero. -/
theorem shepp_criterion_decreasing
    {a : ℕ → ℝ} (hanti : Antitone a)
    (ha₀ : ∀ n, 0 < a n)
    (halim : Tendsto a atTop (nhds 0)) :
    sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition a := by
  have hevent : ∀ᶠ n : ℕ in atTop, a n < 1 / 4 :=
    (tendsto_order.1 halim).2 (1 / 4) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  have htail : ∀ n, sequenceTail a K n ≤ 1 / 4 := by
    intro n
    exact (hK (n + K) (by omega)).le
  rw [measure_fullCoverageEvent_eq_tail_full a K,
    ← sheppCondition_sequenceTail_iff a K]
  exact shepp_criterion_short (antitone_sequenceTail hanti K)
    (fun n ↦ ha₀ (n + K)) htail (tendsto_sequenceTail_zero halim K)

lemma coversInfinitelyOften_iff_infinite_hits
    (a : ℕ → ℝ) (ω : Sample) :
    CoversInfinitelyOften a ω ↔
      ∀ x : Circle, {n : ℕ | x ∈ arc (ω n) (a n)}.Infinite := by
  constructor
  · intro h x hfinite
    obtain ⟨B, hB⟩ := hfinite.bddAbove
    obtain ⟨n, hn, hhit⟩ := h (B + 1) x
    have hnB : n ≤ B := hB hhit
    omega
  · intro h N x
    by_contra hnone
    push_neg at hnone
    have hsub : {n : ℕ | x ∈ arc (ω n) (a n)} ⊆ Set.Iio N := by
      intro n hn
      by_contra hnlt
      exact hnone n (Nat.le_of_not_gt hnlt) hn
    exact (h x) (Set.finite_Iio N |>.subset hsub)

/-- Keep precisely the sample coordinates corresponding to the positive
lengths, in the order specified by `e`. -/
def rearrangedSample {a : ℕ → ℝ}
    (e : ℕ ≃ {n : ℕ // 0 < a n}) (ω : Sample) : Sample :=
  fun k ↦ ω (e k : ℕ)

lemma measurable_rearrangedSample {a : ℕ → ℝ}
    (e : ℕ ≃ {n : ℕ // 0 < a n}) :
    Measurable (rearrangedSample e) := by
  unfold rearrangedSample
  fun_prop

lemma map_rearrangedSample_sampleMeasure {a : ℕ → ℝ}
    (e : ℕ ≃ {n : ℕ // 0 < a n}) :
    sampleMeasure.map (rearrangedSample e) = sampleMeasure := by
  have hinj : Function.Injective (fun k : ℕ ↦ (e k : ℕ)) := by
    intro k l hkl
    exact e.injective (Subtype.ext hkl)
  change (Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)).map
      (fun ω : ℕ → Circle ↦ fun k ↦ ω (e k : ℕ)) =
    Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)
  simpa only using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ uniformCircle)
      (f := fun k : ℕ ↦ (e k : ℕ)) hinj)

lemma image_rearranged_hitSet
    {a b : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (e : ℕ ≃ {n : ℕ // 0 < a n})
    (hb : ∀ k : ℕ, b k = a (e k : ℕ))
    (ω : Sample) (x : Circle) :
    (fun k : ℕ ↦ (e k : ℕ)) ''
        {k : ℕ | x ∈ arc (rearrangedSample e ω k) (b k)} =
      {n : ℕ | x ∈ arc (ω n) (a n)} := by
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    change x ∈ arc (ω (e k : ℕ)) (b k) at hk
    rw [hb] at hk
    exact hk
  · intro hn
    have hpos : 0 < a n := by
      change dist x (ω n) < a n / 2 at hn
      nlinarith [show 0 ≤ dist x (ω n) from dist_nonneg]
    let j : {m : ℕ // 0 < a m} := ⟨n, hpos⟩
    refine ⟨e.symm j, ?_, ?_⟩
    · change x ∈ arc (ω (e (e.symm j) : ℕ)) (b (e.symm j))
      rw [hb, e.apply_symm_apply]
      exact hn
    · exact congrArg Subtype.val (e.apply_symm_apply j)

lemma rearrangedSample_mem_fullCoverageEvent_iff
    {a b : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (e : ℕ ≃ {n : ℕ // 0 < a n})
    (hb : ∀ k : ℕ, b k = a (e k : ℕ)) (ω : Sample) :
    rearrangedSample e ω ∈ fullCoverageEvent b ↔
      ω ∈ fullCoverageEvent a := by
  rw [fullCoverageEvent, fullCoverageEvent, mem_setOf_eq, mem_setOf_eq,
    coversInfinitelyOften_iff_infinite_hits,
    coversInfinitelyOften_iff_infinite_hits]
  have hinj : Function.Injective (fun k : ℕ ↦ (e k : ℕ)) := by
    intro k l hkl
    exact e.injective (Subtype.ext hkl)
  constructor
  · intro h x
    rw [← image_rearranged_hitSet ha₀ e hb ω x]
    exact (h x).image hinj.injOn
  · intro h x
    have hx := h x
    rw [← image_rearranged_hitSet ha₀ e hb ω x] at hx
    exact Set.Infinite.of_image _ hx

lemma rearrangedSample_preimage_fullCoverageEvent
    {a b : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (e : ℕ ≃ {n : ℕ // 0 < a n})
    (hb : ∀ k : ℕ, b k = a (e k : ℕ)) :
    rearrangedSample e ⁻¹' fullCoverageEvent b = fullCoverageEvent a := by
  ext ω
  exact rearrangedSample_mem_fullCoverageEvent_iff ha₀ e hb ω

lemma measure_fullCoverageEvent_eq_rearrangement
    {a b : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (e : ℕ ≃ {n : ℕ // 0 < a n})
    (hb : ∀ k : ℕ, b k = a (e k : ℕ)) :
    sampleMeasure (fullCoverageEvent a) =
      sampleMeasure (fullCoverageEvent b) := by
  have hmeas := measurableSet_fullCoverageEvent b
  calc
    sampleMeasure (fullCoverageEvent a) =
        sampleMeasure (rearrangedSample e ⁻¹' fullCoverageEvent b) := by
      rw [rearrangedSample_preimage_fullCoverageEvent ha₀ e hb]
    _ = (sampleMeasure.map (rearrangedSample e))
          (fullCoverageEvent b) := by
      rw [Measure.map_apply (measurable_rearrangedSample e) hmeas]
    _ = sampleMeasure (fullCoverageEvent b) := by
      rw [map_rearrangedSample_sampleMeasure]

/-- Resolution of Erdős Problem 526.  For an arbitrary nonnegative sequence,
the order-dependent series is evaluated on its nonincreasing rearrangement of
positive terms. -/
theorem erdos_526
    {a b : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a)
    (hrearr : IsDecreasingRearrangement a b) :
    sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b := by
  obtain ⟨hanti, e, hb⟩ := hrearr
  have heinj : Function.Injective (fun k : ℕ ↦ (e k : ℕ)) := by
    intro k l hkl
    exact e.injective (Subtype.ext hkl)
  have heb : Tendsto (fun k : ℕ ↦ (e k : ℕ)) atTop atTop :=
    heinj.nat_tendsto_atTop
  have hblim : Tendsto b atTop (nhds 0) := by
    have hcomp := halim.comp heb
    convert hcomp using 1
    ext k
    exact hb k
  have hbpos : ∀ k, 0 < b k := by
    intro k
    rw [hb]
    exact (e k).property
  rw [measure_fullCoverageEvent_eq_rearrangement ha₀ e hb]
  exact shepp_criterion_decreasing hanti hbpos hblim

lemma finite_superlevel_of_tendsto_zero {a : ℕ → ℝ}
    (halim : Tendsto a atTop (nhds 0)) {c : ℝ} (hc : 0 < c) :
    {n : ℕ | c ≤ a n}.Finite := by
  have hevent : ∀ᶠ n : ℕ in atTop, a n < c :=
    (tendsto_order.1 halim).2 c hc
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  apply (Finset.range N).finite_toSet.subset
  intro n hn
  have hnN : n < N := by
    by_contra hnot
    exact (not_lt_of_ge hn) (hN n (Nat.le_of_not_gt hnot))
  simpa only [Finset.mem_coe, Finset.mem_range] using hnN

lemma infinite_positiveSupport_of_not_summable
    {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n) (hdiv : ¬ Summable a) :
    {n : ℕ | 0 < a n}.Infinite := by
  intro hfinite
  apply hdiv
  apply summable_of_hasFiniteSupport
  exact hfinite.subset (by
    intro n hn
    change a n ≠ 0 at hn
    change 0 < a n
    exact lt_of_le_of_ne (ha₀ n) (Ne.symm hn))

/-- A copy of the positive support with no inherited order.  It is equipped
locally with the lexicographic order by decreasing value and increasing
original index. -/
structure PositiveTermIndex (a : ℕ → ℝ) where
  val : ℕ
  property : 0 < a val

/-- Every nonnegative null sequence with divergent sum admits a decreasing
enumeration of its positive terms.  Ties are broken by the original index. -/
theorem exists_decreasingRearrangement
    {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0)) (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b := by
  let P := PositiveTermIndex a
  let key : P → (OrderDual ℝ ×ₗ ℕ) :=
    fun i ↦ toLex (OrderDual.toDual (a i.val), i.val)
  have hkey : Function.Injective key := by
    intro i j hij
    have hpair := congrArg ofLex hij
    cases i with
    | mk i hi =>
      cases j with
      | mk j hj =>
        congr
        exact congrArg Prod.snd hpair
  have hvalinj : Function.Injective (fun x : P ↦ x.val) := by
    intro x y hxy
    cases x
    cases y
    congr
  letI : LinearOrder P := LinearOrder.lift' key hkey
  have hvalue_of_le {i j : P} (hij : i ≤ j) : a j.val ≤ a i.val := by
    change key i ≤ key j at hij
    rw [Prod.Lex.toLex_le_toLex] at hij
    change a j.val < a i.val ∨
      (a i.val = a j.val ∧ i.val ≤ j.val) at hij
    rcases hij with hlt | heq
    · exact hlt.le
    · exact heq.1.ge
  letI : LocallyFiniteOrder P := LocallyFiniteOrder.ofFiniteIcc fun i j ↦ by
    have hfinite := finite_superlevel_of_tendsto_zero halim j.property
    have hpre : ((fun x : P ↦ x.val) ⁻¹'
        {n : ℕ | a j.val ≤ a n}).Finite :=
      hfinite.preimage hvalinj.injOn
    apply hpre.subset
    intro x hx
    exact hvalue_of_le hx.2
  have hIic_finite (z : P) : (Set.Iic z).Finite := by
    have hfinite := finite_superlevel_of_tendsto_zero halim z.property
    have hpre : ((fun x : P ↦ x.val) ⁻¹'
        {n : ℕ | a z.val ≤ a n}).Finite :=
      hfinite.preimage hvalinj.injOn
    apply hpre.subset
    intro x hx
    exact hvalue_of_le hx
  have hpositive : {n : ℕ | 0 < a n}.Infinite :=
    infinite_positiveSupport_of_not_summable ha₀ hdiv
  letI : Infinite {n : ℕ // 0 < a n} := Set.infinite_coe_iff.mpr hpositive
  let pEquiv : P ≃ {n : ℕ // 0 < a n} := {
    toFun i := ⟨i.val, i.property⟩
    invFun i := ⟨i.val, i.property⟩
    left_inv i := by cases i; rfl
    right_inv i := by cases i; rfl }
  letI : Infinite P := Infinite.of_injective pEquiv.symm pEquiv.symm.injective
  let q : P := Classical.choice (inferInstance : Nonempty P)
  have hIic : (Set.Iic q).Finite := hIic_finite q
  let s : Finset P := hIic.toFinset
  have hs : s.Nonempty := by
    refine ⟨q, ?_⟩
    simp only [s, Set.Finite.mem_toFinset, Set.mem_Iic, le_refl]
  let botP : P := s.min' hs
  letI : OrderBot P := {
    bot := botP
    bot_le x := by
      change botP ≤ x
      by_cases hx : x ≤ q
      · exact s.min'_le x (by
          simpa only [s, Set.Finite.mem_toFinset, Set.mem_Iic] using hx)
      · exact (s.min'_le q (by
          simp only [s, Set.Finite.mem_toFinset, Set.mem_Iic, le_refl])).trans
          (le_of_not_ge hx) }
  letI : NoMaxOrder P := ⟨fun x ↦ by
    by_contra hmax
    push_neg at hmax
    have hall : ∀ y : P, y ≤ x := hmax
    have hicc : (Set.Iic x).Finite := hIic_finite x
    have huniv : Set.Iic x = (Set.univ : Set P) :=
      Set.eq_univ_of_forall fun y ↦ hall y
    rw [huniv] at hicc
    exact Set.infinite_univ hicc⟩
  letI : SuccOrder P := LinearLocallyFiniteOrder.succOrder P
  letI : PredOrder P := LinearLocallyFiniteOrder.predOrder P
  let o : P ≃o ℕ := orderIsoNatOfLinearSuccPredArch
  let e : ℕ ≃ {n : ℕ // 0 < a n} := o.symm.toEquiv.trans pEquiv
  let b : ℕ → ℝ := fun k ↦ a (o.symm k).val
  refine ⟨b, ?_, e, fun k ↦ rfl⟩
  intro m n hmn
  exact hvalue_of_le (o.symm.monotone hmn)

/-- Assumption-free arbitrary-order form: the decreasing rearrangement exists
under the hypotheses, and every such rearrangement gives Shepp's criterion. -/
theorem erdos_526_exists_rearrangement
    {a : ℕ → ℝ} (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0)) (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b ∧
      (sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b) := by
  obtain ⟨b, hb⟩ := exists_decreasingRearrangement ha₀ halim hdiv
  exact ⟨b, hb, erdos_526 ha₀ halim hdiv hb⟩

end
end Erdos526
