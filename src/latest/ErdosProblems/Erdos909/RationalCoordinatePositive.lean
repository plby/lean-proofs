import ErdosProblems.Erdos909.RationalCoordinateUpper
import ErdosProblems.Erdos909.CuttingUpper
import Mathlib.Topology.Algebra.Module.Cardinality

open Set Topology TopologicalSpace
open scoped BigOperators

namespace Erdos909.RationalCoordinatePositive

open RationalCoordinateUpper CuttingUpper

noncomputable section

lemma exists_rat_btwn_not_mem_finset (A : Finset ℚ) {x y : ℝ} (hxy : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y ∧ q ∉ A := by
  let F : Set ℝ := ((fun q : ℚ ↦ (q : ℝ)) '' (A : Set ℚ))
  have hFc : F.Countable := A.countable_toSet.image _
  have hFo : IsOpen Fᶜ := A.finite_toSet.image _ |>.isClosed.isOpen_compl
  have hd : Dense (Set.range ((↑) : ℚ → ℝ) ∩ Fᶜ) :=
    Rat.denseRange_cast.inter_of_isOpen_right (hFc.dense_compl ℝ) hFo
  obtain ⟨z, hz, hzx, hzy⟩ :=
    hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hxy)
  rcases hz.1 with ⟨q, rfl⟩
  refine ⟨q, hzx, hzy, ?_⟩
  intro hq
  exact hz.2 ⟨q, hq, rfl⟩

def rationalIntervalBasisAvoiding (A : Finset ℚ) : Set (Set ℝ) :=
  ⋃ (a : ℚ) (b : ℚ) (_ : a < b) (_ : a ∉ A) (_ : b ∉ A),
    {Set.Ioo (a : ℝ) (b : ℝ)}

lemma mem_rationalIntervalBasisAvoiding_iff {A : Finset ℚ} {U : Set ℝ} :
    U ∈ rationalIntervalBasisAvoiding A ↔
      ∃ a b : ℚ, a < b ∧ a ∉ A ∧ b ∉ A ∧ U = Set.Ioo (a : ℝ) (b : ℝ) := by
  simp only [rationalIntervalBasisAvoiding, Set.mem_iUnion, Set.mem_singleton_iff]
  aesop

lemma isTopologicalBasis_rationalIntervalBasisAvoiding (A : Finset ℚ) :
    IsTopologicalBasis (rationalIntervalBasisAvoiding A) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    obtain ⟨a, b, hab, ha, hb, rfl⟩ := mem_rationalIntervalBasisAvoiding_iff.mp hU
    exact isOpen_Ioo
  · intro x U hxU
    intro hU
    obtain ⟨V, hV, hxV, hVU⟩ :=
      isTopologicalBasis_rationalIntervalBasis.isOpen_iff.mp hU x hxU
    obtain ⟨a, b, hab, rfl⟩ := mem_rationalIntervalBasis_iff.mp hV
    obtain ⟨a', haa', ha'x, ha'A⟩ :=
      exists_rat_btwn_not_mem_finset A hxV.1
    obtain ⟨b', hxb', hb'b, hb'A⟩ :=
      exists_rat_btwn_not_mem_finset A hxV.2
    refine ⟨Set.Ioo (a' : ℝ) (b' : ℝ), ?_, ⟨ha'x, hxb'⟩, ?_⟩
    · apply mem_rationalIntervalBasisAvoiding_iff.mpr
      exact ⟨a', b', Rat.cast_lt.mp (ha'x.trans hxb'), ha'A, hb'A, rfl⟩
    · exact fun z hz ↦ hVU ⟨haa'.trans hz.1, hz.2.trans hb'b⟩

variable {I : Type*} [Finite I]

structure AvoidingBox (used : I → Finset ℚ) where
  active : Finset I
  lower : I → ℚ
  upperEndpoint : I → ℚ
  lower_lt_upper : ∀ i ∈ active, lower i < upperEndpoint i
  lower_fresh : ∀ i ∈ active, lower i ∉ used i
  upper_fresh : ∀ i ∈ active, upperEndpoint i ∉ used i

def AvoidingBox.carrier {used : I → Finset ℚ} (B : AvoidingBox used) :
    Set (I → ℝ) :=
  (B.active : Set I).pi
    (fun i ↦ Set.Ioo (B.lower i : ℝ) (B.upperEndpoint i : ℝ))

def rationalBoxBasisAvoiding (used : I → Finset ℚ) : Set (Set (I → ℝ)) :=
  Set.range (fun B : AvoidingBox used ↦ B.carrier)

lemma isTopologicalBasis_rationalBoxBasisAvoiding (used : I → Finset ℚ) :
    IsTopologicalBasis (rationalBoxBasisAvoiding used) := by
  classical
  let p : Set (Set (I → ℝ)) :=
    {S | ∃ (U : I → Set ℝ) (F : Finset I),
      (∀ i, i ∈ F → U i ∈ rationalIntervalBasisAvoiding (used i)) ∧
        S = (F : Set I).pi U}
  have hp : IsTopologicalBasis p :=
    isTopologicalBasis_pi fun i ↦ isTopologicalBasis_rationalIntervalBasisAvoiding (used i)
  have heq : rationalBoxBasisAvoiding used = p := by
    ext S
    constructor
    · rintro ⟨B, rfl⟩
      refine ⟨_, B.active, ?_, rfl⟩
      intro i hi
      apply mem_rationalIntervalBasisAvoiding_iff.mpr
      exact ⟨B.lower i, B.upperEndpoint i, B.lower_lt_upper i hi,
        B.lower_fresh i hi, B.upper_fresh i hi, rfl⟩
    · rintro ⟨U, F, hUF, rfl⟩
      choose a b hab ha hb hU using fun i : F ↦
        mem_rationalIntervalBasisAvoiding_iff.mp (hUF i i.2)
      let lower : I → ℚ := fun i ↦ if hi : i ∈ F then a ⟨i, hi⟩ else 0
      let upperEndpoint : I → ℚ := fun i ↦ if hi : i ∈ F then b ⟨i, hi⟩ else 1
      let B : AvoidingBox used :=
        { active := F
          lower := lower
          upperEndpoint := upperEndpoint
          lower_lt_upper := by
            intro i hi
            simpa [lower, upperEndpoint, hi] using hab ⟨i, hi⟩
          lower_fresh := by intro i hi; simpa [lower, hi] using ha ⟨i, hi⟩
          upper_fresh := by
            intro i hi
            simpa [upperEndpoint, hi] using hb ⟨i, hi⟩ }
      refine ⟨B, ?_⟩
      simp only [AvoidingBox.carrier, B]
      apply Set.pi_congr rfl
      intro i hi
      change i ∈ F at hi
      rw [show lower i = a ⟨i, hi⟩ by simp [lower, hi],
        show upperEndpoint i = b ⟨i, hi⟩ by simp [upperEndpoint, hi]]
      exact (hU ⟨i, hi⟩).symm
  rw [heq]
  exact hp

def AvoidingBox.updatedUsed {used : I → Finset ℚ} (B : AvoidingBox used) :
    I → Finset ℚ := by
  classical
  exact fun i ↦
    if i ∈ B.active then insert (B.lower i) (insert (B.upperEndpoint i) (used i))
    else used i

lemma frontier_biInter_finset_subset {X : Type*} [TopologicalSpace X]
    (F : Finset I) (s : I → Set X) :
    frontier (⋂ i ∈ F, s i) ⊆ ⋃ i ∈ F, frontier (s i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
      have hweak :
          frontier (s a) ∩ closure (⋂ i ∈ F, s i) ∪
              closure (s a) ∩ frontier (⋂ i ∈ F, s i) ⊆
            frontier (s a) ∪ frontier (⋂ i ∈ F, s i) :=
        union_subset_union inter_subset_left inter_subset_right
      have h := (frontier_inter_subset (s a) (⋂ i ∈ F, s i)).trans hweak |>.trans
        (union_subset_union Set.Subset.rfl ih)
      simpa [ha] using h

lemma AvoidingBox.frontier_carrier_subset_endpoints
    {used : I → Finset ℚ} (B : AvoidingBox used) :
    frontier B.carrier ⊆
      {x | ∃ i ∈ B.active,
        x i = (B.lower i : ℝ) ∨ x i = (B.upperEndpoint i : ℝ)} := by
  classical
  intro x hx
  have hopen : IsOpen B.carrier :=
    (isTopologicalBasis_rationalBoxBasisAvoiding _).isOpen ⟨B, rfl⟩
  rw [hopen.frontier_eq, AvoidingBox.carrier, closure_pi_set] at hx
  by_contra h
  have hnone : ∀ i ∈ B.active,
      x i ≠ (B.lower i : ℝ) ∧ x i ≠ (B.upperEndpoint i : ℝ) := by
    intro i hi
    constructor
    · intro heq
      exact h ⟨i, hi, Or.inl heq⟩
    · intro heq
      exact h ⟨i, hi, Or.inr heq⟩
  apply hx.2
  intro i hi
  change i ∈ B.active at hi
  have hclosed := hx.1 i hi
  change x i ∈ closure (Ioo (B.lower i : ℝ) (B.upperEndpoint i : ℝ)) at hclosed
  change x i ∈ Ioo (B.lower i : ℝ) (B.upperEndpoint i : ℝ)
  have hne : (B.lower i : ℝ) ≠ (B.upperEndpoint i : ℝ) := by
    exact_mod_cast (B.lower_lt_upper i hi).ne
  rw [closure_Ioo hne] at hclosed
  exact ⟨lt_of_le_of_ne hclosed.1 (hnone i hi).1.symm,
    lt_of_le_of_ne hclosed.2 (hnone i hi).2⟩

def HasUsedWitness {X : Type*} (f : X → I → ℝ)
    (used : I → Finset ℚ) (r : ℕ) : Prop :=
  ∀ x, ∃ J : Finset I, J.card = r ∧
    ∀ i ∈ J, ∃ q ∈ used i, f x i = (q : ℝ)

lemma HasUsedWitness.zero {X : Type*} (f : X → I → ℝ)
    (used : I → Finset ℚ) : HasUsedWitness f used 0 := by
  intro x
  exact ⟨∅, rfl, by simp⟩

lemma AvoidingBox.mem_updatedUsed_of_mem {used : I → Finset ℚ}
    (B : AvoidingBox used) {i : I} {q : ℚ} (hq : q ∈ used i) :
    q ∈ B.updatedUsed i := by
  classical
  by_cases hi : i ∈ B.active <;> simp [AvoidingBox.updatedUsed, hi, hq]

lemma AvoidingBox.lower_mem_updatedUsed {used : I → Finset ℚ}
    (B : AvoidingBox used) {i : I} (hi : i ∈ B.active) :
    B.lower i ∈ B.updatedUsed i := by
  classical
  simp [AvoidingBox.updatedUsed, hi]

lemma AvoidingBox.upper_mem_updatedUsed {used : I → Finset ℚ}
    (B : AvoidingBox used) {i : I} (hi : i ∈ B.active) :
    B.upperEndpoint i ∈ B.updatedUsed i := by
  classical
  simp [AvoidingBox.updatedUsed, hi]

lemma HasUsedWitness.frontier_preimage
    {X : Type*} [TopologicalSpace X] {f : X → I → ℝ}
    (hf : IsInducing f) {used : I → Finset ℚ} {r : ℕ}
    (hused : HasUsedWitness f used r) (B : AvoidingBox used) :
    HasUsedWitness
      (fun y : frontier (f ⁻¹' B.carrier) ↦ f y.1)
      B.updatedUsed (r + 1) := by
  classical
  intro y
  have hyAmbient : f y.1 ∈ frontier B.carrier :=
    hf.continuous.frontier_preimage_subset B.carrier y.2
  obtain ⟨i, hiActive, hiEndpoint⟩ := B.frontier_carrier_subset_endpoints hyAmbient
  obtain ⟨J, hJcard, hJ⟩ := hused y.1
  have hiJ : i ∉ J := by
    intro hi
    obtain ⟨q, hqUsed, hqEq⟩ := hJ i hi
    rcases hiEndpoint with hiLower | hiUpper
    · have hq : q = B.lower i := by
        exact_mod_cast hqEq.symm.trans hiLower
      exact B.lower_fresh i hiActive (hq ▸ hqUsed)
    · have hq : q = B.upperEndpoint i := by
        exact_mod_cast hqEq.symm.trans hiUpper
      exact B.upper_fresh i hiActive (hq ▸ hqUsed)
  refine ⟨insert i J, by simp [hiJ, hJcard], ?_⟩
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · rcases hiEndpoint with hiLower | hiUpper
    · exact ⟨B.lower j, B.lower_mem_updatedUsed hiActive, hiLower⟩
    · exact ⟨B.upperEndpoint j, B.upper_mem_updatedUsed hiActive, hiUpper⟩
  · obtain ⟨q, hqUsed, hqEq⟩ := hJ j hj
    exact ⟨q, B.mem_updatedUsed_of_mem hqUsed, hqEq⟩

lemma HasUsedWitness.mem_rationalCoordinatesAtLeast
    {X : Type*} {f : X → I → ℝ} {used : I → Finset ℚ} {r : ℕ}
    (hused : HasUsedWitness f used r) (x : X) :
    f x ∈ rationalCoordinatesAtLeast r := by
  obtain ⟨J, hJcard, hJ⟩ := hused x
  refine ⟨J, hJcard, ?_⟩
  intro i hi
  obtain ⟨q, hq, heq⟩ := hJ i hi
  exact ⟨q, heq.symm⟩

def inducedAvoidingBoxBasis {X : Type*} (f : X → I → ℝ)
    (used : I → Finset ℚ) : Set (Set X) :=
  Set.range (fun B : AvoidingBox used ↦ f ⁻¹' B.carrier)

lemma isTopologicalBasis_inducedAvoidingBoxBasis
    {X : Type*} [TopologicalSpace X] {f : X → I → ℝ}
    (hf : IsInducing f) (used : I → Finset ℚ) :
    IsTopologicalBasis (inducedAvoidingBoxBasis f used) := by
  have h := (isTopologicalBasis_rationalBoxBasisAvoiding used).isInducing hf
  have heq : (fun U : Set (I → ℝ) ↦ f ⁻¹' U) ''
        Set.range (fun B : AvoidingBox used ↦ B.carrier) =
      Set.range (fun B : AvoidingBox used ↦ f ⁻¹' B.carrier) := by
    ext U
    constructor
    · rintro ⟨V, ⟨B, rfl⟩, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨B.carrier, ⟨B, rfl⟩, rfl⟩
  rw [inducedAvoidingBoxBasis, ← heq]
  exact h

noncomputable def boxOfBasisMem
    {X : Type*} {f : X → I → ℝ} {used : I → Finset ℚ}
    {U : Set X} (hU : U ∈ inducedAvoidingBoxBasis f used) : AvoidingBox used :=
  Classical.choose hU

lemma boxOfBasisMem_spec
    {X : Type*} {f : X → I → ℝ} {used : I → Finset ℚ}
    {U : Set X} (hU : U ∈ inducedAvoidingBoxBasis f used) :
    f ⁻¹' (boxOfBasisMem hU).carrier = U :=
  Classical.choose_spec hU

/-- Iterating rational boxes with endpoints fresh at each node proves
directly that the rational-coordinate bad set is an obstruction.  This
avoids any appeal to the finite or countable closed-sum theorem for `ind`. -/
theorem rationalCoordinatesAtLeast_isObstruction
    {X : Type*} [TopologicalSpace X] (k r : ℕ)
    {f : X → I → ℝ} (hf : IsInducing f)
    (used : I → Finset ℚ) (hused : HasUsedWitness f used r) :
    IsSmallInductiveDimensionObstruction
      (f ⁻¹' rationalCoordinatesAtLeast (r + k)) k := by
  induction k generalizing X r used with
  | zero =>
      apply isSmallInductiveDimensionObstruction_univ.mono
      intro x hx
      exact hused.mem_rationalCoordinatesAtLeast x
  | succ k ih =>
      let b := inducedAvoidingBoxBasis f used
      let R : ∀ (U : Set X), U ∈ b → Set (frontier U) := fun U hU ↦
        let B := boxOfBasisMem hU
        (fun y : frontier U ↦ f y.1) ⁻¹'
          rationalCoordinatesAtLeast ((r + 1) + k)
      have hR : ∀ (U : Set X) (hU : U ∈ b),
          IsSmallInductiveDimensionObstruction (R U hU) k := by
        intro U hU
        let B := boxOfBasisMem hU
        have hUeq : f ⁻¹' B.carrier = U := boxOfBasisMem_spec hU
        have hfind : IsInducing (fun y : frontier U ↦ f y.1) :=
          hf.comp IsInducing.subtypeVal
        have hwitness : HasUsedWitness
            (fun y : frontier U ↦ f y.1) B.updatedUsed (r + 1) := by
          rw [← hUeq]
          exact hused.frontier_preimage hf B
        exact ih (r + 1) hfind B.updatedUsed hwitness
      have hsmall := isSmallInductiveDimensionObstruction_iUnion_frontier
        k b (isTopologicalBasis_inducedAvoidingBoxBasis hf used) R hR
      apply hsmall.mono
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨U, hU, y, hy, rfl⟩ := hx
      change f y.1 ∈ rationalCoordinatesAtLeast (r + (k + 1))
      change f y.1 ∈ rationalCoordinatesAtLeast ((r + 1) + k) at hy
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hy

/-- The rational-coordinate Nöbeling set of order `k` has small inductive
dimension at most `k`. -/
theorem rationalCoordinateNobeling_hasSmallInductiveDimensionLT (k : ℕ) :
    HasSmallInductiveDimensionLT
      (rationalCoordinateNobeling (ι := I) k) (k + 1) := by
  let used : I → Finset ℚ := fun _ ↦ ∅
  have hobs := rationalCoordinatesAtLeast_isObstruction (I := I)
    (X := I → ℝ) (k + 1) 0 (f := id) IsInducing.id used
      (HasUsedWitness.zero id used)
  apply hobs (rationalCoordinateNobeling k)
  rw [Set.disjoint_left]
  intro x hxN hxBad
  have hxBad' : x ∈ rationalCoordinatesAtLeast (k + 1) := by
    simpa only [Set.mem_preimage, id_eq, zero_add] using hxBad
  exact hxN hxBad'

end

end Erdos909.RationalCoordinatePositive
