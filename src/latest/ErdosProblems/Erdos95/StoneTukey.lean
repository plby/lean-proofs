/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.FineTucker
import ErdosProblems.Erdos95.Partitioning

/-!
# Finite Stone--Tukey bisection

This file derives the finite central-hyperplane ham-sandwich theorem used by
the polynomial-partitioning construction.  The proof labels a sufficiently
fine antipodal triangulation by a strict-majority open cover and invokes the
fine Tucker lemma.
-/

open scoped BigOperators Topology

namespace Erdos95.StoneTukey

open Set Metric
open ProofsInTheBook.Chapter39
open Erdos95.Barycentric
open Erdos95.FineTucker
open Erdos95.Partitioning

theorem norm_faceAverage_le_one
    {K : FiniteComplex} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : K.Vertex → E) (F : BaryVertex K)
    (hf : ∀ v ∈ F.1, ‖f v‖ ≤ 1) :
    ‖faceAverage f F‖ ≤ 1 := by
  have hcardpos : 0 < F.1.card := Finset.card_pos.mpr (K.face_nonempty F.2)
  have hcardne : (F.1.card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcardpos)
  calc
    ‖faceAverage f F‖
        = ‖(F.1.card : ℝ)⁻¹‖ * ‖∑ v ∈ F.1, f v‖ := by
          simp only [faceAverage, norm_smul]
    _ ≤ ‖(F.1.card : ℝ)⁻¹‖ * ∑ v ∈ F.1, ‖f v‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ‖(F.1.card : ℝ)⁻¹‖ * ∑ _v ∈ F.1, (1 : ℝ) := by
          gcongr with v hv
          exact hf v hv
    _ = 1 := by
          simp [hcardne]

theorem norm_realize_le_one (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    ‖realize d r v‖ ≤ 1 := by
  induction r with
  | zero => exact norm_signedBasisVector_le_one v
  | succ r ih =>
      exact norm_faceAverage_le_one (realize d r) v
        (fun w _hw ↦ ih w)

/-- A separating sign vector for a realized face.  Unlike an arbitrary
linear separator, its coordinates all have absolute value one; this gives a
subdivision-independent lower bound on the norm of every realized vertex. -/
theorem exists_sign_separator_realize (d r : ℕ)
    {s : Finset (iteratedBoundary d r).Vertex}
    (hs : (iteratedBoundary d r).IsFace s) :
    ∃ σ : Fin d → ℝ,
      (∀ i, |σ i| = 1) ∧
        ∀ v ∈ s, (∑ i, σ i * realize d r v i) = 1 := by
  classical
  induction r with
  | zero =>
      let σ : Fin d → ℝ := fun i ↦ if (i, true) ∈ s then 1 else -1
      refine ⟨σ, ?_, ?_⟩
      · intro i
        by_cases hi : (i, true) ∈ s <;> simp [σ, hi]
      · rintro ⟨i, b⟩ hv
        have hnotOpp : (i, !b) ∉ s := by
          intro hopp
          cases b
          · exact hs.2 i ⟨hv, hopp⟩
          · exact hs.2 i ⟨hopp, hv⟩
        cases b
        · have htrue : (i, true) ∉ s := by simpa using hnotOpp
          rw [Finset.sum_eq_single i]
          · have hσi : σ i = -1 := if_neg htrue
            rw [hσi]
            simp [realize, signedBasisVector]
          · intro j _hj hji
            simp [realize, signedBasisVector, hji]
          · simp
        · rw [Finset.sum_eq_single i]
          · have hσi : σ i = 1 := if_pos hv
            rw [hσi]
            simp [realize, signedBasisVector]
          · intro j _hj hji
            simp [realize, signedBasisVector, hji]
          · simp
  | succ r ih =>
      obtain ⟨M, hMs, hlargest⟩ := exists_chain_largest hs
      obtain ⟨σ, hσ, hsep⟩ := ih M.2
      refine ⟨σ, hσ, ?_⟩
      intro F hFs
      have hFM : F.1 ⊆ M.1 := hlargest F hFs
      have hcardpos : 0 < F.1.card :=
        Finset.card_pos.mpr ((iteratedBoundary d r).face_nonempty F.2)
      have hcardne : (F.1.card : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hcardpos)
      let L : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun y ↦ ∑ i, σ i * y i
          map_add' := by
            intro x y
            simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          map_smul' := by
            intro a y
            simp only [Pi.smul_apply, smul_eq_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [RingHom.id_apply]
            ring }
      change L (faceAverage (realize d r) F) = 1
      unfold faceAverage
      rw [LinearMapClass.map_smul, map_sum]
      have hsum : (∑ x ∈ F.1, L (realize d r x)) =
          ∑ _x ∈ F.1, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hsep x (hFM hx)
      rw [hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
        smul_eq_mul]
      simpa [smul_eq_mul] using inv_mul_cancel₀ hcardne

theorem one_le_card_mul_norm_realize (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    1 ≤ (d : ℝ) * ‖realize d r v‖ := by
  classical
  obtain ⟨σ, hσ, hsep⟩ := exists_sign_separator_realize d r
    ((iteratedBoundary d r).singleton_face v)
  have hvsep := hsep v (by simp)
  calc
    (1 : ℝ) = |∑ i, σ i * realize d r v i| := by rw [hvsep]; norm_num
    _ ≤ ∑ i, |σ i * realize d r v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _i : Fin d, |realize d r v _i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, hσ i, one_mul]
    _ ≤ (d : ℝ) * ‖realize d r v‖ := by
      simpa [nsmul_eq_mul] using
        (Pi.sum_norm_apply_le_norm (realize d r v))

/-! ## The strict-majority open cover -/

/-- Evaluation of a coefficient vector against a finite-dimensional feature
vector. -/
noncomputable def linearValueFin {X : Type*} {d : ℕ}
    (a : X → Fin d → ℝ) (c : Fin d → ℝ) (x : X) : ℝ :=
  ∑ j, c j * a x j

theorem linearValueFin_neg {X : Type*} {d : ℕ}
    (a : X → Fin d → ℝ) (c : Fin d → ℝ) (x : X) :
    linearValueFin a (-c) x = -linearValueFin a c x := by
  simp only [linearValueFin, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib]

theorem continuous_linearValueFin {X : Type*} {d : ℕ}
    (a : X → Fin d → ℝ) (x : X) :
    Continuous (fun c : Fin d → ℝ ↦ linearValueFin a c x) := by
  unfold linearValueFin
  fun_prop

/-- Coefficients for which family `i` has a strict positive majority. -/
def positiveMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    Set (Fin d → ℝ) :=
  {c | (S i).card < 2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card}

/-- Coefficients for which family `i` has a strict negative majority. -/
def negativeMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    Set (Fin d → ℝ) :=
  {c | (S i).card < 2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card}

theorem isOpen_positiveMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    IsOpen (positiveMajoritySet S a i) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro c hc
  let T := (S i).filter fun x ↦ 0 < linearValueFin a c x
  have hTcard : (S i).card < 2 * T.card := hc
  have hstable : ∀ᶠ z in 𝓝 c,
      ∀ x ∈ T, 0 < linearValueFin a z x := by
    apply T.eventually_all.mpr
    intro x hx
    have hxpos : 0 < linearValueFin a c x := (Finset.mem_filter.mp hx).2
    exact (isOpen_lt continuous_const (continuous_linearValueFin a x)).mem_nhds hxpos
  filter_upwards [hstable] with z hz
  have hsub : T ⊆ (S i).filter (fun x ↦ 0 < linearValueFin a z x) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hz x hx⟩
  exact lt_of_lt_of_le hTcard
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub))

theorem isOpen_negativeMajoritySet {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) (i : Fin m) :
    IsOpen (negativeMajoritySet S a i) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro c hc
  let T := (S i).filter fun x ↦ linearValueFin a c x < 0
  have hTcard : (S i).card < 2 * T.card := hc
  have hstable : ∀ᶠ z in 𝓝 c,
      ∀ x ∈ T, linearValueFin a z x < 0 := by
    apply T.eventually_all.mpr
    intro x hx
    have hxneg : linearValueFin a c x < 0 := (Finset.mem_filter.mp hx).2
    exact (isOpen_lt (continuous_linearValueFin a x) continuous_const).mem_nhds hxneg
  filter_upwards [hstable] with z hz
  have hsub : T ⊆ (S i).filter (fun x ↦ linearValueFin a z x < 0) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hz x hx⟩
  exact lt_of_lt_of_le hTcard
    (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub))

/-- The signed cover pairs positive and negative strict-majority sets. -/
def majorityCover {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) : Set (Fin d → ℝ) :=
  if L.positive then positiveMajoritySet S a L.index
  else negativeMajoritySet S a L.index

theorem isOpen_majorityCover {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) :
    IsOpen (majorityCover S a L) := by
  cases h : L.positive <;>
    simp [majorityCover, h, isOpen_positiveMajoritySet,
      isOpen_negativeMajoritySet]

theorem positiveMajoritySet_neg_iff_negative {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (i : Fin m) (c : Fin d → ℝ) :
    -c ∈ positiveMajoritySet S a i ↔ c ∈ negativeMajoritySet S a i := by
  classical
  simp [positiveMajoritySet, negativeMajoritySet, linearValueFin_neg]

theorem negativeMajoritySet_neg_iff_positive {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (i : Fin m) (c : Fin d → ℝ) :
    -c ∈ negativeMajoritySet S a i ↔ c ∈ positiveMajoritySet S a i := by
  classical
  simp [positiveMajoritySet, negativeMajoritySet, linearValueFin_neg]

theorem mem_majorityCover_neg_iff {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) (c : Fin d → ℝ) :
    -c ∈ majorityCover S a L.neg ↔ c ∈ majorityCover S a L := by
  cases h : L.positive <;>
    simp [majorityCover, SignedLabel.neg, h,
      positiveMajoritySet_neg_iff_negative,
      negativeMajoritySet_neg_iff_positive]

/-- A compact annulus containing every realized subdivision vertex. -/
def coefficientAnnulus (d : ℕ) : Set (Fin d → ℝ) :=
  Metric.closedBall 0 1 ∩ {c | 1 ≤ (d : ℝ) * ‖c‖}

theorem isCompact_coefficientAnnulus (d : ℕ) :
    IsCompact (coefficientAnnulus d) := by
  apply (isCompact_closedBall (0 : Fin d → ℝ) 1).inter_right
  exact isClosed_le continuous_const (continuous_const.mul continuous_norm)

theorem realize_mem_coefficientAnnulus (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    realize d r v ∈ coefficientAnnulus d := by
  constructor
  · simpa [Metric.mem_closedBall, dist_zero_right] using norm_realize_le_one d r v
  · exact one_le_card_mul_norm_realize d r v

theorem mem_coefficientAnnulus_ne_zero {d : ℕ}
    {c : Fin d → ℝ} (hc : c ∈ coefficientAnnulus d) : c ≠ 0 := by
  intro hzero
  subst c
  have h := hc.2
  norm_num at h

theorem positive_negative_majority_disjoint {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (i : Fin m) (c : Fin d → ℝ) :
    ¬(c ∈ positiveMajoritySet S a i ∧
      c ∈ negativeMajoritySet S a i) := by
  classical
  intro h
  let P := (S i).filter fun x ↦ 0 < linearValueFin a c x
  let N := (S i).filter fun x ↦ linearValueFin a c x < 0
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    have hp := (Finset.mem_filter.mp hxP).2
    have hn := (Finset.mem_filter.mp hxN).2
    linarith
  have hunion : P ∪ N ⊆ S i := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxP | hxN
    · exact (Finset.mem_filter.mp hxP).1
    · exact (Finset.mem_filter.mp hxN).1
  have hcard : P.card + N.card ≤ (S i).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  have hp : (S i).card < 2 * P.card := h.1
  have hn : (S i).card < 2 * N.card := h.2
  omega

theorem majorityCover_disjoint_neg {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) (c : Fin d → ℝ) :
    ¬(c ∈ majorityCover S a L ∧ c ∈ majorityCover S a L.neg) := by
  cases h : L.positive <;>
    simp only [majorityCover, SignedLabel.neg, h, Bool.not_false,
      Bool.not_true, ↓reduceIte]
  · intro hboth
    exact positive_negative_majority_disjoint S a L.index c
      ⟨hboth.2, hboth.1⟩
  · exact positive_negative_majority_disjoint S a L.index c

theorem ball_neg_subset_majorityCover_neg {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (L : SignedLabel m) (c : Fin d → ℝ) (δ : ℝ)
    (h : Metric.ball c δ ⊆ majorityCover S a L) :
    Metric.ball (-c) δ ⊆ majorityCover S a L.neg := by
  intro z hz
  have hz' : -z ∈ Metric.ball c δ := by
    change dist (-z) c < δ
    change dist z (-c) < δ at hz
    calc
      dist (-z) c = dist (-z) (-(-c)) := by simp
      _ = dist z (-c) := dist_neg_neg z (-c)
      _ < δ := hz
  have hmem := h hz'
  simpa using (mem_majorityCover_neg_iff S a L (-z)).mpr hmem

theorem coefficientAnnulus_covered_of_no_bisection
    {X : Type*} {m d : ℕ}
    (S : Fin m → Finset X) (a : X → Fin d → ℝ)
    (hnone : ¬ ∃ c : Fin d → ℝ, c ≠ 0 ∧
      ∀ i, Bisects (fun x ↦ linearValueFin a c x) (S i)) :
    coefficientAnnulus d ⊆ ⋃ L : SignedLabel m, majorityCover S a L := by
  classical
  intro c hc
  have hcne : c ≠ 0 := mem_coefficientAnnulus_ne_zero hc
  have hnotall : ¬∀ i, Bisects (fun x ↦ linearValueFin a c x) (S i) := by
    intro hall
    exact hnone ⟨c, hcne, hall⟩
  push Not at hnotall
  obtain ⟨i, hi⟩ := hnotall
  have hbad :
      (S i).card < 2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card ∨
      (S i).card < 2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card := by
    change ¬(2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card ≤
        (S i).card ∧
      2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card ≤
        (S i).card) at hi
    by_cases hp : 2 * ((S i).filter fun x ↦ 0 < linearValueFin a c x).card ≤
        (S i).card
    · right
      have hn : ¬ 2 * ((S i).filter fun x ↦ linearValueFin a c x < 0).card ≤
          (S i).card := fun hn ↦ hi ⟨hp, hn⟩
      omega
    · left
      omega
  rcases hbad with hpos | hneg
  · let L : SignedLabel m := ⟨true, i⟩
    exact Set.mem_iUnion.mpr ⟨L, by simpa [majorityCover, positiveMajoritySet]⟩
  · let L : SignedLabel m := ⟨false, i⟩
    exact Set.mem_iUnion.mpr ⟨L, by simpa [majorityCover, negativeMajoritySet]⟩

theorem iteratedAntipode_ne (d r : ℕ)
    (v : (iteratedBoundary d r).Vertex) :
    (iteratedAntipode d r).neg v ≠ v := by
  intro hfixed
  have hanti := realize_antipode d r v
  rw [hfixed] at hanti
  have hzero : realize d r v = 0 := by
    funext i
    change realize d r v i = (0 : ℝ)
    have hi := congrFun hanti i
    simp only [Pi.neg_apply] at hi
    linarith
  exact realize_ne_zero d r v hzero

/-! ## Finite-dimensional Stone--Tukey -/

/-- Simultaneous bisection for families already indexed by standard finite
types. -/
theorem finiteLinearBisection_fin {X : Type*} (m d : ℕ) (hmd : m < d)
    (S : Fin m → Finset X) (a : X → Fin d → ℝ) :
    ∃ c : Fin d → ℝ, c ≠ 0 ∧
      ∀ i, Bisects (fun x ↦ linearValueFin a c x) (S i) := by
  classical
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le m) hmd
  by_cases hm : m = 0
  · subst m
    let j : Fin d := ⟨0, hd⟩
    let c : Fin d → ℝ := Pi.single j 1
    refine ⟨c, ?_, ?_⟩
    · intro hc
      have hj := congrFun hc j
      simp [c, j] at hj
    · intro i
      exact Fin.elim0 i
  · by_contra hnone
    have hcover : coefficientAnnulus d ⊆
        ⋃ L : SignedLabel m, majorityCover S a L :=
      coefficientAnnulus_covered_of_no_bisection S a hnone
    obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric
      (isCompact_coefficientAnnulus d)
      (fun L ↦ isOpen_majorityCover S a L) hcover
    obtain ⟨r, hmesh⟩ :=
      exists_iteratedBoundary_faceDiameter_lt d hd hδ
    let A := iteratedAntipode d r
    let eV := Fintype.equivFin (iteratedBoundary d r).Vertex
    let pick : (iteratedBoundary d r).Vertex → SignedLabel m :=
      fun v ↦ Classical.choose
        (hLeb (realize d r v) (realize_mem_coefficientAnnulus d r v))
    have hpick (v : (iteratedBoundary d r).Vertex) :
        Metric.ball (realize d r v) δ ⊆ majorityCover S a (pick v) :=
      Classical.choose_spec
        (hLeb (realize d r v) (realize_mem_coefficientAnnulus d r v))
    let label : (iteratedBoundary d r).Vertex → SignedLabel m :=
      fun v ↦ if eV v < eV (A.neg v) then pick v else (pick (A.neg v)).neg
    have hlabelAnti (v : (iteratedBoundary d r).Vertex) :
        label (A.neg v) = (label v).neg := by
      by_cases hv : eV v < eV (A.neg v)
      · have hrev : ¬ eV (A.neg v) < eV (A.neg (A.neg v)) := by
          rw [A.neg_neg]
          exact not_lt_of_ge (le_of_lt hv)
        simp only [label]
        rw [if_pos hv, if_neg hrev, A.neg_neg]
      · have hne : eV (A.neg v) ≠ eV v := by
          intro heq
          exact iteratedAntipode_ne d r v (eV.injective heq)
        have hrev : eV (A.neg v) < eV (A.neg (A.neg v)) := by
          rw [A.neg_neg]
          exact lt_of_le_of_ne (le_of_not_gt hv) hne
        simp only [label]
        rw [if_neg hv, if_pos hrev]
        apply SignedLabel.ext <;> simp [SignedLabel.neg]
    have hlabelCandidate (v : (iteratedBoundary d r).Vertex) :
        Metric.ball (realize d r v) δ ⊆ majorityCover S a (label v) := by
      by_cases hv : eV v < eV (A.neg v)
      · simpa [label, hv] using hpick v
      · have hflip := ball_neg_subset_majorityCover_neg S a
          (pick (A.neg v)) (realize d r (A.neg v)) δ (hpick (A.neg v))
        simpa [label, hv, A, realize_antipode] using hflip
    obtain ⟨s, hs, v, hv, w, hw, hcomp⟩ :=
      exists_complementary_face_of_antipodal_of_lt d r m hd hmd
        label hlabelAnti
    have hvCandidate := hlabelCandidate v
    have hwCandidate := hlabelCandidate w
    have hvw : dist (realize d r v) (realize d r w) < δ :=
      hmesh hs hv hw
    have hwBallV : realize d r w ∈ Metric.ball (realize d r v) δ := by
      simpa only [Metric.mem_ball, dist_comm] using hvw
    have hwInV := hvCandidate hwBallV
    rw [hcomp] at hwInV
    have hwInW := hwCandidate (Metric.mem_ball_self hδ)
    exact majorityCover_disjoint_neg S a (label w) (realize d r w)
      ⟨hwInW, hwInV⟩

/-- The universal finite central-hyperplane bisection theorem. -/
theorem finiteLinearBisection : FiniteLinearBisection := by
  classical
  intro I B X _instI _instB hcard S a
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let S' : Fin (Fintype.card I) → Finset X := fun i ↦ S (eI.symm i)
  let a' : X → Fin (Fintype.card B) → ℝ := fun x j ↦ a x (eB.symm j)
  obtain ⟨c', hc', hbisect⟩ :=
    finiteLinearBisection_fin (Fintype.card I) (Fintype.card B)
      hcard S' a'
  let c : B → ℝ := fun b ↦ c' (eB b)
  refine ⟨c, ?_, ?_⟩
  · intro hc
    apply hc'
    funext j
    have hj := congrFun hc (eB.symm j)
    simpa [c] using hj
  · intro i
    have hsum (x : X) :
        linearValueFin a' c' x = ∑ b : B, c b * a x b := by
      unfold linearValueFin
      symm
      apply Fintype.sum_equiv eB
      intro b
      simp [a', c]
    simpa only [S', eI.symm_apply_apply, hsum] using hbisect (eI i)

end Erdos95.StoneTukey
