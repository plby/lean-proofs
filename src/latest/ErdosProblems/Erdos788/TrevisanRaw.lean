import ErdosProblems.Erdos788.Reconstruction
import ErdosProblems.Erdos788.TrevisanParameters
import ErdosProblems.Erdos788.SequentialPrediction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The raw Trevisan extractor family

This file combines the finite hybrid/prediction argument with the
reconstruction data from `Reconstruction.lean`.
-/

namespace Erdos788

open scoped BigOperators

namespace Reconstruction

local instance rawFintypeCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : Fintype D.Coord :=
  D.instFintypeCoord

local instance rawDecidableEqCoord {ell r : ℕ}
    {D : SuffixDesign ell r} : DecidableEq D.Coord :=
  D.instDecidableEqCoord

/-- Summing a test function against a pushforward is the same as summing
its pullback against the original finite distribution. -/
theorem sum_map_mass_mul
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinDist A) (f : A → B) (g : B → ℝ) :
    ∑ b, (P.map f).mass b * g b = ∑ a, P.mass a * g (f a) := by
  simp only [FinDist.map_mass, Finset.sum_mul]
  calc
    (∑ b, ∑ a with f a = b, P.mass a * g b) =
        ∑ b, ∑ a with f a = b, P.mass a * g (f a) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, P.mass a * g (f a) := by
      simpa using! (Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset A) (Finset.univ : Finset B) f
        (fun a ↦ P.mass a * g (f a)))

/-- The joint law of a uniform seed and the extractor output on source
`P`. -/
noncomputable def seedOutputDist
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r))) :
    FinDist ((D.Coord → Bool) × FFVec p r) where
  mass := fun yz ↦
    (FinDist.uniform (D.Coord → Bool)).mass yz.1 *
      (P.map (fixedSeedMap C D yz.1)).mass yz.2
  nonneg := fun yz ↦ mul_nonneg
    ((FinDist.uniform (D.Coord → Bool)).nonneg yz.1)
    ((P.map (fixedSeedMap C D yz.1)).nonneg yz.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ y, ∑ z,
          (FinDist.uniform (D.Coord → Bool)).mass y *
            (P.map (fixedSeedMap C D y)).mass z) =
          ∑ y, (FinDist.uniform (D.Coord → Bool)).mass y *
            ∑ z, (P.map (fixedSeedMap C D y)).mass z := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.mul_sum]
      _ = 1 := by
        simp only [FinDist.sum_mass, mul_one]

@[simp]
theorem seedOutputDist_mass
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r)))
    (yz : (D.Coord → Bool) × FFVec p r) :
    (seedOutputDist C D P).mass yz =
      (FinDist.uniform (D.Coord → Bool)).mass yz.1 *
        (P.map (fixedSeedMap C D yz.1)).mass yz.2 :=
  rfl

/-- The seed marginal of the joint seed/output law is uniform. -/
theorem seedOutputDist_fst
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r))) :
    (seedOutputDist C D P).fst =
      FinDist.uniform (D.Coord → Bool) := by
  ext y
  rw [FinDist.fst_mass]
  simp only [seedOutputDist_mass]
  rw [← Finset.mul_sum, FinDist.sum_mass, mul_one]

/-- Averaging the fixed-seed total variations is exactly the total
variation of the joint seed/output law. -/
theorem average_tv_eq_seedOutputDist_tv
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r))) :
    (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ y : D.Coord → Bool,
          (P.map (fixedSeedMap C D y)).tv
            (FinDist.uniform (FFVec p r)) =
      (seedOutputDist C D P).tv
        ((FinDist.uniform (D.Coord → Bool)).prod
          (FinDist.uniform (FFVec p r))) := by
  simp only [FinDist.tv]
  rw [Fintype.sum_prod_type]
  simp only [seedOutputDist_mass, FinDist.prod_mass, FinDist.uniform_mass]
  have hseed : 0 ≤
      (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ := by positivity
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg hseed]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  apply Finset.sum_congr rfl
  intro z _hz
  ring

@[simp]
theorem tuplePrefix_fixedSeedMap
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r)
    (i : Fin r) (x : FFVec p (2 * r))
    (y : D.Coord → Bool) :
    FinDist.tuplePrefix i (fixedSeedMap C D y x) =
      outputPrefix C D i x y := by
  funext j
  unfold FinDist.tuplePrefix fixedSeedMap outputPrefix
  apply congrArg (fun k : Fin r ↦
    C.encoder x (seedCodeCoord D k y))
  apply Fin.ext
  rw [priorIndex_val_of_lt i j.isLt]
  rfl

/-- The success indicator of a sequential predictor on input `x` and seed
`y`. -/
noncomputable def predictorSuccess
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) (y : D.Coord → Bool) : ℝ :=
  if predictor (y, outputPrefix C D i x y) =
      C.encoder x (seedCodeCoord D i y) then 1 else 0

/-- Success probability of a predictor over the uniform design seed. -/
noncomputable def predictorSuccessRate
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) : ℝ :=
  (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
    ∑ y, predictorSuccess C D i predictor x y

/-- The sequential success expression for the joint seed/output law is the
source average of the per-input seed success rates. -/
theorem sequential_sum_eq_weighted_successRate
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (P : FinDist (FFVec p (2 * r))) :
    (∑ w, (seedOutputDist C D P).mass w *
        (if predictor (w.1, FinDist.tuplePrefix i w.2) = w.2 i
          then (1 : ℝ) else 0)) =
      ∑ x, P.mass x * predictorSuccessRate C D i predictor x := by
  rw [Fintype.sum_prod_type]
  simp only [seedOutputDist_mass, FinDist.uniform_mass]
  have hy' (y : D.Coord → Bool) :
      (∑ z, (P.map (fixedSeedMap C D y)).mass z *
          (if predictor (y, FinDist.tuplePrefix i z) = z i
            then (1 : ℝ) else 0)) =
        ∑ x, P.mass x * predictorSuccess C D i predictor x y := by
    rw [sum_map_mass_mul]
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [tuplePrefix_fixedSeedMap]
    rfl
  unfold predictorSuccessRate
  calc
    (∑ y, ∑ z,
        ((Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
          (P.map (fixedSeedMap C D y)).mass z) *
          (if predictor (y, FinDist.tuplePrefix i z) = z i
            then (1 : ℝ) else 0)) =
      ∑ y, (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ z, (P.map (fixedSeedMap C D y)).mass z *
          (if predictor (y, FinDist.tuplePrefix i z) = z i
            then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      ring
    _ = ∑ y, (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ x, P.mass x * predictorSuccess C D i predictor x y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hy']
    _ = ∑ x, P.mass x *
        ((Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
          ∑ y, predictorSuccess C D i predictor x y) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      ring

theorem predictorSuccessRate_nonneg
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) :
    0 ≤ predictorSuccessRate C D i predictor x := by
  unfold predictorSuccessRate
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro y _hy
  unfold predictorSuccess
  split <;> norm_num

theorem predictorSuccessRate_le_one
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) :
    predictorSuccessRate C D i predictor x ≤ 1 := by
  have hpoint : ∀ y : D.Coord → Bool,
      predictorSuccess C D i predictor x y ≤ 1 := by
    intro y
    unfold predictorSuccess
    split <;> norm_num
  have hsum : (∑ y, predictorSuccess C D i predictor x y) ≤
      ∑ _y : D.Coord → Bool, (1 : ℝ) :=
    Finset.sum_le_sum fun y _hy ↦ hpoint y
  unfold predictorSuccessRate
  have hcard : (0 : ℝ) < Fintype.card (D.Coord → Bool) := by
    exact_mod_cast Fintype.card_pos
  calc
    (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ y, predictorSuccess C D i predictor x y ≤
      (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ _y : D.Coord → Bool, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by simp

/-- Inputs whose predictor succeeds with advantage more than `η`. -/
noncomputable def badInputs
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p) :
    Finset (FFVec p (2 * r)) := by
  classical
  exact Finset.univ.filter fun x ↦
    1 / (p : ℝ) + η < predictorSuccessRate C D i predictor x

/-- If the source-average success advantage is more than `2η`, the bad
inputs carry mass more than `η`. -/
theorem eta_lt_mass_badInputs
    {p r : ℕ} [Fact p.Prime] {η : ℝ} (hη : 0 < η)
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (P : FinDist (FFVec p (2 * r)))
    (havg : 1 / (p : ℝ) + 2 * η <
      ∑ x, P.mass x * predictorSuccessRate C D i predictor x) :
    η < ∑ x ∈ badInputs C D i predictor, P.mass x := by
  classical
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hpoint (x : FFVec p (2 * r)) :
      predictorSuccessRate C D i predictor x ≤
        1 / (p : ℝ) + η +
          (if x ∈ badInputs C D i predictor then (1 : ℝ) else 0) := by
    by_cases hx : x ∈ badInputs C D i predictor
    · rw [if_pos hx]
      have hrate := predictorSuccessRate_le_one C D i predictor x
      have hbase : 0 ≤ 1 / (p : ℝ) + η := by positivity
      linarith
    · rw [if_neg hx]
      have hnot : ¬(1 / (p : ℝ) + η <
          predictorSuccessRate C D i predictor x) := by
        simpa [badInputs] using! hx
      linarith
  have hweighted :
      (∑ x, P.mass x * predictorSuccessRate C D i predictor x) ≤
        1 / (p : ℝ) + η +
          ∑ x ∈ badInputs C D i predictor, P.mass x := by
    calc
      (∑ x, P.mass x * predictorSuccessRate C D i predictor x) ≤
          ∑ x, P.mass x *
            (1 / (p : ℝ) + η +
              (if x ∈ badInputs C D i predictor then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun x _hx ↦
          mul_le_mul_of_nonneg_left (hpoint x) (P.nonneg x)
      _ = 1 / (p : ℝ) + η +
          ∑ x ∈ badInputs C D i predictor, P.mass x := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
          P.sum_mass, one_mul]
        simp
  linarith

/-- An average extractor failure produces a sequential predictor with
advantage `2 * trevisanEta`. -/
theorem exists_predictor_of_average_tv_gt
    {p r : ℕ} [Fact p.Prime] (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r))
    (D : SuffixDesign C.ell r)
    (P : FinDist (FFVec p (2 * r)))
    (havg : (1 / 20 : ℝ) <
      (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
        ∑ y : D.Coord → Bool,
          (P.map (fixedSeedMap C D y)).tv
            (FinDist.uniform (FFVec p r))) :
    ∃ i : Fin r,
      ∃ predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p,
        1 / (p : ℝ) + 2 * trevisanEta p r <
          ∑ x, P.mass x * predictorSuccessRate C D i predictor x := by
  let J := seedOutputDist C D P
  have hfar : (1 / 20 : ℝ) <
      J.tv (J.fst.prod (FinDist.uniform (FFVec p r))) := by
    rw [seedOutputDist_fst]
    rw [← average_tv_eq_seedOutputDist_tv]
    exact havg
  obtain ⟨i, predictor, hpredictor⟩ :=
    FinDist.exists_sequential_predictor_of_tv_gt J (1 / 20 : ℝ)
      hr (by norm_num) hfar
  refine ⟨i, predictor, ?_⟩
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hconst :
      2 * trevisanEta p r = (1 / 20 : ℝ) / ((r : ℝ) * p) := by
    rw [trevisanEta]
    field_simp
    ring
  calc
    1 / (p : ℝ) + 2 * trevisanEta p r =
        1 / (p : ℝ) + (1 / 20 : ℝ) / ((r : ℝ) * p) := by
      rw [hconst]
    _ < ∑ w, J.mass w *
        (if predictor (w.1, FinDist.tuplePrefix i w.2) = w.2 i
          then (1 : ℝ) else 0) := hpredictor
    _ = ∑ x, P.mass x * predictorSuccessRate C D i predictor x := by
      exact sequential_sum_eq_weighted_successRate C D i predictor P

@[simp]
theorem seedCodeCoord_combineSeed
    {ell r : ℕ} (D : SuffixDesign ell r) (i : Fin r)
    (a : OutsideAssignment D i) (z : RowAssignment D i) :
    seedCodeCoord D i (combineSeed D i a z) =
      (rowAssignmentEquiv D i).symm z := by
  apply (rowAssignmentEquiv D i).injective
  funext c
  rw [seedCodeCoord_apply_equiv, Equiv.apply_symm_apply]
  exact combineSeed_apply_mem D i a z c.2

/-- Predictor success after fixing all seed bits outside the distinguished
design row. -/
noncomputable def insideSuccessRate
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i) : ℝ :=
  (Fintype.card (RowAssignment D i) : ℝ)⁻¹ *
    ∑ z, predictorSuccess C D i predictor x (combineSeed D i a z)

/-- Averaging first over the outside seed bits and then over the row bits
is the same as averaging over the full seed. -/
theorem predictorSuccessRate_eq_average_inside
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) :
    predictorSuccessRate C D i predictor x =
      (Fintype.card (OutsideAssignment D i) : ℝ)⁻¹ *
        ∑ a, insideSuccessRate C D i predictor x a := by
  have hcard : Fintype.card (D.Coord → Bool) =
      Fintype.card (OutsideAssignment D i) *
        Fintype.card (RowAssignment D i) := by
    rw [Fintype.card_congr (seedSplitEquiv D i), Fintype.card_prod]
  have hsum :
      (∑ y : D.Coord → Bool, predictorSuccess C D i predictor x y) =
        ∑ q : OutsideAssignment D i × RowAssignment D i,
          predictorSuccess C D i predictor x
            (combineSeed D i q.1 q.2) := by
    symm
    exact Fintype.sum_equiv (seedSplitEquiv D i).symm _ _
      (fun q ↦ rfl)
  unfold predictorSuccessRate insideSuccessRate
  rw [hsum, Fintype.sum_prod_type, hcard]
  push_cast
  have hA : (0 : ℝ) < Fintype.card (OutsideAssignment D i) := by
    exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card (RowAssignment D i) := by
    exact_mod_cast Fintype.card_pos
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  field_simp

/-- A globally successful input has an outside-row fixing on which the
inside-row agreement remains above the same threshold. -/
theorem exists_outside_of_successRate_gt
    {p r : ℕ} [Fact p.Prime] {η t : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r))
    (hx : t < predictorSuccessRate C D i predictor x) :
    ∃ a : OutsideAssignment D i,
      t < insideSuccessRate C D i predictor x a := by
  let μ : OutsideAssignment D i → ℝ :=
    fun a ↦ insideSuccessRate C D i predictor x a
  let a₀ := FinDist.finiteArgmax (OutsideAssignment D i) μ
  have havg := FinDist.average_le_argmax_mass μ
  have heq := predictorSuccessRate_eq_average_inside C D i predictor x
  refine ⟨a₀, ?_⟩
  rw [heq] at hx
  have hrewrite :
      (Fintype.card (OutsideAssignment D i) : ℝ)⁻¹ * ∑ a, μ a =
        (∑ a, μ a) / Fintype.card (OutsideAssignment D i) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hrewrite] at hx
  exact hx.trans_le havg

/-- Agreement is the uniform average of its equality indicators. -/
theorem agreement_eq_average_indicator
    {p ell : ℕ} (u v : BinaryCoord ell → ZMod p) :
    agreement u v =
      (Fintype.card (BinaryCoord ell) : ℝ)⁻¹ *
        ∑ q, if u q = v q then (1 : ℝ) else 0 := by
  have hsum :
      (∑ q, if u q = v q then (1 : ℝ) else 0) =
        (agreementCount u v : ℝ) := by
    classical
    unfold agreementCount
    simp [Finset.sum_boole]
  rw [hsum, agreement, div_eq_mul_inv, mul_comm]

/-- For the genuine reconstruction description, inside-row predictor
success is exactly codeword agreement with the reconstructed received
word. -/
theorem insideSuccessRate_eq_agreement_description
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    (x : FFVec p (2 * r)) (a : OutsideAssignment D i) :
    insideSuccessRate C D i predictor x a =
      agreement (C.encoder x)
        (descriptionWord C D i (fun y z ↦ predictor (y, z))
          (a, actualPriorTable C D i x a)) := by
  unfold insideSuccessRate
  rw [agreement_eq_average_indicator]
  rw [card_binaryCoord_eq_rowAssignment D i]
  congr 1
  exact Fintype.sum_equiv (rowAssignmentEquiv D i).symm _ _ (fun z ↦ by
    simp only [predictorSuccess, seedCodeCoord_combineSeed]
    rw [descriptionWord_actual]
    simp only [Equiv.apply_symm_apply]
    by_cases h : C.encoder x ((rowAssignmentEquiv D i).symm z) =
        predictor (combineSeed D i a z,
          outputPrefix C D i x (combineSeed D i a z))
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (by simpa [eq_comm] using! h)])

/-- Every bad input belongs to one list indexed by a reconstruction
description. -/
theorem exists_description_of_mem_badInputs
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p)
    {x : FFVec p (2 * r)}
    (hx : x ∈ badInputs C D i predictor) :
    ∃ desc : Description (p := p) D i,
      x ∈ codeAgreementList C.encoder
        (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η := by
  have hbad : 1 / (p : ℝ) + η <
      predictorSuccessRate C D i predictor x := by
    simpa [badInputs] using! (Finset.mem_filter.mp hx).2
  obtain ⟨a, ha⟩ := exists_outside_of_successRate_gt
    C D i predictor x hbad
  refine ⟨(a, actualPriorTable C D i x a), ?_⟩
  simp only [codeAgreementList, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← insideSuccessRate_eq_agreement_description C D i predictor x a]
  exact ha

/-- The bad inputs are covered by one short code list for every possible
reconstruction description. -/
theorem card_badInputs_lt_description_count
    {p r : ℕ} [Fact p.Prime] {η : ℝ}
    (C : ShortLinearCode p (2 * r) η)
    (D : SuffixDesign C.ell r) (i : Fin r)
    (predictor : (D.Coord → Bool) × FFVec p i.val → ZMod p) :
    ((badInputs C D i predictor).card : ℝ) <
      ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) *
        (2 / η ^ 2 + 1) := by
  classical
  let Bad := {x : FFVec p (2 * r) // x ∈ badInputs C D i predictor}
  let descOf : Bad → Description (p := p) D i := fun bx ↦
    Classical.choose (exists_description_of_mem_badInputs
      C D i predictor bx.2)
  have descOf_mem (bx : Bad) :
      bx.1 ∈ codeAgreementList C.encoder
        (descriptionWord C D i (fun y z ↦ predictor (y, z))
          (descOf bx)) η :=
    Classical.choose_spec (exists_description_of_mem_badInputs
      C D i predictor bx.2)
  let Candidate := Σ desc : Description (p := p) D i,
    {x : FFVec p (2 * r) //
      x ∈ codeAgreementList C.encoder
        (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η}
  let f : Bad → Candidate := fun bx ↦
    ⟨descOf bx, ⟨bx.1, descOf_mem bx⟩⟩
  have hf : Function.Injective f := by
    intro bx bx' hxy
    apply Subtype.ext
    exact congrArg (fun q : Candidate ↦ q.2.1) hxy
  have hcardNat : Fintype.card Bad ≤ Fintype.card Candidate :=
    Fintype.card_le_of_injective f hf
  have hcard : ((badInputs C D i predictor).card : ℝ) ≤
      (Fintype.card Candidate : ℝ) := by
    have hcardNat' : (badInputs C D i predictor).card ≤
        Fintype.card Candidate := by
      simpa only [Bad, Fintype.card_coe] using! hcardNat
    exact_mod_cast hcardNat'
  have hcandidate : (Fintype.card Candidate : ℝ) =
      ∑ desc : Description (p := p) D i,
        ((codeAgreementList C.encoder
          (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η).card : ℝ) := by
    dsimp only [Candidate]
    rw [Fintype.card_sigma]
    push_cast
    apply Finset.sum_congr rfl
    intro desc _hdesc
    simp
  let J : ℝ := 2 / η ^ 2 + 1
  let desc₀ : Description (p := p) D i :=
    (fun _ ↦ false, fun _ _ ↦ 0)
  have hnonempty : (Finset.univ : Finset (Description (p := p) D i)).Nonempty :=
    ⟨desc₀, Finset.mem_univ _⟩
  have hsumlt :
      (∑ desc : Description (p := p) D i,
        ((codeAgreementList C.encoder
          (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η).card : ℝ)) <
        ∑ _desc : Description (p := p) D i, J := by
    apply Finset.sum_lt_sum_of_nonempty hnonempty
    intro desc _hdesc
    exact C.listBound _
  have hsumconst :
      (∑ _desc : Description (p := p) D i, J) =
        (Fintype.card (Description (p := p) D i) : ℝ) * J := by
    simp
  have hdescNat := card_description_le (p := p) D i
  have hdesc : (Fintype.card (Description (p := p) D i) : ℝ) ≤
      ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) := by
    exact_mod_cast hdescNat
  have hJ : 0 ≤ J := by
    dsimp [J]
    positivity
  calc
    ((badInputs C D i predictor).card : ℝ) ≤
        (Fintype.card Candidate : ℝ) := hcard
    _ = ∑ desc : Description (p := p) D i,
        ((codeAgreementList C.encoder
          (descriptionWord C D i (fun y z ↦ predictor (y, z)) desc) η).card : ℝ) :=
      hcandidate
    _ < ∑ _desc : Description (p := p) D i, J := hsumlt
    _ = (Fintype.card (Description (p := p) D i) : ℝ) * J := hsumconst
    _ ≤ ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) * J :=
      mul_le_mul_of_nonneg_right hdesc hJ
    _ = ((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) *
        (2 / η ^ 2 + 1) := rfl

/-- The raw Trevisan family associated with a short code and a suffix-slack
design. -/
noncomputable def rawTrevisanFamily
    {p r d s : ℕ} [Fact p.Prime] (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r))
    (D : SuffixDesign C.ell r)
    (hseed : 2 ^ D.coordCard ≤ p ^ d)
    (hcount :
      (((2 ^ D.coordCard * p ^ (r - 1) : ℕ) : ℝ) *
          (2 / trevisanEta p r ^ 2 + 1)) ≤
        trevisanEta p r * (p ^ (r + s) : ℕ)) :
    RawLinearExtractorFamily p r d s where
  Seed := D.Coord → Bool
  seedFintype := inferInstance
  seedDecidableEq := inferInstance
  seedNonempty := inferInstance
  card_seed_le := by
    simpa [SuffixDesign.coordCard] using! hseed
  map := fixedSeedMap C D
  extracts := by
    intro P hpoint
    by_contra hfail
    have havg : (1 / 20 : ℝ) <
        (Fintype.card (D.Coord → Bool) : ℝ)⁻¹ *
          ∑ y : D.Coord → Bool,
            (P.map (fixedSeedMap C D y)).tv
              (FinDist.uniform (FFVec p r)) := lt_of_not_ge hfail
    obtain ⟨i, predictor, hpredictor⟩ :=
      exists_predictor_of_average_tv_gt hr C D P havg
    have hpNat : 0 < p := (Fact.out : p.Prime).pos
    have hη : 0 < trevisanEta p r := trevisanEta_pos hpNat hr
    have hmass : trevisanEta p r <
        ∑ x ∈ badInputs C D i predictor, P.mass x :=
      eta_lt_mass_badInputs hη C D i predictor P hpredictor
    have hbadCard := card_badInputs_lt_description_count C D i predictor
    have hbadCount : ((badInputs C D i predictor).card : ℝ) <
        trevisanEta p r * (p ^ (r + s) : ℕ) :=
      hbadCard.trans_le hcount
    let K : ℕ := p ^ (r + s)
    have hKnat : 0 < K := by
      dsimp [K]
      positivity
    have hK : (0 : ℝ) < K := by exact_mod_cast hKnat
    have hmassUpper :
        (∑ x ∈ badInputs C D i predictor, P.mass x) ≤
          ((badInputs C D i predictor).card : ℝ) * (K : ℝ)⁻¹ := by
      calc
        (∑ x ∈ badInputs C D i predictor, P.mass x) ≤
            ∑ _x ∈ badInputs C D i predictor, (K : ℝ)⁻¹ :=
          Finset.sum_le_sum fun x _hx ↦ hpoint x
        _ = ((badInputs C D i predictor).card : ℝ) * (K : ℝ)⁻¹ := by
          simp
    have hratio :
        ((badInputs C D i predictor).card : ℝ) * (K : ℝ)⁻¹ <
          trevisanEta p r := by
      rw [← div_eq_mul_inv]
      calc
        ((badInputs C D i predictor).card : ℝ) / K <
            (trevisanEta p r * K) / K :=
          (div_lt_div_iff_of_pos_right hK).2 (by simpa [K] using! hbadCount)
        _ = trevisanEta p r := by field_simp
    linarith

/-- The canonical seed and entropy-slack exponents satisfy the two
counting hypotheses of `rawTrevisanFamily`. -/
noncomputable def canonicalRawTrevisanFamily
    {p r : ℕ} [Fact p.Prime] (hp : 2 < p) (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r))
    (D : SuffixDesign C.ell r) :
    RawLinearExtractorFamily p r
      (trevisanSeedExponent p D.coordCard)
      (trevisanSlackExponent p r D.coordCard) :=
  rawTrevisanFamily hr C D
    (seedThreshold_le_pow_seedExponent (by omega))
    (trevisan_reconstruction_count hp hr)

/-- Existence of the complete raw Trevisan family with the canonical
integer parameters. -/
theorem exists_canonicalRawTrevisanFamily
    (p r : ℕ) [Fact p.Prime] (hp : 2 < p) (hr : 0 < r) :
    ∃ C : ShortLinearCode p (2 * r) (trevisanEta p r),
      ∃ D : SuffixDesign C.ell r,
        Nonempty (RawLinearExtractorFamily p r
          (trevisanSeedExponent p D.coordCard)
          (trevisanSlackExponent p r D.coordCard)) := by
  have hm : 1 ≤ 2 * r := by omega
  obtain ⟨C⟩ := exists_shortLinearCode p (2 * r) hm
    (trevisanEta p r)
    (trevisanEta_pos (by omega) hr)
    (trevisanEta_lt_half hp hr)
  let D := SuffixDesign.build C.ell r
  exact ⟨C, D, ⟨canonicalRawTrevisanFamily hp hr C D⟩⟩

end Reconstruction

end Erdos788
