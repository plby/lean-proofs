import Wikipedia.HopfProblem.ToricHexagon
import Wikipedia.HopfProblem.CuspHoneycombHexagonSquare

/-!
# Oriented charts on the actual zero-ray component

The two coordinates in each of the six affine component charts are
ordered by consecutive rays of the hexagonal fan.  All chart points below
belong to the actual ray divisor in the glued toric space.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open ToricCharts ToricFan Triangle ToricSpace ToricComponent

/-- The existing affine charts need a coordinate interchange precisely in
the second, third, and fourth sectors of the hexagonal fan. -/
def orientedCoordinates (i : Fin 6) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  if i = 1 ∨ i = 2 ∨ i = 3 then ![z 1, z 0] else z

@[simp] theorem orientedCoordinates_involutive (i : Fin 6) (z : CoordinateSpace 2) :
    orientedCoordinates i (orientedCoordinates i z) = z := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext j
    fin_cases j <;> simp [orientedCoordinates, hi]
  · simp [orientedCoordinates, hi]

theorem orientedCoordinates_continuous (i : Fin 6) : Continuous (orientedCoordinates i) := by
  unfold orientedCoordinates
  split_ifs
  · apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 1
    · exact continuous_apply 0
  · exact continuous_id

def orientedHomeomorph (i : Fin 6) : CoordinateSpace 2 ≃ₜ CoordinateSpace 2 where
  toFun := orientedCoordinates i
  invFun := orientedCoordinates i
  left_inv := orientedCoordinates_involutive i
  right_inv := orientedCoordinates_involutive i
  continuous_toFun := orientedCoordinates_continuous i
  continuous_invFun := orientedCoordinates_continuous i

theorem orientedCoordinates_injective (i : Fin 6) : Function.Injective (orientedCoordinates i) :=
  (orientedHomeomorph i).injective

def firstCoordinate : Fin 6 → Fin 3 := ![1, 2, 2, 1, 0, 0]

def secondCoordinate : Fin 6 → Fin 3 := ![2, 1, 0, 0, 1, 2]

theorem firstCoordinate_vertex (i : Fin 6) :
    (zeroTriangle i).vertex (firstCoordinate i) = hexagonRay i := by
  fin_cases i <;> decide

theorem secondCoordinate_vertex (i : Fin 6) :
    (zeroTriangle i).vertex (secondCoordinate i) = hexagonRay (i + 1) := by
  fin_cases i <;> decide

theorem coordinates_exhaustive (i : Fin 6) (j : Fin 3) :
    j = zeroCoordinate i ∨ j = firstCoordinate i ∨ j = secondCoordinate i := by
  fin_cases i <;> fin_cases j <;> decide

def liftCoordinates (i : Fin 6) (z : CoordinateSpace 2) : CoordinateSpace 3 :=
  insertZero (zeroCoordinate i) (orientedCoordinates i z)

@[simp] theorem liftCoordinates_zero (i : Fin 6) (z : CoordinateSpace 2) :
    liftCoordinates i z (zeroCoordinate i) = 0 := insertZero_at _ _

@[simp] theorem liftCoordinates_first (i : Fin 6) (z : CoordinateSpace 2) :
    liftCoordinates i z (firstCoordinate i) = z 0 := by
  fin_cases i <;> rfl

@[simp] theorem liftCoordinates_second (i : Fin 6) (z : CoordinateSpace 2) :
    liftCoordinates i z (secondCoordinate i) = z 1 := by
  fin_cases i <;> rfl

theorem liftCoordinates_table (i : Fin 6) (z : CoordinateSpace 2) :
    liftCoordinates i z =
      ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0],
        ![z 1, z 0, 0], ![z 0, z 1, 0], ![z 0, 0, z 1]] i := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

theorem liftCoordinates_vector (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] =
      ![![0, a, b], ![0, b, a], ![b, 0, a],
        ![b, a, 0], ![a, b, 0], ![a, 0, b]] i :=
  liftCoordinates_table i ![a, b]

/-- The oriented affine chart in the actual zero-ray component. -/
def chartPoint (i : Fin 6) (z : CoordinateSpace 2) : rayDivisor 0 :=
  affineInclusion (zeroChart i) (orientedCoordinates i z)

@[simp] theorem chartPoint_coe (i : Fin 6) (z : CoordinateSpace 2) :
    (chartPoint i z : Space) = inclusion (zeroTriangle i) (liftCoordinates i z) := rfl

theorem chartPoint_openEmbedding (i : Fin 6) : IsOpenEmbedding (chartPoint i) :=
  (affineInclusion_openEmbedding (zeroChart i)).comp (orientedHomeomorph i).isOpenEmbedding

theorem chartPoint_injective (i : Fin 6) : Function.Injective (chartPoint i) :=
  (chartPoint_openEmbedding i).injective

theorem chartPoint_continuous (i : Fin 6) : Continuous (chartPoint i) :=
  (chartPoint_openEmbedding i).continuous

theorem chartPoint_jointly_surjective (x : rayDivisor 0) : ∃ i z, chartPoint i z = x := by
  obtain ⟨c, z, hz⟩ := affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  refine ⟨i, orientedCoordinates i z, ?_⟩
  change affineInclusion (zeroChart i) (orientedCoordinates i (orientedCoordinates i z)) = x
  rw [orientedCoordinates_involutive]
  exact hz

theorem chartPoint_eq_iff (i j : Fin 6) (z w : CoordinateSpace 2) :
    chartPoint i z = chartPoint j w ↔
      liftCoordinates i z ∈ (chartChange (zeroTriangle i) (zeroTriangle j)).source ∧
        chartChange (zeroTriangle i) (zeroTriangle j) (liftCoordinates i z) =
          liftCoordinates j w := by
  rw [Subtype.ext_iff, chartPoint_coe, chartPoint_coe, inclusion_eq_iff]

/-- The two coordinate axes are precisely the two neighboring ray
divisors; every other noncentral ray is absent from this affine chart. -/
theorem chartPoint_mem_rayDivisor_iff (i k : Fin 6) (z : CoordinateSpace 2) :
    (chartPoint i z : Space) ∈ rayDivisor (hexagonRay k) ↔
      (k = i ∧ z 0 = 0) ∨ (k = i + 1 ∧ z 1 = 0) := by
  rw [chartPoint_coe, mem_rayDivisor_inclusion]
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases coordinates_exhaustive i j with rfl | rfl | rfl
    · exact (hexagonRay_ne_zero k ((zeroTriangle_vertex i).symm.trans hv).symm).elim
    · exact Or.inl ⟨(hexagonRay_injective ((firstCoordinate_vertex i).symm.trans hv)).symm,
        by simpa only [liftCoordinates_first] using hj⟩
    · exact Or.inr ⟨(hexagonRay_injective ((secondCoordinate_vertex i).symm.trans hv)).symm,
        by simpa only [liftCoordinates_second] using hj⟩
  · rintro (⟨hki, hz⟩ | ⟨hki, hz⟩)
    · subst k
      exact ⟨firstCoordinate i, (liftCoordinates_first i z).trans hz, firstCoordinate_vertex i⟩
    · subst k
      exact ⟨secondCoordinate i, (liftCoordinates_second i z).trans hz, secondCoordinate_vertex i⟩

/-- The ambient three-coordinate matrices for one step around the
hexagonal star. Only three matrices occur. -/
def nextTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![0, 0, -1; 1, 0, 1; 0, 1, 1],
    !![0, 0, -1; 1, 0, 1; 0, 1, 1],
    !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0]]

theorem transition_next (i : Fin 6) :
    transition (zeroTriangle i) (zeroTriangle (i + 1)) = nextTransitionMatrix i := by
  fin_cases i <;> decide

theorem next_source_iff (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] ∈
      (chartChange (zeroTriangle i) (zeroTriangle (i + 1))).source ↔ a ≠ 0 := by
  rw [chartChange_source, transition_next, liftCoordinates_vector]
  fin_cases i <;>
    norm_num [domain, nextTransitionMatrix, Fin.forall_fin_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]

theorem next_transition (i : Fin 6) (a b : ℂ) :
    chartChange (zeroTriangle i) (zeroTriangle (i + 1))
      (liftCoordinates i ![a, b]) = liftCoordinates (i + 1) ![a * b, a⁻¹] := by
  change monomial (transition _ _) _ = _
  rw [transition_next, liftCoordinates_vector, liftCoordinates_vector]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [monomial, nextTransitionMatrix, Fin.prod_univ_succ, Fin.add_def,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, mul_comm]

/-- The oriented adjacent-chart coordinate change dictated by the fan
relation `vᵢ₊₂ = vᵢ₊₁ - vᵢ`. -/
theorem chartPoint_next (i : Fin 6) (a b : ℂ) (ha : a ≠ 0) :
    chartPoint (i + 1) ![a * b, a⁻¹] = chartPoint i ![a, b] := by
  symm
  exact (chartPoint_eq_iff i (i + 1) ![a, b] ![a * b, a⁻¹]).mpr
    ⟨(next_source_iff i a b).mpr ha, next_transition i a b⟩

theorem chartPoint_eq_next_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 1) ![c, d] ↔
      a ≠ 0 ∧ c = a * b ∧ d = a⁻¹ := by
  constructor
  · intro he
    have ha := (next_source_iff i a b).mp ((chartPoint_eq_iff i (i + 1) _ _).mp he).1
    have hw : ![c, d] = ![a * b, a⁻¹] :=
      chartPoint_injective (i + 1) (he.symm.trans (chartPoint_next i a b ha).symm)
    exact ⟨ha, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact (chartPoint_next i a b ha).symm

/-- Two nonadjacent sectors can meet only in the dense torus of the
component, since their noncentral boundary rays are disjoint. -/
theorem chartPoint_eq_nonadjacent_nonzero {i j : Fin 6} {z w : CoordinateSpace 2}
    (hji : j ≠ i) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1)
    (he : chartPoint i z = chartPoint j w) : z 0 ≠ 0 ∧ z 1 ≠ 0 := by
  have hcoe : (chartPoint i z : Space) = (chartPoint j w : Space) := congrArg Subtype.val he
  constructor
  · intro hz
    have hm : (chartPoint j w : Space) ∈ rayDivisor (hexagonRay i) := by
      rw [← hcoe]
      exact (chartPoint_mem_rayDivisor_iff i i z).mpr (Or.inl ⟨rfl, hz⟩)
    rcases (chartPoint_mem_rayDivisor_iff j i w).mp hm with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hji hi.symm
    · exact hprev hi
  · intro hz
    have hm : (chartPoint j w : Space) ∈ rayDivisor (hexagonRay (i + 1)) := by
      rw [← hcoe]
      exact (chartPoint_mem_rayDivisor_iff i (i + 1) z).mpr (Or.inr ⟨rfl, hz⟩)
    rcases (chartPoint_mem_rayDivisor_iff j (i + 1) w).mp hm with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hnext hi.symm
    · exact hji (add_right_cancel hi).symm

def previousTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![0, 0, -1; 1, 0, 1; 0, 1, 1],
    !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0],
    !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![0, 0, -1; 1, 0, 1; 0, 1, 1]]

theorem transition_previous (i : Fin 6) :
    transition (zeroTriangle i) (zeroTriangle (i + 5)) = previousTransitionMatrix i := by
  fin_cases i <;> decide

theorem previous_source_iff (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] ∈
      (chartChange (zeroTriangle i) (zeroTriangle (i + 5))).source ↔ b ≠ 0 := by
  rw [chartChange_source, transition_previous, liftCoordinates_vector]
  fin_cases i <;>
    norm_num [domain, previousTransitionMatrix, Fin.forall_fin_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]

theorem previous_transition (i : Fin 6) (a b : ℂ) :
    chartChange (zeroTriangle i) (zeroTriangle (i + 5))
      (liftCoordinates i ![a, b]) = liftCoordinates (i + 5) ![b⁻¹, a * b] := by
  change monomial (transition _ _) _ = _
  rw [transition_previous, liftCoordinates_vector, liftCoordinates_vector]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [monomial, previousTransitionMatrix, Fin.prod_univ_succ, Fin.add_def,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, mul_comm] <;> rfl

theorem chartPoint_previous (i : Fin 6) (a b : ℂ) (hb : b ≠ 0) :
    chartPoint (i + 5) ![b⁻¹, a * b] = chartPoint i ![a, b] := by
  symm
  exact (chartPoint_eq_iff i (i + 5) ![a, b] ![b⁻¹, a * b]).mpr
    ⟨(previous_source_iff i a b).mpr hb, previous_transition i a b⟩

theorem chartPoint_eq_previous_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 5) ![c, d] ↔
      b ≠ 0 ∧ c = b⁻¹ ∧ d = a * b := by
  constructor
  · intro he
    have hb := (previous_source_iff i a b).mp ((chartPoint_eq_iff i (i + 5) _ _).mp he).1
    have hw : ![c, d] = ![b⁻¹, a * b] :=
      chartPoint_injective (i + 5) (he.symm.trans (chartPoint_previous i a b hb).symm)
    exact ⟨hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨hb, rfl, rfl⟩
    exact (chartPoint_previous i a b hb).symm

theorem chartPoint_offset_two (i : Fin 6) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    chartPoint (i + 2) ![b, (a * b)⁻¹] = chartPoint i ![a, b] := by
  have hi : (i + 1) + 1 = i + 2 := by rw [add_assoc]; rfl
  have hm : a * b * a⁻¹ = b := by rw [mul_right_comm, mul_inv_cancel₀ ha, one_mul]
  simpa only [hi, hm] using
    (chartPoint_next (i + 1) (a * b) a⁻¹ (mul_ne_zero ha hb)).trans (chartPoint_next i a b ha)

theorem chartPoint_offset_three (i : Fin 6) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    chartPoint (i + 3) ![a⁻¹, b⁻¹] = chartPoint i ![a, b] := by
  have hi : (i + 2) + 1 = i + 3 := by rw [add_assoc]; rfl
  have hm : b * (a * b)⁻¹ = a⁻¹ := by simp [mul_inv_rev, hb]
  simpa only [hi, hm] using
    (chartPoint_next (i + 2) b (a * b)⁻¹ hb).trans (chartPoint_offset_two i a b ha hb)

theorem chartPoint_offset_four (i : Fin 6) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    chartPoint (i + 4) ![(a * b)⁻¹, a] = chartPoint i ![a, b] := by
  have hi : (i + 3) + 1 = i + 4 := by rw [add_assoc]; rfl
  have hm : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by simp [mul_inv_rev, mul_comm]
  simpa only [hi, hm, inv_inv] using
    (chartPoint_next (i + 3) a⁻¹ b⁻¹ (inv_ne_zero ha)).trans
      (chartPoint_offset_three i a b ha hb)

theorem chartPoint_eq_offset_two_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 2) ![c, d] ↔
      a ≠ 0 ∧ b ≠ 0 ∧ c = b ∧ d = (a * b)⁻¹ := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ := chartPoint_eq_nonadjacent_nonzero
      (by fin_cases i <;> decide : i + 2 ≠ i)
      (by fin_cases i <;> decide : i + 2 ≠ i + 1)
      (by fin_cases i <;> decide : i ≠ (i + 2) + 1) he
    have hw : ![c, d] = ![b, (a * b)⁻¹] :=
      chartPoint_injective (i + 2) (he.symm.trans (chartPoint_offset_two i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_two i a b ha hb).symm

theorem chartPoint_eq_offset_three_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 3) ![c, d] ↔
      a ≠ 0 ∧ b ≠ 0 ∧ c = a⁻¹ ∧ d = b⁻¹ := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ := chartPoint_eq_nonadjacent_nonzero
      (by fin_cases i <;> decide : i + 3 ≠ i)
      (by fin_cases i <;> decide : i + 3 ≠ i + 1)
      (by fin_cases i <;> decide : i ≠ (i + 3) + 1) he
    have hw : ![c, d] = ![a⁻¹, b⁻¹] :=
      chartPoint_injective (i + 3) (he.symm.trans (chartPoint_offset_three i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_three i a b ha hb).symm

theorem chartPoint_eq_offset_four_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 4) ![c, d] ↔
      a ≠ 0 ∧ b ≠ 0 ∧ c = (a * b)⁻¹ ∧ d = a := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ := chartPoint_eq_nonadjacent_nonzero
      (by fin_cases i <;> decide : i + 4 ≠ i)
      (by fin_cases i <;> decide : i + 4 ≠ i + 1)
      (by fin_cases i <;> decide : i ≠ (i + 4) + 1) he
    have hw : ![c, d] = ![(a * b)⁻¹, a] :=
      chartPoint_injective (i + 4) (he.symm.trans (chartPoint_offset_four i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_four i a b ha hb).symm

theorem unitSquare_mul_eq_one_iff {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hab : a * b ≤ a := mul_le_of_le_one_right ha.1 hb.2
    have hba : a * b ≤ b := mul_le_of_le_one_left hb.1 ha.2
    rw [h] at hab hba
    exact ⟨le_antisymm ha.2 hab, le_antisymm hb.2 hba⟩
  · rintro ⟨rfl, rfl⟩
    exact one_mul 1

theorem unitSquare_inv_iff {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) = (a : ℂ)⁻¹) ↔ a = 1 ∧ b = 1 := by
  constructor
  · rintro ⟨ha0, hbInv⟩
    have hC : (a : ℂ) * (b : ℂ) = 1 := by
      rw [hbInv, mul_inv_cancel₀ ha0]
    apply (unitSquare_mul_eq_one_iff ha hb).mp
    exact_mod_cast hC
  · rintro ⟨rfl, rfl⟩
    simp

theorem unitSquare_inv_mul_iff {a b c : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv⟩
    have hab : a * b ∈ Icc 0 1 :=
      ⟨mul_nonneg ha.1 hb.1, (mul_le_of_le_one_right ha.1 hb.2).trans ha.2⟩
    have hmul : a * b = 1 ∧ c = 1 := (unitSquare_inv_iff hab hc).mp
      ⟨by simpa only [Complex.ofReal_mul] using mul_ne_zero ha0 hb0,
        by simpa only [Complex.ofReal_mul] using hcInv⟩
    obtain ⟨ha1, hb1⟩ := (unitSquare_mul_eq_one_iff ha hb).mp hmul.1
    exact ⟨ha1, hb1, hmul.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem unitSquare_transition_one_iff {a b c d : ℝ}
    (ha : a ∈ Icc 0 1) (hd : d ∈ Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (c : ℂ) = (a : ℂ) * (b : ℂ) ∧ (d : ℂ) = (a : ℂ)⁻¹) ↔
      a = 1 ∧ c = b ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hc, hdInv⟩
    obtain ⟨ha1, hd1⟩ := (unitSquare_inv_iff ha hd).mp ⟨ha0, hdInv⟩
    refine ⟨ha1, ?_, hd1⟩
    exact_mod_cast (show (c : ℂ) = (b : ℂ) by simpa [ha1] using hc)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem unitSquare_transition_two_iff {a b c d : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hd : d ∈ Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = (b : ℂ) ∧
      (d : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hc, hdInv⟩
    obtain ⟨ha1, hb1, hd1⟩ := (unitSquare_inv_mul_iff ha hb hd).mp ⟨ha0, hb0, hdInv⟩
    refine ⟨ha1, hb1, ?_, hd1⟩
    exact_mod_cast (show (c : ℂ) = 1 by simpa [hb1] using hc)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem unitSquare_transition_three_iff {a b c d : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hd : d ∈ Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = (a : ℂ)⁻¹ ∧
      (d : ℂ) = (b : ℂ)⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv, hdInv⟩
    obtain ⟨ha1, hc1⟩ := (unitSquare_inv_iff ha hc).mp ⟨ha0, hcInv⟩
    obtain ⟨hb1, hd1⟩ := (unitSquare_inv_iff hb hd).mp ⟨hb0, hdInv⟩
    exact ⟨ha1, hb1, hc1, hd1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem unitSquare_transition_four_iff {a b c d : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹ ∧
      (d : ℂ) = (a : ℂ)) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv, hd⟩
    obtain ⟨ha1, hb1, hc1⟩ := (unitSquare_inv_mul_iff ha hb hc).mp ⟨ha0, hb0, hcInv⟩
    refine ⟨ha1, hb1, hc1, ?_⟩
    exact_mod_cast (show (d : ℂ) = 1 by simpa [ha1] using hd)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem unitSquare_transition_five_iff {a b c d : ℝ}
    (hb : b ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    ((b : ℂ) ≠ 0 ∧ (c : ℂ) = (b : ℂ)⁻¹ ∧ (d : ℂ) = (a : ℂ) * (b : ℂ)) ↔
      b = 1 ∧ c = 1 ∧ d = a := by
  constructor
  · rintro ⟨hb0, hcInv, hd⟩
    obtain ⟨hb1, hc1⟩ := (unitSquare_inv_iff hb hc).mp ⟨hb0, hcInv⟩
    refine ⟨hb1, hc1, ?_⟩
    exact_mod_cast (show (d : ℂ) = (a : ℂ) by simpa [hb1] using hd)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem squareComplexCoordinates_vector (p : Square) :
    (fun k : Fin 2 => (p.1 k : ℂ)) = ![(p.1 0 : ℂ), (p.1 1 : ℂ)] := by
  ext k
  fin_cases k <;> rfl

theorem squareComplexCoordinates_injective :
    Function.Injective (fun p : Square => fun k : Fin 2 => (p.1 k : ℂ)) := by
  intro p q h
  apply Subtype.ext
  funext k
  exact Complex.ofReal_injective (congrFun h k)

/-- The literal six unit squares in the actual component have exactly
the common hexagonal gluing relation: neighboring upper edges and the
shared upper-right corner, with no further identifications. -/
theorem chartPoint_square_eq_iff (i j : Fin 6) (p q : Square) :
    chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint j (fun k => (q.1 k : ℂ)) ↔
      SquareRel i j p q := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, j = i + k :=
    ⟨j - i, by rw [add_comm i (j - i), sub_add_cancel]⟩
  fin_cases k
  · change chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 0) (fun k => (q.1 k : ℂ)) ↔
      SquareRel i (i + 0) p q
    rw [add_zero, squareRel_self]
    exact ((chartPoint_injective i).comp squareComplexCoordinates_injective).eq_iff
  · change chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 1) (fun k => (q.1 k : ℂ)) ↔
      SquareRel i (i + 1) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_next_iff, squareRel_next]
    simpa only [and_assoc, and_comm, and_left_comm] using
      (unitSquare_transition_one_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1)
        (p.2 0) (q.2 1))
  · change chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 2) (fun k => (q.1 k : ℂ)) ↔
      SquareRel i (i + 2) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_two_iff, squareRel_add_two]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_two_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1)
        (p.2 0) (p.2 1) (q.2 1))
  · change chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 3) (fun k => (q.1 k : ℂ)) ↔
      SquareRel i (i + 3) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_three_iff, squareRel_add_three]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_three_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1)
        (p.2 0) (p.2 1) (q.2 0) (q.2 1))
  · change chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 4) (fun k => (q.1 k : ℂ)) ↔
      SquareRel i (i + 4) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_four_iff, squareRel_add_four]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_four_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1)
        (p.2 0) (p.2 1) (q.2 0))
  · change chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 5) (fun k => (q.1 k : ℂ)) ↔
      SquareRel i (i + 5) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_previous_iff, squareRel_prev]
    exact unitSquare_transition_five_iff (p.2 1) (q.2 0)

end Wikipedia.HopfProblem.CuspHoneycombHexagon
