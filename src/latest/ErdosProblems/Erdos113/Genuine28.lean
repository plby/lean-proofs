import ErdosProblems.Erdos113.Cycle28
import ErdosProblems.Erdos113.Encode28
import ErdosProblems.Erdos113.Moments28
import ErdosProblems.Erdos113.Moments
import ErdosProblems.Erdos113.MomentsBipartite
import ErdosProblems.Erdos113.ConflictSides28

open scoped Real SimpleGraph BigOperators

namespace Erdos113Genuine28

open Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev HomCycle28 (G : SimpleGraph V) :=
  {x : Fin 28 → V // IsHomCycle G x}

abbrev RepeatedHomCycle28 (G : SimpleGraph V) :=
  {x : HomCycle28 G // ¬ Function.Injective x.1}

noncomputable def homCyclePartition (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    HomCycle28 G → ↑(genuineCycles G 28) ⊕ RepeatedHomCycle28 G :=
  fun x ↦ by
    classical
    by_cases hinj : Function.Injective x.1
    · exact Sum.inl ⟨x.1, mem_genuineCycles.mpr ⟨hinj, x.2⟩⟩
    · exact Sum.inr ⟨x, hinj⟩

def homCyclePartitionDecode {G : SimpleGraph V} [DecidableRel G.Adj] :
    ↑(genuineCycles G 28) ⊕ RepeatedHomCycle28 G → (Fin 28 → V)
  | Sum.inl x => x.1
  | Sum.inr x => x.1.1

@[simp] lemma homCyclePartitionDecode_partition
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : HomCycle28 G) :
    homCyclePartitionDecode (homCyclePartition G x) = x.1 := by
  classical
  unfold homCyclePartition
  split <;> rfl

lemma homCyclePartition_injective (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (homCyclePartition G) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg homCyclePartitionDecode hxy
  simpa using h

noncomputable def repeatedHomCycleToBadClosedWalk
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    RepeatedHomCycle28 G →
      Encode28.BadClosedWalk28 G (fun u v ↦ u = v) :=
  fun x ↦ by
    let P := Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp x.2
    refine ⟨i, j, hne, ?_⟩
    have hread :=
      Erdos113Cycle28.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    exact (congrFun hread i).trans (hij.trans (congrFun hread j).symm)

lemma repeatedHomCycleToBadClosedWalk_injective
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (repeatedHomCycleToBadClosedWalk G) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg (fun z ↦ (z.1 : Encode28.ClosedWalk28 G)) hxy
  change Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2 =
    Erdos113Cycle28.tupleClosedWalk y.1.1 y.1.2 at hP
  have hread := congrArg (Erdos113Cycle28.closedWalkTuple G) hP
  simpa only [Erdos113Cycle28.closedWalkTuple_tupleClosedWalk] using hread

lemma card_homCycle28_le_genuine_add_bad
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (HomCycle28 G) ≤
      (genuineCycles G 28).card +
        Fintype.card
          (Encode28.BadClosedWalk28 G (fun u v ↦ u = v)) := by
  have hpartition := Fintype.card_le_of_injective (homCyclePartition G)
    (homCyclePartition_injective G)
  rw [Fintype.card_sum, Fintype.card_coe] at hpartition
  have hrepeat := Fintype.card_le_of_injective
    (repeatedHomCycleToBadClosedWalk G)
    (repeatedHomCycleToBadClosedWalk_injective G)
  omega

lemma card_homCycle28_eq_closedWalkCount
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (HomCycle28 G) = Conflict28.closedWalkCount G 28 := by
  calc
    Fintype.card (HomCycle28 G) = Conflict.closedWalkCount G 28 :=
      Erdos113Cycle28.card_homCycle28_eq_closedWalkCount G
    _ = Conflict28.closedWalkCount G 28 := rfl

lemma repeatedBadClosedWalk28_cast_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (t D : ℝ)
    (ht : 0 < t) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D) :
    (Fintype.card
      (Encode28.BadClosedWalk28 G (fun u v ↦ u = v)) : ℝ) ≤
      28 * (D * t * (Conflict28.closedWalkCount G 26 : ℝ) +
        14 * t⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) := by
  have hlocal : ∀ u y,
      (((G.neighborFinset y).filter (fun v ↦ u = v)).card : ℝ) ≤ 1 := by
    intro u y
    have hsub : (G.neighborFinset y).filter (fun v ↦ u = v) ⊆ {u} := by
      intro v hv
      simpa using (Finset.mem_filter.mp hv).2.symm
    exact_mod_cast (Finset.card_le_card hsub).trans (by simp)
  simpa only [mul_one, one_mul] using
    (Encode28.card_BadClosedWalk28_cast_le G (fun u v ↦ u = v)
      t D 1 ht (by norm_num) hdeg (fun _ _ h ↦ h.symm) hlocal)

abbrev RelationFreeHomCycle28
    (G : SimpleGraph V) (R : V → V → Prop) :=
  {x : HomCycle28 G // ∀ i j, i ≠ j → ¬ R (x.1 i) (x.1 j)}

abbrev RelationBadHomCycle28
    (G : SimpleGraph V) (R : V → V → Prop) :=
  {x : HomCycle28 G // ∃ i j, i ≠ j ∧ R (x.1 i) (x.1 j)}

noncomputable def relationPartition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    HomCycle28 G → RelationFreeHomCycle28 G R ⊕ RelationBadHomCycle28 G R :=
  fun x ↦ by
    classical
    by_cases hfree : ∀ i j, i ≠ j → ¬ R (x.1 i) (x.1 j)
    · exact Sum.inl ⟨x, hfree⟩
    · push Not at hfree
      exact Sum.inr ⟨x, hfree⟩

def relationPartitionDecode
    {G : SimpleGraph V} {R : V → V → Prop} :
    RelationFreeHomCycle28 G R ⊕ RelationBadHomCycle28 G R → (Fin 28 → V)
  | Sum.inl x => x.1.1
  | Sum.inr x => x.1.1

@[simp] lemma relationPartitionDecode_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] (x : HomCycle28 G) :
    relationPartitionDecode (relationPartition G R x) = x.1 := by
  classical
  unfold relationPartition
  split <;> rfl

lemma relationPartition_injective
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    Function.Injective (relationPartition G R) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg relationPartitionDecode hxy
  simpa using h

noncomputable def relationBadHomCycleToBadClosedWalk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    RelationBadHomCycle28 G R → Encode28.BadClosedWalk28 G R :=
  fun x ↦ by
    let P := Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2
    refine ⟨P, ?_⟩
    obtain ⟨i, j, hij, hR⟩ := x.2
    refine ⟨i, j, hij, ?_⟩
    have hread :=
      Erdos113Cycle28.closedWalkTuple_tupleClosedWalk x.1.1 x.1.2
    have hi := congrFun hread i
    have hj := congrFun hread j
    rw [← hi, ← hj] at hR
    simpa [P, Encode28.cv, Erdos113Cycle28.closedWalkTuple] using hR

@[simp] lemma relationBadHomCycleToBadClosedWalk_walk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (x : RelationBadHomCycle28 G R) :
    ((relationBadHomCycleToBadClosedWalk G R x).1 : Encode28.ClosedWalk28 G) =
      Erdos113Cycle28.tupleClosedWalk x.1.1 x.1.2 := by
  rfl

lemma relationBadHomCycleToBadClosedWalk_injective
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    Function.Injective (relationBadHomCycleToBadClosedWalk G R) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have hP := congrArg (fun z ↦ (z.1 : Encode28.ClosedWalk28 G)) hxy
  simp only [relationBadHomCycleToBadClosedWalk_walk] at hP
  have hread := congrArg (Erdos113Cycle28.closedWalkTuple G) hP
  simpa only [Erdos113Cycle28.closedWalkTuple_tupleClosedWalk] using hread

lemma card_homCycle28_le_relationFree_add_bad
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R] :
    Fintype.card (HomCycle28 G) ≤
      Fintype.card (RelationFreeHomCycle28 G R) +
        Fintype.card (Encode28.BadClosedWalk28 G R) := by
  have hpartition := Fintype.card_le_of_injective (relationPartition G R)
    (relationPartition_injective G R)
  rw [Fintype.card_sum] at hpartition
  have hbad := Fintype.card_le_of_injective
    (relationBadHomCycleToBadClosedWalk G R)
    (relationBadHomCycleToBadClosedWalk_injective G R)
  omega

lemma relationFreeCycles_half_closedWalkCount_of_numerics
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((G.neighborFinset y).filter (R u)).card : ℝ) ≤ 1)
    (t D : ℝ) (ht : 0 < t) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hnum : 28 * (D * t * (Conflict28.closedWalkCount G 26 : ℝ) +
        14 * t⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) ≤
      (Conflict28.closedWalkCount G 28 : ℝ) / 2) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) := by
  have hbad := Encode28.card_BadClosedWalk28_cast_le
    G R t D 1 ht (by norm_num) hdeg hsymm hlocal
  have hcard := card_homCycle28_le_relationFree_add_bad G R
  rw [card_homCycle28_eq_closedWalkCount G] at hcard
  have hcardR : (Conflict28.closedWalkCount G 28 : ℝ) ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) +
        (Fintype.card (Encode28.BadClosedWalk28 G R) : ℝ) := by
    exact_mod_cast hcard
  linarith

lemma genuineCycles_card_lower_of_bad_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : ℝ)
    (hbad : (Fintype.card
      (Encode28.BadClosedWalk28 G (fun u v ↦ u = v)) : ℝ) ≤ B) :
    (Conflict28.closedWalkCount G 28 : ℝ) - B ≤
      ((genuineCycles G 28).card : ℝ) := by
  have hcard := card_homCycle28_le_genuine_add_bad G
  rw [card_homCycle28_eq_closedWalkCount G] at hcard
  have hcardR : (Conflict28.closedWalkCount G 28 : ℝ) ≤
      ((genuineCycles G 28).card : ℝ) +
        (Fintype.card
          (Encode28.BadClosedWalk28 G (fun u v ↦ u = v)) : ℝ) := by
    exact_mod_cast hcard
  linarith

lemma genuineCycles_half_closedWalkCount_of_numerics
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t D : ℝ) (ht : 0 < t) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D)
    (hnum : 28 * (D * t * (Conflict28.closedWalkCount G 26 : ℝ) +
        14 * t⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) ≤
      (Conflict28.closedWalkCount G 28 : ℝ) / 2) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      ((genuineCycles G 28).card : ℝ) := by
  have hbad := repeatedBadClosedWalk28_cast_le G t D ht hdeg
  have hlower := genuineCycles_card_lower_of_bad_bound G
    (28 * (D * t * (Conflict28.closedWalkCount G 26 : ℝ) +
      14 * t⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ))) hbad
  linarith

lemma closedWalkCount_26_interpolation_28
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Conflict28.closedWalkCount G 26 : ℝ) ≤
      (Fintype.card V : ℝ) ^ ((1 : ℝ) / 14) *
        (Conflict28.closedWalkCount G 28 : ℝ) ^ ((13 : ℝ) / 14) :=
  Erdos113Moments28.closedWalkCount_interpolation_28 G

lemma closedWalkCount_28_lower_of_minDegree
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℝ) (hd : 0 ≤ d) (hmin : ∀ x, d ≤ (G.degree x : ℝ)) :
    d ^ 28 ≤ (Conflict28.closedWalkCount G 28 : ℝ) := by
  simpa only [Conflict28.closedWalkCount, Conflict28.walkCount,
    Conflict.closedWalkCount, Conflict.walkCount] using
    Lower.closedWalkCount_lower_of_minDegree G d hd hmin 14

lemma closedWalkCount_28_lower_bipartite
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (d : Bool → ℝ)
    (hd : ∀ b, 0 ≤ d b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hmin : ∀ x, d (side x) ≤ (G.degree x : ℝ)) :
    (d false * d true) ^ 14 ≤
      (Conflict28.closedWalkCount G 28 : ℝ) := by
  let q := (d false * d true) ^ 7
  have hq : 0 ≤ q := by
    dsimp [q]
    exact pow_nonneg (mul_nonneg (hd false) (hd true)) _
  have hmass (x : V) : q ≤ Lower.walkMass G 14 x := by
    have h := Erdos113LowerBipartite.walkMass_lower_bipartite
      G side d hd hcross hmin 14 x
    rw [show 14 = 2 * 7 by norm_num,
      Erdos113LowerBipartite.alternatingProduct_even] at h
    cases hx : side x <;> simpa [q, hx, mul_comm] using h
  have h := Erdos113LowerBipartite.closedWalkCount_lower_of_walkMass
    G q hq 14 hmass
  rw [show 2 * 14 = 28 by norm_num] at h
  calc
    (d false * d true) ^ 14 = q ^ 2 := by dsimp [q]; ring
    _ ≤ (Conflict.closedWalkCount G 28 : ℝ) := h
    _ = (Conflict28.closedWalkCount G 28 : ℝ) := rfl

lemma relationFreeCycles_half_closedWalkCount_of_side_numerics
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (side : V → Bool) (t D : Bool → ℝ)
    (ht : ∀ b, 0 < t b) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdegree : ∀ x, (G.degree x : ℝ) ≤ D (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((G.neighborFinset y).filter (R u)).card : ℝ) ≤ 1)
    (hnum : 28 * ∑ b : Bool,
        (D b * t b * (Conflict28.closedWalkCount G 26 : ℝ) +
          14 * (t b)⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) ≤
      (Conflict28.closedWalkCount G 28 : ℝ) / 2) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) := by
  let s : Bool → ℝ := fun _ ↦ 1
  have hbad := Erdos113Sides28.card_BadClosedWalk28_side_cast_le
    G R side t D s ht hD (fun _ ↦ by norm_num) hcross hdegree hsymm
      (fun u y ↦ by simpa [s] using hlocal u y)
  have hcard := card_homCycle28_le_relationFree_add_bad G R
  rw [card_homCycle28_eq_closedWalkCount G] at hcard
  have hcardR : (Conflict28.closedWalkCount G 28 : ℝ) ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) +
        (Fintype.card (Encode28.BadClosedWalk28 G R) : ℝ) := by
    exact_mod_cast hcard
  have hbad' : (Fintype.card (Encode28.BadClosedWalk28 G R) : ℝ) ≤
      28 * ∑ b : Bool,
        (D b * t b * (Conflict28.closedWalkCount G 26 : ℝ) +
          14 * (t b)⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) := by
    simpa [s] using hbad
  linarith

/-- A quantitative, polynomial-slack substitute for the fixed `C₂₈`
supersaturation input.  In an `L`-almost-regular graph, minimum degree much
larger than `L N^(1/14)` makes repeated-vertex closed walks a minority. -/
lemma relationFreeCycles_half_of_almostRegular
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((G.neighborFinset y).filter (R u)).card : ℝ) ≤ 1)
    (d L N : ℝ) (hN : N = Fintype.card V)
    (hd : 0 < d) (hL : 0 < L)
    (hmin : ∀ x, d ≤ (G.degree x : ℝ))
    (hmax : ∀ x, (G.degree x : ℝ) ≤ L * d)
    (hlarge : 175616 * L * N ^ ((1 : ℝ) / 14) ≤ d) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  let Q : ℝ := N ^ ((1 : ℝ) / 14)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNpos _
  let H : ℝ := Conflict28.closedWalkCount G 28
  let H' : ℝ := Conflict28.closedWalkCount G 26
  have hHlower : d ^ 28 ≤ H := by
    dsimp [H]
    exact closedWalkCount_28_lower_of_minDegree G d hd.le hmin
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < d ^ 28) hHlower
  have hinterp : H' ≤ Q * H ^ ((13 : ℝ) / 14) := by
    dsimp [H', Q, H]
    simpa [hN] using closedWalkCount_26_interpolation_28 G
  have hrootid :
      H ^ ((13 : ℝ) / 14) * H ^ ((1 : ℝ) / 14) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hdroot : d ^ 2 ≤ H ^ ((1 : ℝ) / 14) := by
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ d ^ 28) hHlower
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 14)
    convert hr using 1
    conv_rhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hd.le]
    norm_num
  have hHp : H' * d ^ 2 ≤ Q * H := by
    calc
      H' * d ^ 2 ≤ (Q * H ^ ((13 : ℝ) / 14)) * d ^ 2 := by
        gcongr
      _ ≤ (Q * H ^ ((13 : ℝ) / 14)) *
          H ^ ((1 : ℝ) / 14) := by
        gcongr
      _ = Q *
          (H ^ ((13 : ℝ) / 14) * H ^ ((1 : ℝ) / 14)) := by ring
      _ = Q * H := by rw [hrootid]
  let t : ℝ := d / (112 * L * Q)
  have ht : 0 < t := by dsimp [t]; positivity
  have htlarge : 1568 ≤ t := by
    apply (le_div_iff₀ (by positivity : 0 < 112 * L * Q)).2
    change 1568 * (112 * L * Q) ≤ d
    dsimp [Q]
    nlinarith
  have hfirst : 28 * ((L * d) * t * H') ≤ H / 4 := by
    have hden : 0 < 112 * L * Q := by positivity
    have hquot : (H' * d ^ 2) / Q ≤ H := by
      apply (div_le_iff₀ hQ).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hHp
    dsimp [t]
    have hid : 28 * ((L * d) * (d / (112 * L * Q)) * H') =
        ((H' * d ^ 2) / Q) / 4 := by
      field_simp
      <;> ring
    rw [hid]
    exact div_le_div_of_nonneg_right hquot (by norm_num)
  have htinv : t⁻¹ ≤ (1568 : ℝ)⁻¹ :=
    (inv_le_inv₀ ht (by norm_num)).2 htlarge
  have hsecond : 28 * (14 * t⁻¹ * H) ≤ H / 4 := by
    have hHnonneg : 0 ≤ H := hHpos.le
    calc
      28 * (14 * t⁻¹ * H) ≤
          28 * (14 * (1568 : ℝ)⁻¹ * H) := by
        gcongr
      _ = H / 4 := by norm_num; ring
  apply relationFreeCycles_half_closedWalkCount_of_numerics
    G R hsymm hlocal t (L * d) ht hmax
  calc
    28 * ((L * d) * t * (Conflict28.closedWalkCount G 26 : ℝ) +
        14 * t⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) =
        28 * ((L * d) * t * H') + 28 * (14 * t⁻¹ * H) := by
      dsimp [H, H']
      ring
    _ ≤ H / 4 + H / 4 := add_le_add hfirst hsecond
    _ = (Conflict28.closedWalkCount G 28 : ℝ) / 2 := by
      dsimp [H]
      ring

/-- Two-sided version used for a pruned bipartite degree cell.  The two
degree scales may be different; only the almost-regularity ratio on each
side enters the estimate. -/
lemma relationFreeCycles_half_of_bipartiteAlmostRegular
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : V → V → Prop) [DecidableRel R]
    (side : V → Bool) (d : Bool → ℝ) (L N : ℝ)
    (hN : N = Fintype.card V)
    (hd : ∀ b, 0 < d b) (hL : 0 < L)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hmin : ∀ x, d (side x) ≤ (G.degree x : ℝ))
    (hmax : ∀ x, (G.degree x : ℝ) ≤ L * d (side x))
    (hsymm : ∀ x y, R x y → R y x)
    (hlocal : ∀ u y,
      (((G.neighborFinset y).filter (R u)).card : ℝ) ≤ 1)
    (hlarge : ∀ b, 702464 * L * N ^ ((1 : ℝ) / 14) ≤ d b) :
    (Conflict28.closedWalkCount G 28 : ℝ) / 2 ≤
      (Fintype.card (RelationFreeHomCycle28 G R) : ℝ) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  let Q : ℝ := N ^ ((1 : ℝ) / 14)
  have hQ : 0 < Q := Real.rpow_pos_of_pos hNpos _
  let H : ℝ := Conflict28.closedWalkCount G 28
  let H' : ℝ := Conflict28.closedWalkCount G 26
  let p : ℝ := d false * d true
  have hp : 0 < p := by dsimp [p]; exact mul_pos (hd false) (hd true)
  have hHlower : p ^ 14 ≤ H := by
    dsimp [H, p]
    exact closedWalkCount_28_lower_bipartite
      G side d (fun b ↦ (hd b).le) hcross hmin
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity : 0 < p ^ 14) hHlower
  have hinterp : H' ≤ Q * H ^ ((13 : ℝ) / 14) := by
    dsimp [H', Q, H]
    simpa [hN] using closedWalkCount_26_interpolation_28 G
  have hrootid :
      H ^ ((13 : ℝ) / 14) * H ^ ((1 : ℝ) / 14) = H := by
    rw [← Real.rpow_add hHpos]
    norm_num
  have hproot : p ≤ H ^ ((1 : ℝ) / 14) := by
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ p ^ 14) hHlower
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 14)
    convert hr using 1
    conv_rhs => rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp.le]
    norm_num
  have hHp : H' * p ≤ Q * H := by
    calc
      H' * p ≤ (Q * H ^ ((13 : ℝ) / 14)) * p := by gcongr
      _ ≤ (Q * H ^ ((13 : ℝ) / 14)) *
          H ^ ((1 : ℝ) / 14) := by gcongr
      _ = Q *
          (H ^ ((13 : ℝ) / 14) * H ^ ((1 : ℝ) / 14)) := by ring
      _ = Q * H := by rw [hrootid]
  let t : Bool → ℝ := fun b ↦ p / (224 * (L * d b) * Q)
  have ht : ∀ b, 0 < t b := by
    intro b
    dsimp [t]
    exact div_pos hp (mul_pos (mul_pos (by norm_num) (mul_pos hL (hd b))) hQ)
  have htlarge : ∀ b, 3136 ≤ t b := by
    intro b
    apply (le_div_iff₀
      (mul_pos (mul_pos (by norm_num) (mul_pos hL (hd b))) hQ)).2
    change 3136 * (224 * (L * d b) * Q) ≤ p
    cases b
    · calc
        3136 * (224 * (L * d false) * Q) =
            d false * (702464 * L * Q) := by ring
        _ ≤ d false * d true :=
          mul_le_mul_of_nonneg_left (by simpa [Q] using hlarge true) (hd false).le
        _ = p := by rfl
    · calc
        3136 * (224 * (L * d true) * Q) =
            d true * (702464 * L * Q) := by ring
        _ ≤ d true * d false :=
          mul_le_mul_of_nonneg_left (by simpa [Q] using hlarge false) (hd true).le
        _ = p := by dsimp [p]; ring
  have hquot : (H' * p) / Q ≤ H := by
    apply (div_le_iff₀ hQ).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hHp
  have hfirst : ∀ b,
      (L * d b) * t b * H' ≤ H / 224 := by
    intro b
    have hid : (L * d b) * t b * H' = ((H' * p) / Q) / 224 := by
      dsimp [t]
      field_simp [ne_of_gt hL, ne_of_gt (hd b), ne_of_gt hQ]
    rw [hid]
    exact div_le_div_of_nonneg_right hquot (by norm_num)
  have htinv : ∀ b, (t b)⁻¹ ≤ (3136 : ℝ)⁻¹ := by
    intro b
    exact (inv_le_inv₀ (ht b) (by norm_num)).2 (htlarge b)
  have hsecond : ∀ b, 14 * (t b)⁻¹ * H ≤ H / 224 := by
    intro b
    calc
      14 * (t b)⁻¹ * H ≤ 14 * (3136 : ℝ)⁻¹ * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (htinv b) (by norm_num)) hHpos.le
      _ = H / 224 := by norm_num; ring
  apply relationFreeCycles_half_closedWalkCount_of_side_numerics
    G R side t (fun b ↦ L * d b) ht (fun b ↦ (mul_pos hL (hd b)).le)
    hcross hmax hsymm hlocal
  calc
    28 * ∑ b : Bool,
        ((L * d b) * t b * (Conflict28.closedWalkCount G 26 : ℝ) +
          14 * (t b)⁻¹ * (Conflict28.closedWalkCount G 28 : ℝ)) =
        28 * ∑ b : Bool,
          ((L * d b) * t b * H' + 14 * (t b)⁻¹ * H) := by
      rfl
    _ ≤ 28 * ∑ _b : Bool, (H / 224 + H / 224) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun b _ ↦ add_le_add (hfirst b) (hsecond b))
    _ = (Conflict28.closedWalkCount G 28 : ℝ) / 2 := by
      simp only [Fintype.sum_bool]
      dsimp [H]
      ring

end Erdos113Genuine28
