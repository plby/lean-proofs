/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostDirections
import ErdosProblems.Erdos136.McDiarmid

/-!
# Target-dependent random host partition

For the Erdős--Burr corollary we may choose the final host buckets after the
target graph is known.  We therefore only need simultaneous lower-tail
control of the finitely many bucket sizes and common-neighbour sets actually
used by that target.  This file develops the finite product-space sampling
lemma for a label distribution with a waste label.
-/

open scoped BigOperators
open Finset Real

namespace Erdos163
namespace HostPartition

attribute [local instance] Classical.propDecidable

noncomputable section

universe u

variable {P : Type u} [Fintype P] [DecidableEq P]

local instance optionMeasurableSpace : MeasurableSpace (Option P) := ⊤
local instance optionMeasurableSingletonClass :
    MeasurableSingletonClass (Option P) := ⟨fun _ => trivial⟩

/-- The one-coordinate distribution which gives label `p` mass `q p` and
puts the unused mass on `none`. -/
def labelWeight (q : P → ℝ) : Option P → ℝ
  | none => 1 - ∑ p, q p
  | some p => q p

theorem labelWeight_nonneg (q : P → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1) :
    ∀ z, 0 ≤ labelWeight q z := by
  intro z
  cases z with
  | none => simp [labelWeight, sub_nonneg.mpr hqsum]
  | some p => simpa [labelWeight] using hq p

theorem labelWeight_sum_one (q : P → ℝ) :
    ∑ z : Option P, labelWeight q z = 1 := by
  rw [Fintype.sum_option]
  simp [labelWeight]

/-- Number of active coordinates receiving one prescribed label. -/
def sampleCount {N : ℕ} (active : Fin N → Prop) (p : P)
    (x : Fin N → Option P) : ℝ :=
  ∑ i, if active i ∧ x i = some p then 1 else 0

/-- One coordinate has its prescribed label with exactly its assigned mass. -/
theorem weightedMean_label_eq {N : ℕ} (q : P → ℝ) (i : Fin N) (p : P) :
    Erdos136.McDiarmid.weightedMean (fun _ : Fin N => labelWeight q)
      (fun x : Fin N → Option P => if x i = some p then 1 else 0) = q p := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Erdos136.McDiarmid.weightedMean_succ]
          have hsection :
              Erdos136.McDiarmid.sectionAverage
                  (fun _ : Fin (N + 1) => labelWeight q)
                  (fun x : Fin (N + 1) → Option P =>
                    if x 0 = some p then (1 : ℝ) else 0) =
                fun _ : Fin N → Option P => q p := by
            funext y
            simp [Erdos136.McDiarmid.sectionAverage, labelWeight,
              Fintype.sum_option]
          rw [hsection]
          simp only [Erdos136.McDiarmid.weightedMean]
          rw [← Finset.sum_mul,
            Erdos136.McDiarmid.sum_productMass_eq_one N
              (fun _ : Fin N => labelWeight q)
              (fun _ => labelWeight_sum_one q)]
          simp
      | succ i =>
          rw [Erdos136.McDiarmid.weightedMean_succ]
          have hsection :
              Erdos136.McDiarmid.sectionAverage
                  (fun _ : Fin (N + 1) => labelWeight q)
                  (fun x : Fin (N + 1) → Option P =>
                    if x i.succ = some p then (1 : ℝ) else 0) =
                fun x : Fin N → Option P => if x i = some p then 1 else 0 := by
            funext y
            by_cases h : y i = some p
            · simpa only [Erdos136.McDiarmid.sectionAverage, Fin.cons_succ,
                h, if_pos, mul_one] using labelWeight_sum_one q
            · simp [Erdos136.McDiarmid.sectionAverage, h]
          rw [hsection]
          exact ih i

theorem weightedMean_sampleCount {N : ℕ} (q : P → ℝ)
    (active : Fin N → Prop) (p : P) :
    Erdos136.McDiarmid.weightedMean (fun _ : Fin N => labelWeight q)
        (sampleCount active p) =
      q p * ((Finset.univ.filter active).card : ℝ) := by
  simp only [Erdos136.McDiarmid.weightedMean, sampleCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ i : Fin N, ∑ x : Fin N → Option P,
        Erdos136.McDiarmid.productMass (fun _ : Fin N => labelWeight q) x *
          (if active i ∧ x i = some p then 1 else 0) =
      ∑ i : Fin N, if active i then q p else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hai : active i
        · simpa [hai, Erdos136.McDiarmid.weightedMean] using
            weightedMean_label_eq q i p
        · simp [hai]
    _ = q p * ((Finset.univ.filter active).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [mul_comm]

theorem sum_product_apply {N : ℕ} (h : Fin N → Option P → ℝ) :
    ∑ x : Fin N → Option P, ∏ i, h i (x i) = ∏ i, ∑ z, h i z := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Erdos136.McDiarmid.sum_fin_succ_eq]
      simp_rw [Fin.prod_univ_succ]
      simp_rw [Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum, ih]

def cylinder {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → Fin N) (p : ι → P) (x : Fin N → Option P) : Prop :=
  ∀ i, x (g i) = some (p i)

/-- Distinct requested coordinates have the expected product probability in
the finite label product space. -/
theorem weightedMean_cylinder_of_injective
    {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : P → ℝ) (g : ι → Fin N) (p : ι → P)
    (hg : Function.Injective g) :
    Erdos136.McDiarmid.weightedMean (fun _ : Fin N => labelWeight q)
        (fun x => if cylinder g p x then 1 else 0) = ∏ i, q (p i) := by
  let localWeight : Fin N → Option P → ℝ := fun v z =>
    labelWeight q z * (if ∀ i, g i = v → z = some (p i) then 1 else 0)
  have hindicator : ∀ x : Fin N → Option P,
      (if cylinder g p x then (1 : ℝ) else 0) =
        ∏ v, if ∀ i, g i = v → x v = some (p i) then 1 else 0 := by
    intro x
    by_cases hc : cylinder g p x
    · have hall : ∀ v, ∀ i, g i = v → x v = some (p i) := by
        intro v i hi
        simpa [← hi] using hc i
      rw [if_pos hc]
      symm
      apply Finset.prod_eq_one
      intro v hv
      rw [if_pos (hall v)]
    · have hnot : ¬(∀ v, ∀ i, g i = v → x v = some (p i)) := by
        intro hall
        apply hc
        intro i
        exact hall (g i) i rfl
      rw [if_neg hc]
      push Not at hnot
      obtain ⟨v, i, hgi, hne⟩ := hnot
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      rw [if_neg]
      exact fun hall => hne (hall i hgi)
  have hlocal : ∀ v,
      ∑ z : Option P, localWeight v z =
        if hv : v ∈ Finset.univ.image g then
          q (p (Classical.choose (Finset.mem_image.mp hv))) else 1 := by
    intro v
    by_cases hv : v ∈ Finset.univ.image g
    · obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hv
      have hconstraint : ∀ z : Option P,
          (∀ j, g j = v → z = some (p j)) ↔ z = some (p i) := by
        intro z
        constructor
        · intro h
          exact h i hgi
        · intro h j hgj
          have hij : j = i := hg (hgj.trans hgi.symm)
          simpa [hij] using h
      have hchoice : p (Classical.choose (Finset.mem_image.mp hv)) = p i := by
        have hc := (Classical.choose_spec (Finset.mem_image.mp hv)).2
        have : Classical.choose (Finset.mem_image.mp hv) = i :=
          hg (hc.trans hgi.symm)
        exact congrArg p this
      rw [dif_pos hv]
      simp_rw [localWeight, hconstraint]
      calc
        (∑ z : Option P, labelWeight q z * if z = some (p i) then 1 else 0) =
            q (p i) := by simp [labelWeight]
        _ = q (p (Classical.choose (Finset.mem_image.mp hv))) :=
          congrArg q hchoice.symm
    · have hnone : ∀ z : Option P, ∀ i, g i = v → z = some (p i) := by
        intro z i hgi
        exfalso
        apply hv
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hgi⟩
      rw [dif_neg hv]
      have hconstraint : ∀ z : Option P,
          ∀ i, g i = v → z = some (p i) := hnone
      simp_rw [localWeight, if_pos (hconstraint _), mul_one]
      exact labelWeight_sum_one q
  unfold Erdos136.McDiarmid.weightedMean Erdos136.McDiarmid.productMass
  simp_rw [hindicator]
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ x : Fin N → Option P, ∏ v, localWeight v (x v)) = _
  rw [sum_product_apply]
  simp_rw [hlocal]
  let e : ι ≃ (Finset.univ.image g : Finset (Fin N)) :=
    { toFun := fun i => ⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      invFun := fun v => Classical.choose (Finset.mem_image.mp v.property)
      left_inv := fun i => hg <| by
        simpa using (Classical.choose_spec
          (Finset.mem_image.mp (show g i ∈ Finset.univ.image g from
            Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))).2
      right_inv := fun v => Subtype.ext <| by
        simpa using (Classical.choose_spec (Finset.mem_image.mp v.property)).2 }
  calc
    ∏ v : Fin N, (if hv : v ∈ Finset.univ.image g then
        q (p (Classical.choose (Finset.mem_image.mp hv))) else 1) =
      ∏ v ∈ Finset.univ.image g, (if hv : v ∈ Finset.univ.image g then
        q (p (Classical.choose (Finset.mem_image.mp hv))) else 1) := by
          symm
          apply Finset.prod_subset (by simp)
          intro v hv hnot
          rw [dif_neg hnot]
    _ =
      ∏ v : (Finset.univ.image g : Finset (Fin N)),
        q (p (Classical.choose (Finset.mem_image.mp v.property))) := by
          simpa using
            (Finset.prod_bij
              (s := Finset.univ.image g)
              (t := (Finset.univ : Finset
                (Finset.univ.image g : Finset (Fin N))))
              (f := fun v => if hv : v ∈ Finset.univ.image g then
                q (p (Classical.choose (Finset.mem_image.mp hv))) else 1)
              (g := fun v : (Finset.univ.image g : Finset (Fin N)) =>
                q (p (Classical.choose (Finset.mem_image.mp v.property))))
              (fun v hv => ⟨v, hv⟩)
              (by simp)
              (by
                intro a₁ ha₁ a₂ ha₂ h
                exact congrArg Subtype.val h)
              (by
                intro b hb
                exact ⟨b.1, b.2, rfl⟩)
              (by
                intro v hv
                rw [dif_pos hv]))
    _ = ∏ i : ι, q (p i) := by
      symm
      apply Fintype.prod_equiv e
      intro i
      dsimp [e]
      congr 2
      apply hg
      simpa using (Classical.choose_spec
        (Finset.mem_image.mp (show g i ∈ Finset.univ.image g from
          Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))).2.symm

theorem sampleCount_oscillation {N : ℕ} (active : Fin N → Prop) (p : P)
    (i : Fin N) (x y : Fin N → Option P)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |sampleCount active p x - sampleCount active p y| ≤
      if active i then 1 else 0 := by
  let gx : Fin N → ℝ := fun j =>
    if active j ∧ x j = some p then 1 else 0
  let gy : Fin N → ℝ := fun j =>
    if active j ∧ y j = some p then 1 else 0
  have hrest :
      ∑ j ∈ (Finset.univ.erase i), gx j =
        ∑ j ∈ (Finset.univ.erase i), gy j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [gx, gy, hxy j hji]
  have hxsplit : sampleCount active p x =
      (∑ j ∈ (Finset.univ.erase i), gx j) + gx i := by
    simpa [sampleCount, gx] using
      (Finset.sum_erase_add (Finset.univ : Finset (Fin N)) gx
        (Finset.mem_univ i)).symm
  have hysplit : sampleCount active p y =
      (∑ j ∈ (Finset.univ.erase i), gy j) + gy i := by
    simpa [sampleCount, gy] using
      (Finset.sum_erase_add (Finset.univ : Finset (Fin N)) gy
        (Finset.mem_univ i)).symm
  rw [hxsplit, hysplit, hrest]
  by_cases hai : active i
  · by_cases hxi : x i = some p <;> by_cases hyi : y i = some p <;>
      simp [gx, gy, hai, hxi, hyi]
  · simp [gx, gy, hai]

theorem sum_active_bounds_sq {N : ℕ} (active : Fin N → Prop) :
    ∑ i : Fin N, (if active i then (1 : ℝ) else 0) ^ 2 =
      ((Finset.univ.filter active).card : ℝ) := by
  simp

/-- A strict union bound in the arbitrary finite label product space. -/
theorem exists_avoiding_of_eventMass_sum_lt_one
    {N : ℕ} {K : Type*} [Fintype K]
    (q : P → ℝ) (Bad : K → Set (Fin N → Option P))
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hfail :
      ∑ k : K, Erdos136.McDiarmid.eventMass
        (fun _ : Fin N => labelWeight q) (Bad k) < 1) :
    ∃ x : Fin N → Option P, ∀ k, x ∉ Bad k := by
  let w := fun _ : Fin N => labelWeight q
  have hw0 : ∀ i z, 0 ≤ w i z := fun _ => labelWeight_nonneg q hq hqsum
  have hw1 : ∀ i, ∑ z, w i z = 1 := fun _ => labelWeight_sum_one q
  have hunion : Erdos136.McDiarmid.eventMass w
      (⋃ k ∈ (Finset.univ : Finset K), Bad k) < 1 := by
    refine (Erdos136.McDiarmid.eventMass_biUnion_le_sum
      w hw0 Finset.univ Bad).trans_lt ?_
    simpa using hfail
  by_contra hnone
  push_neg at hnone
  have hall : (⋃ k ∈ (Finset.univ : Finset K), Bad k) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨k, hk⟩ := hnone x
    exact Set.mem_iUnion_of_mem k
      (Set.mem_iUnion_of_mem (Finset.mem_univ k) hk)
  rw [hall, Erdos136.McDiarmid.eventMass_univ w hw1] at hunion
  exact (lt_irrefl (1 : ℝ)) hunion

/-- Simultaneous one-half lower-tail sampling for any finite family of
subsets.  The displayed exponential sum is the only numerical hypothesis. -/
theorem exists_assignment_sampleCount_gt_half
    {N : ℕ} {K : Type*} [Fintype K]
    (q : P → ℝ) (active : K → Fin N → Prop) (bucket : K → P)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hfail :
      ∑ k : K, Real.exp
        (-2 * (q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ)) < 1) :
    ∃ x : Fin N → Option P, ∀ k,
      q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2 <
        sampleCount (active k) (bucket k) x := by
  let w := fun _ : Fin N => labelWeight q
  let Bad : K → Set (Fin N → Option P) := fun k =>
    {x | sampleCount (active k) (bucket k) x ≤
      q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2}
  have hw0 : ∀ i z, 0 ≤ w i z := fun _ => labelWeight_nonneg q hq hqsum
  have hw1 : ∀ i, ∑ z, w i z = 1 := fun _ => labelWeight_sum_one q
  have hmass : ∀ k, Erdos136.McDiarmid.eventMass w (Bad k) ≤
      Real.exp
        (-2 * (q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ)) := by
    intro k
    let b : Fin N → ℝ := fun i => if active k i then 1 else 0
    have hmean := weightedMean_sampleCount q (active k) (bucket k)
    have hset : Bad k =
        {x | sampleCount (active k) (bucket k) x ≤
          Erdos136.McDiarmid.weightedMean w
              (sampleCount (active k) (bucket k)) -
            q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2} := by
      ext x
      simp only [Bad, Set.mem_setOf_eq]
      rw [hmean]
      ring_nf
    rw [hset]
    have hmc := Erdos136.McDiarmid.mcdiarmid_lower_all N w
      (sampleCount (active k) (bucket k)) b hw0 hw1
      (fun i => by dsimp [b]; split <;> norm_num)
      (fun i x y hxy => sampleCount_oscillation (active k) (bucket k) i x y hxy)
      (q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2)
      (div_nonneg (mul_nonneg (hq _) (by positivity)) (by norm_num))
    rw [sum_active_bounds_sq] at hmc
    exact hmc
  have hsum : ∑ k : K, Erdos136.McDiarmid.eventMass w (Bad k) < 1 := by
    exact (Finset.sum_le_sum fun k _ => hmass k).trans_lt hfail
  obtain ⟨x, hx⟩ := exists_avoiding_of_eventMass_sum_lt_one q Bad hq hqsum hsum
  refine ⟨x, ?_⟩
  intro k
  exact lt_of_not_ge (hx k)

/-- Simultaneous lower-tail bucket estimates and upper-tail estimates for an
arbitrary finite family of statistics on the same random labelling.  This is
the finite union-bound form used for Lee's two properties (P1) and (P2). -/
theorem exists_assignment_lower_and_upper
    {N : ℕ} {K L : Type*} [Fintype K] [Fintype L]
    (q : P → ℝ) (active : K → Fin N → Prop) (bucket : K → P)
    (f : L → (Fin N → Option P) → ℝ) (b : L → Fin N → ℝ)
    (t : L → ℝ)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hb : ∀ l i, 0 ≤ b l i)
    (hbd : ∀ l i (x y : Fin N → Option P),
      (∀ j, j ≠ i → x j = y j) → |f l x - f l y| ≤ b l i)
    (ht : ∀ l, 0 ≤ t l)
    (hfail :
      (∑ k : K, Real.exp
        (-2 * (q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ))) +
      ∑ l : L, Real.exp
        (-2 * (t l) ^ 2 / ∑ i : Fin N, (b l i) ^ 2) < 1) :
    ∃ x : Fin N → Option P,
      (∀ k, q (bucket k) *
          ((Finset.univ.filter (active k)).card : ℝ) / 2 <
        sampleCount (active k) (bucket k) x) ∧
      ∀ l, f l x <
        Erdos136.McDiarmid.weightedMean
          (fun _ : Fin N => labelWeight q) (f l) + t l := by
  let w := fun _ : Fin N => labelWeight q
  let Bad : Sum K L → Set (Fin N → Option P)
    | Sum.inl k => {x | sampleCount (active k) (bucket k) x ≤
        q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2}
    | Sum.inr l => {x |
        Erdos136.McDiarmid.weightedMean w (f l) + t l ≤ f l x}
  have hw0 : ∀ i z, 0 ≤ w i z := fun _ => labelWeight_nonneg q hq hqsum
  have hw1 : ∀ i, ∑ z, w i z = 1 := fun _ => labelWeight_sum_one q
  have hlower : ∀ k, Erdos136.McDiarmid.eventMass w (Bad (Sum.inl k)) ≤
      Real.exp
        (-2 * (q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ)) := by
    intro k
    let bk : Fin N → ℝ := fun i => if active k i then 1 else 0
    have hmean := weightedMean_sampleCount q (active k) (bucket k)
    have hset : Bad (Sum.inl k) =
        {x | sampleCount (active k) (bucket k) x ≤
          Erdos136.McDiarmid.weightedMean w
              (sampleCount (active k) (bucket k)) -
            q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2} := by
      ext x
      simp only [Bad, Set.mem_setOf_eq]
      rw [hmean]
      ring_nf
    rw [hset]
    have hmc := Erdos136.McDiarmid.mcdiarmid_lower_all N w
      (sampleCount (active k) (bucket k)) bk hw0 hw1
      (fun i => by dsimp [bk]; split <;> norm_num)
      (fun i x y hxy => sampleCount_oscillation (active k) (bucket k) i x y hxy)
      (q (bucket k) * ((Finset.univ.filter (active k)).card : ℝ) / 2)
      (div_nonneg (mul_nonneg (hq _) (by positivity)) (by norm_num))
    rw [sum_active_bounds_sq] at hmc
    exact hmc
  have hupper : ∀ l, Erdos136.McDiarmid.eventMass w (Bad (Sum.inr l)) ≤
      Real.exp (-2 * (t l) ^ 2 / ∑ i : Fin N, (b l i) ^ 2) := by
    intro l
    exact Erdos136.McDiarmid.mcdiarmid_upper_all N w (f l) (b l)
      hw0 hw1 (hb l) (hbd l) (t l) (ht l)
  have hsum : ∑ z : Sum K L,
      Erdos136.McDiarmid.eventMass w (Bad z) < 1 := by
    rw [Fintype.sum_sum_type]
    exact (add_le_add
      (Finset.sum_le_sum fun k _ => hlower k)
      (Finset.sum_le_sum fun l _ => hupper l)).trans_lt hfail
  obtain ⟨x, hx⟩ := exists_avoiding_of_eventMass_sum_lt_one q Bad hq hqsum hsum
  refine ⟨x, ?_, ?_⟩
  · intro k
    exact lt_of_not_ge (hx (Sum.inl k))
  · intro l
    exact lt_of_not_ge (hx (Sum.inr l))

/-! ## Deterministic conversion of lower-tail events into moment bounds -/

theorem defect_le_sentinel {N θ : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] {ι : Type*} [Fintype ι]
    (g : ι → Fin N) (T : Finset (Fin N)) :
    FiniteDefect.defect G θ g T ≤ (θ : ℝ) * (N + 1) := by
  unfold FiniteDefect.defect
  dsimp
  split_ifs with hsmall hzero
  · positivity
  · simp
  · have hcard : (1 : ℝ) ≤
        (FiniteDefect.commonNeighbors G g T).card := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
    have hdiv : (θ : ℝ) /
        (FiniteDefect.commonNeighbors G g T).card ≤ θ := by
      exact div_le_self (by positivity) hcard
    exact hdiv.trans (le_mul_of_one_le_right (by positivity) (by norm_num))

theorem defectPower_le_sentinel_pow {N θ s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (g : ι → Fin N) (T : Finset (Fin N)) :
    FiniteDefect.defectPower G θ g T s ≤
      ((θ : ℝ) * (N + 1)) ^ s := by
  unfold FiniteDefect.defectPower
  split_ifs
  · positivity
  · exact pow_le_pow_left₀ (FiniteDefect.defect_nonneg G θ g T)
      (defect_le_sentinel G g T) s

/-- If every tuple which was nondefective before restriction remains
nondefective, its new defect power is bounded by the universal finite
sentinel times its old defect power. -/
theorem defectPower_restrict_le {N θ θ' s : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (U T : Finset (Fin N))
    (hgood : θ ≤ (FiniteDefect.commonNeighbors G g U).card →
      θ' ≤ (FiniteDefect.commonNeighbors G g T).card) :
    FiniteDefect.defectPower G θ' g T s ≤
      (((θ' : ℝ) * (N + 1)) ^ s) *
        FiniteDefect.defectPower G θ g U s := by
  by_cases hold : FiniteDefect.defect G θ g U = 0
  · have hbase : θ ≤ (FiniteDefect.commonNeighbors G g U).card := by
      by_contra hnot
      have hlt : (FiniteDefect.commonNeighbors G g U).card < θ :=
        Nat.lt_of_not_ge hnot
      by_cases hz : (FiniteDefect.commonNeighbors G g U).card = 0
      · have hθ : 0 < θ := hz ▸ hlt
        have hempty : FiniteDefect.commonNeighbors G g U = ∅ :=
          Finset.card_eq_zero.mp hz
        rw [FiniteDefect.defect_eq_sentinel_of_empty G hθ hempty] at hold
        have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
        have hpos : (0 : ℝ) <
            (θ : ℝ) * (Fintype.card (Fin N) + 1) := by positivity
        exact hpos.ne' hold
      · rw [FiniteDefect.defect_eq_div_of_pos_card_lt G
            (Nat.pos_of_ne_zero hz) hlt] at hold
        have hθ : (0 : ℝ) < θ := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hlt
        have hm : (0 : ℝ) < (FiniteDefect.commonNeighbors G g U).card := by
          exact_mod_cast Nat.pos_of_ne_zero hz
        exact (div_pos hθ hm).ne' hold
    have hnew := FiniteDefect.defect_eq_zero_of_threshold_le G (hgood hbase)
    simp [FiniteDefect.defectPower, hold, hnew]
  · have hone : 1 ≤ FiniteDefect.defectPower G θ g U s := by
      unfold FiniteDefect.defectPower
      rw [if_neg hold]
      exact one_le_pow₀ (FiniteDefect.one_le_defect_of_ne_zero G hold)
    calc
      FiniteDefect.defectPower G θ' g T s ≤
          ((θ' : ℝ) * (N + 1)) ^ s := defectPower_le_sentinel_pow G g T
      _ ≤ ((θ' : ℝ) * (N + 1)) ^ s *
          FiniteDefect.defectPower G θ g U s :=
        le_mul_of_one_le_right (by positivity) hone

/-- Proportional retention compares the new defect directly with the old
one.  The positive old common-neighbour hypothesis removes the finite
sentinel case. -/
theorem defectPower_restrict_le_of_proportional
    {N θ θ' s : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (g : ι → Fin N)
    (U T : Finset (Fin N)) (q : ℝ) (hq : 0 < q)
    (holdPos : 0 < (FiniteDefect.commonNeighbors G g U).card)
    (hθ : (θ' : ℝ) ≤ q * θ / 2)
    (hretain : q * ((FiniteDefect.commonNeighbors G g U).card : ℝ) / 2 <
      ((FiniteDefect.commonNeighbors G g T).card : ℝ)) :
    FiniteDefect.defectPower G θ' g T s ≤
      FiniteDefect.defectPower G θ g U s := by
  let m := (FiniteDefect.commonNeighbors G g U).card
  let m' := (FiniteDefect.commonNeighbors G g T).card
  have hmR : (0 : ℝ) < m := by exact_mod_cast holdPos
  have hm'R : (0 : ℝ) < m' := by
    have : 0 < q * (m : ℝ) / 2 := by positivity
    exact this.trans hretain
  have hm'Pos : 0 < m' := by exact_mod_cast hm'R
  by_cases holdLarge : θ ≤ m
  · have hnewLarge : θ' ≤ m' := by
      have hmean : q * (θ : ℝ) / 2 ≤ q * (m : ℝ) / 2 := by
        gcongr
      exact_mod_cast (hθ.trans_lt (hmean.trans_lt hretain)).le
    simp [FiniteDefect.defectPower,
      FiniteDefect.defect_eq_zero_of_threshold_le G holdLarge,
      FiniteDefect.defect_eq_zero_of_threshold_le G hnewLarge]
  · have holdSmall : m < θ := Nat.lt_of_not_ge holdLarge
    have hθPos : (0 : ℝ) < θ := by exact_mod_cast holdPos.trans_le holdSmall.le
    by_cases hnewLarge : θ' ≤ m'
    · have hnewZero := FiniteDefect.defect_eq_zero_of_threshold_le G hnewLarge
      rw [FiniteDefect.defectPower, if_pos hnewZero]
      exact FiniteDefect.defectPower_nonneg G θ g U s
    · have hnewSmall : m' < θ' := Nat.lt_of_not_ge hnewLarge
      have holdDef := FiniteDefect.defect_eq_div_of_pos_card_lt G holdPos holdSmall
      have hnewDef := FiniteDefect.defect_eq_div_of_pos_card_lt G hm'Pos hnewSmall
      have hcross : (θ' : ℝ) * m ≤ (θ : ℝ) * m' := by
        have hleft : (θ' : ℝ) * m ≤
            (q * θ / 2) * m :=
          mul_le_mul_of_nonneg_right hθ (by positivity)
        have hright : (q * θ / 2) * m < (θ : ℝ) * m' := by
          have := mul_lt_mul_of_pos_left hretain hθPos
          nlinarith
        exact hleft.trans hright.le
      have hdiv : (θ' : ℝ) / m' ≤ (θ : ℝ) / m := by
        rw [div_le_div_iff₀ hm'R hmR]
        simpa [mul_comm] using hcross
      have hθ'Pos : (0 : ℝ) < θ' := by
        exact_mod_cast hm'Pos.trans_le hnewSmall.le
      have hnewNe : FiniteDefect.defect G θ' g T ≠ 0 := by
        rw [hnewDef]
        exact (div_pos hθ'Pos hm'R).ne'
      have holdNe : FiniteDefect.defect G θ g U ≠ 0 := by
        rw [holdDef]
        exact (div_pos hθPos hmR).ne'
      unfold FiniteDefect.defectPower
      rw [if_neg hnewNe, if_neg holdNe, hnewDef, holdDef]
      exact pow_le_pow_left₀ (by positivity) hdiv s

/-- Coordinate restriction after proportional target retention loses only
the product normalization factor. -/
theorem familyMoment_restrict_proportional_le
    {N θ θ' s K : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B A : ι → Finset (Fin N)} (hB : ∀ i, (B i).Nonempty)
    (hBA : ∀ i, B i ⊆ A i)
    (hcard : ∀ i, (A i).card ≤ K * (B i).card)
    (U T : Finset (Fin N)) (q : ℝ) (hq : 0 < q)
    (hθ : (θ' : ℝ) ≤ q * θ / 2)
    (holdPos : ∀ g ∈ FiniteDefect.familyTuples B,
      0 < (FiniteDefect.commonNeighbors G g U).card)
    (hretain : ∀ g ∈ FiniteDefect.familyTuples B,
      q * ((FiniteDefect.commonNeighbors G g U).card : ℝ) / 2 <
        ((FiniteDefect.commonNeighbors G g T).card : ℝ)) :
    FiniteDefect.familyMoment G θ' s B T ≤
      (K : ℝ) ^ Fintype.card ι *
        FiniteDefect.familyMoment G θ s A U := by
  have hchange : FiniteDefect.familyMoment G θ' s B T ≤
      FiniteDefect.familyMoment G θ s B U := by
    unfold FiniteDefect.familyMoment
    rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
    apply div_le_div_of_nonneg_right
    · apply Finset.sum_le_sum
      intro g hg
      exact defectPower_restrict_le_of_proportional G g U T q hq
        (holdPos g hg) hθ (hretain g hg)
    · positivity
  exact hchange.trans (HostTools.familyMoment_le_pow_mul_of_subset G θ s K
    hB hBA hcard U)

/-- Moment restriction with an explicit coordinate-normalization loss. -/
theorem familyMoment_restrict_le
    {N θ θ' s K : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B A : ι → Finset (Fin N)} (hB : ∀ i, (B i).Nonempty)
    (hBA : ∀ i, B i ⊆ A i)
    (hcard : ∀ i, (A i).card ≤ K * (B i).card)
    (U T : Finset (Fin N))
    (hgood : ∀ g ∈ FiniteDefect.familyTuples B,
      θ ≤ (FiniteDefect.commonNeighbors G g U).card →
        θ' ≤ (FiniteDefect.commonNeighbors G g T).card) :
    FiniteDefect.familyMoment G θ' s B T ≤
      (K : ℝ) ^ Fintype.card ι *
        (((θ' : ℝ) * (N + 1)) ^ s) *
          FiniteDefect.familyMoment G θ s A U := by
  have hchange : FiniteDefect.familyMoment G θ' s B T ≤
      (((θ' : ℝ) * (N + 1)) ^ s) *
        FiniteDefect.familyMoment G θ s B U := by
    unfold FiniteDefect.familyMoment
    rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
    calc
      (∑ g ∈ FiniteDefect.familyTuples B,
            FiniteDefect.defectPower G θ' g T s) /
          (FiniteDefect.familyTuples B).card ≤
        (∑ g ∈ FiniteDefect.familyTuples B,
            (((θ' : ℝ) * (N + 1)) ^ s) *
              FiniteDefect.defectPower G θ g U s) /
          (FiniteDefect.familyTuples B).card := by
        apply div_le_div_of_nonneg_right
        · apply Finset.sum_le_sum
          intro g hg
          exact defectPower_restrict_le G g U T (hgood g hg)
        · positivity
      _ = (((θ' : ℝ) * (N + 1)) ^ s) *
          ((∑ g ∈ FiniteDefect.familyTuples B,
              FiniteDefect.defectPower G θ g U s) /
            (FiniteDefect.familyTuples B).card) := by
        rw [show (∑ g ∈ FiniteDefect.familyTuples B,
              (((θ' : ℝ) * (N + 1)) ^ s) *
                FiniteDefect.defectPower G θ g U s) =
            (((θ' : ℝ) * (N + 1)) ^ s) *
              ∑ g ∈ FiniteDefect.familyTuples B,
                FiniteDefect.defectPower G θ g U s by
          simp only [Finset.mul_sum]]
        ring
  have hcoord := HostTools.familyMoment_le_pow_mul_of_subset G θ s K
    hB hBA hcard U
  calc
    FiniteDefect.familyMoment G θ' s B T ≤
        (((θ' : ℝ) * (N + 1)) ^ s) *
          FiniteDefect.familyMoment G θ s B U := hchange
    _ ≤ (((θ' : ℝ) * (N + 1)) ^ s) *
        ((K : ℝ) ^ Fintype.card ι *
          FiniteDefect.familyMoment G θ s A U) :=
      mul_le_mul_of_nonneg_left hcoord (by positivity)
    _ = (K : ℝ) ^ Fintype.card ι *
        (((θ' : ℝ) * (N + 1)) ^ s) *
          FiniteDefect.familyMoment G θ s A U := by ring

/-- A constant-coordinate family moment depends only on the cardinality of
its finite index type. -/
theorem familyMoment_const_eq_moment_card
    {N θ s : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A T : Finset (Fin N)) :
    FiniteDefect.familyMoment G θ s (fun _ : ι => A) T =
      FiniteDefect.moment G θ s (fun _ : Fin (Fintype.card ι) => A) T := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → Fin N) ≃ (ι → Fin N) :=
    Equiv.piCongrLeft (fun _ : ι => Fin N) e
  unfold FiniteDefect.familyMoment FiniteDefect.moment
  apply Finset.expect_equiv E.symm
  · intro g
    rw [FiniteDefect.mem_familyTuples, FiniteDefect.mem_tuples]
    constructor
    · intro hg i
      simpa [E] using hg (e i)
    · intro hg i
      simpa [E] using hg (e.symm i)
  · intro g hg
    have hcommon : FiniteDefect.commonNeighbors G g T =
        FiniteDefect.commonNeighbors G (E.symm g) T := by
      ext v
      simp only [FiniteDefect.commonNeighbors, Defect.mem_commonNeighbors]
      constructor
      · rintro ⟨hv, hall⟩
        refine ⟨hv, fun i => ?_⟩
        simpa [E] using hall (e i)
      · rintro ⟨hv, hall⟩
        refine ⟨hv, fun j => ?_⟩
        simpa [E] using hall (e.symm j)
    unfold FiniteDefect.defectPower FiniteDefect.defect
    simp only [hcommon]

/-- A sufficiently small family moment excludes an empty common
neighbourhood for every tuple in the product. -/
theorem commonNeighbors_nonempty_of_familyMoment
    {N θ s : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset (Fin N)) (T : Finset (Fin N)) {μ : ℝ}
    (hθ : 0 < θ) (hμ : 0 ≤ μ)
    (hmoment : FiniteDefect.familyMoment G θ s A T ≤ μ)
    (hsmall : ((FiniteDefect.familyTuples A).card : ℝ) * μ <
      ((θ : ℝ) * (N + 1)) ^ s)
    (g : ι → Fin N) (hg : g ∈ FiniteDefect.familyTuples A) :
    (FiniteDefect.commonNeighbors G g T).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hdef := FiniteDefect.defect_eq_sentinel_of_empty G hθ hempty
  have hpower : FiniteDefect.defectPower G θ g T s =
      ((θ : ℝ) * (N + 1)) ^ s := by
    unfold FiniteDefect.defectPower
    rw [if_neg (by rw [hdef]; positivity), hdef]
    simp
  have hsingle : FiniteDefect.defectPower G θ g T s ≤
      HostTools.rawFamilyMoment G θ s A T := by
    unfold HostTools.rawFamilyMoment
    exact Finset.single_le_sum
      (fun z hz => FiniteDefect.defectPower_nonneg G θ z T s) hg
  have hraw : HostTools.rawFamilyMoment G θ s A T ≤
      ((FiniteDefect.familyTuples A).card : ℝ) * μ := by
    rw [HostTools.rawFamilyMoment_eq_card_mul_moment]
    exact mul_le_mul_of_nonneg_left hmoment (by positivity)
  rw [hpower] at hsingle
  exact (not_lt_of_ge (hsingle.trans hraw)) hsmall

/-! ## Reading a label assignment as disjoint host buckets -/

def bucket {N : ℕ} {J : Type*} [DecidableEq J]
    (A : J → Finset (Fin N)) (color : P → J)
    (x : Fin N → Option P) (p : P) : Finset (Fin N) :=
  (A (color p)).filter fun v => x v = some p

theorem bucket_subset {N : ℕ} {J : Type*} [DecidableEq J]
    (A : J → Finset (Fin N)) (color : P → J)
    (x : Fin N → Option P) (p : P) :
    bucket A color x p ⊆ A (color p) := by
  exact Finset.filter_subset _ _

theorem bucket_disjoint {N : ℕ} {J : Type*} [DecidableEq J]
    (A : J → Finset (Fin N)) (color : P → J)
    (x : Fin N → Option P) {{p p' : P}} (hpp' : p ≠ p') :
    Disjoint (bucket A color x p) (bucket A color x p') := by
  refine Finset.disjoint_left.mpr ?_
  intro v hv hv'
  have hp := (Finset.mem_filter.mp hv).2
  have hp' := (Finset.mem_filter.mp hv').2
  exact hpp' (Option.some.inj (hp.symm.trans hp'))

theorem sampleCount_eq_filter_card {N : ℕ} (active : Fin N → Prop)
    (x : Fin N → Option P) (p : P) :
    sampleCount active p x =
      (((Finset.univ : Finset (Fin N)).filter fun v =>
        active v ∧ x v = some p).card : ℝ) := by
  have hnat : (∑ v : Fin N,
      if active v ∧ x v = some p then 1 else 0 : ℕ) =
      ((Finset.univ : Finset (Fin N)).filter fun v =>
        active v ∧ x v = some p).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold sampleCount
  exact_mod_cast hnat

theorem sampleCount_mem_eq_card {N : ℕ} {J : Type*} [DecidableEq J]
    (A : J → Finset (Fin N)) (color : P → J)
    (x : Fin N → Option P) (p : P) :
    sampleCount (fun v => v ∈ A (color p)) p x =
      ((bucket A color x p).card : ℝ) := by
  rw [sampleCount_eq_filter_card]
  norm_cast
  apply congrArg Finset.card
  ext v
  simp [bucket]

theorem sampleCount_common_eq_card
    {N : ℕ} {J : Type*} [DecidableEq J]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : J → Finset (Fin N)) (color : P → J)
    (x : Fin N → Option P) (p : P)
    {ι : Type*} [Fintype ι] (g : ι → Fin N) :
    sampleCount
        (fun v => v ∈ FiniteDefect.commonNeighbors G g (A (color p))) p x =
      ((FiniteDefect.commonNeighbors G g (bucket A color x p)).card : ℝ) := by
  rw [sampleCount_eq_filter_card]
  norm_cast
  apply congrArg Finset.card
  ext v
  simp [bucket, FiniteDefect.commonNeighbors, Defect.commonNeighbors,
    and_comm, and_left_comm, and_assoc]

/-- Test indices for simultaneous bucket-size and common-neighbour lower
tails.  A common-neighbour test stores a tuple from its prescribed ambient
coordinate product. -/
abbrev SamplingTest
    {N : ℕ} (X : Type*) [Fintype X]
    (coord : X → Type*) [∀ a, Fintype (coord a)] [∀ a, DecidableEq (coord a)]
    (base : ∀ a, coord a → Finset (Fin N)) :=
  Sum P (Σ a : X, {g // g ∈ FiniteDefect.familyTuples (base a)})

/-- A target-dependent label assignment simultaneously retains half the
mean size of every host bucket and half the mean common neighbourhood of
every requested ambient tuple. -/
theorem exists_labeling_good
    {N : ℕ} {J X : Type*} [Fintype X] [DecidableEq J]
    (coord : X → Type*) [∀ a, Fintype (coord a)] [∀ a, DecidableEq (coord a)]
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A : J → Finset (Fin N)) (color : P → J) (rootPart : X → P)
    (base : ∀ a, coord a → Finset (Fin N))
    (q : P → ℝ) (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hfail :
      let active : SamplingTest (P := P) X coord base → Fin N → Prop
        | Sum.inl p => fun v => v ∈ A (color p)
        | Sum.inr z => fun v => v ∈
            FiniteDefect.commonNeighbors G z.2.1 (A (color (rootPart z.1)))
      let which : SamplingTest (P := P) X coord base → P
        | Sum.inl p => p
        | Sum.inr z => rootPart z.1
      ∑ k, Real.exp
        (-2 * (q (which k) * ((Finset.univ.filter (active k)).card : ℝ) / 2) ^ 2 /
          ((Finset.univ.filter (active k)).card : ℝ)) < 1) :
    ∃ x : Fin N → Option P,
      (∀ p, q p * ((A (color p)).card : ℝ) / 2 <
        ((bucket A color x p).card : ℝ)) ∧
      (∀ a (g : coord a → Fin N),
        g ∈ FiniteDefect.familyTuples (base a) →
        q (rootPart a) *
            ((FiniteDefect.commonNeighbors G g
              (A (color (rootPart a)))).card : ℝ) / 2 <
          ((FiniteDefect.commonNeighbors G g
            (bucket A color x (rootPart a))).card : ℝ)) := by
  let active : SamplingTest (P := P) X coord base → Fin N → Prop
    | Sum.inl p => fun v => v ∈ A (color p)
    | Sum.inr z => fun v => v ∈
        FiniteDefect.commonNeighbors G z.2.1 (A (color (rootPart z.1)))
  let which : SamplingTest (P := P) X coord base → P
    | Sum.inl p => p
    | Sum.inr z => rootPart z.1
  obtain ⟨x, hx⟩ := exists_assignment_sampleCount_gt_half q active which
    hq hqsum (by simpa [active, which] using hfail)
  refine ⟨x, ?_, ?_⟩
  · intro p
    have hp := hx (Sum.inl p)
    simpa [active, which, sampleCount_mem_eq_card] using hp
  · intro a g hg
    let z : Σ a : X, {g // g ∈ FiniteDefect.familyTuples (base a)} :=
      ⟨a, ⟨g, hg⟩⟩
    have hz := hx (Sum.inr z)
    simpa [active, which, z, sampleCount_common_eq_card] using hz

end
end HostPartition
end Erdos163
