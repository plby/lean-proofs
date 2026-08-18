/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterCenterBadSet

/-!
# Haar-random center groups hit every bounded progression

For every progression we reserve `hunterY D` independent groups, each of
size `hunterGroupSize D`.  A group fails precisely when all its coordinates
miss the positive orbit-kernel set.  Product Haar measure makes the failure
probability an exact power.
-/

open Set Function MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Erdos984

noncomputable section

/-- The center tuples whose entire group `y` misses the positive set for `P`. -/
def hunterGroupMissSet (D : ℕ) (theta : UnitAddTorus (Fin D))
    (P : BoundedAP (hunterN D) (hunterX D)) (y : Fin (hunterY D)) :
    Set ((Fin (hunterY D) × Fin (hunterGroupSize D)) →
      UnitAddTorus (Fin D)) :=
  {center | ∀ l, center (y, l) ∉
    hunterOrbitPositiveSet D theta P.start P.step}

lemma measurableSet_hunterGroupMissSet
    (D : ℕ) (theta : UnitAddTorus (Fin D))
    (P : BoundedAP (hunterN D) (hunterX D)) (y : Fin (hunterY D)) :
    MeasurableSet (hunterGroupMissSet D theta P y) := by
  rw [show hunterGroupMissSet D theta P y =
      ⋂ l : Fin (hunterGroupSize D),
        (fun center : (Fin (hunterY D) × Fin (hunterGroupSize D)) →
          UnitAddTorus (Fin D) ↦ center (y, l)) ⁻¹'
            (hunterOrbitPositiveSet D theta P.start P.step)ᶜ by
    ext center
    simp [hunterGroupMissSet]]
  apply MeasurableSet.iInter
  intro l
  exact (measurableSet_hunterOrbitPositiveSet D theta P.start P.step).compl.preimage
    (measurable_pi_apply (y, l))

/-- Exact product formula for one group-miss event. -/
lemma volume_hunterGroupMissSet
    (D : ℕ) (theta : UnitAddTorus (Fin D))
    (P : BoundedAP (hunterN D) (hunterX D)) (y : Fin (hunterY D)) :
    volume (hunterGroupMissSet D theta P y) =
      (volume (hunterOrbitPositiveSet D theta P.start P.step)ᶜ) ^
        hunterGroupSize D := by
  let A := hunterOrbitPositiveSet D theta P.start P.step
  let B : (Fin (hunterY D) × Fin (hunterGroupSize D)) →
      Set (UnitAddTorus (Fin D)) := fun i ↦
    if i.1 = y then Aᶜ else Set.univ
  have hset : hunterGroupMissSet D theta P y = Set.univ.pi B := by
    ext center
    simp only [hunterGroupMissSet, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_const, B]
    constructor
    · intro h i
      rcases i with ⟨i, l⟩
      split_ifs with hi
      · have hi' : i = y := by simpa using hi
        subst i
        exact h l
      · simp
    · intro h l
      have := h (y, l)
      simpa [A] using this
  rw [hset, MeasureTheory.volume_pi_pi]
  simp_rw [B]
  rw [Fintype.prod_prod_type]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_eq_single y]
  · simp [A, volume_unitAddTorus_univ (D := Fin D)]
  · intro z _hz hzy
    simp [hzy, volume_unitAddTorus_univ (D := Fin D)]
  · simp

/-- A set of Haar probability at least `p` is missed by `L` independent
samples with probability at most `exp (-pL)`. -/
lemma volume_pi_groupMiss_le_exp
    {D : Type*} [Fintype D] {Y L : ℕ}
    (A : Set (UnitAddTorus D)) (hA : MeasurableSet A)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ volume.real A) (y : Fin Y) :
    volume {center : (Fin Y × Fin L) → UnitAddTorus D |
        ∀ l, center (y, l) ∉ A} ≤
      ENNReal.ofReal (Real.exp (-p * L)) := by
  have hvolume : volume {center : (Fin Y × Fin L) → UnitAddTorus D |
      ∀ l, center (y, l) ∉ A} = (volume Aᶜ) ^ L := by
    let B : (Fin Y × Fin L) → Set (UnitAddTorus D) := fun i ↦
      if i.1 = y then Aᶜ else Set.univ
    have hset : {center : (Fin Y × Fin L) → UnitAddTorus D |
        ∀ l, center (y, l) ∉ A} = Set.univ.pi B := by
      ext center
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
        forall_const, B]
      constructor
      · intro h i
        rcases i with ⟨i, l⟩
        split_ifs with hi
        · have hi' : i = y := by simpa using hi
          subst i
          exact h l
        · simp
      · intro h l
        have := h (y, l)
        simpa using this
    rw [hset, MeasureTheory.volume_pi_pi]
    simp_rw [B]
    rw [Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_eq_single y]
    · simp [volume_unitAddTorus_univ (D := D)]
    · intro z _hz hzy
      simp [hzy, volume_unitAddTorus_univ (D := D)]
    · simp
  rw [hvolume]
  letI : IsProbabilityMeasure (volume : Measure (UnitAddTorus D)) :=
    ⟨volume_unitAddTorus_univ⟩
  have hprob := probReal_add_probReal_compl
    (μ := (volume : Measure (UnitAddTorus D))) hA
  have hcomp : volume.real Aᶜ ≤ 1 - p := by linarith
  have hcomp0 : 0 ≤ volume.real Aᶜ := ENNReal.toReal_nonneg
  have honep : 0 ≤ 1 - p := hcomp0.trans hcomp
  have hpow : (volume.real Aᶜ) ^ L ≤ (1 - p) ^ L :=
    pow_le_pow_left₀ hcomp0 hcomp L
  have hexp : (1 - p) ^ L ≤ Real.exp (-p * L) := by
    calc
      (1 - p) ^ L ≤ (Real.exp (-p)) ^ L :=
        pow_le_pow_left₀ honep (Real.one_sub_le_exp_neg p) L
      _ = Real.exp (-p * L) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  rw [← ENNReal.ofReal_toReal (measure_ne_top volume Aᶜ),
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (hpow.trans hexp)

lemma volume_hunterGroupMissSet_le
    (D : ℕ) (hD : 400 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    (P : BoundedAP (hunterN D) (hunterX D)) (y : Fin (hunterY D)) :
    volume (hunterGroupMissSet D theta P y) ≤
      ENNReal.ofReal (Real.exp (-((D : ℝ) ^ (9 * D)))) := by
  let p : ℝ := ((D : ℝ) ^ (6 * D))⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hp : p ≤ volume.real
      (hunterOrbitPositiveSet D theta P.start P.step) :=
    pow_neg_sixD_le_volumeReal_hunterOrbitPositiveSet D hD htheta
      P.start P.step P.step_pos P.1.2.isLt
  have hmiss : volume (hunterGroupMissSet D theta P y) ≤
      ENNReal.ofReal (Real.exp (-p * hunterGroupSize D)) := by
    simpa only [hunterGroupMissSet] using
      (volume_pi_groupMiss_le_exp
        (Y := hunterY D) (L := hunterGroupSize D)
        (hunterOrbitPositiveSet D theta P.start P.step)
        (measurableSet_hunterOrbitPositiveSet D theta P.start P.step)
        hp0 hp y)
  have hexponent : p * hunterGroupSize D = (D : ℝ) ^ (9 * D) := by
    dsimp [p, hunterGroupSize]
    rw [inv_mul_eq_div, div_eq_iff (by positivity)]
    push_cast
    rw [← pow_add]
    congr 1
    ring
  have hnegative : -p * (hunterGroupSize D : ℝ) =
      -((D : ℝ) ^ (9 * D)) := by rw [neg_mul, hexponent]
  rw [hnegative] at hmiss
  exact hmiss

end

end Erdos984
