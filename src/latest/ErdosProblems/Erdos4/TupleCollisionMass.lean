import ErdosProblems.Erdos4.AffineTuples

/-!
# Small atom bounds control tuple-collision mass

A fixed integer can belong to at most `k` translated tuples of one
source. More generally, at most `k * card T` centers give a tuple meeting
`T`. These exact counts control the diagonal and mixed moment errors.
-/

open scoped BigOperators

namespace Erdos4.TupleCollisionMass

open AffineTuples

variable {k : ℕ}

def meetingCenters (h : Fin k → ℕ) (p Y : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun n => ¬Disjoint (tuple h p n) T)

theorem card_meetingCenters_le (h : Fin k → ℕ) (p Y : ℕ) (T : Finset ℕ) :
    (meetingCenters h p Y T).card ≤ T.card * k := by
  let candidates := T.biUnion (fun q => Finset.univ.image (fun i : Fin k => q - h i * p))
  have hsub : meetingCenters h p Y T ⊆ candidates := by
    intro n hn
    obtain ⟨q, hqn, hqT⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hn).2
    obtain ⟨i, hi⟩ := (mem_tuple h p n q).mp hqn
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hqT, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩⟩
    omega
  calc
    _ ≤ candidates.card := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ T, (Finset.univ.image (fun i : Fin k => q - h i * p)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ T, k := by
      apply Finset.sum_le_sum
      intro q _hq
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := fun i => q - h i * p))
    _ = _ := by simp

theorem meeting_mass_le (h : Fin k → ℕ) (p Y : ℕ) (T : Finset ℕ)
    (μ : ℕ → ℝ) {α : ℝ} (hα : 0 ≤ α) (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    (∑ n ∈ Finset.Icc 1 Y, if ¬Disjoint (tuple h p n) T then μ n else 0) ≤
      (T.card : ℝ) * k * α := by
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _n ∈ meetingCenters h p Y T, α :=
      Finset.sum_le_sum (fun n hn => hμ n (Finset.mem_filter.mp hn).1)
    _ = ((meetingCenters h p Y T).card : ℝ) * α := by simp
    _ ≤ ((T.card * k : ℕ) : ℝ) * α :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_meetingCenters_le h p Y T) hα
    _ = _ := by rw [Nat.cast_mul]

noncomputable def hitMass (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, if q ∈ tuple h p n then μ n else 0

theorem hitMass_nonneg (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) : 0 ≤ hitMass h p Y μ q := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact hμ n hn
  · exact le_rfl

theorem hitMass_le (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    hitMass h p Y μ q ≤ (k : ℝ) * α := by
  simpa only [Finset.disjoint_singleton_right, not_not, Finset.card_singleton,
    Nat.cast_one, one_mul, hitMass] using meeting_mass_le h p Y {q} μ hα hμ

theorem hitMass_sq_le (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    hitMass h p Y μ q ^ 2 ≤ (k : ℝ) * α * hitMass h p Y μ q := by
  simpa only [pow_two] using mul_le_mul_of_nonneg_right (hitMass_le h p Y μ q hα hμ)
    (hitMass_nonneg h p Y μ q hμ0)

theorem mixed_collision_mass_le (h : Fin k → ℕ) (hh : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    {α : ℝ} (hα : 0 ≤ α) (hμ0 : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, μ n ≤ α) :
    (∑ m ∈ Finset.Icc 1 Y, if q ∈ tuple h p m then μ m *
      (∑ n ∈ Finset.Icc 1 Y, if ¬Disjoint (tuple h p n) (tuple h p m) then μ n else 0)
      else 0) ≤ (k : ℝ) ^ 2 * α * hitMass h p Y μ q := by
  unfold hitMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hqm : q ∈ tuple h p m
  · rw [if_pos hqm, if_pos hqm]
    have hbound := mul_le_mul_of_nonneg_left
      (meeting_mass_le h p Y (tuple h p m) μ hα hμ) (hμ0 m hm)
    rw [card_tuple h hh hp m] at hbound
    exact hbound.trans_eq (by ring)
  · simp [hqm]

theorem anchor_sum_eq_hitMass (h : Fin k → ℕ) (hh : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hshift : ∀ i : Fin k, h i * p ≤ q)
    (hcenter : ∀ i : Fin k, q - h i * p ∈ Finset.Icc 1 Y) :
    (∑ i : Fin k, μ (q - h i * p)) = hitMass h p Y μ q := by
  have hinj : Function.Injective (fun i : Fin k => q - h i * p) := by
    intro i j hij
    apply hh
    apply mul_right_cancel₀ hp.ne'
    have hi := Nat.sub_add_cancel (hshift i)
    have hj := Nat.sub_add_cancel (hshift j)
    change q - h i * p = q - h j * p at hij
    rw [hij] at hi
    exact Nat.add_left_cancel (hi.trans hj.symm)
  have hset : (Finset.Icc 1 Y).filter (fun n => q ∈ tuple h p n) =
      Finset.univ.image (fun i : Fin k => q - h i * p) := by
    ext n
    constructor
    · intro hn
      obtain ⟨i, hi⟩ := (mem_tuple h p n q).mp (Finset.mem_filter.mp hn).2
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by omega⟩
    · intro hn
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_filter.mpr ⟨hcenter i,
        (mem_tuple h p (q - h i * p) q).mpr ⟨i, Nat.sub_add_cancel (hshift i)⟩⟩
  unfold hitMass
  rw [← Finset.sum_filter, hset, Finset.sum_image]
  exact hinj.injOn

end Erdos4.TupleCollisionMass
