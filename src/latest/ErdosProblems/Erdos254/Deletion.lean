/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- Choose the prescribed number of elements of least weight. -/
lemma exists_least_weight_subset {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (r : ℕ) (hr : r ≤ s.card) :
    ∃ D ⊆ s, D.card = r ∧ ∀ x ∈ D, ∀ y ∈ s \ D, f x ≤ f y := by
  classical
  induction r generalizing s with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ r ih =>
      obtain ⟨x, hx, hxmin⟩ := s.exists_min_image f (Finset.card_pos.mp (by omega))
      obtain ⟨D, hD, hcard, hmin⟩ := ih (s.erase x) (by
        rw [Finset.card_erase_of_mem hx]; omega)
      have hxD : x ∉ D := fun h ↦ (Finset.mem_erase.mp (hD h)).1 rfl
      refine ⟨insert x D, Finset.insert_subset hx (hD.trans (Finset.erase_subset _ _)),
        by simp [hxD, hcard], ?_⟩
      intro z hz y hy
      rcases Finset.mem_sdiff.mp hy with ⟨hys, hyD⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxmin y hys
      · apply hmin z hz y
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, hys⟩, ?_⟩
        · intro h; exact hyD (Finset.mem_insert.mpr (Or.inl h))
        · intro h; exact hyD (Finset.mem_insert_of_mem h)

/-- Removing the least-weight elements retains at least the corresponding
fraction of the total weight (the finite averaging step in Fan's Lemma 3.2). -/
lemma exists_deletion_average {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (r : ℕ) (hr : r < s.card) :
    ∃ D ⊆ s, D.card = r ∧
      ((s.card - r : ℕ) : ℝ) / s.card * (∑ x ∈ s, f x) ≤ ∑ x ∈ s \ D, f x := by
  classical
  obtain ⟨D, hD, hcard, hmin⟩ := exists_least_weight_subset s f r hr.le
  refine ⟨D, hD, hcard, ?_⟩
  have hpair : ∑ x ∈ D, ∑ y ∈ s \ D, f x ≤ ∑ x ∈ D, ∑ y ∈ s \ D, f y :=
    Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦ hmin x hx y hy
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hpair
  have hsum := Finset.sum_sdiff hD (f := f)
  have hscard : (s \ D).card = s.card - r := by rw [Finset.card_sdiff_of_subset hD, hcard]
  rw [hscard, hcard] at hpair
  have hc : (0 : ℝ) < s.card := by exact_mod_cast (Nat.zero_le r).trans_lt hr
  have hsub : ((s.card - r : ℕ) : ℝ) = (s.card : ℝ) - r :=
    Nat.cast_sub hr.le
  rw [hsub] at hpair ⊢
  rw [div_mul_eq_mul_div, div_le_iff₀ hc]
  nlinarith

private lemma exists_interval_mass {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hdiv : ¬ Summable w) (N : ℕ) :
    ∃ L, N < L ∧ 1 ≤ ∑ k ∈ Finset.Ico N L, w k := by
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hw).mp hdiv
  have he : ∀ᶠ L in atTop, N < L ∧ 1 ≤ ∑ k ∈ Finset.Ico N L, w k := by
    filter_upwards [ht.eventually (eventually_ge_atTop (∑ k ∈ Finset.range N, w k + 1)),
      eventually_gt_atTop N] with L hL hN
    refine ⟨hN, ?_⟩
    rw [Finset.sum_Ico_eq_sub w hN.le]
    linarith
  exact he.exists

/-- A diagonal selection on consecutive finite intervals. Each of countably
many objectives is served on arbitrarily late intervals of mass at least one. -/
lemma diagonal_selection (w : ℕ → ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ)
    (hw : ∀ j k, 0 ≤ w j k) (hdiv : ∀ j, ¬ Summable (w j))
    (hg : ∀ j k i, 0 ≤ g j k i) (hdom : ∀ j k, w j k ≤ g j k j) :
    ∃ b : ℕ → ℕ, ∀ j, ¬ Summable (fun k ↦ g j k (b k)) := by
  classical
  choose next hnext hmass using fun j N ↦ exists_interval_mass (hw j) (hdiv j) N
  let K : ℕ → ℕ := fun s ↦ Nat.rec 0 (fun t v ↦ next (Nat.unpair t).1 v) s
  have hK0 : K 0 = 0 := rfl
  have hKsucc : ∀ s, K (s + 1) = next (Nat.unpair s).1 (K s) := fun _ ↦ rfl
  have hK : StrictMono K := strictMono_nat_of_lt_succ fun s ↦ by
    rw [hKsucc]; exact hnext _ _
  have hKid : ∀ s, s ≤ K s := hK.id_le
  have hcover : ∀ k, ∃ s, k < K (s + 1) := fun k ↦ ⟨k, by have := hKid (k + 1); omega⟩
  let stage : ℕ → ℕ := fun k ↦ Nat.find (hcover k)
  have hstage : ∀ s k, k ∈ Finset.Ico (K s) (K (s + 1)) → stage k = s := by
    intro s k hk
    rcases Finset.mem_Ico.mp hk with ⟨hlo, hhi⟩
    apply (Nat.find_eq_iff (hcover k)).mpr
    refine ⟨hhi, ?_⟩
    intro t hts
    have : K (t + 1) ≤ K s := hK.monotone (show t + 1 ≤ s by omega)
    omega
  let b : ℕ → ℕ := fun k ↦ (Nat.unpair (stage k)).1
  refine ⟨b, ?_⟩
  intro j hsum
  obtain ⟨F, hF⟩ := summable_iff_vanishing_norm.mp hsum 1 (by norm_num)
  let s := Nat.pair j (F.sup id + 1)
  have hsj : (Nat.unpair s).1 = j := by simp [s]
  have hstart : F.sup id < K s := by
    have hp := Nat.right_le_pair j (F.sup id + 1)
    have hi := hKid s
    dsimp [s] at hi ⊢
    omega
  have hdisj : Disjoint (Finset.Ico (K s) (K (s + 1))) F := by
    apply Finset.disjoint_left.mpr
    intro k hk hkF
    have hlo := (Finset.mem_Ico.mp hk).1
    have hle : k ≤ F.sup id := Finset.le_sup (f := id) hkF
    omega
  have hlt := hF (Finset.Ico (K s) (K (s + 1))) hdisj
  have hge : 1 ≤ ∑ k ∈ Finset.Ico (K s) (K (s + 1)), g j k (b k) := by
    have hm := hmass (Nat.unpair s).1 (K s)
    rw [← hKsucc, hsj] at hm
    apply hm.trans
    apply Finset.sum_le_sum
    intro k hk
    have hb : b k = j := by dsimp [b]; rw [hstage s k hk, hsj]
    rw [hb]
    exact hdom j k
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ ↦ hg j k (b k)))] at hlt
  linarith

/-- Fan, Lemma 3.2, with the countable objectives indexed by `ℕ`.
The blocks need not be disjoint for this blockwise sum statement. -/
theorem deletion_lemma {α : Type*} [DecidableEq α] (X : ℕ → Finset α)
    (r : ℕ → ℕ) (hr : ∀ k, r k < (X k).card) (f : ℕ → α → ℝ)
    (hf : ∀ j x, 0 ≤ f j x)
    (hdiv : ∀ j, ¬ Summable (fun k ↦
      (((X k).card - r k : ℕ) : ℝ) / (X k).card * ∑ x ∈ X k, f j x)) :
    ∃ D : ℕ → Finset α, (∀ k, D k ⊆ X k ∧ (D k).card = r k) ∧
      ∀ j, ¬ Summable (fun k ↦ ∑ x ∈ X k \ D k, f j x) := by
  classical
  choose R hR hcard havg using fun j k ↦ exists_deletion_average (X k) (f j) (r k) (hr k)
  let w : ℕ → ℕ → ℝ := fun j k ↦
    (((X k).card - r k : ℕ) : ℝ) / (X k).card * ∑ x ∈ X k, f j x
  let g : ℕ → ℕ → ℕ → ℝ := fun j k i ↦ ∑ x ∈ X k \ R i k, f j x
  have hw : ∀ j k, 0 ≤ w j k := by
    intro j k
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun x _ ↦ hf j x)
  have hg : ∀ j k i, 0 ≤ g j k i := fun j k i ↦ Finset.sum_nonneg fun x _ ↦ hf j x
  obtain ⟨b, hb⟩ := diagonal_selection w g hw hdiv hg havg
  exact ⟨fun k ↦ R (b k) k, fun k ↦ ⟨hR _ _, hcard _ _⟩, hb⟩

/-- The same deletion lemma for an arbitrary countable family, including the
empty family. -/
theorem deletion_lemma_countable {α J : Type*} [DecidableEq α] [Countable J]
    (X : ℕ → Finset α) (r : ℕ → ℕ) (hr : ∀ k, r k < (X k).card)
    (f : J → α → ℝ) (hf : ∀ j x, 0 ≤ f j x)
    (hdiv : ∀ j, ¬ Summable (fun k ↦
      (((X k).card - r k : ℕ) : ℝ) / (X k).card * ∑ x ∈ X k, f j x)) :
    ∃ D : ℕ → Finset α, (∀ k, D k ⊆ X k ∧ (D k).card = r k) ∧
      ∀ j, ¬ Summable (fun k ↦ ∑ x ∈ X k \ D k, f j x) := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
      choose D hD hcard using fun k ↦ Finset.exists_subset_card_eq (hr k).le
      exact ⟨D, fun k ↦ ⟨hD k, hcard k⟩, fun j ↦ isEmptyElim j⟩
  | inr h =>
      obtain ⟨e, he⟩ := exists_surjective_nat J
      obtain ⟨D, hD, hsum⟩ := deletion_lemma X r hr (fun j ↦ f (e j))
        (fun j ↦ hf (e j)) (fun j ↦ hdiv (e j))
      refine ⟨D, hD, ?_⟩
      intro j
      obtain ⟨n, rfl⟩ := he j
      exact hsum n

end Erdos254
