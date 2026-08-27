import ErdosProblems.Erdos4.TiltedActualSieve
import ErdosProblems.Erdos4.TiltedColorParameters
import ErdosProblems.Erdos4.TiltedFiberRoots
import ErdosProblems.Erdos4.TiltedPartitionLaw

/-! The actual family of balanced fiber partitions, with all its arithmetic properties. -/

open scoped BigOperators

namespace Erdos4.Tilted

open RandomResidueSieve

structure CompositeFiberFamily (c : ℝ) (x : ℕ) where
  target_count : x ≤ (compositeTargets c x).card
  partition : compositeColors x → Finpartition (compositeTargets c x)
  size : ∀ p, ∀ E ∈ (partition p).parts, E.card ≤ blockSize x (compositeTargets c x)
  fiber : ∀ p, ∀ E ∈ (partition p).parts, ∀ n ∈ E, ∀ m ∈ E,
    (n : ZMod p.val) = (m : ZMod p.val)
  count_lower : ∀ p, x ≤ 2 * (partition p).parts.card
  count_upper : ∀ p, (partition p).parts.card ≤ x + p.val

theorem exists_compositeFiberFamily {c : ℝ} {x : ℕ} (hx : 0 < x)
    (hC : x ≤ (compositeTargets c x).card) : Nonempty (CompositeFiberFamily c x) := by
  classical
  choose P hsize hfiber hlo hhi using fun p : compositeColors x =>
    exists_balanced_fiber_partition hx (mem_compositeColors.mp p.property).1 (compositeTargets c x) hC
  exact ⟨⟨hC, P, hsize, hfiber, hlo, hhi⟩⟩

namespace CompositeFiberFamily

variable {c : ℝ} {x : ℕ} (F : CompositeFiberFamily c x)

include F in
theorem targets_nonempty (hx : 0 < x) : (compositeTargets c x).Nonempty :=
  Finset.card_pos.mp (hx.trans_le F.target_count)

theorem count_le (p : compositeColors x) : (F.partition p).parts.card ≤ 17 * x := by
  have hp := (mem_compositeColors.mp p.property).2.2
  have hh := F.count_upper p
  omega

theorem part_squarefree
    (hwidth : gapTarget c x < (sieveCutoff x + 1) * smallCutoff x)
    (p : compositeColors x) (E : Finset ℕ) (hE : E ∈ (F.partition p).parts) :
    Squarefree (∏ n ∈ E, n) := by
  have hEC := (F.partition p).subset hE
  have hp := mem_compositeColors.mp p.property
  have hbound : ∀ n ∈ E, n ≤ gapTarget c x := fun n hn => (compositeTargets_properties (hEC hn)).2.1
  have hrough : ∀ n ∈ E, IsRough (smallCutoff x) n := fun n hn =>
    (compositeTargets_properties (hEC hn)).2.2.2.2
  have hsmall : ∀ n ∈ E, ∀ s, s.Prime → s ∣ n → s < p.val := by
    intro n hn s hs hsn
    have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le x) (compositeTargets_properties (hEC hn)).1
    have hsf := composite_factors_supported (hEC hn) hwidth (Nat.mem_primeFactors.mpr ⟨hs, hsn, hnpos.ne'⟩)
    exact ((mem_coordinatePrimes.mp hsf).2.2.trans (Nat.div_le_self x 64)).trans_lt hp.2.1
  have hpwidth : gapTarget c x < p.val * smallCutoff x := by
    have hBp : sieveCutoff x + 1 ≤ p.val := by have hh := Nat.div_le_self x 64; unfold sieveCutoff; omega
    exact hwidth.trans_le (Nat.mul_le_mul_right _ hBp)
  have hcop := fiber_pairwise_coprime hp.1 hpwidth hbound hrough hsmall (F.fiber p E hE)
  exact fiber_product_squarefree hcop (fun n hn => (compositeTargets_properties (hEC hn)).2.2.2.1)

noncomputable def companion (v : compositeTargets c x) (p : ℕ) : Finset ℕ := by
  classical
  exact if hp : p ∈ compositeColors x then rootCompanions (F.partition ⟨p, hp⟩) v.val else ∅

@[simp] theorem companion_apply (v : compositeTargets c x) (p : compositeColors x) :
    F.companion v p.val = rootCompanions (F.partition p) v.val := by
  simp only [companion, dif_pos p.property]

theorem companion_subset (v : compositeTargets c x) (p : compositeColors x) :
    F.companion v p.val ⊆ compositeTargets c x := by
  rw [companion_apply]
  exact rootCompanions_subset _ _

theorem companion_properties (v : compositeTargets c x) (p : compositeColors x) :
    ∀ n ∈ F.companion v p.val,
      n ≤ gapTarget c x ∧ n ≠ v.val ∧ (n : ZMod p.val) = (v.val : ZMod p.val) := by
  rw [companion_apply]
  intro n hn
  exact ⟨(compositeTargets_properties (rootCompanions_subset _ _ hn)).2.1,
    rootCompanions_ne_root _ hn, rootCompanions_fiber _ v.property (F.fiber p) n hn⟩

theorem companion_card (v : compositeTargets c x) (p : compositeColors x) :
    (F.companion v p.val).card ≤ blockSize x (compositeTargets c x) := by
  rw [companion_apply]
  exact rootCompanions_card_le _ v.property (F.size p)

theorem companion_squarefree
    (hwidth : gapTarget c x < (sieveCutoff x + 1) * smallCutoff x)
    (v : compositeTargets c x) (p : compositeColors x) :
    Squarefree (∏ n ∈ F.companion v p.val, n) := by
  rw [companion_apply]
  exact rootCompanions_squarefree _ v.property (F.part_squarefree hwidth p)

theorem companion_avoid_root
    (hwidth : gapTarget c x < (sieveCutoff x + 1) * smallCutoff x)
    (v : compositeTargets c x) (p : compositeColors x) (l : sievePrimes x) :
    (v.val : ZMod (sievePrimeValue x l)) ∉ residues (sievePrimeValue x) (F.companion v p.val) l := by
  rw [companion_apply]
  have hp := mem_compositeColors.mp p.property
  have hl := mem_coordinatePrimes.mp l.property
  have hpl : p.val ≠ sievePrimeValue x l := ne_of_gt ((sievePrimeValue_le x l).trans_lt hp.2.1)
  have hwidth' : gapTarget c x < p.val * sievePrimeValue x l := by
    have hBp : sieveCutoff x + 1 ≤ p.val := by have hh := Nat.div_le_self x 64; unfold sieveCutoff; omega
    exact hwidth.trans_le (Nat.mul_le_mul hBp hl.2.1.le)
  exact rootCompanions_avoid_root (F.partition p) v.property hp.1 hl.1 hpl hwidth'
    (fun n hn => (compositeTargets_properties hn).2.1) (F.fiber p)

theorem companions_disjoint (hY : gapTarget c x ≤ x ^ 2) (v : compositeTargets c x)
    (p q : compositeColors x) (hpq : p ≠ q) : Disjoint (F.companion v p.val) (F.companion v q.val) := by
  rw [companion_apply, companion_apply]
  have hp := mem_compositeColors.mp p.property
  have hq := mem_compositeColors.mp q.property
  have hne : p.val ≠ q.val := fun hh => hpq (Subtype.ext hh)
  have hwidth : gapTarget c x < p.val * q.val := by
    have hprod := Nat.mul_le_mul (show x + 1 ≤ p.val by omega) (show x + 1 ≤ q.val by omega)
    nlinarith
  exact rootCompanions_disjoint (F.partition p) (F.partition q) v.property hp.1 hq.1 hne hwidth
    (fun n hn => (compositeTargets_properties hn).2.1) (F.fiber p) (F.fiber q)

end CompositeFiberFamily

theorem blockEvent_survives {P : Type*} [Fintype P] [DecidableEq P] (ell : P → ℕ)
    [∀ p, Fact (ell p).Prime] (T : Finset ℕ) (a : ∀ p, ZMod (ell p)) :
    blockEvent (fun v a => Survives ell a {v}) T a ↔ Survives ell a T := by
  constructor
  · intro h l ha
    obtain ⟨n, hn, hna⟩ := Finset.mem_image.mp ha
    apply h n hn l
    simpa only [residues, Finset.image_singleton, Finset.mem_singleton] using hna.symm
  · intro h n hn l ha
    apply h l
    have heq : a l = (n : ZMod (ell l)) := by
      simpa only [residues, Finset.image_singleton, Finset.mem_singleton] using ha
    exact Finset.mem_image.mpr ⟨n, hn, heq.symm⟩

end Erdos4.Tilted
