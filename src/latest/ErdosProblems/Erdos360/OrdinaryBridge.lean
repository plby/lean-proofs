import ErdosProblems.Erdos360.Core

open scoped BigOperators Pointwise

namespace Erdos360

lemma subsetSum_image_subset_image_subsetSum
    {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    [DecidableEq G] [DecidableEq H]
    (f : G →+ H) (A : Finset G) :
    (A.image f).subsetSum ⊆ A.subsetSum.image f := by
  classical
  intro x hx
  obtain ⟨B, hB, hBsum⟩ := Finset.mem_subsetSum_iff.mp hx
  have hpre : ∀ b : B, ∃ a : A, f a.1 = b.1 := by
    intro b
    have hbImage : b.1 ∈ A.image f := hB b.2
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hbImage
    exact ⟨⟨a, ha⟩, hab⟩
  let g : B → A := fun b => Classical.choose (hpre b)
  have hg (b : B) : f (g b).1 = b.1 :=
    Classical.choose_spec (hpre b)
  have hginj : Function.Injective g := by
    intro b c hbc
    apply Subtype.ext
    rw [← hg b, ← hg c, hbc]
  let C : Finset G := (Finset.univ : Finset B).image fun b => (g b).1
  have hCA : C ⊆ A := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
    exact (g b).2
  have hCsum : f (∑ a ∈ C, a) = x := by
    rw [map_sum]
    change (∑ a ∈ C, f a) = x
    rw [show (∑ a ∈ C, f a) = ∑ b : B, f (g b).1 by
      dsimp only [C]
      rw [Finset.sum_image]
      intro b _ c _ hbc
      apply hginj
      exact Subtype.ext hbc]
    rw [show (∑ b : B, f (g b).1) = ∑ b : B, b.1 by
      apply Finset.sum_congr rfl
      intro b _
      exact hg b]
    calc
      (∑ b : B, b.1) = ∑ b ∈ B, b :=
        (Finset.sum_subtype B (fun _ => Iff.rfl) id).symm
      _ = x := hBsum
  apply Finset.mem_image.mpr
  refine ⟨∑ a ∈ C, a, Finset.mem_subsetSum_iff.mpr ⟨C, hCA, rfl⟩, hCsum⟩

lemma modularPhaseSums_singleton_zero_subset_initialSubsetSum
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ : Finset (ZMod b))
    (hdiverse : PhaseDiverse hb R₀) (k : ℕ) :
    modularPhaseSums hb R₀ {0} (by simp) hdiverse k ⊆ R₀.subsetSum := by
  rw [modularPhaseSums]
  intro x hx
  rw [Finset.mem_add] at hx
  obtain ⟨z, hz, s, hs, rfl⟩ := hx
  simp only [Finset.mem_singleton] at hz
  subst z
  simpa using (Finset.subsetSum_mono
    (Finset.sdiff_subset : R₀ \ modularRemainder hb R₀ {0} (by simp) hdiverse k ⊆ R₀) hs)

lemma modularPhaseSums_cast_subset_occupiedResidues
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ => (a : ZMod t)))
    (k : ℕ) :
    modularPhaseSums ht (A.image fun a : ℕ => (a : ZMod t)) {0}
        (by simp) hdiverse k ⊆ occupiedResidues A.subsetSum t := by
  have hphase := modularPhaseSums_singleton_zero_subset_initialSubsetSum
    ht (A.image fun a : ℕ => (a : ZMod t)) hdiverse k
  exact hphase.trans (by
    simpa [occupiedResidues] using
      (subsetSum_image_subset_image_subsetSum
        (Nat.castAddMonoidHom (ZMod t)) A))

/-- The deterministic phase machine, specialized to the residue image of an
integer set.  Its modular sumset is represented by ordinary subset sums of
the original integers. -/
theorem occupiedResidues_lower_of_phaseDiverse
    {t : ℕ} [NeZero t] (ht : 0 < t) (A : Finset ℕ)
    (hdiverse : PhaseDiverse ht (A.image fun a : ℕ => (a : ZMod t)))
    {k : ℕ} (hlog : 4 * (Nat.log 2 t + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ (A.image fun a : ℕ => (a : ZMod t)).card) :
    t ≤ 4 * (occupiedResidues A.subsetSum t).card ∨
      k * (A.image fun a : ℕ => (a : ZMod t)).card ≤
        64 * (occupiedResidues A.subsetSum t).card := by
  have hsub := modularPhaseSums_cast_subset_occupiedResidues
    ht A hdiverse k
  have hcard := Finset.card_le_card hsub
  rcases bounded_modular_subsetSum_growth ht
      (A.image fun a : ℕ => (a : ZMod t)) {0} (by simp)
      hdiverse hlog hhalf with hfill | hquad
  · exact Or.inl (hfill.trans (Nat.mul_le_mul_left 4 hcard))
  · exact Or.inr (hquad.trans (Nat.mul_le_mul_left 64 hcard))

lemma zmod_natCast_injOn_Ico
    {lo hi t : ℕ} (hwidth : hi - lo ≤ t) :
    Set.InjOn (fun a : ℕ => (a : ZMod t)) (Finset.Ico lo hi : Set ℕ) := by
  intro a ha b hb hab
  have haI := Finset.mem_Ico.mp ha
  have hbI := Finset.mem_Ico.mp hb
  have hmod : a ≡ b [MOD t] :=
    (ZMod.natCast_eq_natCast_iff a b t).mp hab
  have hsub : a - lo ≡ b - lo [MOD t] :=
    hmod.sub haI.1 hbI.1 (Nat.ModEq.refl lo)
  have hasub : a - lo < t := by omega
  have hbsub : b - lo < t := by omega
  have heq : a - lo = b - lo := hsub.eq_of_lt_of_lt hasub hbsub
  omega

lemma card_image_zmod_eq_of_subset_Ico
    {lo hi t : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Ico lo hi)
    (hwidth : hi - lo ≤ t) :
    (A.image fun a : ℕ => (a : ZMod t)).card = A.card := by
  exact Finset.card_image_iff.mpr
    ((zmod_natCast_injOn_Ico hwidth).mono (by exact_mod_cast hA))

lemma card_filter_image_zmod_nondivisible
    {lo hi t d : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Ico lo hi)
    (hwidth : hi - lo ≤ t) (hdt : d ∣ t) :
    ((A.image fun a : ℕ => (a : ZMod t)).filter
        fun x => ¬d ∣ x.val).card =
      (A.filter fun a => ¬d ∣ a).card := by
  have heq :
      (A.image fun a : ℕ => (a : ZMod t)).filter (fun x => ¬d ∣ x.val) =
        (A.filter fun a => ¬d ∣ a).image fun a : ℕ => (a : ZMod t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hnon⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      simpa [ZMod.val_natCast, Nat.dvd_mod_iff hdt] using hnon
    · rintro ⟨a, ⟨ha, hnon⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_⟩
      simpa [ZMod.val_natCast, Nat.dvd_mod_iff hdt] using hnon
  rw [heq]
  exact Finset.card_image_iff.mpr
    ((zmod_natCast_injOn_Ico hwidth).mono (by
      exact_mod_cast (Finset.filter_subset (fun a => ¬d ∣ a) A |>.trans hA)))

/-- Diversity of integers implies phase diversity modulo a pivot as soon as
every subgroup modulus that can occur while at least half the residues
remain is bounded by the diversity parameter. -/
lemma phaseDiverse_cast_of_diverse_of_closure_bounded
    {lo hi t K : ℕ} [NeZero t] (ht : 0 < t)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ico lo hi)
    (hwidth : hi - lo ≤ t)
    (hdiverse : DiverseSampling.DiverseNat A K)
    (hclosure : ∀ R : Finset (ZMod t),
      R ⊆ (A.image fun a : ℕ => (a : ZMod t)) →
      (A.image fun a : ℕ => (a : ZMod t)).card ≤ 2 * R.card →
      ∀ d : ℕ, 1 < d → d ∣ closureModulus ht R → d ≤ K + 1) :
    PhaseDiverse ht (A.image fun a : ℕ => (a : ZMod t)) := by
  intro R hsub hwide d hd hdclosure
  have hdK := hclosure R hsub hwide d hd hdclosure
  have hdiv := hdiverse d (by omega)
  rw [card_filter_image_zmod_nondivisible A hA hwidth
    (hdclosure.trans (closureModulus_dvd ht R))]
  omega

/-- A numerical version of `phaseDiverse_cast_of_diverse_of_closure_bounded`.
If the integer set is large enough compared with the ambient modulus, then
every subgroup modulus which can occur while at least half the residues
remain is bounded by the available diversity.  This is the form needed by
the ordinary-growth application, where the seed lies in a short dyadic
interval and its cardinality is controlled by the parameter ledger. -/
lemma phaseDiverse_cast_of_diverse_of_card_scale
    {lo hi t K : ℕ} [NeZero t] (ht : 0 < t)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ico lo hi)
    (hwidth : hi - lo ≤ t)
    (hdiverse : DiverseSampling.DiverseNat A K)
    (hscale : 2 * t ≤ (K + 1) * A.card) :
    PhaseDiverse ht (A.image fun a : ℕ ↦ (a : ZMod t)) := by
  apply phaseDiverse_of_bounded
  intro d hd hdt hdcard
  have hcardImage :
      (A.image fun a : ℕ ↦ (a : ZMod t)).card = A.card :=
    card_image_zmod_eq_of_subset_Ico A hA hwidth
  rw [hcardImage] at hdcard
  have hApos : 0 < A.card := by
    by_contra hnot
    have hzero : A.card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hscale
    simp only [mul_zero] at hscale
    omega
  have hmul : d * A.card ≤ (K + 1) * A.card :=
    hdcard.trans hscale
  have hdK : d ≤ K + 1 :=
    Nat.le_of_mul_le_mul_right hmul hApos
  rw [card_filter_image_zmod_nondivisible A hA hwidth hdt]
  exact (show d - 1 ≤ K by omega).trans (hdiverse d (by omega))

/-- Uniform ordinary growth from a seed and a disjoint set of pivots in one
short interval.  The hypotheses expose exactly the two numerical outputs of
the modular phase machine. -/
theorem subsetSum_card_add_pivot_growth
    {lo hi k q : ℕ} {A B : Finset ℕ}
    (hlo : 0 < lo) (hwidth : hi - lo ≤ lo)
    (hA : A ⊆ Finset.Ico lo hi) (hB : B ⊆ Finset.Ico lo hi)
    (hAB : Disjoint A B)
    (hphase : ∀ (t : ℕ) (ht : t ∈ B),
      @PhaseDiverse t ⟨by
        have htI := Finset.mem_Ico.mp (hB ht)
        omega⟩ (by
        have htI := Finset.mem_Ico.mp (hB ht)
        omega) (A.image fun a : ℕ => (a : ZMod t)))
    (hlog : ∀ t ∈ B, 4 * (Nat.log 2 t + 1) ^ 2 ≤ k)
    (hhalf : 2 * k ≤ A.card)
    (hqmod : ∀ t ∈ B, 64 * q ≤ t)
    (hqquad : 64 * q ≤ k * A.card) :
    A.subsetSum.card + B.card * q ≤ (A ∪ B).subsetSum.card := by
  have hres : ∀ t ∈ B, q ≤ (occupiedResidues A.subsetSum t).card := by
    intro t ht
    have htI := Finset.mem_Ico.mp (hB ht)
    have htpos : 0 < t := by omega
    letI : NeZero t := ⟨htpos.ne'⟩
    have hcardImage :
        (A.image fun a : ℕ => (a : ZMod t)).card = A.card := by
      apply card_image_zmod_eq_of_subset_Ico A hA
      exact hwidth.trans htI.1
    have hgrowth := occupiedResidues_lower_of_phaseDiverse
      htpos A (hphase t ht) (hlog t ht) (by simpa [hcardImage] using hhalf)
    rcases hgrowth with hfill | hquadratic
    · have hq := hqmod t ht
      omega
    · rw [hcardImage] at hquadratic
      omega
  have hgrowth := subsetSum_card_add_sum_le_union hAB (fun _ => q)
    (fun t ht => by
      have htI := Finset.mem_Ico.mp (hB ht)
      omega) hres
  simpa [mul_comm] using hgrowth

end Erdos360
