import ErdosProblems.Erdos336.StableHighPowerCertificate
import ErdosProblems.Erdos336.KneserAlmostExpansion

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Full one-fibre growth under every nonzero subgroup forces the standard
aperiodic lower bound `|2A|≥2|A|-1`, even if `2A` is periodic. -/
theorem two_mul_card_le_card_add_self_add_one_of_saturation_growth
    {A : Finset G} (hA : A.Nonempty)
    (hsat : ∀ K : AddSubgroup G, K ≠ ⊥ →
      A.card + (addSubgroupFinset K).card ≤
        (A + addSubgroupFinset K).card) :
    2 * A.card ≤ (A + A).card + 1 := by
  let K : AddSubgroup G :=
    AddAction.stabilizer G (↑(A + A) : Set G)
  let H : Finset G := (A + A).addStab
  have hAA : (A + A).Nonempty := hA.add hA
  have hKH : addSubgroupFinset K = H := by
    ext x
    simp only [mem_addSubgroupFinset, H]
    change (x ∈ (K : Set G)) ↔ x ∈ (H : Set G)
    rw [Finset.coe_addStab hAA]
  have hzero : 0 ∈ H := Finset.zero_mem_addStab.mpr hAA
  have hAsub : A ⊆ A + H := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hkneser : 2 * (A + H).card ≤ (A + A).card + H.card := by
    have h := Finset.add_kneser A A
    simpa [H, two_mul] using h
  have hAc := Finset.card_le_card hAsub
  by_cases hK : K = ⊥
  · have hH : H.card = 1 := by
      rw [← hKH, hK]
      simp [addSubgroupFinset]
    omega
  · have hs : A.card + H.card ≤ (A + H).card := by
      simpa [hKH] using hsat K hK
    have hHpos : 0 < H.card := by
      rw [Finset.card_pos]
      exact ⟨0, hzero⟩
    omega

section Minimal

variable [IsAddCyclic G]

/-- A minimal counterexample to the stable high-power certificate has
almost-full expansion against every nonempty subset of its high power. -/
theorem almost_expansion_of_smaller_stable
    (C : Set G) (t : ℕ) (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hnot : ¬ StableHighPowerCertificate C t)
    (hsmaller : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < Fintype.card G →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificate D t)
    {B : Finset G} (hB : B.Nonempty)
    (hBsub : B ⊆ exactPowerFinset C t) :
    (exactPowerFinset C t).card + B.card ≤
      (exactPowerFinset C t + B).card + 1 := by
  let A := exactPowerFinset C t
  have hA : A.Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_exactPowerFinset]
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hsat := proper_saturation_growth_of_smaller_stable C t hzero
    hprimitive hdoub hnot hsmaller
  have hdouble : 2 * A.card ≤ (A + A).card + 1 :=
    two_mul_card_le_card_add_self_add_one_of_saturation_growth hA hsat
  have hBcard : B.card ≤ A.card := Finset.card_le_card hBsub
  have hsumcard : (A + A).card ≤ Fintype.card G := Finset.card_le_univ _
  have hsize : A.card + B.card ≤ Fintype.card G + 1 := by omega
  exact card_add_add_one_ge_of_proper_saturation_growth hA hB hsize
    (fun K hKbot _hKtop => hsat K hKbot)

end Minimal

end Erdos336
