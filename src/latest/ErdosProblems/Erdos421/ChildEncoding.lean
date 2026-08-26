import ErdosProblems.Erdos421.ChildCount
import ErdosProblems.Erdos421.WeightedDescendants

/-! # A length-sensitive encoding of children -/

namespace Erdos421

abbrev ChildCode (L H : ℕ) := Σ r : Fin L, Fin H × Fin (r.val + 1)

theorem parentData_encoding (I : Finset ℕ) (i L H : ℕ)
    (w : (k : I) → ParentData k)
    (hparent : ∀ k, (w k).index = i)
    (hL : ∀ k, (w k).witness.E.card ≤ L)
    (hH : ∀ k, (w k).witness.n - (w k).witness.m + 1 ≤ H) :
    ∃ code : I → ChildCode L H, Function.Injective code ∧
      ∀ k, (code k).1.val + 1 = (w k).witness.E.card := by
  classical
  have hp : prime i ∈ Set.range candidateSequence := by
    rw [range_candidateSequence]
    exact candidate_contains_primes (prime_prime i)
  obtain ⟨t, ht⟩ := hp
  have hstarts : ∀ k : I, ∃ u,
      (w k).witness.E = (Finset.Ico u (u + (w k).witness.E.card)).image candidateSequence := by
    intro k
    have hblock := (w k).old_block.stage_to_candidate
    rw [← range_candidateSequence] at hblock
    exact hblock.exists_start candidateSequence_strictMono
  choose start hstart using hstarts
  have hcross : ∀ k : I, start k ≤ t ∧ t < start k + (w k).witness.E.card := by
    intro k
    have hmem := (w k).left_mem
    rw [hparent k, ← ht, hstart k] at hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
    have hjt : j = t := candidateSequence_strictMono.injective heq
    simpa only [hjt, Finset.mem_Ico] using hj
  let code : I → ChildCode L H := fun k ↦
    ⟨⟨(w k).witness.E.card - 1, by
        have := (w k).old_block.nonempty.card_pos
        have := hL k
        omega⟩,
     ⟨(w k).witness.n - (w k).witness.m, by have := hH k; omega⟩,
     ⟨t - start k, by
        have := hcross k
        have := (w k).old_block.nonempty.card_pos
        dsimp only
        omega⟩⟩
  refine ⟨code, ?_, ?_⟩
  · intro k l heq
    have hr : (w k).witness.E.card = (w l).witness.E.card := by
      have h := congrArg (fun c : ChildCode L H ↦ c.1.val) heq
      have := (w k).old_block.nonempty.card_pos
      have := (w l).old_block.nonempty.card_pos
      dsimp only [code] at h
      omega
    have hs : (w k).witness.n - (w k).witness.m =
        (w l).witness.n - (w l).witness.m :=
      congrArg (fun c : ChildCode L H ↦ c.2.1.val) heq
    have hc : t - start k = t - start l :=
      congrArg (fun c : ChildCode L H ↦ c.2.2.val) heq
    have hstartEq : start k = start l := by
      have := hcross k
      have := hcross l
      omega
    have hE : (w k).witness.E = (w l).witness.E := by
      rw [hstart k, hstart l, hstartEq, hr]
    have hprod : intervalProduct (w k).witness.m
        ((w k).witness.n - (w k).witness.m + 1) =
        intervalProduct (w l).witness.m ((w k).witness.n - (w k).witness.m + 1) := by
      calc
        _ = (w k).witness.E.prod id :=
          (intervalProduct_eq_Icc (w k).witness.later_nonempty).trans
            (w k).witness.product_eq.symm
        _ = (w l).witness.E.prod id := congrArg (Finset.prod · id) hE
        _ = _ := by
          rw [hs, intervalProduct_eq_Icc (w l).witness.later_nonempty]
          exact (w l).witness.product_eq
    have hm : (w k).witness.m = (w l).witness.m :=
      intervalProduct_injective (by omega) hprod
    apply Subtype.ext
    apply prime_gap_index_unique (w k).witness.gap_left
      ((w k).witness.later_nonempty.trans_lt (w k).witness.gap_right)
    · rw [hm]
      exact (w l).witness.gap_left
    · rw [hm]
      exact (w l).witness.later_nonempty.trans_lt (w l).witness.gap_right
  · intro k
    dsimp only [code]
    have := (w k).old_block.nonempty.card_pos
    omega

theorem sum_weight_le_of_injective {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ a, w (f a)) ≤ ∑ b, w b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image f, w b := (Finset.sum_image hf.injOn).symm
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hw

theorem childCode_weight_sum (L H : ℕ) (C : ℝ) :
    (∑ c : ChildCode L H, C / (c.1.val + 1 : ℕ)) = C * L * H := by
  rw [Fintype.sum_sigma]
  have hinner : ∀ r : Fin L,
      (∑ _p : Fin H × Fin (r.val + 1), C / (r.val + 1 : ℕ)) = C * H := by
    intro r
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hr : (r.val : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simp_rw [hinner]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

/-- The reciprocal lengths of children of one parent cost only `C L H`,
where their earlier blocks have length at most `C` times their gap length. -/
theorem parentData_reciprocal_sum_bound (I : Finset ℕ) (i C L H : ℕ)
    (w : (k : I) → ParentData k)
    (hparent : ∀ k, (w k).index = i)
    (hL : ∀ k, (w k).witness.E.card ≤ L)
    (hH : ∀ k, (w k).witness.n - (w k).witness.m + 1 ≤ H)
    (hgap : ∀ k, (w k).witness.E.card ≤ C * gapLength k) :
    (∑ k : I, (1 : ℝ) / gapLength k) ≤ (C : ℝ) * L * H := by
  classical
  obtain ⟨code, hinj, hcode⟩ := parentData_encoding I i L H w hparent hL hH
  have hpoint : ∀ k : I, (1 : ℝ) / gapLength k ≤ C / ((code k).1.val + 1 : ℕ) := by
    intro k
    rw [hcode k]
    have hg : (0 : ℝ) < gapLength k := by exact_mod_cast gapLength_pos k
    have hr : (0 : ℝ) < (w k).witness.E.card :=
      by exact_mod_cast (w k).old_block.nonempty.card_pos
    apply (div_le_div_iff₀ hg hr).mpr
    simpa only [one_mul] using (show ((w k).witness.E.card : ℝ) ≤ C * gapLength k by
      exact_mod_cast hgap k)
  calc
    _ ≤ ∑ k : I, (C : ℝ) / ((code k).1.val + 1 : ℕ) := Finset.sum_le_sum (fun k _ ↦ hpoint k)
    _ ≤ ∑ c : ChildCode L H, (C : ℝ) / (c.1.val + 1 : ℕ) :=
      sum_weight_le_of_injective code hinj
        (fun c : ChildCode L H ↦ (C : ℝ) / (c.1.val + 1 : ℕ)) (fun _ ↦ by positivity)
    _ = _ := childCode_weight_sum L H C

end Erdos421
