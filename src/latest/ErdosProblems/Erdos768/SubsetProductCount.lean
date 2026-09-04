import ErdosProblems.Erdos768.Analytic

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting form of the subset-product lemma

`subset_product_hits_identity` is stated probabilistically (over independent
uniform variables with laws `μ_j`).  For the constructive lower bound we need the
equivalent *counting* statement: choosing `s_j ∈ S_j` uniformly and independently,
the number of tuples for which no nonempty subset of the images `f_j(s_j)` sums to
`0 ∈ G` is at most `C₁·|G|/2^m · ∏|S_j|`.

This is a direct consequence of `subset_product_hits_identity`, obtained by taking
`μ_j` to be the pushforward of the uniform measure on `S_j` under `f_j`, and using
the elementary fiber-count identity
`#{s ∈ ∏ S_j : P(f∘s)} = ∏_j |S_j| · ∑_ω (∏_j μ_j(ω_j)) · [P ω]`.
-/

open scoped Classical BigOperators
open Finset

namespace Erdos768

/-
**Counting form of Lemma 3.1.**  Let `G` be a finite abelian group,
`S_j ⊆ ℕ` nonempty finite index sets, and `f_j : ℕ → G`.  If every nonprincipal
Fourier coefficient of the pushforward of uniform-on-`S_j` is at most `ρ`
(equivalently `‖∑_{q∈S_j} χ(f_j q)‖ ≤ ρ·|S_j|`), `mρ ≤ 1`, and
`2^m/|G| ≥ Λ₀`, then the number of tuples `s ∈ ∏_j S_j` for which no nonempty
subset of `{f_j(s_j)}` sums to `0` is at most `C₁·|G|/2^m·∏_j|S_j|`.
-/
theorem subset_product_count :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G] (m : ℕ)
        (S : Fin m → Finset ℕ) (f : Fin m → ℕ → G) (ρ : ℝ),
        (∀ j, (S j).Nonempty) →
        (∀ j, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ q ∈ S j, χ (f j q)‖ ≤ ρ * ((S j).card : ℝ)) →
        (m : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ m / (Fintype.card G : ℝ) →
        (((Fintype.piFinset S).filter
            (fun s => ∀ J : Finset (Fin m), J.Nonempty →
              ∑ j ∈ J, f j (s j) ≠ 0)).card : ℝ)
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ m * ∏ j, ((S j).card : ℝ) := by
  obtain ⟨ Λ₀, C₁, hΛ₀, hC₁, h ⟩ := subset_product_hits_identity;
  refine' ⟨ Λ₀, C₁, hΛ₀, hC₁, fun G _ _ m S f ρ hSne hFourier hmρ hΛ => _ ⟩;
  convert! mul_le_mul_of_nonneg_right ( h G m ( fun j => PMF.map ( f j ) ( PMF.uniformOfFinset ( S j ) ( hSne j ) ) ) ρ _ hmρ hΛ ) ( show 0 ≤ ( ∏ j : Fin m, ( S j |> Finset.card : ℝ ) ) by exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) using 1;
  · -- By definition of $μ$, we know that $(μ j (ω j)).toReal = ((S j).filter (fun q => f j q = ω j)).card / (S j).card$.
    have hμ : ∀ j ω, ((PMF.map (f j) (PMF.uniformOfFinset (S j) (hSne j)) ω).toReal) = ((S j).filter (fun q => f j q = ω)).card / (S j).card := by
      intro j ω;
      rw [ PMF.map_apply ];
      rw [ tsum_eq_sum ];
      any_goals exact S j;
      · simp +decide [ Finset.sum_ite, PMF.uniformOfFinset_apply ];
        simp +decide [ eq_comm, Finset.filter_inter ];
        ring;
      · simp +contextual [ PMF.uniformOfFinset_apply ];
    simp +decide only [hμ, mul_comm];
    simp +decide only [ne_eq, prod_div_distrib, mul_ite, mul_one, mul_zero];
    rw [ Finset.sum_congr rfl fun x hx => by rw [ mul_div_cancel₀ _ <| Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr <| hSne _ ] ] ; norm_cast;
    rw [ show ( Finset.filter ( fun s : Fin m → ℕ => ∀ J : Finset ( Fin m ), J.Nonempty → ¬∑ j ∈ J, f j ( s j ) = 0 ) ( Fintype.piFinset S ) ) = Finset.biUnion ( Finset.filter ( fun ω : Fin m → G => ∀ J : Finset ( Fin m ), J.Nonempty → ¬∑ j ∈ J, ω j = 0 ) ( Finset.univ : Finset ( Fin m → G ) ) ) ( fun ω => Finset.filter ( fun s : Fin m → ℕ => ∀ j, f j ( s j ) = ω j ) ( Fintype.piFinset S ) ) from ?_, Finset.card_biUnion ];
    · refine' Finset.sum_congr rfl fun x hx => _;
      rw [ ← Fintype.card_piFinset ];
      congr with s ; simp +decide;
      exact ⟨ fun h j => ⟨ h.1 j, h.2 j ⟩, fun h => ⟨ fun j => h j |>.1, fun j => h j |>.2 ⟩ ⟩;
    · intros ω hω ω' hω' hωω';
      simp +decide [ Finset.disjoint_left ];
      grind +splitIndPred;
    · ext; simp [Finset.mem_biUnion];
      exact ⟨ fun h => ⟨ _, h.2, h.1, fun j => rfl ⟩, by rintro ⟨ a, ha₁, ha₂, ha₃ ⟩ ; exact ⟨ ha₂, fun J hJ => by simpa only [ ha₃ ] using! ha₁ J hJ ⟩ ⟩;
  · intro j χ hχ;
    -- By definition of $μ$, we know that
    have hμ : ∑ g : G, (PMF.map (f j) (PMF.uniformOfFinset (S j) (hSne j)) g).toReal * χ g = (∑ q ∈ S j, χ (f j q)) / (S j).card := by
      simp +decide only [PMF.map_apply, PMF.uniformOfFinset_apply];
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( f j ) ( S j ) ) ) ];
      · rw [ Finset.sum_image' ];
        intro i hi; rw [ tsum_eq_sum ];
        any_goals exact S j;
        · simp +decide [ Finset.sum_ite, div_eq_mul_inv, mul_comm, mul_left_comm ];
          rw [ Finset.sum_congr rfl fun x hx => by rw [ show f j x = f j i from Finset.mem_filter.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm ];
          simp +decide [ eq_comm, Finset.filter_inter ];
        · grind;
      · intro x hx hx'; rw [ tsum_eq_single ( Classical.choose ( hSne j ) ) ] <;> simp +contextual [ Classical.choose_spec ( hSne j ) ] ;
        · exact Or.inl ( by rw [ if_neg ( by intro h; exact hx' <| h.symm ▸ Finset.mem_image_of_mem _ ( Classical.choose_spec ( hSne j ) ) ) ] ; norm_num );
        · exact fun y hy₁ hy₂ hy₃ => hx' <| hy₂ ▸ Finset.mem_image_of_mem _ hy₃;
    rw [ hμ, norm_div ];
    rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ hSne j ];
    exact hFourier j χ hχ

/-
**Fintype-indexed counting form.**  Same as `subset_product_count` but with an
arbitrary finite index type `ι` in place of `Fin m`.  Obtained from the `Fin m`
version by transporting along an equivalence `ι ≃ Fin (Fintype.card ι)`.
-/
set_option maxHeartbeats 1000000 in
theorem subset_product_count_fintype :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G]
        (ι : Type) [Fintype ι] [DecidableEq ι]
        (S : ι → Finset ℕ) (f : ι → ℕ → G) (ρ : ℝ),
        (∀ j, (S j).Nonempty) →
        (∀ j, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ q ∈ S j, χ (f j q)‖ ≤ ρ * ((S j).card : ℝ)) →
        (Fintype.card ι : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ (Fintype.card ι) / (Fintype.card G : ℝ) →
        (((Fintype.piFinset S).filter
            (fun s => ∀ J : Finset ι, J.Nonempty →
              ∑ j ∈ J, f j (s j) ≠ 0)).card : ℝ)
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ (Fintype.card ι) * ∏ j, ((S j).card : ℝ) := by
  obtain ⟨ Λ₀, C₁, hΛ₀, hC₁, h ⟩ := subset_product_count;
  refine' ⟨ Λ₀, C₁, hΛ₀, hC₁, _ ⟩;
  intro G _ _ ι _ _ S f ρ hSne hFourier hmρ hΛ;
  specialize h G ( Fintype.card ι ) ( fun k => S ( Fintype.equivFin ι |>.symm k ) ) ( fun k => f ( Fintype.equivFin ι |>.symm k ) ) ρ;
  convert! h ( fun j => hSne _ ) ( fun j χ hχ => hFourier _ _ hχ ) hmρ hΛ using 1;
  · refine' congr_arg _ ( Finset.card_bij ( fun s hs => fun k => s ( Fintype.equivFin ι |>.symm k ) ) _ _ _ ) <;> simp +decide only [ne_eq, mem_filter, Fintype.mem_piFinset, and_imp, exists_prop];
    · intro a ha₁ ha₂; refine' ⟨ fun j => ha₁ _, fun J hJ => _ ⟩ ; contrapose! ha₂; simp_all +decide ;
      use Finset.image ( fun x => ( Fintype.equivFin ι ).symm x ) J; aesop;
    · exact fun a₁ ha₁ ha₂ a₂ ha₃ ha₄ h => funext fun x => by simpa using! congr_fun h ( Fintype.equivFin ι x ) ;
    · intro b hb hb'; use fun j => b ( Fintype.equivFin ι j ) ; simp +decide ;
      refine' ⟨ _, _ ⟩;
      · exact fun a => by simpa using! hb ( Fintype.equivFin ι a ) ;
      · intro J hJ; specialize hb' ( Finset.image ( Fintype.equivFin ι ) J ) ; simp_all +decide [ Finset.Nonempty ] ;
  · rw [ ← Equiv.prod_comp ( Fintype.equivFin ι ) ] ; aesop

end Erdos768
