import ErdosProblems.Erdos134

open scoped Classical

/-- The maximum degree of a graph on `Fin n` (as a natural number). -/
noncomputable def maxDegreeFin {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup (fun v : Fin n => (G.neighborFinset v).card)

/-- For a graph `G` on `n` vertices, `h2 G` is the smallest number of edges that need
to be added to obtain a supergraph with diameter ≤ 2 that is still triangle-free
(expressed as `CliqueFree 3`). -/
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  exact sInf {k : ℕ |
    ∃ H : SimpleGraph (Fin n),
      G ≤ H ∧
      H.CliqueFree 3 ∧
      (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
      ((H.edgeFinset \ G.edgeFinset).card = k)}

/-
Positive answer (asymptotic form):

For a family of triangle-free graphs `G n` on `n` vertices, if the maximum degree is `o(n^(1/2))`
then `h₂(G n)` is `o(n^2)`, where `h₂` counts the minimum number of edges to add to make the
graph triangle-free and of diameter ≤ 2.
-/
theorem erdos_618
    (G : ∀ n : ℕ, SimpleGraph (Fin n))
    (hTriangleFree : ∀ n : ℕ, (G n).CliqueFree 3)
    (hMaxDeg :
      (fun n : ℕ => (maxDegreeFin (G n) : ℝ))
        =o[Filter.atTop] (fun n : ℕ => Real.rpow (n : ℝ) ((1 : ℝ) / 2))) :
    (fun n : ℕ => (h2 (G n) : ℝ))
      =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (2 : ℕ)) := by
  rw [ Asymptotics.isLittleO_iff ] at *;
  intro c hc_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (maxDegreeFin (G n) : ℝ) ≤ (min (1 / 10) (c / 3)) * Real.sqrt n ∧ n ≥ 1000 ∧ (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 ∧ (min (1 / 10) (c / 3)) ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ) := by
    have h_conds : ∀ᶠ n : ℕ in Filter.atTop,
      n ≥ 1000 ∧
      (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 ∧
      (min (1 / 10) (c / 3)) ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ) := by
        have h_conds : Filter.Tendsto (fun n : ℕ => 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ)) Filter.atTop (nhds 0) := by
          -- We can factor out the constant $2$ and use the fact that $(\log n)^{1/3} / n^{1/6}$ tends to $0$ as $n$ tends to infinity.
          have h_log_div_n : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{y^{1/3}}{e^{y/6}}$.
            suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ (1 / 3 : ℝ) / Real.exp (y / 6)) Filter.atTop (nhds 0) by
              have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (1 / 3 : ℝ) / Real.exp (Real.log (n : ℝ) / 6)) Filter.atTop (nhds 0) := by
                exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
              refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
            -- Let $z = \frac{y}{6}$, therefore the expression becomes $\frac{(6z)^{1/3}}{e^z}$.
            suffices h_z : Filter.Tendsto (fun z : ℝ => (6 * z) ^ (1 / 3 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
              convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 6⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
            -- We can factor out the constant $6^{1/3}$ and use the fact that $z^{1/3} / e^z$ tends to $0$ as $z$ tends to infinity.
            suffices h_factor : Filter.Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
              have h_factor : Filter.Tendsto (fun z : ℝ => 6 ^ (1 / 3 : ℝ) * (z ^ (1 / 3 : ℝ) / Real.exp z)) Filter.atTop (nhds 0) := by
                simpa using h_factor.const_mul _;
              refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with z hz using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring );
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
            refine' squeeze_zero_norm' _ this;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ Real.exp_neg ] ; exact mul_le_mul_of_nonneg_right ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le hx.le <| show ( 1 : ℝ ) / 3 ≤ 1 by norm_num ) <| by norm_num ) <| by positivity;
          simpa [ mul_div_assoc ] using h_log_div_n.const_mul 2;
        have h_conds : ∀ᶠ n : ℕ in Filter.atTop, (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 ∧ (min (1 / 10) (c / 3)) ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ) := by
          have h_conds : ∀ᶠ n : ℕ in Filter.atTop, (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 := by
            have h_conds : Filter.Tendsto (fun n : ℕ => (min (1 / 10) (c / 3)) * Real.sqrt n) Filter.atTop Filter.atTop := by
              exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
            exact h_conds.eventually_ge_atTop 4;
          filter_upwards [ h_conds, ‹Filter.Tendsto ( fun n : ℕ => 2 * Real.log ( n : ℝ ) ^ ( 1 / 3 : ℝ ) / ( n : ℝ ) ^ ( 1 / 6 : ℝ ) ) Filter.atTop ( nhds 0 ) ›.eventually ( ge_mem_nhds <| show 0 < Min.min ( 1 / 10 ) ( c / 3 ) by positivity ) ] with n hn hn' using ⟨ hn, hn' ⟩;
        filter_upwards [ h_conds, Filter.eventually_ge_atTop 1000 ] with n hn hn' using ⟨ hn', hn ⟩;
    have := hMaxDeg ( show 0 < Min.min ( 1 / 10 ) ( c / 3 ) by positivity );
    norm_num [ Real.sqrt_eq_rpow ] at *;
    exact ⟨ Max.max this.choose h_conds.choose, fun n hn => ⟨ by simpa only [ abs_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ] using this.choose_spec n ( le_trans ( le_max_left _ _ ) hn ), h_conds.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ⟩ ⟩;
  filter_upwards [ Filter.eventually_ge_atTop N ] with n hn;
  obtain ⟨h_max_deg, h_n_large, h_c_sqrt, h_c_lower⟩ := hN n hn;
  have h_binom : (n.choose (Nat.floor (5 * (min (1 / 10) (c / 3)) * n)) : ℝ) ≤ 2 ^ (10 * (min (1 / 10) (c / 3)) * n * Real.log (1 / (min (1 / 10) (c / 3)))) := by
    apply binom_entropy_bound n (min (1 / 10) (c / 3)) (by
    positivity) (by
    nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ), min_le_left ( 1 / 10 ) ( c / 3 ), min_le_right ( 1 / 10 ) ( c / 3 ) ]) (by
    exact min_le_left _ _);
  obtain ⟨G', h_le, h_free', h_diam, h_edges⟩ := theorem_1_2 (G n) n (min (1 / 10) (c / 3)) (by
  norm_num +zetaDelta at *) h_n_large (by
  positivity) (by
  exact min_le_left _ _) (by
  exact h_c_sqrt) (by
  exact h_c_lower) (by
  exact fun v => le_trans ( Nat.cast_le.mpr ( Finset.le_sup ( f := fun v => ( G n |> SimpleGraph.neighborFinset |> fun s => s v |> Finset.card ) ) ( Finset.mem_univ v ) ) ) h_max_deg) (by
  exact hTriangleFree n) (by
  convert h_binom using 1);
  have h2_le_k : h2 (G n) ≤ (G'.edgeFinset \ (G n).edgeFinset).card := by
    exact csInf_le ⟨ 0, fun k hk => Nat.zero_le _ ⟩ ⟨ G', h_le, h_free', h_diam, rfl ⟩;
  norm_num [ Norm.norm ] at *;
  exact le_trans ( Nat.cast_le.mpr h2_le_k ) ( le_trans ( Nat.cast_le.mpr ( Finset.card_le_card ( Finset.sdiff_subset ) ) ) ( by norm_num at *; nlinarith [ min_le_left ( 1 / 10 ) ( c / 3 ), min_le_right ( 1 / 10 ) ( c / 3 ) ] ) )

#print axioms erdos_618
-- 'erdos_618' depends on axioms: [propext, Classical.choice, Quot.sound]
