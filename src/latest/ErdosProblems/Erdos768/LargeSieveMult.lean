import ErdosProblems.Erdos768.LargeSieve

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Multiplicative large sieve: arithmetic reduction

We reduce the Bombieri–Davenport multiplicative large sieve to the additive
(Gallagher) large sieve proven in `LargeSieve.lean`, via Gauss sums, character
orthogonality, and Farey spacing.
-/

open scoped Classical BigOperators Real
open Finset Filter

namespace Erdos768LS

/-
**Plancherel for the `ZMod` DFT.**
-/
set_option maxHeartbeats 1600000 in
lemma plancherel_dft (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    ∑ k : ZMod q, ‖ZMod.dft Φ k‖ ^ 2 = q * ∑ a : ZMod q, ‖Φ a‖ ^ 2 := by
  -- By definition of DFT, we have:
  have h_dft_def : ∀ k : ZMod q, ZMod.dft Φ k = ∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a)) := by
    simp +decide [ ZMod.dft_apply, mul_comm ];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ k : ZMod q, ‖∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))‖ ^ 2 = ∑ a : ZMod q, ∑ b : ZMod q, Φ a * starRingEnd ℂ (Φ b) * ∑ k : ZMod q, ZMod.stdAddChar (-(k * a)) * ZMod.stdAddChar (k * b) := by
    have h_fubini : ∀ k : ZMod q, ‖∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))‖ ^ 2 = ∑ a : ZMod q, ∑ b : ZMod q, Φ a * starRingEnd ℂ (Φ b) * ZMod.stdAddChar (-(k * a)) * ZMod.stdAddChar (k * b) := by
      intro k
      have h_fubini : ‖∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))‖ ^ 2 = (∑ a : ZMod q, Φ a * ZMod.stdAddChar (-(k * a))) * (∑ b : ZMod q, starRingEnd ℂ (Φ b) * ZMod.stdAddChar (k * b)) := by
        have h_fubini : ∀ z : ℂ, ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
          norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        convert! h_fubini _ using 2;
        simp +decide [ ZMod.stdAddChar ];
        simp +decide [ ZMod.toCircle, Complex.ext_iff ];
        simp +decide [ AddCircle.toCircle_addChar ];
        simp +decide [ ZMod.toAddCircle, AddCircle.toCircle_neg ];
        rw [ Finset.sum_add_distrib ];
      exact h_fubini.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
    simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  -- By orthogonality of the additive characters, we have:
  have h_orthogonality : ∀ a b : ZMod q, ∑ k : ZMod q, ZMod.stdAddChar (-(k * a)) * ZMod.stdAddChar (k * b) = if a = b then q else 0 := by
    intro a b; split_ifs with h; simp_all +decide [ ← ZMod.stdAddChar.map_add_eq_mul ] ;
    convert! AddChar.sum_mulShift ( b - a ) ( ZMod.isPrimitive_stdAddChar q ) using 1;
    · exact Finset.sum_congr rfl fun _ _ => by rw [ ← ZMod.stdAddChar.map_add_eq_mul ] ; ring_nf;
    · simp +decide [ sub_eq_zero ];
      aesop;
  simp_all +decide [ Finset.mul_sum _ _ _, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
  norm_cast at * ; simp_all +decide [ mul_comm ]

/-
**Gauss sum norm.**  For a primitive Dirichlet character `χ` mod `q`, the
Gauss sum with the standard additive character has squared norm `q`.
-/
set_option maxHeartbeats 1600000 in
lemma gauss_norm (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = q := by
  by_contra h_contra;
  have h_plancherel : ∑ k : ZMod q, ‖(ZMod.dft (fun a => χ a) k)‖ ^ 2 = q * ∑ a : ZMod q, ‖χ a‖ ^ 2 := by
    convert! plancherel_dft q ( fun a => χ a ) using 1;
  -- By definition of $gaussSum$, we know that $‖(ZMod.dft (fun a => χ a) k)‖^2 = ‖χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar‖^2$.
  have h_gauss_sum : ∀ k : ZMod q, ‖(ZMod.dft (fun a => χ a) k)‖ ^ 2 = ‖χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar‖ ^ 2 := by
    intro k; rw [ DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hχ k ] ;
  -- By definition of $gaussSum$, we know that $‖χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar‖^2 = ‖gaussSum χ ZMod.stdAddChar‖^2$ if $-k$ is a unit, and $0$ otherwise.
  have h_gauss_sum_unit : ∀ k : ZMod q, ‖χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar‖ ^ 2 = if IsUnit (-k) then ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 else 0 := by
    intro k; split_ifs <;> simp_all +decide [ IsUnit ] ;
    · obtain ⟨ u, hu ⟩ := ‹_›; simp +decide [ ← hu, DirichletCharacter ] ;
    · exact Or.inl <| MulChar.map_nonunit _ <| by rintro ⟨ u, hu ⟩ ; exact ‹∀ x : ( ZMod q ) ˣ, ¬ ( x : ZMod q ) = -k› u <| by aesop;
  -- By definition of $gaussSum$, we know that $‖χ a‖^2 = if IsUnit a then 1 else 0$.
  have h_gauss_sum_norm : ∀ a : ZMod q, ‖χ a‖ ^ 2 = if IsUnit a then 1 else 0 := by
    intro a; split_ifs <;> simp_all +decide [ DirichletCharacter ] ;
    · obtain ⟨ u, rfl ⟩ := ‹IsUnit a›; simp +decide ;
    · grind +suggestions;
  simp_all +decide [ Finset.sum_ite ];
  exact h_contra ( mul_left_cancel₀ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Finset.card_pos.mpr ⟨ 1, by aesop ⟩ : ( Finset.card ( Finset.filter ( fun x : ZMod q => IsUnit x ) Finset.univ ) : ℝ ) ≠ 0 ) <| by linarith )

/-- The Farey point `val(b)/q` attached to a residue `b : ZMod q`. -/
noncomputable def frac (q : ℕ) (b : ZMod q) : ℝ := (ZMod.val b : ℝ) / q

/-
Casting: `e(n · val(b)/q) = stdAddChar (n·b)`.
-/
lemma e_frac (q n : ℕ) [NeZero q] (b : ZMod q) :
    e ((n : ℝ) * frac q b) = ZMod.stdAddChar ((n : ZMod q) * b) := by
  simp +decide [ e, frac, ZMod.stdAddChar ];
  convert! Complex.exp_eq_exp_iff_exists_int.mpr _ using 1;
  use (n * b.val - (n * b).val) / q;
  cases q <;> simp_all +decide [ ZMod.natCast_val ];
  rw [ Int.cast_div ] <;> norm_num ; ring_nf;
  · simp +decide [ ZMod.cast, ZMod.val ] ; ring;
  · erw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
  · norm_cast

/-
The inverse of a primitive character is primitive.
-/
lemma isPrimitive_inv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  by_contra h_contra;
  obtain ⟨d, hd, hcd⟩ : ∃ d, d ∣ q ∧ d < q ∧ χ.FactorsThrough d := by
    obtain ⟨d, hd, hcd⟩ : ∃ d, d ∣ q ∧ d < q ∧ χ⁻¹.FactorsThrough d := by
      contrapose! h_contra;
      refine' le_antisymm _ _;
      · exact Nat.sInf_le ⟨ dvd_rfl, by simp +decide ⟩;
      · grind +suggestions;
    use d;
    simp_all +decide [ DirichletCharacter.FactorsThrough ];
    obtain ⟨ χ₀, hχ₀ ⟩ := hcd.2; use χ₀⁻¹; ext; simp +decide [ ← hχ₀ ] ;
  contrapose! hχ; simp_all +decide ;
  exact ne_of_lt ( lt_of_le_of_lt ( csInf_le' hcd.2 ) hcd.1 )

/-
**Separability.**  `∑_b χ⁻¹(b) S(val b/q) = τ(χ⁻¹) · ∑_n a_n χ(n)`.
-/
lemma gauss_sep (N q : ℕ) [NeZero q] (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∑ b : ZMod q, χ⁻¹ b * S N a (frac q b))
      = gaussSum χ⁻¹ ZMod.stdAddChar * ∑ n ∈ Finset.Icc 1 N, a n * χ n := by
  -- Apply the separability lemma to each term in the sum.
  have h_sep : ∀ n ∈ Finset.Icc 1 N, ∑ b : ZMod q, (χ⁻¹ b) * (ZMod.stdAddChar ((n : ZMod q) * b)) = (χ n) * (gaussSum χ⁻¹ ZMod.stdAddChar) := by
    intro n hn;
    have := @gaussSum_mulShift_of_isPrimitive;
    convert! this ZMod.stdAddChar ( isPrimitive_inv q χ hχ ) n using 1;
    simp +decide [ mul_comm ];
  -- Apply the separability lemma to each term in the sum to factor out the Gauss sum.
  have h_factor : ∑ b : ZMod q, (χ⁻¹ b) * (S N a (frac q b)) = ∑ n ∈ Finset.Icc 1 N, a n * (∑ b : ZMod q, (χ⁻¹ b) * (ZMod.stdAddChar ((n : ZMod q) * b))) := by
    simp +decide only [S, mul_sum _ _ _];
    rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; rw [ e_frac ] ; ring;
  rw [ h_factor, Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun x hx => by rw [ h_sep x hx ] ; ring;

/-
**Per-character Gauss identity.**  `‖∑_b χ⁻¹(b) S(val b/q)‖² = q·‖∑_n a_nχ(n)‖²`.
-/
lemma gauss_identity (N q : ℕ) [NeZero q] (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ‖∑ b : ZMod q, χ⁻¹ b * S N a (frac q b)‖ ^ 2
      = q * ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 := by
  rw [ gauss_sep, norm_mul, mul_pow ];
  · rw [ gauss_norm q χ⁻¹ ( isPrimitive_inv q χ hχ ) ];
  · assumption

/-
**Character orthogonality (dual sum).**  For any `w : ZMod q → ℂ`,
`∑_χ ‖∑_b χ⁻¹(b) w(b)‖² = φ(q) · ∑_{b unit} ‖w(b)‖²`.
-/
lemma orthogonality_sum (q : ℕ) [NeZero q] (w : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * w b‖ ^ 2)
      = (Nat.totient q : ℝ) * ∑ b : (ZMod q)ˣ, ‖w (b : ZMod q)‖ ^ 2 := by
  -- Expand ‖z‖² = z * conj z and note χ⁻¹ b has conj = χ b on units and both are 0 on non-units.
  have h_expand : ∀ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * w b‖ ^ 2 = ∑ b : ZMod q, ∑ b' : ZMod q, χ⁻¹ b * χ b' * w b * starRingEnd ℂ (w b') := by
    intro χ
    have h_expand : ‖∑ b : ZMod q, χ⁻¹ b * w b‖ ^ 2 = (∑ b : ZMod q, χ⁻¹ b * w b) * (∑ b' : ZMod q, χ b' * starRingEnd ℂ (w b')) := by
      have h_expand : starRingEnd ℂ (∑ b : ZMod q, χ⁻¹ b * w b) = ∑ b : ZMod q, χ b * starRingEnd ℂ (w b) := by
        rw [ map_sum ] ; congr ; ext x ; by_cases hx : IsUnit x <;> simp_all +decide ;
        · -- Since χ is a Dirichlet character, χ(x) is a root of unity, so its conjugate is its inverse.
          have h_root_of_unity : χ x * starRingEnd ℂ (χ x) = 1 := by
            rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
            obtain ⟨ u, rfl ⟩ := hx; norm_num [ χ.map_pow ] ;
          rw [ show χ⁻¹ x = ( χ x ) ⁻¹ from ?_ ];
          · rw [map_inv₀, inv_eq_of_mul_eq_one_left h_root_of_unity]
            exact Or.inl rfl
          · convert! χ.inv_apply x;
            cases hx ; aesop;
        · erw [ χ.map_nonunit hx, χ⁻¹.map_nonunit hx ] ; norm_num;
      rw [ ← h_expand, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow ];
    exact h_expand.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
  -- For the inner character sum, use the orthogonality relation:
  have h_inner : ∀ b b' : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ b' = if IsUnit b ∧ IsUnit b' ∧ b = b' then (q.totient : ℂ) else 0 := by
    intro b b'
    by_cases hb : IsUnit b
    by_cases hb' : IsUnit b'
    generalize_proofs at *;
    · obtain ⟨ u, rfl ⟩ := hb
      obtain ⟨ u', rfl ⟩ := hb'
      simp +decide;
      convert! DirichletCharacter.sum_char_inv_mul_char_eq ℂ ( show IsUnit ( u' : ZMod q ) from Units.isUnit _ ) u using 1;
      · refine' Finset.sum_bij ( fun χ _ => χ⁻¹ ) _ _ _ _ <;> simp +decide [ mul_comm ];
        · exact fun b => ⟨ b⁻¹, inv_inv b ⟩;
        · simp +decide [ mul_comm, MulChar.inv_apply ];
      · simp +decide only [eq_comm];
    · simp_all +decide [ DirichletCharacter ];
      rw [ Finset.sum_eq_zero ] ; intros ; simp_all +decide [ MulChar.map_nonunit ];
    · simp +decide [ hb, MulChar.map_nonunit ]
  generalize_proofs at *;
  -- Apply the orthogonality relation to rewrite the sum.
  have h_sum : ∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q, ∑ b' : ZMod q, χ⁻¹ b * χ b' * w b * starRingEnd ℂ (w b') = ∑ b : ZMod q, ∑ b' : ZMod q, (if IsUnit b ∧ IsUnit b' ∧ b = b' then (q.totient : ℂ) else 0) * w b * starRingEnd ℂ (w b') := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_comm ] ; simp +decide [ ← Finset.sum_mul, h_inner ] ;
  generalize_proofs at *;
  convert! congr_arg Complex.re h_sum using 1;
  · rw [ ← Finset.sum_congr rfl fun _ _ => h_expand _ ] ; norm_cast;
  · rw [ Finset.sum_congr rfl fun x hx => Finset.sum_eq_single x ( fun y hy => ?_ ) ( ?_ ) ] <;> simp +decide;
    · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : ( ZMod q ) ˣ => ( x : ZMod q ) ) Finset.univ ) ) ] <;> norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      · rw [ Finset.sum_image ] <;> norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        · norm_num [ Complex.normSq, Complex.sq_norm, Finset.mul_sum _ _ _ ] ; ring_nf;
        · exact fun x y h => Units.ext h;
      · intro x hx; split_ifs <;> simp_all +decide [ IsUnit ] ;
    · lia

/-
**Per-modulus bound.**  `(q/φ(q)) ∑_{χ prim} ‖T(χ)‖² ≤ ∑_{b unit} ‖S(val b/q)‖²`.
-/
lemma per_q_bound (N q : ℕ) [NeZero q] (a : ℕ → ℂ) :
    (q : ℝ) / (Nat.totient q) * ∑ χ : DirichletCharacter ℂ q,
        (if χ.IsPrimitive then ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
      ≤ ∑ b : (ZMod q)ˣ, ‖S N a (frac q (b : ZMod q))‖ ^ 2 := by
  rw [ div_mul_eq_mul_div, div_le_iff₀ ];
  · convert! Finset.sum_le_sum fun χ _ => ?_ using 1;
    rotate_left;
    convert! orthogonality_sum q ( fun b => S N a ( frac q b ) ) |> Eq.symm using 1;
    rw [ mul_comm ];
    use fun χ => if χ.IsPrimitive then q * ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0;
    · infer_instance;
    · split_ifs <;> simp_all +decide [ gauss_identity ];
    · rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; split_ifs <;> ring;
  · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) )

/-
**Additive large sieve, indexed by an arbitrary finite type.**
-/
theorem additive_large_sieve_indexed (N : ℕ) (a : ℕ → ℂ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ι : Type*) [Fintype ι] (x : ι → ℝ) (hmem : ∀ i, x i ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : ι, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k:ℝ)|) :
    ∑ i, ‖S N a (x i)‖ ^ 2 ≤ (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := by
    exact ⟨ Fintype.equivFin ι ⟩;
  convert! additive_large_sieve N a δ hδ0 hδ1 ( Fintype.card ι ) ( fun i => x ( e.symm i ) ) ?_ ?_ using 1;
  · conv_lhs => rw [ ← Equiv.sum_comp e.symm ] ;
  · exact fun i => hmem _;
  · exact fun i j hij k => hsp _ _ ( by simpa [ e.symm.injective.eq_iff ] using! hij ) k

/-- The coprime residues in `[0,q)`. -/
def coprimeRes (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun m => Nat.Coprime m q)

/-
Bridge: a sum over `(ZMod q)ˣ` equals a sum over coprime residues.
-/
lemma units_sum_eq_coprime (q : ℕ) [NeZero q] (f : ℝ → ℝ) :
    (∑ b : (ZMod q)ˣ, f (frac q (b : ZMod q)))
      = ∑ m ∈ coprimeRes q, f ((m : ℝ) / q) := by
  have h_reindex : Finset.image (fun b : (ZMod q)ˣ => (b : ZMod q).val) (Finset.univ : Finset (ZMod q)ˣ) = coprimeRes q := by
    ext m;
    simp +zetaDelta at *;
    constructor;
    · rintro ⟨ a, rfl ⟩ ; exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( ZMod.val_lt _ ), ZMod.val_coe_unit_coprime _ ⟩ ;
    · intro hm
      use ZMod.unitOfCoprime m (by
      exact Finset.mem_filter.mp hm |>.2)
      generalize_proofs at *;
      simp +decide [ ZMod.val_natCast, Nat.mod_eq_of_lt ( show m < q from Finset.mem_range.mp ( Finset.mem_filter.mp hm |>.1 ) ) ];
  rw [ ← h_reindex, Finset.sum_image ];
  · convert! rfl;
  · intro b hb b' hb' h; simp_all +decide ;
    exact Units.ext ( ZMod.val_injective q h )

/-
**Farey spacing (natural-number form).**  Distinct reduced fractions `m/q`,
`m'/q'` with denominators `≤ Q` are `1/Q²`-spaced mod `1`.
-/
lemma farey_spacing_nat (Q q q' m m' : ℕ) (hq1 : 1 ≤ q) (hqQ : q ≤ Q)
    (hq'1 : 1 ≤ q') (hq'Q : q' ≤ Q) (hm : m < q) (hm' : m' < q')
    (hcop : Nat.Coprime m q) (hcop' : Nat.Coprime m' q')
    (hne : q ≠ q' ∨ m ≠ m') (k : ℤ) :
    (1:ℝ)/(Q:ℝ)^2 ≤ |(m : ℝ)/q - (m' : ℝ)/q' - (k:ℝ)| := by
  -- By multiplying both sides of the inequality by $q * q'$, we get $|m * q' - m' * q - k * q * q'| \geq 1$.
  have h_mul : |(m : ℝ) * q' - (m' : ℝ) * q - k * (q * q')| ≥ 1 := by
    contrapose! hne; norm_cast at *; simp_all +decide [ sub_eq_iff_eq_add ] ;
    -- From the equality part, we have $m * q' = m' * q + k * q * q'$.
    -- Since $q$ and $q'$ are coprime, it follows that $q \mid q'$ and $q' \mid q$, hence $q = q'$.
    have h_eq : q = q' := by
      have h_eq : q ∣ q' ∧ q' ∣ q := by
        have h_div : q ∣ (m * q') ∧ q' ∣ (m' * q) := by
          rw [ Int.subNatNat_eq_coe ] at hne ; exact ⟨ Int.natCast_dvd_natCast.mp ⟨ k * q' + m', by push_cast at *; linarith ⟩, Int.natCast_dvd_natCast.mp ⟨ -k * q + m, by push_cast at *; linarith ⟩ ⟩ ;
        exact ⟨ hcop.symm.dvd_of_dvd_mul_left h_div.1, hcop'.symm.dvd_of_dvd_mul_left h_div.2 ⟩;
      exact Nat.dvd_antisymm h_eq.left h_eq.right;
    simp_all +decide [ Int.subNatNat_eq_coe ];
    nlinarith [ show k = 0 by nlinarith ];
  field_simp;
  rw [ abs_div, div_le_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ mul_comm ];
  · exact le_trans ( by norm_cast; nlinarith ) ( mul_le_mul_of_nonneg_right h_mul ( sq_nonneg _ ) );
  · nlinarith;
  · exact ⟨ hq1, hq'1 ⟩

/-
**Farey sum bound.**  Summing `‖S‖²` over all reduced fractions with
denominator in `[1,Q]` is bounded via the additive large sieve with `δ = 1/Q²`.
-/
lemma farey_sum_bound (N Q : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ m ∈ coprimeRes q, ‖S N a ((m : ℝ) / q)‖ ^ 2
      ≤ ((Q:ℝ)^2 + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  set s := (Finset.Icc 1 Q).sigma (fun q => coprimeRes q) with hs_def
  set ι := {i : Σ _ : ℕ, ℕ // i ∈ s} with hι_def;
  -- Apply the indexed additive large sieve with `δ = 1/Q^2`.
  have h_apply : (∑ i : ι, ‖S N a ((i.val.2 : ℝ) / (i.val.1 : ℝ))‖ ^ 2) ≤ ((1 : ℝ) / (Q : ℝ) ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) + 4 * Real.pi * N * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
    convert! additive_large_sieve_indexed N a ( 1 / ( Q : ℝ ) ^ 2 ) ?_ ?_ ι ( fun i => ( i.val.2 : ℝ ) / ( i.val.1 : ℝ ) ) ?_ ?_ using 1;
    · ring;
    · positivity;
    · exact div_le_self zero_le_one ( mod_cast Nat.one_le_pow _ _ hQ );
    · simp +zetaDelta at *;
      exact fun a ha₁ ha₂ ha₃ => ⟨ by positivity, by rw [ div_lt_one ( by positivity ) ] ; exact_mod_cast Finset.mem_range.mp ( Finset.mem_filter.mp ha₃ |>.1 ) ⟩;
    · simp +zetaDelta at *;
      intro a ha₁ ha₂ ha₃ b hb₁ hb₂ hb₃ hab k; convert! farey_spacing_nat Q a.fst b.fst a.snd b.snd ha₁ ha₂ hb₁ hb₂ ( Finset.mem_range.mp ( Finset.mem_filter.mp ha₃ |>.1 ) ) ( Finset.mem_range.mp ( Finset.mem_filter.mp hb₃ |>.1 ) ) ( Finset.mem_filter.mp ha₃ |>.2 ) ( Finset.mem_filter.mp hb₃ |>.2 ) ?_ k using 1 ;
      · ring;
      · exact not_and_or.mp fun h => hab <| by cases a; cases b; aesop;
  convert! h_apply using 1;
  · convert! Finset.sum_sigma' ( Finset.Icc 1 Q ) ( fun q => coprimeRes q ) fun q m => ‖S N a ( m / q : ℝ )‖ ^ 2 using 1;
    refine' Finset.sum_bij ( fun x hx => x.val ) _ _ _ _ <;> aesop;
  · norm_num ; ring

/-
**Multiplicative large sieve (Bombieri–Davenport).**  The exact statement of
`Erdos768.multiplicative_large_sieve`.
-/
theorem mult_large_sieve_final :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (Nat.totient q) *
          ∑ χ : DirichletCharacter ℂ q,
            (if DirichletCharacter.IsPrimitive χ then
              ‖∑ n ∈ Finset.Icc 1 N, a n * χ n‖ ^ 2 else 0)
        ≤ C * ((N : ℝ) + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  refine' ⟨ 4 * Real.pi, by positivity, fun N Q a => _ ⟩;
  by_cases hQ : 1 ≤ Q;
  · refine' le_trans _ ( le_trans ( farey_sum_bound N Q hQ a ) _ );
    · refine' Finset.sum_le_sum fun q hq => _;
      convert! per_q_bound N q a using 1;
      convert! units_sum_eq_coprime q ( fun x => ‖S N a x‖ ^ 2 ) |> Eq.symm using 1;
      exact ⟨ by linarith [ Finset.mem_Icc.mp hq ] ⟩;
    · exact mul_le_mul_of_nonneg_right ( by nlinarith [ Real.pi_gt_three, show ( Q : ℝ ) ^ 2 ≥ 1 by norm_cast; nlinarith ] ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ );
  · interval_cases Q ; norm_num;
    exact mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )

end Erdos768LS
