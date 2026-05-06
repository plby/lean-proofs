/-
Bhowmick managed to construct a set of $n$ points in $\mathbb{R}^2$ such that $\lfloor \frac{n}{4} \rfloor$ distances occur at least $n+1$ times.

K. Bhowmick, A problem of Erdős about rich distances. arXiv:2407.01174 (2024).

He thereby solved Erdős Problem #756 (https://www.erdosproblems.com/756). Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) managed to formalize his proof, and the result can be found below.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
The number of times a distance `d` appears in a set of points `P`. We divide by 2 because `offDiag` counts both `(x, y)` and `(y, x)`.
-/
def distance_count (P : Finset ℂ) (d : ℝ) : ℕ :=
  (P.offDiag.filter (fun (x, y) => dist x y = d)).card / 2

/-
The set of vertices of a regular `m`-gon, represented as the `m`-th roots of unity in the complex plane.
-/
def regular_polygon (m : ℕ) : Finset ℂ :=
  Polynomial.nthRootsFinset m (1 : ℂ)

/-
The distance between the vertex 1 and the vertex corresponding to the `k`-th root of unity in a regular `m`-gon.
-/
def regular_polygon_distance (m k : ℕ) : ℝ :=
  dist 1 (Complex.exp (2 * Real.pi * Complex.I * k / m))

/-
The primitive `m`-th root of unity `exp(2 * pi * I / m)`.
-/
def zeta (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

/-
The number of vertices in a regular `m`-gon is `m`.
-/
lemma regular_polygon_card (m : ℕ) (hm : m ≥ 1) : (regular_polygon m).card = m := by
  unfold regular_polygon
  exact (Complex.isPrimitiveRoot_exp m (by omega)).card_nthRootsFinset

/-
For any vertex `x` in a regular `m`-gon, the vertices `y` at distance corresponding to step `k` are exactly `x * zeta^k` and `x * zeta^(m-k)`.
-/
lemma neighbors_at_distance_eq (m k : ℕ) (hm : m ≥ 3) (hk2 : k ≤ (m - 1) / 2) (x : ℂ) (hx : x ∈ regular_polygon m) :
  (regular_polygon m).filter (fun y => dist x y = regular_polygon_distance m k) =
    {x * (zeta m) ^ k, x * (zeta m) ^ (m - k)} := by
      ext y;
      constructor <;> intro hy <;> simp_all +decide [ regular_polygon, zeta, Polynomial.nthRootsFinset ];
      · -- Since $x$ and $y$ are $m$-th roots of unity, we have $y = x \cdot \zeta^j$ for some integer $j$.
        obtain ⟨j, hj⟩ : ∃ j : ℤ, y = x * Complex.exp (2 * Real.pi * Complex.I * j / m) := by
          -- Since $x$ and $y$ are $m$-th roots of unity, we can write $y = x \cdot \zeta$ for some $\zeta$ on the unit circle.
          obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, y = x * ζ ∧ ζ ^ m = 1 := by
            simp_all +decide [ Polynomial.nthRoots ];
            refine' ⟨ y / x, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add, mul_div_cancel₀, show x ≠ 0 from by rintro rfl; norm_num [ show m ≠ 0 by linarith ] at hx ];
            rw [ div_pow, hy.1, hx.2, div_one ];
          -- Since ζ is an m-th root of unity, we can write ζ = exp(2πiθ) for some real number θ.
          obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ζ = Complex.exp (2 * Real.pi * Complex.I * θ) := by
            rw [ ← Complex.norm_mul_exp_arg_mul_I ζ ];
            exact ⟨ ζ.arg / ( 2 * Real.pi ), by push_cast; rw [ show ‖ζ‖ = 1 by have := congr_arg Norm.norm hζ.2; norm_num at this; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop ] ; ring_nf; norm_num [ mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ] ⟩;
          simp_all +decide [ ← Complex.exp_nat_mul ];
          rw [ Complex.exp_eq_one_iff ] at hζ; obtain ⟨ j, hj ⟩ := hζ.2; exact ⟨ j, Or.inl <| congr_arg Complex.exp <| by rw [ eq_div_iff <| Nat.cast_ne_zero.mpr <| by positivity ] ; linear_combination' hj ⟩ ;
        -- Since $|1 - \exp(2\pi i j / m)| = |1 - \exp(2\pi i k / m)|$, we have $\cos(2\pi j / m) = \cos(2\pi k / m)$.
        have h_cos_eq : Real.cos (2 * Real.pi * j / m) = Real.cos (2 * Real.pi * k / m) := by
          have h_cos_eq : ‖1 - Complex.exp (2 * Real.pi * Complex.I * j / m)‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * k / m)‖ := by
            simp_all +decide [ dist_eq_norm, regular_polygon_distance ];
            simp_all +decide [← hy.2];
            field_simp;
            norm_num [ Polynomial.nthRoots ] at *;
            rw [ show ‖x‖ = 1 by simpa [ show m ≠ 0 by linarith, pow_eq_one_iff_of_nonneg ] using congr_arg Norm.norm ( eq_of_sub_eq_zero hx.2 ) ] ; ring;
          norm_num [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im ] at *;
          rw [ Real.sqrt_inj ] at h_cos_eq <;> nlinarith [ Real.cos_sq' ( 2 * Real.pi * j / m ), Real.cos_sq' ( 2 * Real.pi * k / m ) ];
        -- Since $\cos(2\pi j / m) = \cos(2\pi k / m)$, we have $j \equiv \pm k \pmod{m}$.
        have h_j_eq : ∃ t : ℤ, j = k + t * m ∨ j = -k + t * m := by
          rw [ Real.cos_eq_cos_iff ] at h_cos_eq;
          rcases h_cos_eq with ⟨ t, h_cos_eq | h_cos_eq ⟩ <;> [ exact ⟨ -t, Or.inl <| by rw [ ← @Int.cast_inj ℝ ] ; push_cast; nlinarith [ Real.pi_pos, mul_div_cancel₀ ( 2 * Real.pi * ( k : ℝ ) ) ( by positivity : ( m : ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi * ( j : ℝ ) ) ( by positivity : ( m : ℝ ) ≠ 0 ) ] ⟩ ; exact ⟨ t, Or.inr <| by rw [ ← @Int.cast_inj ℝ ] ; push_cast; nlinarith [ Real.pi_pos, mul_div_cancel₀ ( 2 * Real.pi * ( k : ℝ ) ) ( by positivity : ( m : ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi * ( j : ℝ ) ) ( by positivity : ( m : ℝ ) ≠ 0 ) ] ⟩ ];
        rcases h_j_eq with ⟨ t, rfl | rfl ⟩ <;> norm_num [ hj, ← Complex.exp_nat_mul, ← Complex.exp_int_mul ] <;> ring_nf <;> norm_num [ show m ≠ 0 by positivity ] ;
        · exact Or.inl <| Or.inl <| Complex.exp_eq_exp_iff_exists_int.mpr ⟨ t, by ring ⟩;
        · rw [ Nat.cast_sub ( by omega ) ] ; ring_nf ; norm_num [ show m ≠ 0 by positivity ] ;
          exact Or.inr <| Or.inl <| Complex.exp_eq_exp_iff_exists_int.mpr ⟨ t - 1, by push_cast; ring ⟩;
      · rcases hy with ( rfl | rfl ) <;> simp_all +decide [ ← Complex.exp_nat_mul ];
        · unfold regular_polygon_distance; simp_all +decide [ dist_eq_norm, Polynomial.nthRoots ] ; ring_nf;
          rw [ ← Complex.exp_nat_mul ] ; ring_nf ;
          norm_num [ show x ^ m = 1 by linear_combination' hx.2, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_three.trans_le hm ) ];
          norm_num [ show Complex.exp ( Complex.I * ( Real.pi * ( k * 2 ) ) ) = 1 by rw [ Complex.exp_eq_one_iff ] ; use k; push_cast; ring ];
          rw [ show x - x * Complex.exp _ = x * ( 1 - Complex.exp _ ) by ring, norm_mul ] ;
          have := congr_arg Norm.norm ( eq_add_of_sub_eq' hx.2 ) ; norm_num at this ; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop;
        · constructor;
          · simp_all +decide [ Polynomial.nthRoots ];
            rw [ mul_pow, ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff.mpr ⟨ ( m - k ), ?_ ⟩ ] ; ring_nf;
            · linear_combination' hx.2;
            · rw [ Nat.cast_sub ( by omega ) ] ; simp +decide [mul_comm, mul_left_comm,
              div_eq_mul_inv, show m ≠ 0 by linarith];
          · unfold regular_polygon_distance;
            rw [ Nat.cast_sub ( by omega ) ] ; ring_nf;
            norm_num [ Complex.dist_eq, Complex.norm_exp, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_three.trans_le hm ) ];
            rw [ show x - x * Complex.exp _ = x * ( 1 - Complex.exp _ ) by ring, norm_mul ];
            norm_num [ Polynomial.nthRoots ] at hx;
            rw [ show ‖x‖ = 1 by simpa [ show m ≠ 0 by linarith, pow_eq_one_iff_of_nonneg ] using congr_arg Norm.norm ( sub_eq_zero.mp hx.2 ) ] ; ring_nf;
            norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
            norm_num [ mul_two, Real.cos_sub, Real.sin_sub ]

/-
In a regular $m$-gon, the distance corresponding to a step of size $k$ appears $m$ times, for $1 \le k \le (m-1)/2$.
-/
lemma mgon_helper (m k : ℕ) (hm : m ≥ 3) (hk1 : 1 ≤ k) (hk2 : k ≤ (m - 1) / 2) :
  distance_count (regular_polygon m) (regular_polygon_distance m k) = m := by
    -- By `neighbors_at_distance_eq`, each vertex has exactly two neighbors at distance `regular_polygon_distance m k`.
    have h_degree (x : ℂ) (hx : x ∈ regular_polygon m) : (Finset.filter (fun y => dist x y = regular_polygon_distance m k) (regular_polygon m)).card = 2 := by
      convert congr_arg Finset.card ( neighbors_at_distance_eq m k hm hk2 x hx ) using 2;
      rw [ Finset.card_pair ] ; norm_num [ zeta ];
      constructor;
      · rw [ ← Complex.exp_nat_mul, ← Complex.exp_nat_mul ] ; rw [ Complex.exp_eq_exp_iff_exists_int ] ; rintro ⟨ l, hl ⟩ ; rcases l with ⟨ _ | l ⟩ <;> norm_num [ Complex.ext_iff ] at *;
        · omega;
        · nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 1 by norm_cast, show ( m : ℝ ) ≥ k + 1 by norm_cast; omega, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( m : ℝ ) ≠ 0 ), mul_pos Real.pi_pos ( show ( 0 : ℝ ) < m by positivity ) ];
        · rw [ Nat.cast_sub ( by omega ) ] at hl ; nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 1 by norm_cast, show ( m : ℝ ) ≥ 3 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( m : ℝ ) ≠ 0 ), mul_pos Real.pi_pos ( show ( m : ℝ ) > 0 by positivity ) ];
      · intro h; simp_all +decide [ regular_polygon ] ;
        cases m <;> norm_num at *;
    -- Summing the degrees of all vertices gives us twice the number of edges.
    have h_sum_degrees : (Finset.offDiag (regular_polygon m)).filter (fun (x, y) => dist x y = regular_polygon_distance m k) = Finset.biUnion (regular_polygon m) (fun x => Finset.image (fun y => (x, y)) (Finset.filter (fun y => dist x y = regular_polygon_distance m k) (regular_polygon m))) := by
      -- To prove equality, we show each set is a subset of the other.
      apply Finset.ext
      intro p
      simp [Finset.mem_biUnion, Finset.mem_image];
      constructor <;> intro h;
      · exact ⟨ p.1, h.1.1, p.2, ⟨ h.1.2.1, h.2 ⟩, rfl ⟩;
      · rcases h with ⟨ x, hx, y, ⟨ hy, hxy ⟩, rfl ⟩ ; specialize h_degree x hx ; simp_all +decide [ Finset.card_eq_two ] ;
        obtain ⟨ z, w, hne, heq ⟩ := h_degree; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
        rintro rfl; simp_all +decide [ regular_polygon_distance ] ;
    -- Since each vertex has degree 2, the total number of edges is $m$.
    have h_total_edges : (Finset.offDiag (regular_polygon m)).filter (fun (x, y) => dist x y = regular_polygon_distance m k) = Finset.biUnion (regular_polygon m) (fun x => Finset.image (fun y => (x, y)) (Finset.filter (fun y => dist x y = regular_polygon_distance m k) (regular_polygon m))) ∧ (Finset.biUnion (regular_polygon m) (fun x => Finset.image (fun y => (x, y)) (Finset.filter (fun y => dist x y = regular_polygon_distance m k) (regular_polygon m)))).card = 2 * (regular_polygon m).card := by
      rw [ Finset.card_biUnion ];
      · exact ⟨ h_sum_degrees, by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.card_image_of_injective _ fun y z h => by injection h ] ] ; rw [ Finset.sum_congr rfl fun x hx => h_degree x hx ] ; simp +decide [ mul_comm ] ⟩;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;
    unfold distance_count;
    rw [ h_total_edges.1, h_total_edges.2, Nat.mul_div_cancel_left _ ( by decide ), regular_polygon_card m ( by linarith ) ]

/-
The distance function `regular_polygon_distance` is injective for step sizes `k` in the range `1` to `(m-1)/2`.
-/
lemma regular_polygon_distance_inj (m : ℕ) (hm : m ≥ 3) :
  Set.InjOn (regular_polygon_distance m) (Set.Icc 1 ((m - 1) / 2)) := by
    intro k hk l hl hkl; simp_all +decide ;
    -- By definition of $regular_polygon_distance$, we have $2 \sin(\pi k / m) = 2 \sin(\pi l / m)$.
    have h_sin_eq : Real.sin (Real.pi * k / m) = Real.sin (Real.pi * l / m) := by
      have h_sin_eq : Real.sin (Real.pi * k / m) ^ 2 = Real.sin (Real.pi * l / m) ^ 2 := by
        unfold regular_polygon_distance at hkl;
        norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im ] at hkl;
        rw [ Real.sqrt_inj ( by nlinarith ) ( by nlinarith ) ] at hkl ; ring_nf at * ; norm_num [ Real.sin_sq, Real.cos_sq ] at * ; ring_nf at * ; aesop;
      rw [ ← sq_eq_sq₀ ( Real.sin_nonneg_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( k : ℝ ) ≤ m by norm_cast; omega ] ) ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( l : ℝ ) ≤ m by norm_cast; omega ] ) ), h_sin_eq ];
    exact_mod_cast ( by apply_fun Real.arcsin at h_sin_eq; rw [ Real.arcsin_sin, Real.arcsin_sin ] at h_sin_eq <;> nlinarith [ Real.pi_pos, show ( k : ℝ ) ≤ ( m - 1 ) / 2 by exact le_div_iff₀' ( by positivity ) |>.2 <| by rw [ le_sub_iff_add_le ] ; norm_cast ; omega, show ( l : ℝ ) ≤ ( m - 1 ) / 2 by exact le_div_iff₀' ( by positivity ) |>.2 <| by rw [ le_sub_iff_add_le ] ; norm_cast ; omega, mul_div_cancel₀ ( Real.pi * k ) ( by positivity : ( m : ℝ ) ≠ 0 ), mul_div_cancel₀ ( Real.pi * l ) ( by positivity : ( m : ℝ ) ≠ 0 ) ] : ( k : ℝ ) = l ) ;

/-
In a regular $m$-gon, $\left\lfloor\frac{m-1}{2}\right\rfloor$ distances appear $m$ times.
-/
lemma mgon (m : ℕ) (hm : m ≥ 3) :
  let P := regular_polygon m
  let distances := (P.offDiag.image (fun (x, y) => dist x y))
  ∃ S ⊆ distances, S.card = (m - 1) / 2 ∧ ∀ d ∈ S, distance_count P d = m := by
    use Finset.image ( regular_polygon_distance m ) ( Finset.Icc 1 ( ( m - 1 ) / 2 ) );
    field_simp;
    refine' ⟨ _, _, _ ⟩ <;> norm_num [ Finset.card_image_of_injOn ];
    · intro;
      simp +zetaDelta at *;
      rintro x hx₁ hx₂ rfl;
      refine' ⟨ 1, Complex.exp ( 2 * Real.pi * Complex.I * x / m ), _, _ ⟩;
      · refine' ⟨ _, _, _ ⟩ <;> norm_num [ regular_polygon ];
        · simp +decide [ Polynomial.nthRootsFinset ];
          simp +decide [ Polynomial.nthRoots ];
          exact Polynomial.X_pow_sub_C_ne_zero ( by linarith ) _;
        · norm_num [ Polynomial.nthRootsFinset ];
          rw [ Polynomial.mem_nthRoots ] <;> norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, show m ≠ 0 by positivity ];
          · exact Complex.exp_eq_one_iff.mpr ⟨ x, by push_cast; ring ⟩;
          · linarith;
        · rw [ eq_comm, Complex.exp_eq_one_iff ];
          field_simp;
          exact fun ⟨ n, hn ⟩ => by rw [ div_eq_iff ( by norm_cast; linarith ) ] at hn; norm_cast at hn; nlinarith [ show n = 0 by nlinarith [ Nat.div_mul_le_self ( m - 1 ) 2, Nat.sub_add_cancel ( by linarith : 1 ≤ m ) ] ] ;
      · unfold regular_polygon_distance; ring;
    · rw [ Finset.card_image_of_injOn ] <;> norm_num [ regular_polygon_distance_inj m hm ];
    · exact fun d x hx₁ hx₂ hx₃ => hx₃ ▸ mgon_helper m x hm hx₁ hx₂

/-
Rotation of a point `z` around a center `c` by an angle `θ` in the complex plane.
-/
def rotate_around (c : ℂ) (θ : ℝ) (z : ℂ) : ℂ := c + (z - c) * Complex.exp (θ * Complex.I)

/-
Rotation around a point `c` by angle `θ` is an isometry.
-/
lemma rotate_around_isometry (c : ℂ) (θ : ℝ) : Isometry (rotate_around c θ) := by
  refine' Isometry.of_dist_eq fun x y => _;
  unfold rotate_around; rw [ dist_eq_norm, dist_eq_norm ] ; ring_nf;
  rw [ show x * Complex.exp ( θ * Complex.I ) - Complex.exp ( θ * Complex.I ) * y = ( x - y ) * Complex.exp ( θ * Complex.I ) by ring, norm_mul, Complex.norm_exp ] ; norm_num

/-
Rotation around a point `c` fixes `c`.
-/
lemma rotate_around_self (c : ℂ) (θ : ℝ) : rotate_around c θ c = c := by
  unfold rotate_around; norm_num;

/-
For any finite set of points `P` and a point `c` in `P`, there exists a non-zero rotation angle `θ` such that the rotated set `P` intersects the original set `P` only at `c`.
-/
lemma exists_good_rotation (P : Finset ℂ) (c : ℂ) (hc : c ∈ P) :
  ∃ θ : ℝ, θ ≠ 0 ∧ (P.image (rotate_around c θ)) ∩ P = {c} := by
    -- The set of angles $\theta \in [0, 2\pi)$ such that $rotate\_around(c, \theta, x) = y$ for some $x, y \in P$ is countable.
    have h_countable : Set.Countable {θ : ℝ | ∃ x y : ℂ, x ∈ P ∧ y ∈ P ∧ x ≠ c ∧ rotate_around c θ x = y} := by
      have h_countable : ∀ x y : ℂ, x ∈ P → y ∈ P → x ≠ c → Set.Countable {θ : ℝ | rotate_around c θ x = y} := by
        intros x y hx hy hxc
        have h_eq : ∀ θ : ℝ, rotate_around c θ x = y → Complex.exp (θ * Complex.I) = (y - c) / (x - c) := by
          exact fun θ hθ => eq_div_of_mul_eq ( sub_ne_zero_of_ne hxc ) ( by rw [ ← hθ ] ; unfold rotate_around; ring );
        -- Since $e^{i\theta} = \frac{y - c}{x - c}$ has at most one solution for $\theta$ in $[0, 2\pi)$, the set of such $\theta$ is countable.
        have h_unique : ∀ θ₁ θ₂ : ℝ, Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) → ∃ k : ℤ, θ₁ = θ₂ + 2 * k * Real.pi := by
          exact fun θ₁ θ₂ h => by rw [ Complex.exp_eq_exp_iff_exists_int ] at h; obtain ⟨ k, hk ⟩ := h; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
        by_cases h : ∃ θ : ℝ, rotate_around c θ x = y;
        · obtain ⟨ θ₀, hθ₀ ⟩ := h; exact Set.Countable.mono ( fun θ hθ => by obtain ⟨ k, rfl ⟩ := h_unique θ θ₀ ( by rw [ h_eq θ hθ, h_eq θ₀ hθ₀ ] ) ; exact ⟨ k, rfl ⟩ ) ( Set.countable_range ( fun k : ℤ => θ₀ + 2 * k * Real.pi ) ) ;
        · exact Set.countable_empty.mono fun θ hθ => h ⟨ θ, hθ ⟩;
      convert Set.Countable.biUnion ( Finset.countable_toSet ( P.filter fun x => x ≠ c ) ) fun x hx => Set.Countable.biUnion ( Finset.countable_toSet P ) fun y hy => h_countable x y ( Finset.mem_filter.mp hx |>.1 ) hy ( Finset.mem_filter.mp hx |>.2 ) using 1 ; aesop;
    -- Since there are only finitely many such pairs, we can choose a $\theta$ that avoids all these bad angles.
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ ≠ 0 ∧ θ ∉ {θ : ℝ | ∃ x y : ℂ, x ∈ P ∧ y ∈ P ∧ x ≠ c ∧ rotate_around c θ x = y} := by
      contrapose! h_countable;
      exact fun h => absurd ( h.mono <| show { θ : ℝ | ∃ x y : ℂ, x ∈ P ∧ y ∈ P ∧ x ≠ c ∧ rotate_around c θ x = y } ⊇ Set.Ioi 0 from fun x hx => h_countable x <| ne_of_gt hx ) ( by exact fun h' => absurd ( h'.measure_zero <| MeasureTheory.MeasureSpace.volume ) <| by simp +decide );
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact ⟨ θ, hθ.1, ⟨ c, hc, by simp +decide [ rotate_around_self ] ⟩, fun x hx hx' => by rw [ hθ.2 x hx hx', rotate_around_self ] ⟩

/-
Reflection of a point `z` across the line passing through `a` and `b` in the complex plane.
-/
def reflect_over (a b z : ℂ) : ℂ :=
  a + (b - a) * starRingEnd ℂ ((z - a) / (b - a))

/-
Reflection across the line passing through `a` and `b` is an isometry.
-/
lemma reflect_over_isometry (a b : ℂ) (h : a ≠ b) : Isometry (reflect_over a b) := by
  refine' Isometry.of_dist_eq fun x y => _;
  simp +decide [ dist_eq_norm, reflect_over ];
  norm_num [ ← mul_sub, ← mul_div_assoc, h ];
  rw [ ← sub_div ];
  norm_num [ ← mul_sub, norm_mul, norm_div ];
  rw [ div_eq_iff ] <;> simp_all +decide [ Complex.norm_def, Complex.normSq ];
  · ring_nf;
  · exact ne_of_gt <| Real.sqrt_pos.mpr <| not_le.mp fun h' => h <| by refine' Complex.ext _ _ <;> nlinarith;

/-
For odd `n = 2m+1`, there exists a set of `n` points with `floor(m/2)` distances appearing at least `n+1` times.
-/
lemma erdos756_odd (m : ℕ) (hm : m ≥ 2) :
  let n := 2 * m + 1
  ∃ P : Finset ℂ, P.card = n ∧
    ∃ S ⊆ (P.offDiag.image (fun (x, y) => dist x y)),
      S.card = m / 2 ∧ ∀ d ∈ S, distance_count P d ≥ n + 1 := by
        -- Let $P_0$ be the set of vertices of a regular $(m+1)$-gon.
        set P0 := regular_polygon (m + 1);
        -- Let $v$ be a vertex of $P_0$.
        obtain ⟨v, hv⟩ : ∃ v ∈ P0, True := by
          simp +zetaDelta at *;
          exact Finset.card_pos.mp ( by rw [ regular_polygon_card ] <;> linarith );
        -- By `exists_good_rotation`, there exists a rotation $R$ around $v$ such that $P_0 \cap R(P_0) = \{v\}$.
        obtain ⟨R, hR⟩ : ∃ R : ℂ → ℂ, Isometry R ∧ R v = v ∧ (P0.image R) ∩ P0 = {v} := by
          obtain ⟨ θ, hθ ⟩ := exists_good_rotation P0 v hv.1;
          exact ⟨ _, rotate_around_isometry v θ, rotate_around_self v θ, hθ.2 ⟩;
        -- Let $P = P_0 \cup R(P_0)$.
        set P := P0 ∪ P0.image R;
        -- Let $S_0$ be the set of distances in $P_0$ that appear $m+1$ times (from `mgon`). $|S_0| = \lfloor m/2 \rfloor$.
        obtain ⟨S0, hS0⟩ : ∃ S0 : Finset ℝ, S0 ⊆ (P0.offDiag.image (fun (x, y) => dist x y)) ∧ S0.card = m / 2 ∧ ∀ d ∈ S0, distance_count P0 d = m + 1 := by
          convert mgon ( m + 1 ) ( by linarith ) using 1;
        -- For each $d \in S_0$, it appears $m+1$ times in $P_0$ and $m+1$ times in $R(P_0)$ (since $R$ is an isometry).
        have h_count : ∀ d ∈ S0, distance_count P d ≥ distance_count P0 d + distance_count (P0.image R) d := by
          intro d hd
          have h_count : (P.offDiag.filter (fun (x, y) => dist x y = d)).card ≥ (P0.offDiag.filter (fun (x, y) => dist x y = d)).card + ((P0.image R).offDiag.filter (fun (x, y) => dist x y = d)).card := by
            rw [ ← Finset.card_union_of_disjoint ];
            · refine Finset.card_mono ?_;
              simp +decide [ Finset.subset_iff ];
              grind;
            · simp_all +decide [ Finset.disjoint_left ];
              intro a b ha hb hab hdist x hx hx' y hy hy'; have := hR.1.dist_eq x y; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
              grind +ring;
          unfold distance_count at *;
          grind;
        -- Since $R$ is an isometry, the distance count in $R(P_0)$ is the same as in $P_0$.
        have h_isometry_count : ∀ d ∈ S0, distance_count (P0.image R) d = distance_count P0 d := by
          intros d hd
          have h_isometry_count : ∀ x y : ℂ, dist (R x) (R y) = dist x y := by
            exact hR.1.dist_eq;
          unfold distance_count;
          rw [ show ( Finset.image R P0 ).offDiag = Finset.image ( fun x : ℂ × ℂ => ( R x.1, R x.2 ) ) ( P0.offDiag ) from ?_, Finset.card_filter, Finset.card_filter ];
          · rw [ Finset.sum_image ] ; aesop;
            exact fun x hx y hy hxy => Prod.ext ( hR.1.injective <| by aesop ) ( hR.1.injective <| by aesop );
          · ext ⟨x, y⟩; simp [Finset.mem_offDiag, Finset.mem_image];
            constructor;
            · grind;
            · rintro ⟨ a, b, ⟨ ha, hb, hab ⟩, rfl, rfl ⟩ ; exact ⟨ ⟨ a, ha, rfl ⟩, ⟨ b, hb, rfl ⟩, by intro h; have := hR.1.injective h; aesop ⟩ ;
        refine' ⟨ P, _, S0, _, _, _ ⟩ <;> simp_all +decide [ two_mul ];
        · rw [ Finset.card_union ];
          rw [ Finset.inter_comm, hR.2.2 ] ; norm_num [ regular_polygon_card ] ; ring_nf;
          rw [ Finset.card_image_of_injective _ hR.1.injective ] ; rw [ regular_polygon_card ] <;> linarith;
        · intro d hd; specialize hS0; have := hS0.1 hd; aesop;
        · exact fun d hd => by linarith [ h_count d hd ] ;

/-
The intersection of a regular `(m+1)`-gon and its reflection across an edge is exactly the two endpoints of the edge.
-/
lemma regular_polygon_reflection_inter (m : ℕ) (hm : m ≥ 2) :
  let P := regular_polygon (m + 1)
  let u := (1 : ℂ)
  let v := zeta (m + 1)
  let R := reflect_over u v
  P ∩ (P.image R) = {u, v} := by
    ext x;
    constructor;
    · simp [reflect_over];
      intro hx y hy hxy; rw [ mul_div, add_div', div_eq_iff ] at hxy <;> simp_all +decide [ Complex.ext_iff ] ;
      · -- Since $x$ and $y$ are vertices of the regular $(m+1)$-gon, we have $|x| = |y| = 1$.
        have hx_abs : x.re^2 + x.im^2 = 1 := by
          rw [ ← Complex.normSq_add_mul_I, Complex.normSq_eq_norm_sq ];
          -- Since $x$ is a root of unity, we have $x^{m+1} = 1$, which implies $|x| = 1$.
          have hx_abs : x ^ (m + 1) = 1 := by
            unfold regular_polygon at hx; aesop;
          have := congr_arg Norm.norm hx_abs ; norm_num at this ; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop
        have hy_abs : y.re^2 + y.im^2 = 1 := by
          have hy_abs : y ^ (m + 1) = 1 := by
            unfold regular_polygon at hy; aesop;
          have := congr_arg Complex.normSq hy_abs ; norm_num [ Complex.normSq_eq_norm_sq ] at this;
          rw [ ← Complex.normSq_add_mul_I, Complex.normSq_eq_norm_sq ] ; norm_num [ show ‖y‖ = 1 by exact le_antisymm ( le_of_not_gt fun h => by have := this.resolve_right ( by linarith [ pow_nonneg ( norm_nonneg y ) ( m + 1 ) ] ) ; linarith [ pow_lt_pow_right₀ h ( by linarith : m + 1 > 0 ) ] ) ( le_of_not_gt fun h => by have := this.resolve_right ( by linarith [ pow_nonneg ( norm_nonneg y ) ( m + 1 ) ] ) ; linarith [ pow_lt_one₀ ( norm_nonneg y ) h ( by linarith : m + 1 ≠ 0 ) ] ) ]
        have hzeta_abs : (zeta (m + 1)).re^2 + (zeta (m + 1)).im^2 = 1 := by
          unfold zeta; norm_num [ Complex.exp_re, Complex.exp_im, sq ] ; ring_nf; norm_num;
        by_cases h_im : (zeta (m + 1)).im = 0;
        · unfold zeta at *; norm_num [ Complex.exp_re, Complex.exp_im ] at *;
          norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ] at *;
          norm_num [ show ( m + 1 : ℝ ) ≠ 0 by positivity, mul_div_mul_right ] at *;
          exact absurd h_im ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith only [ Real.pi_pos, show ( m : ℝ ) ≥ 2 by norm_cast ] ) ) );
        · grind;
      · norm_num [ zeta ];
        ring_nf; norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ];
        exact fun _ => ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( m : ℝ ) ≥ 2 by norm_cast, mul_inv_cancel₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) ] ) );
      · norm_num [ zeta ];
        norm_num [ Complex.exp_re, Complex.exp_im ];
        ring_nf; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ];
        exact fun _ => ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( m : ℝ ) ≥ 2 by norm_cast, mul_inv_cancel₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) ] ) );
    · simp +zetaDelta at *;
      rintro ( rfl | rfl ) <;> norm_num [ regular_polygon, zeta ];
      · use 1; simp [reflect_over];
      · refine' ⟨ _, Complex.exp ( 2 * Real.pi * Complex.I / ( m + 1 ) ), _, _ ⟩ <;> norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀, show ( m : ℂ ) + 1 ≠ 0 from Nat.cast_add_one_ne_zero m ];
        unfold reflect_over; norm_num [ Complex.exp_ne_zero ] ;
        rw [ div_self ] <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
        ring_nf; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ];
        exact fun _ => ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( m : ℝ ) ≥ 2 by norm_cast, mul_inv_cancel₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) ] ) )

/-
For even `n = 2m`, there exists a set of `n` points with `floor(m/2)` distances appearing at least `n+1` times.
-/
lemma erdos756_even (m : ℕ) (hm : m ≥ 2) :
  let n := 2 * m
  ∃ P : Finset ℂ, P.card = n ∧
    ∃ S ⊆ (P.offDiag.image (fun (x, y) => dist x y)),
      S.card = m / 2 ∧ ∀ d ∈ S, distance_count P d ≥ n + 1 := by
        -- Let $P_0$ be the set of vertices of a regular $(m+1)$-gon.
        set P0 := regular_polygon (m + 1) with hP0_def
        have hP0_card : P0.card = m + 1 := by
          exact regular_polygon_card _ ( by linarith );
        -- Let $R$ be the reflection over the line passing through $u$ and $v$.
        set u := (1 : ℂ)
        set v := zeta (m + 1)
        set R := reflect_over u v with hR_def
        have hR_isometry : Isometry R := by
          apply reflect_over_isometry; simp [u, v];
          norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, zeta ];
          ring_nf; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ] ;
          exact fun _ => ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( m : ℝ ) ≥ 2 by norm_cast, mul_inv_cancel₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) ] ) )
        have hR_P0_card : (P0.image R).card = m + 1 := by
          rw [ Finset.card_image_of_injective _ hR_isometry.injective, hP0_card ]
        have hR_P0_inter : P0 ∩ (P0.image R) = {u, v} := by
          exact regular_polygon_reflection_inter m hm
        have hP_union_card : (P0 ∪ (P0.image R)).card = 2 * m := by
          have hP_union_card : (P0 ∪ (P0.image R)).card = P0.card + (P0.image R).card - ({u, v} : Finset ℂ).card := by
            grind;
          rw [ hP_union_card, hP0_card, hR_P0_card, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> norm_num [ Complex.exp_ne_zero ] ; omega;
          norm_num +zetaDelta at *;
          unfold zeta; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring_nf ;
          norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring_nf ;
          exact fun _ => ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by nlinarith [ Real.pi_pos, show ( m : ℝ ) ≥ 2 by norm_cast, mul_inv_cancel₀ ( by positivity : ( 1 + m : ℝ ) ≠ 0 ) ] ) )
        set P := P0 ∪ (P0.image R) with hP_def
        have hP_card : P.card = 2 * m := by
          exact hP_union_card
        let distances := P.offDiag.image (fun (x, y) => dist x y)
        have hS_exists : ∃ S ⊆ distances, S.card = m / 2 ∧ ∀ d ∈ S, distance_count P d ≥ 2 * m + 1 := by
          -- Let $S_0$ be the set of distances in $P_0$ that appear $m+1$ times (from `mgon`).
          obtain ⟨S0, hS0_sub, hS0_card, hS0_count⟩ : ∃ S0 ⊆ (P0.offDiag.image (fun (x, y) => dist x y)), S0.card = m / 2 ∧ ∀ d ∈ S0, distance_count P0 d = m + 1 := by
            have := mgon ( m + 1 ) ( by linarith ) ; aesop;
          -- For each $d \in S_0$, it appears $m+1$ times in $P_0$ and $m+1$ times in $R(P_0)$ (since $R$ is an isometry).
          have hS0_count_P : ∀ d ∈ S0, distance_count P d ≥ distance_count P0 d + distance_count (P0.image R) d - (if d = dist u v then 1 else 0) := by
            intro d hd
            have hS0_count_P : (P.offDiag.filter (fun (x, y) => dist x y = d)).card ≥ (P0.offDiag.filter (fun (x, y) => dist x y = d)).card + ((P0.image R).offDiag.filter (fun (x, y) => dist x y = d)).card - (if d = dist u v then 2 else 0) := by
              have hS0_count_P : (P.offDiag.filter (fun (x, y) => dist x y = d)).card ≥ (P0.offDiag.filter (fun (x, y) => dist x y = d)).card + ((P0.image R).offDiag.filter (fun (x, y) => dist x y = d)).card - ((P0 ∩ (P0.image R)).offDiag.filter (fun (x, y) => dist x y = d)).card := by
                rw [ ← Finset.card_union_add_card_inter ];
                refine' Nat.sub_le_of_le_add _;
                refine' add_le_add _ _;
                · refine' Finset.card_mono _;
                  simp +decide [ Finset.subset_iff ];
                  rintro a b ( ⟨ ⟨ ha, hb, hab ⟩, rfl ⟩ | ⟨ ⟨ ⟨ x, hx, rfl ⟩, ⟨ y, hy, rfl ⟩, hab ⟩, rfl ⟩ ) <;> simp +decide [ *, Finset.mem_union ];
                  · exact ⟨ Or.inl ha, Or.inl hb ⟩;
                  · exact ⟨ Or.inr ⟨ x, hx, rfl ⟩, Or.inr ⟨ y, hy, rfl ⟩, hab ⟩;
                · refine' Finset.card_mono _;
                  simp +contextual [ Finset.subset_iff ];
              split_ifs <;> simp_all +decide ;
              · refine le_trans hS0_count_P ?_;
                simp +zetaDelta at *;
                refine' le_trans ( Finset.card_le_card _ ) _;
                exact { ( 1, zeta ( m + 1 ) ), ( zeta ( m + 1 ), 1 ) };
                · simp +decide [ Finset.subset_iff ];
                  rintro a b ( rfl | rfl ) ( rfl | rfl ) <;> norm_num [ dist_comm ] at *;
                · exact Finset.card_insert_le _ _;
              · refine le_trans hS0_count_P ?_;
                simp +zetaDelta at *;
                rintro a b ( rfl | rfl ) ( rfl | rfl ) <;> simp_all +decide [ dist_comm ];
                · exact fun _ => Ne.symm ‹_›;
                · exact fun _ => Ne.symm ‹_›;
            unfold distance_count at *; simp_all +decide ;
            grind;
          -- Since $R$ is an isometry, the distance count in $R(P_0)$ is the same as in $P_0$.
          have hS0_count_R : ∀ d ∈ S0, distance_count (P0.image R) d = distance_count P0 d := by
            intro d hd
            have h_dist_eq : ∀ x y : ℂ, dist (R x) (R y) = dist x y := by
              exact fun x y => hR_isometry.dist_eq x y ▸ rfl;
            have h_dist_eq_set : (P0.image R).offDiag.filter (fun (x, y) => dist x y = d) = Finset.image (fun (x, y) => (R x, R y)) (P0.offDiag.filter (fun (x, y) => dist x y = d)) := by
              ext ⟨x, y⟩; simp;
              constructor <;> intro h;
              · rcases h with ⟨ ⟨ ⟨ a, ha, rfl ⟩, ⟨ b, hb, rfl ⟩, hab ⟩, hd ⟩ ; use a, b; aesop;
              · rcases h with ⟨ a, b, ⟨ ⟨ ha, hb, hab ⟩, rfl ⟩, rfl, rfl ⟩ ; exact ⟨ ⟨ ⟨ a, ha, rfl ⟩, ⟨ b, hb, rfl ⟩, by simpa [ hR_isometry.injective.eq_iff ] using hab ⟩, h_dist_eq a b ⟩ ;
            have h_dist_eq_card : ((P0.image R).offDiag.filter (fun (x, y) => dist x y = d)).card = (P0.offDiag.filter (fun (x, y) => dist x y = d)).card := by
              rw [ h_dist_eq_set, Finset.card_image_of_injective ];
              exact fun x y hxy => Prod.ext ( hR_isometry.injective <| by simpa using congr_arg Prod.fst hxy ) ( hR_isometry.injective <| by simpa using congr_arg Prod.snd hxy )
            have h_dist_eq_final : distance_count (P0.image R) d = distance_count P0 d := by
              exact congr_arg ( · / 2 ) h_dist_eq_card
            exact h_dist_eq_final;
          refine' ⟨ S0, _, hS0_card, _ ⟩ <;> simp_all +decide [ two_mul ];
          · exact fun x hx => Finset.mem_image.mpr <| by rcases Finset.mem_image.mp ( hS0_sub hx ) with ⟨ y, hy, rfl ⟩ ; exact ⟨ y, Finset.mem_offDiag.mpr ⟨ Finset.mem_union_left _ <| Finset.mem_offDiag.mp hy |>.1, Finset.mem_union_left _ <| Finset.mem_offDiag.mp hy |>.2.1, Finset.mem_offDiag.mp hy |>.2.2 ⟩, rfl ⟩ ;
          · grind
        use P, hP_card, hS_exists.choose, hS_exists.choose_spec.left, hS_exists.choose_spec.right.left, hS_exists.choose_spec.right.right

/-
For all $n \in \mathbb{N}$, there exists a set of $n$ points such that $\left\lfloor\frac{n}{4}\right\rfloor$ distances occur at least $n+1$ times.
-/
theorem erdos756 (n : ℕ) :
  ∃ P : Finset ℂ, P.card = n ∧
    ∃ S ⊆ (P.offDiag.image (fun (x, y) => dist x y)),
      S.card = n / 4 ∧ ∀ d ∈ S, distance_count P d ≥ n + 1 := by
        rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
        · by_cases hk : 2 ≤ k;
          · obtain ⟨ P, hP₁, S, hS₁, hS₂, hS₃ ⟩ := erdos756_even k hk;
            exact ⟨ P, hP₁, S, hS₁, by omega, hS₃ ⟩;
          · interval_cases k <;> [ exact ⟨ ∅, by norm_num ⟩ ; exact ⟨ { 0, 1 }, by norm_num, ∅, by norm_num ⟩ ];
        · by_cases hk : k ≥ 2;
          · convert erdos756_odd k hk using 1;
            grind +ring;
          · interval_cases k <;> simp_all +decide;
            · exact ⟨ { 0 }, by norm_num ⟩;
            · exact ⟨ { 0, 1, 2 }, by norm_num ⟩

#print axioms erdos756
