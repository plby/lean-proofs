/-

This is a Lean formalization of a solution to Erdős Problem 1048.
https://www.erdosproblems.com/forum/thread/1048

The original proof was found by: Pommerenke

[Po61] Pommerenke, Ch., On metric properties of complex
polynomials. Michigan Math. J. (1961), 97-115.


The STATEMENT of Pommerenke's result was given to Aristotle (no proof
provided), and it auto-formalized the proof.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We define the function $f(z) = z^n - r^n$ and the set $S = \{z \in \mathbb{C} : |f(z)| \le 1\}$. We prove that for $r > 1$, $S$ has exactly $n$ connected components. This is done by constructing $n$ disjoint branches of the inverse function (n-th root) mapping the disk $D(r^n, 1)$ into $S$, and showing that their images are the connected components. We then prove that the diameter of these components tends to 0 as $n \to \infty$ by bounding the derivative of the branch functions and applying the Mean Value Inequality. The main result is `main_result`.
-/

import Mathlib

/-
Define f(z) = z^n - r^n and S = {z : |f(z)| <= 1}.
-/
def f (n : ℕ) (r : ℝ) (z : ℂ) : ℂ := z^n - (r : ℂ)^n

def S (n : ℕ) (r : ℝ) : Set ℂ := { z | ‖f n r z‖ ≤ 1 }

/-
If r > 1 and n > 0, then any complex number w in the closed ball of radius 1 centered at r^n has a positive real part.
-/
lemma disk_in_right_half_plane {r : ℝ} (hr : r > 1) {n : ℕ} (hn : n > 0) :
  ∀ w ∈ Metric.closedBall (r ^ n : ℂ) 1, 0 < w.re := by
    intro w hw
    have h_re_w : w.re ≥ r ^ n - 1 := by
      norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def ] at hw;
      norm_cast at * ; nlinarith;
    linarith [ pow_lt_pow_right₀ hr hn ]

/-
Define the k-th branch of the n-th root of w. Prove that (branch n k w)^n = w if w has positive real part.
-/
noncomputable def branch (n : ℕ) (k : ℕ) (w : ℂ) : ℂ :=
  (Real.rpow (norm w) (1 / (n : ℝ)) : ℂ) * Complex.exp (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n : ℝ))

lemma branch_pow {n : ℕ} (hn : n > 0) (k : ℕ) (w : ℂ) :
  (branch n k w) ^ n = w := by
    unfold branch;
    norm_num [ mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀, hn.ne', mul_div_cancel₀, Complex.exp_nat_mul ];
    convert Complex.norm_mul_exp_arg_mul_I w using 1;
    field_simp;
    rw [ ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( norm_nonneg _ ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ; rw [ ← Complex.exp_nat_mul ] ; ring_nf ; norm_num [ hn.ne' ] ;
    exact Or.inl ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ k, by simp [ hn.ne', mul_assoc, mul_comm, mul_left_comm ] ⟩ )

/-
For any k, the k-th branch maps the disk D(r^n, 1) into S. This follows because (branch n k w)^n = w for w in the disk, and |w - r^n| <= 1.
-/
lemma branch_mem_S {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) (w : ℂ) (hw : w ∈ Metric.closedBall (r ^ n : ℂ) 1) :
  branch n k w ∈ S n r := by
  rw [S, Set.mem_setOf_eq, f]
  have hre : 0 < w.re := disk_in_right_half_plane hr hn w hw
  rw [branch_pow hn k w]
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw
  exact hw

/-
The branch function is continuous on the disk D(r^n, 1). This is because it is a composition of continuous functions (norm, rpow, exp, arg) and the argument function is continuous on the right half-plane, where the disk lies.
-/
lemma branch_continuous_on_disk {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  ContinuousOn (branch n k) (Metric.closedBall (r^n : ℂ) 1) := by
    -- The argument function is continuous on the right half-plane, where the disk lies.
    have h_arg_cont : ContinuousOn (fun z : ℂ => Complex.arg z) (Metric.closedBall (r ^ n : ℂ) 1) := by
      refine' continuousOn_of_forall_continuousAt fun z hz => _;
      refine' Complex.continuousAt_arg _;
      simp_all +decide [ Complex.slitPlane ];
      contrapose! hz;
      norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def, hz ];
      norm_cast ; norm_num;
      rw [ Real.sqrt_mul_self_eq_abs, abs_of_nonpos ] <;> nlinarith [ pow_le_pow_right₀ hr.le hn ];
    refine' ContinuousOn.mul _ _;
    · exact Complex.continuous_ofReal.comp_continuousOn ( ContinuousOn.rpow ( continuous_norm.continuousOn ) continuousOn_const <| by intro x hx; exact Or.inr <| by positivity );
    · exact Complex.continuous_exp.comp_continuousOn ( ContinuousOn.mul continuousOn_const <| Complex.continuous_ofReal.comp_continuousOn <| ContinuousOn.div_const ( h_arg_cont.add continuousOn_const ) _ )

/-
Define component n r k as the image of the disk D(r^n, 1) under the k-th branch. Prove it is a subset of S and is connected.
-/
def component (n : ℕ) (r : ℝ) (k : ℕ) : Set ℂ :=
  branch n k '' Metric.closedBall (r^n : ℂ) 1

lemma component_subset_S {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  component n r k ⊆ S n r := by
    exact Set.image_subset_iff.mpr fun z hz => branch_mem_S hn hr k z hz

lemma component_connected {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  IsConnected (component n r k) := by
    apply_rules [ IsConnected.image, isConnected_Icc ];
    · exact convex_closedBall _ _ |> fun h => h.isConnected <| by norm_num;
    · exact branch_continuous_on_disk hn hr k

/-
S is contained in the union of the components. If z is in S, then z^n is in the disk, so z is an n-th root of a point in the disk, hence in one of the components.
-/
lemma S_subset_union_components {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) :
  S n r ⊆ ⋃ k ∈ Finset.range n, component n r k := by
  intro z hz
  rw [S, Set.mem_setOf_eq, f] at hz
  let w := z^n
  have hw : w ∈ Metric.closedBall (r^n : ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    exact hz
  have h_root : z ^ n = w := rfl
  -- z is an n-th root of w.
  -- We need to show z = branch n k w for some k.
  -- We know w is in the right half plane, so w != 0.
  have hw_ne_zero : w ≠ 0 := by
    have : 0 < w.re := disk_in_right_half_plane hr hn w hw
    intro h
    rw [h] at this
    simp at this
  -- The n-th roots of w are branch n k w for k in 0..n-1.
  -- This is a standard fact about complex roots.
  -- Since $w$ is in the disk, it can be written as $w = (branch n k w)^n$ for some $k$. Therefore, $z$ must be one of the branches.
  obtain ⟨k, hk⟩ : ∃ k ∈ Finset.range n, z = branch n k w := by
    -- Since $w \neq 0$, we can write $z$ as $z = \sqrt[n]{w} \cdot e^{2\pi i k/n}$ for some integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, z = (Real.rpow (norm w) (1 / (n : ℝ)) : ℂ) * Complex.exp (Complex.I * ((Complex.arg w + 2 * Real.pi * k) / n : ℝ)) := by
      -- Since $z^n = w$, we can write $z = \sqrt[n]{w}$ for some $k \in \{0, 1, ..., n-1\}$ by the properties of roots of unity. Use the fact that $z^n = w$ to express $z$ in terms of $w$.
      have h_exp : ∃ θ : ℝ, z = (Real.rpow (norm w) (1 / n) : ℂ) * Complex.exp (Complex.I * θ) := by
        have h_polar : z = ‖z‖ * Complex.exp (Complex.I * Complex.arg z) := by
          nth_rw 1 [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring_nf;
        norm_num [ ← h_root, Complex.norm_exp ] at *;
        exact ⟨ Complex.arg z, by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( norm_nonneg _ ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ] ; exact h_polar ⟩;
      -- Since $z^n = w$, we have $e^{i n \theta} = e^{i \arg w}$, which implies $n \theta = \arg w + 2 \pi k$ for some integer $k$.
      obtain ⟨θ, hθ⟩ := h_exp
      have h_eq : ∃ k : ℤ, n * θ = Complex.arg w + 2 * Real.pi * k := by
        have h_eq : Complex.exp (Complex.I * (n * θ)) = Complex.exp (Complex.I * Complex.arg w) := by
          have h_exp : z^n = (Real.rpow (norm w) (1 / n : ℝ))^n * Complex.exp (Complex.I * (n * θ)) := by
            rw [ hθ, mul_pow, ← Complex.exp_nat_mul ] ; ring_nf;
          have h_exp : (Real.rpow (norm w) (1 / n : ℝ))^n = norm w := by
            norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( norm_nonneg _ ), hn.ne' ];
          have h_exp : w = norm w * Complex.exp (Complex.I * Complex.arg w) := by
            nth_rw 1 [ ← Complex.norm_mul_exp_arg_mul_I w ] ; ring_nf;
          norm_num [ Complex.ext_iff ] at *;
          norm_cast at *; aesop;
        rw [ Complex.exp_eq_exp_iff_exists_int ] at h_eq; obtain ⟨ k, hk ⟩ := h_eq; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
      exact h_eq.imp fun k hk => by rw [ hθ, ← hk ] ; push_cast; ring_nf; norm_num [ hn.ne' ] ;
    -- Since $k$ is an integer, we can write it as $k = qn + r$ for some integer $q$ and $0 \leq r < n$.
    obtain ⟨q, r, hr⟩ : ∃ q : ℤ, ∃ r : ℕ, r < n ∧ k = q * n + r := by
      exact ⟨ k / n, Int.toNat ( k % n ), by linarith [ Int.emod_lt_of_pos k ( by positivity : 0 < ( n : ℤ ) ), Int.emod_nonneg k ( by positivity : ( n : ℤ ) ≠ 0 ), Int.toNat_of_nonneg ( Int.emod_nonneg k ( by positivity : ( n : ℤ ) ≠ 0 ) ) ], by linarith [ Int.emod_add_mul_ediv k n, Int.toNat_of_nonneg ( Int.emod_nonneg k ( by positivity : ( n : ℤ ) ≠ 0 ) ) ] ⟩;
    refine' ⟨ r, Finset.mem_range.mpr hr.1, hk.trans _ ⟩ ; norm_num [ hr.2, branch ] ; ring_nf ; norm_num [ hn.ne' ] ; ring_nf;
    exact Or.inl ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ q, by ring ⟩ );
  exact hk.2.symm ▸ Set.mem_iUnion₂.2 ⟨ k, hk.1, ⟨ w, hw, rfl ⟩ ⟩

/-
If two components intersect, their indices must be equal. This is because the branches are distinct.
-/
lemma components_disjoint {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k l : ℕ) (hk : k < n) (hl : l < n) (h : (component n r k ∩ component n r l).Nonempty) : k = l := by
  -- By definition of component, if $z \in \text{component } n r k \cap \text{component } n r l$, then there exist $w_1, w_2 \in \text{Metric.closedBall } (r^n : ℂ) 1$ such that $z = \text{branch } n k w_1$ and $z = \text{branch } n l w_2$.
  obtain ⟨z, hz⟩ : ∃ z, z ∈ component n r k ∧ z ∈ component n r l := h
  obtain ⟨w1, hw1, hw1z⟩ : ∃ w1 ∈ Metric.closedBall (r^n : ℂ) 1, z = branch n k w1 := by
    exact hz.1.imp fun x hx => ⟨ hx.1, hx.2.symm ⟩
  obtain ⟨w2, hw2, hw2z⟩ : ∃ w2 ∈ Metric.closedBall (r^n : ℂ) 1, z = branch n l w2 := by
    exact hz.2.imp fun x hx => ⟨ hx.1, hx.2.symm ⟩;
  -- Since $z^n = w1 = w2$, we have $w1 = w2$.
  have hw1w2 : w1 = w2 := by
    have hw1w2 : z^n = w1 ∧ z^n = w2 := by
      exact ⟨ by rw [ hw1z, branch_pow hn k w1 ], by rw [ hw2z, branch_pow hn l w2 ] ⟩;
    grind;
  -- Since $w1 = w2$, we have $branch n k w1 = branch n l w1$.
  have h_branch_eq : branch n k w1 = branch n l w1 := by
    grind;
  -- Since $branch n k w1 = branch n l w1$, we have $Complex.exp (Complex.I * ((Complex.arg w1 + 2 * Real.pi * k) / n)) = Complex.exp (Complex.I * ((Complex.arg w1 + 2 * Real.pi * l) / n))$.
  have h_exp_eq : Complex.exp (Complex.I * ((Complex.arg w1 + 2 * Real.pi * k) / n)) = Complex.exp (Complex.I * ((Complex.arg w1 + 2 * Real.pi * l) / n)) := by
    unfold branch at h_branch_eq;
    simp +zetaDelta at *;
    refine h_branch_eq.resolve_right ?_;
    refine' ne_of_gt ( Real.rpow_pos_of_pos _ _ );
    refine' norm_pos_iff.mpr _;
    rintro rfl; norm_num at *;
    exact hw1.not_gt ( one_lt_pow₀ ( by rw [ abs_of_pos ] <;> linarith ) ( by linarith ) );
  rw [ Complex.exp_eq_exp_iff_exists_int ] at h_exp_eq;
  obtain ⟨ m, hm ⟩ := h_exp_eq; rw [ Complex.ext_iff ] at hm; simp_all +decide
  -- Simplify the equation $hm$ to get $k = l + m * n$.
  have hkl : k = l + m * n := by
    exact_mod_cast ( by nlinarith [ Real.pi_pos, mul_div_cancel₀ ( w2.arg + 2 * Real.pi * k ) ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( w2.arg + 2 * Real.pi * l ) ( by positivity : ( n : ℝ ) ≠ 0 ) ] : ( k : ℝ ) = l + m * n );
  nlinarith [ show m = 0 by nlinarith ]

/-
The components are compact (image of compact set under continuous map) and therefore closed.
-/
lemma component_compact {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  IsCompact (component n r k) := by
    convert ( isCompact_closedBall ( r ^ n : ℂ ) 1 |> IsCompact.image_of_continuousOn ) ( branch_continuous_on_disk hn hr k ) using 1

lemma component_isClosed {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  IsClosed (component n r k) := by
    convert IsCompact.isClosed ?_;
    · infer_instance;
    · exact IsCompact.image_of_continuousOn ( ProperSpace.isCompact_closedBall _ _ ) ( branch_continuous_on_disk hn hr k )

/-
Define component_subtype as the restriction of component to the subtype S. Prove it is closed and open in S. It is closed because component is closed in C. It is open because its complement is a finite union of closed sets (the other components).
-/
def component_subtype (n : ℕ) (r : ℝ) (k : ℕ) : Set { z // z ∈ S n r } :=
  { z | z.val ∈ component n r k }

lemma component_subtype_isClosed {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  IsClosed (component_subtype n r k) := by
    exact IsClosed.preimage continuous_subtype_val ( component_isClosed hn hr k )

lemma component_subtype_isOpen {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) (hk : k < n) :
  IsOpen (component_subtype n r k) := by
    -- The complement of the component_subtype is the union of the other components, which are closed sets.
    have h_complement_closed : IsClosed ((⋃ l ∈ Finset.erase (Finset.range n) k, component n r l) ∩ S n r) := by
      refine' IsClosed.inter _ _;
      · exact isClosed_biUnion_finset fun l hl => component_isClosed hn hr l;
      · refine' isClosed_le _ _;
        · exact Continuous.norm ( by unfold f; continuity );
        · exact continuous_const;
    have h_complement : (⋃ l ∈ Finset.erase (Finset.range n) k, component n r l) ∩ S n r = (component n r k)ᶜ ∩ S n r := by
      ext aesop;
      constructor <;> intro h <;> simp_all +decide
      · obtain ⟨ ⟨ i, hi, hi' ⟩, hi'' ⟩ := h;
        exact fun h => hi.1 <| components_disjoint hn hr i k hi.2 hk ⟨ aesop, hi', h ⟩;
      · have := S_subset_union_components hn hr h.2;
        aesop;
    use ( ( ⋃ l ∈ Finset.erase ( Finset.range n ) k, component n r l ) ∩ S n r ) ᶜ;
    aesop

/-
Prove that component_subtype is connected by showing it is homeomorphic to component (which is connected).
-/
lemma isConnected_subtype_component {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  IsConnected (component_subtype n r k) := by
    have component_subtype_connected : IsConnected (component n r k) := by
      exact component_connected hn hr k;
    rw [ show component_subtype n r k = Set.image ( fun x : component n r k => ⟨ x.val, component_subset_S hn hr k x.2 ⟩ ) Set.univ from ?_ ];
    · apply_rules [ IsConnected.image, isConnected_univ ];
      · exact isConnected_iff_connectedSpace.mp component_subtype_connected;
      · fun_prop;
    · ext ; aesop

/-
Prove that component_subtype is exactly the connected component of x. Use the fact that component_subtype is connected (so subset of component) and clopen (so superset of component).
-/
lemma isComponent_component_subtype {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) (hk : k < n) :
  component_subtype n r k = connectedComponent (⟨branch n k (r^n), branch_mem_S hn hr k (r^n) (by rw [Metric.mem_closedBall, dist_self]; norm_num)⟩ : S n r) := by
  let x : S n r := ⟨branch n k (r^n), branch_mem_S hn hr k (r^n) (by rw [Metric.mem_closedBall, dist_self]; norm_num)⟩
  have hx : x ∈ component_subtype n r k := by
    show branch n k (r^n) ∈ component n r k
    use r^n
    simp [Metric.mem_closedBall, dist_self]
  have h_conn : IsConnected (component_subtype n r k) := isConnected_subtype_component hn hr k
  have h_clopen : IsClopen (component_subtype n r k) := ⟨component_subtype_isClosed hn hr k, component_subtype_isOpen hn hr k hk⟩
  apply Set.Subset.antisymm
  · -- component_subtype ⊆ connectedComponent x
    exact h_conn.subset_connectedComponent hx
  · -- connectedComponent x ⊆ component_subtype
    apply IsPreconnected.subset_isClopen isPreconnected_connectedComponent h_clopen
    use x
    constructor
    · exact mem_connectedComponent
    · exact hx

/-
Define the center of the k-th component as the image of r^n under the k-th branch.
-/
noncomputable def component_center (n : ℕ) (hn : n > 0) (r : ℝ) (hr : r > 1) (k : ℕ) : S n r :=
  ⟨branch n k (r^n), branch_mem_S hn hr k (r^n) (by rw [Metric.mem_closedBall, dist_self]; norm_num)⟩

/-
Define the map from Fin n to the connected components of S using ConnectedComponents.mk.
-/
noncomputable def components_map (n : ℕ) (hn : n > 0) (r : ℝ) (hr : r > 1) : Fin n → ConnectedComponents (S n r) :=
  fun k => ConnectedComponents.mk (component_center n hn r hr k)

/-
Prove that components_map is surjective. Any component c has a representative x, which belongs to some component_subtype k. Thus c is the image of k.
-/
lemma components_map_surjective {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) :
  Function.Surjective (components_map n hn r hr) := by
    intro B;
    -- By definition of connected components, there exists some $x \in S$ such that $x \in B$.
    obtain ⟨x, hx⟩ : ∃ x : S n r, B = ConnectedComponents.mk x := by
      induction B using Quotient.inductionOn' ; aesop;
    -- Since $x \in S$, by the lemma $S_subset_union_components$, $x$ must be in one of the components $component_subtype k$ for some $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k < n ∧ x.val ∈ component n r k := by
      have := S_subset_union_components hn hr x.2;
      aesop;
    -- Since $x \in component_subtype k$, we have $ConnectedComponents.mk x = ConnectedComponents.mk (component_center n hn r hr k)$.
    have h_eq : ConnectedComponents.mk x = ConnectedComponents.mk (component_center n hn r hr k) := by
      have h_eq : x ∈ component_subtype n r k ∧ component_center n hn r hr k ∈ component_subtype n r k := by
        exact ⟨ hk.2, Set.mem_image_of_mem _ <| by norm_num ⟩;
      have h_eq : IsConnected (component_subtype n r k) := by
        exact isConnected_subtype_component hn hr k;
      have h_eq : ∀ y ∈ component_subtype n r k, ConnectedComponents.mk y = ConnectedComponents.mk (component_center n hn r hr k) := by
        intro y hy;
        have h_eq : IsPreconnected (component_subtype n r k) := by
          exact h_eq.isPreconnected;
        have h_eq : ∀ y ∈ component_subtype n r k, ConnectedComponents.mk y = ConnectedComponents.mk (component_center n hn r hr k) := by
          intro y hy
          have h_eq : IsPreconnected (component_subtype n r k) := by
            exact h_eq
          have h_eq : IsPreconnected (Set.image (ConnectedComponents.mk : { z : ℂ // z ∈ S n r } → ConnectedComponents (S n r)) (component_subtype n r k)) := by
            apply_rules [ IsPreconnected.image, h_eq ];
            exact continuous_quotient_mk'.continuousOn
          have h_eq : ∀ z ∈ Set.image (ConnectedComponents.mk : { z : ℂ // z ∈ S n r } → ConnectedComponents (S n r)) (component_subtype n r k), z = ConnectedComponents.mk (component_center n hn r hr k) := by
            intro z hz
            obtain ⟨y, hy, rfl⟩ := hz;
            have := h_eq.subsingleton ( Set.mem_image_of_mem _ hy ) ( Set.mem_image_of_mem _ ( show component_center n hn r hr k ∈ component_subtype n r k from by
                                                                                                aesop ) ) ; aesop;
          exact h_eq _ <| Set.mem_image_of_mem _ hy;
        exact h_eq y hy;
      exact h_eq x ( by tauto );
    exact ⟨ ⟨ k, hk.1 ⟩, hx.symm ▸ h_eq.symm ⟩

/-
Prove that components_map is injective. If two indices map to the same component, the components intersect, so the indices must be equal.
-/
lemma components_map_injective {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) :
  Function.Injective (components_map n hn r hr) := by
    intro k l hkl;
    -- Since the components are disjoint, if their images under the map are equal, then their centers must be in the same component.
    have h_center_eq : component_center n hn r hr k ∈ component_subtype n r l := by
      have h_center_eq : connectedComponent (component_center n hn r hr k) = connectedComponent (component_center n hn r hr l) := by
        convert hkl using 1;
        constructor <;> intro h <;> simp_all +decide [ connectedComponent, components_map ];
      have h_center_eq : component_center n hn r hr k ∈ connectedComponent (component_center n hn r hr l) := by
        exact h_center_eq ▸ mem_connectedComponent;
      convert h_center_eq using 1;
      convert isComponent_component_subtype hn hr l ( Fin.is_lt l );
    have h_center_eq : (component n r k ∩ component n r l).Nonempty := by
      exact ⟨ _, ⟨ Set.mem_image_of_mem _ ( Metric.mem_closedBall_self <| by positivity ), h_center_eq ⟩ ⟩;
    exact Fin.ext <| components_disjoint hn hr _ _ ( Fin.is_lt k ) ( Fin.is_lt l ) h_center_eq

/-
The cardinality of the set of connected components is n. This follows from the bijection with Fin n.
-/
lemma card_components_eq_n {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) :
  Nat.card (ConnectedComponents (S n r)) = n := by
    have h_card : Nat.card (ConnectedComponents (S n r)) = Nat.card (Fin n) := by
      have h_surjective : Function.Surjective (components_map n hn r hr) := by
        exact components_map_surjective hn hr
      have h_injective : Function.Injective (components_map n hn r hr) := by
        exact components_map_injective hn hr
      exact Nat.card_congr ( Equiv.ofBijective ( components_map n hn r hr ) ⟨ h_injective, h_surjective ⟩ |> Equiv.symm );
    aesop

/-
Express branch n k w in terms of w^(1/n). This is useful for differentiation.
-/
lemma branch_eq_cpow_mul {n : ℕ} (k : ℕ) (w : ℂ) (hw : 0 < w.re) :
  branch n k w = (w ^ (1 / (n : ℂ))) * Complex.exp (2 * Real.pi * Complex.I * k / n) := by
    rw [ Complex.cpow_def_of_ne_zero ];
    · unfold branch; ring_nf;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
      rw [ Real.rpow_def_of_pos ( norm_pos_iff.mpr <| by aesop ) ] ; ring_nf ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] ;
      exact ⟨ by rw [ Real.cos_add ] ; ring, by rw [ Real.sin_add ] ; ring ⟩;
    · aesop

/-
Compute the derivative of the branch function. It is (1/n) * w^(1/n - 1) * exp(...).
-/
lemma deriv_branch {n : ℕ} (k : ℕ) (w : ℂ) (hw : 0 < w.re) :
  deriv (branch n k) w = ((1 / n : ℂ) * w ^ ((1 / n : ℂ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * k / n) := by
    field_simp;
    convert HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq _ ?_ ) using 1;
    exact fun z => z ^ ( 1 / ( n : ℂ ) ) * Complex.exp ( 2 * Real.pi * Complex.I * k / n );
    · convert HasDerivAt.mul ( HasDerivAt.cpow_const ( hasDerivAt_id w ) _ ) ( hasDerivAt_const _ _ ) using 1 <;> norm_num ;
      · ring;
      · exact Or.inl hw;
    · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) hw ] with z hz;
      convert branch_eq_cpow_mul k z hz using 1

/-
Bound the norm of the derivative of the branch function. The derivative is bounded by (1/n) * (r^n - 1)^(1/n - 1).
-/
lemma norm_deriv_branch_le {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) (w : ℂ) (hw : w ∈ Metric.closedBall (r^n : ℂ) 1) :
  ‖deriv (branch n k) w‖ ≤ (1 / n : ℝ) * (r^n - 1) ^ ((1 / n : ℝ) - 1) := by
    -- Apply the formula for the derivative of the branch function.
    have h_deriv : deriv (branch n k) w = ((1 / n : ℂ) * w ^ ((1 / n : ℂ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * k / n) := by
      convert deriv_branch k w _ using 1;
      exact disk_in_right_half_plane hr hn w hw;
    -- Bound the norm of the derivative using the fact that |exp(iθ)| = 1.
    have h_norm_deriv : ‖deriv (branch n k) w‖ ≤ (1 / n : ℝ) * ‖w‖ ^ ((1 / n : ℝ) - 1) := by
      simp_all +decide [ Complex.norm_exp ];
      convert Complex.norm_cpow_le _ _ using 1 ; norm_num;
    -- Since $w$ is in the closed ball of radius 1 centered at $r^n$, we have $‖w‖ ≥ r^n - 1$.
    have h_norm_w : ‖w‖ ≥ r ^ n - 1 := by
      -- Apply the reverse triangle inequality to get |‖w‖ - ‖r^n‖| ≤ ‖w - r^n‖.
      have h_reverse_triangle : |‖w‖ - ‖(r^n : ℂ)‖| ≤ ‖w - (r^n : ℂ)‖ := by
        exact abs_norm_sub_norm_le _ _;
      norm_num [ abs_le ] at *;
      simpa [ abs_of_pos ( zero_lt_one.trans hr ) ] using h_reverse_triangle.1.trans ( add_le_add_left hw _ );
    refine le_trans h_norm_deriv ?_;
    rcases n with ( _ | _ | n ) <;> norm_num at *;
    exact mul_le_mul_of_nonneg_left ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> nlinarith [ inv_mul_cancel₀ ( by linarith : ( n : ℝ ) + 1 + 1 ≠ 0 ), pow_le_pow_right₀ hr.le ( by linarith : n + 1 + 1 ≥ 2 ) ] ) ( by positivity )

/-
The branch function is differentiable on the closed ball D(r^n, 1).
-/
lemma branch_differentiable_on_disk {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  ∀ w ∈ Metric.closedBall (r^n : ℂ) 1, DifferentiableAt ℂ (branch n k) w := by
    intro w hw;
    refine' DifferentiableAt.congr_of_eventuallyEq _ _;
    exact fun z => ( z ^ ( 1 / ( n : ℂ ) ) ) * Complex.exp ( 2 * Real.pi * Complex.I * k / n );
    · refine' DifferentiableAt.mul _ _ <;> norm_num;
      refine' DifferentiableAt.cpow _ _ _ <;> norm_num [ hn.ne' ];
      refine' Or.inl _;
      exact disk_in_right_half_plane hr hn w hw;
    · -- Since $w$ is in the closed ball $D(r^n, 1)$, we know that $w$ has a positive real part.
      have h_pos_re : 0 < w.re := by
        exact disk_in_right_half_plane hr hn w hw;
      filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) h_pos_re ] with z hz;
      convert branch_eq_cpow_mul k z hz using 1

/-
If f is differentiable on a bounded convex set s with derivative bounded by C, then diam(f(s)) <= C * diam(s). Corrected version using Bornology.IsBounded and correct argument order.
-/
lemma diam_image_le_of_convex_norm_deriv_le {f : ℂ → ℂ} {s : Set ℂ} (hs : Convex ℝ s) (hb : Bornology.IsBounded s)
  (hf : ∀ x ∈ s, DifferentiableAt ℂ f x) {C : ℝ} (hC : 0 ≤ C)
  (h_bound : ∀ x ∈ s, ‖deriv f x‖ ≤ C) :
  Metric.diam (f '' s) ≤ C * Metric.diam s := by
  have h_lip : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y := by
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    -- The theorem concludes ‖f y - f x‖ ≤ C * ‖y - x‖.
    -- We want ‖f x - f y‖ ≤ C * ‖x - y‖.
    -- So we apply it with x=y and y=x.
    rw [norm_sub_rev, norm_sub_rev]
    exact Convex.norm_image_sub_le_of_norm_deriv_le hf h_bound hs hy hx
  apply Metric.diam_le_of_forall_dist_le
  · apply mul_nonneg hC Metric.diam_nonneg
  · intro y1 hy1 y2 hy2
    obtain ⟨x1, hx1, rfl⟩ := hy1
    obtain ⟨x2, hx2, rfl⟩ := hy2
    apply le_trans (h_lip x1 hx1 x2 hx2)
    apply mul_le_mul_of_nonneg_left
    · apply Metric.dist_le_diam_of_mem hb hx1 hx2
    · exact hC

/-
Bound the diameter of the component using the helper lemma. The diameter is at most 2 times the bound on the derivative.
-/
lemma diam_component_le {n : ℕ} (hn : n > 0) {r : ℝ} (hr : r > 1) (k : ℕ) :
  Metric.diam (component n r k) ≤ 2 * ((1 / n : ℝ) * (r^n - 1) ^ ((1 / n : ℝ) - 1)) := by
    -- Apply the Mean Value Inequality to bound the diameter of the image.
    have h_diam_image : Metric.diam (branch n k '' Metric.closedBall (r^n : ℂ) 1) ≤ (1 / n : ℝ) * (r^n - 1) ^ ((1 / n : ℝ) - 1) * Metric.diam (Metric.closedBall (r^n : ℂ) 1) := by
      apply diam_image_le_of_convex_norm_deriv_le;
      · exact convex_closedBall _ _;
      · exact Metric.isBounded_closedBall;
      · exact fun x a ↦ branch_differentiable_on_disk hn hr k x a;
      · exact mul_nonneg ( by positivity ) ( Real.rpow_nonneg ( sub_nonneg.2 ( one_le_pow₀ hr.le ) ) _ );
      · exact fun x a ↦ norm_deriv_branch_le hn hr k x a;
    refine le_trans h_diam_image ?_;
    rw [ mul_comm ] ; gcongr;
    · exact mul_nonneg ( by positivity ) ( Real.rpow_nonneg ( sub_nonneg.2 ( one_le_pow₀ hr.le ) ) _ );
    · refine' le_trans ( Metric.diam_le_of_forall_dist_le _ _ ) _ <;> norm_num;
      exacts [ 2, by norm_num, fun x hx y hy => le_trans ( dist_triangle_right _ _ _ ) ( by linarith ), by norm_num ]

/-
If r > 1, then for all n > 0, the set S = {z : |z^n - r^n| <= 1} has n connected components, and the diameter of these components tends to 0 as n tends to infinity.
-/
theorem main_result (r : ℝ) (hr : r > 1) :
  (∀ n > 0, Nat.card (ConnectedComponents (S n r)) = n) ∧
  (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x : S n r, Metric.diam (Subtype.val '' (connectedComponent x)) < ε) := by
    constructor;
    · exact fun n a ↦ card_components_eq_n a hr;
    · intro ε hε;
      -- By Lemma 2, the diameter of each component is bounded by $2 \cdot \frac{1}{n} \cdot (r^n - 1)^{\frac{1}{n} - 1}$.
      have h_diam_bound : ∀ n : ℕ, n > 0 → ∀ x : S n r, Metric.diam (Subtype.val '' connectedComponent x) ≤ 2 * ((1 / n : ℝ) * (r^n - 1) ^ ((1 / n : ℝ) - 1)) := by
        intro n hn x
        have h_connected_component : ∃ k < n, x ∈ component_subtype n r k := by
          have := S_subset_union_components hn hr x.2;
          aesop
        obtain ⟨k, hk_lt, hk_mem⟩ := h_connected_component
        have h_diam_bound : Metric.diam (component n r k) ≤ 2 * ((1 / n : ℝ) * (r^n - 1) ^ ((1 / n : ℝ) - 1)) := by
          convert diam_component_le hn hr k using 1
        exact (by
        refine' le_trans _ h_diam_bound;
        apply_rules [ Metric.diam_mono ];
        · have h_connected_component_eq : connectedComponent x = component_subtype n r k := by
            have h_connected_component_eq : connectedComponent x = connectedComponent (component_center n hn r hr k) := by
              have h_connected_component_eq : x ∈ component_subtype n r k ∧ component_center n hn r hr k ∈ component_subtype n r k := by
                exact ⟨ hk_mem, by exact Set.mem_image_of_mem _ ( by norm_num ) ⟩;
              have h_connected_component_eq : IsConnected (component_subtype n r k) := by
                exact isConnected_subtype_component hn hr k;
              have h_connected_component_eq : connectedComponent x = connectedComponent (component_center n hn r hr k) := by
                have h_connected_component_eq : component_subtype n r k ⊆ connectedComponent x := by
                  exact h_connected_component_eq.isPreconnected.subset_connectedComponent hk_mem
                have h_connected_component_eq' : component_subtype n r k ⊆ connectedComponent (component_center n hn r hr k) := by
                  apply_rules [ IsPreconnected.subset_connectedComponent ];
                  · exact ‹IsConnected ( component_subtype n r k ) ›.isPreconnected;
                  · aesop
                apply le_antisymm;
                · apply_rules [ IsPreconnected.subset_connectedComponent ];
                  · exact isPreconnected_connectedComponent;
                  · grind;
                · apply_rules [ IsPreconnected.subset_connectedComponent ];
                  exact isPreconnected_connectedComponent;
              exact h_connected_component_eq;
            exact h_connected_component_eq.trans ( isComponent_component_subtype hn hr k hk_lt ▸ rfl );
          aesop_cat;
        · exact IsCompact.isBounded ( component_compact hn hr k ));
      -- We need to show that $2 \cdot \frac{1}{n} \cdot (r^n - 1)^{\frac{1}{n} - 1}$ tends to $0$ as $n$ tends to infinity.
      have h_lim : Filter.Tendsto (fun n : ℕ => 2 * ((1 / n : ℝ) * (r^n - 1) ^ ((1 / n : ℝ) - 1))) Filter.atTop (nhds 0) := by
        -- We can factor out the constant $2$ and use the fact that $(r^n - 1)^{1/n - 1}$ tends to $0$ as $n$ tends to infinity.
        have h_factor : Filter.Tendsto (fun n : ℕ => (r^n - 1) ^ ((1 / n : ℝ) - 1)) Filter.atTop (nhds 0) := by
          -- We can rewrite $(r^n - 1)^{\frac{1}{n} - 1}$ as $r^{1 - n} \cdot (1 - \frac{1}{r^n})^{\frac{1}{n} - 1}$.
          suffices h_rewrite : Filter.Tendsto (fun n : ℕ => r ^ (1 - n : ℝ) * (1 - 1 / r ^ n) ^ ((1 / n : ℝ) - 1)) Filter.atTop (nhds 0) by
            refine h_rewrite.congr' ?_;
            filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
            rw [ show ( r ^ n - 1 : ℝ ) = r ^ n * ( 1 - 1 / r ^ n ) by rw [ mul_sub, mul_one, mul_div_cancel₀ _ ( by positivity ) ], Real.mul_rpow ( by positivity ) ( by exact sub_nonneg.2 <| div_le_self zero_le_one <| one_le_pow₀ hr.le ) ];
            field_simp;
            rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_div_cancel₀ _ ( by positivity ), mul_comm ];
          -- As $n \to \infty$, $r^{1 - n} \to 0$ because $r > 1$.
          have h_exp : Filter.Tendsto (fun n : ℕ => r ^ (1 - n : ℝ)) Filter.atTop (nhds 0) := by
            norm_num [ Real.rpow_sub ( by positivity : 0 < r ) ];
            exact tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt hr );
          convert h_exp.mul ( Filter.Tendsto.rpow ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt hr ) ) ) ( tendsto_one_div_atTop_nhds_zero_nat.sub_const 1 ) _ ) using 2 <;> norm_num;
        simpa using Filter.Tendsto.const_mul 2 ( Filter.Tendsto.mul ( tendsto_inverse_atTop_nhds_zero_nat ) h_factor );
      exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds hε ) ) |> fun ⟨ N, hN ⟩ => ⟨ N + 1, fun n hn x => lt_of_le_of_lt ( h_diam_bound n ( by linarith ) x ) ( hN n ( by linarith ) ) ⟩

open Polynomial

/--
If `f ∈ ℂ[X]` is monic (non-constant) and all its roots satisfy `‖z‖ ≤
r` for some `r < 2`, must the open sublevel set `{z : ℂ | ‖f.eval z‖ <
1}` have a connected component with diameter `> 2 - r`?
-/
def erdos_1048 : Prop :=
  ∀ f : ℂ[X],
    f.Monic →
    degree f ≥ 1 →
  ∀ r : ℝ,
    r < 2 →
    (∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ r) →
      let U : Set ℂ := { z : ℂ | ‖f.eval z‖ < 1 }
      ∃ x : ↥U,
        (2 - r) ≤
          Metric.diam (Subtype.val '' (connectedComponent x : Set (↥U)))

/-
The set S(n, r) is bounded for n > 0.
-/
lemma S_bounded {n : ℕ} (hn : n > 0) {r : ℝ} : Bornology.IsBounded (S n r) := by
  -- By definition of $S$, we know that $|z^n - r^n| \leq 1$ for all $z \in S$.
  have h_bound : ∀ z ∈ S n r, ‖z‖ ^ n ≤ ‖r‖ ^ n + 1 := by
    -- By definition of $S$, we know that $|z^n - r^n| \leq 1$ for all $z \in S$. Using the triangle inequality, we have $|z^n| \leq |r^n| + 1$.
    have h_triangle : ∀ z ∈ S n r, ‖z^n‖ ≤ ‖r^n‖ + 1 := by
      intro z hz;
      exact le_trans ( norm_le_of_mem_closedBall <| by simpa using hz ) ( by norm_num );
    aesop;
  exact isBounded_iff_forall_norm_le.mpr ⟨ ( ‖r‖ ^ n + 1 ) ^ ( 1 / n : ℝ ), fun z hz => le_trans ( le_of_eq ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( norm_nonneg _ ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ) ) ( Real.rpow_le_rpow ( by positivity ) ( h_bound z hz ) ( by positivity ) ) ⟩

/-
If K is a connected subset of a bounded set S, then the diameter of K is bounded by the diameter of some connected component of S.
-/
lemma connected_subset_le_diam {S : Set ℂ} (hS : Bornology.IsBounded S) (K : Set ℂ) (hK : IsConnected K) (hKS : K ⊆ S) (hK_nonempty : K.Nonempty) : ∃ x : S, Metric.diam K ≤ Metric.diam (Subtype.val '' (connectedComponent x)) := by
  cases' hK_nonempty with x hxK_nonempty;
  refine' ⟨ ⟨ x, hKS hxK_nonempty ⟩, _ ⟩;
  apply_rules [ Metric.diam_mono ];
  · intro y hyKop;
    refine' ⟨ ⟨ y, hKS hyKop ⟩, _, rfl ⟩;
    refine' ⟨ _, _ ⟩;
    exact { z : { x : ℂ // x ∈ S } | z.val ∈ K };
    simp_all +decide [ IsPreconnected, IsConnected ];
    rintro u v hu hv huv ⟨ z, hz ⟩ ⟨ w, hw ⟩;
    obtain ⟨ u', hu', hu'' ⟩ := hu; obtain ⟨ v', hv', hv'' ⟩ := hv; simp_all +decide [ Set.subset_def ] ;
    contrapose! hK;
    refine' fun _ => ⟨ u', v', hu', hv', _, _, _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
    · exact ⟨ _, hz.1, hu'' _ ( hKS _ hz.1 ) |>.2 hz.2 ⟩;
    · exact ⟨ _, hw.1, hv'' _ _ |>.2 hw.2 ⟩;
  · refine' hS.subset _;
    exact Subtype.coe_image_subset S (connectedComponent ⟨x, hKS hxK_nonempty⟩)

theorem not_erdos_1048 : ¬ erdos_1048 := by
  intro h_erdos_1048
  obtain ⟨hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∀ x : S n 1.5, Metric.diam (Subtype.val '' (connectedComponent x)) < 0.5 := by
    exact Exists.imp ( fun N hN n hn x => hN n hn x ) ( main_result 1.5 ( by norm_num ) |>.2 0.5 ( by norm_num ) );
  -- Consider the polynomial $P(z) = z^n - (1.5)^n$.
  set n := max hN 1
  set P : Polynomial ℂ := Polynomial.X^n - Polynomial.C ((1.5 : ℂ)^n);
  -- By `erdos_1048`, $U = \{z : |P(z)| < 1\}$ has a component $K$ (formally `Subtype.val '' (connectedComponent x)` for some $x \in U$) with diameter $\ge \epsilon$.
  obtain ⟨x, hx⟩ : ∃ x : { z : ℂ // ‖P.eval z‖ < 1 }, 0.5 ≤ Metric.diam (Subtype.val '' (connectedComponent x)) := by
    convert h_erdos_1048 P _ _ 1.5 _ _ using 1 <;> norm_num;
    · rfl;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ];
      exact lt_max_of_lt_right zero_lt_one;
    · rw [ Polynomial.degree_sub_C ] <;> norm_num;
      · exact le_max_right _ _;
      · positivity;
    · simp +zetaDelta at *;
      intro z hz; rw [ sub_eq_zero ] at hz; replace hz := congr_arg Norm.norm hz; norm_num at hz ⊢; aesop;
  -- By `connected_subset_le_diam`, there exists a component $C$ of $S(n, 1.5)$ such that $\text{diam}(K) \le \text{diam}(C)$.
  obtain ⟨C, hC⟩ : ∃ C : S n 1.5, Metric.diam (Subtype.val '' (connectedComponent x)) ≤ Metric.diam (Subtype.val '' (connectedComponent C)) := by
    have h_connected_subset_le_diam : ∀ K : Set ℂ, IsConnected K → K ⊆ S n 1.5 → K.Nonempty → ∃ C : S n 1.5, Metric.diam K ≤ Metric.diam (Subtype.val '' (connectedComponent C)) := by
      intros K hK hKS hK_nonempty
      apply connected_subset_le_diam (S_bounded (by
      exact lt_max_of_lt_right zero_lt_one)) K hK hKS hK_nonempty;
    apply h_connected_subset_le_diam;
    · exact isConnected_connectedComponent.image _ ( continuous_subtype_val.continuousOn );
    · rintro _ ⟨ y, hy, rfl ⟩;
      exact show ‖y.val ^ n - ( 1.5 : ℂ ) ^ n‖ ≤ 1 from le_of_lt <| by simpa [ P ] using y.2;
    · exact ⟨ _, Set.mem_image_of_mem _ ( mem_connectedComponent ) ⟩;
  exact not_lt_of_ge ( le_trans hx hC ) ( by linarith [ ‹∀ n ≥ hN, ∀ x : S n 1.5, Metric.diam ( Subtype.val '' connectedComponent x ) < 0.5› n ( le_max_left _ _ ) C ] )

#print axioms not_erdos_1048
-- 'not_erdos_1048' depends on axioms: [propext, Classical.choice, Quot.sound]
