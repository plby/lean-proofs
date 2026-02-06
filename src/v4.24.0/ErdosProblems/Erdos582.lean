/-

This is a Lean formalization of a solution to Erdős Problem 582.
https://www.erdosproblems.com/forum/thread/582

The original proof was found by: Folkman

[Fo70] Folkman, Jon, Graphs with monochromatic complete subgraphs in
every edge coloring. SIAM J. Appl. Math. (1970), 19-24.


A proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have constructed a graph $G$ that is $K_4$-free (clique number 3) and edge-Ramsey for triangles ($G \to (K_3, K_3)$).
The graph $G$ is constructed based on the Folkman graph construction.
We defined the graph $G$ using auxiliary graphs $H_1$ and $H_2$ with specific Ramsey properties.
We proved that $\omega(G) = 3$ (`GraphG_cliqueNum_eq_three`).
We proved that for any 2-edge-coloring of $G$, there exists a monochromatic triangle (`folkman_theorem`).
Finally, we combined these results to prove the main theorem `erdos_582`.
-/

import Mathlib

--set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical
open SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (v0 : V) (H' : SimpleGraph W)

set_option maxHeartbeats 0
--set_option maxRecDepth 4000

/-
Definitions of vertex-partition Ramsey property, and edge-Ramsey property for triangles.
-/
def VertexPartitionRamsey {V W : Type*} (n : ℕ) (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∀ (f : W → Fin n), ∃ i, ∃ (S : Set W), (∀ w ∈ S, f w = i) ∧ Nonempty (G ≃g H.induce S)

def EdgeRamseyTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (c : G.edgeSet → Bool), ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
    c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩

/-
If $H \Rightarrow_2 K$ and $K \Rightarrow_n G$, then $H \Rightarrow_{n+1} G$.
-/
lemma ramsey_trans {V W U : Type*} [Fintype V] [Fintype W] [Fintype U] [DecidableEq V] [DecidableEq W] [DecidableEq U]
  (G : SimpleGraph V) (K : SimpleGraph W) (H : SimpleGraph U)
  (n : ℕ) (hn : n ≥ 1)
  (hK : VertexPartitionRamsey n K G)
  (hH : VertexPartitionRamsey 2 H K) :
  VertexPartitionRamsey (n + 1) H G := by
    intro f;
    -- Define a new function $g : U \to \{0, 1\}$ by $g(u) = 0$ if $f(u) < n$, and $g(u) = 1$ if $f(u) = n$.
    set g : U → Fin 2 := fun u => if f u < n then 0 else 1;
    -- By hypothesis $hH$, there exists $i \in \{0, 1\}$ and $S \subseteq U$ such that $H[S] \cong K$ and $g$ is constant $i$ on $S$.
    obtain ⟨i, S, hS⟩ : ∃ i : Fin 2, ∃ S : Set U, (∀ w ∈ S, g w = i) ∧ Nonempty (K ≃g H.induce S) := by
      have := hH g;
      exact this;
    -- Let's consider the two cases for $i$.
    by_cases hi : i = 0;
    · -- Since $g$ is constant $0$ on $S$, we have $f(u) < n$ for all $u \in S$.
      have h_f_lt_n : ∀ w ∈ S, f w < n := by
        grind;
      -- Since $K \Rightarrow_n G$, there exists $j \in \{0, \dots, n-1\}$ and $T \subseteq W$ such that $K[T] \cong G$ and $f'$ is constant $j$ on $T$.
      obtain ⟨j, T, hT⟩ : ∃ j : Fin n, ∃ T : Set W, (∀ w ∈ T, (fun w => ⟨f (hS.right.some w), h_f_lt_n _ (hS.right.some w).2⟩) w = j) ∧ Nonempty (G ≃g K.induce T) := by
        convert hK _;
      refine' ⟨ ⟨ j, by linarith [ Fin.is_lt j ] ⟩, Set.image ( fun w : T => ( hS.2.some w : U ) ) ( Set.univ : Set T ), _, _ ⟩ <;> simp_all +decide
      · exact fun w hw => Fin.ext <| by simpa [ Fin.ext_iff ] using congr_arg Fin.val ( hT.1 w hw ) ;
      · refine' ⟨ hT.2.some.trans _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        refine' Equiv.ofBijective ( fun x => ⟨ _, Set.mem_image_of_mem _ ( Set.mem_univ x ) ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
        all_goals simp_all +decide
        · have := hS.2.some.injective ( Subtype.ext hxy ) ; aesop;
        · rcases x with ⟨ x, hx ⟩ ; aesop;
        · intro h; have := hS.2.some.symm.map_adj_iff.2 h; aesop;
        · intro h; have := hS.2.some.map_adj_iff.2 h; aesop;
    · -- Since $i = 1$, for all $w \in S$, we have $f w = n$.
      have h_f_eq_n : ∀ w ∈ S, f w = n := by
        grind;
      -- Since $K$ contains a monochromatic copy of $G$ with color $n$, we can find such a copy in $H$.
      obtain ⟨T, hT⟩ : ∃ T : Set S, Nonempty (G ≃g (SimpleGraph.induce S H).induce T) := by
        obtain ⟨ ϕ ⟩ := hS.2;
        obtain ⟨ T, hT ⟩ := hK ( fun w => ⟨ 0, by linarith ⟩ );
        obtain ⟨ S, hS₁, hS₂ ⟩ := hT;
        refine' ⟨ ϕ '' S, _ ⟩;
        refine' ⟨ hS₂.some.trans _ ⟩;
        refine' ⟨ _, _, _ ⟩;
        refine' Equiv.ofBijective ( fun x => ⟨ ϕ x, Set.mem_image_of_mem _ x.2 ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
        all_goals simp_all +decide [ SimpleGraph.induce ];
        · grind;
        · rcases x with ⟨ x, hx ⟩ ; aesop;
        · exact fun h => ϕ.map_adj_iff.mp h;
        · exact fun h => ϕ.map_adj_iff.mpr h;
      refine' ⟨ ⟨ n, Nat.lt_succ_self _ ⟩, T.image Subtype.val, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.induce, Set.image ];
      · exact fun w hw hw' => Fin.ext ( h_f_eq_n w hw );
      · obtain ⟨ e ⟩ := hT;
        refine' ⟨ e.trans _ ⟩;
        refine' ⟨ _, _ ⟩;
        refine' Equiv.ofBijective ( fun x => ⟨ x.val, x, x.2, rfl ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
        all_goals simp_all +decide [ SimpleGraph.comap ];
        · grind;
        · rcases x with ⟨ x, ⟨ a, ha, rfl ⟩ ⟩ ; aesop;

/-
Reduction of the existence of $H(n,G)$ to the case $n=2$.
If for every graph $G$ there exists $H$ such that $\om(H)=\om(G)$ and $H \Rightarrow_2 G$, then for every $n \ge 1$ and every $G$ there exists $H$ such that $\om(H)=\om(G)$ and $H \Rightarrow_n G$.
-/
theorem exists_H_n_of_exists_H_2
  (h2 : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey 2 H G) :
  ∀ (n : ℕ) (hn : n ≥ 1) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey n H G := by
        intro n hn;
        induction' n, hn using Nat.le_induction with n hn ih;
        · -- For the base case $n = 1$, we can take $H = G$.
          intros V _ _ G
          use V, inferInstance, inferInstance, G
          simp [VertexPartitionRamsey];
          intro f; use Set.univ; simp +decide [ Fin.eq_zero ] ;
          refine' ⟨ _, _ ⟩;
          exacts [ Equiv.ofBijective ( fun x => ⟨ x, trivial ⟩ ) ⟨ fun x y hxy => by simpa using hxy, fun x => by cases x; exact ⟨ _, rfl ⟩ ⟩, by simp +decide [ SimpleGraph.induce ] ];
        · intro V _ _ G
          obtain ⟨W, x, x', H, hH⟩ := ih V G
          obtain ⟨W', x', x'', H', hH'⟩ := h2 W H;
          use W', x', x'', H';
          exact ⟨ hH'.1.trans hH.1, ramsey_trans G H H' n hn hH.2 hH'.2 ⟩

/-
Definitions of $V'$, $G'$, $V''$, $G''$, and $X$, and the lemma that $X$ is nonempty.
-/
def V_prime : Set V := {v | v ≠ v0}
def G_prime : SimpleGraph (V_prime v0) := G.induce (V_prime v0)

def V_double_prime : Set (V_prime v0) := {u | G.Adj u.val v0}
def G_double_prime : SimpleGraph (V_double_prime G v0) := (G_prime G v0).induce (V_double_prime G v0)

def X_set : Set (Set W) := { S | Nonempty ((H'.induce S) ≃g (G_double_prime G v0)) }

lemma X_nonempty (h : VertexPartitionRamsey 2 H' (G_prime G v0)) : (X_set G v0 H').Nonempty := by
  -- By definition of $X_set$, we need to show that there exists a subset $S \subseteq (G 인덱스 (SimpleGraph.induce {v0}ᶜ G)).vertexSet$ such that $H'.induce (Gszczę (H'.induce {v0}ᶜ H')) S) \cong G''$.
  obtain ⟨S, hS⟩ := h (fun _ => 0);
  obtain ⟨ S', hS' ⟩ := hS;
  obtain ⟨ f, hf ⟩ := hS'.2;
  refine' ⟨ _, _, _ ⟩;
  exact Set.image ( fun x : { x : V // x ≠ v0 ∧ G.Adj x v0 } => f ⟨ x, by
    exact x.2.1 ⟩ ) ( Set.univ : Set { x : V // x ≠ v0 ∧ G.Adj x v0 } );
  all_goals generalize_proofs at *;
  refine' Equiv.ofBijective _ ⟨ _, _ ⟩;
  use fun x => ⟨ f.symm ⟨ x, by
    grind ⟩, by
    rcases x with ⟨ x, hx ⟩;
    rcases hx with ⟨ y, -, rfl ⟩;
    simp +decide [ V_double_prime ];
    exact y.2.2 ⟩
  all_goals generalize_proofs at *
  all_goals generalize_proofs at *;
  all_goals norm_num [ Function.Injective, Function.Surjective ];
  exact fun a ha ha' => ⟨ _, ⟨ a, ⟨ ha, ha' ⟩, rfl ⟩, by simp +decide ⟩;
  intro a x hx hx' hx'' a' x' hx'' hx''' hx''''; subst_vars; simp +decide
  convert hf.symm using 1

/-
Definitions of parameters and f_map.
-/

def t_param (W : Type*) [Fintype W] : ℕ := 2 ^ (Fintype.card W)
def r_param (V : Type*) [Fintype V] : ℕ := Fintype.card V
def I_param (V W : Type*) [Fintype V] [Fintype W] : ℕ := (r_param V - 1) * t_param W + 1

abbrev I_type (V W : Type*) [Fintype V] [Fintype W] : Type := Fin (I_param V W)

abbrev J_type (V W : Type*) [Fintype V] [Fintype W] : Type := { s : Finset (I_type V W) // s.card = r_param V }

noncomputable def f_map (V W : Type*) [Fintype V] [Fintype W] (T : J_type V W) : {x // x ∈ T.val} ≃ V :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, T.property, r_param]
  )

/-
Definition of f_map_val.
-/

noncomputable def f_map_val (T : J_type V W) (i : I_type V W) (h : i ∈ T.val) : V :=
  f_map V W T ⟨i, h⟩

/-
Definition of X_type and its instances.
-/
def X_type : Type _ := { S : Set W // S ∈ X_set G v0 H' }

noncomputable instance : Fintype (X_type G v0 H') := by
  have : Finite (Set W) := Finite.of_fintype (Set W)
  have : Finite (X_type G v0 H') := Subtype.finite
  exact Fintype.ofFinite _

noncomputable instance : DecidableEq (X_type G v0 H') := Classical.decEq _

/-
Definition of VertexH and its instances, using unfold to help type class inference.
-/
def VertexH : Type _ := (V × (X_type G v0 H') × (J_type V W)) ⊕ (W × (I_type V W))

noncomputable instance : Fintype (VertexH G v0 H') := by
  unfold VertexH
  infer_instance

noncomputable instance : DecidableEq (VertexH G v0 H') := by
  unfold VertexH
  infer_instance

/-
Definition of AdjH.
-/
noncomputable def AdjH (x y : VertexH G v0 H') : Prop :=
  match x, y with
  | Sum.inl (v, S, T), Sum.inl (v', S', T') => S = S' ∧ T = T' ∧ G.Adj v v'
  | Sum.inr (w, i), Sum.inr (w', i') => i = i' ∧ H'.Adj w w'
  | Sum.inl (v, S, T), Sum.inr (w, i) => w ∈ S.val ∧ ∃ (h : i ∈ T.val), f_map_val T i h = v
  | Sum.inr (w, i), Sum.inl (v, S, T) => w ∈ S.val ∧ ∃ (h : i ∈ T.val), f_map_val T i h = v

/-
Definition of GraphH using the previously defined AdjH.
-/
noncomputable def GraphH : SimpleGraph (VertexH G v0 H') where
  Adj := AdjH G v0 H'
  symm := by
    intro x y hxy; induction y; simp +decide [ AdjH ] ;
    · rcases x with ( ⟨ v', S', T' ⟩ | ⟨ w', i' ⟩ ) <;> simp +decide [ AdjH ] at hxy ⊢
      all_goals generalize_proofs at *;
      · exact ⟨ hxy.1.symm, hxy.2.1.symm, hxy.2.2.symm ⟩;
      · exact hxy;
    · cases x <;> simp +decide [ AdjH ] at hxy ⊢ ; aesop ( simp_config := { singlePass := true } ) ;
      exact ⟨ hxy.1.symm, hxy.2.symm ⟩
  loopless := by
    intro x
    unfold AdjH at * ; aesop

/-
Lower bound on the clique number of H(2,G).
-/
lemma GraphH_cliqueNum_ge
  (h_ramsey : VertexPartitionRamsey 2 H' (G_prime G v0)) :
  G.cliqueNum ≤ (GraphH G v0 H').cliqueNum := by
    -- Since $H' \Rightarrow_2 G'$, $X$ is nonempty. Let $S \in X$ and $T \in J$.
    obtain ⟨S, hS⟩ : ∃ S : Set W, S ∈ X_set G v0 H' := by
      exact Set.nonempty_iff_ne_empty.2 ( X_nonempty G v0 H' h_ramsey |> Set.Nonempty.ne_empty )
    obtain ⟨T, hT⟩ : ∃ T : J_type V W, True := by
      have h_card_I : Finset.card (Finset.univ : Finset (I_type V W)) ≥ r_param V := by
        simp +decide [ r_param, I_param ];
        rcases k : Fintype.card V with ( _ | _ | k ) <;> simp_all +decide [ t_param ];
        exact Nat.one_le_pow _ _ ( by decide );
      obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq h_card_I;
      exact ⟨ ⟨ T, hT.2 ⟩, trivial ⟩;
    -- The map $v \mapsto (v, S, T)$ is an embedding of $G$ into $H$.
    have h_embedding : ∃ (f : V → VertexH G v0 H'), Function.Injective f ∧ ∀ u v, G.Adj u v → (GraphH G v0 H').Adj (f u) (f v) := by
      refine' ⟨ fun v => Sum.inl ( v, ⟨ S, hS ⟩, T ), _, _ ⟩ <;> simp +decide [ Function.Injective ];
      · grind;
      · exact fun u v huv => by exact ⟨ rfl, rfl, huv ⟩ ;
    obtain ⟨ f, hf_inj, hf_adj ⟩ := h_embedding;
    refine' le_csSup _ _;
    · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
    · obtain ⟨ s, hs ⟩ := ( show ∃ s : Finset V, G.IsNClique ( G.cliqueNum ) s from by
                              exact exists_isNClique_cliqueNum );
      refine' ⟨ Finset.image f s, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · intro x hx y hy hxy; aesop;
      · rw [ Finset.card_image_of_injective _ hf_inj, hs.2 ]


/-
If a clique contains at least two type A vertices, its size is at most the clique number of G.
-/
lemma clique_case_two_A
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (x y : VertexH G v0 H')
  (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
  (hx_A : ∃ a, x = Sum.inl a) (hy_A : ∃ b, y = Sum.inl b) :
  Q.card ≤ G.cliqueNum := by
    -- Since there are at least two type A vertices, there cannot be any type B vertices in $Q$.
    have h_no_B : ∀ z ∈ Q, ¬∃ w i, z = Sum.inr (w, i) := by
      intro z hz hz_B
      obtain ⟨w, i, hz_B⟩ := hz_B
      have h_adj_x : (GraphH G v0 H').Adj x z := by
        exact hQ ( by aesop ) ( by aesop ) ( by aesop )
      have h_adj_y : (GraphH G v0 H').Adj y z := by
        exact hQ hy hz ( by aesop ) |> fun h => by aesop;
      generalize_proofs at *; (
      rcases hx_A with ⟨ a, rfl ⟩ ; rcases hy_A with ⟨ b, rfl ⟩ ; simp_all +decide [ GraphH ] ;
      rcases a with ⟨ a₁, a₂, a₃ ⟩ ; rcases b with ⟨ b₁, b₂, b₃ ⟩ ; simp_all +decide [ AdjH ] ;
      unfold AdjH at hQ; specialize hQ hx hy; aesop;)
    generalize_proofs at *; (
    -- Since there are at least two type A vertices, there cannot be any type B vertices in $Q$, so $Q$ consists of type A vertices with fixed $S, T$.
    have h_typeA : ∃ S : X_type G v0 H', ∃ T : J_type V W, ∀ z ∈ Q, ∃ a : V, z = Sum.inl (a, S, T) := by
      -- Since there are at least two type A vertices, there cannot be any type B vertices in $Q$, so $Q$ consists of type A vertices with fixed $S, T$. Let's obtain these $S$ and $T$.
      obtain ⟨a, ha⟩ := hx_A
      obtain ⟨b, hb⟩ := hy_A
      have hS : ∀ z ∈ Q, ∃ c : V × (X_type G v0 H') × (J_type V W), z = Sum.inl c ∧ c.2.1 = a.2.1 ∧ c.2.2 = a.2.2 := by
        intro z hz
        obtain ⟨c, hc⟩ : ∃ c : V × (X_type G v0 H') × (J_type V W), z = Sum.inl c := by
          cases z <;> aesop ( simp_config := { singlePass := true } ) ;
        generalize_proofs at *; (
        have := hQ hx hz; have := hQ hy hz; simp_all +decide [ GraphH ] ;
        by_cases hac : a = c <;> by_cases hbc : b = c <;> simp_all +decide [ AdjH ] ; aesop ( simp_config := { singlePass := true } ) ;
        · exact ⟨ c.1, by aesop ⟩;
        · grind)
      generalize_proofs at *; (
      exact ⟨ a.2.1, a.2.2, fun z hz => by obtain ⟨ c, rfl, hc₁, hc₂ ⟩ := hS z hz; exact ⟨ c.1, by aesop ⟩ ⟩)
    generalize_proofs at *; (
    obtain ⟨ S, T, hS ⟩ := h_typeA
    have h_clique_G : (Finset.image (fun z => (z : VertexH G v0 H').elim (fun a => a.1) (fun b => v0)) Q).card ≤ G.cliqueNum := by
      have h_clique_G : ∀ u v : V, u ∈ Finset.image (fun z => (z : VertexH G v0 H').elim (fun a => a.1) (fun b => v0)) Q → v ∈ Finset.image (fun z => (z : VertexH G v0 H').elim (fun a => a.1) (fun b => v0)) Q → u ≠ v → G.Adj u v := by
        intros u v hu hv huv
        obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.mp hv
        have h_adj : (GraphH G v0 H').Adj z₁ z₂ := by
          exact hQ hz₁ hz₂ ( by aesop ) |> fun h => by aesop;
        generalize_proofs at *; (
        rcases hS z₁ hz₁ with ⟨ a₁, rfl ⟩ ; rcases hS z₂ hz₂ with ⟨ a₂, rfl ⟩ ; simp_all +decide [ GraphH ] ;
        cases h_adj ; aesop ( simp_config := { singlePass := true } ) ;)
      generalize_proofs at *; (
      have h_clique_G : ∀ (S : Finset V), (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) → S.card ≤ G.cliqueNum := by
        intro S hS; exact (by
        refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
        · exact ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ S, by rw [ SimpleGraph.isNClique_iff ] ; exact ⟨ by aesop_cat, by aesop_cat ⟩ ⟩);
      generalize_proofs at *; (
      exact h_clique_G _ fun u hu v hv huv => by aesop;))
    generalize_proofs at *; (
    rwa [ Finset.card_image_of_injOn ] at h_clique_G ; intro a ha b hb ; cases hS a ha ; cases hS b hb ; aesop ( simp_config := { singlePass := true } ) ;)))

/-
The clique number of G'' plus 1 is at most the clique number of G.
-/
lemma cliqueNum_G_double_prime_le :
  (G_double_prime G v0).cliqueNum + 1 ≤ G.cliqueNum := by
    simp +decide [ SimpleGraph.cliqueNum ];
    refine' le_csSup _ _;
    · exact ⟨ Fintype.card V, fun n hn => by rcases hn with ⟨ s, hs ⟩ ; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
    · -- Let $K$ be a clique in $G''$ with size equal to the clique number of $G''$.
      obtain ⟨K, hK⟩ : ∃ K : Finset (↥(V_double_prime G v0)), (G_double_prime G v0).IsNClique (sSup {n | ∃ s, (G_double_prime G v0).IsNClique n s}) K := by
        have := Nat.sSup_mem ( show { n : ℕ | ∃ s : Finset ( ↥ ( V_double_prime G v0 ) ), ( G_double_prime G v0 ).IsNClique n s }.Nonempty from ?_ );
        · exact this ⟨ _, fun n hn => hn.choose_spec.card_eq.symm ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
      -- Let $K'$ be the set of vertices in $G$ corresponding to the vertices in $K$.
      obtain ⟨K', hK'⟩ : ∃ K' : Finset V, K'.card = K.card ∧ ∀ x ∈ K', x ≠ v0 ∧ G.Adj x v0 ∧ ∀ y ∈ K', y ≠ x → G.Adj x y := by
        use K.image (fun x => x.val.val);
        rw [ Finset.card_image_of_injective ];
        · simp_all +decide [ SimpleGraph.isNClique_iff ];
          intro x hx₁ hx₂ hx₃; have := hK.1 hx₃; aesop;
        · aesop_cat;
      refine' ⟨ Insert.insert v0 K', _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · exact ⟨ fun x hx y hy hxy => hK'.2 x hx |>.2.2 y hy ( Ne.symm hxy ), fun x hx hx' => hK'.2 x hx |>.2.1.symm ⟩;
      · grind

/-
If a clique contains a type A vertex and a type B vertex, the type B vertex must be in the subset S associated with the type A vertex.
-/
lemma clique_case_one_A_subset_S
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (v : V) (S : X_type G v0 H') (T : J_type V W)
  (hv : Sum.inl (v, S, T) ∈ Q)
  (w : W) (i : I_type V W)
  (hw : Sum.inr (w, i) ∈ Q) :
  w ∈ S.val := by
    have := hQ hv hw; simp_all +decide [ GraphH ] ;
    exact this.1

/-
The type B vertices in a clique containing a specific type A vertex correspond to a clique in H' that is contained in S.
-/
lemma clique_case_one_A_type_B_is_clique_in_S
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (v : V) (S : X_type G v0 H') (T : J_type V W)
  (hv : Sum.inl (v, S, T) ∈ Q) :
  ∃ (W_B : Finset W),
    W_B.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card ∧
    H'.IsClique W_B ∧
    ∀ w ∈ W_B, w ∈ S.val := by
      -- Let $Q_B$ be the set of type B vertices in $Q$. If $Q_B$ is empty, take $W_B = \emptyset$.
      by_cases hQB : ∃ y ∈ Q, ∃ w i, y = Sum.inr (w, i);
      · -- By `clique_case_one_A_same_fiber`, all $(w, i) \in Q_B$ have $i = i_0$.
        obtain ⟨w0, i0, hw0⟩ : ∃ w0 i0, ∃ y ∈ Q, y = Sum.inr (w0, i0) ∧ ∀ y ∈ Q, (∃ w i, y = Sum.inr (w, i)) → ∃ w i, y = Sum.inr (w, i) ∧ i = i0 := by
          obtain ⟨ y, hy, w, i, rfl ⟩ := hQB;
          refine' ⟨ w, i, _, hy, rfl, fun y hy' hy'' => _ ⟩;
          rcases hy'' with ⟨ w', i', rfl ⟩ ; have := hQ hy hy' ; simp_all +decide [ SimpleGraph.IsClique ] ;
          unfold GraphH at this; simp_all +decide
          unfold AdjH at this; simp_all +decide
          grind;
        -- Let $W_B = \{ w \mid (w, i_0) \in Q_B \}$.
        obtain ⟨W_B, hW_B⟩ : ∃ W_B : Finset W, W_B.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card ∧ ∀ w ∈ W_B, ∃ y ∈ Q, y = Sum.inr (w, i0) ∧ w ∈ S.val := by
          have hW_B : ∀ y ∈ Q, (∃ w i, y = Sum.inr (w, i)) → ∃ w, y = Sum.inr (w, i0) ∧ w ∈ S.val := by
            intros y hy hyB
            obtain ⟨w, i, hy_eq, hi⟩ : ∃ w i, y = Sum.inr (w, i) ∧ i = i0 := by
              exact hw0.choose_spec.2.2 y hy hyB;
            have := clique_case_one_A_subset_S G v0 H' Q hQ v S T hv w i0; aesop;
          choose! f hf1 hf2 using hW_B;
          use Finset.image ( fun y : { y : VertexH G v0 H' // y ∈ Q ∧ ∃ w i, y = Sum.inr ( w, i ) } => f y.val y.2.1 y.2.2 ) ( Finset.univ.filter fun y : { y : VertexH G v0 H' // y ∈ Q ∧ ∃ w i, y = Sum.inr ( w, i ) } => True ) ; simp +decide
          refine' ⟨ _, _ ⟩;
          · rw [ Finset.card_image_of_injective ];
            · refine' Finset.card_bij ( fun y hy => y.val ) _ _ _ <;> simp +decide [ Finset.mem_univ ];
            · intro x y hxy;
              grind +ring;
          · grind +ring;
        refine' ⟨ W_B, hW_B.1, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.IsClique ];
        intro w hw w' hw' hne; have := hQ ( hW_B.2 w hw |>.1 ) ( hW_B.2 w' hw' |>.1 ) ; simp_all +decide
        unfold GraphH at this; simp_all +decide
        unfold AdjH at this; simp_all +decide
        grind;
      · refine' ⟨ ∅, _, _, _ ⟩ <;> simp_all +decide
        exact Eq.symm ( Finset.card_eq_zero.mpr <| Finset.filter_eq_empty_iff.mpr fun x hx => by aesop )

/-
If a clique is contained in a subset of vertices, its size is at most the clique number of the induced subgraph on that subset.
-/
lemma clique_subset_le_cliqueNum_induce
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Set V) [Fintype S] [DecidableEq S]
  (C : Finset V) (hC : G.IsClique C) (hCS : ∀ v ∈ C, v ∈ S) :
  C.card ≤ (G.induce S).cliqueNum := by
    refine' le_csSup _ _;
    · exact ⟨ _, fun n hn => by rcases hn with ⟨ s, hs ⟩ ; exact hs.card_eq.symm ▸ Finset.card_le_univ _ ⟩;
    · use Finset.filter (fun v => v.val ∈ C) (Finset.univ : Finset S);
      constructor;
      · intro x hx y hy hxy; specialize hC ( by aesop : ( x : V ) ∈ C ) ( by aesop : ( y : V ) ∈ C ) ; aesop;
      · refine' Finset.card_bij ( fun v hv => v ) _ _ _ <;> aesop

/-
If a clique contains exactly one type A vertex, its size is at most the clique number of G'' plus 1.
-/
lemma clique_case_one_A
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (x : VertexH G v0 H')
  (hx : x ∈ Q)
  (hx_A : ∃ a, x = Sum.inl a)
  (h_unique : ∀ y ∈ Q, (∃ b, y = Sum.inl b) → y = x) :
  Q.card ≤ (G_double_prime G v0).cliqueNum + 1 := by
    obtain ⟨v, S, T, hv⟩ : ∃ v : V, ∃ S : X_type G v0 H', ∃ T : J_type V W, x = Sum.inl (v, S, T) := by
      bound;
    -- By `clique_case_one_A_type_B_is_clique_in_S`, there exists `W_B ⊆ W` such that `|W_B| = |Q_B|`, `W_B` is a clique in `H'`, and `W_B ⊆ S`.
    obtain ⟨W_B, hW_B_card, hW_B_clique, hW_B_subset⟩ : ∃ (W_B : Finset W),
      W_B.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card ∧
      H'.IsClique W_B ∧
      ∀ w ∈ W_B, w ∈ S.val := by
        convert clique_case_one_A_type_B_is_clique_in_S G v0 H' Q hQ v S T _;
        exact hv ▸ hx;
    -- By `clique_subset_le_cliqueNum_induce`, `|W_B| \le \omega(H'.induce S)`.
    have hW_B_le_cliqueNum_induce : W_B.card ≤ (H'.induce S.val).cliqueNum := by
      convert clique_subset_le_cliqueNum_induce H' S.val W_B hW_B_clique hW_B_subset;
    -- Since `S \in X`, `H'.induce S \cong G''`, so $\omega(H'.induce S) = \omega(G'')$.
    have h_cliqueNum_H'_induce_S : (H'.induce S.val).cliqueNum = (G_double_prime G v0).cliqueNum := by
      obtain ⟨ f, hf ⟩ := S.2;
      refine' le_antisymm _ _ <;> simp +decide [ SimpleGraph.cliqueNum ];
      · refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · intro b x hx
          obtain ⟨hx_card, hx_clique⟩ := hx
          have h_image_clique : (G_double_prime G v0).IsNClique b (Finset.image (fun y => f y) x) := by
            constructor <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
            intro y hy z hz; obtain ⟨ a, ha, rfl ⟩ := hy; obtain ⟨ b, hb, rfl ⟩ := hz; specialize hx_card ha hb; aesop;
          exact le_csSup (by
          exact ⟨ Fintype.card ( V_double_prime G v0 ), fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩) ⟨_, h_image_clique⟩
      · refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · intro b x hx; refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
          · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
          · refine' ⟨ Finset.image ( fun y => ⟨ f.symm y |>.1, f.symm y |>.2 ⟩ ) x, _ ⟩;
            simp +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff ] at hx ⊢;
            simp +decide [ Set.Pairwise, Finset.card_image_of_injective, Function.Injective, hx.2 ];
            exact fun a ha ha' b hb hb' hab => hf a ha b hb |>.1 ( hx.1 ha' hb' ( by aesop ) );
    -- Since `Q` contains exactly one type A vertex (which is `x`), `|Q| = |Q_B| + 1`.
    have hQ_card : Q.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card + 1 := by
      have hQ_card : Q.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card + (Q.filter (fun y => ∃ a, y = Sum.inl a)).card := by
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ ← Finset.sum_add_distrib, Finset.card_eq_sum_ones ];
        refine' Finset.sum_congr rfl fun x hx => _;
        rcases x with ( ⟨ v, S, T ⟩ | ⟨ w, i ⟩ ) <;> simp +decide at hx ⊢;
      rw [ hQ_card, show Finset.filter ( fun y => ∃ a, y = Sum.inl a ) Q = { x } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ hx, hx_A ⟩, fun y hy => h_unique y ( Finset.mem_filter.mp hy |>.1 ) ( Finset.mem_filter.mp hy |>.2 ) ⟩ ] ; simp +decide [ hv ] ;
    linarith

/-
If a clique contains no type A vertices, its size is at most the clique number of H'.
-/
lemma clique_case_zero_A
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (h_no_A : ∀ x ∈ Q, ∀ a, x ≠ Sum.inl a) :
  Q.card ≤ H'.cliqueNum := by
    -- Since there are no type A vertices in Q, all vertices in Q must be of type B.
    have h_all_B : ∀ x ∈ Q, ∃ w i, x = Sum.inr (w, i) := by
      intro x hx; specialize h_no_A x hx; rcases x with ( ⟨ v, S, T ⟩ | ⟨ w, i ⟩ ) <;> tauto;
    -- Since all vertices in Q are of type B, they must lie in the same fiber. Let's denote this fiber by i.
    obtain ⟨i, hi⟩ : ∃ i : I_type V W, ∀ x ∈ Q, ∃ w, x = Sum.inr (w, i) := by
      rcases Q.eq_empty_or_nonempty with ( rfl | ⟨ x, hx ⟩ ) <;> simp_all +decide [ SimpleGraph.IsClique ];
      · exact ⟨ 0, Nat.zero_lt_succ _ ⟩;
      · obtain ⟨ w, i, rfl ⟩ := h_all_B x hx; use i; intro y hy; obtain ⟨ w', i', rfl ⟩ := h_all_B y hy; have := hQ hx hy; simp_all +decide [ GraphH ] ;
        by_cases hi : i = i' <;> simp_all +decide [ AdjH ];
        · exact ⟨ w', rfl ⟩;
        · cases this ; tauto;
    choose f hf using hi;
    -- Since $f$ is a bijection between $Q$ and a subset of $W$, and $Q$ is a clique in $H$, the image of $Q$ under $f$ is a clique in $H'$.
    have h_image_clique : (Finset.image (fun x => f x.1 x.2) (Q.attach)).card ≤ H'.cliqueNum := by
      have h_image_clique : ∀ x ∈ Q.attach, ∀ y ∈ Q.attach, x ≠ y → H'.Adj (f x.1 x.2) (f y.1 y.2) := by
        intro x hx y hy hxy
        have h_adj : (GraphH G v0 H').Adj (Sum.inr (f x.1 x.2, i)) (Sum.inr (f y.1 y.2, i)) := by
          convert hQ ( show x.val ∈ Q from x.2 ) ( show y.val ∈ Q from y.2 ) ( by simpa [ Subtype.ext_iff ] using hxy ) using 1
          generalize_proofs at *;
          · exact hf _ _ ▸ rfl;
          · exact hf _ _ ▸ rfl
        generalize_proofs at *;
        unfold GraphH at h_adj; simp +decide [ AdjH ] at h_adj; tauto;
      refine' le_csSup _ _;
      · exact ⟨ Fintype.card W, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
      · refine' ⟨ Finset.image ( fun x : { x // x ∈ Q } => f x.1 x.2 ) Q.attach, _, _ ⟩;
        · intro x hx y hy hxy;
          grind;
        · convert rfl;
    rwa [ Finset.card_image_of_injOn, Finset.card_attach ] at h_image_clique;
    intro x hx y hy; have := hf x.1 x.2; have := hf y.1 y.2; simp +decide at *;
    grind

/-
The clique number of H(2,G) is at most the clique number of G.
-/
lemma GraphH_cliqueNum_le
  (h_clique : H'.cliqueNum = (G_prime G v0).cliqueNum) :
  (GraphH G v0 H').cliqueNum ≤ G.cliqueNum := by
    -- Let $Q$ be a clique in $H(2,G)$. We need to show that $|Q| \le G.cliqueNum$ by considering the three cases: $Q$ contains at least two type A vertices, $Q$ contains exactly one type A vertex, and $Q$ contains no type A vertices.
    have h_clique_size : ∀ Q : Finset (VertexH G v0 H'), (GraphH G v0 H').IsClique Q → Q.card ≤ G.cliqueNum := by
      intro Q hQ
      generalize_proofs at *;
      by_cases h_two_A : ∃ x y : VertexH G v0 H', x ∈ Q ∧ y ∈ Q ∧ x ≠ y ∧ (∃ a, x = Sum.inl a) ∧ (∃ b, y = Sum.inl b);
      · obtain ⟨ x, y, hx, hy, hxy, ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩ := h_two_A; exact clique_case_two_A G v0 H' Q hQ _ _ hx hy hxy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ;
      · by_cases h_one_A : ∃ x : VertexH G v0 H', x ∈ Q ∧ (∃ a, x = Sum.inl a) ∧ ∀ y ∈ Q, (∃ b, y = Sum.inl b) → y = x;
        · obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_one_A
          have h_card : Q.card ≤ (G_double_prime G v0).cliqueNum + 1 := by
            apply clique_case_one_A G v0 H' Q hQ x hx₁ hx₂ hx₃
          have h_card_le : (G_double_prime G v0).cliqueNum + 1 ≤ G.cliqueNum := by
            exact cliqueNum_G_double_prime_le G v0
          linarith [h_card, h_card_le];
        · by_cases h_no_A : ∀ x ∈ Q, ∀ a, x ≠ Sum.inl a;
          · refine' le_trans ( clique_case_zero_A G v0 H' Q hQ h_no_A ) _;
            rw [ h_clique ];
            refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
            · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
            · intro b x hx
              have h_induce : (G_prime G v0).IsNClique b x → G.IsNClique b (Finset.image (fun v => v.val) x) := by
                intro hx
                have h_induce : ∀ u v : V_prime v0, u ∈ x → v ∈ x → u ≠ v → G.Adj u.val v.val := by
                  exact fun u v hu hv huv => hx.1 hu hv ( by simpa [ Subtype.ext_iff ] using huv ) |> fun h => by simpa [ Subtype.ext_iff ] using h;
                generalize_proofs at *;
                simp_all +decide [ SimpleGraph.isNClique_iff ];
                simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
                intro a ha b hb hab; aesop;
              generalize_proofs at *;
              exact le_csSup ⟨ Fintype.card V, fun n hn => by obtain ⟨ y, hy ⟩ := hn; exact hy.card_eq ▸ Finset.card_le_univ _ ⟩ ⟨ _, h_induce hx ⟩;
          · grind
    generalize_proofs at *;
    exact csSup_le' fun n hn => by obtain ⟨ s, hs ⟩ := hn; simpa [ hs.2 ] using h_clique_size s hs.1;

/-
The clique number of H(2,G) is equal to the clique number of G.
-/
lemma GraphH_cliqueNum_eq
  (h_ramsey : VertexPartitionRamsey 2 H' (G_prime G v0))
  (h_clique : H'.cliqueNum = (G_prime G v0).cliqueNum) :
  (GraphH G v0 H').cliqueNum = G.cliqueNum := by
    refine' le_antisymm _ _;
    · exact GraphH_cliqueNum_le G v0 H' h_clique;
    · convert GraphH_cliqueNum_ge G v0 H' h_ramsey using 1

/-
The partition of W induced by a coloring of H and an index i.
-/
def induced_partition (f : VertexH G v0 H' → Fin 2) (i : I_type V W) : W → Fin 2 :=
  fun w => f (Sum.inr (w, i))

/-
A subset of indices is uniform if the induced partition is the same for all indices in the subset.
-/
def is_uniform (f : VertexH G v0 H' → Fin 2) (T : Finset (I_type V W)) : Prop :=
  ∃ (c : W → Fin 2), ∀ i ∈ T, induced_partition G v0 H' f i = c

/-
There exists a subset of indices of size r that is uniform with respect to the induced partition.
-/
lemma exists_uniform_subset
  (f : VertexH G v0 H' → Fin 2) :
  ∃ (T : J_type V W), is_uniform G v0 H' f T.val := by
    -- By the pigeonhole principle, since there are $(r-1)t + 1$ indices and only $t$ possible functions $c_i$, there exists a function $c : W \to \text{Fin } 2$ such that at least $r$ indices $i$ satisfy $c_i = c$.
    obtain ⟨c, hc⟩ : ∃ c : W → Fin 2, (Finset.card (Finset.filter (fun i => induced_partition G v0 H' f i = c) Finset.univ)) ≥ r_param V := by
      have h_pigeonhole : (Finset.univ : Finset (I_type V W)).card = (r_param V - 1) * t_param W + 1 := by
        simp +decide [ r_param, t_param, I_type ];
        rfl;
      by_contra h_contra;
      have h_card : (Finset.univ : Finset (I_type V W)).card = Finset.sum (Finset.univ : Finset (W → Fin 2)) (fun c => (Finset.filter (fun i => induced_partition G v0 H' f i = c) Finset.univ).card) := by
        simp +decide only [Finset.card_eq_sum_ones, Finset.sum_fiberwise];
      refine' h_pigeonhole.not_lt ( h_card.symm ▸ lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => Nat.le_sub_one_of_lt ( lt_of_not_ge fun h => h_contra ⟨ _, h ⟩ ) ) _ );
      simp +decide [ mul_comm, t_param ];
    obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq hc;
    exact ⟨ ⟨ T, hT.2 ⟩, c, fun i hi => Finset.mem_filter.mp ( hT.1 hi ) |>.2 ⟩

/-
The map psi maps v0 to the type A vertex (v1, S'', T) and other vertices v to type B vertices (phi(v), i_star).
-/
def psi_map
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V)
  (i_star : I_type V W)
  (v : V) : VertexH G v0 H' :=
  if h : v = v0 then
    Sum.inl (v1, S'', T)
  else
    Sum.inr (phi ⟨v, h⟩, i_star)

/-
The map psi is injective.
-/
lemma psi_map_injective
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V)
  (i_star : I_type V W) :
  Function.Injective (psi_map G v0 H' T S' phi S'' v1 i_star) := by
    intro x y hxy
    simp [psi_map] at hxy
    cases' eq_or_ne x v0 with hx hx <;> cases' eq_or_ne y v0 with hy hy <;> simp_all +decide
    have := phi.injective ( Subtype.ext ( by injection hxy with h; aesop ) ) ; aesop;

/-
The map psi preserves adjacency between G and H.
-/
lemma psi_map_preserves_adj
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (h_phi_iso : ∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val)
  (S'' : X_type G v0 H')
  (h_S''_eq : S''.val = Subtype.val '' (phi '' (V_double_prime G v0)))
  (v1 : V)
  (i_star : I_type V W)
  (h_i_star_mem : i_star ∈ T.val)
  (h_i_star_map : f_map_val T i_star h_i_star_mem = v1)
  (u v : V) :
  G.Adj u v ↔ (GraphH G v0 H').Adj (psi_map G v0 H' T S' phi S'' v1 i_star u) (psi_map G v0 H' T S' phi S'' v1 i_star v) := by
    by_cases hu : u = v0 <;> by_cases hv : v = v0 <;> simp +decide [ *, psi_map ];
    · unfold GraphH; simp +decide [ * ] ;
      unfold AdjH; simp +decide [ * ] ;
      exact ⟨ fun h => h.symm, fun h => h.symm ⟩;
    · simp +decide [ ← h_i_star_map, GraphH ];
      unfold AdjH; aesop;
    · unfold GraphH; simp +decide [ *, AdjH ] ;
      convert h_phi_iso ⟨ u, hu ⟩ ⟨ v, hv ⟩ using 1

/-
Helper definitions for extracting the index $i^*$ corresponding to a vertex $v$ under the bijection $f_T$.
-/

noncomputable def get_i_star (T : J_type V W) (v : V) : I_type V W :=
  ((f_map V W T).symm v).val

lemma get_i_star_mem (T : J_type V W) (v : V) : get_i_star T v ∈ T.val := by
  exact ( Equiv.symm ( f_map V W T ) ) v |>.2

lemma f_map_get_i_star (T : J_type V W) (v : V) :
  f_map_val T (get_i_star T v) (get_i_star_mem T v) = v := by
    exact Equiv.apply_symm_apply _ _

/-
A specialized version of `psi_map` for Case 1, where the index $i^*$ is determined by $v_1$ and $T$.
-/
noncomputable def psi_map_case_1
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V)
  (v : V) : VertexH G v0 H' :=
  psi_map G v0 H' T S' phi S'' v1 (get_i_star T v1) v

/-
The map `psi_map_case_1` preserves adjacency, i.e., it is a graph embedding from $G$ to $H$.
-/
lemma psi_map_case_1_preserves_adj
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (h_phi_iso : ∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val)
  (S'' : X_type G v0 H')
  (h_S''_eq : S''.val = Subtype.val '' (phi '' (V_double_prime G v0)))
  (v1 : V)
  (u v : V) :
  G.Adj u v ↔ (GraphH G v0 H').Adj (psi_map_case_1 G v0 H' T S' phi S'' v1 u) (psi_map_case_1 G v0 H' T S' phi S'' v1 v) := by
    convert psi_map_preserves_adj G v0 H' T S' phi h_phi_iso S'' h_S''_eq v1 ( get_i_star T v1 ) ( get_i_star_mem T v1 ) ( f_map_get_i_star T v1 ) u v using 1

/-
The set of vertices $U$ used in Case 1 of the Ramsey proof.
-/
noncomputable def U_case_1
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V) : Set (VertexH G v0 H') :=
  Set.range (psi_map_case_1 G v0 H' T S' phi S'' v1)

/-
The map `psi_map_case_1` is injective.
-/
lemma psi_map_case_1_injective
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V) :
  Function.Injective (psi_map_case_1 G v0 H' T S' phi S'' v1) := by
    convert psi_map_injective G v0 H' T S' phi S'' v1 _ using 1

/-
All vertices in the set $U$ constructed for Case 1 have color $k$.
-/
lemma U_case_1_monochromatic
  (f : VertexH G v0 H' → Fin 2)
  (T : J_type V W)
  (k : Fin 2)
  (c : W → Fin 2)
  (h_uniform : ∀ i ∈ T.val, induced_partition G v0 H' f i = c)
  (S' : Set W)
  (h_S'_mono : ∀ w ∈ S', c w = k)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V)
  (h_v1_color : f (Sum.inl (v1, S'', T)) = k)
  (x : VertexH G v0 H')
  (hx : x ∈ U_case_1 G v0 H' T S' phi S'' v1) :
  f x = k := by
    obtain ⟨ v, rfl ⟩ := Set.mem_range.mp hx;
    by_cases h : v = v0 <;> simp_all +decide [ psi_map_case_1 ];
    · unfold psi_map; aesop;
    · convert h_S'_mono ( phi ⟨ v, h ⟩ ) ( phi ⟨ v, h ⟩ |>.2 ) using 1;
      convert congr_fun ( h_uniform ( get_i_star T v1 ) ( get_i_star_mem T v1 ) ) ( phi ⟨ v, h ⟩ ) using 1;
      unfold psi_map; aesop;

/-
The map `psi_map_case_1` induces an isomorphism between $G$ and the induced subgraph on its range $U$.
-/
lemma psi_map_case_1_is_iso
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (h_phi_iso : ∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val)
  (S'' : X_type G v0 H')
  (h_S''_eq : S''.val = Subtype.val '' (phi '' (V_double_prime G v0)))
  (v1 : V) :
  Nonempty (G ≃g (GraphH G v0 H').induce (U_case_1 G v0 H' T S' phi S'' v1)) := by
    refine' ⟨ _ ⟩;
    refine' { Equiv.ofBijective ( fun x => ⟨ _, ⟨ x, rfl ⟩ ⟩ ) ⟨ _, _ ⟩ with .. };
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    · exact fun x y hxy => psi_map_case_1_injective G v0 H' T S' phi S'' v1 hxy;
    · exact fun x hx => by obtain ⟨ y, rfl ⟩ := hx; exact ⟨ y, rfl ⟩ ;
    · exact fun {a b} =>
      Iff.symm (psi_map_case_1_preserves_adj G v0 H' T S' phi h_phi_iso S'' h_S''_eq v1 a b)

/-
The set of vertices $U$ used in Case 2 of the Ramsey proof.
-/
noncomputable def U_case_2
  (S'' : X_type G v0 H')
  (T : J_type V W) : Set (VertexH G v0 H') :=
  Set.range (fun v => Sum.inl (v, S'', T))

/-
The map `psi_map_case_2` induces an isomorphism between $G$ and the induced subgraph on its range $U$.
-/
lemma psi_map_case_2_is_iso
  (S'' : X_type G v0 H')
  (T : J_type V W) :
  Nonempty (G ≃g (GraphH G v0 H').induce (U_case_2 G v0 H' S'' T)) := by
    refine' ⟨ _, _, _ ⟩;
    refine' Equiv.ofBijective ( fun v => ⟨ Sum.inl ( v, S'', T ), _ ⟩ ) ⟨ fun v w h => _, fun x => _ ⟩;
    all_goals norm_num [ U_case_2 ] at *;
    · grind +ring;
    · rcases x with ⟨ x, hx ⟩ ; aesop;
    · exact fun h => by cases h; tauto;
    · exact fun h => ⟨ rfl, rfl, h ⟩

/-
Case 1 of the Ramsey proof: if we find a vertex $v_1$ of the same color as the monochromatic set $S'$, we construct a monochromatic copy of $G$.
-/
lemma GraphH_ramsey_2_case_1
  (f : VertexH G v0 H' → Fin 2)
  (T : J_type V W)
  (k : Fin 2)
  (c : W → Fin 2)
  (h_uniform : ∀ i ∈ T.val, induced_partition G v0 H' f i = c)
  (S' : Set W)
  (h_S'_mono : ∀ w ∈ S', c w = k)
  (phi : V_prime v0 ≃ S')
  (h_phi_iso : ∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val)
  (S'' : X_type G v0 H')
  (h_S''_eq : S''.val = Subtype.val '' (phi '' (V_double_prime G v0)))
  (v1 : V)
  (h_v1_color : f (Sum.inl (v1, S'', T)) = k) :
  ∃ (U : Set (VertexH G v0 H')), (∀ x ∈ U, f x = k) ∧ Nonempty (G ≃g (GraphH G v0 H').induce U) := by
    refine' ⟨ _, _, _ ⟩;
    exact Set.range ( psi_map_case_1 G v0 H' T S' phi S'' v1 );
    · exact fun x a =>
      U_case_1_monochromatic G v0 H' f T k c h_uniform S' h_S'_mono phi S'' v1 h_v1_color x a;
    · apply_rules [ psi_map_case_1_is_iso ]

/-
The graph $H(2,G)$ satisfies the vertex-partition Ramsey property for $G$ with 2 colors.
-/
lemma GraphH_ramsey_2
  (h_ramsey : VertexPartitionRamsey 2 H' (G_prime G v0)) :
  VertexPartitionRamsey 2 (GraphH G v0 H') G := by
    revert h_ramsey;
    intro h_ramsey f;
    -- By `exists_uniform_subset`, there exists $T \in J$ such that the induced partition on $W$ is constant $c$ for all $i \in T$.
    obtain ⟨T, c, h_uniform⟩ : ∃ T : J_type V W, ∃ c : W → Fin 2, ∀ i ∈ T.val, induced_partition G v0 H' f i = c := by
      exact Exists.elim ( exists_uniform_subset G v0 H' f ) fun T hT => ⟨ T, hT.choose, fun i hi => hT.choose_spec i hi ⟩;
    -- Since $H' \Rightarrow_2 G'$, there exists a monochromatic copy of $G'$ in $H'$ under the coloring $c$.
    obtain ⟨k, S', phi, h_phi_iso, h_S'_mono⟩ : ∃ k : Fin 2, ∃ S' : Set W, ∃ phi : V_prime v0 ≃ S', (∀ w ∈ S', c w = k) ∧ (∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val) := by
      have := h_ramsey c;
      obtain ⟨ k, S, hS, ⟨ phi ⟩ ⟩ := this;
      refine' ⟨ k, S, _, hS, _ ⟩;
      exact phi.toEquiv;
      exact fun x y => phi.map_adj_iff.symm;
    -- Define $S''$ as the image of $V''$ under $\phi$. Note $S'' \in X$ because $H'[S''] \cong G''$.
    obtain ⟨S'', h_S''_eq⟩ : ∃ S'' : X_type G v0 H', S''.val = Subtype.val '' (phi '' (V_double_prime G v0)) := by
      have h_iso : Nonempty ((H'.induce (Subtype.val '' (phi '' (V_double_prime G v0)))) ≃g (G_double_prime G v0)) := by
        refine' ⟨ _, _ ⟩;
        refine' Equiv.ofBijective ( fun x => ⟨ phi.symm ⟨ x.val, _ ⟩, _ ⟩ ) ⟨ _, _ ⟩;
        grind;
        all_goals norm_num [ Function.Injective, Function.Surjective ];
        all_goals norm_num [ V_double_prime, G_double_prime ] at *;
        · rcases x with ⟨ x, ⟨ y, ⟨ z, hz, rfl ⟩, rfl ⟩ ⟩ ; aesop;
        · intro a ha h; use phi ⟨ a, ha ⟩ ; aesop;
        · intro a ha ha' b hb hb'; specialize h_S'_mono ( phi.symm ⟨ a, ha ⟩ ) ( phi.symm ⟨ b, hb ⟩ ) ; aesop;
      exact ⟨ ⟨ _, h_iso ⟩, rfl ⟩;
    -- Consider the vertices $(v, S'', T)$ for $v \in V$.
    -- Case 1: There exists $v_1 \in V$ such that $f(v_1, S'', T) = k$.
    by_cases h_case1 : ∃ v1 : V, f (Sum.inl (v1, S'', T)) = k;
    · obtain ⟨ v1, hv1 ⟩ := h_case1;
      exact GraphH_ramsey_2_case_1 G v0 H' f T k c h_uniform S' h_phi_iso phi h_S'_mono S'' h_S''_eq v1 hv1 |> fun ⟨ U, hU₁, hU₂ ⟩ => ⟨ k, U, hU₁, hU₂ ⟩;
    · -- Since there are only 2 colors, this means $f(v, S'', T) = 1-k$ for all $v \in V$.
      have h_case2 : ∀ v : V, f (Sum.inl (v, S'', T)) = 1 - k := by
        grind;
      exact ⟨ 1 - k, U_case_2 G v0 H' S'' T, fun x hx => by obtain ⟨ v, rfl ⟩ := hx; exact h_case2 v, psi_map_case_2_is_iso G v0 H' S'' T ⟩

/-
The inductive hypothesis for the existence of $H(2,G)$.
-/
def PropH2 (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = n →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey 2 H G

/-
Base case of the induction: for any graph $G$ with 1 vertex, $H=G$ satisfies the required properties.
-/
lemma PropH2_base : PropH2 1 := by
  intro V _ _ G hV;
  refine' ⟨ V, inferInstance, inferInstance, G, _, _ ⟩;
  · rfl;
  · -- Since V has only one vertex, the only possible partition is {v} and the empty set. The empty set can't contain G, but {v} does. So, there exists a k (either 0 or 1) such that the class containing v is nonempty and contains G. That should satisfy the definition.
    obtain ⟨v, hv⟩ : ∃ v : V, ∀ w : V, w = v := by
      rw [ Fintype.card_eq_one_iff ] at hV; tauto;
    intro f;
    use f v, {v};
    refine' ⟨ by aesop, ⟨ _, _, _ ⟩ ⟩;
    exact (Equiv.subtypeUnivEquiv hv).symm;
    · exact fun a => a;
    · aesop

/-
Inductive step for the existence of $H(2,G)$: if the property holds for graphs of size $n-1$, it holds for graphs of size $n$.
-/
lemma PropH2_step (n : ℕ) (hn : n > 1) (IH : PropH2 (n - 1)) : PropH2 n := by
  intro V hV hV' G hG;
  -- By the induction hypothesis, there exists a graph $H'$ such that $\omega(H') = \omega(G')$ and $H' \Rightarrow_2 G'$.
  obtain ⟨W', hW', hW'_eq, H', hH'_clique, hH'_ramsey⟩ : ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W') (H' : SimpleGraph W'),
    (H'.cliqueNum = (G_prime G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))).cliqueNum) ∧
    (VertexPartitionRamsey 2 H' (G_prime G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V))))) := by
      have h_card_V' : Fintype.card (V_prime (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))) = n - 1 := by
        rw [ Fintype.card_ofFinset ];
        rw [ show ( Finset.filter ( Membership.mem ( V_prime ( Classical.choose ( Finset.card_pos.mp ( by linarith : 0 < Fintype.card V ) ) ) ) ) Finset.univ : Finset V ) = Finset.univ.erase ( Classical.choose ( Finset.card_pos.mp ( by linarith : 0 < Fintype.card V ) ) ) by ext x; aesop ] ; aesop;
      specialize IH (V_prime (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))) ; aesop;
  use VertexH G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V))) H', by infer_instance, by infer_instance, GraphH G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V))) H';
  exact ⟨ GraphH_cliqueNum_eq G _ H' hH'_ramsey hH'_clique, GraphH_ramsey_2 G _ H' hH'_ramsey ⟩

/-
Base case $n=0$ for the existence of $H(2,G)$.
-/
lemma PropH2_0 : PropH2 0 := by
  intro V _ _ G hG; have := Fintype.card_eq_zero_iff.mp hG; cases this; simp_all +decide ;
  refine' ⟨ PEmpty, _, _ ⟩ <;> norm_num +zetaDelta at *;
  · exact ⟨ inferInstance ⟩;
  · -- Since $V$ is empty, $G$ is the empty graph, and its clique number is $0$.
    have h_empty : G.cliqueNum = 0 := by
      simp +decide [ SimpleGraph.cliqueNum ];
      rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num [ SimpleGraph.isNClique_iff ];
      · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
      · exact fun a ha => Finset.eq_empty_of_forall_notMem fun x hx => ‹∀ a : V, False› x;
    refine' ⟨ ⊥, _, _ ⟩ <;> simp_all +decide [ VertexPartitionRamsey ];
    · simp +decide [ SimpleGraph.cliqueNum ];
      rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num;
      · exact ⟨ 0, ⟨ by norm_num, ∅, by norm_num ⟩ ⟩;
      · exact fun a ha x hx => by fin_cases x; aesop;
    · constructor;
      constructor ; norm_num +zetaDelta at *;
      constructor;
      exact?;
      swap;
      exact Set.univ;
      exact Fintype.equivOfCardEq hG

/-
For every graph $G$, there exists a graph $H$ such that $\omega(H) = \omega(G)$ and $H \Rightarrow_2 G$.
-/
theorem exists_H_2 :
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey 2 H G := by
        have h_ind : ∀ n : ℕ, PropH2 n := by
          intro n
          induction' n using Nat.strong_induction_on with n ih;
          rcases n with ( _ | _ | n ) <;> simp_all +arith +decide
          · exact PropH2_0;
          · exact PropH2_base;
          · exact PropH2_step _ ( Nat.succ_lt_succ ( Nat.succ_pos _ ) ) ( ih _ ( Nat.le_refl _ ) );
        exact fun V [Fintype V] [DecidableEq V] G => h_ind (Fintype.card V) V G rfl

/-
For every graph $G$ and integer $n \ge 1$, there exists a graph $H(n,G)$ with the same clique number such that $H(n,G) \Rightarrow_n G$.
-/
theorem exists_H_n :
  ∀ (n : ℕ) (hn : n ≥ 1) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey n H G := by
  intro n hn V _ _ G
  exact exists_H_n_of_exists_H_2 exists_H_2 n hn V G

/-
Definitions of the graphs $K_2$ and $2K_3$.
-/
def K2 : SimpleGraph (Fin 2) := completeGraph (Fin 2)

def TwoK3 : SimpleGraph (Fin 3 ⊕ Fin 3) := SimpleGraph.sum (completeGraph (Fin 3)) (completeGraph (Fin 3))

/-
Construction of the graph $H_2$ and the parameter $N$.
-/
lemma H2_witness_proof : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    H.cliqueNum = K2.cliqueNum ∧ VertexPartitionRamsey 36 H K2 :=
  exists_H_n 36 (by norm_num) (Fin 2) K2

noncomputable def V2 : Type := Classical.choose H2_witness_proof

noncomputable instance : Fintype V2 := Classical.choose (Classical.choose_spec H2_witness_proof)
noncomputable instance : DecidableEq V2 := Classical.choose (Classical.choose_spec (Classical.choose_spec H2_witness_proof))

noncomputable def H2 : SimpleGraph V2 := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H2_witness_proof)))

lemma H2_props :
  H2.cliqueNum = K2.cliqueNum ∧ VertexPartitionRamsey 36 H2 K2 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H2_witness_proof)))

noncomputable def N_param : ℕ := 2 ^ H2.edgeFinset.card

lemma N_ge_one : N_param ≥ 1 := by
  unfold N_param
  apply Nat.one_le_pow
  norm_num

/-
Construction of the graph $H_1$.
-/
lemma H1_witness_proof : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    H.cliqueNum = TwoK3.cliqueNum ∧ VertexPartitionRamsey N_param H TwoK3 :=
  exists_H_n N_param N_ge_one (Fin 3 ⊕ Fin 3) TwoK3

noncomputable def V1 : Type := Classical.choose H1_witness_proof

noncomputable instance : Fintype V1 := Classical.choose (Classical.choose_spec H1_witness_proof)
noncomputable instance : DecidableEq V1 := Classical.choose (Classical.choose_spec (Classical.choose_spec H1_witness_proof))

noncomputable def H1 : SimpleGraph V1 := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H1_witness_proof)))

lemma H1_props :
  H1.cliqueNum = TwoK3.cliqueNum ∧ VertexPartitionRamsey N_param H1 TwoK3 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H1_witness_proof)))

/-
The set $X$ of unordered pairs of distinct vertices of $V_1$.
-/
noncomputable def X_type_G : Type := { e : Sym2 V1 // ¬ e.IsDiag }

noncomputable instance : Fintype X_type_G := Subtype.fintype _
noncomputable instance : DecidableEq X_type_G := by infer_instance

/-
The vertex set of the Folkman graph $G$.
-/
noncomputable def VertexG : Type := (V1 × V2) ⊕ X_type_G

noncomputable instance : Fintype VertexG := by
  unfold VertexG
  infer_instance

noncomputable instance : DecidableEq VertexG := by
  unfold VertexG
  infer_instance

/-
The adjacency relation of the Folkman graph $G$.
-/
noncomputable def AdjG (x y : VertexG) : Prop :=
  match x, y with
  | Sum.inl (u, v), Sum.inl (u', v') => (u = u' ∧ H2.Adj v v') ∨ (v = v' ∧ H1.Adj u u')
  | Sum.inr S, Sum.inl (u, v) => u ∈ S.val
  | Sum.inl (u, v), Sum.inr S => u ∈ S.val
  | Sum.inr _, Sum.inr _ => False

/-
The Folkman graph $G$.
-/
noncomputable def GraphG : SimpleGraph VertexG where
  Adj := AdjG
  symm := by
    intro x y hxy;
    -- By definition of $AdjG$, we need to check all possible cases.
    cases x <;> cases y <;> simp [AdjG] at hxy ⊢;
    · exact Or.imp ( fun h => ⟨ h.1.symm, h.2.symm ⟩ ) ( fun h => ⟨ h.1.symm, h.2.symm ⟩ ) hxy;
    · exact hxy;
    · exact hxy
  loopless := by
    -- By definition of $AdjG$, we need to show that for any vertex $x$, $x$ is not adjacent to itself.
    intro x
    cases x <;> simp [AdjG]

/-
If a clique contains two vertices in different rows, then all its grid vertices lie in the same column.
-/
lemma clique_grid_force_col
  (Q : Finset VertexG) (hQ : GraphG.IsClique Q)
  (u u' : V1) (v v' : V2)
  (hx : Sum.inl (u, v) ∈ Q)
  (hy : Sum.inl (u', v') ∈ Q)
  (h_diff : u ≠ u') :
  v = v' ∧ ∀ u'' v'', Sum.inl (u'', v'') ∈ Q → v'' = v := by
    have h_row : v = v' := by
      have := hQ hx hy; simp_all +decide [ GraphG, AdjG ] ;
      grind
    have h_col : ∀ u'' v'' (hx'' : Sum.inl (u'', v'') ∈ Q), v'' = v := by
      intros u'' v'' hx''; have := hQ hx'' hx; have := hQ hx'' hy; simp_all +decide [ GraphG ] ;
      cases eq_or_ne u'' u <;> cases eq_or_ne u'' u' <;> simp_all +decide [ AdjG ];
      · grind +ring;
      · grind +ring;
      · grind +ring
    exact ⟨h_row, h_col⟩

/-
A clique contained in a single row of the grid has size at most 2.
-/
lemma clique_in_row_le_two
  (Q : Finset VertexG) (hQ : GraphG.IsClique Q)
  (u : V1)
  (h_subset : ∀ x ∈ Q, ∃ v, x = Sum.inl (u, v)) :
  Q.card ≤ 2 := by
    have h_row_clique : ∀ Q' : Finset V2, (H2.IsClique Q') → Q'.card ≤ 2 := by
      have := H2_props.1; ( rw [ show H2.cliqueNum = 2 from this.trans ( by
                                  unfold SimpleGraph.cliqueNum; simp +decide [ K2 ] ;
                                  rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;> norm_num [ SimpleGraph.isNClique_iff ];
                                  · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
                                  · exact fun a ha => Finset.card_le_univ _;
                                  · exact fun w hw => ⟨ { 0, 1 }, by simp +decide, by interval_cases w <;> simp +decide ⟩ ) ] at *; );
      -- By definition of clique number, any clique in $H_2$ has size at most 2.
      have h_clique_num : ∀ (Q' : Finset V2), (H2.IsClique Q') → Q'.card ≤ H2.cliqueNum := by
        intro Q' hQ'; exact (by
        apply le_csSup (by
        exact ⟨ Fintype.card V2, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩) (by
        exact ⟨ Q', by simpa [ SimpleGraph.isNClique_iff ] using hQ' ⟩));
      exact fun Q' hQ' => le_trans ( h_clique_num Q' hQ' ) ( by rw [ H2_props.1 ] ; exact this ▸ le_rfl );
    convert h_row_clique ( Finset.image ( fun v => v ) ( Finset.filter ( fun v => Sum.inl ( u, v ) ∈ Q ) Finset.univ ) ) _ using 1;
    · rw [ show Q = Finset.image ( fun v => Sum.inl ( u, v ) ) ( Finset.filter ( fun v => Sum.inl ( u, v ) ∈ Q ) Finset.univ ) from ?_, Finset.card_image_of_injective ] ; aesop_cat;
      · exact fun x y h => by injection h with h; aesop;
      · ext x; specialize h_subset x; aesop;
    · intro v hv w hw hvw; specialize hQ; simp_all +decide
      have := hQ hv hw; unfold GraphG at this; simp_all +decide
      unfold AdjG at this; simp_all +decide
      grind

/-
A clique contained in a single column of the grid has size at most 3.
-/
lemma clique_in_col_le_three
  (Q : Finset VertexG) (hQ : GraphG.IsClique Q)
  (v : V2)
  (h_subset : ∀ x ∈ Q, ∃ u, x = Sum.inl (u, v)) :
  Q.card ≤ 3 := by
    -- Let $Q' = \{u \in V1 \mid \exists w, \text{Sum.inl} (u, v) = w \land w \in Q\}$.
    set Q' : Finset V1 := Finset.filter (fun u => Sum.inl (u, v) ∈ Q) Finset.univ with hQ';
    -- Since $Q'$ is a clique in $H_1$, its size is at most the clique number of $H_1$, which is 3.
    have hQ'_clique : H1.IsClique Q' := by
      intro u hu u' hu' hne; have := hQ; simp_all +decide [ SimpleGraph.IsClique ] ;
      have := this hu hu'; simp_all +decide
      unfold GraphG at this; simp_all +decide
      unfold AdjG at this; simp_all +decide
      grind
    have hQ'_size : Q'.card ≤ 3 := by
      have hQ'_size : Q'.card ≤ H1.cliqueNum := by
        convert clique_subset_le_cliqueNum_induce H1 _ _ _ _;
        any_goals exact Set.univ;
        · simp +decide [ SimpleGraph.cliqueNum ];
          congr! 3;
          constructor <;> rintro ⟨ s, hs ⟩;
          · use s.image (fun u => ⟨u, trivial⟩);
            simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
            intro x hx y hy hxy; aesop;
          · use s.image Subtype.val;
            simp_all +decide [ SimpleGraph.isNClique_iff ];
            simp_all +decide [ SimpleGraph.IsClique, Set.Pairwise ];
            rw [ Finset.card_image_of_injective _ Subtype.coe_injective, hs.2 ];
        · infer_instance;
        · exact hQ'_clique;
        · exact fun _ _ => Set.mem_univ _;
      refine le_trans hQ'_size ?_;
      rw [ H1_props.1 ];
      unfold TwoK3; simp +decide [ SimpleGraph.cliqueNum ] ;
      refine' csSup_le _ _ <;> norm_num [ SimpleGraph.isNClique_iff ];
      · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
      · simp +decide [ Set.Pairwise ];
    have hQ_eq_Q' : Q = Finset.image (fun u => Sum.inl (u, v)) Q' := by
      ext x; specialize h_subset x; aesop;
    exact hQ_eq_Q'.symm ▸ Finset.card_image_le.trans hQ'_size

/-
Any clique contained in the grid part of $G$ has size at most 3.
-/
lemma clique_grid_le_three
  (Q : Finset VertexG) (hQ : GraphG.IsClique Q)
  (h_grid : ∀ x ∈ Q, ∃ u v, x = Sum.inl (u, v)) :
  Q.card ≤ 3 := by
    by_cases hQ_nonempty : Q.Nonempty;
    · obtain ⟨ x, hx ⟩ := hQ_nonempty;
      obtain ⟨ u, v, rfl ⟩ := h_grid x hx;
      by_cases h_case : ∃ y ∈ Q, ∃ u' v', y = Sum.inl (u', v') ∧ u' ≠ u;
      · obtain ⟨ y, hy, u', v', rfl, hu' ⟩ := h_case;
        have h_col : ∀ x ∈ Q, ∃ u'' v'', x = Sum.inl (u'', v'') ∧ v'' = v := by
          intros x hx
          obtain ⟨ u'', v'', rfl ⟩ := h_grid x hx
          have h_col : v'' = v := by
            have := clique_grid_force_col Q hQ u' u v' v hy ‹_›; aesop;
          use u'', v'';
        exact clique_in_col_le_three Q hQ v fun x hx => by obtain ⟨ u'', v'', rfl, rfl ⟩ := h_col x hx; exact ⟨ u'', rfl ⟩ ;
      · -- Since all elements of Q have the same row u, Q is contained in row u.
        have h_row : ∀ x ∈ Q, ∃ v, x = Sum.inl (u, v) := by
          grind;
        exact le_trans ( clique_in_row_le_two Q hQ u h_row ) ( by norm_num );
    · aesop

/-
A clique in $G$ containing a vertex from $X$ has size at most 3.
-/
lemma clique_with_X_le_three
  (Q : Finset VertexG) (hQ : GraphG.IsClique Q)
  (S : X_type_G)
  (hS : Sum.inr S ∈ Q) :
  Q.card ≤ 3 := by
    -- For any $y \in Q \setminus \{Sum.inr S\}$, $y = Sum.inl (u, v)$ and $y \sim Sum.inr S$.
    -- This implies $u \in S.val$.
    -- Since $S \in X$, $S.val$ is not diagonal, so $S.val = s(a, b)$ with $a \ne b$.
    -- Thus $u = a$ or $u = b$.
    -- If $Q \setminus \{Sum.inr S\}$ contains vertices with $u=a$ and $u=b$, say $(a, v)$ and $(b, v')$, then they must be adjacent.
    -- Since $a \ne b$, they are in different rows, so they must be in the same column $v=v'$.
    -- Then all vertices in $Q \setminus \{Sum.inr S\}$ must be in column $v$ (by `clique_grid_force_col`).
    have h_case1 : ∃ a b : V1, a ≠ b ∧ S.val = s(a, b) ∧ ∀ y ∈ Q \ {Sum.inr S}, ∃ u v, y = Sum.inl (u, v) ∧ (u = a ∨ u = b) := by
      -- Since $S$ is in $X_type_G$, its value is a pair of distinct elements from $V1$. Let's denote these elements as $a$ and $b$, so $S.val = s(a, b)$.
      obtain ⟨a, b, hab⟩ : ∃ a b : V1, a ≠ b ∧ S.val = s(a, b) := by
        rcases S with ⟨ ⟨ a, b ⟩, h ⟩ ; use a, b ; aesop;
      refine' ⟨ a, b, hab.1, hab.2, fun y hy => _ ⟩;
      rcases y with ( ⟨ u, v ⟩ | ⟨ S ⟩ ) <;> simp_all +decide [ SimpleGraph.IsClique ];
      · have := hQ hS hy; simp_all +decide [ GraphG, AdjG ] ;
        exact ⟨ u, ⟨ v, rfl ⟩, this ⟩;
      · have := hQ hy.1 hS; simp_all +decide [ X_type_G ] ;
        exact absurd this ( by exact fun a => this );
    have h_case1_size : ∃ a b : V1, a ≠ b ∧ S.val = s(a, b) ∧ (∀ y ∈ Q \ {Sum.inr S}, ∃ u v, y = Sum.inl (u, v) ∧ (u = a ∨ u = b)) ∧ ((∀ y ∈ Q \ {Sum.inr S}, ∃ u v, y = Sum.inl (u, v) ∧ u = a) ∨ (∀ y ∈ Q \ {Sum.inr S}, ∃ u v, y = Sum.inl (u, v) ∧ u = b) ∨ ∃ v : V2, ∀ y ∈ Q \ {Sum.inr S}, ∃ u, y = Sum.inl (u, v) ∧ (u = a ∨ u = b)) := by
      obtain ⟨ a, b, hab, hS, h ⟩ := h_case1;
      by_cases h_case : ∃ y ∈ Q \ {Sum.inr S}, ∃ u v, y = Sum.inl (u, v) ∧ u = a ∧ ∃ y' ∈ Q \ {Sum.inr S}, ∃ u' v', y' = Sum.inl (u', v') ∧ u' = b ∧ v ≠ v';
      · obtain ⟨ y, hy, u, v, hy', hu, y', hy', u', v', hy'', hu', hv ⟩ := h_case;
        have := hQ ( show y ∈ Q from Finset.mem_sdiff.mp hy |>.1 ) ( show y' ∈ Q from Finset.mem_sdiff.mp hy' |>.1 ) ; simp_all +decide
        have := clique_grid_force_col Q hQ a b v v' hy hy' ; aesop;
      · by_cases h_case : ∃ y ∈ Q \ {Sum.inr S}, ∃ u v, y = Sum.inl (u, v) ∧ u = a ∧ ∃ y' ∈ Q \ {Sum.inr S}, ∃ u' v', y' = Sum.inl (u', v') ∧ u' = b ∧ v = v';
        · obtain ⟨ y, hy, u, v, hy', hu, y', hy'', u', v', hy''', hu', hv ⟩ := h_case;
          refine' ⟨ a, b, hab, hS, h, Or.inr <| Or.inr <| ⟨ v, _ ⟩ ⟩;
          grind;
        · grind;
    obtain ⟨ a, b, hab, hS, h₁, h₂ | h₂ | ⟨ v, hv ⟩ ⟩ := h_case1_size <;> simp_all +decide
    · have h_case1_size : (Q \ {Sum.inr S}).card ≤ 2 := by
        convert clique_in_row_le_two _ _ _ _ using 1;
        exact fun x hx y hy hxy => hQ ( Finset.mem_sdiff.mp hx |>.1 ) ( Finset.mem_sdiff.mp hy |>.1 ) hxy;
        exacts [ a, fun x hx => by obtain ⟨ v, rfl ⟩ := h₂ x ( Finset.mem_sdiff.mp hx |>.1 ) ( by simpa using Finset.mem_sdiff.mp hx |>.2 ) ; exact ⟨ v, rfl ⟩ ];
      rw [ Finset.card_sdiff ] at h_case1_size ; aesop;
    · have h_case1_size : (Q \ {Sum.inr S}).card ≤ 2 := by
        have h_subset : ∀ y ∈ Q \ {Sum.inr S}, ∃ v : V2, y = Sum.inl (b, v) := by
          aesop
        convert clique_in_row_le_two _ _ _ _;
        exact fun x hx y hy hxy => hQ ( Finset.mem_sdiff.mp hx |>.1 ) ( Finset.mem_sdiff.mp hy |>.1 ) hxy;
        exacts [ b, h_subset ];
      rw [ Finset.card_sdiff ] at h_case1_size ; aesop;
    · have h_case1_size : (Q \ {Sum.inr S}).card ≤ 2 := by
        exact le_trans ( Finset.card_le_card ( show Q \ { Sum.inr S } ⊆ { Sum.inl ( a, v ), Sum.inl ( b, v ) } from fun x hx => by obtain ⟨ u, rfl, hu ⟩ := hv x ( Finset.mem_sdiff.mp hx |>.1 ) ( Finset.mem_sdiff.mp hx |>.2 |> fun h => by aesop ) ; aesop ) ) ( Finset.card_insert_le _ _ ) |> le_trans <| by norm_num;
      rw [ Finset.card_sdiff ] at h_case1_size ; aesop

/-
The clique number of $G$ is at most 3.
-/
lemma GraphG_cliqueNum_le_three : GraphG.cliqueNum ≤ 3 := by
  refine' csSup_le' _;
  rintro n ⟨ s, hs ⟩;
  by_cases hX : ∃ S : X_type_G, Sum.inr S ∈ s;
  · exact hs.2 ▸ clique_with_X_le_three _ hs.1 _ hX.choose_spec;
  · -- Since there's no vertex from X in s, all vertices in s must be in the grid part. By the lemma clique_grid_le_three, the size of s is at most 3.
    have h_grid : ∀ x ∈ s, ∃ u v, x = Sum.inl (u, v) := by
      intro x hx; rcases x with ( ⟨ u, v ⟩ | ⟨ S ⟩ ) <;> aesop;
    have := hs.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    exact this ▸ clique_grid_le_three s ( fun x hx y hy hxy => hs hx hy hxy ) h_grid

/-
The clique number of $G$ is at least 3.
-/
lemma GraphG_cliqueNum_ge_three : GraphG.cliqueNum ≥ 3 := by
  -- Since $\omega(H_1) = 3$, there exists a clique $C$ of size 3 in $H_1$. Let's denote this clique by $C$. We can embed $C$ into $G$ by mapping each vertex $u \in C$ to $(u, v)$ for some fixed $v \in V_2$.
  obtain ⟨C, hC⟩ : ∃ C : Finset V1, C.card = 3 ∧ H1.IsClique C := by
    have h_clique_H1 : H1.cliqueNum ≥ 3 := by
      have := H1_props.1;
      rw [ this ];
      refine' le_csSup _ _;
      · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
      · exists { Sum.inl 0, Sum.inl 1, Sum.inl 2 };
        simp +decide [ SimpleGraph.isNClique_iff ];
        simp +decide [ TwoK3 ];
    have h_clique_H1 : ∃ C : Finset V1, H1.IsClique C ∧ C.card ≥ 3 := by
      contrapose! h_clique_H1;
      refine' lt_of_le_of_lt ( csSup_le _ _ ) _ <;> norm_num;
      exact 2;
      · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
      · exact fun b x hx => Nat.le_of_lt_succ ( by linarith [ h_clique_H1 x hx.1, hx.2.symm ] );
      · norm_num;
    obtain ⟨ C, hC₁, hC₂ ⟩ := h_clique_H1;
    exact Exists.elim ( Finset.exists_subset_card_eq hC₂ ) fun s hs => ⟨ s, hs.2, hC₁.subset <| by aesop ⟩;
  have h_embedding : ∃ v : V2, ∀ u u' : V1, u ∈ C → u' ∈ C → u ≠ u' → GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u', v)) := by
    -- Since $H2$ is a finite graph, there exists a vertex $v \in H2$ such that for all $u, u' \in C$, $u \sim u'$ in $H1$ implies $(u, v) \sim (u', v)$ in $G$.
    obtain ⟨v, hv⟩ : ∃ v : V2, True := by
      by_contra h_empty2;
      simp_all +decide
      exact absurd ( H2_props.2 ) ( by
        unfold VertexPartitionRamsey; simp +decide
        intro x; exact ⟨ fun f => h_empty2.elim ( f.toEquiv ( 0 ) ) ⟩ ; );
    use v; intro u u' hu hu' hne; exact Or.inr ⟨ rfl, hC.2 hu hu' hne ⟩ ;
  obtain ⟨ v, hv ⟩ := h_embedding;
  have h_embedding : ∃ C' : Finset VertexG, C'.card = 3 ∧ GraphG.IsClique C' := by
    obtain ⟨u, u', u'', hu, hu', hu''⟩ : ∃ u u' u'' : V1, u ∈ C ∧ u' ∈ C ∧ u'' ∈ C ∧ u ≠ u' ∧ u ≠ u'' ∧ u' ≠ u'' := by
      rcases Finset.card_eq_three.mp hC.1 with ⟨ u, u', u'', hu, hu', hu'', h ⟩ ; use u, u', u'' ; aesop;
    use {Sum.inl (u, v), Sum.inl (u', v), Sum.inl (u'', v)}; simp_all +decide [ SimpleGraph.isClique_iff ] ;
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> simp +decide
    · grind +ring;
    · grind +ring;
  obtain ⟨ C', hC'₁, hC'₂ ⟩ := h_embedding;
  refine' le_csSup _ _;
  · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
  · exact ⟨ C', by simpa [ SimpleGraph.isNClique_iff ] using hC'₂, hC'₁ ⟩

/-
The clique number of $G$ is exactly 3.
-/
lemma GraphG_cliqueNum_eq_three : GraphG.cliqueNum = 3 := by
  -- Since the clique number is both at most 3 and at least 3, it must be exactly 3.
  apply le_antisymm GraphG_cliqueNum_le_three GraphG_cliqueNum_ge_three

/-
The coloring of $H_2$ induced by a coloring of $G$ on a specific row.
-/
noncomputable def induced_coloring (c : GraphG.edgeSet → Bool) (u : V1) : H2.edgeSet → Bool :=
  fun e =>
    let v := e.val.out.1
    let v' := e.val.out.2
    let e_G : Sym2 VertexG := Sym2.mk (Sum.inl (u, v), Sum.inl (u, v'))
    have h_adj : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u, v')) := by
      -- By definition of $GraphG.Adj$, we know that $Sum.inl (u, v)$ is adjacent to $Sum.inl (u, v')$ if and only if $v \sim v'$ in $H2$.
      have h_adj : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u, v')) ↔ v ≠ v' ∧ (H2.Adj v v' ∨ H2.Adj v' v) := by
        constructor <;> intro h <;> simp_all +decide [ GraphG ];
        · unfold AdjG at h; aesop;
        · exact Or.inl ⟨ rfl, by cases h.2 <;> tauto ⟩
      generalize_proofs at *;
      -- Since $e$ is an edge in $H2$, by definition, $H2.Adj v v'$ must be true.
      have h_adj_H2 : H2.Adj v v' := by
        have h_edge : (Sym2.mk (v, v')) ∈ H2.edgeSet := by
          convert e.2 using 1
          generalize_proofs at *;
          exact Quot.out_eq e.val ▸ rfl
        convert h_edge using 1;
      exact h_adj.mpr ⟨ by rintro h; simpa [ h ] using h_adj_H2.ne, Or.inl h_adj_H2 ⟩
    c ⟨e_G, h_adj⟩

/-
There exists a set $U \subseteq V_1$ inducing $2K_3$ in $H_1$ such that all rows in $U$ have the same induced coloring on $H_2$.
-/
noncomputable def row_coloring_map (c : GraphG.edgeSet → Bool) (u : V1) : H2.edgeSet → Bool :=
  induced_coloring c u

lemma exists_monochromatic_U
  (c : GraphG.edgeSet → Bool) :
  ∃ (U : Set V1) (chi : H2.edgeSet → Bool),
    Nonempty (H1.induce U ≃g TwoK3) ∧
    ∀ u ∈ U, row_coloring_map c u = chi := by
      norm_num +zetaDelta at *;
      have := H1_props.2;
      contrapose! this;
      unfold VertexPartitionRamsey; simp +decide ;
      refine' ⟨ _, _ ⟩;
      exact fun u => Fintype.equivFinOfCardEq ( show Fintype.card ( H2.edgeSet → Bool ) = N_param from by
                                                  simp +decide [ N_param ] ) ( row_coloring_map c u );
      intro x U hx; specialize this U; simp_all +decide [ SimpleGraph.comap, SimpleGraph.induce ] ;
      exact ⟨ fun f => by obtain ⟨ u, hu, hu' ⟩ := this f.symm ( Fintype.equivFinOfCardEq ( show Fintype.card ( H2.edgeSet → Bool ) = N_param from by
                                                                                              grind ) |>.symm x ) ; specialize hx u hu; aesop ⟩

/-
The number of pairs $(e, v)$ where $e$ is an edge in a set of size 3 and $v \in e$ is 6.
-/
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeWithVertexFinset (S : Finset V) : Finset (Sym2 V × V) :=
  (S.offDiag.image Sym2.mk ×ˢ S).filter (fun p => p.1 ∈ S.offDiag.image Sym2.mk ∧ p.2 ∈ p.1)

lemma card_edgeWithVertexFinset (S : Finset V) (hS : S.card = 3) :
  (edgeWithVertexFinset S).card = 6 := by
    have := Finset.card_eq_three.mp hS;
    rcases this with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp +decide [ *, edgeWithVertexFinset ] ;
    convert Finset.card_eq_sum_ones _ using 1;
    rw [ Finset.sum_filter ];
    rw [ Finset.sum_eq_multiset_sum ] ; simp +decide [ *, Finset.offDiag ] ;
    simp +decide [ Multiset.filter_cons, Multiset.filter_singleton ];
    split_ifs <;> simp_all +decide [ Sym2.eq_swap ];
    rw [ if_pos ⟨ x, y, by tauto ⟩, if_pos ⟨ x, z, by tauto ⟩, if_pos ⟨ y, z, by tauto ⟩ ] ; simp +decide [ * ]

/-
The cardinality of the signature data type is 36.
-/
def SigData (A B : Finset V) : Type _ :=
  { x // x ∈ edgeWithVertexFinset A } × { x // x ∈ edgeWithVertexFinset B }

instance (A B : Finset V) : Fintype (SigData A B) := by
  unfold SigData
  infer_instance

instance (A B : Finset V) : DecidableEq (SigData A B) := by
  unfold SigData
  infer_instance

lemma card_SigData (A B : Finset V) (hA : A.card = 3) (hB : B.card = 3) :
  Fintype.card (SigData A B) = 36 := by
    convert congr_arg₂ ( · * · ) ( card_edgeWithVertexFinset A hA ) ( card_edgeWithVertexFinset B hB ) using 1;
    convert Fintype.card_prod _ _;
    all_goals try infer_instance;
    · rw [ Fintype.card_coe ];
    · rw [ Fintype.card_coe ]

/-
Edges in a signature are non-diagonal.
-/
lemma SigData_edge_nd1 (A B : Finset V) (s : SigData A B) : ¬ s.1.val.1.IsDiag := by
  -- By definition of `edgeWithVertexFinset`, the edges in the signature are non-diagonal.
  have h_edge_non_diag : ∀ e ∈ edgeWithVertexFinset A, ¬e.1.IsDiag := by
    unfold edgeWithVertexFinset; aesop;
  generalize_proofs at *; (
  exact h_edge_non_diag _ s.1.2)

lemma SigData_edge_nd2 (A B : Finset V) (s : SigData A B) : ¬ s.2.val.1.IsDiag := by
  obtain ⟨ a, ha ⟩ := s.2;
  unfold edgeWithVertexFinset at ha; aesop;

/-
If there are no monochromatic triangles, then any clique of size 3 must contain a red edge.
-/
lemma exists_red_edge_in_clique3
  (c : GraphG.edgeSet → Bool)
  (A : Finset V1)
  (hA : H1.IsClique A)
  (hA_card : A.card = 3)
  (v : V2)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩)) :
  ∃ (u w : V1) (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
    u ∈ A ∧ w ∈ A ∧ c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false := by
      by_contra h_contra;
      -- Since $A$ is a clique of size 3 in $H_1$, $A \times \{v\}$ is a clique of size 3 in $G$.
      have h_clique : ∀ u w : V1, u ∈ A → w ∈ A → u ≠ w → GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v)) := by
        intros u w hu hw hne; exact (by
        -- Since $u$ and $w$ are adjacent in $H_1$, their images under the col_embedding should be adjacent in $G$.
        have h_adj : H1.Adj u w := by
          exact hA hu hw hne;
        exact Or.inr ⟨ rfl, h_adj ⟩);
      obtain ⟨u, w, x, huA, hwA, hxA, huvw⟩ : ∃ u w x : V1, u ∈ A ∧ w ∈ A ∧ x ∈ A ∧ u ≠ w ∧ u ≠ x ∧ w ≠ x := by
        rcases Finset.card_eq_three.mp hA_card with ⟨ u, w, x, hu, hw, hx, h ⟩ ; use u, w, x ; aesop;
      exact h_no_mono ( Sum.inl ( u, v ) ) ( Sum.inl ( w, v ) ) ( Sum.inl ( x, v ) ) ( h_clique u w huA hwA huvw.1 ) ( h_clique w x hwA hxA huvw.2.2 ) ( h_clique u x huA hxA huvw.2.1 ) ( by aesop )

/-
Predicate defining a valid signature for a vertex $v$.
-/
def ValidSignature
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (v : V2)
  (s : SigData A B) : Prop :=
  let e1 := s.1.val.1
  let u1 := s.1.val.2
  let e2 := s.2.val.1
  let u2 := s.2.val.2
  let u := e1.out.1
  let w := e1.out.2
  let p := e2.out.1
  let q := e2.out.2
  
  (∃ (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))), c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false) ∧
  (∃ (h : GraphG.Adj (Sum.inr ⟨e1, SigData_edge_nd1 A B s⟩) (Sum.inl (u1, v))), c ⟨Sym2.mk (Sum.inr ⟨e1, SigData_edge_nd1 A B s⟩, Sum.inl (u1, v)), h⟩ = true) ∧
  (∃ (h : GraphG.Adj (Sum.inl (p, v)) (Sum.inl (q, v))), c ⟨Sym2.mk (Sum.inl (p, v), Sum.inl (q, v)), h⟩ = true) ∧
  (∃ (h : GraphG.Adj (Sum.inr ⟨e2, SigData_edge_nd2 A B s⟩) (Sum.inl (u2, v))), c ⟨Sym2.mk (Sum.inr ⟨e2, SigData_edge_nd2 A B s⟩, Sum.inl (u2, v)), h⟩ = false)

/-
Adjacency between $X$ and grid vertices.
-/
lemma adj_X_col_redef
  (e : Sym2 V1) (he : ¬ e.IsDiag)
  (u : V1) (hu : u ∈ e)
  (v : V2) :
  GraphG.Adj (Sum.inr ⟨e, he⟩) (Sum.inl (u, v)) := by
  simp [GraphG, AdjG]
  exact hu

/-
If an edge in the grid is red, one of the edges connecting it to the corresponding vertex in X must be blue.
-/
lemma exists_blue_edge_to_X
  (c : GraphG.edgeSet → Bool)
  (u w : V1)
  (v : V2)
  (h_neq : u ≠ w)
  (h_red : ∃ (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))), c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false)
  (h_no_mono : ∀ (x y z : VertexG) (hxy : GraphG.Adj x y) (hyz : GraphG.Adj y z) (hxz : GraphG.Adj x z),
    ¬(c ⟨Sym2.mk (x, y), hxy⟩ = c ⟨Sym2.mk (y, z), hyz⟩ ∧ c ⟨Sym2.mk (y, z), hyz⟩ = c ⟨Sym2.mk (x, z), hxz⟩)) :
  ∃ (u1 : V1), (u1 = u ∨ u1 = w) ∧
    ∃ (h_nd : ¬(Sym2.mk (u, w)).IsDiag) (h_adj : GraphG.Adj (Sum.inr ⟨Sym2.mk (u, w), h_nd⟩) (Sum.inl (u1, v))),
      c ⟨Sym2.mk (Sum.inr ⟨Sym2.mk (u, w), h_nd⟩, Sum.inl (u1, v)), h_adj⟩ = true := by
        contrapose! h_no_mono;
        -- Let's choose $x = X_{(u,w)}$, $y = (u,v)$, and $z = (w,v)$.
        use Sum.inr ⟨Sym2.mk (u, w), by
          cases h : Sym2.mk ( u, w ) ; aesop⟩, Sum.inl (u, v), Sum.inl (w, v)
        generalize_proofs at *;
        use adj_X_col_redef _ ‹_› _ (by
        exact Sym2.mem_mk_left u w) _, h_red.choose, adj_X_col_redef _ ‹_› _ (by
        exact Sym2.mem_mk_right u w) _
        generalize_proofs at *;
        have := h_no_mono u ( Or.inl rfl ) ‹_› ‹_›; have := h_no_mono w ( Or.inr rfl ) ‹_› ‹_›; aesop;

/-
If there are no monochromatic triangles, then any clique of size 3 must contain a blue edge.
-/
lemma exists_blue_edge_in_clique3
  (c : GraphG.edgeSet → Bool)
  (B : Finset V1)
  (hB : H1.IsClique B)
  (hB_card : B.card = 3)
  (v : V2)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩)) :
  ∃ (u w : V1) (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
    u ∈ B ∧ w ∈ B ∧ c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (w, v)), h⟩ = true := by
      -- Suppose for contradiction that all edges in $B \times \{v\}$ are red (false).
      by_contra h_contra
      have h_all_red : ∀ u w : V1, u ∈ B → w ∈ B → u ≠ w → c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), by
        have := Finset.card_eq_three.mp hB_card; obtain ⟨ u, v, w, hu, hv, hw, h ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        have := h_no_mono ( Sum.inl ( u, ‹_› ) ) ( Sum.inl ( v, ‹_› ) ) ( Sum.inl ( w, ‹_› ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
        exact False.elim <| this ( by exact Or.inr ⟨ rfl, hB.2.1 ⟩ ) ( by exact Or.inr ⟨ rfl, hB.1 ⟩ ) ( by exact Or.inr ⟨ rfl, hB.2.2 ⟩ )⟩ = false := by
        grind
      generalize_proofs at *;
      obtain ⟨u, w, x, hu, hw, hx, h_adj⟩ : ∃ u w x : V1, u ∈ B ∧ w ∈ B ∧ x ∈ B ∧ u ≠ w ∧ u ≠ x ∧ w ≠ x ∧ GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v)) ∧ GraphG.Adj (Sum.inl (w, v)) (Sum.inl (x, v)) ∧ GraphG.Adj (Sum.inl (u, v)) (Sum.inl (x, v)) := by
        rcases Finset.card_eq_three.mp hB_card with ⟨ u, w, x, hu, hw, hx, h ⟩ ; use u, w, x ; aesop;
      exact h_no_mono ( Sum.inl ( u, v ) ) ( Sum.inl ( w, v ) ) ( Sum.inl ( x, v ) ) h_adj.2.2.2.1 h_adj.2.2.2.2.1 h_adj.2.2.2.2.2 ⟨ by aesop, by aesop ⟩

/-
If there are no monochromatic triangles, then for every vertex v in V2, there exists a valid signature s in SigData A B.
-/
lemma exists_signature_for_v
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (v : V2)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩)) :
  ∃ (s : SigData A B), ValidSignature c A B v s := by
    -- By Lemma 25, there exists a red edge (u, w) in A and a blue edge (p, q) in B.
    obtain ⟨u, w, h_red⟩ : ∃ u w : V1, u ∈ A ∧ w ∈ A ∧ u ≠ w ∧ ∃ (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))), c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false := by
      have h_exists_red_edge : ∃ (u w : V1) (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))), u ∈ A ∧ w ∈ A ∧ c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false := by
        apply exists_red_edge_in_clique3 c A hA hA_card v h_no_mono;
      grind
    obtain ⟨p, q, h_blue⟩ : ∃ p q : V1, p ∈ B ∧ q ∈ B ∧ p ≠ q ∧ ∃ (h : GraphG.Adj (Sum.inl (p, v)) (Sum.inl (q, v))), c ⟨Sym2.mk (Sum.inl (p, v), Sum.inl (q, v)), h⟩ = true := by
      convert exists_blue_edge_in_clique3 c B hB hB_card v h_no_mono using 1;
      grind +ring;
    -- By Lemma 25, there exists a blue edge (p, q) in B and a red edge (u, w) in A.
    obtain ⟨u1, hu1⟩ : ∃ u1 : V1, (u1 = u ∨ u1 = w) ∧ ∃ (h_nd : ¬(Sym2.mk (u, w)).IsDiag) (h_adj : GraphG.Adj (Sum.inr ⟨Sym2.mk (u, w), h_nd⟩) (Sum.inl (u1, v))), c ⟨Sym2.mk (Sum.inr ⟨Sym2.mk (u, w), h_nd⟩, Sum.inl (u1, v)), h_adj⟩ = true := by
      apply exists_blue_edge_to_X c u w v h_red.2.2.1 h_red.2.2.2 h_no_mono
    obtain ⟨u2, hu2⟩ : ∃ u2 : V1, (u2 = p ∨ u2 = q) ∧ ∃ (h_nd : ¬(Sym2.mk (p, q)).IsDiag) (h_adj : GraphG.Adj (Sum.inr ⟨Sym2.mk (p, q), h_nd⟩) (Sum.inl (u2, v))), c ⟨Sym2.mk (Sum.inr ⟨Sym2.mk (p, q), h_nd⟩, Sum.inl (u2, v)), h_adj⟩ = false := by
      apply Classical.byContradiction
      intro h_no_u2;
      exact h_no_mono ( Sum.inr ⟨ s(p, q), by aesop ⟩ ) ( Sum.inl ( p, v ) ) ( Sum.inl ( q, v ) ) ( by exact adj_X_col_redef _ ( by aesop ) _ ( by aesop ) _ ) ( by exact h_blue.2.2.2.choose ) ( by exact adj_X_col_redef _ ( by aesop ) _ ( by aesop ) _ ) <| by aesop;
    generalize_proofs at *;
    refine' ⟨ ⟨ ⟨ ⟨ Sym2.mk ( u, w ), u1 ⟩, _ ⟩, ⟨ ⟨ Sym2.mk ( p, q ), u2 ⟩, _ ⟩ ⟩, _ ⟩ <;> simp_all +decide [ ValidSignature ];
    all_goals norm_num [ Finset.mem_filter, Finset.mem_product, edgeWithVertexFinset ] at *;
    all_goals simp_all +decide [ Quot.out ];
    exact ⟨ ⟨ ⟨ u, w, ⟨ h_red.1, h_red.2.1, h_red.2.2.1 ⟩, by tauto ⟩, by rcases hu1.1 with ( rfl | rfl ) <;> tauto ⟩, ⟨ u, w, ⟨ h_red.1, h_red.2.1, h_red.2.2.1 ⟩, by tauto ⟩ ⟩
    all_goals generalize_proofs at *;
    · exact ⟨ ⟨ ⟨ p, q, ⟨ h_blue.1, h_blue.2.1, h_blue.2.2.1 ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩, by rcases hu2.1 with ( rfl | rfl ) <;> tauto ⟩, ⟨ p, q, ⟨ h_blue.1, h_blue.2.1, h_blue.2.2.1 ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩ ⟩;
    · refine' ⟨ _, _, _, _ ⟩
      all_goals generalize_proofs at *;
      · cases' ‹∃ x : V1 × V1, x = ( u, w ) ∨ x = ( w, u ) ›.choose_spec with h h <;> simp_all +decide [ Sym2.eq_swap ];
        exact ⟨ by simpa only [ SimpleGraph.adj_comm ] using h_red.2.2.2.choose, h_red.2.2.2.choose_spec ⟩;
      · exact hu1.2.choose_spec.imp fun h => by tauto;
      · cases' ‹∃ x : V1 × V1, x = ( p, q ) ∨ x = ( q, p ) ›.choose_spec with h h <;> simp_all +decide [ Sym2.eq_swap ];
        exact ⟨ by simpa only [ SimpleGraph.adj_comm ] using h_blue.2.2.2.choose, by simpa only [ SimpleGraph.adj_comm ] using h_blue.2.2.2.choose_spec ⟩;
      · grind

/-
There exist two adjacent vertices in H2 that have the same signature.
-/
noncomputable def signature_map
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩))
  (v : V2) : SigData A B :=
  Classical.choose (exists_signature_for_v c A B hA hA_card hB hB_card v h_no_mono)

lemma signature_map_valid
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩))
  (v : V2) :
  ValidSignature c A B v (signature_map c A B hA hA_card hB hB_card h_no_mono v) :=
  Classical.choose_spec (exists_signature_for_v c A B hA hA_card hB hB_card v h_no_mono)

lemma exists_same_signature_edge
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩)) :
  ∃ (v w : V2), H2.Adj v w ∧
    signature_map c A B hA hA_card hB hB_card h_no_mono v = signature_map c A B hA hA_card hB hB_card h_no_mono w := by
      by_contra! h;
      -- By the properties of the Ramsey number, there exists a monochromatic copy of $K_2$ in $H_2$.
      obtain ⟨v, w, hvw, h_mono⟩ : ∃ v w : V2, H2.Adj v w ∧ (signature_map c A B hA hA_card hB hB_card h_no_mono v = signature_map c A B hA hA_card hB hB_card h_no_mono w) := by
        have h_ramsey : ∀ (f : V2 → Fin 36), ∃ v w : V2, H2.Adj v w ∧ f v = f w := by
          intro f
          by_contra h_no_monochromatic
          push_neg at h_no_monochromatic;
          have := H2_props.2;
          obtain ⟨ U, hU_mono, hU_iso ⟩ := this f;
          obtain ⟨ g, hg ⟩ := hU_iso.2;
          have := @h_no_monochromatic ( g 0 ) ( g 1 ) ?_ <;> simp_all +decide [ K2 ]
        have h_equiv : Nonempty (SigData A B ≃ Fin 36) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ card_SigData A B hA_card hB_card ] ⟩;
        exact h_ramsey ( fun v => h_equiv.some ( signature_map c A B hA hA_card hB hB_card h_no_mono v ) ) |> fun ⟨ v, w, hvw, h ⟩ => ⟨ v, w, hvw, h_equiv.some.injective h ⟩;
      exact h v w hvw h_mono

/-
If v and w are adjacent in H2, then (u, v) and (u, w) are adjacent in G for any u.
-/
lemma adj_row_of_adj_H2
  (u : V1) (v w : V2) (h : H2.Adj v w) :
  GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u, w)) := by
    exact Or.inl ⟨ rfl, h ⟩

/-
If two adjacent vertices in H2 have the same signature and the rows corresponding to the cliques A and B have the same color on the edge connecting them, then there is a monochromatic triangle.
-/
lemma same_signature_contradiction
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (v w : V2)
  (hvw : H2.Adj v w)
  (s : SigData A B)
  (h_valid_v : ValidSignature c A B v s)
  (h_valid_w : ValidSignature c A B w s)
  (k : Bool)
  (h_row_color : ∀ u, u ∈ A ∨ u ∈ B → c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ = k)
  (h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩)) :
  False := by
    cases k <;> simp_all +decide only [ValidSignature];
    · -- From the validity of the signatures, we know that the edge from X to (u1, v) is blue and the edge from X to (u2, v) is red.
      obtain ⟨h1, h2, h3, h4⟩ := h_valid_v
      obtain ⟨h5, h6, h7, h8⟩ := h_valid_w;
      obtain ⟨ h, h' ⟩ := h3; obtain ⟨ h'', h''' ⟩ := h4; specialize h_no_mono ( Sum.inr ⟨ ( s.2.val.1 ), SigData_edge_nd2 A B s ⟩ ) ( Sum.inl ( s.2.val.2, v ) ) ( Sum.inl ( s.2.val.2, w ) ) ; simp_all +decide [ SimpleGraph.adj_comm ] ;
      specialize h_no_mono ( by exact h'' ) ( by exact? )
      generalize_proofs at *;
      convert h_row_color ( s.2.val.2 ) _ using 1
      all_goals generalize_proofs at *;
      · grind +ring;
      · exact Finset.mem_union.mp ( Finset.mem_filter.mp s.2.2 |>.1 |> Finset.mem_product.mp |>.2 |> fun h => by aesop );
    · contrapose! h_no_mono;
      use Sum.inr ⟨ ( s.1.val.1 ), by
        exact SigData_edge_nd1 A B s ⟩, Sum.inl ( s.1.val.2, v ), Sum.inl ( s.1.val.2, w )
      generalize_proofs at *;
      exact Finset.mem_product.mp ( Finset.mem_filter.mp s.1.2 |>.1 ) |>.2 |> fun x => by aesop;

/-
If an induced subgraph is isomorphic to 2K3, it contains two disjoint cliques of size 3.
-/
lemma extract_disjoint_cliques
  (U : Set V1)
  (h_iso : Nonempty (H1.induce U ≃g TwoK3)) :
  ∃ (A B : Finset V1),
    (A : Set V1) ⊆ U ∧ (B : Set V1) ⊆ U ∧
    H1.IsClique A ∧ A.card = 3 ∧
    H1.IsClique B ∧ B.card = 3 ∧
    Disjoint A B := by
      -- By definition of $TwoK3$, there exist two disjoint cliques of size 3 in $TwoK3$.
      obtain ⟨A, B, hA, hB, h_disjoint⟩ : ∃ A B : Finset (Fin 3 ⊕ Fin 3), A.card = 3 ∧ B.card = 3 ∧ A ∩ B = ∅ ∧ (TwoK3.IsClique A) ∧ (TwoK3.IsClique B) := by
        exists { Sum.inl 0, Sum.inl 1, Sum.inl 2 }, { Sum.inr 0, Sum.inr 1, Sum.inr 2 } ; simp +decide [ SimpleGraph.IsClique ] ;
        simp +decide [ TwoK3 ];
      obtain ⟨g, hg⟩ : ∃ g : U ≃ Fin 3 ⊕ Fin 3, ∀ u v : U, H1.Adj u v ↔ TwoK3.Adj (g u) (g v) := by
        exact ⟨ h_iso.some.toEquiv, fun u v => by simp +decide [ SimpleGraph.Iso.map_adj_iff ] ⟩;
      refine' ⟨ Finset.image ( fun x : Fin 3 ⊕ Fin 3 => ( g.symm x : V1 ) ) A, Finset.image ( fun x : Fin 3 ⊕ Fin 3 => ( g.symm x : V1 ) ) B, _, _, _, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
      any_goals rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using g.symm.injective <| Subtype.ext hxy ] ; aesop;
      · exact fun x hx => by simp;
      · grind;
      · intro x hx y hy; aesop;
      · intro x hx y hy hxy; aesop;
      · intro a ha; rcases ha with ( ⟨ x, hx, rfl ⟩ | ⟨ x, hx, rfl ⟩ ) <;> simp_all +decide [ Finset.ext_iff ] ;
        · grind;
        · grind

/-
If U is a set of vertices such that all rows u in U induce the same coloring chi on H2, and A, B are subsets of U, then for any edge vw in H2 with color k under chi, the corresponding edges (u, v)~(u, w) in G have color k for all u in A or B.
-/
lemma row_color_of_cliques_in_U
  (c : GraphG.edgeSet → Bool)
  (U : Set V1)
  (chi : H2.edgeSet → Bool)
  (hU_color : ∀ u ∈ U, row_coloring_map c u = chi)
  (A B : Finset V1)
  (hA_sub : (A : Set V1) ⊆ U)
  (hB_sub : (B : Set V1) ⊆ U)
  (v w : V2)
  (hvw : H2.Adj v w)
  (k : Bool)
  (hk : chi ⟨Sym2.mk (v, w), hvw⟩ = k) :
  ∀ u, u ∈ A ∨ u ∈ B → c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ = k := by
    -- By definition of `row_coloring_map`, we know that `row_coloring_map c u ⟨(v, w), hvw⟩ = c ⟨(u, v)(u, w), ...⟩`.
    have h_row_coloring_map : ∀ u ∈ U, row_coloring_map c u ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ := by
      -- By definition of `row_coloring_map`, we know that `row_coloring_map c u ⟨(v, w), hvw⟩` is the color of the edge `(u, v) \sim (u, w)` in `G` under `c`.
      simp [row_coloring_map, induced_coloring];
      congr! 2
      generalize_proofs at *; (
      have := Quot.out_eq ( s(v, w) ) ; ( rcases h : Quot.out ( s(v, w) ) with ⟨ x, y ⟩ ; aesop; ) ;)
    generalize_proofs at *; (
    exact fun u hu => h_row_coloring_map u ( hu.elim ( fun hu => hA_sub hu ) fun hu => hB_sub hu ) ▸ hU_color u ( hu.elim ( fun hu => hA_sub hu ) fun hu => hB_sub hu ) ▸ hk ▸ rfl;)

/-
The graph G is edge-Ramsey for triangles.
-/
theorem folkman_theorem : EdgeRamseyTriangle GraphG := by
  intro c
  obtain ⟨U, chi, h_iso, h_color⟩ := exists_monochromatic_U c;
  obtain ⟨ A, B, hA_sub, hB_sub, hA, hA_card, hB, hB_card, h_disjoint ⟩ := extract_disjoint_cliques U h_iso;
  by_cases h_no_mono : ∀ (u v w : VertexG) (huv : GraphG.Adj u v) (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w), ¬(c ⟨Sym2.mk (u, v), huv⟩ = c ⟨Sym2.mk (v, w), hvw⟩ ∧ c ⟨Sym2.mk (v, w), hvw⟩ = c ⟨Sym2.mk (u, w), huw⟩);
  · obtain ⟨ v, w, hvw, h_eq ⟩ := exists_same_signature_edge c A B hA hA_card hB hB_card h_no_mono;
    -- Let `k` be the color of the edge `vw` in `H2` under `chi`.
    obtain ⟨k, hk⟩ : ∃ k : Bool, chi ⟨Sym2.mk (v, w), hvw⟩ = k := by
      use chi ⟨Sym2.mk (v, w), hvw⟩;
    -- By `row_color_of_cliques_in_U`, for any `u \in A \cup B`, the edge `(u, v) \sim (u, w)` has color `k`.
    have h_row_color : ∀ u, u ∈ A ∨ u ∈ B → c ⟨Sym2.mk (Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ = k := by
      apply row_color_of_cliques_in_U c U chi h_color A B hA_sub hB_sub v w hvw k hk;
    exact False.elim ( same_signature_contradiction c A B v w hvw _ ( signature_map_valid c A B hA hA_card hB hB_card h_no_mono v ) ( by simpa only [ h_eq ] using signature_map_valid c A B hA hA_card hB hB_card h_no_mono w ) k h_row_color h_no_mono );
  · exact by push_neg at h_no_mono; exact h_no_mono;

/-
There exists a graph G with clique number 3 that is edge-Ramsey for triangles.
-/
theorem erdos_582 : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), G.cliqueNum = 3 ∧ EdgeRamseyTriangle G := by
  use VertexG, inferInstance, inferInstance, GraphG
  exact ⟨GraphG_cliqueNum_eq_three, folkman_theorem⟩

#print axioms erdos_582
-- 'erdos_582' depends on axioms: [propext, Classical.choice, Quot.sound]
