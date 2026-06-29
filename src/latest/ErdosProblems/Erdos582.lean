/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 582.
https://www.erdosproblems.com/forum/thread/582

Informal authors:
- Jon Folkman

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos582.md
-/
/-
We have constructed a graph $G$ that is $K_4$-free (clique number 3) and edge-Ramsey
for triangles ($G \to (K_3, K_3)$).
The graph $G$ is constructed based on the Folkman graph construction.
We defined the graph $G$ using auxiliary graphs $H_1$ and $H_2$ with specific Ramsey properties.
We proved that $\omega(G) = 3$ (`GraphG_cliqueNum_eq_three`).
We proved that for any 2-edge-coloring of $G$, there exists a monochromatic triangle
(`folkman_theorem`).
Finally, we combined these results to prove the main theorem `erdos_582`.
-/

import Mathlib

namespace Erdos582

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (v0 : V) (H' : SimpleGraph W)

set_option maxHeartbeats 50000000
-- Several generated Ramsey-partition arguments time out at the default heartbeat limit.
set_option maxRecDepth 4000

/-
Definitions of vertex-partition Ramsey property, and edge-Ramsey property for triangles.
-/
def VertexPartitionRamsey {V W : Type*} (n : ℕ) (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∀ (f : W → Fin n),
    ∃ i, ∃ (S : Set W), (∀ w ∈ S, f w = i) ∧ Nonempty (G ≃g H.induce S)

def EdgeRamseyTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (c : G.edgeSet → Bool),
    ∃ (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w),
      c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧
        c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩

/-
If $H \Rightarrow_2 K$ and $K \Rightarrow_n G$, then $H \Rightarrow_{n+1} G$.
-/
lemma ramsey_trans
  {V W U : Type*}
  (G : SimpleGraph V) (K : SimpleGraph W) (H : SimpleGraph U)
  (n : ℕ) (hn : n ≥ 1)
  (hK : VertexPartitionRamsey n K G)
  (hH : VertexPartitionRamsey 2 H K) :
  VertexPartitionRamsey (n + 1) H G := by
    classical
    intro f;
    -- Define a new function $g : U \to \{0, 1\}$ by $g(u) = 0$ if $f(u) < n$,
    -- and $g(u) = 1$ if $f(u) = n$.
    set g : U → Fin 2 := fun u => if f u < n then 0 else 1;
    -- By hypothesis $hH$, there exists $i \in \{0, 1\}$ and $S \subseteq U$ such
    -- that $H[S] \cong K$ and $g$ takes value $i$ throughout $S$.
    obtain ⟨i, S, hS⟩ :
        ∃ i : Fin 2, ∃ S : Set U,
          (∀ w ∈ S, g w = i) ∧ Nonempty (K ≃g H.induce S) := by
      have := hH g;
      exact this;
    -- Let's consider the two cases for $i$.
    by_cases hi : i = 0;
    · -- Since $g$ is constant $0$ on $S$, we have $f(u) < n$ for all $u \in S$.
      have h_f_lt_n : ∀ w ∈ S, f w < n := by
        grind;
      -- Since $K \Rightarrow_n G$, there exists $j \in \{0, \dots, n-1\}$ and
      -- $T \subseteq W$ such that $K[T] \cong G$ and $f'$ takes value $j$ on $T$.
      obtain ⟨j, T, hT⟩ :
          ∃ j : Fin n, ∃ T : Set W,
            (∀ w ∈ T,
              (fun w =>
                ⟨f (hS.right.some w), h_f_lt_n _ (hS.right.some w).2⟩) w = j) ∧
              Nonempty (G ≃g K.induce T) := by
        convert hK _;
      refine ⟨ ⟨ j, by linarith [ Fin.is_lt j ] ⟩,
        Set.image (fun w : T => (hS.2.some w : U)) (Set.univ : Set T), ?_, ?_ ⟩
      · intro w hw
        rcases hw with ⟨ a, _, rfl ⟩
        exact Fin.ext <| by
          simpa [ Fin.ext_iff ] using congr_arg Fin.val ( hT.1 a a.2 ) ;
      · simp_all +decide
        refine ⟨ hT.2.some.trans ?_ ⟩
        refine
          { toEquiv := Equiv.ofBijective
              (fun x => ⟨ (hS.2.some x : U), Set.mem_image_of_mem _ (Set.mem_univ x) ⟩)
              ⟨ ?_, ?_ ⟩
            map_rel_iff' := ?_ }
        · intro x y hxy
          simp_all +decide
          have := hS.2.some.injective ( Subtype.ext hxy ) ; aesop
        · intro x
          simp_all +decide
          rcases x with ⟨ x, hx ⟩ ; aesop
        · intro a b
          constructor
          · intro h
            have := hS.2.some.symm.map_adj_iff.2 h
            aesop
          · intro h
            have := hS.2.some.map_adj_iff.2 h
            aesop
    · -- Since $i = 1$, for all $w \in S$, we have $f w = n$.
      have h_f_eq_n : ∀ w ∈ S, f w = n := by
        grind;
      -- Since $K$ contains a monochromatic copy of $G$ with color $n$, we can find
      -- such a copy in $H$.
      obtain ⟨T, hT⟩ : ∃ T : Set S, Nonempty (G ≃g (SimpleGraph.induce S H).induce T) := by
        obtain ⟨ ϕ ⟩ := hS.2;
        obtain ⟨ T, hT ⟩ := hK ( fun w => ⟨ 0, by linarith ⟩ );
        obtain ⟨ S, hS₁, hS₂ ⟩ := hT;
        refine ⟨ ϕ '' S, ?_ ⟩;
        refine ⟨ hS₂.some.trans ?_ ⟩
        refine
          { toEquiv := Equiv.ofBijective
              (fun x => ⟨ ϕ x, Set.mem_image_of_mem _ x.2 ⟩)
              ⟨ ?_, ?_ ⟩
            map_rel_iff' := ?_ }
        · intro x y hxy
          exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
        · intro x
          simp_all +decide [ SimpleGraph.induce ]
          rcases x with ⟨ x, hx ⟩ ; aesop
        · intro a b
          constructor
          · exact fun h => ϕ.map_adj_iff.mp h
          · exact fun h => ϕ.map_adj_iff.mpr h
      refine ⟨ ⟨ n, Nat.lt_succ_self n ⟩, T.image Subtype.val, ?_, ?_ ⟩ <;>
        simp_all +decide [ SimpleGraph.induce, Set.image ];
      · exact fun w hw hw' => Fin.ext ( h_f_eq_n w hw );
      · obtain ⟨ e ⟩ := hT;
        refine ⟨ e.trans ?_ ⟩;
        refine ⟨ ?_, ?_ ⟩;
        · let F : T → { x : U // ∃ a ∈ T, (a : U) = x } :=
            fun x => ⟨ x.val, x, x.2, rfl ⟩
          have h_inj : Function.Injective F := by
            intro x y hxy
            have hU : ((x : S) : U) = ((y : S) : U) :=
              congrArg
                (fun z : { x : U // ∃ a ∈ T, (a : U) = x } => z.1)
                hxy
            exact Subtype.ext (Subtype.ext hU)
          have h_surj : Function.Surjective F := by
            intro x
            rcases x with ⟨ x, ⟨ a, ha, rfl ⟩ ⟩
            exact ⟨ ⟨ a, ha ⟩, rfl ⟩
          exact Equiv.ofBijective F ⟨ h_inj, h_surj ⟩
        · intro a b
          rfl

/-
Reduction of the existence of $H(n,G)$ to the case $n=2$.
If for every graph $G$ there exists $H$ such that $\om(H)=\om(G)$ and
$H \Rightarrow_2 G$, then for every $n \ge 1$ and every $G$ there exists $H$ such
that $\om(H)=\om(G)$ and $H \Rightarrow_n G$.
-/
omit [Fintype V] [DecidableEq V] in
theorem exists_H_n_of_exists_H_2
  (h2 : ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey 2 H G) :
  ∀ (n : ℕ) (hn : n ≥ 1) (V : Type) [Finite V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey n H G := by
        classical
        intro n hn;
        induction n, hn using Nat.le_induction with
        | base =>
          -- For the base case $n = 1$, we can take $H = G$.
          intros V _ G
          letI := Fintype.ofFinite V
          use V, inferInstance, inferInstance, G
          simp [VertexPartitionRamsey];
          intro f; use Set.univ; simp +decide [ Fin.eq_zero ] ;
          refine ⟨ ?_, ?_ ⟩;
          exacts [
            Equiv.ofBijective (fun x => ⟨ x, trivial ⟩)
              ⟨ fun x y hxy => by
                  simpa using hxy,
                fun x => by
                  cases x
                  exact ⟨ _, rfl ⟩ ⟩,
            by simp +decide [ SimpleGraph.induce ] ];
        | succ n hn ih =>
          intro V _ G
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
def G_double_prime : SimpleGraph (V_double_prime G v0) :=
  (G_prime G v0).induce (V_double_prime G v0)

def X_set : Set (Set W) := { S | Nonempty ((H'.induce S) ≃g (G_double_prime G v0)) }

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
lemma X_nonempty (h : VertexPartitionRamsey 2 H' (G_prime G v0)) : (X_set G v0 H').Nonempty := by
  classical
  -- By definition of $X_set$, we need to show that there exists a subset
  -- $S \subseteq (G 인덱스 (SimpleGraph.induce {v0}ᶜ G)).vertexSet$ such that
  -- $H'.induce (Gszczę (H'.induce {v0}ᶜ H')) S) \cong G''$.
  obtain ⟨S, hS⟩ := h (fun _ => 0);
  obtain ⟨ S', hS' ⟩ := hS;
  obtain ⟨ f, hf ⟩ := hS'.2;
  refine ⟨ ?_, ?_, ?_ ⟩;
  focus
    exact Set.image ( fun x : { x : V // x ≠ v0 ∧ G.Adj x v0 } => f ⟨ x, by
      exact x.2.1 ⟩ ) ( Set.univ : Set { x : V // x ≠ v0 ∧ G.Adj x v0 } );
  all_goals generalize_proofs at *;
  focus
    refine Equiv.ofBijective ?_ ⟨ ?_, ?_ ⟩;
    focus
      use fun x => ⟨ f.symm ⟨ x, by
        grind ⟩, by
        rcases x with ⟨ x, hx ⟩;
        rcases hx with ⟨ y, -, rfl ⟩;
        simp +decide [ V_double_prime ];
        exact y.2.2 ⟩
    all_goals generalize_proofs at *
    all_goals generalize_proofs at *;
    all_goals norm_num [ Function.Injective, Function.Surjective ];
    focus
      exact fun a ha ha' => ⟨ _, ⟨ a, ⟨ ha, ha' ⟩, rfl ⟩, by simp +decide ⟩
  intro a x
  simp +decide
  convert hf.symm using 1
  simp +decide [SimpleGraph.induce]

/-
Definitions of parameters and f_map.
-/

def t_param (W : Type*) [Fintype W] : ℕ := 2 ^ (Fintype.card W)
def r_param (V : Type*) [Fintype V] : ℕ := Fintype.card V
def I_param (V W : Type*) [Fintype V] [Fintype W] : ℕ := (r_param V - 1) * t_param W + 1

abbrev I_type (V W : Type*) [Fintype V] [Fintype W] : Type := Fin (I_param V W)

abbrev J_type (V W : Type*) [Fintype V] [Fintype W] : Type :=
  { s : Finset (I_type V W) // s.card = r_param V }

noncomputable def f_map
    (V W : Type*) [Fintype V] [Fintype W] (T : J_type V W) :
    {x // x ∈ T.val} ≃ V :=
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
    intro x y hxy; induction y
    · rcases x with ( ⟨ v', S', T' ⟩ | ⟨ w', i' ⟩ ) <;> simp +decide [ AdjH ] at hxy ⊢
      all_goals generalize_proofs at *;
      · exact ⟨ hxy.1.symm, hxy.2.1.symm, hxy.2.2.symm ⟩;
      · exact hxy;
    · cases x <;> simp +decide [ AdjH ] at hxy ⊢ ;
      focus
        aesop ( simp_config := { singlePass := true } ) ;
      exact ⟨ hxy.1.symm, hxy.2.symm ⟩
  loopless := ⟨fun x h => by
    rcases x with ⟨v, S, T⟩ | ⟨w, i⟩ <;> simp [AdjH] at h⟩

/-
Lower bound on the clique number of H(2,G).
-/
omit [DecidableEq V] [DecidableEq W] in
lemma GraphH_cliqueNum_ge
  (h_ramsey : VertexPartitionRamsey 2 H' (G_prime G v0)) :
  G.cliqueNum ≤ (GraphH G v0 H').cliqueNum := by
    classical
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
    have h_embedding :
        ∃ (f : V → VertexH G v0 H'),
          Function.Injective f ∧
            ∀ u v, G.Adj u v → (GraphH G v0 H').Adj (f u) (f v) := by
      refine ⟨ fun v => Sum.inl ( v, ⟨ S, hS ⟩, T ), ?_, ?_ ⟩ <;>
        simp +decide [ Function.Injective ];
      · grind;
      · exact fun u v huv => by exact ⟨ rfl, rfl, huv ⟩ ;
    obtain ⟨ f, hf_inj, hf_adj ⟩ := h_embedding;
    refine le_csSup (α := ℕ) ?_ ?_;
    · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
    · obtain ⟨ s, hs ⟩ := ( show ∃ s : Finset V, G.IsNClique ( G.cliqueNum ) s from by
                              exact exists_isNClique_cliqueNum );
      refine ⟨ Finset.image f s, ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · intro x hx y hy hxy; aesop;
      · rw [ Finset.card_image_of_injective _ hf_inj, hs.2 ]


/-
If a clique contains at least two type A vertices, its size is at most the clique number of G.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma clique_case_two_A
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (x y : VertexH G v0 H')
  (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
  (hx_A : ∃ a, x = Sum.inl a) (hy_A : ∃ b, y = Sum.inl b) :
  Q.card ≤ G.cliqueNum := by
    classical
    -- Since there are at least two type A vertices, there cannot be any type B vertices in $Q$.
    have h_no_B : ∀ z ∈ Q, ¬∃ w i, z = Sum.inr (w, i) := by
      intro z hz hz_B
      obtain ⟨w, i, hz_B⟩ := hz_B
      have h_adj_x : (GraphH G v0 H').Adj x z := by
        exact hQ ( by aesop ) ( by aesop ) ( by aesop )
      have h_adj_y : (GraphH G v0 H').Adj y z := by
        exact hQ hy hz ( by aesop ) |> fun h => by aesop;
      generalize_proofs at *; (
      rcases hx_A with ⟨ a, rfl ⟩ ;
      rcases hy_A with ⟨ b, rfl ⟩ ;
      simp_all +decide [ GraphH ] ;
      rcases a with ⟨ a₁, a₂, a₃ ⟩ ;
      rcases b with ⟨ b₁, b₂, b₃ ⟩ ;
      simp_all +decide [ AdjH ] ;
      unfold AdjH at hQ; specialize hQ hx hy; aesop;)
    generalize_proofs at *; (
    -- Since there are at least two type A vertices, there cannot be any type B vertices
    -- in $Q$, so $Q$ consists of type A vertices with fixed $S, T$.
    have h_typeA :
        ∃ S : X_type G v0 H', ∃ T : J_type V W,
          ∀ z ∈ Q, ∃ a : V, z = Sum.inl (a, S, T) := by
      -- Since there are at least two type A vertices, there cannot be any type B
      -- vertices in $Q$, so $Q$ consists of type A vertices with fixed $S, T$.
      -- Let's obtain these $S$ and $T$.
      obtain ⟨a, ha⟩ := hx_A
      obtain ⟨b, hb⟩ := hy_A
      have hS :
          ∀ z ∈ Q, ∃ c : V × (X_type G v0 H') × (J_type V W),
            z = Sum.inl c ∧ c.2.1 = a.2.1 ∧ c.2.2 = a.2.2 := by
        intro z hz
        obtain ⟨c, hc⟩ : ∃ c : V × (X_type G v0 H') × (J_type V W), z = Sum.inl c := by
          cases z <;> aesop ( simp_config := { singlePass := true } ) ;
        generalize_proofs at *; (
        have := hQ hx hz; have := hQ hy hz; simp_all +decide [ GraphH ] ;
        by_cases hac : a = c <;>
        by_cases hbc : b = c <;>
        simp_all +decide [ AdjH ] ;
        focus
          aesop ( simp_config := { singlePass := true } ) ;
        · exact ⟨ c.1, by aesop ⟩;
        · grind)
      generalize_proofs at *; (
      exact ⟨ a.2.1, a.2.2, fun z hz => by
        obtain ⟨ c, rfl, hc₁, hc₂ ⟩ := hS z hz
        exact ⟨ c.1, by aesop ⟩ ⟩)
    generalize_proofs at *; (
    obtain ⟨ S, T, hS ⟩ := h_typeA
    have h_clique_G :
        (Finset.image
          (fun z => (z : VertexH G v0 H').elim (fun a => a.1) (fun b => v0))
          Q).card ≤ G.cliqueNum := by
      have h_clique_G :
          ∀ u v : V,
            u ∈ Finset.image
              (fun z => (z : VertexH G v0 H').elim (fun a => a.1) (fun b => v0))
              Q →
            v ∈ Finset.image
              (fun z => (z : VertexH G v0 H').elim (fun a => a.1) (fun b => v0))
              Q →
            u ≠ v → G.Adj u v := by
        intros u v hu hv huv
        obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.mp hv
        have h_adj : (GraphH G v0 H').Adj z₁ z₂ := by
          exact hQ hz₁ hz₂ ( by aesop ) |> fun h => by aesop;
        generalize_proofs at *; (
        rcases hS z₁ hz₁ with ⟨ a₁, rfl ⟩ ;
        rcases hS z₂ hz₂ with ⟨ a₂, rfl ⟩ ;
        simp_all +decide [ GraphH ] ;
        cases h_adj ; aesop ( simp_config := { singlePass := true } ) ;)
      generalize_proofs at *; (
      have h_clique_G :
          ∀ (S : Finset V),
            (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) → S.card ≤ G.cliqueNum := by
        intro S hS; exact (by
        refine le_csSup ?_ ?_ <;> norm_num +zetaDelta at *;
        · exact ⟨ Fintype.card V, fun n hn => by
            obtain ⟨ s, hs ⟩ := hn
            exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ S, by
            rw [ SimpleGraph.isNClique_iff ]
            exact ⟨ by aesop_cat, by aesop_cat ⟩ ⟩);
      generalize_proofs at *; (
      exact h_clique_G _ fun u hu v hv huv => by aesop;))
    generalize_proofs at *; (
    rwa [ Finset.card_image_of_injOn ] at h_clique_G
    intro a ha b hb
    cases hS a ha
    cases hS b hb
    aesop ( simp_config := { singlePass := true } ) ;)))

/-
The clique number of G'' plus 1 is at most the clique number of G.
-/
omit [Fintype V] [DecidableEq V] in
lemma cliqueNum_G_double_prime_le [Finite V] :
  (G_double_prime G v0).cliqueNum + 1 ≤ G.cliqueNum := by
    classical
    letI := Fintype.ofFinite V
    simp +decide [ SimpleGraph.cliqueNum ];
    refine (le_csSup (α := ℕ) ?_ ?_);
    · exact ⟨ Fintype.card V, fun n hn => by
        rcases hn with ⟨ s, hs ⟩
        exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
    · -- Let $K$ be a clique in $G''$ with size equal to the clique number of $G''$.
      obtain ⟨K, hK⟩ :
          ∃ K : Finset (↥(V_double_prime G v0)),
            (G_double_prime G v0).IsNClique
              (sSup {n | ∃ s, (G_double_prime G v0).IsNClique n s}) K := by
        have := Nat.sSup_mem
          (show
            { n : ℕ | ∃ s : Finset (↥(V_double_prime G v0)),
              (G_double_prime G v0).IsNClique n s }.Nonempty from ?_);
        · exact this ⟨ _, fun n hn => hn.choose_spec.card_eq.symm ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
      -- Let $K'$ be the set of vertices in $G$ corresponding to the vertices in $K$.
      obtain ⟨K', hK'⟩ :
          ∃ K' : Finset V,
            K'.card = K.card ∧
              ∀ x ∈ K', x ≠ v0 ∧ G.Adj x v0 ∧ ∀ y ∈ K', y ≠ x → G.Adj x y := by
        use K.image (fun x => x.val.val);
        rw [ Finset.card_image_of_injective ];
        · simp_all +decide [ SimpleGraph.isNClique_iff ];
          intro x hx₁ hx₂ hx₃; have := hK.1 hx₃; aesop;
        · aesop_cat;
      refine ⟨ Insert.insert v0 K', ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · exact ⟨ fun x hx y hy hxy =>
            hK'.2 x hx |>.2.2 y hy ( Ne.symm hxy ),
          fun x hx hx' => hK'.2 x hx |>.2.1.symm ⟩;
      · grind

/-
If a clique contains a type A vertex and a type B vertex, the type B vertex must be
in the subset S associated with the type A vertex.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma clique_case_one_A_subset_S
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (v : V) (S : X_type G v0 H') (T : J_type V W)
  (hv : Sum.inl (v, S, T) ∈ Q)
  (w : W) (i : I_type V W)
  (hw : Sum.inr (w, i) ∈ Q) :
  w ∈ S.val := by
    classical
    have := hQ hv hw; simp_all +decide [ GraphH ] ;
    exact this.1

/-
The type B vertices in a clique containing a specific type A vertex correspond to a
clique in H' that is contained in S.
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
        obtain ⟨w0, i0, hw0⟩ :
            ∃ w0 i0, ∃ y ∈ Q, y = Sum.inr (w0, i0) ∧
              ∀ y ∈ Q, (∃ w i, y = Sum.inr (w, i)) →
                ∃ w i, y = Sum.inr (w, i) ∧ i = i0 := by
          obtain ⟨ y, hy, w, i, rfl ⟩ := hQB;
          refine ⟨ w, i, Sum.inr (w, i), hy, rfl, fun y hy' hy'' => ?_ ⟩;
          rcases hy'' with ⟨ w', i', rfl ⟩
          have := hQ hy hy'
          simp_all +decide [ SimpleGraph.IsClique ]
          unfold GraphH at this; simp_all +decide
          unfold AdjH at this; simp_all +decide
          grind;
        -- Let $W_B = \{ w \mid (w, i_0) \in Q_B \}$.
        obtain ⟨W_B, hW_B⟩ :
            ∃ W_B : Finset W,
              W_B.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card ∧
                ∀ w ∈ W_B, ∃ y ∈ Q, y = Sum.inr (w, i0) ∧ w ∈ S.val := by
          have hW_B :
              ∀ y ∈ Q, (∃ w i, y = Sum.inr (w, i)) →
                ∃ w, y = Sum.inr (w, i0) ∧ w ∈ S.val := by
            intros y hy hyB
            obtain ⟨w, i, hy_eq, hi⟩ : ∃ w i, y = Sum.inr (w, i) ∧ i = i0 := by
              exact hw0.choose_spec.2.2 y hy hyB;
            have := clique_case_one_A_subset_S G v0 H' Q hQ v S T hv w i0; aesop;
          choose! f hf1 hf2 using hW_B;
          let QB : Finset (VertexH G v0 H') := Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))
          use Finset.image
            (fun y : QB =>
              f y.val (Finset.mem_filter.mp y.property).1 (Finset.mem_filter.mp y.property).2)
            Finset.univ
          constructor
          · have hinj :
                Function.Injective
                  (fun y : QB =>
                    f y.val
                      (Finset.mem_filter.mp y.property).1
                      (Finset.mem_filter.mp y.property).2) := by
              intro x y hxy
              apply Subtype.ext
              have hxQ := (Finset.mem_filter.mp x.property).1
              have hxB := (Finset.mem_filter.mp x.property).2
              have hyQ := (Finset.mem_filter.mp y.property).1
              have hyB := (Finset.mem_filter.mp y.property).2
              have hxy' :
                  (Sum.inr (f x.val hxQ hxB, i0) : VertexH G v0 H') =
                    Sum.inr (f y.val hyQ hyB, i0) := by
                exact congrArg (fun w : W => (Sum.inr (w, i0) : VertexH G v0 H')) hxy
              exact (hf1 x.val hxQ hxB).trans
                (hxy'.trans (hf1 y.val hyQ hyB).symm)
            rw [Finset.card_image_of_injective _ hinj]
            rw [Finset.card_univ, Fintype.card_coe]
            rfl
          · intro w hw
            rcases Finset.mem_image.mp hw with ⟨y, _hy, rfl⟩
            exact ⟨y.val, (Finset.mem_filter.mp y.property).1,
              hf1 y.val (Finset.mem_filter.mp y.property).1 (Finset.mem_filter.mp y.property).2,
              hf2 y.val (Finset.mem_filter.mp y.property).1 (Finset.mem_filter.mp y.property).2⟩
        refine ⟨ W_B, hW_B.1, ?_, ?_ ⟩ <;> simp_all +decide [ SimpleGraph.IsClique ];
        intro w hw w' hw' hne
        have := hQ (hW_B.2 w hw |>.1) (hW_B.2 w' hw' |>.1)
        simp_all +decide
        unfold GraphH at this; simp_all +decide
        unfold AdjH at this; simp_all +decide
        grind;
      · refine ⟨ ∅, ?_, ?_, ?_ ⟩
        · have hfilter_empty : Q.filter (fun y => ∃ w i, y = Sum.inr (w, i)) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro y hy
            rcases Finset.mem_filter.mp hy with ⟨hyQ, hyB⟩
            exact hQB ⟨y, hyQ, hyB⟩
          simp [hfilter_empty]
        · simp [SimpleGraph.IsClique]
        · simp

/-
If a clique is contained in a subset of vertices, its size is at most the clique number
of the induced subgraph on that subset.
-/
lemma clique_subset_le_cliqueNum_induce
  {V : Type*} [Finite V]
  (G : SimpleGraph V) (S : Set V) [Finite S]
  (C : Finset V) (hC : G.IsClique C) (hCS : ∀ v ∈ C, v ∈ S) :
  C.card ≤ (G.induce S).cliqueNum := by
    classical
    letI := Fintype.ofFinite V
    letI := Fintype.ofFinite S
    refine le_csSup ?_ ?_;
    · exact ⟨ _, fun n hn => by
        rcases hn with ⟨ s, hs ⟩
        exact hs.card_eq.symm ▸ Finset.card_le_univ _ ⟩;
    · use Finset.filter (fun v => v.val ∈ C) (Finset.univ : Finset S);
      constructor;
      · intro x hx y hy hxy
        specialize hC (by aesop : (x : V) ∈ C) (by aesop : (y : V) ∈ C)
        aesop;
      · refine Finset.card_bij ( fun v hv => v ) ?_ ?_ ?_ <;> aesop

/-
If a clique contains exactly one type A vertex, its size is at most the clique number of G'' plus 1.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma clique_case_one_A
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (x : VertexH G v0 H')
  (hx : x ∈ Q)
  (hx_A : ∃ a, x = Sum.inl a)
  (h_unique : ∀ y ∈ Q, (∃ b, y = Sum.inl b) → y = x) :
  Q.card ≤ (G_double_prime G v0).cliqueNum + 1 := by
    classical
    obtain ⟨v, S, T, hv⟩ :
        ∃ v : V, ∃ S : X_type G v0 H', ∃ T : J_type V W,
          x = Sum.inl (v, S, T) := by
      bound;
    -- By `clique_case_one_A_type_B_is_clique_in_S`, there exists `W_B ⊆ W`
    -- such that `|W_B| = |Q_B|`, `W_B` is a clique in `H'`, and `W_B ⊆ S`.
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
    have h_cliqueNum_H'_induce_S :
        (H'.induce S.val).cliqueNum = (G_double_prime G v0).cliqueNum := by
      obtain ⟨ f, hf ⟩ := S.2;
      refine le_antisymm ?_ ?_ <;> simp +decide [ SimpleGraph.cliqueNum ];
      · refine csSup_le ?_ ?_ <;> norm_num +zetaDelta at *;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · intro b x hx
          obtain ⟨hx_card, hx_clique⟩ := hx
          have h_image_clique :
              (G_double_prime G v0).IsNClique b (Finset.image (fun y => f y) x) := by
            constructor <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
            intro y hy z hz
            obtain ⟨ a, ha, rfl ⟩ := hy
            obtain ⟨ b, hb, rfl ⟩ := hz
            specialize hx_card ha hb
            aesop;
          exact le_csSup (by
          exact ⟨ Fintype.card ( V_double_prime G v0 ), fun n hn => by
            obtain ⟨ s, hs ⟩ := hn
            exact hs.card_eq ▸ Finset.card_le_univ _ ⟩) ⟨_, h_image_clique⟩
      · refine csSup_le ?_ ?_ <;> norm_num +zetaDelta at *;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · intro b x hx; refine le_csSup ?_ ?_ <;> norm_num +zetaDelta at *;
          · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
          · refine ⟨ Finset.image ( fun y => ⟨ f.symm y |>.1, f.symm y |>.2 ⟩ ) x, ?_ ⟩;
            simp +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff ] at hx ⊢;
            simp +decide [ Set.Pairwise, Finset.card_image_of_injective, Function.Injective, hx.2 ];
            exact fun a ha ha' b hb hb' hab => hf a ha b hb |>.1 ( hx.1 ha' hb' ( by aesop ) );
    -- Since `Q` contains exactly one type A vertex (which is `x`), `|Q| = |Q_B| + 1`.
    have hQ_card : Q.card = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card + 1 := by
      have hA_single : Q.filter (fun y => ∃ a, y = Sum.inl a) = {x} := by
        exact Finset.eq_singleton_iff_unique_mem.mpr
          ⟨Finset.mem_filter.mpr ⟨hx, hx_A⟩,
            fun y hy => h_unique y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2⟩
      have hnotA_eq_B :
          Q.filter (fun y => ¬ ∃ a, y = Sum.inl a) =
            Q.filter (fun y => ∃ w i, y = Sum.inr (w, i)) := by
        ext y
        constructor
        · intro hy
          rcases Finset.mem_filter.mp hy with ⟨hyQ, hnotA⟩
          refine Finset.mem_filter.mpr ⟨hyQ, ?_⟩
          rcases y with a | ⟨w, i⟩
          · exact False.elim (hnotA ⟨a, rfl⟩)
          · exact ⟨w, i, rfl⟩
        · intro hy
          rcases Finset.mem_filter.mp hy with ⟨hyQ, hB⟩
          refine Finset.mem_filter.mpr ⟨hyQ, ?_⟩
          intro hA
          rcases hA with ⟨a, ha⟩
          rcases hB with ⟨w, i, hB⟩
          cases ha
          cases hB
      have hsplit :
          (Q.filter (fun y => ∃ a, y = Sum.inl a)).card +
            (Q.filter (fun y => ¬ ∃ a, y = Sum.inl a)).card = Q.card :=
        Finset.card_filter_add_card_filter_not (s := Q) (p := fun y => ∃ a, y = Sum.inl a)
      rw [← hsplit, hA_single, hnotA_eq_B]
      have hxcard : ({x} : Finset (VertexH G v0 H')).card = 1 := by simp
      calc
        ({x} : Finset (VertexH G v0 H')).card +
            (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card
            = 1 + (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card := by
              rw [hxcard]
        _ = (Q.filter (fun y => ∃ w i, y = Sum.inr (w, i))).card + 1 := Nat.add_comm 1 _
    rw [hQ_card, ← hW_B_card, ← h_cliqueNum_H'_induce_S]
    exact Nat.add_le_add_right hW_B_le_cliqueNum_induce 1

/-
If a clique contains no type A vertices, its size is at most the clique number of H'.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma clique_case_zero_A
  (Q : Finset (VertexH G v0 H'))
  (hQ : (GraphH G v0 H').IsClique Q)
  (h_no_A : ∀ x ∈ Q, ∀ a, x ≠ Sum.inl a) :
  Q.card ≤ H'.cliqueNum := by
    classical
    -- Since there are no type A vertices in Q, all vertices in Q must be of type B.
    have h_all_B : ∀ x ∈ Q, ∃ w i, x = Sum.inr (w, i) := by
      intro x hx; specialize h_no_A x hx; rcases x with ( ⟨ v, S, T ⟩ | ⟨ w, i ⟩ ) <;> tauto;
    -- Since all vertices in Q are of type B, they must lie in the same fiber.
    -- Let's denote this fiber by i.
    obtain ⟨i, hi⟩ : ∃ i : I_type V W, ∀ x ∈ Q, ∃ w, x = Sum.inr (w, i) := by
      rcases Q.eq_empty_or_nonempty with ( rfl | ⟨ x, hx ⟩ ) <;>
        simp_all +decide [ SimpleGraph.IsClique ];
      · exact ⟨ 0, Nat.zero_lt_succ _ ⟩;
      · obtain ⟨ w, i, rfl ⟩ := h_all_B x hx
        use i
        intro y hy
        obtain ⟨ w', i', rfl ⟩ := h_all_B y hy
        have := hQ hx hy
        simp_all +decide [ GraphH ] ;
        by_cases hi : i = i' <;> simp_all +decide [ AdjH ];
        · exact ⟨ w', rfl ⟩;
        · cases this ; tauto;
    choose f hf using hi;
    -- Since $f$ is a bijection between $Q$ and a subset of $W$, and $Q$ is a
    -- clique in $H$, the image of $Q$ under $f$ is a clique in $H'$.
    have h_image_clique : (Finset.image (fun x => f x.1 x.2) (Q.attach)).card ≤ H'.cliqueNum := by
      have h_image_clique :
          ∀ x ∈ Q.attach, ∀ y ∈ Q.attach,
            x ≠ y → H'.Adj (f x.1 x.2) (f y.1 y.2) := by
        intro x hx y hy hxy
        have h_adj : (GraphH G v0 H').Adj (Sum.inr (f x.1 x.2, i)) (Sum.inr (f y.1 y.2, i)) := by
          have hx_eq : x.val = Sum.inr (f x.1 x.2, i) := hf x.1 x.2
          have hy_eq : y.val = Sum.inr (f y.1 y.2, i) := hf y.1 y.2
          have hxy_ne : x.val ≠ y.val := by
            intro h
            exact hxy (Subtype.ext h)
          have h_adj0 := hQ x.2 y.2 hxy_ne
          rw [hx_eq, hy_eq] at h_adj0
          exact h_adj0
        change i = i ∧ H'.Adj (f x.1 x.2) (f y.1 y.2) at h_adj
        exact h_adj.2
      refine le_csSup ?_ ?_;
      · exact ⟨ Fintype.card W, fun n hn => by
          obtain ⟨ s, hs ⟩ := hn
          exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
      · refine ⟨ Finset.image ( fun x : { x // x ∈ Q } => f x.1 x.2 ) Q.attach, ?_, ?_ ⟩;
        · intro x hx y hy hxy;
          grind;
        · convert rfl;
    rwa [ Finset.card_image_of_injOn, Finset.card_attach ] at h_image_clique;
    intro x hx y hy; have := hf x.1 x.2; have := hf y.1 y.2; simp +decide at *;
    grind

/-
The clique number of H(2,G) is at most the clique number of G.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma GraphH_cliqueNum_le
  (h_clique : H'.cliqueNum = (G_prime G v0).cliqueNum) :
  (GraphH G v0 H').cliqueNum ≤ G.cliqueNum := by
    classical
    -- Let $Q$ be a clique in $H(2,G)$. We show that $|Q| \le G.cliqueNum$ by
    -- considering the cases with at least two, exactly one, or no type A vertices.
    have h_clique_size :
        ∀ Q : Finset (VertexH G v0 H'),
          (GraphH G v0 H').IsClique Q → Q.card ≤ G.cliqueNum := by
      intro Q hQ
      generalize_proofs at *;
      by_cases h_two_A :
          ∃ x y : VertexH G v0 H',
            x ∈ Q ∧ y ∈ Q ∧ x ≠ y ∧
              (∃ a, x = Sum.inl a) ∧ (∃ b, y = Sum.inl b);
      · obtain ⟨ x, y, hx, hy, hxy, ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩ := h_two_A
        exact clique_case_two_A G v0 H' Q hQ _ _ hx hy hxy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ;
      · by_cases h_one_A :
            ∃ x : VertexH G v0 H',
              x ∈ Q ∧ (∃ a, x = Sum.inl a) ∧
                ∀ y ∈ Q, (∃ b, y = Sum.inl b) → y = x;
        · obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_one_A
          have h_card : Q.card ≤ (G_double_prime G v0).cliqueNum + 1 := by
            apply clique_case_one_A G v0 H' Q hQ x hx₁ hx₂ hx₃
          have h_card_le : (G_double_prime G v0).cliqueNum + 1 ≤ G.cliqueNum := by
            exact cliqueNum_G_double_prime_le G v0
          linarith [h_card, h_card_le];
        · by_cases h_no_A : ∀ x ∈ Q, ∀ a, x ≠ Sum.inl a;
          · refine le_trans ( clique_case_zero_A G v0 H' Q hQ h_no_A ) ?_;
            rw [ h_clique ];
            refine csSup_le ?_ ?_ <;> norm_num +zetaDelta at *;
            · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
            · intro b x hx
              have h_induce :
                  (G_prime G v0).IsNClique b x →
                    G.IsNClique b (Finset.image (fun v => v.val) x) := by
                intro hx
                have h_induce :
                    ∀ u v : V_prime v0,
                      u ∈ x → v ∈ x → u ≠ v → G.Adj u.val v.val := by
                  exact fun u v hu hv huv =>
                    hx.1 hu hv (by simpa [ Subtype.ext_iff ] using huv) |> fun h =>
                      by simpa [ Subtype.ext_iff ] using h;
                generalize_proofs at *;
                simp_all +decide [ SimpleGraph.isNClique_iff ];
                simp_all +decide [
                  SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
                intro a ha b hb hab; aesop;
              generalize_proofs at *;
              exact le_csSup
                ⟨ Fintype.card V, fun n hn => by
                  obtain ⟨ y, hy ⟩ := hn
                  exact hy.card_eq ▸ Finset.card_le_univ _ ⟩
                ⟨ _, h_induce hx ⟩;
          · grind
    generalize_proofs at *;
    exact csSup_le' fun n hn => by
      obtain ⟨ s, hs ⟩ := hn
      simpa [ hs.2 ] using h_clique_size s hs.1;

/-
The clique number of H(2,G) is equal to the clique number of G.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma GraphH_cliqueNum_eq
  (h_ramsey : VertexPartitionRamsey 2 H' (G_prime G v0))
  (h_clique : H'.cliqueNum = (G_prime G v0).cliqueNum) :
  (GraphH G v0 H').cliqueNum = G.cliqueNum := by
    classical
    refine le_antisymm ?_ ?_;
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
omit [DecidableEq V] [DecidableEq W] in
lemma exists_uniform_subset
  (f : VertexH G v0 H' → Fin 2) :
  ∃ (T : J_type V W), is_uniform G v0 H' f T.val := by
    classical
    -- By the pigeonhole principle, since there are $(r-1)t + 1$ indices and only
    -- $t$ possible functions $c_i$, some function $c : W \to \text{Fin } 2$
    -- occurs for at least $r$ indices.
    obtain ⟨c, hc⟩ :
        ∃ c : W → Fin 2,
          (Finset.card
            (Finset.filter (fun i => induced_partition G v0 H' f i = c)
              Finset.univ)) ≥ r_param V := by
      have h_pigeonhole :
          (Finset.univ : Finset (I_type V W)).card =
            (r_param V - 1) * t_param W + 1 := by
        simp +decide [ r_param, t_param, I_type ];
        rfl;
      by_contra h_contra;
      have h_card :
          (Finset.univ : Finset (I_type V W)).card =
            Finset.sum (Finset.univ : Finset (W → Fin 2)) fun c =>
              (Finset.filter (fun i => induced_partition G v0 H' f i = c)
                Finset.univ).card := by
        simp +decide only [Finset.card_eq_sum_ones, Finset.sum_fiberwise];
      refine h_pigeonhole.not_lt
        (h_card.symm ▸
          lt_of_le_of_lt
            (Finset.sum_le_sum fun c _ =>
              Nat.le_sub_one_of_lt (lt_of_not_ge fun h => h_contra ⟨ c, h ⟩)) ?_);
      simp +decide [ mul_comm, t_param ];
    obtain ⟨ T, hT ⟩ := Finset.exists_subset_card_eq hc;
    exact ⟨ ⟨ T, hT.2 ⟩, c, fun i hi => Finset.mem_filter.mp ( hT.1 hi ) |>.2 ⟩

/-
The map psi maps v0 to the type A vertex (v1, S'', T) and other vertices v to
type B vertices (phi(v), i_star).
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
omit [DecidableEq W] in
lemma psi_map_injective
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V)
  (i_star : I_type V W) :
  Function.Injective (psi_map G v0 H' T S' phi S'' v1 i_star) := by
    classical
    intro x y hxy
    simp [psi_map] at hxy
    cases eq_or_ne x v0 with
    | inl hx =>
      cases eq_or_ne y v0 with
      | inl hy => simp_all +decide
      | inr hy => simp_all +decide
    | inr hx =>
      cases eq_or_ne y v0 with
      | inl hy => simp_all +decide
      | inr hy =>
        simp_all +decide
        have := phi.injective ( Subtype.ext ( by injection hxy with h; aesop ) )
        aesop

/-
The map psi preserves adjacency between G and H.
-/
omit [DecidableEq W] in
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
  G.Adj u v ↔
    (GraphH G v0 H').Adj
      (psi_map G v0 H' T S' phi S'' v1 i_star u)
      (psi_map G v0 H' T S' phi S'' v1 i_star v) := by
    classical
    by_cases hu : u = v0 <;> by_cases hv : v = v0 <;> simp +decide [ *, psi_map ];
    · unfold GraphH; simp +decide [ * ] ;
      unfold AdjH; simp +decide [ * ] ;
      exact ⟨ fun h => h.symm, fun h => h.symm ⟩;
    · simp +decide [ ← h_i_star_map, GraphH ];
      unfold AdjH; aesop;
    · unfold GraphH; simp +decide [ *, AdjH ] ;
      convert h_phi_iso ⟨ u, hu ⟩ ⟨ v, hv ⟩ using 1

/-
Helper definitions for extracting the index $i^*$ corresponding to a vertex $v$
under the bijection $f_T$.
-/

noncomputable def get_i_star (T : J_type V W) (v : V) : I_type V W :=
  ((f_map V W T).symm v).val

omit [DecidableEq V] [DecidableEq W] in
lemma get_i_star_mem (T : J_type V W) (v : V) : get_i_star T v ∈ T.val := by
  classical
  exact ( Equiv.symm ( f_map V W T ) ) v |>.2

omit [DecidableEq V] [DecidableEq W] in
lemma f_map_get_i_star (T : J_type V W) (v : V) :
  f_map_val T (get_i_star T v) (get_i_star_mem T v) = v := by
    classical
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
omit [DecidableEq W] in
lemma psi_map_case_1_preserves_adj
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (h_phi_iso : ∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val)
  (S'' : X_type G v0 H')
  (h_S''_eq : S''.val = Subtype.val '' (phi '' (V_double_prime G v0)))
  (v1 : V)
  (u v : V) :
  G.Adj u v ↔
    (GraphH G v0 H').Adj
      (psi_map_case_1 G v0 H' T S' phi S'' v1 u)
      (psi_map_case_1 G v0 H' T S' phi S'' v1 v) := by
    classical
    convert psi_map_preserves_adj G v0 H' T S' phi h_phi_iso S'' h_S''_eq v1
      (get_i_star T v1) (get_i_star_mem T v1) (f_map_get_i_star T v1) u v using 1

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
omit [DecidableEq W] in
lemma psi_map_case_1_injective
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (S'' : X_type G v0 H')
  (v1 : V) :
  Function.Injective (psi_map_case_1 G v0 H' T S' phi S'' v1) := by
    classical
    convert psi_map_injective G v0 H' T S' phi S'' v1 _ using 1

/-
All vertices in the set $U$ constructed for Case 1 have color $k$.
-/
omit [DecidableEq W] in
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
    classical
    obtain ⟨ v, rfl ⟩ := Set.mem_range.mp hx;
    by_cases h : v = v0 <;> simp_all +decide [ psi_map_case_1 ];
    · unfold psi_map; aesop;
    · convert h_S'_mono ( phi ⟨ v, h ⟩ ) ( phi ⟨ v, h ⟩ |>.2 ) using 1;
      convert congr_fun (h_uniform (get_i_star T v1) (get_i_star_mem T v1))
        (phi ⟨ v, h ⟩) using 1;
      unfold psi_map; aesop;

/-
The map `psi_map_case_1` induces an isomorphism between $G$ and the induced subgraph
on its range $U$.
-/
omit [DecidableEq W] in
lemma psi_map_case_1_is_iso
  (T : J_type V W)
  (S' : Set W)
  (phi : V_prime v0 ≃ S')
  (h_phi_iso : ∀ x y : V_prime v0, (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val)
  (S'' : X_type G v0 H')
  (h_S''_eq : S''.val = Subtype.val '' (phi '' (V_double_prime G v0)))
  (v1 : V) :
  Nonempty (G ≃g (GraphH G v0 H').induce (U_case_1 G v0 H' T S' phi S'' v1)) := by
    classical
    refine ⟨ ?_ ⟩;
    refine
      { toEquiv := Equiv.ofBijective
          (fun x => ⟨ psi_map_case_1 G v0 H' T S' phi S'' v1 x, ⟨ x, rfl ⟩ ⟩)
          ⟨ ?_, ?_ ⟩
        map_rel_iff' := ?_ };
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
The map `psi_map_case_2` induces an isomorphism between $G$ and the induced subgraph
on its range $U$.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma psi_map_case_2_is_iso
  (S'' : X_type G v0 H')
  (T : J_type V W) :
  Nonempty (G ≃g (GraphH G v0 H').induce (U_case_2 G v0 H' S'' T)) := by
    classical
    refine ⟨
      { toEquiv := Equiv.ofBijective
          (fun v => ⟨ Sum.inl (v, S'', T), ⟨ v, rfl ⟩ ⟩)
          ⟨ ?_, ?_ ⟩
        map_rel_iff' := ?_ } ⟩
    · intro v w h
      norm_num [ U_case_2 ] at *
      grind +ring
    · intro x
      rcases x with ⟨ x, hx ⟩
      rcases hx with ⟨ v, rfl ⟩
      exact ⟨ v, rfl ⟩
    · intro a b
      constructor
      · exact fun h => by cases h; tauto
      · exact fun h => ⟨ rfl, rfl, h ⟩

/-
Case 1 of the Ramsey proof: if we find a vertex $v_1$ of the same color as the
monochromatic set $S'$, we construct a monochromatic copy of $G$.
-/
omit [DecidableEq V] [DecidableEq W] in
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
  ∃ (U : Set (VertexH G v0 H')),
    (∀ x ∈ U, f x = k) ∧ Nonempty (G ≃g (GraphH G v0 H').induce U) := by
    classical
    refine ⟨ ?_, ?_, ?_ ⟩;
    focus
      exact Set.range ( psi_map_case_1 G v0 H' T S' phi S'' v1 );
    · exact fun x a =>
      U_case_1_monochromatic G v0 H' f T k c h_uniform S' h_S'_mono phi S'' v1 h_v1_color x a;
    · apply_rules [ psi_map_case_1_is_iso ]

/-
The graph $H(2,G)$ satisfies the vertex-partition Ramsey property for $G$ with 2 colors.
-/
omit [DecidableEq V] [DecidableEq W] in
lemma GraphH_ramsey_2
  (h_ramsey : VertexPartitionRamsey 2 H' (G_prime G v0)) :
  VertexPartitionRamsey 2 (GraphH G v0 H') G := by
    classical
    revert h_ramsey;
    intro h_ramsey f;
    -- By `exists_uniform_subset`, there exists $T \in J$ such that the induced
    -- partition on $W$ agrees with $c$ for all $i \in T$.
    obtain ⟨T, c, h_uniform⟩ :
        ∃ T : J_type V W, ∃ c : W → Fin 2,
          ∀ i ∈ T.val, induced_partition G v0 H' f i = c := by
      exact Exists.elim ( exists_uniform_subset G v0 H' f ) fun T hT =>
        ⟨ T, hT.choose, fun i hi => hT.choose_spec i hi ⟩;
    -- Since $H' \Rightarrow_2 G'`, there exists a monochromatic copy of $G'$ in
    -- $H'$ under the coloring $c$.
    obtain ⟨k, S', phi, h_phi_iso, h_S'_mono⟩ :
        ∃ k : Fin 2, ∃ S' : Set W, ∃ phi : V_prime v0 ≃ S',
          (∀ w ∈ S', c w = k) ∧
            (∀ x y : V_prime v0,
              (G_prime G v0).Adj x y ↔ H'.Adj (phi x).val (phi y).val) := by
      have := h_ramsey c;
      obtain ⟨ k, S, hS, ⟨ phi ⟩ ⟩ := this;
      refine ⟨ k, S, ?_, hS, ?_ ⟩;
      · exact phi.toEquiv;
      · exact fun x y => phi.map_adj_iff.symm;
    -- Define $S''$ as the image of $V''$ under $\phi`. It is in `X` because
    -- $H'[S''] \cong G''$.
    obtain ⟨S'', h_S''_eq⟩ :
        ∃ S'' : X_type G v0 H',
          S''.val = Subtype.val '' (phi '' (V_double_prime G v0)) := by
      have h_iso :
          Nonempty
            ((H'.induce (Subtype.val '' (phi '' (V_double_prime G v0)))) ≃g
              (G_double_prime G v0)) := by
        refine ⟨ ?_, ?_ ⟩;
        focus
          refine Equiv.ofBijective ( fun x => ⟨ phi.symm ⟨ x.val, ?_ ⟩, ?_ ⟩ ) ⟨ ?_, ?_ ⟩;
          focus
            grind;
          all_goals norm_num [ Function.Injective, Function.Surjective ];
          all_goals norm_num [ V_double_prime, G_double_prime ];
          · rcases x with ⟨ x, ⟨ y, ⟨ z, hz, rfl ⟩, rfl ⟩ ⟩
            aesop
          · intro a ha h
            use phi ⟨ a, ha ⟩
            aesop
        intro a b
        rcases a with ⟨a, ha⟩
        rcases b with ⟨b, hb⟩
        have haS : a ∈ S' := by
          rcases ha with ⟨a', -, rfl⟩
          exact a'.property
        have hbS : b ∈ S' := by
          rcases hb with ⟨b', -, rfl⟩
          exact b'.property
        simpa [G_prime, G_double_prime] using
          (h_S'_mono (phi.symm ⟨a, haS⟩) (phi.symm ⟨b, hbS⟩))
      exact ⟨ ⟨ _, h_iso ⟩, rfl ⟩;
    -- Consider the vertices $(v, S'', T)$ for $v \in V$.
    -- Case 1: There exists $v_1 \in V$ such that $f(v_1, S'', T) = k$.
    by_cases h_case1 : ∃ v1 : V, f (Sum.inl (v1, S'', T)) = k;
    · obtain ⟨ v1, hv1 ⟩ := h_case1;
      exact GraphH_ramsey_2_case_1 G v0 H' f T k c h_uniform S' h_phi_iso phi
        h_S'_mono S'' h_S''_eq v1 hv1 |>
          fun ⟨ U, hU₁, hU₂ ⟩ => ⟨ k, U, hU₁, hU₂ ⟩;
    · -- Since there are only 2 colors, this means $f(v, S'', T) = 1-k$ for all $v \in V$.
      have h_case2 : ∀ v : V, f (Sum.inl (v, S'', T)) = 1 - k := by
        grind;
      exact ⟨ 1 - k, U_case_2 G v0 H' S'' T, fun x hx => by
        obtain ⟨ v, rfl ⟩ := hx
        exact h_case2 v, psi_map_case_2_is_iso G v0 H' S'' T ⟩

/-
The inductive hypothesis for the existence of $H(2,G)$.
-/
def PropH2 (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    Fintype.card V = n →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey 2 H G

/-
Base case of the induction: for any graph $G$ with 1 vertex, $H=G$ satisfies the
required properties.
-/
lemma PropH2_base : PropH2 1 := by
  intro V _ _ G hV;
  refine ⟨ V, inferInstance, inferInstance, G, ?_, ?_ ⟩;
  · rfl;
  · -- Since V has only one vertex, the only possible partition is {v} and the
    -- empty set. The empty set cannot contain G, but {v} does.
    obtain ⟨v, hv⟩ : ∃ v : V, ∀ w : V, w = v := by
      rw [ Fintype.card_eq_one_iff ] at hV; tauto;
    intro f;
    use f v, {v};
    refine ⟨ by aesop, ⟨ ?_, ?_, ?_ ⟩ ⟩;
    focus
      exact (Equiv.subtypeUnivEquiv hv).symm;
    · exact fun a => a;
    · aesop

/-
Inductive step for the existence of $H(2,G)$: if the property holds for graphs of
size $n-1$, it holds for graphs of size $n$.
-/
lemma PropH2_step (n : ℕ) (hn : n > 1) (IH : PropH2 (n - 1)) : PropH2 n := by
  intro V hV hV' G hG;
  -- By the induction hypothesis, there exists a graph $H'$ such that
  -- $\omega(H') = \omega(G')$ and $H' \Rightarrow_2 G'$.
  obtain ⟨W', hW', hW'_eq, H', hH'_clique, hH'_ramsey⟩ :
      ∃ (W' : Type) (_ : Fintype W') (_ : DecidableEq W') (H' : SimpleGraph W'),
        (H'.cliqueNum =
          (G_prime G
            (Classical.choose
              (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))).cliqueNum) ∧
        (VertexPartitionRamsey 2 H'
          (G_prime G
            (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V))))) := by
      have h_card_V' :
          Fintype.card
            (V_prime
              (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))) =
            n - 1 := by
        have hv0 :
            Fintype.card
              (V_prime
                (Classical.choose (Finset.card_pos.mp
                  (by linarith : 0 < Fintype.card V)))) =
            Fintype.card V - 1 := by
          change
            Fintype.card
              {x : V // x ∈ V_prime
                (Classical.choose (Finset.card_pos.mp
                  (by linarith : 0 < Fintype.card V)))} =
              Fintype.card V - 1
          simp only [V_prime, Set.mem_setOf_eq]
          simp [ne_eq]
        exact hv0.trans (by rw [hG])
      specialize IH
        (V_prime
          (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V))))
      aesop;
  use VertexH G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))
      H',
    by infer_instance,
    by infer_instance,
    GraphH G (Classical.choose (Finset.card_pos.mp (by linarith : 0 < Fintype.card V)))
      H';
  exact ⟨ GraphH_cliqueNum_eq G _ H' hH'_ramsey hH'_clique, GraphH_ramsey_2 G _ H' hH'_ramsey ⟩

/-
Base case $n=0$ for the existence of $H(2,G)$.
-/
lemma PropH2_0 : PropH2 0 := by
  intro V _ _ G hG
  have h_emptyV : IsEmpty V := Fintype.card_eq_zero_iff.mp hG
  letI := h_emptyV
  refine ⟨ PEmpty, inferInstance, inferInstance, ⊥, ?_, ?_ ⟩
  · -- Since $V$ is empty, both clique numbers are zero.
    have h_empty : G.cliqueNum = 0 := by
      simp +decide [ SimpleGraph.cliqueNum ];
      rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;>
        norm_num [ SimpleGraph.isNClique_iff ];
      · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
      · exact fun a ha => Finset.eq_empty_of_forall_notMem fun x hx => isEmptyElim x
    rw [h_empty]
    apply le_antisymm
    · refine csSup_le' ?_
      rintro n ⟨s, hs⟩
      have hs_empty : s = ∅ := by
        ext x
        cases x
      have hs_card_zero : s.card = 0 := by simp [hs_empty]
      have hs_card_eq : s.card = n := hs.card_eq
      omega
    · exact Nat.zero_le _
  · intro f
    refine ⟨ 0, Set.univ, ?_, ?_ ⟩
    · intro w hw
      cases w
    · refine ⟨ { toEquiv := Fintype.equivOfCardEq (by simp), map_rel_iff' := ?_ } ⟩
      intro a b
      exact False.elim (isEmptyElim a)

/-
For every graph $G$, there exists a graph $H$ such that $\omega(H) = \omega(G)$ and
$H \Rightarrow_2 G$.
-/
omit [Fintype V] [DecidableEq V] in
theorem exists_H_2 :
  ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey 2 H G := by
        classical
        have h_ind : ∀ n : ℕ, PropH2 n := by
          intro n
          induction n using Nat.strong_induction_on with
          | h n ih =>
            rcases n with ( _ | _ | n ) <;> simp_all +arith +decide
            · exact PropH2_0;
            · exact PropH2_base;
            · exact PropH2_step _
                (Nat.succ_lt_succ (Nat.succ_pos _)) (ih _ (Nat.le_refl _));
        exact fun V [Finite V] G => by
          classical
          letI := Fintype.ofFinite V
          exact h_ind (Fintype.card V) V G rfl

/-
For every graph $G$ and integer $n \ge 1$, there exists a graph $H(n,G)$ with the
same clique number such that $H(n,G) \Rightarrow_n G$.
-/
omit [Fintype V] [DecidableEq V] in
theorem exists_H_n :
  ∀ (n : ℕ) (hn : n ≥ 1) (V : Type) [Finite V] (G : SimpleGraph V),
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
      H.cliqueNum = G.cliqueNum ∧ VertexPartitionRamsey n H G := by
  classical
  intro n hn V _ G
  exact exists_H_n_of_exists_H_2 exists_H_2 n hn V G

/-
Definitions of the graphs $K_2$ and $2K_3$.
-/
def K2 : SimpleGraph (Fin 2) := completeGraph (Fin 2)

def TwoK3 : SimpleGraph (Fin 3 ⊕ Fin 3) :=
  SimpleGraph.sum (completeGraph (Fin 3)) (completeGraph (Fin 3))

/-
Construction of the graph $H_2$ and the parameter $N$.
-/
lemma H2_witness_proof : ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W),
    H.cliqueNum = K2.cliqueNum ∧ VertexPartitionRamsey 36 H K2 :=
  exists_H_n 36 (by norm_num) (Fin 2) K2

noncomputable def V2 : Type := Classical.choose H2_witness_proof

noncomputable instance : Fintype V2 := Classical.choose (Classical.choose_spec H2_witness_proof)
noncomputable instance : DecidableEq V2 :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec H2_witness_proof))

noncomputable def H2 : SimpleGraph V2 :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H2_witness_proof)))

lemma H2_props :
  H2.cliqueNum = K2.cliqueNum ∧ VertexPartitionRamsey 36 H2 K2 :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec H2_witness_proof)))

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
noncomputable instance : DecidableEq V1 :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec H1_witness_proof))

noncomputable def H1 : SimpleGraph V1 :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H1_witness_proof)))

lemma H1_props :
  H1.cliqueNum = TwoK3.cliqueNum ∧ VertexPartitionRamsey N_param H1 TwoK3 :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec H1_witness_proof)))

lemma TwoK3_cliqueNum_le_three : TwoK3.cliqueNum ≤ 3 := by
  refine csSup_le' ?_
  rintro n ⟨Q, hQ⟩
  rw [SimpleGraph.isNClique_iff] at hQ
  rw [← hQ.2]
  by_cases hQ_empty : Q = ∅
  · simp [hQ_empty]
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hQ_empty
  rcases x with i | i
  · have hsubset : Q ⊆ Finset.image (fun i : Fin 3 => (Sum.inl i : Fin 3 ⊕ Fin 3)) Finset.univ := by
      intro y hy
      rcases y with j | j
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      · have hne : (Sum.inl i : Fin 3 ⊕ Fin 3) ≠ Sum.inr j := by simp
        have hAdj := hQ.1 hx hy hne
        simp [TwoK3] at hAdj
    have hcard :
        (Finset.image (fun i : Fin 3 => (Sum.inl i : Fin 3 ⊕ Fin 3)) Finset.univ).card = 3 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro x y h
        exact Sum.inl.inj h
    exact le_trans (Finset.card_le_card hsubset) (by rw [hcard])
  · have hsubset : Q ⊆ Finset.image (fun i : Fin 3 => (Sum.inr i : Fin 3 ⊕ Fin 3)) Finset.univ := by
      intro y hy
      rcases y with j | j
      · have hne : (Sum.inr i : Fin 3 ⊕ Fin 3) ≠ Sum.inl j := by simp
        have hAdj := hQ.1 hx hy hne
        simp [TwoK3] at hAdj
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have hcard :
        (Finset.image (fun i : Fin 3 => (Sum.inr i : Fin 3 ⊕ Fin 3)) Finset.univ).card = 3 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro x y h
        exact Sum.inr.inj h
    exact le_trans (Finset.card_le_card hsubset) (by rw [hcard])

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
  | Sum.inr S, Sum.inl (u, _) => u ∈ S.val
  | Sum.inl (u, _), Sum.inr S => u ∈ S.val
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
  loopless := ⟨fun x h => by
    -- By definition of $AdjG`, no vertex is adjacent to itself.
    cases x <;> simp [AdjG] at h⟩

/-
If a clique contains two vertices in different rows, then all its grid vertices lie in
the same column.
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
                                  rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ] <;>
                                    norm_num [ SimpleGraph.isNClique_iff ];
                                  · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
                                  · exact fun a ha => Finset.card_le_univ _;
                                  · exact fun w hw =>
                                      ⟨ { 0, 1 }, by simp +decide,
                                        by interval_cases w <;> simp +decide ⟩ ) ] at *; );
      -- By definition of clique number, any clique in $H_2$ has size at most 2.
      have h_clique_num : ∀ (Q' : Finset V2), (H2.IsClique Q') → Q'.card ≤ H2.cliqueNum := by
        intro Q' hQ'; exact (by
        apply le_csSup (by
        exact ⟨ Fintype.card V2, fun n hn => by
          obtain ⟨ s, hs ⟩ := hn
          exact hs.card_eq ▸ Finset.card_le_univ _ ⟩) (by
        exact ⟨ Q', by simpa [ SimpleGraph.isNClique_iff ] using hQ' ⟩));
      exact fun Q' hQ' =>
        le_trans ( h_clique_num Q' hQ' ) ( by rw [ H2_props.1 ] ; exact this ▸ le_rfl );
    let Q' : Finset V2 := Finset.filter (fun v => Sum.inl (u, v) ∈ Q) Finset.univ
    have hQ_eq : Q = Finset.image (fun v => Sum.inl (u, v)) Q' := by
      ext x
      constructor
      · intro hx
        rcases h_subset x hx with ⟨v, rfl⟩
        exact Finset.mem_image.mpr ⟨v, by simpa [Q'], rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
        simpa [Q'] using hv
    have hQ'_clique : H2.IsClique Q' := by
      intro v hv w hw hvw
      have hvQ : Sum.inl (u, v) ∈ Q := by simpa [Q'] using hv
      have hwQ : Sum.inl (u, w) ∈ Q := by simpa [Q'] using hw
      have hne : (Sum.inl (u, v) : VertexG) ≠ Sum.inl (u, w) := by
        intro h
        exact hvw (congrArg Prod.snd (Sum.inl.inj h))
      have hAdj := hQ hvQ hwQ hne
      change (u = u ∧ H2.Adj v w) ∨ (v = w ∧ H1.Adj u u) at hAdj
      rcases hAdj with hrow | hcol
      · exact hrow.2
      · exact False.elim (hvw hcol.1)
    rw [hQ_eq]
    have hcard : (Finset.image (fun v => (Sum.inl (u, v) : VertexG)) Q').card = Q'.card := by
      rw [Finset.card_image_of_injective]
      intro v w h
      exact congrArg Prod.snd (Sum.inl.inj h)
    change (Finset.image (fun v => (Sum.inl (u, v) : VertexG)) Q').card ≤ 2
    rw [hcard]
    exact h_row_clique Q' hQ'_clique

/-
A clique contained in a single column of the grid has size at most 3.
-/
lemma clique_in_col_le_three
  (Q : Finset VertexG) (hQ : GraphG.IsClique Q)
  (v : V2)
  (h_subset : ∀ x ∈ Q, ∃ u, x = Sum.inl (u, v)) :
  Q.card ≤ 3 := by
    -- Let $Q' = \{u \in V1 \mid \exists w, \text{Sum.inl} (u, v) = w \land w \in Q\}$.
    let Q' : Finset V1 := Finset.filter (fun u => Sum.inl (u, v) ∈ Q) Finset.univ
    have hQ_eq_Q' : Q = Finset.image (fun u => Sum.inl (u, v)) Q' := by
      ext x
      constructor
      · intro hx
        rcases h_subset x hx with ⟨u, rfl⟩
        exact Finset.mem_image.mpr ⟨u, by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hx⟩, rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
        exact (Finset.mem_filter.mp hu).2
    -- Since $Q'$ is a clique in $H_1$, its size is at most the clique number of $H_1$, which is 3.
    have hQ'_clique : H1.IsClique Q' := by
      intro u hu u' hu' hne
      have huQ : Sum.inl (u, v) ∈ Q := (Finset.mem_filter.mp hu).2
      have hu'Q : Sum.inl (u', v) ∈ Q := (Finset.mem_filter.mp hu').2
      have hneG : (Sum.inl (u, v) : VertexG) ≠ Sum.inl (u', v) := by
        intro h
        exact hne (congrArg Prod.fst (Sum.inl.inj h))
      have hAdj := hQ huQ hu'Q hneG
      change (u = u' ∧ H2.Adj v v) ∨ (v = v ∧ H1.Adj u u') at hAdj
      rcases hAdj with hrow | hcol
      · exact False.elim (hne hrow.1)
      · exact hcol.2
    have hQ'_size : Q'.card ≤ 3 := by
      have hQ'_size : Q'.card ≤ H1.cliqueNum := by
        exact le_csSup
          (by
            exact ⟨Fintype.card V1, fun n hn => by
              obtain ⟨s, hs⟩ := hn
              exact hs.card_eq ▸ Finset.card_le_univ _⟩)
          (by
            exact ⟨Q', by simpa [SimpleGraph.isNClique_iff] using hQ'_clique⟩)
      exact le_trans hQ'_size (by rw [H1_props.1]; exact TwoK3_cliqueNum_le_three)
    rw [hQ_eq_Q']
    exact le_trans Finset.card_image_le hQ'_size

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
        exact clique_in_col_le_three Q hQ v fun x hx => by
          obtain ⟨ u'', v'', rfl, rfl ⟩ := h_col x hx
          exact ⟨ u'', rfl ⟩ ;
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
  obtain ⟨a, b, hne_ab, hSval⟩ : ∃ a b : V1, a ≠ b ∧ S.val = s(a, b) := by
    rcases S with ⟨e, he⟩
    rcases e with ⟨a, b⟩
    exact ⟨a, b, by simpa [Sym2.mk_isDiag_iff] using he, rfl⟩
  let R : Finset VertexG := Q \ {Sum.inr S}
  have hR_clique : GraphG.IsClique R := by
    intro x hx y hy hxy
    exact hQ (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
  have hR_rows : ∀ y ∈ R, ∃ u v, y = Sum.inl (u, v) ∧ (u = a ∨ u = b) := by
    intro y hy
    rcases y with ⟨u, v⟩ | S'
    · have hne : (Sum.inr S : VertexG) ≠ Sum.inl (u, v) := by simp
      have hAdj := hQ hS (Finset.mem_sdiff.mp hy).1 hne
      change u ∈ S.val at hAdj
      have hu : u ∈ s(a, b) := by simpa [hSval] using hAdj
      exact ⟨u, v, rfl, (Sym2.mem_iff.mp hu)⟩
    · have hne : (Sum.inr S : VertexG) ≠ Sum.inr S' := by
        intro h
        exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_singleton.mpr h.symm)
      have hAdj := hQ hS (Finset.mem_sdiff.mp hy).1 hne
      change False at hAdj
      exact False.elim hAdj
  have hQ_eq : Q = insert (Sum.inr S) R := by
    ext x
    constructor
    · intro hx
      by_cases hxS : x = Sum.inr S
      · exact Finset.mem_insert.mpr (Or.inl hxS)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, by
          intro hxmem
          exact hxS (Finset.mem_singleton.mp hxmem)⟩))
    · intro hx
      rcases Finset.mem_insert.mp hx with hxS | hxR
      · simpa [hxS] using hS
      · exact (Finset.mem_sdiff.mp hxR).1
  have hnotR : Sum.inr S ∉ R := by
    intro h
    exact (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self _)
  have hR_card : R.card ≤ 2 := by
    by_cases hA : ∃ y ∈ R, ∃ v, y = Sum.inl (a, v)
    · by_cases hB : ∃ y ∈ R, ∃ v, y = Sum.inl (b, v)
      · obtain ⟨ya, hya, va, hya_eq⟩ := hA
        obtain ⟨yb, hyb, vb, hyb_eq⟩ := hB
        have hyaQ : Sum.inl (a, va) ∈ Q := by
          simpa [hya_eq] using (Finset.mem_sdiff.mp hya).1
        have hybQ : Sum.inl (b, vb) ∈ Q := by
          simpa [hyb_eq] using (Finset.mem_sdiff.mp hyb).1
        have hcol := clique_grid_force_col Q hQ a b va vb hyaQ hybQ hne_ab
        have hR_subset : R ⊆ {Sum.inl (a, va), Sum.inl (b, va)} := by
          intro x hx
          obtain ⟨u, v, rfl, hu⟩ := hR_rows x hx
          have hv : v = va := hcol.2 u v (Finset.mem_sdiff.mp hx).1
          rcases hu with rfl | rfl
          · rw [hv]
            exact Finset.mem_insert_self _ _
          · rw [hv]
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
        exact le_trans (Finset.card_le_card hR_subset) (Finset.card_insert_le _ _)
      · have h_subset : ∀ x ∈ R, ∃ v, x = Sum.inl (a, v) := by
          intro x hx
          obtain ⟨u, v, rfl, hu⟩ := hR_rows x hx
          rcases hu with rfl | rfl
          · exact ⟨v, rfl⟩
          · exact False.elim (hB ⟨_, hx, v, rfl⟩)
        exact clique_in_row_le_two R hR_clique a h_subset
    · have h_subset : ∀ x ∈ R, ∃ v, x = Sum.inl (b, v) := by
        intro x hx
        obtain ⟨u, v, rfl, hu⟩ := hR_rows x hx
        rcases hu with rfl | rfl
        · exact False.elim (hA ⟨_, hx, v, rfl⟩)
        · exact ⟨v, rfl⟩
      exact clique_in_row_le_two R hR_clique b h_subset
  rw [hQ_eq]
  have hcard : (insert (Sum.inr S) R).card = R.card + 1 :=
    Finset.card_insert_of_notMem hnotR
  rw [hcard]
  omega

/-
The clique number of $G$ is at most 3.
-/
lemma GraphG_cliqueNum_le_three : GraphG.cliqueNum ≤ 3 := by
  refine csSup_le' ?_;
  rintro n ⟨ s, hs ⟩;
  by_cases hX : ∃ S : X_type_G, Sum.inr S ∈ s;
  · exact hs.2 ▸ clique_with_X_le_three _ hs.1 _ hX.choose_spec;
  · -- Since there's no vertex from X in s, all vertices in s must be in the grid
    -- part. By `clique_grid_le_three`, the size of s is at most 3.
    have h_grid : ∀ x ∈ s, ∃ u v, x = Sum.inl (u, v) := by
      intro x hx
      rcases x with ⟨u, v⟩ | S
      · exact ⟨u, v, rfl⟩
      · exact False.elim (hX ⟨S, hx⟩)
    have := hs.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    exact this ▸ clique_grid_le_three s ( fun x hx y hy hxy => hs hx hy hxy ) h_grid

/-
The clique number of $G$ is at least 3.
-/
lemma GraphG_cliqueNum_ge_three : GraphG.cliqueNum ≥ 3 := by
  -- Since $\omega(H_1) = 3$, there exists a clique $C$ of size 3 in $H_1$.
  -- We embed $C$ into $G$ by mapping each vertex $u \in C$ to $(u, v)$ for a
  -- fixed $v \in V_2$.
  obtain ⟨C, hC⟩ : ∃ C : Finset V1, C.card = 3 ∧ H1.IsClique C := by
    have h_clique_H1 : H1.cliqueNum ≥ 3 := by
      have := H1_props.1;
      rw [ this ];
      refine le_csSup ?_ ?_;
      · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
      · exists { Sum.inl 0, Sum.inl 1, Sum.inl 2 };
        simp +decide [ SimpleGraph.isNClique_iff ];
        simp +decide [ TwoK3 ];
    have h_clique_H1 : ∃ C : Finset V1, H1.IsClique C ∧ C.card ≥ 3 := by
      contrapose! h_clique_H1;
      refine lt_of_le_of_lt (csSup_le (a := 2) ?_ ?_) ?_ <;> norm_num;
      · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
      · exact fun b x hx => Nat.le_of_lt_succ ( by linarith [ h_clique_H1 x hx.1, hx.2.symm ] );
    obtain ⟨ C, hC₁, hC₂ ⟩ := h_clique_H1;
    exact Exists.elim ( Finset.exists_subset_card_eq hC₂ ) fun s hs =>
      ⟨ s, hs.2, hC₁.subset <| by aesop ⟩;
  have h_embedding :
      ∃ v : V2,
        ∀ u u' : V1,
          u ∈ C → u' ∈ C → u ≠ u' →
            GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u', v)) := by
    -- Since $H2$ is finite, choose a vertex $v$ and embed the clique into one row.
    obtain ⟨v, hv⟩ : ∃ v : V2, True := by
      by_contra h_empty2;
      simp_all +decide
      exact absurd ( H2_props.2 ) ( by
        unfold VertexPartitionRamsey; simp +decide
        intro x; exact ⟨ fun f => h_empty2.elim ( f.toEquiv ( 0 ) ) ⟩ ; );
    use v; intro u u' hu hu' hne; exact Or.inr ⟨ rfl, hC.2 hu hu' hne ⟩ ;
  obtain ⟨ v, hv ⟩ := h_embedding;
  have h_embedding : ∃ C' : Finset VertexG, C'.card = 3 ∧ GraphG.IsClique C' := by
    use Finset.image (fun u : V1 => (Sum.inl (u, v) : VertexG)) C
    constructor
    · rw [Finset.card_image_of_injective]
      · exact hC.1
      · intro u u' h
        exact congrArg Prod.fst (Sum.inl.inj h)
    · intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨u', hu', hyeq⟩
      cases hyeq
      have hne : u ≠ u' := by
        intro huu
        apply hxy
        rw [huu]
      exact hv u u' hu hu' hne
  obtain ⟨ C', hC'₁, hC'₂ ⟩ := h_embedding;
  refine le_csSup ?_ ?_;
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
    let e_G : Sym2 VertexG := s(Sum.inl (u, v), Sum.inl (u, v'))
    have h_adj : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u, v')) := by
      -- By definition of $GraphG.Adj$, adjacency in one row is adjacency in $H2$.
      have h_adj :
          GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u, v')) ↔
            v ≠ v' ∧ (H2.Adj v v' ∨ H2.Adj v' v) := by
        constructor <;> intro h <;> simp_all +decide [ GraphG ];
        · unfold AdjG at h; aesop;
        · exact Or.inl ⟨ rfl, by cases h.2 <;> tauto ⟩
      generalize_proofs at *;
      -- Since $e$ is an edge in $H2$, by definition, $H2.Adj v v'$ must be true.
      have h_adj_H2 : H2.Adj v v' := by
        have h_edge : (s(v, v')) ∈ H2.edgeSet := by
          convert e.2 using 1
          generalize_proofs at *;
          exact Quot.out_eq e.val ▸ rfl
        convert h_edge using 1;
      exact h_adj.mpr ⟨ by rintro h; simpa [ h ] using h_adj_H2.ne, Or.inl h_adj_H2 ⟩
    c ⟨e_G, h_adj⟩

/-
There exists a set $U \subseteq V_1$ inducing $2K_3$ in $H_1$ such that all rows
in $U$ have the same induced coloring on $H_2$.
-/
noncomputable def row_coloring_map (c : GraphG.edgeSet → Bool) (u : V1) : H2.edgeSet → Bool :=
  induced_coloring c u

lemma exists_monochromatic_U
  (c : GraphG.edgeSet → Bool) :
  ∃ (U : Set V1) (chi : H2.edgeSet → Bool),
    Nonempty (H1.induce U ≃g TwoK3) ∧
    ∀ u ∈ U, row_coloring_map c u = chi := by
      norm_num +zetaDelta at *;
      have h_edgeSet_card : Fintype.card H2.edgeSet = H2.edgeFinset.card := by
        rw [ Fintype.card_subtype ]
        simp [ SimpleGraph.edgeFinset ]
      have := H1_props.2;
      contrapose! this;
      unfold VertexPartitionRamsey; simp +decide ;
      refine ⟨ ?_, ?_ ⟩;
      focus
        exact fun u =>
          Fintype.equivFinOfCardEq
            (show Fintype.card ( H2.edgeSet → Bool ) = N_param from by
              simp +decide [ N_param, h_edgeSet_card ])
            (row_coloring_map c u);
      intro x U hx; specialize this U; simp_all +decide [ SimpleGraph.comap, SimpleGraph.induce ] ;
      exact ⟨ fun f => by
        obtain ⟨ u, hu, hu' ⟩ := this f.symm
          (Fintype.equivFinOfCardEq
            (show Fintype.card ( H2.edgeSet → Bool ) = N_param from by
              simp +decide [ N_param, h_edgeSet_card ]) |>.symm x)
        specialize hx u hu
        aesop ⟩

/-
The number of pairs $(e, v)$ where $e$ is an edge in a set of size 3 and $v \in e$ is 6.
-/
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
noncomputable def edgeWithVertexFinset (S : Finset V) : Finset (Sym2 V × V) :=
  S.offDiag.image (fun p : V × V => (s(p.1, p.2), p.1))

omit [Fintype V] in
lemma card_edgeWithVertexFinset (S : Finset V) (hS : S.card = 3) :
  (edgeWithVertexFinset S).card = 6 := by
  rw [edgeWithVertexFinset, Finset.card_image_of_injOn]
  · rw [Finset.offDiag_card, hS]
  · intro p hp q hq hpq
    rcases p with ⟨a, b⟩
    rcases q with ⟨c, d⟩
    have hfst : a = c := congrArg Prod.snd hpq
    have hsym : s(a, b) = s(c, d) := congrArg Prod.fst hpq
    have hne : a ≠ b := by
      exact (Finset.mem_offDiag.mp hp).2.2
    subst c
    have hbd : b = d := by
      have h' : b = d ∨ a = d ∧ b = a := by
        simpa [Sym2.eq] using hsym
      rcases h' with hbd | hbad
      · exact hbd
      · exact False.elim (hne hbad.2.symm)
    subst d
    rfl

/-
The cardinality of the signature data type is 36.
-/
noncomputable def SigData (A B : Finset V) : Type _ :=
  { x // x ∈ edgeWithVertexFinset A } × { x // x ∈ edgeWithVertexFinset B }

omit [Fintype V] in
noncomputable instance (A B : Finset V) : Fintype (SigData A B) := by
  unfold SigData
  infer_instance

omit [Fintype V] in
noncomputable instance (A B : Finset V) : DecidableEq (SigData A B) := by
  unfold SigData
  infer_instance

omit [Fintype V] in
lemma card_SigData (A B : Finset V) (hA : A.card = 3) (hB : B.card = 3) :
  Fintype.card (SigData A B) = 36 := by
    convert congr_arg₂ ( · * · )
      ( card_edgeWithVertexFinset A hA )
      ( card_edgeWithVertexFinset B hB ) using 1;
    convert Fintype.card_prod _ _;
    all_goals try infer_instance;
    · rw [ Fintype.card_coe ];
    · rw [ Fintype.card_coe ]

/-
Edges in a signature are non-diagonal.
-/
omit [Fintype V] in
lemma SigData_edge_nd1 (A B : Finset V) (s : SigData A B) : ¬ s.1.val.1.IsDiag := by
  rcases s.1 with ⟨⟨e, u⟩, hmem⟩
  change ¬ e.IsDiag
  unfold edgeWithVertexFinset at hmem
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hp⟩
  have he : e = s(a, b) := congrArg Prod.fst hp.symm
  have hne : a ≠ b := by
    exact (Finset.mem_offDiag.mp hab).2.2
  rw [he]
  simpa [Sym2.mk_isDiag_iff] using hne

omit [Fintype V] in
lemma SigData_edge_nd2 (A B : Finset V) (s : SigData A B) : ¬ s.2.val.1.IsDiag := by
  rcases s.2 with ⟨⟨e, u⟩, hmem⟩
  change ¬ e.IsDiag
  unfold edgeWithVertexFinset at hmem
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hp⟩
  have he : e = s(a, b) := congrArg Prod.fst hp.symm
  have hne : a ≠ b := by
    exact (Finset.mem_offDiag.mp hab).2.2
  rw [he]
  simpa [Sym2.mk_isDiag_iff] using hne

omit [Fintype V] in
lemma SigData_mem_left (A B : Finset V) (s : SigData A B) : s.1.val.2 ∈ A := by
  rcases s.1 with ⟨⟨e, u⟩, hmem⟩
  change u ∈ A
  unfold edgeWithVertexFinset at hmem
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hp⟩
  have hu : u = a := congrArg Prod.snd hp.symm
  rw [hu]
  exact (Finset.mem_offDiag.mp hab).1

omit [Fintype V] in
lemma SigData_mem_right (A B : Finset V) (s : SigData A B) : s.2.val.2 ∈ B := by
  rcases s.2 with ⟨⟨e, u⟩, hmem⟩
  change u ∈ B
  unfold edgeWithVertexFinset at hmem
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hp⟩
  have hu : u = a := congrArg Prod.snd hp.symm
  rw [hu]
  exact (Finset.mem_offDiag.mp hab).1

lemma sym2_out_eq_or_swap {α : Type*} (a b : α) :
    (s(a, b) : Sym2 α).out = (a, b) ∨ (s(a, b) : Sym2 α).out = (b, a) := by
  have hout := Quot.out_eq (s(a, b) : Sym2 α)
  change s((s(a, b) : Sym2 α).out.1, (s(a, b) : Sym2 α).out.2) = s(a, b) at hout
  have hrel := Sym2.eq.mp hout
  simpa [Sym2.Rel] using hrel

/-
If there are no monochromatic triangles, then any clique of size 3 must contain a red edge.
-/
lemma exists_red_edge_in_clique3
  (c : GraphG.edgeSet → Bool)
  (A : Finset V1)
  (hA : H1.IsClique A)
  (hA_card : A.card = 3)
  (v : V2)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩)) :
  ∃ (u w : V1) (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
    u ∈ A ∧ w ∈ A ∧ c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false := by
      by_contra h_contra;
      -- Since $A$ is a clique of size 3 in $H_1$, $A \times \{v\}$ is a clique
      -- of size 3 in $G$.
      have h_clique :
          ∀ u w : V1,
            u ∈ A → w ∈ A → u ≠ w →
              GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v)) := by
        intros u w hu hw hne; exact (by
        -- Since $u$ and $w$ are adjacent in $H_1`, their images are adjacent in $G`.
        have h_adj : H1.Adj u w := by
          exact hA hu hw hne;
        exact Or.inr ⟨ rfl, h_adj ⟩);
      obtain ⟨u, w, x, huA, hwA, hxA, huvw⟩ :
          ∃ u w x : V1,
            u ∈ A ∧ w ∈ A ∧ x ∈ A ∧ u ≠ w ∧ u ≠ x ∧ w ≠ x := by
        rcases Finset.card_eq_three.mp hA_card with ⟨ u, w, x, hu, hw, hx, h ⟩
        use u, w, x
        aesop;
      exact h_no_mono
        (Sum.inl (u, v)) (Sum.inl (w, v)) (Sum.inl (x, v))
        (h_clique u w huA hwA huvw.1)
        (h_clique w x hwA hxA huvw.2.2)
        (h_clique u x huA hxA huvw.2.1) (by aesop)

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
  (∃ (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
    c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false) ∧
  (∃ (h : GraphG.Adj (Sum.inr ⟨e1, SigData_edge_nd1 A B s⟩) (Sum.inl (u1, v))),
    c ⟨s(Sum.inr ⟨e1, SigData_edge_nd1 A B s⟩, Sum.inl (u1, v)), h⟩ = true) ∧
  (∃ (h : GraphG.Adj (Sum.inl (p, v)) (Sum.inl (q, v))),
    c ⟨s(Sum.inl (p, v), Sum.inl (q, v)), h⟩ = true) ∧
  (∃ (h : GraphG.Adj (Sum.inr ⟨e2, SigData_edge_nd2 A B s⟩) (Sum.inl (u2, v))),
    c ⟨s(Sum.inr ⟨e2, SigData_edge_nd2 A B s⟩, Sum.inl (u2, v)), h⟩ = false)

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
If an edge in the grid is red, one of the edges connecting it to the corresponding
vertex in X must be blue.
-/
lemma exists_blue_edge_to_X
  (c : GraphG.edgeSet → Bool)
  (u w : V1)
  (v : V2)
  (h_neq : u ≠ w)
  (h_red :
    ∃ (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
      c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false)
  (h_no_mono :
    ∀ (x y z : VertexG) (hxy : GraphG.Adj x y)
      (hyz : GraphG.Adj y z) (hxz : GraphG.Adj x z),
    ¬(c ⟨s(x, y), hxy⟩ = c ⟨s(y, z), hyz⟩ ∧ c ⟨s(y, z), hyz⟩ = c ⟨s(x, z), hxz⟩)) :
  ∃ (u1 : V1), (u1 = u ∨ u1 = w) ∧
    ∃ (h_nd : ¬(s(u, w)).IsDiag) (h_adj : GraphG.Adj (Sum.inr ⟨s(u, w), h_nd⟩) (Sum.inl (u1, v))),
      c ⟨s(Sum.inr ⟨s(u, w), h_nd⟩, Sum.inl (u1, v)), h_adj⟩ = true := by
        contrapose! h_no_mono;
        -- Let's choose $x = X_{(u,w)}$, $y = (u,v)$, and $z = (w,v)$.
        use Sum.inr ⟨s(u, w), by
          cases h : s( u, w ) ; aesop⟩, Sum.inl (u, v), Sum.inl (w, v)
        generalize_proofs at *;
        use adj_X_col_redef _ ‹_› _ (by
        exact Sym2.mem_mk_left u w) _, h_red.choose, adj_X_col_redef _ ‹_› _ (by
        exact Sym2.mem_mk_right u w) _
        generalize_proofs at *;
        have := h_no_mono u ( Or.inl rfl ) ‹_› ‹_›
        have := h_no_mono w ( Or.inr rfl ) ‹_› ‹_›
        aesop;

/-
If there are no monochromatic triangles, then any clique of size 3 must contain a blue edge.
-/
lemma exists_blue_edge_in_clique3
  (c : GraphG.edgeSet → Bool)
  (B : Finset V1)
  (hB : H1.IsClique B)
  (hB_card : B.card = 3)
  (v : V2)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩)) :
  ∃ (u w : V1) (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
    u ∈ B ∧ w ∈ B ∧ c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h⟩ = true := by
      -- Suppose for contradiction that all edges in $B \times \{v\}$ are red (false).
      by_contra h_contra
      have h_all_red :
          ∀ u w : V1, ∀ (hu : u ∈ B) (hw : w ∈ B) (hne : u ≠ w),
            c ⟨s(Sum.inl (u, v), Sum.inl (w, v)),
              (Or.inr ⟨rfl, hB hu hw hne⟩ :
                GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v)))⟩ = false := by
        intro u w hu hw hne
        let h_adj : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v)) :=
          Or.inr ⟨rfl, hB hu hw hne⟩
        change c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h_adj⟩ = false
        cases hcol : c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h_adj⟩
        · rfl
        · exact False.elim (h_contra ⟨u, w, h_adj, hu, hw, hcol⟩)
      generalize_proofs at *;
      obtain ⟨u, w, x, hu, hw, hx, h_adj⟩ :
          ∃ u w x : V1,
            u ∈ B ∧ w ∈ B ∧ x ∈ B ∧ u ≠ w ∧ u ≠ x ∧ w ≠ x ∧
              GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v)) ∧
              GraphG.Adj (Sum.inl (w, v)) (Sum.inl (x, v)) ∧
              GraphG.Adj (Sum.inl (u, v)) (Sum.inl (x, v)) := by
        rcases Finset.card_eq_three.mp hB_card with ⟨ u, w, x, hu, hw, hx, h ⟩
        use u, w, x
        aesop;
      exact h_no_mono
        (Sum.inl (u, v)) (Sum.inl (w, v)) (Sum.inl (x, v))
        h_adj.2.2.2.1 h_adj.2.2.2.2.1 h_adj.2.2.2.2.2
        ⟨ by aesop, by aesop ⟩

/-
If there are no monochromatic triangles, then for every vertex v in V2, there exists
a valid signature s in SigData A B.
-/
lemma exists_signature_for_v
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (v : V2)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩)) :
  ∃ (s : SigData A B), ValidSignature c A B v s := by
    -- By Lemma 25, there exists a red edge (u, w) in A and a blue edge (p, q) in B.
    obtain ⟨u, w, h_red⟩ :
        ∃ u w : V1,
          u ∈ A ∧ w ∈ A ∧ u ≠ w ∧
            ∃ (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
              c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false := by
      have h_exists_red_edge :
          ∃ (u w : V1) (h : GraphG.Adj (Sum.inl (u, v)) (Sum.inl (w, v))),
            u ∈ A ∧ w ∈ A ∧
              c ⟨s(Sum.inl (u, v), Sum.inl (w, v)), h⟩ = false := by
        apply exists_red_edge_in_clique3 c A hA hA_card v h_no_mono;
      grind
    obtain ⟨p, q, h_blue⟩ :
        ∃ p q : V1,
          p ∈ B ∧ q ∈ B ∧ p ≠ q ∧
            ∃ (h : GraphG.Adj (Sum.inl (p, v)) (Sum.inl (q, v))),
              c ⟨s(Sum.inl (p, v), Sum.inl (q, v)), h⟩ = true := by
      convert exists_blue_edge_in_clique3 c B hB hB_card v h_no_mono using 1;
      grind +ring;
    -- By Lemma 25, there exists a blue edge (p, q) in B and a red edge (u, w) in A.
    obtain ⟨u1, hu1⟩ :
        ∃ u1 : V1, (u1 = u ∨ u1 = w) ∧
          ∃ (h_nd : ¬(s(u, w)).IsDiag)
            (h_adj : GraphG.Adj (Sum.inr ⟨s(u, w), h_nd⟩) (Sum.inl (u1, v))),
            c ⟨s(Sum.inr ⟨s(u, w), h_nd⟩, Sum.inl (u1, v)), h_adj⟩ = true := by
      apply exists_blue_edge_to_X c u w v h_red.2.2.1 h_red.2.2.2 h_no_mono
    obtain ⟨u2, hu2⟩ :
        ∃ u2 : V1, (u2 = p ∨ u2 = q) ∧
          ∃ (h_nd : ¬(s(p, q)).IsDiag)
            (h_adj : GraphG.Adj (Sum.inr ⟨s(p, q), h_nd⟩) (Sum.inl (u2, v))),
            c ⟨s(Sum.inr ⟨s(p, q), h_nd⟩, Sum.inl (u2, v)), h_adj⟩ = false := by
      apply Classical.byContradiction
      intro h_no_u2;
      exact h_no_mono
        (Sum.inr ⟨ s(p, q), by aesop ⟩)
        (Sum.inl (p, v)) (Sum.inl (q, v))
        (by exact adj_X_col_redef _ (by aesop) _ (by aesop) _)
        (by exact h_blue.2.2.2.choose)
        (by exact adj_X_col_redef _ (by aesop) _ (by aesop) _) <| by aesop;
    have hmem1 : (s(u, w), u1) ∈ edgeWithVertexFinset A := by
      unfold edgeWithVertexFinset
      rcases hu1.1 with hu1u | hu1w
      · exact Finset.mem_image.mpr
          ⟨(u, w),
            Finset.mem_offDiag.mpr ⟨h_red.1, h_red.2.1, h_red.2.2.1⟩,
            by simp [hu1u]⟩
      · exact Finset.mem_image.mpr
          ⟨(w, u),
            Finset.mem_offDiag.mpr ⟨h_red.2.1, h_red.1, Ne.symm h_red.2.2.1⟩,
            by simp [hu1w, Sym2.eq_swap]⟩
    have hmem2 : (s(p, q), u2) ∈ edgeWithVertexFinset B := by
      unfold edgeWithVertexFinset
      rcases hu2.1 with hu2p | hu2q
      · exact Finset.mem_image.mpr
          ⟨(p, q),
            Finset.mem_offDiag.mpr ⟨h_blue.1, h_blue.2.1, h_blue.2.2.1⟩,
            by simp [hu2p]⟩
      · exact Finset.mem_image.mpr
          ⟨(q, p),
            Finset.mem_offDiag.mpr ⟨h_blue.2.1, h_blue.1, Ne.symm h_blue.2.2.1⟩,
            by simp [hu2q, Sym2.eq_swap]⟩
    let sig : SigData A B := ⟨⟨(s(u, w), u1), hmem1⟩, ⟨(s(p, q), u2), hmem2⟩⟩
    refine ⟨sig, ?_⟩
    unfold ValidSignature
    dsimp [sig]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases sym2_out_eq_or_swap u w with hout | hout
      · rw [hout]
        exact h_red.2.2.2
      · rw [hout]
        obtain ⟨h_adj, h_col⟩ := h_red.2.2.2
        refine ⟨GraphG.symm h_adj, ?_⟩
        simpa [Sym2.eq_swap] using h_col
    · obtain ⟨h_nd, h_adj, h_col⟩ := hu1.2
      refine ⟨by simpa using h_adj, ?_⟩
      simpa using h_col
    · rcases sym2_out_eq_or_swap p q with hout | hout
      · rw [hout]
        exact h_blue.2.2.2
      · rw [hout]
        obtain ⟨h_adj, h_col⟩ := h_blue.2.2.2
        refine ⟨GraphG.symm h_adj, ?_⟩
        simpa [Sym2.eq_swap] using h_col
    · obtain ⟨h_nd, h_adj, h_col⟩ := hu2.2
      refine ⟨by simpa using h_adj, ?_⟩
      simpa using h_col

/-
There exist two adjacent vertices in H2 that have the same signature.
-/
noncomputable def signature_map
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩))
  (v : V2) : SigData A B :=
  Classical.choose (exists_signature_for_v c A B hA hA_card hB hB_card v h_no_mono)

lemma signature_map_valid
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩))
  (v : V2) :
  ValidSignature c A B v (signature_map c A B hA hA_card hB hB_card h_no_mono v) :=
  Classical.choose_spec (exists_signature_for_v c A B hA hA_card hB hB_card v h_no_mono)

lemma exists_same_signature_edge
  (c : GraphG.edgeSet → Bool)
  (A B : Finset V1)
  (hA : H1.IsClique A) (hA_card : A.card = 3)
  (hB : H1.IsClique B) (hB_card : B.card = 3)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩)) :
  ∃ (v w : V2), H2.Adj v w ∧
    signature_map c A B hA hA_card hB hB_card h_no_mono v =
      signature_map c A B hA hA_card hB hB_card h_no_mono w := by
      by_contra! h;
      -- By the Ramsey property, there exists a monochromatic copy of $K_2$ in $H_2$.
      obtain ⟨v, w, hvw, h_mono⟩ :
          ∃ v w : V2, H2.Adj v w ∧
            signature_map c A B hA hA_card hB hB_card h_no_mono v =
              signature_map c A B hA hA_card hB hB_card h_no_mono w := by
        have h_ramsey : ∀ (f : V2 → Fin 36), ∃ v w : V2, H2.Adj v w ∧ f v = f w := by
          intro f
          by_contra h_no_monochromatic
          push Not at h_no_monochromatic;
          have := H2_props.2;
          obtain ⟨ U, hU_mono, hU_iso ⟩ := this f;
          obtain ⟨ g, hg ⟩ := hU_iso.2;
          have := @h_no_monochromatic ( g 0 ) ( g 1 ) ?_ <;> simp_all +decide [ K2 ]
        have h_equiv : Nonempty (SigData A B ≃ Fin 36) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ card_SigData A B hA_card hB_card ] ⟩;
        exact h_ramsey
          (fun v => h_equiv.some (signature_map c A B hA hA_card hB hB_card h_no_mono v)) |>
            fun ⟨ v, w, hvw, h ⟩ => ⟨ v, w, hvw, h_equiv.some.injective h ⟩;
      exact h v w hvw h_mono

/-
If v and w are adjacent in H2, then (u, v) and (u, w) are adjacent in G for any u.
-/
lemma adj_row_of_adj_H2
  (u : V1) (v w : V2) (h : H2.Adj v w) :
  GraphG.Adj (Sum.inl (u, v)) (Sum.inl (u, w)) := by
    exact Or.inl ⟨ rfl, h ⟩

/-
If two adjacent vertices in H2 have the same signature and the rows corresponding to
the cliques A and B have the same color on the edge connecting them, then there is a
monochromatic triangle.
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
  (h_row_color :
    ∀ u, u ∈ A ∨ u ∈ B →
      c ⟨s(Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ = k)
  (h_no_mono :
    ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
      (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
    ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧ c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩)) :
  False := by
  unfold ValidSignature at h_valid_v h_valid_w
  dsimp at h_valid_v h_valid_w
  cases k
  · obtain ⟨_, _, _, hvX⟩ := h_valid_v
    obtain ⟨_, _, _, hwX⟩ := h_valid_w
    obtain ⟨hXv, hcXv⟩ := hvX
    obtain ⟨hXw, hcXw⟩ := hwX
    let x : VertexG := Sum.inr ⟨s.2.val.1, SigData_edge_nd2 A B s⟩
    let y : VertexG := Sum.inl (s.2.val.2, v)
    let z : VertexG := Sum.inl (s.2.val.2, w)
    let hyz : GraphG.Adj y z := adj_row_of_adj_H2 s.2.val.2 v w hvw
    have hrow : c ⟨s(y, z), hyz⟩ = false :=
      h_row_color s.2.val.2 (Or.inr (SigData_mem_right A B s))
    exact h_no_mono x y z hXv hyz hXw
      ⟨by rw [hcXv, hrow], by rw [hrow, hcXw]⟩
  · obtain ⟨_, hvX, _, _⟩ := h_valid_v
    obtain ⟨_, hwX, _, _⟩ := h_valid_w
    obtain ⟨hXv, hcXv⟩ := hvX
    obtain ⟨hXw, hcXw⟩ := hwX
    let x : VertexG := Sum.inr ⟨s.1.val.1, SigData_edge_nd1 A B s⟩
    let y : VertexG := Sum.inl (s.1.val.2, v)
    let z : VertexG := Sum.inl (s.1.val.2, w)
    let hyz : GraphG.Adj y z := adj_row_of_adj_H2 s.1.val.2 v w hvw
    have hrow : c ⟨s(y, z), hyz⟩ = true :=
      h_row_color s.1.val.2 (Or.inl (SigData_mem_left A B s))
    exact h_no_mono x y z hXv hyz hXw
      ⟨by rw [hcXv, hrow], by rw [hrow, hcXw]⟩

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
      obtain ⟨A, B, hA, hB, h_disjoint⟩ :
          ∃ A B : Finset (Fin 3 ⊕ Fin 3),
            A.card = 3 ∧ B.card = 3 ∧ A ∩ B = ∅ ∧
              (TwoK3.IsClique A) ∧ (TwoK3.IsClique B) := by
        exists { Sum.inl 0, Sum.inl 1, Sum.inl 2 },
          { Sum.inr 0, Sum.inr 1, Sum.inr 2 }
        simp +decide [ SimpleGraph.IsClique ] ;
        simp +decide [ TwoK3 ];
      obtain ⟨g, hg⟩ : ∃ g : U ≃ Fin 3 ⊕ Fin 3, ∀ u v : U, H1.Adj u v ↔ TwoK3.Adj (g u) (g v) := by
        exact ⟨ h_iso.some.toEquiv, fun u v => by simp +decide [ SimpleGraph.Iso.map_adj_iff ] ⟩;
      let A' : Finset V1 := Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) A
      let B' : Finset V1 := Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) B
      refine ⟨ A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_ ⟩
      · intro x hx
        change x ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) A at hx
        rcases Finset.mem_image.mp hx with ⟨ a, ha, hxa ⟩
        rw [← hxa]
        exact (g.symm a).2
      · intro x hx
        change x ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) B at hx
        rcases Finset.mem_image.mp hx with ⟨ b, hb, hxb ⟩
        rw [← hxb]
        exact (g.symm b).2
      · intro x hx y hy hxy
        change x ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) A at hx
        change y ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) A at hy
        rcases Finset.mem_image.mp hx with ⟨ a, ha, hxa ⟩
        rcases Finset.mem_image.mp hy with ⟨ b, hb, hyb ⟩
        have hab : a ≠ b := by
          intro h
          apply hxy
          rw [← hxa, ← hyb, h]
        exact
          by
          rw [← hxa, ← hyb]
          exact (hg (g.symm a) (g.symm b)).2 (by
            simpa using h_disjoint.2.1 ha hb hab)
      · change (Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) A).card = 3
        rw [ Finset.card_image_of_injective _ fun x y hxy => by
          exact g.symm.injective <| Subtype.ext hxy ]
        exact hA
      · intro x hx y hy hxy
        change x ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) B at hx
        change y ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) B at hy
        rcases Finset.mem_image.mp hx with ⟨ a, ha, hxa ⟩
        rcases Finset.mem_image.mp hy with ⟨ b, hb, hyb ⟩
        have hab : a ≠ b := by
          intro h
          apply hxy
          rw [← hxa, ← hyb, h]
        exact
          by
          rw [← hxa, ← hyb]
          exact (hg (g.symm a) (g.symm b)).2 (by
            simpa using h_disjoint.2.2 ha hb hab)
      · change (Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) B).card = 3
        rw [ Finset.card_image_of_injective _ fun x y hxy => by
          exact g.symm.injective <| Subtype.ext hxy ]
        exact hB
      · rw [Finset.disjoint_left]
        intro x hxA hxB
        change x ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) A at hxA
        change x ∈ Finset.image (fun x : Fin 3 ⊕ Fin 3 => (g.symm x : V1)) B at hxB
        rcases Finset.mem_image.mp hxA with ⟨ a, ha, hxa ⟩
        rcases Finset.mem_image.mp hxB with ⟨ b, hb, hxb ⟩
        have hab : a = b := by
          apply g.symm.injective
          exact Subtype.ext (hxa.trans hxb.symm)
        have hmem : a ∈ A ∩ B := by
          exact Finset.mem_inter.mpr ⟨ ha, by simpa [hab] using hb ⟩
        rw [h_disjoint.1] at hmem
        simp at hmem

/-
If U is a set of vertices such that all rows u in U induce the same coloring chi on
H2, and A, B are subsets of U, then for any edge vw in H2 with color k under chi,
the corresponding edges (u, v)~(u, w) in G have color k for all u in A or B.
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
  (hk : chi ⟨s(v, w), hvw⟩ = k) :
  ∀ u, u ∈ A ∨ u ∈ B →
    c ⟨s(Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ = k := by
    -- By definition of `row_coloring_map`, it agrees with the corresponding row
    -- edge color in `G`.
    have h_row_coloring_map :
        ∀ u ∈ U,
          row_coloring_map c u ⟨s(v, w), hvw⟩ =
            c ⟨s(Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ := by
      -- By definition, this is the color of the edge `(u, v) \sim (u, w)`.
      simp [row_coloring_map, induced_coloring];
      congr! 2
      generalize_proofs at *; (
      have := Quot.out_eq ( s(v, w) )
      ( rcases h : Quot.out ( s(v, w) ) with ⟨ x, y ⟩ ; aesop; ) ;)
    generalize_proofs at *; (
    exact fun u hu =>
      h_row_coloring_map u (hu.elim (fun hu => hA_sub hu) fun hu => hB_sub hu) ▸
      hU_color u (hu.elim (fun hu => hA_sub hu) fun hu => hB_sub hu) ▸ hk ▸ rfl;)

/-
The graph G is edge-Ramsey for triangles.
-/
theorem folkman_theorem : EdgeRamseyTriangle GraphG := by
  intro c
  obtain ⟨U, chi, h_iso, h_color⟩ := exists_monochromatic_U c;
  obtain ⟨ A, B, hA_sub, hB_sub, hA, hA_card, hB, hB_card, h_disjoint ⟩ :=
    extract_disjoint_cliques U h_iso;
  by_cases h_no_mono :
      ∀ (u v w : VertexG) (huv : GraphG.Adj u v)
        (hvw : GraphG.Adj v w) (huw : GraphG.Adj u w),
        ¬(c ⟨s(u, v), huv⟩ = c ⟨s(v, w), hvw⟩ ∧
          c ⟨s(v, w), hvw⟩ = c ⟨s(u, w), huw⟩);
  · obtain ⟨ v, w, hvw, h_eq ⟩ := exists_same_signature_edge c A B hA hA_card hB hB_card h_no_mono;
    -- Let `k` be the color of the edge `vw` in `H2` under `chi`.
    obtain ⟨k, hk⟩ : ∃ k : Bool, chi ⟨s(v, w), hvw⟩ = k := by
      use chi ⟨s(v, w), hvw⟩;
    -- By `row_color_of_cliques_in_U`, for any `u \in A \cup B`, the edge
    -- `(u, v) \sim (u, w)` has color `k`.
    have h_row_color :
        ∀ u, u ∈ A ∨ u ∈ B →
          c ⟨s(Sum.inl (u, v), Sum.inl (u, w)), adj_row_of_adj_H2 u v w hvw⟩ = k := by
      apply row_color_of_cliques_in_U c U chi h_color A B hA_sub hB_sub v w hvw k hk;
    exact False.elim
      (same_signature_contradiction c A B v w hvw _
        (signature_map_valid c A B hA hA_card hB hB_card h_no_mono v)
        (by
          simpa only [ h_eq ] using
            signature_map_valid c A B hA hA_card hB hB_card h_no_mono w)
        k h_row_color h_no_mono);
  · exact by push Not at h_no_mono; exact h_no_mono;

/-
There exists a graph G with clique number 3 that is edge-Ramsey for triangles.
-/
theorem erdos_582 :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      G.cliqueNum = 3 ∧ EdgeRamseyTriangle G := by
  use VertexG, inferInstance, inferInstance, GraphG
  exact ⟨GraphG_cliqueNum_eq_three, folkman_theorem⟩

end Erdos582

#print axioms Erdos582.erdos_582
-- 'Erdos582.erdos_582' depends on axioms: [propext, Classical.choice, Quot.sound]
