/-

This is a Lean formalization of a solution to Erdős Problem 1036.
https://www.erdosproblems.com/forum/thread/1036

The original proof was found by: Saharon Shelah

[Sh98] Shelah, Saharon, Erdős and {R}ényi
conjecture. J. Combin. Theory Ser. A (1998), 179--185.


A proof was auto-formalized by Aristotle (from Harmonic).  The final
theorem statement was written by Aristotle.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
Formalized the main theorem of the provided paper as `erdos_1036`.
The proof utilizes the helper lemmas and definitions provided in the assumptions, specifically `shelah_epsilon`, `shelah_n0`, `shelah_epsilon_pos`, and `shelah_contrapositive`.
The theorem states that for every $c > 0$, there exist $\varepsilon > 0$ and $n_0$ such that for any graph $G$ on $n \ge n_0$ vertices, if $\operatorname{hom}(G) \le c \log n$, then $I(G) \ge 2^{\varepsilon n}$.
-/

import Mathlib

import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic


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
hom(G) is the size of the largest homogeneous set (clique or independent set).
-/
def hom_num {V : Type*} (G : SimpleGraph V) : ℕ := max G.cliqueNum G.indepNum

/-
I(G) is the number of isomorphism types of induced subgraphs of G.
-/
def induced_iso_rel {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  Nonempty (G.induce s ≃g G.induce t)

def I_num {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  Fintype.card (Quotient (Setoid.mk (induced_iso_rel G) (by
  constructor;
  · intro x
    use Equiv.refl x
    simp
  · rintro x y ⟨ f, hf ⟩;
    refine' ⟨ f.symm, _ ⟩;
    grind;
  · rintro x y z ⟨ f, hf ⟩ ⟨ g, hg ⟩;
    exact ⟨ f.trans g, by aesop ⟩)))

/-
R(a,b) is the Ramsey number.
-/
def Ramsey_prop (a b N : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin N)), a ≤ G.cliqueNum ∨ b ≤ G.indepNum

noncomputable def R (a b : ℕ) : ℕ := sInf { N | Ramsey_prop a b N }

/-
Adding a vertex connected to all vertices in a clique of size n results in a clique of size n+1.
-/
theorem clique_extension {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (s : Finset V) (n : ℕ)
    (h_subset : s ⊆ G.neighborFinset v) (h_clique : G.IsNClique n s) :
    G.IsNClique (n + 1) (insert v s) := by
      simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
      exact Finset.card_insert_of_notMem ( fun h => by simpa [ h ] using h_subset h ) |> fun h => h.trans ( by simp +decide [ h_clique.2 ] )

/-
Ramsey property is monotone in N.
-/
theorem ramsey_prop_mono {a b N N' : ℕ} (h : Ramsey_prop a b N) (h_le : N ≤ N') : Ramsey_prop a b N' := by
  intro G;
  -- Let $G'$ be the induced subgraph of $G$ on the first $N$ vertices.
  set G' : SimpleGraph (Fin N) := SimpleGraph.comap (fun v => Fin.castLE h_le v) G;
  specialize h G';
  contrapose! h;
  constructor <;> rw [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ] at *;
  · refine' lt_of_le_of_lt ( csSup_le _ _ ) h.1;
    · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
    · rintro n ⟨ s, hs ⟩;
      refine' le_csSup _ _;
      · exact ⟨ N', fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq.symm ▸ le_trans ( Finset.card_le_univ _ ) ( by simp ) ⟩;
      · refine' ⟨ s.image ( Fin.castLE h_le ), _ ⟩;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        simp_all +decide [ SimpleGraph.IsClique, Finset.card_image_of_injective, Function.Injective ];
        intro x hx y hy hxy; aesop;
  · refine' lt_of_le_of_lt ( csSup_le _ _ ) h.2;
    · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩ ⟩;
    · rintro n ⟨ s, hs ⟩;
      refine' le_csSup _ _;
      · exact ⟨ N', fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ |> le_trans <| by simp ⟩;
      · use s.image (fun v => Fin.castLE h_le v);
        simp_all +decide [ SimpleGraph.isNIndepSet_iff, Finset.card_image_of_injective, Function.Injective ];
        intro x hx y hy; aesop;

/-
Generalization of Ramsey property to any type with cardinality N.
-/
theorem ramsey_prop_general {V : Type*} [Fintype V] [DecidableEq V] (a b N : ℕ) (hN : Fintype.card V = N)
  (h : Ramsey_prop a b N) (G : SimpleGraph V) :
  a ≤ G.cliqueNum ∨ b ≤ G.indepNum := by
    have := Fintype.truncEquivFinOfCardEq hN;
    obtain ⟨ e ⟩ := this;
    convert h ( G.map e );
    · rw [ SimpleGraph.cliqueNum, SimpleGraph.cliqueNum ];
      congr! 3;
      constructor <;> rintro ⟨ s, hs ⟩;
      · use s.image e;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        exact ⟨ fun x hx y hy hxy => by rcases hx with ⟨ u, hu, rfl ⟩ ; rcases hy with ⟨ v, hv, rfl ⟩ ; exact by simpa [ e.injective.eq_iff ] using hs.1 hu hv ( by aesop ), by rw [ Finset.card_image_of_injective _ e.injective, hs.2 ] ⟩;
      · use s.image e.symm;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        simp_all +decide [ SimpleGraph.IsClique, Set.Pairwise ];
        exact ⟨ fun x hx y hy hxy => by obtain ⟨ u', v', huv', hu', hv' ⟩ := hs.1 hx hy ( by aesop ) ; have := e.injective ( by aesop : e u' = e x ) ; have := e.injective ( by aesop : e v' = e y ) ; aesop, by rw [ Finset.card_image_of_injective _ e.symm.injective, hs.2 ] ⟩;
    · rw [ SimpleGraph.indepNum, SimpleGraph.indepNum ];
      congr! 3;
      constructor <;> rintro ⟨ s, hs ⟩;
      · use s.image e;
        simp_all +decide [ SimpleGraph.isNIndepSet_iff, Finset.card_image_of_injective _ e.injective ];
        intro x hx y hy hxy; aesop;
      · refine' ⟨ s.preimage e ( by simp +decide ), _ ⟩;
        simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
        simp_all +decide [ SimpleGraph.IsIndepSet, Set.preimage ];
        exact ⟨ fun x hx y hy hxy => fun h => hs.1 hx hy ( by aesop ) x y h rfl rfl, by rw [ Finset.card_preimage ] ; aesop ⟩

/-
Pigeonhole principle for Ramsey proof: for any vertex v, either |N(v)| >= N1 or |non-N(v)| >= N2.
-/
theorem pigeonhole_ramsey {N1 N2 : ℕ} (G : SimpleGraph (Fin (N1 + N2))) (v : Fin (N1 + N2)) :
  N1 ≤ (G.neighborFinset v).card ∨ N2 ≤ (Finset.univ \ (insert v (G.neighborFinset v))).card := by
    rw [ Finset.card_sdiff ] ; norm_num [ Finset.subset_iff ];
    omega

/-
Inductive step for Ramsey numbers: if Ramsey_prop holds for (a-1, b) at N1 and (a, b-1) at N2, it holds for (a, b) at N1 + N2.
-/
theorem ramsey_step (a b N1 N2 : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
  (h1 : Ramsey_prop (a - 1) b N1) (h2 : Ramsey_prop a (b - 1) N2) :
  Ramsey_prop a b (N1 + N2) := by
    intro G
    obtain ⟨v, hv⟩ : ∃ v : Fin (N1 + N2), N1 ≤ (G.neighborFinset v).card ∨ N2 ≤ (Finset.univ \ (insert v (G.neighborFinset v))).card := by
      have := @pigeonhole_ramsey N1 N2 G;
      cases N1 <;> cases N2 <;> simp_all +decide [ Finset.card_sdiff ];
      cases a <;> cases b <;> simp_all +decide [ Ramsey_prop ];
      simp_all +decide [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ];
      simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ];
      simp_all +decide [ Finset.eq_empty_of_forall_notMem ];
    cases' hv with hv hv;
    · -- Let $S$ be a subset of $N(v)$ with $|S| = N1$.
      obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (N1 + N2)), S ⊆ G.neighborFinset v ∧ S.card = N1 := by
        exact Finset.le_card_iff_exists_subset_card.mp hv;
      -- Consider the induced subgraph $G[S]$. Since $|S| = N1$, by `ramsey_prop_general` and `h1`, $G[S]$ has either a clique of size $a-1$ or an independent set of size $b$.
      have h_induced_S : (a - 1) ≤ (G.induce S).cliqueNum ∨ b ≤ (G.induce S).indepNum := by
        apply ramsey_prop_general;
        simp +zetaDelta at *;
        exacts [ hS.2, h1 ];
      cases' h_induced_S with h h;
      · -- If $G[S]$ has a clique $K$ of size $a-1$, then $K \subseteq S \subseteq N(v)$, so $v$ is adjacent to all vertices in $K$.
        obtain ⟨K, hK⟩ : ∃ K : Finset (Fin (N1 + N2)), K ⊆ S ∧ K.card = a - 1 ∧ G.IsClique K := by
          contrapose! h;
          refine' lt_of_le_of_lt ( csSup_le _ _ ) _;
          exact a - 2;
          · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
          · rintro n ⟨ s, hs ⟩;
            rcases a with ( _ | _ | a ) <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
            contrapose! h;
            obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( by linarith : a + 1 ≤ s.card );
            use t.image Subtype.val;
            simp_all +decide [ Finset.subset_iff, SimpleGraph.isClique_iff ];
            exact ⟨ by rw [ Finset.card_image_of_injective _ Subtype.coe_injective, ht.2 ], fun x hx y hy hxy => by obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; exact hs.1 ( ht.1 _ _ hu ) ( ht.1 _ _ hv ) ( by aesop ) ⟩;
          · omega;
        -- By `clique_extension`, $K \cup \{v\}$ is a clique of size $a$ in $G$.
        have h_clique : G.IsNClique a (insert v K) := by
          convert clique_extension G v K ( a - 1 ) _ _;
          · grind;
          · exact Finset.Subset.trans hK.1 hS.1;
          · exact ⟨ hK.2.2, hK.2.1 ⟩;
        exact Or.inl <| le_csSup ⟨ _, fun x hx => by obtain ⟨ t, ht ⟩ := hx; exact ht.2.symm ▸ Finset.card_le_univ _ ⟩ ⟨ _, h_clique ⟩;
      · refine Or.inr <| le_trans h ?_;
        refine' le_csSup _ _;
        · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
        · obtain ⟨ s, hs ⟩ := ( show ∃ s : Finset S, ( SimpleGraph.induce ( S : Set ( Fin ( N1 + N2 ) ) ) G ).IsNIndepSet ( SimpleGraph.induce ( S : Set ( Fin ( N1 + N2 ) ) ) G ).indepNum s from by
                                  exact SimpleGraph.exists_isNIndepSet_indepNum );
          use s.image Subtype.val;
          convert hs using 1;
          simp +decide [ SimpleGraph.isNIndepSet_iff, Finset.card_image_of_injective, Function.Injective ];
          simp +decide [ SimpleGraph.IsIndepSet, Set.Pairwise ];
          exact fun _ => Iff.rfl;
    · -- Let $T$ be a subset of $N^c(v)$ with $|T| = N2$.
      obtain ⟨T, hT⟩ : ∃ T : Finset (Fin (N1 + N2)), T.card = N2 ∧ T ⊆ Finset.univ \ (insert v (G.neighborFinset v)) := by
        exact Exists.elim ( Finset.exists_subset_card_eq hv ) fun T hT => ⟨ T, hT.2, hT.1 ⟩;
      -- Consider the induced subgraph $G[T]$. Since $|T| = N2$, by `ramsey_prop_general` and `h2`, $G[T]$ has either a clique of size $a$ or an independent set of size $b-1$.
      have h_induced_T : a ≤ (SimpleGraph.induce T G).cliqueNum ∨ b - 1 ≤ (SimpleGraph.induce T G).indepNum := by
        have := ramsey_prop_general a ( b - 1 ) N2 ?_ h2 ( SimpleGraph.induce T G ) <;> aesop;
      rcases h_induced_T with h | h;
      · -- If $G[T]$ has a clique $K$ of size $a$, then $K$ is a clique of size $a$ in $G$.
        obtain ⟨K, hK⟩ : ∃ K : Finset (Fin (N1 + N2)), K.card = a ∧ K ⊆ T ∧ ∀ x ∈ K, ∀ y ∈ K, x ≠ y → G.Adj x y := by
          contrapose! h;
          refine' lt_of_le_of_lt ( csSup_le _ _ ) _;
          exact a - 1;
          · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩;
          · rintro n ⟨ s, hs ⟩;
            refine' Nat.le_sub_one_of_lt _;
            refine' lt_of_not_ge fun hn => _;
            obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( show a ≤ s.card from by linarith [ hs.2 ] );
            obtain ⟨ x, hx, y, hy, hxy, h ⟩ := h ( Finset.image ( fun x : T => x.val ) t ) ( by simpa [ Finset.card_image_of_injective, Function.Injective ] using ht.2 ) ( Finset.image_subset_iff.mpr fun x hx => by aesop ) ; simp_all +decide
            have := hs.1; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            have := this ( show ( ⟨ x, hx.1 ⟩ : T ) ∈ s from ht.1 hx.2 ) ( show ( ⟨ y, hy.1 ⟩ : T ) ∈ s from ht.1 hy.2 ) ; simp_all +decide
            exact h this;
          · exact Nat.pred_lt ( ne_bot_of_gt ha );
        refine Or.inl ?_;
        refine' le_csSup _ _;
        · exact ⟨ _, fun n hn => hn.choose_spec.card_eq ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ K, by rw [ SimpleGraph.isNClique_iff ] ; aesop ⟩;
      · -- Let $I$ be an independent set of size $b-1$ in $G[T]$.
        obtain ⟨I, hI⟩ : ∃ I : Finset (Fin (N1 + N2)), I.card = b - 1 ∧ I ⊆ T ∧ ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬G.Adj x y := by
          contrapose! h;
          refine' lt_of_le_of_lt ( csSup_le' _ ) _;
          exact b - 2;
          · rintro n ⟨ s, hs ⟩;
            rcases hs with ⟨ hs₁, hs₂ ⟩;
            contrapose! h;
            obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( show b - 1 ≤ s.card from by omega );
            use t.image (fun x => x.val);
            simp_all +decide [ Finset.subset_iff ];
            exact ⟨ by rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ; linarith, fun x hx₁ hx₂ y hy₁ hy₂ hxy => by have := hs₁ ( ht.1 x hx₁ hx₂ ) ( ht.1 y hy₁ hy₂ ) ; aesop ⟩;
          · omega;
        -- Since $I \subseteq T \subseteq N^c(v)$, $v$ is not adjacent to any vertex in $I$ (and $v \notin I$).
        have h_not_adj : ∀ x ∈ I, ¬G.Adj v x := by
          intro x hx; specialize hT; have := hT.2 ( hI.2.1 hx ) ; aesop;
        have h_not_mem : v ∉ I := by
          intro H; have := hT.2 ( hI.2.1 H ) ; aesop;
        -- By `indep_extension`, $I \cup \{v\}$ is an independent set of size $b$ in $G$.
        have h_indep : ∃ I' : Finset (Fin (N1 + N2)), I'.card = b ∧ I' ⊆ Finset.univ ∧ ∀ x ∈ I', ∀ y ∈ I', x ≠ y → ¬G.Adj x y := by
          use Insert.insert v I;
          simp_all +decide [ Finset.subset_iff ];
          exact ⟨ Nat.succ_pred_eq_of_pos ( pos_of_gt hb ), fun x hx => by have := hT.2 ( hI.2.1 hx ) ; tauto ⟩;
        obtain ⟨ I', hI'₁, hI'₂, hI'₃ ⟩ := h_indep;
        refine Or.inr ?_;
        refine' le_csSup _ _;
        · exact ⟨ _, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ I', by rw [ SimpleGraph.isNIndepSet_iff ] ; aesop ⟩

/-
Ramsey property holds for the Erdos-Szekeres bound.
-/
theorem ramsey_upper_bound_prop (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
  Ramsey_prop a b (Nat.choose (a + b - 2) (a - 1)) := by
    induction' a using Nat.strong_induction_on with a ih generalizing b;
    induction' b using Nat.strong_induction_on with b ih;
    rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp_all +arith +decide;
    -- By the induction hypothesis, we know that Ramsey_prop (a + 1) (b + 2) ((a + b + 1).choose (a)) holds.
    have h_ind_a : Ramsey_prop (a + 1) (b + 2) ((a + b + 1).choose (a)) := by
      rcases a with ( _ | a ) <;> simp_all +arith +decide;
      · intro G; simp +decide [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ] ;
        refine' Or.inl ( le_csSup _ _ );
        · exact ⟨ 1, by rintro n ⟨ s, hs ⟩ ; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ { 0 }, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩;
      · convert ‹∀ m ≤ a + 2, ∀ b : ℕ, 2 ≤ m → 2 ≤ b → Ramsey_prop m b ( ( m + b - 2 ).choose ( m - 1 ) ) › ( a + 2 ) ( by linarith ) ( b + 2 ) ( by linarith ) ( by linarith ) using 1;
        grind;
    -- By the induction hypothesis, we know that Ramsey_prop (a + 2) (b + 1) ((a + b + 1).choose (a + 1)) holds.
    have h_ind_b : Ramsey_prop (a + 2) (b + 1) ((a + b + 1).choose (a + 1)) := by
      by_cases hb : b + 1 ≥ 2;
      · exact ih _ le_rfl hb;
      · interval_cases _ : b + 1 <;> simp_all +decide;
        intro G; simp +decide [ SimpleGraph.cliqueNum ] ;
        refine' Or.inr _;
        refine' le_csSup _ _ <;> norm_num;
        · exact ⟨ 1, by rintro n ⟨ s, hs ⟩ ; exact hs.card_eq.symm ▸ Finset.card_le_univ _ ⟩;
        · exact ⟨ { 0 }, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩;
    convert ramsey_step ( a + 2 ) ( b + 2 ) ( Nat.choose ( a + b + 1 ) a ) ( Nat.choose ( a + b + 1 ) ( a + 1 ) ) ( by linarith ) ( by linarith ) h_ind_a h_ind_b using 1

/-
Upper bound for binomial coefficient: binom(N, m) <= (eN/m)^m.
-/
theorem lemma_binom (N m : ℕ) (hm : 1 ≤ m) :
  (Nat.choose N m : ℝ) ≤ (Real.exp 1 * N / m) ^ m := by
    -- Using the fact that $m! \geq (m/e)^m$, we can derive that $\binom{N}{m} \leq \frac{N^m}{(m/e)^m} = \left(\frac{eN}{m}\right)^m$.
    have h_binom_le : (Nat.choose N m : ℝ) ≤ N^m / (m^m / Real.exp m) := by
      rw [ le_div_iff₀ ( by positivity ) ];
      -- Using the fact that $m! \geq (m/e)^m$, we can derive that $\frac{N!}{m!(N-m)!} \leq \frac{N^m}{(m/e)^m}$.
      have h_factorial : (Nat.factorial m : ℝ) ≥ (m / Real.exp 1) ^ m := by
        field_simp;
        rw [ div_pow, div_le_iff₀ ] <;> norm_num [ Real.exp_pos ];
        rw [ Real.exp_eq_exp_ℝ ];
        rw [ ← div_le_iff₀' ( by positivity ), NormedSpace.exp_eq_tsum_div ];
        exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) m ( fun _ _ => by positivity );
      have h_choose : (Nat.choose N m : ℝ) ≤ N^m / (Nat.factorial m : ℝ) := by
        exact Nat.choose_le_pow_div m N;
      rw [ le_div_iff₀ ( by positivity ) ] at h_choose;
      exact le_trans ( mul_le_mul_of_nonneg_left ( by simpa [ div_pow, Real.exp_nat_mul ] using h_factorial ) ( Nat.cast_nonneg _ ) ) h_choose;
    convert h_binom_le using 1 ; ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, ← Real.exp_nat_mul ]

/-
Corollary: R(km,m) <= (e(k+1))^m.
-/
theorem cor_ramsey_km (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
  (R (k * m) m : ℝ) ≤ (Real.exp 1 * (k + 1)) ^ m := by
    -- First, let's use Lemma~\ref{lem:ES} to get an upper bound for $R(km, m)$ in terms of binomial coefficients.
    have h_ES : R (k * m) m ≤ Nat.choose (k * m + m - 2) (k * m - 1) := by
      by_cases hkm : 2 ≤ k * m <;> by_cases hm₂ : 2 ≤ m <;> simp_all +decide [ R ];
      · refine' Nat.sInf_le _;
        exact ramsey_upper_bound_prop _ _ hkm hm₂;
      · interval_cases m ; simp_all +decide;
        refine' Nat.le_trans ( Nat.sInf_le _ ) _;
        exact 1;
        · intro G;
          refine' Or.inr _;
          refine' le_csSup _ _ <;> norm_num;
          · exact ⟨ 1, by rintro n ⟨ s, hs ⟩ ; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
          · exact ⟨ { 0 }, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩;
        · norm_num;
      · nlinarith;
      · interval_cases m ; simp_all +decide;
        interval_cases k ; simp_all +decide [ Ramsey_prop ];
        refine' Nat.sInf_le _;
        intro G; exact Or.inl ( by exact le_csSup ⟨ 1, by rintro x ⟨ s, hs ⟩ ; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩ ⟨ { 0 }, by simp +decide ⟩ ) ;
    have h_binom : Nat.choose (k * m + m - 2) (k * m - 1) ≤ Nat.choose ((k + 1) * m) m := by
      rcases m with ( _ | _ | m ) <;> simp_all +decide [ add_mul ];
      rw [ Nat.choose_symm_of_eq_add ] ; simp +arith +decide
      any_goals exact m + 1 + 1 - 1;
      · simp +arith +decide [ Nat.choose_succ_succ ];
      · grind;
    refine' le_trans ( Nat.cast_le.mpr ( h_ES.trans h_binom ) ) _;
    convert lemma_binom ( ( k + 1 ) * m ) m hm using 1 ; norm_num [ mul_pow, mul_comm ];
    rw [ mul_assoc, mul_div_cancel_left₀ _ ( by positivity ) ];
    rw [ mul_pow, ← Real.exp_nat_mul ] ; ring_nf

/-
dif(x,y) is the size of the symmetric difference of the neighborhoods of x and y.
-/
def dif_size {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℕ :=
  (symmDiff (G.neighborFinset x) (G.neighborFinset y)).card

/-
Helper lemma: exp(-pT) = n^(-20/ln 2).
-/
noncomputable def param_p (γ : ℝ) (n : ℕ) : ℝ := γ / Real.logb 2 n

noncomputable def param_T (γ : ℝ) (n : ℕ) : ℝ := 20 / γ * (Real.logb 2 n)^2

theorem prob_bound_aux (γ : ℝ) (n : ℕ) (hγ : 0 < γ) (hn : 2 ≤ n) :
  let p := param_p γ n
  let T := param_T γ n
  Real.exp (-p * T) = (n : ℝ) ^ (-20 / Real.log 2) := by
    unfold param_p param_T;
    -- Substitute p and T into the exponent and simplify.
    field_simp [Real.logb]
    ring_nf;
    norm_num [ Real.logb, Real.rpow_def_of_pos ( by positivity : 0 < ( n : ℝ ) ) ] ; ring

/-
Definition of Bernoulli weight and proof that they sum to 1.
-/
noncomputable def bernoulli_weight {V : Type*} [Fintype V] (p : ℝ) (A : Finset V) : ℝ :=
  p ^ A.card * (1 - p) ^ (Fintype.card V - A.card)

theorem sum_bernoulli_weight {V : Type*} [Fintype V] (p : ℝ) :
  ∑ A : Finset V, bernoulli_weight p A = 1 := by
    have h_sum : ∑ A : Finset V, p ^ A.card * (1 - p) ^ (Fintype.card V - A.card) = (p + (1 - p)) ^ Fintype.card V := by
      exact Fintype.sum_pow_mul_eq_add_pow V p (1 - p);
    aesop

/-
Probability that random set A is disjoint from D is (1-p)^|D|.
-/
theorem sum_bernoulli_weight_disjoint {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) (D : Finset V) :
  ∑ A ∈ Finset.univ.filter (fun A => Disjoint A D), bernoulli_weight p A = (1 - p) ^ D.card := by
    have h_disjoint : ∑ A ∈ Finset.powerset (Finset.univ \ D), bernoulli_weight p A = (1 - p)^D.card := by
      have h_sum_subset : ∑ A ∈ Finset.powerset (Finset.univ \ D), bernoulli_weight p A = (1 - p) ^ D.card * ∑ A ∈ Finset.powerset (Finset.univ \ D), p ^ A.card * (1 - p) ^ ((Finset.univ \ D).card - A.card) := by
        simp +decide only [bernoulli_weight];
        rw [ Finset.mul_sum _ _ _ ];
        refine' Finset.sum_congr rfl fun x hx => _;
        simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
        rw [ show Fintype.card V - x.card = ( Fintype.card V - D.card ) - x.card + D.card by rw [ tsub_right_comm, tsub_add_cancel_of_le ( Nat.le_sub_of_add_le' <| by linarith [ show x.card + D.card ≤ Fintype.card V from by rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun y hyx hyD => hx hyx hyD ) ] ; exact Finset.card_le_univ _ ] ) ] ] ; ring;
      have h_sum_subset : ∑ A ∈ Finset.powerset (Finset.univ \ D), p ^ A.card * (1 - p) ^ ((Finset.univ \ D).card - A.card) = (p + (1 - p)) ^ ((Finset.univ \ D).card) := by
        rw [ add_pow ];
        rw [ Finset.sum_powerset ];
        exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm ] ;
      aesop;
    convert h_disjoint using 2 ; ext ; simp +decide [ Finset.disjoint_left ];
    simp +decide [ Finset.subset_iff ]

/-
Probability of an event E under Bernoulli distribution.
-/
noncomputable def prob_event {V : Type*} [Fintype V] (p : ℝ) (E : Set (Finset V)) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A => A ∈ E), bernoulli_weight p A

/-
Probability that random set A is disjoint from D is (1-p)^|D|.
-/
theorem prob_disjoint_eq {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) (D : Finset V) :
  prob_event p {A | Disjoint A D} = (1 - p) ^ D.card := by
    unfold prob_event;
    convert sum_bernoulli_weight_disjoint p D using 1;
    simp +decide [ Finset.disjoint_left ]

/-
Expectation of |A| is p*n.
-/
theorem expectation_card {V : Type*} [Fintype V] (p : ℝ) :
  ∑ A : Finset V, (A.card : ℝ) * bernoulli_weight p A = p * Fintype.card V := by
    -- We can rewrite the sum as a product over the vertices.
    have h_prod : ∑ A : Finset V, (A.card : ℝ) * bernoulli_weight p A = ∑ v : V, ∑ A : Finset V, (if v ∈ A then p ^ A.card * (1 - p) ^ (Fintype.card V - A.card) else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    -- For each vertex $v$, the sum $\sum_{A \ni v} p^{|A|} (1-p)^{n-|A|}$ is equal to $p$.
    have h_vertex : ∀ v : V, ∑ A : Finset V, (if v ∈ A then p ^ A.card * (1 - p) ^ (Fintype.card V - A.card) else 0) = p := by
      intro v
      have h_vertex_sum : ∑ A ∈ Finset.powerset (Finset.univ.erase v), p ^ (A.card + 1) * (1 - p) ^ (Fintype.card V - (A.card + 1)) = p := by
        have h_vertex_sum : ∑ A ∈ Finset.powerset (Finset.univ.erase v), p ^ A.card * (1 - p) ^ (Fintype.card V - 1 - A.card) = 1 := by
          have h_vertex_sum : ∑ A ∈ Finset.powerset (Finset.univ.erase v), p ^ A.card * (1 - p) ^ (Finset.card (Finset.univ.erase v) - A.card) = (p + (1 - p)) ^ (Finset.card (Finset.univ.erase v)) := by
            exact Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ.erase v);
          aesop;
        convert congr_arg ( fun x => p * x ) h_vertex_sum using 1 <;> ring_nf;
        simp +decide only [mul_assoc, tsub_tsub, Finset.mul_sum _ _ _];
      rw [ ← Finset.sum_filter ];
      convert h_vertex_sum using 1;
      refine' Finset.sum_bij ( fun A hA => A.erase v ) _ _ _ _ <;> simp +decide;
      · exact fun A hv => Finset.erase_subset_erase _ ( Finset.subset_univ _ );
      · intro a₁ hv₁ a₂ hv₂ h; rw [ ← Finset.insert_erase hv₁, ← Finset.insert_erase hv₂, h ] ;
      · exact fun b hb => ⟨ Insert.insert v b, Finset.mem_insert_self _ _, by rw [ Finset.erase_insert ( Finset.notMem_mono hb ( Finset.notMem_erase _ _ ) ) ] ⟩;
      · intro A hv; rw [ Finset.card_erase_add_one hv ] ;
    simp_all +decide [ mul_comm ]

/-
Bound on failure probability for one pair: (1-p)^T <= n^(-20/ln 2).
-/
theorem prob_bound_main_v3 (γ : ℝ) (n : ℕ) (hγ : 0 < γ ∧ γ < 1) (hn : 2 ≤ n) :
  let p := param_p γ n
  let T := param_T γ n
  (1 - p) ^ T ≤ (n : ℝ) ^ (-20 / Real.log 2) := by
    -- Apply `pow_le_exp_mul` with $p = \gamma / \log_2 n$ and $T = 20 / \gamma * (\log_2 n)^2$.
    have h_exp : (1 - param_p γ n) ^ (param_T γ n) ≤ Real.exp (-param_p γ n * param_T γ n) := by
      convert Real.rpow_le_rpow _ _ _ using 1;
      rw [ ← Real.exp_mul ];
      · exact sub_nonneg.2 ( div_le_one_of_le₀ ( by nlinarith [ show 1 ≤ Real.logb 2 n by rw [ Real.le_logb_iff_rpow_le ] <;> norm_num <;> linarith ] ) ( Real.logb_nonneg ( by norm_num ) ( by norm_cast ; linarith ) ) );
      · linarith [ Real.add_one_le_exp ( -param_p γ n ) ];
      · exact mul_nonneg ( div_nonneg ( by norm_num ) hγ.1.le ) ( sq_nonneg _ );
    -- Apply `prob_bound_aux` to get $e^{-pT} = n^{-20/\ln 2}$.
    have h_aux : Real.exp (-param_p γ n * param_T γ n) = (n : ℝ) ^ (-20 / Real.log 2) := by
      apply prob_bound_aux γ n hγ.left hn;
    exact h_aux ▸ h_exp

/-
Helper for Markov: k * P(X >= k) <= E[X].
-/
open Classical

theorem sum_ge_k_le_expectation {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) (k : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  k * prob_event p {A : Finset V | k ≤ A.card} ≤ ∑ A : Finset V, (A.card : ℝ) * bernoulli_weight p A := by
    unfold prob_event;
    rw [ Finset.mul_sum _ _ _ ];
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) _;
    exact Finset.univ.filter fun A => k ≤ A.card;
    · aesop_cat;
    · aesop;
    · refine' le_trans ( Finset.sum_le_sum fun A hA => mul_le_mul_of_nonneg_right ( Finset.mem_filter.mp hA |>.2 ) ( show 0 ≤ bernoulli_weight p A from _ ) ) _;
      · exact mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ );
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ ) )

/-
Markov's inequality for cardinality of random set.
-/
open Classical

theorem markov_inequality_card {V : Type*} [Fintype V] [DecidableEq V] (p : ℝ) (k : ℝ) (hk : 0 < k) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  prob_event p {A : Finset V | k ≤ A.card} ≤ (p * Fintype.card V) / k := by
    rw [ le_div_iff₀' hk ];
    convert sum_ge_k_le_expectation p k hp hp1 using 1;
    · exact Eq.symm (expectation_card p);
    · infer_instance

/-
The probability that there exists a pair (x,y) with large difference that is not distinguished by A is small.
-/
def DifFinset {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Finset V :=
  symmDiff (G.neighborFinset x) (G.neighborFinset y)

def BadPairsEvent {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℝ) : Set (Finset V) :=
  {A | ∃ x y : V, x ≠ y ∧ (dif_size G x y : ℝ) ≥ T ∧ Disjoint A (DifFinset G x y)}

theorem prob_bad_pairs_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n) (p T : ℝ) (hp : 0 ≤ p ∧ p < 1) :
    prob_event p (BadPairsEvent G T) ≤ (n : ℝ) ^ 2 * (1 - p) ^ T := by
      have h_union_bound : prob_event p (BadPairsEvent G T) ≤ ∑ x : V, ∑ y : V, prob_event p {A : Finset V | x ≠ y ∧ T ≤ dif_size G x y ∧ Disjoint A (Finset.filter (fun w => (G.Adj x w ∧ ¬G.Adj y w) ∨ (G.Adj y w ∧ ¬G.Adj x w)) (Finset.univ : Finset V))} := by
        have h_union_bound : prob_event p (BadPairsEvent G T) ≤ ∑ x : V, ∑ y : V, prob_event p {A : Finset V | x ≠ y ∧ T ≤ dif_size G x y ∧ Disjoint A (symmDiff (G.neighborFinset x) (G.neighborFinset y))} := by
          have h_event : BadPairsEvent G T = ⋃ x : V, ⋃ y : V, {A : Finset V | x ≠ y ∧ T ≤ dif_size G x y ∧ Disjoint A (symmDiff (G.neighborFinset x) (G.neighborFinset y))} := by
            ext A; simp [BadPairsEvent];
            congr! 7;
            ext; simp [DifFinset, symmDiff]
          rw [h_event];
          have h_union_bound : ∀ (S : Finset (V × V)), prob_event p (⋃ x ∈ S, {A : Finset V | x.1 ≠ x.2 ∧ T ≤ dif_size G x.1 x.2 ∧ Disjoint A (symmDiff (G.neighborFinset x.1) (G.neighborFinset x.2))}) ≤ ∑ x ∈ S, prob_event p {A : Finset V | x.1 ≠ x.2 ∧ T ≤ dif_size G x.1 x.2 ∧ Disjoint A (symmDiff (G.neighborFinset x.1) (G.neighborFinset x.2))} := by
            intro S;
            induction' S using Finset.induction with x S hxS ih;
            · simp +decide [ prob_event ];
            · simp_all +decide [ Finset.sum_insert hxS ];
              refine' le_trans _ ( add_le_add_left ih _ );
              unfold prob_event;
              rw [ ← Finset.sum_union_inter ];
              exact le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by aesop ) fun _ _ _ => mul_nonneg ( pow_nonneg hp.1 _ ) ( pow_nonneg ( sub_nonneg.2 hp.2.le ) _ ) ) ( Finset.sum_nonneg fun _ _ => mul_nonneg ( pow_nonneg hp.1 _ ) ( pow_nonneg ( sub_nonneg.2 hp.2.le ) _ ) );
          convert h_union_bound ( Finset.univ.product Finset.univ ) using 1;
          · congr! 1;
            ext; simp
          · erw [ Finset.sum_product ];
        convert h_union_bound using 1;
        simp +decide [ Finset.disjoint_left, symmDiff ];
      -- For a fixed pair $(x, y)$, if $x \neq y$ and $T \leq \text{dif}(x, y)$, then the event is $\{A \mid \text{Disjoint } A (\text{Dif}(x, y))\}$.
      have h_fixed_pair : ∀ x y : V, x ≠ y → T ≤ dif_size G x y → prob_event p {A : Finset V | Disjoint A (Finset.filter (fun w => (G.Adj x w ∧ ¬G.Adj y w) ∨ (G.Adj y w ∧ ¬G.Adj x w)) (Finset.univ : Finset V))} ≤ (1 - p) ^ T := by
        intros x y hxy hTxy
        have h_event : prob_event p {A : Finset V | Disjoint A (Finset.filter (fun w => (G.Adj x w ∧ ¬G.Adj y w) ∨ (G.Adj y w ∧ ¬G.Adj x w)) (Finset.univ : Finset V))} = (1 - p) ^ (dif_size G x y) := by
          convert prob_disjoint_eq p ( Finset.filter ( fun w => ( G.Adj x w ∧ ¬G.Adj y w ) ∨ ( G.Adj y w ∧ ¬G.Adj x w ) ) Finset.univ ) using 1;
          simp +decide [ dif_size ];
          congr with w ; simp +decide [ SimpleGraph.neighborFinset, symmDiff ];
        exact h_event.symm ▸ by simpa using Real.rpow_le_rpow_of_exponent_ge ( by linarith ) ( by linarith ) hTxy;
      refine' le_trans h_union_bound ( le_trans ( Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => _ ) _ );
      use fun x y => if x ≠ y ∧ T ≤ dif_size G x y then ( 1 - p ) ^ T else 0;
      · split_ifs with h <;> simp_all +decide
        by_cases hxy : x = y <;> simp_all +decide [ not_le_of_gt ];
        · simp +decide [ prob_event ];
        · simp +decide [ prob_event ];
      · simp +decide [ ← Finset.sum_filter, hn.symm ];
        rw [ ← Finset.sum_mul _ _ _ ];
        exact mul_le_mul_of_nonneg_right ( mod_cast le_trans ( Finset.sum_le_sum fun _ _ => Finset.card_le_univ _ ) ( by simp +decide [ sq ] ) ) ( Real.rpow_nonneg ( sub_nonneg.2 hp.2.le ) _ )

/-
Definition of two vertices having the same adjacency to a set A.
-/
def same_adj_to_A {V : Type*} (G : SimpleGraph V) (A : Finset V) (x y : V) : Prop :=
  ∀ a ∈ A, G.Adj a x ↔ G.Adj a y

/-
The probability that a random set is empty is small for large n.
-/
theorem lemma_prob_empty_small (γ : ℝ) (hγ : 0 < γ) :
    ∃ n₀, ∀ n ≥ n₀,
    let p := param_p γ n
    (1 - p) ^ n < 1 / 4 := by
      -- Since $\gamma > 0$, $\gamma n / \log_2 n \to \infty$ as $n \to \infty$.
      have h_gamma_n_log2_n_inf : Filter.Tendsto (fun n : ℕ => γ * (n : ℝ) / Real.logb 2 n) Filter.atTop Filter.atTop := by
        -- We can use the fact that $\frac{n}{\log_2 n}$ grows to infinity as $n$ tends to infinity.
        have h_log_growth : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) Filter.atTop Filter.atTop := by
          -- We can use the change of variables $u = \log n$ to transform the limit expression.
          suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
            have := h_log.comp Real.tendsto_log_atTop;
            exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
          simpa using Real.tendsto_exp_div_pow_atTop 1;
        convert h_log_growth.const_mul_atTop ( show 0 < γ * Real.log 2 by positivity ) using 2 ; norm_num [ Real.logb, mul_div_assoc ];
        group;
      -- Since $\gamma n / \log_2 n \to \infty$ as $n \to \infty$, we have $(1 - \gamma / \log_2 n)^n \to 0$ as $n \to \infty$.
      have h_exp_zero : Filter.Tendsto (fun n : ℕ => (1 - γ / Real.logb 2 n) ^ n) Filter.atTop (nhds 0) := by
        have h_exp_zero : Filter.Tendsto (fun n : ℕ => Real.exp (-γ * (n : ℝ) / Real.logb 2 n)) Filter.atTop (nhds 0) := by
          simpa [ neg_div ] using h_gamma_n_log2_n_inf;
        refine' squeeze_zero_norm' _ h_exp_zero;
        -- Since $1 - \frac{\gamma}{\log_2 n}$ is positive for sufficiently large $n$, we can drop the absolute value.
        have h_pos : ∀ᶠ n in Filter.atTop, 0 < 1 - γ / Real.logb 2 n := by
          have h_pos : Filter.Tendsto (fun n : ℝ => γ / Real.logb 2 n) Filter.atTop (nhds 0) := by
            exact tendsto_const_nhds.div_atTop ( Real.tendsto_logb_atTop ( by norm_num ) );
          exact h_pos.eventually ( gt_mem_nhds zero_lt_one ) |> fun h => h.mono fun n hn => by linarith;
        filter_upwards [ h_pos.natCast_atTop ] with n hn using by rw [ Real.norm_of_nonneg ( pow_nonneg hn.le _ ) ] ; exact le_trans ( pow_le_pow_left₀ ( by linarith ) ( show ( 1 - γ / Real.logb 2 n ) ≤ Real.exp ( -γ / Real.logb 2 n ) by exact le_trans ( by ring_nf; norm_num ) ( Real.add_one_le_exp _ ) ) _ ) ( by rw [ ← Real.exp_nat_mul ] ; ring_nf; norm_num ) ;
      simpa using h_exp_zero.eventually ( gt_mem_nhds <| by norm_num )

/-
The probability of bad pairs is small for large n.
-/
theorem lemma_prob_bad_pairs_small (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    ∃ n₀, ∀ n ≥ n₀,
    let p := param_p γ n
    let T := param_T γ n
    (n : ℝ) ^ 2 * (1 - p) ^ T < 1 / 4 := by
      have h_exp : ∃ n₀, ∀ n ≥ n₀, (n : ℝ) ^ 2 * (n : ℝ) ^ (-20 / Real.log 2) < 1 / 4 := by
        have h_exp : Filter.Tendsto (fun n : ℝ => n ^ 2 * (n : ℝ) ^ (-20 / Real.log 2)) Filter.atTop (nhds 0) := by
          have h_exp : Filter.Tendsto (fun n : ℝ => n ^ (2 - 20 / Real.log 2)) Filter.atTop (nhds 0) := by
            simpa using tendsto_rpow_neg_atTop ( show 0 < - ( 2 - 20 / Real.log 2 ) by nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, mul_div_cancel₀ 20 ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] );
          refine h_exp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ ← Real.rpow_natCast, ← Real.rpow_add hn ] ; ring_nf );
        simpa using h_exp.eventually ( gt_mem_nhds <| by norm_num );
      obtain ⟨ n₀, hn₀ ⟩ := h_exp;
      refine' ⟨ ⌈n₀⌉₊ + 2, fun n hn => lt_of_le_of_lt _ ( hn₀ n ( Nat.le_of_ceil_le ( by linarith ) ) ) ⟩;
      gcongr;
      convert prob_bound_main_v3 γ n hγ ( by linarith ) using 1

/-
The probability that the random set A is too large is at most 1/2.
-/
theorem lemma_prob_size_large {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : Fintype.card V = n)
    (γ : ℝ) (hγ : 0 < γ) (hn_ge_2 : 2 ≤ n) :
    let p := param_p γ n
    let k := 2 * γ * n / Real.logb 2 n
    prob_event p {A : Finset V | k < A.card} ≤ 1 / 2 := by
      have h_markov : prob_event (γ / Real.logb 2 n) {A : Finset V | (A.card : ℝ) > 2 * γ * n / Real.logb 2 n} ≤ (γ * n / Real.logb 2 n) / (2 * γ * n / Real.logb 2 n) := by
        have := @markov_inequality_card V;
        by_cases h : γ / Real.logb 2 n ≤ 1;
        · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) _;
          exact Finset.univ.filter fun A => ( A.card : ℝ ) ≥ 2 * γ * n / Real.logb 2 n;
          · grind;
          · exact fun _ _ _ => mul_nonneg ( pow_nonneg ( div_nonneg hγ.le ( Real.logb_nonneg ( by norm_num ) ( by norm_cast; linarith ) ) ) _ ) ( pow_nonneg ( sub_nonneg.2 h ) _ );
          · convert this ( γ / Real.logb 2 n ) ( 2 * γ * n / Real.logb 2 n ) _ _ h using 1 <;> norm_num [ hn ];
            · ring;
            · exact div_pos ( mul_pos ( mul_pos zero_lt_two hγ ) ( Nat.cast_pos.mpr ( zero_lt_two.trans_le hn_ge_2 ) ) ) ( Real.logb_pos ( by norm_num ) ( by norm_cast ) );
            · exact div_nonneg hγ.le ( Real.logb_nonneg ( by norm_num ) ( by norm_cast; linarith ) );
        · refine' le_trans ( Finset.sum_nonpos _ ) _;
          · simp +zetaDelta at *;
            intro A hA;
            rw [ div_lt_iff₀ ( Real.logb_pos ( by norm_num ) ( by norm_cast ) ) ] at hA;
            exact False.elim ( hA.not_ge ( by rw [ lt_div_iff₀ ( Real.logb_pos ( by norm_num ) ( by norm_cast ) ) ] at h; nlinarith [ show ( A.card : ℝ ) ≤ n by exact_mod_cast hn ▸ Finset.card_le_univ A, Real.logb_pos ( by norm_num : ( 1 : ℝ ) < 2 ) ( by norm_cast : ( 1 : ℝ ) < n ) ] ) );
          · grind;
      convert h_markov using 1 ; rw [ div_eq_mul_inv ] ; ring_nf ; norm_num [ show n ≠ 0 by linarith, show γ ≠ 0 by linarith, show Real.logb 2 n ≠ 0 by exact ne_of_gt ( Real.logb_pos ( by norm_num ) ( by norm_cast ) ) ];
      linear_combination' mul_inv_cancel₀ hγ.ne' * mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) * mul_inv_cancel₀ ( ne_of_gt ( Real.logb_pos one_lt_two ( by norm_cast ) : 0 < Real.logb 2 n ) )

/-
Lemma 3: There exists a small set A distinguishing all pairs with large difference.
-/
theorem lemma_distinguish (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    ∃ n₀, ∀ {V : Type*} [Fintype V] [DecidableEq V], ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    ∀ n, Fintype.card V = n → n ≥ n₀ →
    let T := param_T γ n
    ∃ A : Finset V, A.Nonempty ∧
      (A.card : ℝ) ≤ 2 * γ * n / Real.logb 2 n ∧
      ∀ x y : V, x ∉ A → y ∉ A →
        same_adj_to_A G A x y →
        (dif_size G x y : ℝ) < T := by
          -- Let n₀ be large enough for all lemmas.
          obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ (n : ℕ) (hn : n ≥ n₀),
            let p := param_p γ n
            let T := param_T γ n
            (1 - p) ^ n < 1 / 4 ∧ (n : ℝ) ^ 2 * (1 - p) ^ T < 1 / 4 ∧ (1 / 2 : ℝ) ≤ 1 := by
              obtain ⟨ n₀₁, hn₁ ⟩ := lemma_prob_empty_small γ hγ.1; obtain ⟨ n₀₂, hn₂ ⟩ := lemma_prob_bad_pairs_small γ hγ; exact ⟨ Max.max n₀₁ n₀₂, fun n hn => ⟨ hn₁ n ( le_trans ( le_max_left _ _ ) hn ), hn₂ n ( le_trans ( le_max_right _ _ ) hn ), by norm_num ⟩ ⟩ ;
          use n₀ + 2;
          -- By the union bound, the probability that the random set A is empty, has size greater than 2γn/log n, or is bad is at most 1/4 + 1/2 + 1/4 = 1.
          intros V _ _ G _ n hn hn_ge
          have h_union : prob_event (param_p γ n) {A : Finset V | A = ∅ ∨ (2 * γ * n / Real.logb 2 n : ℝ) < A.card ∨ A ∈ BadPairsEvent G (param_T γ n)} < 1 := by
            have h_union : prob_event (param_p γ n) {A : Finset V | A = ∅ ∨ (2 * γ * n / Real.logb 2 n : ℝ) < A.card ∨ A ∈ BadPairsEvent G (param_T γ n)} ≤ prob_event (param_p γ n) {A : Finset V | A = ∅} + prob_event (param_p γ n) {A : Finset V | (2 * γ * n / Real.logb 2 n : ℝ) < A.card} + prob_event (param_p γ n) (BadPairsEvent G (param_T γ n)) := by
              have h_union_bound : ∀ (E₁ E₂ E₃ : Set (Finset V)), prob_event (param_p γ n) (E₁ ∪ E₂ ∪ E₃) ≤ prob_event (param_p γ n) E₁ + prob_event (param_p γ n) E₂ + prob_event (param_p γ n) E₃ := by
                intros E₁ E₂ E₃
                have h_union_bound : prob_event (param_p γ n) (E₁ ∪ E₂ ∪ E₃) ≤ prob_event (param_p γ n) E₁ + prob_event (param_p γ n) E₂ + prob_event (param_p γ n) E₃ := by
                  have h_union_bound : ∀ (E₁ E₂ : Set (Finset V)), prob_event (param_p γ n) (E₁ ∪ E₂) ≤ prob_event (param_p γ n) E₁ + prob_event (param_p γ n) E₂ := by
                    intros E₁ E₂
                    have h_union_bound : prob_event (param_p γ n) (E₁ ∪ E₂) ≤ prob_event (param_p γ n) E₁ + prob_event (param_p γ n) E₂ := by
                      have h_union_bound : ∀ (A : Finset V), A ∈ E₁ ∪ E₂ → A ∈ E₁ ∨ A ∈ E₂ := by
                        exact fun A hA => hA
                      have h_union_bound : ∑ A ∈ Finset.univ.filter (fun A => A ∈ E₁ ∪ E₂), bernoulli_weight (param_p γ n) A ≤ ∑ A ∈ Finset.univ.filter (fun A => A ∈ E₁), bernoulli_weight (param_p γ n) A + ∑ A ∈ Finset.univ.filter (fun A => A ∈ E₂), bernoulli_weight (param_p γ n) A := by
                        rw [ ← Finset.sum_union_inter ];
                        exact le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset_of_nonneg ( by aesop_cat ) fun _ _ _ => by exact mul_nonneg ( pow_nonneg ( by exact div_nonneg ( by linarith ) ( Real.logb_nonneg ( by norm_num ) ( by norm_cast; linarith ) ) ) _ ) ( pow_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( by linarith [ show ( γ : ℝ ) ≤ 1 by linarith, show ( Real.logb 2 n : ℝ ) ≥ 1 by rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_cast <;> linarith ] ) <| by linarith [ show ( γ : ℝ ) ≤ 1 by linarith, show ( Real.logb 2 n : ℝ ) ≥ 1 by rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_cast <;> linarith ] ) _ ) ) ( Finset.sum_nonneg fun _ _ => by exact mul_nonneg ( pow_nonneg ( by exact div_nonneg ( by linarith ) ( Real.logb_nonneg ( by norm_num ) ( by norm_cast; linarith ) ) ) _ ) ( pow_nonneg ( sub_nonneg.2 <| div_le_one_of_le₀ ( by linarith [ show ( γ : ℝ ) ≤ 1 by linarith, show ( Real.logb 2 n : ℝ ) ≥ 1 by rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_cast <;> linarith ] ) <| by linarith [ show ( γ : ℝ ) ≤ 1 by linarith, show ( Real.logb 2 n : ℝ ) ≥ 1 by rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_cast <;> linarith ] ) _ ) );
                      unfold prob_event; aesop;
                    exact h_union_bound
                  exact le_trans ( h_union_bound _ _ ) ( add_le_add_right ( h_union_bound _ _ ) _ );
                exact h_union_bound;
              convert h_union_bound _ _ _ using 2 ; ext ; aesop;
            have h_empty : prob_event (param_p γ n) {A : Finset V | A = ∅} = (1 - param_p γ n) ^ n := by
              unfold prob_event;
              simp +decide [ hn, bernoulli_weight ];
              rw [ Finset.sum_eq_single ∅ ] <;> aesop;
            have := hn₀ n ( by linarith );
            -- Apply the bounds from the lemmas to each term in the union bound.
            have h_bounds : prob_event (param_p γ n) {A : Finset V | (2 * γ * n / Real.logb 2 n : ℝ) < A.card} ≤ 1 / 2 ∧ prob_event (param_p γ n) (BadPairsEvent G (param_T γ n)) < 1 / 4 := by
              apply And.intro;
              · convert lemma_prob_size_large n hn γ hγ.1 ( by linarith ) using 1;
              · apply lt_of_le_of_lt (prob_bad_pairs_le G n hn (param_p γ n) (param_T γ n) ⟨by
                exact div_nonneg hγ.1.le ( Real.logb_nonneg ( by norm_num ) ( by norm_cast; linarith ) ), by
                  unfold param_p;
                  rw [ div_lt_iff₀ ( Real.logb_pos ( by norm_num ) ( by norm_cast; linarith ) ) ];
                  rw [ one_mul, Real.lt_logb_iff_rpow_lt ] <;> norm_num <;> try linarith;
                  exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) hγ.2 ) ( by norm_num; linarith [ show ( n : ℝ ) ≥ 2 by norm_cast; linarith ] )⟩) this.right.left;
            linarith [ this.1, h_empty ];
          -- Therefore, there exists a set A that is not in the union of the bad events.
          obtain ⟨A, hA⟩ : ∃ A : Finset V, ¬(A = ∅ ∨ (2 * γ * n / Real.logb 2 n : ℝ) < A.card ∨ A ∈ BadPairsEvent G (param_T γ n)) := by
            contrapose! h_union;
            rw [ show { A : Finset V | A = ∅ ∨ 2 * γ * n / Real.logb 2 n < A.card ∨ A ∈ BadPairsEvent G ( param_T γ n ) } = Set.univ from Set.eq_univ_of_forall fun x => h_union x ] ; simp +decide [ prob_event ];
            have h_sum : ∑ A : Finset V, bernoulli_weight (param_p γ n) A = 1 := by
              exact sum_bernoulli_weight (param_p γ n);
            exact h_sum.ge;
          refine' ⟨ A, _, _, _ ⟩ <;> simp_all +decide [ not_or ];
          · exact Finset.nonempty_of_ne_empty hA.1;
          · intro x y hx hy hxy;
            contrapose! hA;
            intro hA₁ hA₂;
            refine' ⟨ x, y, _, _, _ ⟩ <;> simp_all +decide [ same_adj_to_A ];
            · rintro rfl; simp_all +decide [ dif_size ];
              simp_all +decide [ param_T, symmDiff ];
              norm_num [ Finset.sdiff_self ] at hA;
              exact hA.not_gt ( mul_pos ( div_pos ( by norm_num ) hγ.1 ) ( sq_pos_of_pos ( Real.logb_pos ( by norm_num ) ( by norm_cast; linarith ) ) ) );
            · simp_all +decide [ DifFinset, Finset.disjoint_left ];
              simp_all +decide [ symmDiff ];
              intro a ha; specialize hxy a ha; simp_all +decide [ SimpleGraph.adj_comm ] ;

/-
Definitions for A-isomorphism classes of subsets containing A.
-/
def SubsetsContaining {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) : Type _ :=
  { S : Finset V // A ⊆ S }

instance {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) : Fintype (SubsetsContaining A) :=
  Subtype.fintype (fun S => A ⊆ S)

def A_iso {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (S T : SubsetsContaining A) : Prop :=
  ∃ (f : G.induce (S.val : Set V) ≃g G.induce (T.val : Set V)),
    ∀ (a : A), f ⟨a.1, S.property a.2⟩ = ⟨a.1, T.property a.2⟩

def A_iso_setoid {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    Setoid (SubsetsContaining A) :=
  Setoid.mk (A_iso G A) (by
  constructor;
  · simp [A_iso];
    exact fun x => ⟨ 1, fun a ha => rfl ⟩;
  · rintro x y ⟨ f, hf ⟩;
    refine' ⟨ f.symm, fun a => _ ⟩;
    have := f.symm_apply_apply ⟨ a, x.2 a.2 ⟩ ; aesop;
  · rintro ⟨ B, hB ⟩ ⟨ C, hC ⟩ ⟨ D, hD ⟩ ⟨ f ⟩ ⟨ g ⟩;
    refine' ⟨ g.comp f, _ ⟩;
    aesop)

noncomputable def num_A_iso {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) : ℕ :=
  Fintype.card (Quotient (A_iso_setoid G A))

/-
The number of distinct adjacency patterns to A among vertices not in A.
-/
def num_patterns {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  let S := Finset.univ.filter (fun v => v ∉ A)
  let pattern (v : V) : A → Bool := fun a => G.Adj a v
  (S.image pattern).card

/-
Definitions of the set of patterns and the subset of vertices corresponding to a set of patterns.
-/
def patterns_set {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (A → Bool) :=
  let S := Finset.univ.filter (fun v => v ∉ A)
  let pattern (v : V) : A → Bool := fun a => decide (G.Adj a v)
  S.image pattern

def subset_from_patterns {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (U : Finset (A → Bool)) : SubsetsContaining A :=
  ⟨A ∪ (Finset.univ.filter (fun v => v ∉ A ∧ (fun (a : A) => decide (G.Adj a v)) ∈ U)), by
    -- By definition of union, any element in A is already in the union.
    simp [Finset.subset_union_left]⟩

/-
An A-isomorphism preserves adjacency to vertices in A.
-/
theorem lemma_A_iso_preserves_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (S T : SubsetsContaining A) (f : G.induce (S.val : Set V) ≃g G.induce (T.val : Set V))
    (h_fix : ∀ (a : A), f ⟨a.1, S.property a.2⟩ = ⟨a.1, T.property a.2⟩)
    (v : S.val) :
    ∀ a : A, G.Adj a.1 v.val ↔ G.Adj a.1 (f v).val := by
      intro a;
      -- Since $f$ is an isomorphism, it preserves adjacency.
      have h_adj : G.Adj (a : V) v ↔ G.Adj (a : V) (f v) := by
        have h_adj_S : SimpleGraph.Adj (G.induce S.val) ⟨a, by
          exact S.2 a.2⟩ v ↔ SimpleGraph.Adj (G.induce T.val) ⟨a, by
          exact T.2 a.2⟩ (f v) := by
          rw [ ← f.map_adj_iff ] ; aesop
        convert h_adj_S using 1
      generalize_proofs at *;
      exact h_adj

/-
An A-isomorphism maps vertices not in A to vertices not in A.
-/
theorem lemma_A_iso_maps_diff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (S T : SubsetsContaining A) (f : G.induce (S.val : Set V) ≃g G.induce (T.val : Set V))
    (h_fix : ∀ (a : A), f ⟨a.1, S.property a.2⟩ = ⟨a.1, T.property a.2⟩)
    (v : S.val) (hv : v.val ∉ A) :
    (f v).val ∉ A := by
      rintro ( H : _ ∈ _ );
      -- Since $f$ is an isomorphism, $f(v) = a$ for some $a \in A$.
      obtain ⟨a, ha⟩ : ∃ a : A, f v = ⟨a, by
        exact T.property a.2⟩ := by
        aesop;
      have := f.injective ( ha.trans ( h_fix a |> Eq.symm ) ) ; aesop;

/-
If two subsets of patterns generate A-isomorphic subgraphs, the subsets must be equal.
-/
theorem patterns_inj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (U V : Finset (A → Bool))
    (hU : U ⊆ patterns_set G A) (hV : V ⊆ patterns_set G A)
    (h_iso : A_iso G A (subset_from_patterns G A U) (subset_from_patterns G A V)) :
    U = V := by
      apply le_antisymm;
      · intro p hp
        obtain ⟨v, hv⟩ := Finset.mem_image.mp (hU hp);
        obtain ⟨ f, hf ⟩ := h_iso;
        have hv_in_U : v ∈ (subset_from_patterns G A U).val := by
          unfold subset_from_patterns; aesop;
        have hv_in_V : (f ⟨v, hv_in_U⟩).val ∈ (subset_from_patterns G A V).val := by
          exact f ⟨ v, hv_in_U ⟩ |>.2;
        have hv_pattern_eq : ∀ a : A, G.Adj a v ↔ G.Adj a (f ⟨v, hv_in_U⟩).val := by
          apply lemma_A_iso_preserves_adj G A (subset_from_patterns G A U) (subset_from_patterns G A V) f hf ⟨v, hv_in_U⟩;
        have hv_pattern_eq : (fun a : A => decide (G.Adj a (f ⟨v, hv_in_U⟩).val)) = p := by
          aesop;
        have hv_pattern_eq : (f ⟨v, hv_in_U⟩).val ∉ A := by
          have hv_pattern_eq : (f ⟨v, hv_in_U⟩).val ∉ A := by
            have := lemma_A_iso_maps_diff G A (subset_from_patterns G A U) (subset_from_patterns G A V) f hf ⟨v, hv_in_U⟩
            aesop;
          exact hv_pattern_eq;
        have hv_pattern_eq : (fun a : A => decide (G.Adj a (f ⟨v, hv_in_U⟩).val)) ∈ V := by
          convert Finset.mem_coe.mp hv_in_V using 1;
          exact ⟨ fun h => Finset.mem_union_right _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hv_pattern_eq, h ⟩ ), fun h => by rcases Finset.mem_union.mp h with ( h | h ) <;> aesop ⟩;
        grind;
      · obtain ⟨ f, hf ⟩ := h_iso;
        intro p hp;
        -- Since $p \in V$, there exists $v \in V \setminus A$ such that $pattern(v) = p$.
        obtain ⟨v, hv₁, hv₂⟩ : ∃ v ∈ Finset.univ.filter (fun v => v ∉ A), (fun a : A => decide (G.Adj a v)) = p := by
          have := hV hp; simp_all +decide [ patterns_set ] ;
        -- Since $v \in V \setminus A$, we have $v \in S_V$.
        have hv_SV : v ∈ (subset_from_patterns G A V).val := by
          unfold subset_from_patterns; aesop;
        -- Let $w = f^{-1}(v)$. Then $w \in S_U$.
        obtain ⟨w, hw⟩ : ∃ w : (subset_from_patterns G A U).val, f w = ⟨v, hv_SV⟩ := by
          exact f.surjective ⟨ v, hv_SV ⟩;
        -- Since $w \in S_U$, we have $w \in A$ or $w \notin A$.
        by_cases hwA : w.val ∈ A;
        · have := hf ⟨ w.val, hwA ⟩ ; aesop;
        · -- Since $w \notin A$, we have $pattern(w) \in U$.
          have hw_pattern : (fun a : A => decide (G.Adj a w.val)) ∈ U := by
            have hw_pattern : w.val ∈ Finset.univ.filter (fun v => v ∉ A) ∧ (fun a : A => decide (G.Adj a w.val)) ∈ U := by
              simp +zetaDelta at *;
              exact ⟨ hwA, by have := w.2; exact Finset.mem_union.mp this |> Or.rec ( fun h => by aesop ) fun h => by aesop ⟩;
            exact hw_pattern.2;
          have hw_pattern_eq : ∀ a : A, G.Adj a.1 w.val ↔ G.Adj a.1 (f w).val := by
            exact fun a =>
              lemma_A_iso_preserves_adj G A (subset_from_patterns G A U)
                (subset_from_patterns G A V) f hf w a;
          aesop

/-
The number of A-isomorphism types is at least 2^(number of patterns).
-/
theorem lemma_eqclasses_part1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    (2 : ℝ) ^ (num_patterns G A) ≤ (num_A_iso G A : ℝ) := by
      -- Let P = patterns_set G A.
      let P := patterns_set G A;
      -- Define a map f : Finset.powerset P -> Quotient (A_iso_setoid G A) by f(U) = Quotient.mk (A_iso_setoid G A) (subset_from_patterns G A U).
      let f := fun U : Finset (A → Bool) => Quotient.mk (A_iso_setoid G A) (subset_from_patterns G A U);
      have h_f_inj : Set.InjOn f (Finset.powerset P) := by
        intro U hU V hV h_eq;
        apply patterns_inj G A U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV);
        exact Quotient.exact h_eq;
      have h_card_f : (Finset.powerset P).card ≤ (Fintype.card (Quotient (A_iso_setoid G A))) := by
        have h_card_f : (Finset.powerset P).card ≤ (Finset.image f (Finset.powerset P)).card := by
          rw [ Finset.card_image_of_injOn h_f_inj ];
        exact h_card_f.trans ( Finset.card_le_univ _ );
      convert h_card_f using 1;
      norm_num [ num_patterns ];
      norm_cast

/-
A-isomorphism implies induced subgraph isomorphism.
-/
theorem forget_label_respects {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (S T : SubsetsContaining A) (h : A_iso G A S T) :
    induced_iso_rel G (S.val : Set V) (T.val : Set V) := by
      exact ⟨ h.choose ⟩

/-
Setoid for induced subgraph isomorphism and representative function.
-/
def induced_iso_setoid {V : Type*} [Fintype V] (G : SimpleGraph V) : Setoid (Set V) :=
  Setoid.mk (induced_iso_rel G) (by
    constructor
    · intro s; exact ⟨RelIso.refl _⟩
    · intro s t ⟨f⟩; exact ⟨f.symm⟩
    · intro s t u ⟨f⟩ ⟨g⟩; exact ⟨f.trans g⟩)

/-
The map forgetting the labels of A.
-/
def forget_label {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    Quotient (A_iso_setoid G A) → Quotient (induced_iso_setoid G) :=
  Quotient.lift (fun S => Quotient.mk (induced_iso_setoid G) S.val) (fun S T h => Quotient.sound (forget_label_respects G A S T h))

/-
The size of the fiber of the forgetful map is at most n^|A|.
-/
theorem lemma_fiber_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) (y : Quotient (induced_iso_setoid G)) :
    Fintype.card { x : Quotient (A_iso_setoid G A) // forget_label G A x = y } ≤ (Fintype.card V) ^ A.card := by
      have h_inj : ∃ f : {x : Quotient (A_iso_setoid G A) | forget_label G A x = y} → (A → V), Function.Injective f := by
        -- For each $x$ in the fiber, let $S$ be a representative of $x$ (so $S$ is a subset containing $A$).
        have h_rep : ∀ x : {x : Quotient (A_iso_setoid G A) | forget_label G A x = y}, ∃ S : SubsetsContaining A, x.val = Quotient.mk (A_iso_setoid G A) S := by
          rintro ⟨ x, hx ⟩;
          rcases x with ⟨ S ⟩ ; aesop;
        choose f hf using h_rep;
        -- For each $x$ in the fiber, let $\phi_x$ be an isomorphism from $G[f(x)]$ to $G[y.out]$.
        have h_iso : ∀ x : {x : Quotient (A_iso_setoid G A) | forget_label G A x = y}, ∃ ϕ : G.induce (f x).val ≃g G.induce y.out, True := by
          intro x
          have h_iso : induced_iso_rel G (f x).val y.out := by
            have h_iso : induced_iso_rel G (f x).val y.out := by
              have h_eq : Quotient.mk (induced_iso_setoid G) (f x).val = y := by
                exact x.2.symm ▸ hf x ▸ rfl
              exact Quotient.exact ( h_eq.trans ( Quotient.out_eq' _ ).symm );
            exact h_iso;
          exact ⟨ h_iso.some, trivial ⟩;
        choose ϕ hϕ using h_iso;
        refine' ⟨ fun x => fun a => ( ϕ x ) ⟨ a.1, ( f x ).2 a.2 ⟩ |>.1, fun x y hxy => _ ⟩;
        -- Since $\phi_x$ and $\phi_y$ are isomorphisms, we have $\phi_x(a) = \phi_y(a)$ for all $a \in A$.
        have h_iso_eq : ∀ a : A, (ϕ x) ⟨a.1, (f x).2 a.2⟩ = (ϕ y) ⟨a.1, (f y).2 a.2⟩ := by
          exact fun a => Subtype.ext <| congr_fun hxy a;
        -- Since $\phi_x$ and $\phi_y$ are isomorphisms, we have $f(x)$ and $f(y)$ are A-isomorphic.
        have h_A_iso : A_iso G A (f x) (f y) := by
          use (ϕ x).trans (RelIso.symm (ϕ y));
          aesop;
        have := hf x; have := hf y; simp_all +decide
        exact Subtype.ext ( by rw [ ‹ ( x : Quotient ( A_iso_setoid G A ) ) = ⟦f x⟧ ›, ‹ ( y : Quotient ( A_iso_setoid G A ) ) = ⟦f y⟧ › ] ; exact Quotient.sound h_A_iso );
      obtain ⟨ f, hf ⟩ := h_inj;
      have := Fintype.card_le_of_injective f hf; simp_all +decide [ Fintype.card_pi ] ;

/-
The number of A-isomorphism types is at most I(G) * n^|A|.
-/
theorem lemma_eqclasses_part2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    (num_A_iso G A : ℝ) ≤ (I_num G : ℝ) * (Fintype.card V : ℝ) ^ A.card := by
      -- By definition of quotient, we can express the cardinality of the quotient as the sum of the cardinalities of the fibers.
      have h_card_eq : (Fintype.card (Quotient (A_iso_setoid G A))) = ∑ y : Quotient (induced_iso_setoid G), (Fintype.card { x : Quotient (A_iso_setoid G A) // forget_label G A x = y }) := by
        have h_fiber : ∀ y : Quotient (induced_iso_setoid G), (Fintype.card { x : Quotient (A_iso_setoid G A) // forget_label G A x = y }) = Finset.card (Finset.filter (fun x => forget_label G A x = y) Finset.univ) := by
          exact fun y => by rw [ Fintype.subtype_card ] ;
        simp +decide only [h_fiber];
        simp +decide only [Finset.card_filter];
        rw [ Finset.sum_comm ] ; aesop;
      refine' mod_cast h_card_eq.le.trans ( le_trans ( Finset.sum_le_sum fun y _ => lemma_fiber_bound G A y ) _ );
      simp +decide [ I_num ];
      rfl

/-
The Caro-Wei bound: the independence number is at least the sum of 1/(d(v)+1).
-/
theorem lemma_caro_wei {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ G.indepNum := by
      by_contra h_contra;
      -- We prove by induction on the number of vertices.
      induction' n : Fintype.card V using Nat.strong_induction_on with n ih generalizing V G;
      -- Let $v$ be a vertex of minimum degree $\delta$.
      obtain ⟨v, hv⟩ : ∃ v : V, ∀ u : V, G.degree u ≥ G.degree v := by
        by_cases hV : Nonempty V;
        · simpa using Finset.exists_min_image Finset.univ ( fun v => G.degree v ) ⟨ hV.some, Finset.mem_univ _ ⟩;
        · norm_num +zetaDelta at *;
          exact h_contra.not_ge ( by simp +decide [ SimpleGraph.indepNum ] );
      -- Let $S = \{v\} \cup N(v)$.
      set S : Finset V := {v} ∪ G.neighborFinset v;
      -- Let $G'$ be the induced subgraph on $V \setminus S$.
      set G' : SimpleGraph {x : V // x ∉ S} := SimpleGraph.comap (fun x => x.val) G;
      -- By induction, $\alpha(G') \ge \sum_{u \in V \setminus S} \frac{1}{d_{G'}(u)+1}$.
      have h_ind : (G'.indepNum : ℝ) ≥ ∑ u : {x : V // x ∉ S}, (1 / (G'.degree u + 1) : ℝ) := by
        by_cases h_card : Fintype.card {x : V // x ∉ S} < Fintype.card V;
        · specialize ih ( Fintype.card { x // x ∉ S } ) ( by linarith ) G' ; aesop;
        · simp +zetaDelta at *;
          rw [ Fintype.card_subtype ] at h_card;
          exact absurd h_card ( not_le_of_gt ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ v, by simp +decide ⟩ ) ) ( by simp +decide ) ) );
      -- We need to show $1 + \sum_{u \in V \setminus S} \frac{1}{d_{G'}(u)+1} \ge \sum_{u \in V} \frac{1}{d_G(u)+1}$.
      have h_sum : 1 + ∑ u : {x : V // x ∉ S}, (1 / (G'.degree u + 1) : ℝ) ≥ ∑ u : V, (1 / (G.degree u + 1) : ℝ) := by
        -- Split the RHS sum into $u=v$, $u \in N(v)$, and $u \in V \setminus S$.
        have h_split : ∑ u : V, (1 / (G.degree u + 1) : ℝ) = (1 / (G.degree v + 1) : ℝ) + ∑ u ∈ G.neighborFinset v, (1 / (G.degree u + 1) : ℝ) + ∑ u ∈ Finset.univ \ S, (1 / (G.degree u + 1) : ℝ) := by
          rw [ ← Finset.sum_sdiff ( Finset.subset_univ S ) ];
          rw [ Finset.sum_union ] <;> norm_num ; ring;
        -- For $u \in V \setminus S$, $d_{G'}(u) \le d_G(u)$, so $\frac{1}{d_{G'}(u)+1} \ge \frac{1}{d_G(u)+1}$.
        have h_deg_le : ∀ u : {x : V // x ∉ S}, (G'.degree u : ℝ) ≤ (G.degree u.val : ℝ) := by
          simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
          intro u hu; rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; refine' Finset.card_mono _ ; intro x hx; aesop;
        -- Since $v$ has minimum degree, for all $u \in N(v)$, $d_G(u) \ge \delta$.
        have h_deg_ge : ∀ u ∈ G.neighborFinset v, (G.degree u : ℝ) ≥ (G.degree v : ℝ) := by
          exact fun u hu => mod_cast hv u;
        -- Thus $\sum_{u \in N(v)} \frac{1}{d_G(u)+1} \le \sum_{u \in N(v)} \frac{1}{\delta+1} = \frac{\delta}{\delta+1}$.
        have h_sum_Nv : ∑ u ∈ G.neighborFinset v, (1 / (G.degree u + 1) : ℝ) ≤ (G.degree v : ℝ) / (G.degree v + 1) := by
          exact le_trans ( Finset.sum_le_sum fun u hu => one_div_le_one_div_of_le ( by positivity ) ( add_le_add_right ( h_deg_ge u hu ) _ ) ) ( by simp +decide [ div_eq_mul_inv ] );
        -- Since $d_{G'}(u) \le d_G(u)$ for all $u \in V \setminus S$, we have $\frac{1}{d_{G'}(u)+1} \ge \frac{1}{d_G(u)+1}$.
        have h_sum_ge : ∑ u ∈ Finset.univ \ S, (1 / (G.degree u + 1) : ℝ) ≤ ∑ u : {x : V // x ∉ S}, (1 / (G'.degree u + 1) : ℝ) := by
          refine' le_trans _ ( Finset.sum_le_sum fun u hu => one_div_le_one_div_of_le ( by positivity ) ( add_le_add_right ( h_deg_le u ) _ ) );
          refine' le_of_eq _;
          refine' Finset.sum_bij ( fun u hu => ⟨ u, by aesop ⟩ ) _ _ _ _ <;> simp +decide;
        linarith [ show ( 1 : ℝ ) / ( G.degree v + 1 ) + ( G.degree v : ℝ ) / ( G.degree v + 1 ) ≤ 1 by rw [ ← add_div, div_le_iff₀ ] <;> linarith ];
      -- Since $\alpha(G) \ge 1 + \alpha(G')$, we have $\alpha(G) \ge 1 + \sum_{u \in V \setminus S} \frac{1}{d_{G'}(u)+1}$.
      have h_alpha : (G.indepNum : ℝ) ≥ 1 + (G'.indepNum : ℝ) := by
        -- Let $I'$ be an independent set in $G'$.
        obtain ⟨I', hI'⟩ : ∃ I' : Finset {x : V // x ∉ S}, G'.IsNIndepSet (G'.indepNum) I' := by
          exact SimpleGraph.exists_isNIndepSet_indepNum;
        -- Let $I = \{v\} \cup I'$.
        set I : Finset V := {v} ∪ Finset.image (fun x => x.val) I';
        -- Since $I$ is an independent set in $G$, we have $G.indepNum \geq |I|$.
        have h_I_indep : G.IsNIndepSet (1 + G'.indepNum) I := by
          have h_I_indep : G.IsNIndepSet (1 + I'.card) I := by
            constructor;
            · intro x hx y hy hxy; simp_all +decide
              simp +zetaDelta at *;
              rcases hx with ( rfl | ⟨ hx₁, hx₂ ⟩ ) <;> rcases hy with ( rfl | ⟨ hy₁, hy₂ ⟩ ) <;> simp_all +decide [ SimpleGraph.comap ];
              · exact fun h => hx₁.2 ( h.symm );
              · have := hI'.1 hx₂ hy₂; aesop;
            · rw [ Finset.card_union_of_disjoint ] <;> norm_num;
              · exact Finset.card_image_of_injective _ Subtype.coe_injective;
              · aesop;
          convert h_I_indep using 1;
          exact hI'.card_eq.symm ▸ rfl;
        norm_cast;
        exact le_csSup ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩ ⟨ I, h_I_indep ⟩;
      linarith

/-
A graph with N vertices and at most Nd edges has an independent set of size at least N/(2d+1).
-/
theorem lemma_indset_edges {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (N : ℕ) (hN : Fintype.card V = N)
    (d : ℝ) (h_edges : H.edgeFinset.card ≤ N * d) :
    (N : ℝ) / (2 * d + 1) ≤ H.indepNum := by
      have h_avg_deg : ∑ v, (1 : ℝ) / (H.degree v + 1) ≥ N / (2 * d + 1) := by
        have h_jensen : (∑ v, (1 : ℝ) / (H.degree v + 1)) ≥ N ^ 2 / (∑ v, (H.degree v + 1)) := by
          have h_cauchy_schwarz : ∀ (a b : V → ℝ), (∀ v, 0 ≤ a v) → (∀ v, 0 ≤ b v) → (∑ v, a v * b v) ^ 2 ≤ (∑ v, a v ^ 2) * (∑ v, b v ^ 2) := by
            exact fun a b a_1 a_2 => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b;
          have := h_cauchy_schwarz ( fun v => 1 / Real.sqrt ( H.degree v + 1 ) ) ( fun v => Real.sqrt ( H.degree v + 1 ) ) ; simp_all +decide [ Real.sq_sqrt ( add_nonneg ( Nat.cast_nonneg _ ) zero_le_one ) ];
          simp_all +decide [ ne_of_gt ( Real.sqrt_pos.mpr ( add_pos_of_nonneg_of_pos ( Nat.cast_nonneg _ ) zero_lt_one ) ) ];
          exact div_le_of_le_mul₀ ( Finset.sum_nonneg fun _ _ => by positivity ) ( Finset.sum_nonneg fun _ _ => by positivity ) this;
        -- Since $\sum_{v} (H.degree v + 1) = 2|E| + N$, we can substitute this into Jensen's inequality.
        have h_sum_deg : ∑ v, (H.degree v + 1) = 2 * H.edgeFinset.card + N := by
          simp +decide [ Finset.sum_add_distrib, SimpleGraph.sum_degrees_eq_twice_card_edges, hN ];
        refine' le_trans _ h_jensen ; rw [ h_sum_deg ] ; push_cast ; rcases N with ( _ | _ | N ) <;> norm_num at *;
        · exact inv_anti₀ ( by positivity ) ( by linarith );
        · rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( 0 : ℝ ) ≤ d by nlinarith ];
      exact h_avg_deg.trans ( by exact lemma_caro_wei H )

/-
We can greedily extract disjoint homogeneous sets of size m from C until fewer than R(m,m) vertices remain.
-/
theorem lemma_greedy_homogeneous {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (m : ℕ) (hm : 2 ≤ m) :
    ∃ (B : List (Finset V)),
      (∀ b ∈ B, b ⊆ C) ∧
      (∀ b ∈ B, b.card = m) ∧
      (∀ b ∈ B, G.IsNClique m b ∨ G.IsNIndepSet m b) ∧
      (B.Pairwise Disjoint) ∧
      (C \ B.foldr (· ∪ ·) ∅).card < R m m := by
        have h_exists_B : ∃ B : List (Finset V), (∀ b ∈ B, b ⊆ C) ∧ (∀ b ∈ B, b.card = m) ∧ (∀ b ∈ B, G.IsNClique m b ∨ G.IsNIndepSet m b) ∧ List.Pairwise Disjoint B ∧ (C \ B.foldr (fun x1 x2 => x1 ∪ x2) ∅).card < R m m := by
          have h_exists_homogeneous : ∀ S : Finset V, S.card ≥ R m m → ∃ H : Finset V, H ⊆ S ∧ H.card = m ∧ (G.IsNClique m H ∨ G.IsNIndepSet m H) := by
            intro S hS_card
            have h_ramsey : ∀ (G : SimpleGraph (Fin (R m m))), m ≤ G.cliqueNum ∨ m ≤ G.indepNum := by
              exact fun G => Nat.sInf_mem ( show { N : ℕ | Ramsey_prop m m N }.Nonempty from by
                                              exact ⟨ _, ramsey_upper_bound_prop m m hm hm ⟩ ) G;
            obtain ⟨f, hf⟩ : ∃ f : Fin (R m m) → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
              have := Finset.exists_subset_card_eq hS_card;
              obtain ⟨ t, ht₁, ht₂ ⟩ := this;
              have := Finset.equivFinOfCardEq ht₂;
              exact ⟨ fun i => this.symm i |>.1, fun i j hij => by simpa [ Fin.ext_iff ] using this.symm.injective ( Subtype.ext hij ), fun i => ht₁ ( this.symm i |>.2 ) ⟩;
            specialize h_ramsey ( SimpleGraph.comap f G );
            rcases h_ramsey with h | h;
            · obtain ⟨H, hH⟩ : ∃ H : Finset (Fin (R m m)), H.card = m ∧ (SimpleGraph.comap f G).IsNClique m H := by
                contrapose! h;
                refine' lt_of_not_ge fun h' => _;
                obtain ⟨H, hH⟩ : ∃ H : Finset (Fin (R m m)), (SimpleGraph.comap f G).IsClique H ∧ H.card ≥ m := by
                  obtain ⟨ n, hn ⟩ := exists_lt_of_lt_csSup ( show { n : ℕ | ∃ s : Finset ( Fin ( R m m ) ), ( SimpleGraph.comap f G ).IsNClique n s }.Nonempty from ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNClique_iff ] ⟩ ⟩ ) ( show m - 1 < sSup { n : ℕ | ∃ s : Finset ( Fin ( R m m ) ), ( SimpleGraph.comap f G ).IsNClique n s } from lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hm ) ) h' );
                  rcases hn.1 with ⟨ H, hH ⟩ ; exact ⟨ H, hH.1, by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ m ), hH.2 ] ⟩ ;
                obtain ⟨H', hH'⟩ : ∃ H' : Finset (Fin (R m m)), H' ⊆ H ∧ H'.card = m ∧ (SimpleGraph.comap f G).IsClique H' := by
                  obtain ⟨H', hH'⟩ : ∃ H' : Finset (Fin (R m m)), H' ⊆ H ∧ H'.card = m := by
                    exact Finset.exists_subset_card_eq hH.2;
                  exact ⟨ H', hH'.1, hH'.2, fun x hx y hy hxy => hH.1 ( hH'.1 hx ) ( hH'.1 hy ) hxy ⟩;
                exact h H' hH'.2.1 ⟨ hH'.2.2, hH'.2.1 ⟩;
              refine' ⟨ Finset.image f H, _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ];
              · exact Finset.image_subset_iff.mpr fun i hi => hf.2 i;
              · rw [ Finset.card_image_of_injective _ hf.1, hH.1 ];
              · simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.isIndepSet_iff, Set.Pairwise ];
                exact Or.inl ⟨ fun x hx y hy hxy => hH.2.1 hx hy ( by simpa [ hf.1.eq_iff ] using hxy ), by rw [ Finset.card_image_of_injective _ hf.1, hH.1 ] ⟩;
            · obtain ⟨ H, hH ⟩ := ( show ∃ H : Finset ( Fin ( R m m ) ), H.card = m ∧ ( SimpleGraph.comap f G ).IsNIndepSet m H from by
                                      obtain ⟨ H, hH ⟩ := ( show ∃ H : Finset ( Fin ( R m m ) ), H.card = ( SimpleGraph.comap f G ).indepNum ∧ ( SimpleGraph.comap f G ).IsNIndepSet ( SimpleGraph.comap f G ).indepNum H from by
                                                              obtain ⟨ H, hH ⟩ := ( show ∃ H : Finset ( Fin ( R m m ) ), ( SimpleGraph.comap f G ).IsNIndepSet ( SimpleGraph.comap f G ).indepNum H from by
                                                                                      have := Nat.sSup_mem ( show { n : ℕ | ∃ s : Finset ( Fin ( R m m ) ), ( SimpleGraph.comap f G ).IsNIndepSet n s }.Nonempty from ?_ );
                                                                                      · exact this ⟨ _, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
                                                                                      · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩ ⟩ );
                                                              exact ⟨ H, hH.2, hH ⟩ );
                                      obtain ⟨ H', hH' ⟩ := Finset.exists_subset_card_eq ( by linarith : m ≤ H.card );
                                      use H';
                                      simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
                                      exact hH.2.1.mono ( by simpa [ Finset.subset_iff ] using hH'.1 ) );
              use Finset.image f H;
              simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ];
              simp_all +decide [ SimpleGraph.isIndepSet_iff, SimpleGraph.isClique_iff, Finset.card_image_of_injective _ hf.1 ];
              simp_all +decide [ Set.Pairwise, hf.1.eq_iff ]
          induction' n : C.card using Nat.strong_induction_on with n ih generalizing C;
          by_cases hC : C.card ≥ R m m;
          · obtain ⟨ H, hH₁, hH₂, hH₃ ⟩ := h_exists_homogeneous C hC;
            obtain ⟨ B, hB₁, hB₂, hB₃, hB₄, hB₅ ⟩ := ih ( C.card - m ) ( by
              rw [ ← n ];
              exact Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( by linarith ) ) ( C \ H ) ( by
              grind );
            use H :: B;
            simp +zetaDelta at *;
            refine' ⟨ ⟨ hH₁, fun b hb => Finset.Subset.trans ( hB₁ b hb ) ( Finset.sdiff_subset ) ⟩, ⟨ hH₂, hB₂ ⟩, ⟨ hH₃, hB₃ ⟩, ⟨ fun b hb => Finset.disjoint_left.mpr fun x hx₁ hx₂ => by have := hB₁ b hb; have := this hx₂; aesop, hB₄ ⟩, _ ⟩;
            convert hB₅ using 2 ; ext ; aesop;
          · exact ⟨ [ ], by aesop ⟩;
        exact h_exists_B

/-
Definition of bad indices and the bad graph.
-/
def bad_indices {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (j : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j' => j' ≠ j ∧ ∃ x ∈ B j, ¬Disjoint (B j') (DifFinset G (rep j) x))

def bad_graph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (B : Fin N → Finset V) (rep : Fin N → V) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun j j' => j' ∈ bad_indices G B rep j ∨ j ∈ bad_indices G B rep j')

/-
The number of bad indices for a given block is bounded by (m-1)T.
-/
theorem lemma_bad_indices_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (m : ℕ) (T : ℝ)
    (h_disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (h_size : ∀ i, (B i).card = m)
    (h_rep : ∀ i, rep i ∈ B i)
    (h_dif : ∀ i, ∀ x ∈ B i, (dif_size G (rep i) x : ℝ) < T) :
    ∀ j, ((bad_indices G B rep j).card : ℝ) ≤ (m - 1) * T := by
      intro j
      set U := bad_indices G B rep j with hU_def
      set S := Finset.biUnion (B j \ {rep j}) (fun x => DifFinset G (rep j) x) with hS_def;
      -- Since $U$ is the set of indices $j'$ such that $B j'$ intersects $S$, and $B j'$ are disjoint, each point in $S$ belongs to at most one $B j'$.
      have h_card_U_le_card_S : (U.card : ℝ) ≤ S.card := by
        have h_card_U_le_card_S : ∀ j' ∈ U, ∃ v ∈ S, v ∈ B j' := by
          intro j' hj'
          obtain ⟨x, hx_Bj, hx_dif⟩ : ∃ x ∈ B j, ¬Disjoint (B j') (DifFinset G (rep j) x) := by
            exact Finset.mem_filter.mp hj' |>.2 |> fun ⟨ h₁, x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂ ⟩;
          by_cases hx_rep : x = rep j;
          · simp_all +decide [ Finset.disjoint_left, DifFinset ];
            obtain ⟨ v, hv₁, hv₂ ⟩ := hx_dif; use v; simp_all +decide [ symmDiff ] ;
          · exact Exists.elim ( Finset.not_disjoint_iff.mp hx_dif ) fun v hv => ⟨ v, Finset.mem_biUnion.mpr ⟨ x, Finset.mem_sdiff.mpr ⟨ hx_Bj, by aesop ⟩, hv.2 ⟩, hv.1 ⟩;
        have h_card_U_le_card_S : (U.card : ℝ) ≤ Finset.card (Finset.biUnion U (fun j' => B j' ∩ S)) := by
          rw [ Finset.card_biUnion ];
          · exact_mod_cast le_trans ( by simp +decide ) ( Finset.sum_le_sum fun i hi => Finset.card_pos.mpr <| by obtain ⟨ v, hv₁, hv₂ ⟩ := h_card_U_le_card_S i hi; exact ⟨ v, Finset.mem_inter.mpr ⟨ hv₂, hv₁ ⟩ ⟩ );
          · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( h_disjoint i j hij ) ( Finset.mem_of_mem_inter_left hx₁ ) ( Finset.mem_of_mem_inter_left hx₂ );
        exact h_card_U_le_card_S.trans ( mod_cast Finset.card_le_card <| Finset.biUnion_subset.mpr fun i hi => Finset.inter_subset_right );
      -- Since $S$ is the union of sets each of size less than $T$, and there are $m-1$ such sets, $S$'s size is less than $(m-1)*T$.
      have h_card_S_le : S.card ≤ (B j \ {rep j}).card * (T : ℝ) := by
        have h_card_S_le : ∀ x ∈ B j \ {rep j}, (DifFinset G (rep j) x).card ≤ T := by
          exact fun x hx => le_of_lt ( h_dif j x ( Finset.mem_sdiff.mp hx |>.1 ) );
        exact le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) <| by simpa using Finset.sum_le_sum h_card_S_le;
      simp_all +decide [ Finset.card_sdiff ];
      convert h_card_S_le.trans' ( Nat.cast_le.mpr h_card_U_le_card_S ) using 1 ; cases m <;> simp_all +decide;
      exact False.elim ( h_rep j )

/-
The number of edges in the bad graph is at most N*d.
-/
theorem lemma_bad_graph_edge_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (d : ℝ)
    (h_bound : ∀ j, (bad_indices G B rep j).card ≤ d) :
    ((bad_graph G N B rep).edgeFinset.card : ℝ) ≤ N * d := by
      -- Let E be the set of edges of H.
      set E := (bad_graph G N B rep).edgeFinset;
      -- Each edge {j, j'} in E corresponds to a pair (j, j') such that j' in bad_indices j or j in bad_indices j'.
      have h_edge_count : E.card ≤ ∑ j, ((bad_indices G B rep j).card : ℝ) := by
        have h_edge_count : E.card ≤ ∑ j, ((bad_indices G B rep j).card : ℕ) := by
          -- Each edge {j, j'} in E contributes to the sum on the RHS.
          have h_edge_contribution : ∀ e ∈ E, ∃ j : Fin N, e ∈ Finset.image (fun j' => Sym2.mk (j, j')) (bad_indices G B rep j) := by
            simp +zetaDelta at *;
            rintro ⟨ x, y ⟩ hxy; cases' hxy with hxy hxy; aesop;
          have h_edges_bound : E ⊆ Finset.biUnion Finset.univ (fun j => Finset.image (fun j' => Sym2.mk (j, j')) (bad_indices G B rep j)) := by
            grind;
          exact le_trans ( Finset.card_le_card h_edges_bound ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun _ _ => Finset.card_image_le ) );
        exact_mod_cast h_edge_count;
      exact h_edge_count.trans ( le_trans ( Finset.sum_le_sum fun _ _ => h_bound _ ) ( by simp +decide ) )

/-
If a set of indices is independent in the bad graph, then the corresponding blocks have uniform adjacency.
-/
theorem lemma_bad_graph_indep_implies_uniformity {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (h_rep : ∀ i, rep i ∈ B i)
    (W : Finset (Fin N))
    (h_indep : (bad_graph G N B rep).IsIndepSet W) :
    ∀ i ∈ W, ∀ j ∈ W, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y ↔ G.Adj (rep i) (rep j) := by
      intro i hi j hj hij x hx y hy; contrapose! h_indep; simp_all +decide [ SimpleGraph.IsIndepSet ] ;
      unfold bad_graph; simp_all +decide
      unfold bad_indices; simp_all +decide
      unfold Set.Pairwise; simp_all +decide [ Finset.disjoint_left ] ;
      cases' h_indep with h_indep h_indep <;> use i, hi, j, hj <;> simp_all +decide [ DifFinset ];
      · intro h; use y, hy, x, hx; simp_all +decide [ SimpleGraph.adj_comm, symmDiff ] ;
        grind +ring;
      · intro h; use y, hy, x, hx; simp_all +decide [ SimpleGraph.adj_comm, symmDiff ] ;
        grind +ring

/-
There exists a large subset of indices W such that the blocks indexed by W have uniform adjacency.
-/
theorem lemma_uniform_subset_existence {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (m : ℕ) (T : ℝ)
    (h_disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (h_size : ∀ i, (B i).card = m)
    (h_rep : ∀ i, rep i ∈ B i)
    (h_dif : ∀ i, ∀ x ∈ B i, (dif_size G (rep i) x : ℝ) < T) :
    ∃ W : Finset (Fin N),
      (W.card : ℝ) ≥ (N : ℝ) / (2 * ((m - 1) * T) + 1) ∧
      ∀ i ∈ W, ∀ j ∈ W, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y ↔ G.Adj (rep i) (rep j) := by
        -- By lemma_indset_edges, H has an independent set W of size at least N/(2d+1).
        obtain ⟨W, hW⟩ : ∃ W : Finset (Fin N), (W.card : ℝ) ≥ N / (2 * ((m - 1) * T) + 1) ∧ (bad_graph G N B rep).IsIndepSet W := by
          have h_ind : (N : ℝ) / (2 * ((m - 1) * T) + 1) ≤ (bad_graph G N B rep).indepNum := by
            apply_rules [ lemma_indset_edges ];
            · simp +decide;
            · convert lemma_bad_graph_edge_bound G B rep _ ( fun j => lemma_bad_indices_bound G B rep m T h_disjoint h_size h_rep h_dif j ) using 1;
          obtain ⟨W, hW⟩ : ∃ W : Finset (Fin N), W.card = (bad_graph G N B rep).indepNum ∧ (bad_graph G N B rep).IsIndepSet W := by
            -- By definition of indepNum, there exists an independent set W with cardinality equal to the indepNum.
            have h_indep_exists : ∃ W : Finset (Fin N), (bad_graph G N B rep).IsIndepSet W ∧ W.card = (bad_graph G N B rep).indepNum := by
              have h_max : ∃ W : Finset (Fin N), (bad_graph G N B rep).IsIndepSet W ∧ ∀ W' : Finset (Fin N), (bad_graph G N B rep).IsIndepSet W' → W'.card ≤ W.card := by
                have h_max : ∃ W ∈ Finset.filter (fun W : Finset (Fin N) => (bad_graph G N B rep).IsIndepSet W) (Finset.powerset (Finset.univ : Finset (Fin N))), ∀ W' ∈ Finset.filter (fun W : Finset (Fin N) => (bad_graph G N B rep).IsIndepSet W) (Finset.powerset (Finset.univ : Finset (Fin N))), W'.card ≤ W.card := by
                  exact Finset.exists_max_image _ _ ⟨ ∅, by simp +decide ⟩;
                aesop
              obtain ⟨ W, hW₁, hW₂ ⟩ := h_max;
              refine' ⟨ W, hW₁, le_antisymm _ _ ⟩;
              · exact SimpleGraph.IsIndepSet.card_le_indepNum hW₁;
              · exact csSup_le' fun n hn => by obtain ⟨ W', hW'₁, hW'₂ ⟩ := hn; exact hW'₂ ▸ hW₂ W' ( by simpa [ SimpleGraph.isIndepSet_iff ] using hW'₁ ) ;
            exact ⟨ h_indep_exists.choose, h_indep_exists.choose_spec.2, h_indep_exists.choose_spec.1 ⟩;
          aesop;
        use W;
        exact ⟨ hW.1, fun i hi j hj hij x hx y hy => lemma_bad_graph_indep_implies_uniformity G B rep h_rep W hW.2 i hi j hj hij x hx y hy ⟩

/-
Definition of the adjacency pattern of a vertex and the set of vertices with a given pattern.
-/
def pattern {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) : A → Bool :=
  fun a => G.Adj a v

def vertices_with_pattern {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (p : A → Bool) : Finset V :=
  (Finset.univ \ A).filter (fun v => pattern G A v = p)

/-
The sum of the sizes of the pattern classes is the number of vertices not in A.
-/
theorem lemma_partition_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    ∑ p ∈ patterns_set G A, (vertices_with_pattern G A p).card = Fintype.card V - A.card := by
      simp +decide [ vertices_with_pattern, patterns_set ];
      rw [ Finset.sum_image' ];
      rotate_left;
      use fun v => if v ∈ A then 0 else 1;
      · simp +decide [ Finset.sum_ite ];
        intro i hi; congr 1 with j ; aesop;
      · simp +decide [ Finset.filter_not ];
        rw [ Finset.sum_congr rfl fun x hx => if_neg ( Finset.mem_sdiff.mp hx |>.2 ) ] ; simp +decide [ Finset.card_sdiff ]

/-
Properties of the greedily chosen blocks.
-/
noncomputable def greedy_blocks {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (m : ℕ) : List (Finset V) :=
  if hm : 2 ≤ m then
    (lemma_greedy_homogeneous G C m hm).choose
  else
    []

theorem greedy_blocks_props {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (m : ℕ) (hm : 2 ≤ m) :
    let B := greedy_blocks G C m
    (∀ b ∈ B, b ⊆ C) ∧
    (∀ b ∈ B, b.card = m) ∧
    (∀ b ∈ B, G.IsNClique m b ∨ G.IsNIndepSet m b) ∧
    (B.Pairwise Disjoint) ∧
    (C \ B.foldr (· ∪ ·) ∅).card < R m m := by
      have := @lemma_greedy_homogeneous;
      unfold greedy_blocks;
      split_ifs ; simp_all +decide;
      exact Exists.choose_spec ( this G C m hm )

/-
The list of all blocks collected from all pattern classes.
-/
noncomputable def all_blocks_list {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ℕ) : List (Finset V) :=
  (patterns_set G A).toList.flatMap (fun p => greedy_blocks G (vertices_with_pattern G A p) m)

/-
Properties of the list of all blocks: size, homogeneity, disjointness, pattern uniformity, and total count.
-/
theorem all_blocks_props {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (m : ℕ) (hm : 2 ≤ m) :
    let B := all_blocks_list G A m
    (∀ b ∈ B, b.card = m) ∧
    (∀ b ∈ B, G.IsNClique m b ∨ G.IsNIndepSet m b) ∧
    (B.Pairwise Disjoint) ∧
    (∀ b ∈ B, ∃ p, ∀ x ∈ b, pattern G A x = p) ∧
    ((B.length : ℝ) * m ≥ (Fintype.card V : ℝ) - A.card - (patterns_set G A).card * (R m m)) := by
      refine' ⟨ _, _, _, _, _ ⟩;
      · unfold all_blocks_list;
        norm_num +zetaDelta at *;
        intro b x hx hb;
        have := greedy_blocks_props G ( vertices_with_pattern G A x ) m hm;
        exact this.2.1 b hb;
      · intro b hb
        obtain ⟨p, hp⟩ : ∃ p ∈ patterns_set G A, b ∈ greedy_blocks G (vertices_with_pattern G A p) m := by
          unfold all_blocks_list at hb; aesop;
        have := greedy_blocks_props G ( vertices_with_pattern G A p ) m hm; aesop;
      · -- By definition of `all_blocks_list`, the blocks within each pattern class are disjoint.
        have h_disjoint_within_classes : ∀ p ∈ patterns_set G A, List.Pairwise Disjoint (greedy_blocks G (vertices_with_pattern G A p) m) := by
          intro p hp
          have := greedy_blocks_props G (vertices_with_pattern G A p) m hm
          aesop;
        -- By definition of `all_blocks_list`, blocks from different pattern classes are disjoint.
        have h_disjoint_between_classes : ∀ p q : A → Bool, p ≠ q → ∀ b ∈ greedy_blocks G (vertices_with_pattern G A p) m, ∀ c ∈ greedy_blocks G (vertices_with_pattern G A q) m, Disjoint b c := by
          intro p q hpq b hb c hc
          have h_disjoint_vertices : Disjoint (vertices_with_pattern G A p) (vertices_with_pattern G A q) := by
            exact Finset.disjoint_filter.mpr fun x _ hx hx' => hpq <| funext fun a => by aesop;
          have h_disjoint_blocks : b ⊆ vertices_with_pattern G A p ∧ c ⊆ vertices_with_pattern G A q := by
            have := greedy_blocks_props G ( vertices_with_pattern G A p ) m hm; have := greedy_blocks_props G ( vertices_with_pattern G A q ) m hm; aesop;
          exact Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp h_disjoint_vertices ( h_disjoint_blocks.1 hx ) ( h_disjoint_blocks.2 hx' );
        -- By definition of `all_blocks_list`, the blocks are pairwise disjoint.
        have h_disjoint_all : ∀ {l : List (A → Bool)}, (∀ p ∈ l, p ∈ patterns_set G A) → List.Pairwise (fun p q => p ≠ q) l → List.Pairwise Disjoint (List.flatMap (fun p => greedy_blocks G (vertices_with_pattern G A p) m) l) := by
          grind;
        exact h_disjoint_all ( fun p hp => by aesop ) ( by simpa using Finset.nodup_toList _ );
      · unfold all_blocks_list;
        simp +zetaDelta at *;
        intro b x hx hb;
        -- By definition of `vertices_with_pattern`, all vertices in `b` have the same pattern `x`.
        use x;
        have := greedy_blocks_props G ( vertices_with_pattern G A x ) m hm;
        exact fun y hy => Finset.mem_filter.mp ( this.1 b hb hy ) |>.2;
      · -- Let's calculate the total number of vertices covered by the blocks.
        have h_total_vertices : ∑ p ∈ patterns_set G A, (greedy_blocks G (vertices_with_pattern G A p) m).length * m ≥ (Fintype.card V : ℝ) - A.card - (patterns_set G A).card * (R m m : ℝ) := by
          have h_total_vertices : ∑ p ∈ patterns_set G A, (greedy_blocks G (vertices_with_pattern G A p) m).length * m ≥ ∑ p ∈ patterns_set G A, ((vertices_with_pattern G A p).card : ℝ) - (patterns_set G A).card * (R m m : ℝ) := by
            have h_total_edges : ∀ p ∈ patterns_set G A, (greedy_blocks G (vertices_with_pattern G A p) m).length * m ≥ (vertices_with_pattern G A p).card - R m m := by
              intro p hp
              have h_block_prop : (greedy_blocks G (vertices_with_pattern G A p) m).length * m ≥ (vertices_with_pattern G A p).card - (vertices_with_pattern G A p \ (greedy_blocks G (vertices_with_pattern G A p) m).foldr (· ∪ ·) ∅).card := by
                have h_block_prop : (greedy_blocks G (vertices_with_pattern G A p) m).length * m ≥ (vertices_with_pattern G A p ∩ (greedy_blocks G (vertices_with_pattern G A p) m).foldr (· ∪ ·) ∅).card := by
                  have h_block_prop : (vertices_with_pattern G A p ∩ (greedy_blocks G (vertices_with_pattern G A p) m).foldr (· ∪ ·) ∅).card ≤ (greedy_blocks G (vertices_with_pattern G A p) m).length * m := by
                    have h_block_prop : ∀ b ∈ greedy_blocks G (vertices_with_pattern G A p) m, b.card = m := by
                      exact fun b hb => (greedy_blocks_props G (vertices_with_pattern G A p) m hm).2.1 b hb
                    have h_block_prop : ∀ {l : List (Finset V)}, (∀ b ∈ l, b.card = m) → (vertices_with_pattern G A p ∩ l.foldr (· ∪ ·) ∅).card ≤ l.length * m := by
                      intros l hl; induction' l with b l ih <;> simp_all +decide
                      rw [ Finset.inter_union_distrib_left ];
                      exact le_trans ( Finset.card_union_le _ _ ) ( by linarith [ show Finset.card ( vertices_with_pattern G A p ∩ b ) ≤ m by exact le_trans ( Finset.card_le_card fun x hx => by aesop ) hl.1.le ] );
                    exact h_block_prop ‹_›;
                  exact h_block_prop;
                grind;
              refine' Nat.le_trans _ h_block_prop;
              have := greedy_blocks_props G ( vertices_with_pattern G A p ) m hm;
              exact Nat.sub_le_sub_left this.2.2.2.2.le _;
            simp +zetaDelta at *;
            exact le_trans ( Finset.sum_le_sum fun p hp => Nat.cast_le.mpr ( h_total_edges p hp ) ) ( by simp +decide [ Finset.sum_add_distrib ] );
          have h_total_vertices : ∑ p ∈ patterns_set G A, (vertices_with_pattern G A p).card = (Fintype.card V : ℝ) - A.card := by
            convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( lemma_partition_sum G A ) using 1;
            rw [ Nat.cast_sub ( Finset.card_le_univ _ ) ];
          aesop;
        convert h_total_vertices using 1;
        unfold all_blocks_list; simp +decide [ Finset.sum_mul _ _ _ ] ;

/-
For any $c>0$, there exists an integer $k \ge 2$ such that $\frac{c+1}{k} \log_2(e(k+1)) < 1/4$.
-/
lemma existence_of_k (c : ℝ) :
  ∃ k : ℕ, k ≥ 2 ∧ (c + 1) / k * Real.logb 2 (Real.exp 1 * (k + 1)) < 1 / 4 := by
    -- We'll use that $\frac{\log x}{x}$ tends to $0$ as $x \to \infty$.
    have h_log_div_x_zero : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
      suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
        exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    have h_log_div_x_zero : Filter.Tendsto (fun k : ℕ => (Real.log (Real.exp 1 * (k + 1))) / (k : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_div_x_zero : Filter.Tendsto (fun k : ℕ => Real.log (Real.exp 1 * (k + 1)) / (k + 1 : ℝ)) Filter.atTop (nhds 0) := by
        have h_log_div_x_zero : Filter.Tendsto (fun k : ℕ => Real.log (Real.exp 1 * k) / k) Filter.atTop (nhds 0) := by
          have := h_log_div_x_zero.comp ( tendsto_natCast_atTop_atTop.const_mul_atTop ( by positivity : 0 < Real.exp 1 ) );
          convert this.const_mul ( Real.exp 1 ) using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.exp_ne_zero ];
        exact_mod_cast h_log_div_x_zero.comp ( Filter.tendsto_add_atTop_nat 1 );
      have h_log_div_x_zero : Filter.Tendsto (fun k : ℕ => (Real.log (Real.exp 1 * (k + 1)) / (k + 1 : ℝ)) * ((k + 1 : ℝ) / k)) Filter.atTop (nhds 0) := by
        simpa using h_log_div_x_zero.mul ( show Filter.Tendsto ( fun k : ℕ => ( k + 1 : ℝ ) / k ) Filter.atTop ( nhds 1 ) from by simpa [ add_div ] using tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat ) |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with k hk; aesop ) );
      exact h_log_div_x_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by rw [ div_mul_div_cancel₀ ( by positivity ) ] );
    norm_num [ Real.logb, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] at *;
    have := h_log_div_x_zero.const_mul ( ( c + 1 ) * ( Real.log 2 ) ⁻¹ ) ; norm_num at *;
    exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds <| show 0 < 1 / 4 by norm_num ) ) |> fun ⟨ k, hk ⟩ ↦ ⟨ k + 2, by linarith, by have := hk ( k + 2 ) ( by linarith ) ; push_cast at *; nlinarith ⟩

/-
For $m_2 \ge 1$, if $\varepsilon = \frac{1}{100 m_2}$ and $\gamma = \frac{\varepsilon}{4}$, then for sufficiently large $n$, $1 - \frac{2\gamma}{\log_2 n} - m_2(\varepsilon + 2\gamma) \ge 0.9$.
-/
lemma arithmetic_bound (m₂ : ℕ) (hm₂ : m₂ ≥ 1) :
  let ε := 1 / (100 * m₂ : ℝ)
  let γ := ε / 4
  ∃ n₀, ∀ n ≥ n₀,
    1 - (2 * γ / Real.logb 2 n) - m₂ * (ε + 2 * γ) ≥ 0.9 := by
      -- Since $0.985 > 0.9$, the inequality holds for sufficiently large $n$.
      have h_limit : Filter.Tendsto (fun n : ℝ => 1 - 2 * (1 / (400 * (m₂ : ℝ))) / Real.logb 2 n - m₂ * (3 / (200 * (m₂ : ℝ)))) Filter.atTop (nhds 0.985) := by
        exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Real.tendsto_logb_atTop ( by linarith ) ) tendsto_const_nhds ) ( by ring_nf; norm_num [ show m₂ ≠ 0 by linarith ] );
      -- By the definition of limit, for any ε' > 0, there exists an N such that for all n ≥ N, the expression is within ε' of 0.985.
      have h_eps : ∀ ε' > 0, ∃ N : ℝ, ∀ n ≥ N, |(1 - 2 * (1 / (400 * (m₂ : ℝ))) / Real.logb 2 n - m₂ * (3 / (200 * (m₂ : ℝ)))) - 0.985| < ε' := by
        exact fun ε' ε'_pos => Metric.tendsto_atTop.mp h_limit ε' ε'_pos;
      exact Exists.elim ( h_eps ( 0.985 - 0.9 ) ( by norm_num ) ) fun N hN => ⟨ N, fun n hn => by have := abs_lt.mp ( hN n hn ) ; ring_nf at *; linarith ⟩

/-
Under the assumptions of the theorem, the total size of the greedy blocks is at least $0.9n$.
-/
lemma lemma_blocks_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (m : ℕ) (hm : 2 ≤ m)
    (m₂ : ℕ) (hm₂ : m₂ = R m m)
    (ε γ : ℝ)
    (hε : ε = 1 / (100 * m₂))
    (hγ : γ = ε / 4)
    (A : Finset V)
    (hA : (A.card : ℝ) ≤ 2 * γ * n / Real.logb 2 n)
    (hI : (I_num G : ℝ) < (2 : ℝ) ^ (ε * n))
    (n_large : 1 - (2 * γ / Real.logb 2 n) - m₂ * (ε + 2 * γ) ≥ 0.9) :
    ((all_blocks_list G A m).length : ℝ) * m ≥ 0.9 * n := by
      -- By Lemma~\ref{lem:all_blocks_props}, we have the bound:
      have h_length_bound : (all_blocks_list G A m).length * m ≥ (n : ℝ) - A.card - m₂ * (patterns_set G A).card := by
        have := all_blocks_props G A m hm
        simp_all +decide
        linarith;
      -- By Lemma~\ref{lem:all_blocks_props}, we have the bound on the number of patterns:
      have h_pattern_bound : (patterns_set G A).card ≤ ε * n + A.card * Real.logb 2 n := by
        -- From the problem statement, we know that $2^\ell \le I(G) n^{|A|} < 2^{\varepsilon n} n^{|A|}$.
        have h_card_bound : (2 : ℝ) ^ (patterns_set G A).card ≤ (I_num G : ℝ) * (n : ℝ) ^ A.card := by
          have h_card_bound : (2 : ℝ) ^ (patterns_set G A).card ≤ (num_A_iso G A : ℝ) := by
            convert lemma_eqclasses_part1 G A using 1;
          refine le_trans h_card_bound ?_;
          convert lemma_eqclasses_part2 G A;
          exact hn.symm;
        -- Taking the logarithm base 2 of both sides of the inequality $2^\ell \le I(G) n^{|A|} < 2^{\varepsilon n} n^{|A|}$, we get $\ell \le \varepsilon n + |A| \log_2 n$.
        have h_log_bound : (patterns_set G A).card ≤ Real.logb 2 ((2 : ℝ) ^ (ε * n) * (n : ℝ) ^ A.card) := by
          rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast at * <;> norm_num at *;
          · exact le_trans ( mod_cast h_card_bound ) ( mul_le_mul_of_nonneg_right hI.le ( by positivity ) );
          · rcases n with ( _ | _ | n ) <;> norm_num at *;
            · rw [ Fintype.card_eq_zero_iff ] at hn ; aesop;
            · positivity;
            · positivity;
        rw [ Real.logb_mul ] at h_log_bound <;> norm_num at *;
        · simpa [ Real.logb, mul_div_assoc ] using h_log_bound;
        · positivity;
        · aesop;
      -- Substitute the bounds from hA and h_pattern_bound into h_length_bound.
      have h_substitute : (all_blocks_list G A m).length * m ≥ n - (2 * γ * n / Real.logb 2 n) - m₂ * (ε * n + (2 * γ * n / Real.logb 2 n) * Real.logb 2 n) := by
        have h_substitute : (all_blocks_list G A m).length * m ≥ n - A.card - m₂ * (ε * n + A.card * Real.logb 2 n) := by
          exact h_length_bound.trans' ( sub_le_sub_left ( mul_le_mul_of_nonneg_left h_pattern_bound <| Nat.cast_nonneg _ ) _ );
        refine le_trans ?_ h_substitute;
        gcongr;
        rcases n with ( _ | _ | n ) <;> norm_num at *;
        exact Real.logb_nonneg ( by norm_num ) ( by linarith );
      by_cases h : Real.logb 2 n = 0 <;> simp_all +decide [ division_def ];
      · rcases h with ( h | rfl | rfl | h ) <;> norm_num at *;
        · exact_mod_cast h_substitute;
        · linarith;
        · linarith;
      · nlinarith [ show ( 0 : ℝ ) < n by exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero h.2.1 ) ]

/-
For sufficiently large $n$, $s \le \frac{c+1}{m_1} \log_2 n$.
-/
lemma lemma_s_bound (c : ℝ) (hc : c > 0) (m₁ : ℕ) (hm₁ : m₁ ≥ 1) :
  ∃ n₀, ∀ n ≥ n₀,
    let r := ⌊c * Real.logb 2 n⌋₊ + 1
    let s := ⌈(r : ℝ) / m₁⌉₊
    (s : ℝ) ≤ (c + 1) / m₁ * Real.logb 2 n := by
      -- To satisfy the inequality $1 + m₁ \leq \log₂ n$, we can choose $n₀$ such that $2^{1 + m₁} \leq n₀$.
      use 2^(1 + m₁);
      -- We'll use the fact that if $n \geq 2^{m₁ + 1}$, then $\log₂ n \geq m₁ + 1$.
      intro n hn
      have h_log : Real.logb 2 n ≥ m₁ + 1 := by
        rw [ ge_iff_le, Real.le_logb_iff_rpow_le ] <;> norm_num <;> try linarith [ pow_pos ( zero_lt_two' ℝ ) ( 1 + m₁ ) ] ;
        exact_mod_cast hn.trans' ( by ring_nf; norm_num );
      have h_ceil : (Nat.ceil ((Nat.floor (c * Real.logb 2 n) + 1) / (m₁ : ℝ)) : ℝ) ≤ (Nat.floor (c * Real.logb 2 n) + 1) / (m₁ : ℝ) + 1 := by
        exact le_of_lt <| Nat.ceil_lt_add_one <| by positivity;
      field_simp;
      rw [ div_add_one, le_div_iff₀ ] at h_ceil <;> norm_num at * <;> nlinarith [ Nat.floor_le ( show 0 ≤ c * Real.logb 2 n by exact mul_nonneg hc.le ( by linarith ) ), Nat.lt_floor_add_one ( c * Real.logb 2 n ) ]

/-
For sufficiently large $n$, $R(r, s) \le n^{1/3}$.
-/
lemma lemma_R_rs_bound (c : ℝ) (hc : c > 0)
    (k : ℕ) (hk : k ≥ 2)
    (h_delta : (c + 1) / k * Real.logb 2 (Real.exp 1 * (k + 1)) < 1 / 4)
    (m₁ : ℕ) (hm₁ : m₁ = k) :
    ∃ n₀, ∀ n ≥ n₀,
      let r := ⌊c * Real.logb 2 n⌋₊ + 1
      let s := ⌈(r : ℝ) / m₁⌉₊
      (R r s : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
        -- By Lemma 2, if $r \le m_1 s$, then $R(r,s) \le R(m_1 s, s)$.
        have lemma2 : ∀ n ≥ 2, let r := ⌊c * Real.logb 2 n⌋₊ + 1; let s := ⌈(r : ℝ) / m₁⌉₊; (R r s : ℝ) ≤ (R (m₁ * s) s : ℝ) := by
          -- By definition of $r$ and $s$, we have $r \le m_1 s$.
          intros n hn
          set r := ⌊c * Real.logb 2 n⌋₊ + 1
          set s := ⌈(r : ℝ) / m₁⌉₊
          have h_rs : r ≤ m₁ * s := by
            rw [ ← @Nat.cast_le ℝ ] ; push_cast ; nlinarith [ Nat.le_ceil ( ( r : ℝ ) / m₁ ), show ( m₁ : ℝ ) ≥ 2 by norm_cast; linarith, mul_div_cancel₀ ( r : ℝ ) ( by norm_cast; linarith : ( m₁ : ℝ ) ≠ 0 ) ];
          -- By definition of $R$, if $r \le m_1 s$, then $R(r, s) \le R(m_1 s, s)$.
          have h_rs : Ramsey_prop r s (R (m₁ * s) s) := by
            have := Nat.sInf_mem ( show { N | Ramsey_prop ( m₁ * s ) s N }.Nonempty from ?_ );
            · exact fun G => Or.imp ( fun h => by linarith ) id ( this G );
            · use Nat.choose ( m₁ * s + s - 2 ) ( m₁ * s - 1 );
              intro G;
              have := @ramsey_upper_bound_prop ( m₁ * s ) s;
              rcases m₁ with ( _ | _ | m₁ ) <;> rcases s with ( _ | _ | s ) <;> norm_num at *;
              · linarith;
              · linarith;
              · refine' Or.inr _;
                refine' le_csSup _ _;
                · exact ⟨ _, fun n hn => hn.choose_spec.card_eq.symm ▸ Finset.card_le_univ _ ⟩;
                · exact ⟨ { ⟨ 0, by simp +decide ⟩ }, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩;
              · exact this ( by nlinarith ) G;
          exact_mod_cast Nat.sInf_le h_rs;
        -- By Corollary `cor_ramsey_km`, $R(m_1 s, s) \le (e(m_1+1))^s$.
        have lemma3 : ∀ n ≥ 2, let r := ⌊c * Real.logb 2 n⌋₊ + 1; let s := ⌈(r : ℝ) / m₁⌉₊; (R (m₁ * s) s : ℝ) ≤ (Real.exp 1 * (m₁ + 1)) ^ s := by
          intros n hn
          generalize_proofs at *;
          have := cor_ramsey_km k ( Nat.ceil ( ( ⌊c * Real.logb 2 n⌋₊ + 1 : ℝ ) / k ) ) ( by linarith ) ( Nat.ceil_pos.mpr ( by positivity ) ) ; aesop;
        -- By Lemma `lemma_s_bound`, for large $n$, $s \le \frac{c+1}{m_1} \log_2 n$.
        obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, let r := ⌊c * Real.logb 2 n⌋₊ + 1; let s := ⌈(r : ℝ) / m₁⌉₊; (s : ℝ) ≤ (c + 1) / m₁ * Real.logb 2 n := by
          have := @lemma_s_bound c hc m₁ ( by linarith );
          exact this;
        -- Let $A = e(m_1+1)$. Then $R(r,s) \le A^s \le A^{\frac{c+1}{m_1} \log_2 n}$.
        have lemma4 : ∀ n ≥ max 2 n₀, let r := ⌊c * Real.logb 2 n⌋₊ + 1; let s := ⌈(r : ℝ) / m₁⌉₊; (R r s : ℝ) ≤ (Real.exp 1 * (m₁ + 1)) ^ ((c + 1) / m₁ * Real.logb 2 n) := by
          intros n hn
          specialize lemma2 n (le_trans (le_max_left 2 n₀) hn)
          specialize lemma3 n (le_trans (le_max_left 2 n₀) hn)
          specialize hn₀ n (le_trans (le_max_right 2 n₀) hn);
          exact le_trans lemma2 ( le_trans lemma3 ( by simpa using Real.rpow_le_rpow_of_exponent_le ( by nlinarith [ Real.add_one_le_exp 1, show ( m₁ : ℝ ) ≥ 2 by norm_cast; linarith ] ) hn₀ ) );
        -- We have $A^{\frac{c+1}{m_1} \log_2 n} = n^{\frac{c+1}{m_1} \log_2 A}$.
        have lemma5 : ∀ n ≥ max 2 n₀, let r := ⌊c * Real.logb 2 n⌋₊ + 1; let s := ⌈(r : ℝ) / m₁⌉₊; (R r s : ℝ) ≤ n ^ ((c + 1) / m₁ * Real.logb 2 (Real.exp 1 * (m₁ + 1))) := by
          intro n hn
          specialize lemma4 n hn
          have h_exp : (Real.exp 1 * (m₁ + 1)) ^ ((c + 1) / m₁ * Real.logb 2 n) = n ^ ((c + 1) / m₁ * Real.logb 2 (Real.exp 1 * (m₁ + 1))) := by
            rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by linarith [ le_max_left 2 n₀, le_max_right 2 n₀ ] ) ] ; ring_nf ; norm_num [ Real.logb ] ; ring_nf;
          rw [h_exp] at lemma4
          exact lemma4;
        refine' ⟨ Max.max 2 n₀, fun n hn => le_trans ( lemma5 n hn ) _ ⟩;
        exact Real.rpow_le_rpow_of_exponent_le ( by linarith [ le_max_left 2 n₀, le_max_right 2 n₀ ] ) ( by subst hm₁; linarith )

/-
For sufficiently large $n$, $W_{size}/2 \ge R(r,s)$.
-/
lemma lemma_W_large_enough (c : ℝ) (hc : c > 0)
    (k : ℕ) (hk : k ≥ 2)
    (h_delta : (c + 1) / k * Real.logb 2 (Real.exp 1 * (k + 1)) < 1 / 4)
    (m₁ : ℕ) (hm₁ : m₁ = k)
    (γ : ℝ) (hγ : γ > 0) :
    ∃ n₀, ∀ n ≥ n₀,
      let r := ⌊c * Real.logb 2 n⌋₊ + 1
      let s := ⌈(r : ℝ) / m₁⌉₊
      let T := 20 / γ * (Real.logb 2 n)^2
      let N_min := 0.9 * n / m₁
      let W_size := N_min / (2 * ((m₁ - 1) * T) + 1)
      W_size / 2 ≥ (R r s : ℝ) := by
        -- We need to show that $W_{size}/2 \ge n^{1/3}$.
        suffices h_W_size_ge_n_cubed_root : ∃ n₀, ∀ n ≥ n₀,
          let r := ⌊c * Real.logb 2 n⌋₊ + 1
          let s := ⌈(r : ℝ) / m₁⌉₊
          (R r s : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) ∧
          (n : ℝ) ^ (1 / 3 : ℝ) * 2 ≤ (0.9 * n / m₁) / (2 * ((m₁ - 1) * (20 / γ * (Real.logb 2 n) ^ 2)) + 1) by
            field_simp at h_W_size_ge_n_cubed_root ⊢;
            exact ⟨ h_W_size_ge_n_cubed_root.choose, fun n hn => by have := h_W_size_ge_n_cubed_root.choose_spec n hn; ring_nf at this ⊢; linarith ⟩;
        -- By `lemma_R_rs_bound`, for large $n$, $R(r,s) \le n^{1/3}$.
        obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀,
          let r := ⌊c * Real.logb 2 n⌋₊ + 1
          let s := ⌈(r : ℝ) / m₁⌉₊
          (R r s : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
            exact lemma_R_rs_bound c hc k hk h_delta m₁ hm₁;
        -- We need to show that $W_{size}/2 \ge n^{1/3}$ by finding a suitable $n₀$.
        obtain ⟨n₁, hn₁⟩ : ∃ n₁, ∀ n ≥ n₁,
          (n : ℝ) ^ (1 / 3 : ℝ) * 2 ≤ (0.9 * n / m₁) / (2 * ((m₁ - 1) * (20 / γ * (Real.logb 2 n) ^ 2)) + 1) := by
            -- We can divide both sides by $n^{1/3}$ and simplify the inequality.
            suffices h_div : ∃ n₁, ∀ n ≥ n₁,
              2 * (2 * ((m₁ - 1) * (20 / γ * (Real.logb 2 n) ^ 2)) + 1) ≤ (0.9 / m₁) * n ^ (2 / 3 : ℝ) by
                obtain ⟨ n₁, hn₁ ⟩ := h_div;
                refine' ⟨ Max.max n₁ 1, fun n hn => _ ⟩ ; specialize hn₁ n ( le_trans ( le_max_left _ _ ) hn ) ; rw [ le_div_iff₀ ] <;> norm_num at *;
                · convert mul_le_mul_of_nonneg_left hn₁ ( Real.rpow_nonneg ( by linarith : 0 ≤ n ) ( 1 / 3 : ℝ ) ) using 1 ; ring;
                  field_simp;
                  rw [ ← Real.rpow_add ] <;> norm_num ; linarith;
                · exact add_pos_of_nonneg_of_pos ( mul_nonneg zero_le_two ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ( mul_nonneg ( by positivity ) ( sq_nonneg _ ) ) ) ) zero_lt_one;
            -- We can divide both sides by $n^{2/3}$ and simplify the inequality.
            suffices h_div : ∃ n₁, ∀ n ≥ n₁,
              2 * (2 * ((m₁ - 1) * (20 / γ * (Real.logb 2 n) ^ 2)) + 1) / n ^ (2 / 3 : ℝ) ≤ 0.9 / m₁ by
                exact ⟨ Max.max h_div.choose 1, fun n hn => by have := h_div.choose_spec n ( le_trans ( le_max_left _ _ ) hn ) ; rwa [ div_le_iff₀ ( Real.rpow_pos_of_pos ( by linarith [ le_max_right h_div.choose 1 ] ) _ ) ] at this ⟩;
            -- We can use the fact that $\frac{\log^2 n}{n^{2/3}}$ tends to $0$ as $n$ tends to infinity.
            have h_log_sq_div_n_cubed_root : Filter.Tendsto (fun n : ℝ => (Real.logb 2 n) ^ 2 / n ^ (2 / 3 : ℝ)) Filter.atTop (nhds 0) := by
              -- We can convert this limit into a form that is easier to handle by substituting $x = \log n$.
              suffices h_log : Filter.Tendsto (fun x : ℝ => x ^ 2 / Real.exp (2 * x / 3)) Filter.atTop (nhds 0) by
                have h_log : Filter.Tendsto (fun n : ℝ => (Real.log n) ^ 2 / n ^ (2 / 3 : ℝ)) Filter.atTop (nhds 0) := by
                  have := h_log.comp Real.tendsto_log_atTop;
                  refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring_nf );
                convert h_log.div_const ( Real.log 2 ^ 2 ) using 2 <;> norm_num [ Real.logb ] ; ring;
              -- Let $y = \frac{2x}{3}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{(3y/2)^2}{e^y}$.
              suffices h_y : Filter.Tendsto (fun y : ℝ => (3 * y / 2) ^ 2 / Real.exp y) Filter.atTop (nhds 0) by
                convert h_y.comp ( Filter.tendsto_id.const_mul_atTop ( show ( 0 : ℝ ) < 2 / 3 by norm_num ) ) using 2 ; norm_num ; ring_nf;
              ring_nf;
              simpa [ Real.exp_neg ] using Filter.Tendsto.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 ) tendsto_const_nhds;
            -- We can use the fact that the limit of the expression is 0 to find such an N.
            have h_limit : Filter.Tendsto (fun n : ℝ => 2 * (2 * ((m₁ - 1) * (20 / γ * (Real.logb 2 n) ^ 2)) + 1) / n ^ (2 / 3 : ℝ)) Filter.atTop (nhds 0) := by
              have h_limit : Filter.Tendsto (fun n : ℝ => 2 * (2 * ((m₁ - 1) * (20 / γ * (Real.logb 2 n) ^ 2))) / n ^ (2 / 3 : ℝ)) Filter.atTop (nhds 0) := by
                convert h_log_sq_div_n_cubed_root.const_mul ( 2 * ( 2 * ( ( m₁ - 1 ) * ( 20 / γ ) ) ) ) using 2 <;> ring;
              convert h_limit.add ( show Filter.Tendsto ( fun n : ℝ => 2 / n ^ ( 2 / 3 : ℝ ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by norm_num ) ) ) using 2 <;> ring;
            simpa using h_limit.eventually ( ge_mem_nhds <| by exact div_pos ( by norm_num ) <| Nat.cast_pos.mpr <| hm₁.symm ▸ by linarith );
        exact ⟨ Max.max n₀ n₁, fun n hn => ⟨ hn₀ n ( le_trans ( le_max_left _ _ ) hn ), hn₁ n ( le_trans ( le_max_right _ _ ) hn ) ⟩ ⟩

/-
The Ramsey number $R(a,b)$ is equal to $R(b,a)$.
-/
theorem lemma_ramsey_symm (a b : ℕ) : R a b = R b a := by
  unfold R;
  congr! 3;
  constructor <;> intro h G <;> specialize h ( Gᶜ ) <;> aesop

/-
The graph on indices where $i \sim j$ iff $rep(i) \sim rep(j)$.
-/
def R_graph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (rep : Fin N → V) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel (fun i j => G.Adj (rep i) (rep j))

/-
There exists a subset $W' \subseteq W$ of size at least $|W|/2$ such that all blocks in $W'$ are cliques or all are independent sets.
-/
lemma lemma_large_homogeneous_subset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V)
    (m : ℕ)
    (h_hom : ∀ i, G.IsNClique m (B i) ∨ G.IsNIndepSet m (B i))
    (W : Finset (Fin N)) :
    ∃ W' ⊆ W, (W'.card : ℝ) ≥ (W.card : ℝ) / 2 ∧
      ((∀ i ∈ W', G.IsNClique m (B i)) ∨ (∀ i ∈ W', G.IsNIndepSet m (B i))) := by
        -- Let $W_{clique} = \{i \in W \mid B_i \text{ is clique}\}$ and $W_{indep} = \{i \in W \mid B_i \text{ is indep}\}$.
        set W_clique := Finset.filter (fun i => G.IsNClique m (B i)) W
        set W_indep := Finset.filter (fun i => G.IsNIndepSet m (B i)) W;
        -- Since each $i \in W$ is in at least one of these sets, $W \subseteq W_{clique} \cup W_{indep}$.
        have h_union : W ⊆ W_clique ∪ W_indep := by
          intro i hi; specialize h_hom i; aesop;
        have h_card_union : (W_clique.card : ℝ) + (W_indep.card : ℝ) ≥ (W.card : ℝ) := by
          exact_mod_cast le_trans ( Finset.card_le_card h_union ) ( Finset.card_union_le _ _ );
        cases le_total ( W_clique.card : ℝ ) ( W_indep.card : ℝ ) <;> [ exact ⟨ W_indep, Finset.filter_subset _ _, by linarith, Or.inr fun i hi => Finset.mem_filter.mp hi |>.2 ⟩ ; exact ⟨ W_clique, Finset.filter_subset _ _, by linarith, Or.inl fun i hi => Finset.mem_filter.mp hi |>.2 ⟩ ]

/-
The Ramsey number $R(a,b)$ satisfies the Ramsey property.
-/
theorem lemma_ramsey_prop_R (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : Ramsey_prop a b (R a b) := by
  have h_nonempty : {N | Ramsey_prop a b N}.Nonempty := by
    exact ⟨ _, ramsey_upper_bound_prop a b ha hb ⟩;
  exact Nat.sInf_mem h_nonempty

/-
If a graph has a subset of vertices $S$ with $|S| \ge R(a,b)$, then $S$ contains a clique of size $a$ or an independent set of size $b$.
-/
lemma lemma_ramsey_on_subset {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hS : S.card ≥ R a b) :
    (∃ K ⊆ S, G.IsNClique a K) ∨ (∃ I ⊆ S, G.IsNIndepSet b I) := by
      have := @ramsey_prop_general;
      specialize this a b ( S.card ) ( by simp +decide ) ( ramsey_prop_mono ( lemma_ramsey_prop_R a b ha hb ) hS ) ( G.induce S );
      cases' this with h h;
      · contrapose! h;
        refine' lt_of_not_ge fun ha' => _;
        obtain ⟨ K, hK ⟩ := show ∃ K : Finset (↥S), (SimpleGraph.induce (↑S) G).IsNClique a K from by
                              contrapose! ha';
                              refine' lt_of_le_of_lt ( csSup_le' _ ) ( Nat.pred_lt ( ne_bot_of_gt ha ) );
                              rintro n ⟨ s, hs ⟩;
                              refine' Nat.le_pred_of_lt ( lt_of_not_ge fun hn => ha' s _ );
                              obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( show a ≤ s.card from hn.trans ( hs.card_eq.symm ▸ le_rfl ) );
                              simp_all +decide [ SimpleGraph.isNClique_iff ];
                              refine' False.elim ( ha' t _ ht.2 );
                              exact fun x hx y hy hxy => hs.1 ( ht.1 hx ) ( ht.1 hy ) hxy;
        refine' h.1 ( Finset.image Subtype.val K ) ( Finset.image_subset_iff.mpr fun x hx => x.2 ) _;
        convert hK using 1;
        simp +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
        simp +decide [ SimpleGraph.isClique_iff, Set.Pairwise ];
        exact fun _ => ⟨ fun h x hx hx' y hy hy' hxy => h hx hx' hy hy' hxy, fun h x hx hx' y hy hy' hxy => h x hx hx' y hy hy' hxy ⟩;
      · contrapose! h;
        refine' lt_of_le_of_lt ( csSup_le' _ ) _;
        exact b - 1;
        · rintro n ⟨ s, hs ⟩;
          refine' Nat.le_sub_one_of_lt _;
          contrapose! h;
          intro h;
          obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( show b ≤ s.card from by linarith [ hs.2 ] );
          refine' ⟨ t.image Subtype.val, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, SimpleGraph.isNIndepSet_iff ];
          simp_all +decide [ SimpleGraph.IsIndepSet, Finset.card_image_of_injective, Function.Injective ];
          intro x hx y hy hxy; obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; have := hs.1 ( ht.1 _ _ hu ) ( ht.1 _ _ hv ) ; aesop;
        · exact Nat.pred_lt ( ne_bot_of_gt hb )

/-
If a large set of blocks are cliques and uniform, then $G$ has a large homogeneous set.
-/
lemma lemma_hom_from_uniform_W_cliques {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (m : ℕ)
    (h_disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (h_size : ∀ i, (B i).card = m)
    (h_rep : ∀ i, rep i ∈ B i)
    (W' : Finset (Fin N))
    (h_cliques : ∀ i ∈ W', G.IsNClique m (B i))
    (h_uniform : ∀ i ∈ W', ∀ j ∈ W', i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y ↔ G.Adj (rep i) (rep j))
    (r s : ℕ) (hr : r ≤ m * s)
    (hs : 2 ≤ s) (hr_ge_2 : 2 ≤ r)
    (hW' : (W'.card : ℝ) ≥ R s r) :
    hom_num G ≥ r := by
      -- Apply `lemma_ramsey_on_subset` to `R_graph G rep` and `W'` with parameters `s` and `r`.
      obtain ⟨K, hK⟩ : ∃ K ⊆ W', (R_graph G rep).IsClique K ∧ K.card ≥ s ∨ (R_graph G rep).IsIndepSet K ∧ K.card ≥ r := by
        have := @lemma_ramsey_on_subset ( Fin N );
        specialize this ( R_graph G rep ) W' s r hs hr_ge_2;
        rcases this ( mod_cast hW' ) with ( ⟨ K, hK₁, hK₂ ⟩ | ⟨ I, hI₁, hI₂ ⟩ ) <;> [ refine' ⟨ K, hK₁, Or.inl ⟨ _, _ ⟩ ⟩ ; refine' ⟨ I, hI₁, Or.inr ⟨ _, _ ⟩ ⟩ ] <;> simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ];
      rcases hK with ⟨ hK₁, hK₂ | hK₂ ⟩ <;> simp_all +decide [ SimpleGraph.isNClique_iff ];
      · have h_clique : G.cliqueNum ≥ K.card * m := by
          have h_clique : ∀ i ∈ K, G.IsNClique m (B i) := by
            exact fun i hi => by rw [ SimpleGraph.isNClique_iff ] ; specialize h_cliques i ( hK₁ hi ) ; aesop;
          have h_K_clique : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → G.Adj (rep i) (rep j) := by
            intros i hi j hj hij;
            have := hK₂.1 hi hj hij; simp_all +decide [ R_graph ] ;
            exact this.elim ( fun h => h ) fun h => h.symm
          have h_clique : G.cliqueNum ≥ K.card * m := by
            have h_union : ∃ K' ⊆ Finset.biUnion K B, G.IsNClique (K.card * m) K' := by
              have h_union : G.IsNClique (K.card * m) (Finset.biUnion K B) := by
                have h_union : ∀ x ∈ Finset.biUnion K B, ∀ y ∈ Finset.biUnion K B, x ≠ y → G.Adj x y := by
                  simp +zetaDelta at *;
                  intro x i hi hx y j hj hy hxy; cases eq_or_ne i j <;> simp_all +decide
                  · exact h_clique j hj |> fun h => h.1 ( by aesop ) ( by aesop ) hxy;
                  · exact h_uniform i ( hK₁ hi ) j ( hK₁ hj ) ‹_› x hx y hy |>.2 ( h_K_clique i hi j hj ‹_› );
                refine' ⟨ _, _ ⟩;
                · exact fun x hx y hy hxy => h_union x hx y hy hxy;
                · rw [ Finset.card_biUnion ] ; aesop;
                  exact fun i hi j hj hij => h_disjoint i j hij;
              exact ⟨ _, Finset.Subset.refl _, h_union ⟩
            obtain ⟨ K', hK'₁, hK'₂ ⟩ := h_union;
            exact le_csSup ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.2 ▸ Finset.card_le_univ _ ⟩ ⟨ K', hK'₂ ⟩;
          exact h_clique;
        exact le_trans ( by nlinarith ) ( h_clique.trans ( le_max_left _ _ ) );
      · have h_indep : G.indepNum ≥ K.card := by
          have h_ind : ∃ I ⊆ Finset.biUnion K (fun i => B i), G.IsNIndepSet K.card I := by
            use Finset.image (fun i => rep i) K;
            simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
            simp_all +decide [ Finset.subset_iff, SimpleGraph.IsIndepSet ];
            simp_all +decide [ Set.Pairwise ];
            refine' ⟨ fun i hi => ⟨ i, hi, h_rep i ⟩, _, _ ⟩;
            · intro i hi j hj hij; specialize hK₂; have := hK₂.1 hi hj; simp_all +decide [ R_graph ] ;
              exact hK₂.1 hi hj ( by aesop ) |>.1;
            · rw [ Finset.card_image_of_injOn ] ; intro i hi j hj hij ; have := hK₂.1 hi hj ; simp_all +decide
              exact Classical.not_not.1 fun hi' => Finset.disjoint_left.1 ( h_disjoint i j hi' ) ( h_rep i ) ( hij.symm ▸ h_rep j )
          obtain ⟨ I, hI₁, hI₂ ⟩ := h_ind;
          apply le_csSup;
          · exact ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
          · exact ⟨ I, hI₂ ⟩;
        exact le_trans hK₂.2 ( h_indep.trans ( le_max_right _ _ ) )

/-
If a large set of blocks are independent sets and uniform, then $G$ has a large homogeneous set.
-/
lemma lemma_hom_from_uniform_W_indep {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (m : ℕ)
    (h_disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (h_size : ∀ i, (B i).card = m)
    (h_rep : ∀ i, rep i ∈ B i)
    (W' : Finset (Fin N))
    (h_indep : ∀ i ∈ W', G.IsNIndepSet m (B i))
    (h_uniform : ∀ i ∈ W', ∀ j ∈ W', i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y ↔ G.Adj (rep i) (rep j))
    (r s : ℕ) (hr : r ≤ m * s)
    (hs : 2 ≤ s) (hr_ge_2 : 2 ≤ r)
    (hW' : (W'.card : ℝ) ≥ R r s) :
    hom_num G ≥ r := by
      -- Apply `lemma_ramsey_on_subset` to `R_graph G rep` and `W'` with parameters `r` and `s`.
      have h_subset : ∃ K ⊆ W', (R_graph G rep).IsClique K ∧ K.card = r ∨ ∃ I ⊆ W', (R_graph G rep).IsIndepSet I ∧ I.card = s := by
        have h_ramsey : ∀ (H : SimpleGraph (Fin N)), (Finset.card W' : ℝ) ≥ (R r s : ℝ) → (∃ K ⊆ W', H.IsClique K ∧ K.card = r) ∨ (∃ I ⊆ W', H.IsIndepSet I ∧ I.card = s) := by
          intro H hW';
          have := @lemma_ramsey_on_subset ( Fin N );
          specialize this H W' r s hr_ge_2 hs ( mod_cast hW' ) ; simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ] ;
        specialize h_ramsey ( R_graph G rep ) hW' ; aesop;
      obtain ⟨ K, hK₁, hK₂ ⟩ := h_subset;
      cases' hK₂ with hK₂ hK₂;
      · have h_clique : G.cliqueNum ≥ K.card := by
          have h_clique_def : ∃ K' ⊆ Finset.biUnion K B, G.IsClique K' ∧ K'.card = K.card := by
            refine' ⟨ Finset.image ( fun i => rep i ) K, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
            · exact fun i hi => ⟨ i, hi, h_rep i ⟩;
            · simp_all +decide [ SimpleGraph.IsClique, Set.Pairwise ];
              intro i hi j hj hij; specialize hK₂; have := hK₂.1 hi hj; simp_all +decide [ R_graph ] ;
              cases hK₂.1 hi hj ( by aesop ) <;> tauto;
            · rw [ Finset.card_image_of_injOn, hK₂.2 ];
              exact fun i hi j hj hij => Classical.not_not.1 fun hi' => Finset.disjoint_left.1 ( h_disjoint i j hi' ) ( h_rep i ) ( hij.symm ▸ h_rep j )
          obtain ⟨ K', hK'₁, hK'₂, hK'₃ ⟩ := h_clique_def;
          refine' le_trans _ ( le_csSup _ ⟨ K', hK'₂, hK'₃ ⟩ );
          · rfl;
          · exact ⟨ Fintype.card V, fun n hn => by obtain ⟨ s, hs ⟩ := hn; exact hs.card_eq ▸ Finset.card_le_univ _ ⟩;
        exact hK₂.2 ▸ h_clique.trans ( le_max_left _ _ );
      · obtain ⟨ I, hI₁, hI₂, rfl ⟩ := hK₂;
        -- Since $I$ is an independent set in $R_graph G rep$, the union of the blocks $B i$ for $i \in I$ is an independent set in $G$.
        have h_indep_union : G.IsNIndepSet (I.card * m) (Finset.biUnion I B) := by
          have h_indep_union : G.IsNIndepSet (I.card * m) (Finset.biUnion I B) := by
            have h_adj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, ¬G.Adj x y := by
              intros i hi j hj hij x hx y hy; have := h_uniform i ( hI₁ hi ) j ( hI₁ hj ) hij x hx y hy; simp_all +decide [ SimpleGraph.IsIndepSet ] ;
              exact fun h => hI₂ hi hj hij <| by tauto;
            have h_indep_union : G.IsNIndepSet (I.card * m) (Finset.biUnion I B) := by
              have h_card : (Finset.biUnion I B).card = I.card * m := by
                rw [ Finset.card_biUnion ] ; aesop;
                exact fun i hi j hj hij => h_disjoint i j hij
              have h_indep_union : ∀ x ∈ Finset.biUnion I B, ∀ y ∈ Finset.biUnion I B, x ≠ y → ¬G.Adj x y := by
                simp +contextual [ Finset.mem_biUnion ];
                intro x i hi hx y j hj hy hxy; by_cases hij : i = j <;> simp_all +decide
                · have := h_indep j ( hI₁ hj );
                  exact this.1 ( by aesop ) ( by aesop ) hxy;
                · exact h_adj i hi j hj hij x hx y hy;
              exact { isIndepSet := h_indep_union, card_eq := h_card };
            exact h_indep_union;
          exact h_indep_union;
        have h_indep_union : G.indepNum ≥ I.card * m := by
          have h_indep_union : ∃ I' : Finset V, G.IsNIndepSet (I.card * m) I' := by
            use Finset.biUnion I B;
          exact le_csSup ⟨ Fintype.card V, fun n hn => by obtain ⟨ I', hI' ⟩ := hn; exact hI'.card_eq ▸ Finset.card_le_univ _ ⟩ h_indep_union;
        exact le_trans hr ( by linarith ) |> le_trans <| le_max_right _ _ |> le_trans h_indep_union

/-
If there is a large uniform subset of indices $W$, then $G$ has a large homogeneous set.
-/
lemma lemma_hom_from_uniform_W {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {N : ℕ} (B : Fin N → Finset V) (rep : Fin N → V)
    (m : ℕ)
    (h_disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (h_size : ∀ i, (B i).card = m)
    (h_rep : ∀ i, rep i ∈ B i)
    (h_hom : ∀ i, G.IsNClique m (B i) ∨ G.IsNIndepSet m (B i))
    (W : Finset (Fin N))
    (h_uniform : ∀ i ∈ W, ∀ j ∈ W, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y ↔ G.Adj (rep i) (rep j))
    (r s : ℕ) (hr : r ≤ m * s)
    (hs : 2 ≤ s) (hr_ge_2 : 2 ≤ r)
    (hW : (W.card : ℝ) ≥ 2 * R r s) :
    hom_num G ≥ r := by
      -- Apply `lemma_large_homogeneous_subset` to get $W' \subseteq W$ with $|W'| \ge |W|/2 \ge R(r,s)$.
      obtain ⟨W', hW'_subset, hW'_card, hW'_hom⟩ : ∃ W' ⊆ W, (W'.card : ℝ) ≥ (W.card : ℝ) / 2 ∧ ((∀ i ∈ W', G.IsNClique m (B i)) ∨ (∀ i ∈ W', G.IsNIndepSet m (B i))) := by
        exact lemma_large_homogeneous_subset G B m h_hom W;
      cases' hW'_hom with hW'_clique hW'_indep;
      · -- Apply `lemma_hom_from_uniform_W_cliques` with the given parameters.
        apply lemma_hom_from_uniform_W_cliques G B rep m h_disjoint h_size h_rep W' hW'_clique (fun i hi j hj hij => h_uniform i (hW'_subset hi) j (hW'_subset hj) hij) r s hr hs hr_ge_2 (by
        rw [ lemma_ramsey_symm ];
        linarith);
      · -- Apply `lemma_hom_from_uniform_W_indep`.
        apply lemma_hom_from_uniform_W_indep G B rep m h_disjoint h_size h_rep W' hW'_indep (fun i hi j hj hij => h_uniform i (hW'_subset hi) j (hW'_subset hj) hij) r s hr hs hr_ge_2 (by
        linarith)

/-
Given the assumptions of the main theorem, there exists a family of $N$ disjoint homogeneous blocks of size $m$, with representatives, covering at least $0.9n$ vertices, such that elements in each block are close to their representative in terms of adjacency difference.
-/
lemma lemma_good_blocks_and_reps {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (m : ℕ) (hm : 2 ≤ m)
    (m₂ : ℕ) (hm₂ : m₂ = R m m)
    (ε γ : ℝ)
    (hε : ε = 1 / (100 * m₂))
    (hγ : γ = ε / 4)
    (A : Finset V)
    (hA : (A.card : ℝ) ≤ 2 * γ * n / Real.logb 2 n)
    (hI : (I_num G : ℝ) < (2 : ℝ) ^ (ε * n))
    (n_large : 1 - (2 * γ / Real.logb 2 n) - m₂ * (ε + 2 * γ) ≥ 0.9)
    (T : ℝ)
    (h_distinguish : ∀ x y : V, x ∉ A → y ∉ A → same_adj_to_A G A x y → (dif_size G x y : ℝ) < T) :
    ∃ (N : ℕ) (B : Fin N → Finset V) (rep : Fin N → V),
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, (B i).card = m) ∧
      (∀ i, rep i ∈ B i) ∧
      (∀ i, G.IsNClique m (B i) ∨ G.IsNIndepSet m (B i)) ∧
      (∀ i, ∀ x ∈ B i, (dif_size G (rep i) x : ℝ) < T) ∧
      ((N : ℝ) * m ≥ 0.9 * n) := by
        -- Let $L$ be the list of blocks given by `all_blocks_list G A m`.
        set L := all_blocks_list G A m;
        have hL_prop : ∀ b ∈ L, b.card = m ∧ (G.IsNClique m b ∨ G.IsNIndepSet m b) ∧ ∀ x ∈ b, x ∉ A := by
          intro b hb
          obtain ⟨p, hp⟩ : ∃ p : A → Bool, ∀ x ∈ b, pattern G A x = p := by
            have := all_blocks_props G A m hm; aesop;
          have := List.mem_flatMap.mp hb;
          obtain ⟨ a, ha, hb ⟩ := this;
          have := greedy_blocks_props G ( vertices_with_pattern G A a ) m hm;
          exact ⟨ this.2.1 b hb, this.2.2.1 b hb, fun x hx hx' => by have := this.1 b hb hx; simp_all +decide [ vertices_with_pattern ] ⟩;
        have hL_length : (L.length : ℝ) * m ≥ 0.9 * n := by
          convert lemma_blocks_count G n hn m hm m₂ hm₂ ε γ hε hγ A hA hI n_large using 1;
        refine' ⟨ L.length, fun i => L.get i, fun i => Classical.choose ( Finset.card_pos.mp ( by linarith [ hL_prop _ ( List.get_mem L i ) ] ) ), _, _, _, _, _ ⟩ <;> simp_all +decide [ Fin.ext_iff ];
        · have := all_blocks_props G A m hm;
          have := List.pairwise_iff_get.mp this.2.2.1;
          exact fun i j hij => by cases lt_or_gt_of_ne hij <;> [ exact this _ _ ‹_› ; exact Disjoint.symm ( this _ _ ‹_› ) ] ;
        · intro i; have := Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hL_prop ( L.get i ) ( List.get_mem _ _ ) ] ) ) ; aesop;
        · intro i x hx
          have h_same_pattern : ∀ x y : V, x ∈ L.get i → y ∈ L.get i → pattern G A x = pattern G A y := by
            have := all_blocks_props G A m hm;
            exact fun x y hx hy => by obtain ⟨ p, hp ⟩ := this.2.2.2.1 _ ( List.get_mem _ _ ) ; exact hp x hx ▸ hp y hy ▸ rfl;
          apply h_distinguish;
          · exact hL_prop _ ( List.get_mem _ _ ) |>.2.2 _ ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hL_prop _ ( List.get_mem L i ) ] ) ) );
          · exact hL_prop _ ( List.get_mem _ _ ) |>.2.2 _ hx;
          · exact fun a ha => by have := h_same_pattern _ _ ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hL_prop ( L.get i ) ( by simp ) ] ) ) ) hx; simp_all +decide [ funext_iff, pattern ] ;

/-
For sufficiently large $n$, the parameters $r$ and $s$ satisfy $r \ge 2$, $s \ge 2$, $r \le ms$, and $r > c \log n$.
-/
lemma lemma_rs_properties (c : ℝ) (hc : c > 0) (m : ℕ) (hm : m ≥ 1) :
  ∃ n₀, ∀ n ≥ n₀,
    let r := ⌊c * Real.logb 2 n⌋₊ + 1
    let s := ⌈(r : ℝ) / m⌉₊
    2 ≤ r ∧ 2 ≤ s ∧ (r : ℝ) ≤ (m : ℝ) * s ∧ (r : ℝ) > c * Real.logb 2 n := by
      refine' ⟨ 2 ^ ( m / c ), fun n hn => ⟨ _, _, _, _ ⟩ ⟩ <;> norm_num [ Nat.floor_add_natCast ];
      · refine' Nat.succ_le_succ ( Nat.floor_pos.mpr _ );
        rw [ Real.logb, mul_div, le_div_iff₀ ] <;> try positivity;
        have := Real.log_le_log ( by positivity ) hn;
        rw [ Real.log_rpow ] at this <;> nlinarith [ mul_div_cancel₀ ( m : ℝ ) hc.ne', Real.log_pos one_lt_two, show ( m : ℝ ) ≥ 1 by norm_cast ];
      · refine' Nat.lt_ceil.mpr _;
        rw [ lt_div_iff₀ ] <;> norm_cast;
        refine' Nat.lt_succ_of_le ( Nat.le_floor _ );
        rw [ Real.logb, mul_div, le_div_iff₀ ] <;> norm_num;
        · have := Real.log_le_log ( by positivity ) hn ; rw [ Real.log_rpow ( by positivity ) ] at this ; nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( m : ℝ ) hc.ne' ] ;
        · positivity;
      · exact_mod_cast Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( ( ⌊c * Real.logb 2 n⌋₊ + 1 : ℝ ) / m ), mul_div_cancel₀ ( ( ⌊c * Real.logb 2 n⌋₊ + 1 : ℝ ) : ℝ ) ( by positivity : ( m : ℝ ) ≠ 0 ) ] ;
      · exact Nat.lt_floor_add_one _

/-
Definitions of constants used in the proof of Shelah's theorem.
-/
noncomputable def shelah_k (c : ℝ) : ℕ :=
  Classical.choose (existence_of_k c)

lemma shelah_k_spec (c : ℝ) :
  let k := shelah_k c
  k ≥ 2 ∧ (c + 1) / k * Real.logb 2 (Real.exp 1 * (k + 1)) < 1 / 4 :=
  Classical.choose_spec (existence_of_k c)

noncomputable def shelah_m1 (c : ℝ) : ℕ := shelah_k c

noncomputable def shelah_m2 (c : ℝ) : ℕ := R (shelah_m1 c) (shelah_m1 c)

noncomputable def shelah_epsilon (c : ℝ) : ℝ := 1 / (100 * shelah_m2 c)

noncomputable def shelah_gamma (c : ℝ) : ℝ := (shelah_epsilon c) / 4

noncomputable def shelah_r (c : ℝ) (n : ℕ) : ℕ := ⌊c * Real.logb 2 n⌋₊ + 1

noncomputable def shelah_s (c : ℝ) (n : ℕ) : ℕ := ⌈(shelah_r c n : ℝ) / (shelah_m1 c)⌉₊

/-
Definition of n0 for Shelah's theorem.
-/
noncomputable def shelah_n0 (c : ℝ) (hc : c > 0) : ℕ :=
  let m2 := shelah_m2 c
  let γ := shelah_gamma c
  let k := shelah_k c
  let m1 := shelah_m1 c
  let n0_1_real := Classical.choose (arithmetic_bound m2 (by
  -- Since $R(k, k) \geq k$ for any $k \geq 1$, and $k \geq 2$, we have $R(k, k) \geq 2$.
  have h_R_ge_2 : ∀ k : ℕ, 2 ≤ k → R k k ≥ k := by
    intros k hk_ge_2
    have h_R_ge_k : ∀ N, N < k → ¬Ramsey_prop k k N := by
      intros N hN_lt_k
      simp [Ramsey_prop];
      use ⊥;
      constructor;
      · exact lt_of_le_of_lt ( csSup_le' fun x hx => by obtain ⟨ S, hS ⟩ := hx; exact hS.2 |> fun h => by have := Finset.card_le_univ S; aesop ) hN_lt_k;
      · refine' lt_of_le_of_lt _ hN_lt_k;
        refine' csSup_le' _;
        rintro n ⟨ s, hs ⟩;
        rcases hs with ⟨ hs₁, hs₂ ⟩;
        exact hs₂ ▸ le_trans ( Finset.card_le_univ _ ) ( by simp );
    exact le_csInf ⟨ _, Classical.choose_spec ( show ∃ N, Ramsey_prop k k N from by
                                                  exact ⟨ _, lemma_ramsey_prop_R k k hk_ge_2 hk_ge_2 ⟩ ) ⟩ fun N hN => not_lt.1 fun contra => h_R_ge_k N contra hN;
  exact le_trans ( by linarith [ shelah_k_spec c |>.1 ] ) ( h_R_ge_2 k ( shelah_k_spec c |>.1 ) )))
  let n0_1 := ⌈n0_1_real⌉₊
  let n0_2 := Classical.choose (lemma_distinguish.{0} γ (by
  simp +zetaDelta at *;
  unfold shelah_gamma shelah_epsilon shelah_m2; norm_num [ hc ] ; ring_nf ; norm_num [ Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_div, Nat.cast_ofNat ] ;
  -- Since $m1 \geq 2$, we have $R(m1, m1) \geq 2$, thus $1/(400*m1) < 1$.
  have h_R_ge_2 : 2 ≤ R (shelah_m1 c) (shelah_m1 c) := by
    -- Since $m1 \geq 2$, we have $R(m1, m1) \geq 2$ by definition.
    have h_R_ge_2 : 2 ≤ R m1 m1 := by
      have h_m1_ge_2 : 2 ≤ m1 := by
        exact shelah_k_spec c |>.1
      have h_R_ge_2 : Ramsey_prop m1 m1 (R m1 m1) := by
        exact lemma_ramsey_prop_R m1 m1 h_m1_ge_2 h_m1_ge_2;
      contrapose! h_R_ge_2;
      interval_cases R m1 m1 <;> simp_all +decide [ Ramsey_prop ];
      · use ⊥;
        constructor <;> refine' lt_of_le_of_lt ( csSup_le _ _ ) h_m1_ge_2 <;> norm_num;
        · exact ⟨ 0, by norm_num, ∅, by norm_num ⟩;
        · exact fun b a x h => a;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · simp +decide [ SimpleGraph.isNIndepSet_iff ];
      · use ⊥;
        simp +decide [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ];
        constructor;
        · exact lt_of_le_of_lt ( csSup_le ⟨ 0, by norm_num ⟩ fun n hn => hn.1 ) ( by linarith );
        · refine' lt_of_le_of_lt ( csSup_le _ _ ) h_m1_ge_2;
          · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
          · simp +decide [ SimpleGraph.isNIndepSet_iff ];
    exact h_R_ge_2;
  exact ⟨ by positivity, by rw [ inv_mul_lt_iff₀ ] <;> norm_num <;> linarith [ show ( R ( shelah_m1 c ) ( shelah_m1 c ) : ℝ ) ≥ 2 by exact_mod_cast h_R_ge_2 ] ⟩))
  let n0_3_real := Classical.choose (lemma_W_large_enough c hc k (shelah_k_spec c).1 (shelah_k_spec c).2 m1 rfl γ (by
  apply div_pos; apply one_div_pos.mpr; exact mul_pos (by norm_num) (by
  -- Since $R(k, k)$ is the Ramsey number, which is always positive for any $k \geq 2$, we have $0 < R(k, k)$.
  have h_R_pos : ∀ k : ℕ, 2 ≤ k → 0 < R k k := by
    intros k hk;
    refine' lt_of_lt_of_le zero_lt_one ( le_csInf _ _ );
    · -- By the definition of Ramsey numbers, R(k, k) exists and is finite for any k ≥ 2.
      have h_ramsey_exists : ∀ k : ℕ, 2 ≤ k → ∃ N : ℕ, Ramsey_prop k k N := by
        intro k hk; exact ⟨ _, lemma_ramsey_prop_R k k hk hk ⟩ ;
      exact h_ramsey_exists k hk;
    · rintro ( _ | _ | N ) <;> simp +arith +decide [ Ramsey_prop ];
      use ⊥;
      constructor <;> norm_num [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ];
      · refine' lt_of_le_of_lt ( csSup_le _ _ ) hk;
        · exact ⟨ 0, by norm_num, ∅, by norm_num ⟩;
        · exact fun n hn => hn.1;
      · refine' lt_of_le_of_lt ( csSup_le _ _ ) hk;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · simp +decide [ SimpleGraph.isNIndepSet_iff ];
  exact_mod_cast h_R_pos k ( shelah_k_spec c |>.1 )); exact by norm_num;))
  let n0_3 := ⌈n0_3_real⌉₊
  let n0_4_real := Classical.choose (lemma_rs_properties c hc m1 (by
  exact Nat.one_le_of_lt ( shelah_k_spec c |>.1 )))
  let n0_4 := ⌈n0_4_real⌉₊
  max (max n0_1 n0_2) (max n0_3 n0_4)

/-
The arithmetic bound holds for n >= shelah_n0.
-/
lemma shelah_n0_arithmetic_bound (c : ℝ) (hc : c > 0) (n : ℕ) (hn : n ≥ shelah_n0 c hc) :
  let m2 := shelah_m2 c
  let ε := shelah_epsilon c
  let γ := shelah_gamma c
  1 - (2 * γ / Real.logb 2 n) - m2 * (ε + 2 * γ) ≥ 0.9 := by
    have := Classical.choose_spec ( arithmetic_bound ( shelah_m2 c ) ( Nat.succ_le_of_lt ( show 0 < shelah_m2 c from ?_ ) ) );
    exact this n ( Nat.le_of_ceil_le <| le_trans ( le_max_of_le_left <| le_max_left _ _ ) hn );
    -- Since $R(k, k) \geq 2$ for any $k \geq 2$, and $k \geq 2$, we have $R(k, k) \geq 2$.
    have h_R_ge_2 : ∀ k : ℕ, 2 ≤ k → 2 ≤ R k k := by
      intros k hk_ge_2
      have h_R_ge_k : ∀ N, N < k → ¬Ramsey_prop k k N := by
        intros N hN_lt_k
        simp [Ramsey_prop];
        refine' ⟨ ⊥, _, _ ⟩ <;> norm_num [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ];
        · exact lt_of_le_of_lt ( csSup_le ⟨ 0, by norm_num, ∅, by norm_num ⟩ fun n hn => hn.1 ) ( by linarith );
        · refine' lt_of_le_of_lt ( csSup_le _ _ ) hN_lt_k <;> norm_num [ SimpleGraph.isNIndepSet_iff ];
          · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
          · exact fun a ha => le_trans ( Finset.card_le_univ _ ) ( by simp );
      exact Nat.succ_le_of_lt ( lt_of_lt_of_le ( by linarith ) ( le_csInf ( by exact ⟨ _, lemma_ramsey_prop_R k k hk_ge_2 hk_ge_2 ⟩ ) fun N hN => not_lt.1 fun contra => h_R_ge_k N contra hN ) );
    exact lt_of_lt_of_le zero_lt_two ( h_R_ge_2 _ ( shelah_k_spec c |>.1 ) )

lemma shelah_gamma_bounds (c : ℝ) :
  0 < shelah_gamma c ∧ shelah_gamma c < 1 := by
    -- By Lemma~\ref{lem:R_subtriples_def:shelah_m1_def:shelah_m1_def:shelah_m1_def:shelah_m1_def:shelah_m1_def:shelah_m1_def:shelah_m1}, $R(k,k) \geq k \geq 2$.
    have h_R_ge_two : 2 ≤ R (shelah_m1 c) (shelah_m1 c) := by
      have h_R_ge_k : ∀ k : ℕ, 2 ≤ k → R k k ≥ k := by
        intro k hk_2
        have h_R_ge_k : ∀ N, N < k → ¬Ramsey_prop k k N := by
          intros N hN_lt_k
          simp [Ramsey_prop];
          refine' ⟨ ⊥, _, _ ⟩ <;> norm_num [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ];
          · exact lt_of_le_of_lt ( csSup_le' fun n hn => hn.1 ) ( by linarith );
          · refine' lt_of_le_of_lt ( csSup_le _ _ ) hN_lt_k <;> norm_num [ SimpleGraph.isNIndepSet_iff ];
            · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
            · exact fun a ha => le_trans ( Finset.card_le_univ _ ) ( by simp );
        exact le_csInf ( by exact ⟨ _, lemma_ramsey_prop_R k k hk_2 hk_2 ⟩ ) fun N hN => not_lt.1 fun contra => h_R_ge_k N contra hN;
      exact le_trans ( shelah_k_spec c |>.1 ) ( h_R_ge_k _ ( shelah_k_spec c |>.1 ) );
    unfold shelah_gamma shelah_epsilon shelah_m2; norm_num ; ring_nf ; norm_num [ Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_div, Nat.cast_ofNat ];
    exact ⟨ pos_of_gt h_R_ge_two, by rw [ inv_mul_lt_iff₀ ] <;> norm_num <;> linarith [ show ( R ( shelah_m1 c ) ( shelah_m1 c ) : ℝ ) ≥ 2 by exact_mod_cast h_R_ge_two ] ⟩

/-
The distinguishing property holds for n >= shelah_n0.
-/
lemma shelah_n0_distinguish (c : ℝ) (hc : c > 0) (n : ℕ) (hn : n ≥ shelah_n0 c hc) :
  let γ := shelah_gamma c
  let T := param_T γ n
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    ∃ A : Finset V, A.Nonempty ∧
      (A.card : ℝ) ≤ 2 * γ * n / Real.logb 2 n ∧
      ∀ x y : V, x ∉ A → y ∉ A →
        same_adj_to_A G A x y →
        (dif_size G x y : ℝ) < T := by
          convert Classical.choose_spec ( lemma_distinguish ( shelah_gamma c ) ( shelah_gamma_bounds c ) );
          any_goals exact Fin n;
          refine' ⟨ fun h => _, fun h => _ ⟩;
          any_goals try infer_instance;
          · intro G _ n_1 hn_1 hn_1';
            convert Classical.choose_spec ( lemma_distinguish ( shelah_gamma c ) ( shelah_gamma_bounds c ) ) _ _ _ _;
            · infer_instance;
            · exact hn_1;
            · convert hn_1' using 1;
          · intro γ T V _ _ G _ hn_card
            obtain ⟨A, hA_nonempty, hA_size, hA_dist⟩ := h (SimpleGraph.map (Fintype.equivFinOfCardEq hn_card) G) n (by simp) (by
            exact le_trans ( Nat.le_ceil _ ) ( le_trans ( Nat.cast_le.mpr ( le_max_right _ _ ) ) ( le_trans ( le_max_left _ _ ) hn ) ));
            use Finset.image (fun x => (Fintype.equivFinOfCardEq hn_card).symm x) A;
            refine' ⟨ _, _, _ ⟩;
            · exact ⟨ _, Finset.mem_image_of_mem _ hA_nonempty.choose_spec ⟩;
            · rwa [ Finset.card_image_of_injective _ ( Fintype.equivFinOfCardEq hn_card |> Equiv.symm |> Equiv.injective ) ];
            · intro x y hx hy hxy;
              convert hA_dist ( Fintype.equivFinOfCardEq hn_card x ) ( Fintype.equivFinOfCardEq hn_card y ) _ _ _ using 1;
              · simp +decide [ dif_size ];
                simp +decide [ SimpleGraph.neighborFinset, symmDiff ];
                refine' Finset.card_bij ( fun z hz => Fintype.equivFinOfCardEq hn_card z ) _ _ _ <;> simp +decide [ SimpleGraph.neighborSet ];
                grind;
              · grind;
              · exact fun h => hy <| Finset.mem_image.mpr ⟨ _, h, by simp +decide ⟩;
              · intro a ha;
                convert hxy ( Fintype.equivFinOfCardEq hn_card |>.symm a ) _ using 1 <;> simp +decide [ ha ];
                · grind;
                · grind

/-
The W size condition holds for n >= shelah_n0.
-/
lemma shelah_n0_W_large (c : ℝ) (hc : c > 0) (n : ℕ) (hn : n ≥ shelah_n0 c hc) :
  let m1 := shelah_m1 c
  let γ := shelah_gamma c
  let r := shelah_r c n
  let s := shelah_s c n
  let T := param_T γ n
  let N_min := 0.9 * (n : ℝ) / (m1 : ℝ)
  let W_size := N_min / (2 * (((m1 : ℝ) - 1) * T) + 1)
  W_size / 2 ≥ (R r s : ℝ) := by
    have := Classical.choose_spec ( lemma_W_large_enough c hc ( shelah_k c ) ( shelah_k_spec c |>.1 ) ( shelah_k_spec c |>.2 ) ( shelah_m1 c ) rfl ( shelah_gamma c ) ( by
      unfold shelah_gamma shelah_epsilon shelah_m2; norm_num [ hc ] ; ring_nf ;
      have h_R_pos : ∀ k : ℕ, 2 ≤ k → 0 < R k k := by
        intro k hk
        have h_ramsey_exists : ∃ N : ℕ, Ramsey_prop k k N := by
          exact ⟨ _, lemma_ramsey_prop_R k k hk hk ⟩
        obtain ⟨N, hN⟩ := h_ramsey_exists
        exact lt_of_lt_of_le zero_lt_one ( le_csInf ( show { N : ℕ | Ramsey_prop k k N }.Nonempty from ⟨ N, hN ⟩ ) fun n hn => by
                                                        rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Ramsey_prop ];
                                                        specialize hn ⊥ ; simp_all +decide [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ];
                                                        rcases hn with ( hn | hn ) <;> [ exact absurd hn ( not_le_of_gt ( lt_of_le_of_lt ( csSup_le ⟨ 0, by norm_num ⟩ fun n hn => hn.1 ) ( by linarith ) ) ) ; exact absurd hn ( not_le_of_gt ( lt_of_le_of_lt ( csSup_le ⟨ 0, by norm_num ⟩ fun n hn => by obtain ⟨ s, hs ⟩ := hn; fin_cases s ; aesop ) ( by linarith ) ) ) ];
                                                        simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
                                                        exact hn.not_gt <| lt_of_le_of_lt ( csSup_le ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩ fun n hn => by obtain ⟨ s, hs ⟩ := hn; fin_cases s ; aesop ) <| by linarith; );
      exact h_R_pos _ ( shelah_k_spec c |>.1 ) ) ) n ( by
      exact le_trans ( Nat.le_ceil _ ) ( mod_cast hn.trans' ( by unfold shelah_n0; aesop ) ) )
    generalize_proofs at *;
    convert this using 1

/-
If I(G) is small, then hom(G) is large.
-/
lemma shelah_hom_lower_bound (c : ℝ) (hc : c > 0) (n : ℕ) (hn : n ≥ shelah_n0 c hc)
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (hV : Fintype.card V = n)
  (hI : (I_num G : ℝ) < (2 : ℝ) ^ (shelah_epsilon c * n)) :
  hom_num G ≥ shelah_r c n := by
    -- Let's choose the set A from the hypothesis Shellah_n0_distinguish.
    obtain ⟨A, hA_nonempty, hA_card, hA_distinguish⟩ := shelah_n0_distinguish c hc n hn G hV;
    -- Use `lemma_good_blocks_and_reps` to get $B$ and $rep$.
    obtain ⟨N, B, rep, hB_disjoint, hB_size, hB_rep, hB_hom, hB_dif, hN⟩ : ∃ (N : ℕ) (B : Fin N → Finset V) (rep : Fin N → V),
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, (B i).card = shelah_m1 c) ∧
      (∀ i, rep i ∈ B i) ∧
      (∀ i, G.IsNClique (shelah_m1 c) (B i) ∨ G.IsNIndepSet (shelah_m1 c) (B i)) ∧
      (∀ i, ∀ x ∈ B i, (dif_size G (rep i) x : ℝ) < param_T (shelah_gamma c) n) ∧
      ((N : ℝ) * shelah_m1 c ≥ 0.9 * n) := by
        apply_rules [ lemma_good_blocks_and_reps ];
        · exact shelah_k_spec c |>.1;
        · convert shelah_n0_arithmetic_bound c hc n hn using 1;
    -- Use `lemma_uniform_subset_existence` to get $W$.
    obtain ⟨W, hW_card, hW_uniform⟩ : ∃ W : Finset (Fin N),
      (W.card : ℝ) ≥ (N : ℝ) / (2 * ((shelah_m1 c - 1) * param_T (shelah_gamma c) n) + 1) ∧
      ∀ i ∈ W, ∀ j ∈ W, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, G.Adj x y ↔ G.Adj (rep i) (rep j) := by
        exact
          lemma_uniform_subset_existence G B rep (shelah_m1 c) (param_T (shelah_gamma c) n)
            hB_disjoint hB_size hB_rep hB_dif;
    -- Use `shelah_n0_W_large` to show $|W| \ge 2 R(r, s)$.
    have hW_large : (W.card : ℝ) ≥ 2 * R (shelah_r c n) (shelah_s c n) := by
      have := shelah_n0_W_large c hc n hn;
      refine le_trans ( mul_le_mul_of_nonneg_left this zero_le_two ) ?_;
      refine le_trans ?_ hW_card;
      rw [ mul_div_cancel₀ _ two_ne_zero ];
      gcongr;
      · exact add_nonneg ( mul_nonneg zero_le_two ( mul_nonneg ( sub_nonneg.mpr ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by
          exact ne_of_gt ( shelah_k_spec c |>.1.trans_lt' ( by decide ) ) ) ) ) ( by
          exact mul_nonneg ( div_nonneg ( by norm_num ) ( by linarith [ show 0 ≤ shelah_gamma c by exact div_nonneg ( by exact one_div_nonneg.mpr ( by exact mul_nonneg ( by norm_num ) ( by exact Nat.cast_nonneg _ ) ) ) ( by norm_num ) ] ) ) ( sq_nonneg _ ) ) ) ) zero_le_one;
      · rw [ div_le_iff₀ ] <;> nlinarith [ show ( shelah_m1 c : ℝ ) ≥ 2 by exact_mod_cast shelah_k_spec c |>.1 ];
    -- Use `lemma_rs_properties` to show $r \le m1 * s$ and $s \ge 2$ and $r \ge 2$.
    have h_rs_properties : 2 ≤ shelah_r c n ∧ 2 ≤ shelah_s c n ∧ (shelah_r c n : ℝ) ≤ (shelah_m1 c : ℝ) * shelah_s c n ∧ (shelah_r c n : ℝ) > c * Real.logb 2 n := by
      have := Classical.choose_spec ( lemma_rs_properties c hc ( shelah_m1 c ) ( by
        exact Nat.succ_le_of_lt ( shelah_k_spec c |>.1.trans_lt' ( by norm_num ) ) ) ) n ( by
        exact le_trans ( Nat.le_ceil _ ) ( Nat.cast_le.mpr ( le_trans ( le_max_right _ _ ) ( le_trans ( le_max_right _ _ ) hn ) ) ) );
      exact this;
    apply lemma_hom_from_uniform_W G B rep (shelah_m1 c) hB_disjoint hB_size hB_rep hB_hom W hW_uniform (shelah_r c n) (shelah_s c n) (by
    exact_mod_cast h_rs_properties.2.2.1) (by
    exact h_rs_properties.2.1) (by
    exact h_rs_properties.1) (by
    exact hW_large)

/-
shelah_epsilon is positive.
-/
lemma shelah_epsilon_pos (c : ℝ) : shelah_epsilon c > 0 := by
  -- Since $m2 = R(k, k)$ and $R(k, k) \geq k$ for $k \geq 2$, we have $m2 \geq 2$.
  have h_m2_ge_2 : 2 ≤ shelah_m2 c := by
    have h_R_ge_2 : ∀ k : ℕ, 2 ≤ k → 2 ≤ R k k := by
      intros k hk
      have h_R_ge_k : Ramsey_prop k k (R k k) := by
        exact lemma_ramsey_prop_R k k hk hk;
      contrapose! h_R_ge_k;
      interval_cases _ : R k k <;> simp_all +decide [ Ramsey_prop ];
      · use ⊥;
        constructor <;> refine' lt_of_le_of_lt ( csSup_le _ _ ) hk <;> norm_num;
        · exact ⟨ 0, by norm_num, ∅, by norm_num ⟩;
        · exact fun b a x h => a;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · simp +decide [ SimpleGraph.isNIndepSet_iff ];
      · use ⊥; simp +decide [ SimpleGraph.cliqueNum, SimpleGraph.indepNum ] ;
        constructor <;> refine' lt_of_le_of_lt ( csSup_le _ _ ) hk <;> norm_num;
        · exact ⟨ 0, by norm_num, ∅, by norm_num ⟩;
        · exact fun b a x h => a;
        · exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        · simp +decide [ SimpleGraph.isNIndepSet_iff ];
    exact h_R_ge_2 _ ( shelah_k_spec c |>.1 );
  exact one_div_pos.mpr ( by positivity )

/-
shelah_r(c, n) is strictly greater than c * log2(n).
-/
lemma shelah_r_gt (c : ℝ) (n : ℕ) : (shelah_r c n : ℝ) > c * Real.logb 2 n := by
  exact Nat.lt_of_floor_lt ( Nat.lt_succ_self _ )

/-
If hom(G) is both <= c log n and >= shelah_r(c, n), we have a contradiction.
-/
lemma shelah_contradiction {V : Type*} [Fintype V] (c : ℝ) (n : ℕ) (G : SimpleGraph V)
  (h1 : (hom_num G : ℝ) ≤ c * Real.logb 2 n)
  (h2 : hom_num G ≥ shelah_r c n) : False := by
    exact h1.not_gt ( lt_of_lt_of_le ( shelah_r_gt c n ) ( Nat.cast_le.mpr h2 ) )

/-
If n >= n0 and hom(G) <= c log n, then I(G) >= 2^(epsilon * n).
-/
lemma shelah_contrapositive (c : ℝ) (hc : c > 0) (n : ℕ) (hn : n ≥ shelah_n0 c hc)
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (hV : Fintype.card V = n)
  (h_hom : (hom_num G : ℝ) ≤ c * Real.logb 2 n) :
  (I_num G : ℝ) ≥ (2 : ℝ) ^ (shelah_epsilon c * n) := by
    -- By contradiction, assume `(I_num G : ℝ) < (2 : ℝ) ^ (shelah_epsilon c * n)`.
    by_contra h_contra;
    have := shelah_hom_lower_bound c hc n hn G hV ( lt_of_not_ge h_contra );
    exact shelah_contradiction c n G ( mod_cast h_hom ) this

/-
Theorem 1: For every real c > 0, there exist constants ε > 0 and n₀ such that if n ≥ n₀ and G is a graph on n vertices with hom(G) ≤ c log n, then I(G) ≥ 2^(εn).
-/
theorem erdos_1036 (c : ℝ) (hc : c > 0) :
  ∃ (ε : ℝ), ε > 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
  Fintype.card V = n →
  (hom_num G : ℝ) ≤ c * Real.logb 2 n →
  (I_num G : ℝ) ≥ (2 : ℝ) ^ (ε * n) :=
  ⟨shelah_epsilon c, shelah_epsilon_pos c, shelah_n0 c hc, fun n hn _ _ _ G _ hV h_hom => shelah_contrapositive c hc n hn G hV h_hom⟩

#print axioms erdos_1036
-- 'erdos_1036' depends on axioms: [propext, Classical.choice, Quot.sound]
