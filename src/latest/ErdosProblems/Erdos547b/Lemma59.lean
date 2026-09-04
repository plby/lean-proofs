/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RegularPair

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma59

open Finset Fintype SimpleGraph

variable {V : Type*} [DecidableEq V]

/-!
This file isolates the genuinely graph-theoretic greedy core of Zhao's
Lemmas 5.2 and 5.9.  The source derives the hypotheses below from regular
pairs and matching-capacity inequalities.  Expressing the conclusion in
terms of candidate sets makes the online/flexibility invariant explicit:
after fewer than `card A` target vertices have been used, every next vertex
still has an unused candidate.
-/

/-- Leaf-induction core for a rooted tree with a separate candidate set for
every non-root vertex.  The asymmetric `b ≠ root` condition is intentional:
the induction never has to embed the distinguished root. -/
private theorem exists_rooted_candidate_copy_aux
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card A = n + 1) (hT : T.IsTree)
    (root : A) (candidate : A → Finset B) (rootImage : B)
    (hroot : ∀ ⦃a⦄, T.Adj root a →
      Fintype.card A ≤ #{w ∈ candidate a | G.Adj rootImage w})
    (hcross : ∀ ⦃a b⦄, T.Adj a b → b ≠ root → ∀ v ∈ candidate a,
      Fintype.card A ≤ #{w ∈ candidate b | G.Adj v w}) :
    ∃ f : T.Copy G, f root = rootImage ∧
      ∀ a, a ≠ root → f a ∈ candidate a := by
  classical
  induction n generalizing A with
  | zero =>
      have hsub : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      let F : A → B := fun _ ↦ rootImage
      have hF_inj : Function.Injective F := fun a b _ ↦ hsub.elim a b
      let f : T.Copy G :=
        ⟨⟨F, fun {a b} hab ↦ False.elim (T.ne_of_adj hab (hsub.elim a b))⟩, hF_inj⟩
      refine ⟨f, rfl, ?_⟩
      intro a ha
      exact False.elim (ha (hsub.elim a root))
  | succ n ih =>
      have hcard_large : 1 < Fintype.card A := by omega
      let : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp hcard_large
      obtain ⟨x₀, x₁, hxne, hx₀deg, hx₁deg⟩ :=
        hT.exists_ne_and_degree_eq_one
      obtain ⟨x, hxroot, hxdeg⟩ : ∃ x : A, x ≠ root ∧ T.degree x = 1 := by
        by_cases h : x₀ = root
        · exact ⟨x₁, fun h' ↦ hxne (h.trans h'.symm), hx₁deg⟩
        · exact ⟨x₀, h, hx₀deg⟩
      obtain ⟨parent, hxparent, hparent_unique⟩ :=
        degree_eq_one_iff_existsUnique_adj.mp hxdeg
      let s : Set A := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      let root' : s := ⟨root, by simpa [s] using hxroot.symm⟩
      let candidate' : s → Finset B := fun a ↦ candidate a
      have hcard' : Fintype.card s = n + 1 := by
        have hc := Fintype.card_subtype_compl (fun a : A ↦ a = x)
        change Fintype.card {a : A // ¬a = x} = n + 1
        rw [hc, hcard]
        simp
      have hT' : T'.IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg,
          hT.isAcyclic.induce s⟩
      have hroot' : ∀ ⦃a : s⦄, T'.Adj root' a →
          Fintype.card s ≤ #{w ∈ candidate' a | G.Adj rootImage w} := by
        intro a ha
        exact (show Fintype.card s ≤ Fintype.card A by omega).trans
          (hroot (by simpa [T', root'] using ha))
      have hcross' : ∀ ⦃a b : s⦄, T'.Adj a b → b ≠ root' →
          ∀ v ∈ candidate' a,
            Fintype.card s ≤ #{w ∈ candidate' b | G.Adj v w} := by
        intro a b hab hb v hv
        apply (show Fintype.card s ≤ Fintype.card A by omega).trans
        apply hcross (by simpa [T'] using hab)
          (by intro h; apply hb; exact Subtype.ext h)
        exact hv
      obtain ⟨f, hfroot, hfmem⟩ :=
        ih T' hcard' hT' root' candidate' hroot' hcross'
      let parent' : s := ⟨parent, by simpa [s] using hxparent.ne'⟩
      let choices : Finset B := (candidate x).filter (G.Adj (f parent'))
      have hchoices : Fintype.card A ≤ #choices := by
        by_cases hp : parent = root
        · subst parent
          have hfp : f parent' = rootImage := by
            simpa [parent', root'] using hfroot
          change Fintype.card A ≤ #((candidate x).filter (G.Adj (f parent')))
          rw [hfp]
          exact hroot hxparent.symm
        · have hpmem : f parent' ∈ candidate parent := by
            have := hfmem parent' (by
              intro h
              apply hp
              exact Subtype.ext_iff.mp h)
            simpa [parent', candidate'] using this
          exact hcross hxparent.symm hxroot (f parent') hpmem
      let used : Finset B := univ.image f
      have hused : #used = Fintype.card s :=
        Finset.card_image_iff.mpr fun _ _ _ _ h ↦ f.injective h
      have hused_lt : #used < #choices := by omega
      obtain ⟨w, hwchoices, hwunused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hused_lt
      have hwmem : w ∈ candidate x := (mem_filter.mp hwchoices).1
      have hwadj : G.Adj (f parent') w := (mem_filter.mp hwchoices).2
      have hw_not_range : ∀ a : s, w ≠ f a := by
        intro a hwa
        apply hwunused
        exact mem_image.mpr ⟨a, mem_univ a, hwa.symm⟩
      let F : A → B := fun a ↦ if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      have hF_adj : ∀ ⦃a b⦄, T.Adj a b → G.Adj (F a) (F b) := by
        intro a b hab
        by_cases ha : a = x
        · subst a
          have hbp : b = parent := hparent_unique b hab
          subst b
          simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj.symm
        · by_cases hb : b = x
          · subst b
            have hap : a = parent := hparent_unique a hab.symm
            subst a
            simpa [F, parent', hxparent.ne, hxparent.ne'] using hwadj
          · let a' : s := ⟨a, by simpa [s] using ha⟩
            let b' : s := ⟨b, by simpa [s] using hb⟩
            have hab' : T'.Adj a' b' := by simpa [T', a', b'] using hab
            have hmap := f.toHom.map_rel hab'
            simpa [F, ha, hb, a', b'] using hmap
      have hF_inj : Function.Injective F := by
        intro a b hab
        by_cases ha : a = x
        · subst a
          by_cases hb : b = x
          · exact hb.symm
          · exfalso
            apply hw_not_range ⟨b, by simpa [s] using hb⟩
            simpa [F, hb] using hab
        · by_cases hb : b = x
          · subst b
            exfalso
            apply hw_not_range ⟨a, by simpa [s] using ha⟩
            simpa [F, ha] using hab.symm
          · have hsub : (⟨a, by simpa [s] using ha⟩ : s) =
                ⟨b, by simpa [s] using hb⟩ := by
              apply f.injective
              simpa [F, ha, hb] using hab
            exact Subtype.ext_iff.mp hsub
      let f' : T.Copy G := ⟨⟨F, fun {a b} hab ↦ hF_adj hab⟩, hF_inj⟩
      refine ⟨f', ?_, ?_⟩
      · show F root = rootImage
        simp only [F, dif_neg hxroot.symm]
        simpa [root'] using hfroot
      · intro a haroot
        by_cases ha : a = x
        · subst a
          simpa [f', F] using hwmem
        · have hsub_ne : (⟨a, by simpa [s] using ha⟩ : s) ≠ root' := by
            intro h
            apply haroot
            exact Subtype.ext_iff.mp h
          have := hfmem ⟨a, by simpa [s] using ha⟩ hsub_ne
          simpa [f', F, ha, candidate'] using this

/-- Candidate-set form of the greedy rooted-tree embedding lemma. -/
theorem exists_rooted_candidate_copy
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (root : A) (candidate : A → Finset B) (rootImage : B)
    (hroot : ∀ ⦃a⦄, T.Adj root a →
      Fintype.card A ≤ #{w ∈ candidate a | G.Adj rootImage w})
    (hcross : ∀ ⦃a b⦄, T.Adj a b → b ≠ root → ∀ v ∈ candidate a,
      Fintype.card A ≤ #{w ∈ candidate b | G.Adj v w}) :
    ∃ f : T.Copy G, f root = rootImage ∧
      ∀ a, a ≠ root → f a ∈ candidate a := by
  apply exists_rooted_candidate_copy_aux T G (Fintype.card A - 1)
  · have hpos : 0 < Fintype.card A :=
      Fintype.card_pos_iff.mpr hT.connected.nonempty
    omega
  · exact hT
  · exact hroot
  · exact hcross

/-- Cone over a rooted forest: the new vertex is adjacent precisely to the
declared component roots.  Requiring this cone to be a tree is a concise,
exact encoding that the roots select exactly one vertex in each component. -/
def rootedForestCone {A : Type*} [DecidableEq A]
    (F : SimpleGraph A) (roots : Finset A) : SimpleGraph (Option A) where
  Adj x y := match x, y with
    | none, some b => b ∈ roots
    | some a, none => a ∈ roots
    | some a, some b => F.Adj a b
    | none, none => False
  symm := by
    constructor
    intro x y
    cases x <;> cases y <;> simp [F.adj_comm]
  loopless := by
    constructor
    intro x
    cases x <;> simp

/-- A cone over the host graph in which the new vertex sees every old
vertex. -/
def hostCone {B : Type*} (G : SimpleGraph B) : SimpleGraph (Option B) where
  Adj x y := match x, y with
    | none, some _ => True
    | some _, none => True
    | some a, some b => G.Adj a b
    | none, none => False
  symm := by
    constructor
    intro x y
    cases x <;> cases y <;> simp [G.adj_comm]
  loopless := by
    constructor
    intro x
    cases x <;> simp

/-- Greedy embedding of a rooted forest with vertex-dependent candidate
sets.  `rootedForestCone F roots` being a tree is the rooted-forest
hypothesis; the `+ 1` is the harmless artificial cone vertex. -/
theorem exists_forest_candidate_copy
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (roots : Finset A) (hforest : (rootedForestCone F roots).IsTree)
    (candidate : A → Finset B)
    (hsize : ∀ a ∈ roots, Fintype.card A + 1 ≤ #(candidate a))
    (hcross : ∀ ⦃a b⦄, F.Adj a b → ∀ v ∈ candidate a,
      Fintype.card A + 1 ≤ #{w ∈ candidate b | G.Adj v w}) :
    ∃ f : F.Copy G, ∀ a, f a ∈ candidate a := by
  classical
  let candidateCone : Option A → Finset (Option B)
    | none => ∅
    | some a => (candidate a).image some
  have hcardCone : Fintype.card (Option A) = Fintype.card A + 1 := by simp
  obtain ⟨fc, hfcroot, hfcmem⟩ :=
    exists_rooted_candidate_copy (rootedForestCone F roots) (hostCone G)
      hforest none candidateCone none (by
        intro a ha
        cases a with
        | none => simp [rootedForestCone] at ha
        | some a =>
            have haroot : a ∈ roots := by simpa [rootedForestCone] using ha
            have hall : ∀ w ∈ (candidate a).image some,
                (hostCone G).Adj none w := by
              intro w hw
              obtain ⟨b, hb, rfl⟩ := mem_image.mp hw
              simp [hostCone]
            rw [filter_eq_self.mpr hall,
              Finset.card_image_iff.mpr (fun _ _ _ _ h ↦ Option.some.inj h)]
            simpa [hcardCone] using hsize a haroot) (by
        intro a b hab hb v hv
        cases a with
        | none => simp [candidateCone] at hv
        | some a =>
            cases b with
            | none => exact False.elim (hb rfl)
            | some b =>
                have habF : F.Adj a b := by simpa [rootedForestCone] using hab
                obtain ⟨v', hv', rfl⟩ := by
                  simpa [candidateCone] using hv
                have heq :
                    {w ∈ (candidate b).image some | (hostCone G).Adj (some v') w} =
                      ((candidate b).filter (G.Adj v')).image some := by
                  ext w
                  cases w with
                  | none =>
                      constructor
                      · intro hw
                        obtain ⟨himage, _⟩ := mem_filter.mp hw
                        obtain ⟨x, _, hx⟩ := mem_image.mp himage
                        cases hx
                      · intro hw
                        obtain ⟨x, _, hx⟩ := mem_image.mp hw
                        cases hx
                  | some w =>
                      constructor
                      · intro hw
                        obtain ⟨himage, hadj⟩ := mem_filter.mp hw
                        obtain ⟨x, hx, hxw⟩ := mem_image.mp himage
                        have hxw' : x = w := Option.some.inj hxw
                        subst x
                        apply mem_image.mpr
                        exact ⟨w, mem_filter.mpr ⟨hx, by simpa [hostCone] using hadj⟩, rfl⟩
                      · intro hw
                        obtain ⟨x, hx, hxw⟩ := mem_image.mp hw
                        have hxw' : x = w := Option.some.inj hxw
                        subst x
                        obtain ⟨hx, hadj⟩ := mem_filter.mp hx
                        apply mem_filter.mpr
                        exact ⟨mem_image.mpr ⟨w, hx, rfl⟩, by simpa [hostCone] using hadj⟩
                rw [heq, Finset.card_image_iff.mpr
                  (fun _ _ _ _ h ↦ Option.some.inj h)]
                simpa [hcardCone] using hcross habF v' hv')
  have hsome : ∀ a : A, ∃ b ∈ candidate a, fc (some a) = some b := by
    intro a
    have hm := hfcmem (some a) (by simp)
    simp only [candidateCone, mem_image] at hm
    obtain ⟨b, hb, hba⟩ := hm
    exact ⟨b, hb, hba.symm⟩
  choose f hfmem hfc using hsome
  have hfadj : ∀ ⦃a b⦄, F.Adj a b → G.Adj (f a) (f b) := by
    intro a b hab
    have hcAdj := fc.toHom.map_rel (show (rootedForestCone F roots).Adj (some a) (some b) by
      simpa [rootedForestCone] using hab)
    change (hostCone G).Adj (fc (some a)) (fc (some b)) at hcAdj
    rw [hfc a, hfc b] at hcAdj
    simpa [hostCone] using hcAdj
  have hfinj : Function.Injective f := by
    intro a b hab
    have hc : fc (some a) = fc (some b) := by rw [hfc a, hfc b, hab]
    exact Option.some.inj (fc.injective hc)
  exact ⟨⟨⟨f, fun {a b} hab ↦ hfadj hab⟩, hfinj⟩, hfmem⟩

/-- Flexible form of `exists_forest_candidate_copy`.  An arbitrary set of at
most `q` previously occupied target vertices may be forbidden.  This is the
formal content of Zhao's notation that every prescribed image has `q`
choices. -/
theorem exists_forest_candidate_copy_avoiding
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (roots : Finset A) (hforest : (rootedForestCone F roots).IsTree)
    (candidate : A → Finset B) (q : ℕ)
    (hsize : ∀ a ∈ roots, Fintype.card A + 1 + q ≤ #(candidate a))
    (hcross : ∀ ⦃a b⦄, F.Adj a b → ∀ v ∈ candidate a,
      Fintype.card A + 1 + q ≤ #{w ∈ candidate b | G.Adj v w})
    (forbidden : Finset B) (hforbidden : #forbidden ≤ q) :
    ∃ f : F.Copy G, ∀ a, f a ∈ candidate a ∧ f a ∉ forbidden := by
  let available : A → Finset B := fun a ↦ candidate a \ forbidden
  have havailSize : ∀ a ∈ roots,
      Fintype.card A + 1 ≤ #(available a) := by
    intro a ha
    have hsub : candidate a ⊆ available a ∪ forbidden := by
      intro w hw
      by_cases hforb : w ∈ forbidden
      · exact mem_union_right _ hforb
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hw, hforb⟩)
    have hcard : #(candidate a) ≤ #(available a) + #forbidden :=
      (card_le_card hsub).trans (card_union_le _ _)
    have hs := hsize a ha
    omega
  have havailCross : ∀ ⦃a b⦄, F.Adj a b → ∀ v ∈ available a,
      Fintype.card A + 1 ≤ #{w ∈ available b | G.Adj v w} := by
    intro a b hab v hv
    have hvCandidate : v ∈ candidate a := (mem_sdiff.mp hv).1
    have hdeg : Fintype.card A + 1 + #forbidden ≤
        #{w ∈ candidate b | G.Adj v w} := by
      exact (Nat.add_le_add_left hforbidden (Fintype.card A + 1)).trans
        (hcross hab v hvCandidate)
    simpa [available] using
      RegularPair.card_neighbors_cleaned_ge G (candidate b) forbidden v
        (Fintype.card A + 1) hdeg
  obtain ⟨f, hf⟩ :=
    exists_forest_candidate_copy F G roots hforest available havailSize havailCross
  refine ⟨f, ?_⟩
  intro a
  simpa [available] using (mem_sdiff.mp (hf a))

/-- The placement core of Zhao Lemma 5.2.  Roots use `X0`, other even-level
vertices use `X1`, and odd-level vertices may use either `Y1` or `Z1`.
The pointwise inequalities are precisely the invariant supplied by regular
pair typicality after already occupied vertices have been removed. -/
theorem lemma5_2_candidate_core
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (roots : Finset A) (hforest : (rootedForestCone F roots).IsTree)
    (level : A → ℕ) (hrootLevel : ∀ a ∈ roots, level a = 0)
    (hparity : ∀ ⦃a b⦄, F.Adj a b → level a % 2 ≠ level b % 2)
    (X0 X1 Y1 Z1 : Finset B)
    (hsize : Fintype.card A + 1 ≤ #X0)
    (hcross : ∀ ⦃a b⦄, F.Adj a b →
      ∀ v ∈ (if a ∈ roots then X0 else if level a % 2 = 0 then X1 else Y1 ∪ Z1),
        Fintype.card A + 1 ≤
          #{w ∈ (if b ∈ roots then X0 else if level b % 2 = 0 then X1 else Y1 ∪ Z1) |
            G.Adj v w}) :
    ∃ f : F.Copy G,
      (∀ a ∈ roots, f a ∈ X0) ∧
      (∀ a, a ∉ roots → level a % 2 = 0 → f a ∈ X1) ∧
      (∀ a, level a % 2 = 1 → f a ∈ Y1 ∪ Z1) := by
  let candidate : A → Finset B := fun a =>
    if a ∈ roots then X0 else if level a % 2 = 0 then X1 else Y1 ∪ Z1
  obtain ⟨f, hf⟩ := exists_forest_candidate_copy F G roots hforest candidate (by
    intro a ha
    simpa [candidate, ha] using hsize) (by
    intro a b hab v hv
    exact hcross hab v hv)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a ha
    simpa [candidate, ha] using hf a
  · intro a ha hlev
    simpa [candidate, ha, hlev] using hf a
  · intro a hlev
    have hnotroot : a ∉ roots := by
      intro ha
      have := hrootLevel a ha
      omega
    simpa [candidate, hnotroot, hlev] using hf a

/-- Choice-sensitive version of the Lemma 5.2 core.  The function `side` is
arbitrary, so every odd-level vertex may independently be assigned to `Y1`
or `Z1` before the local greedy embedding is run. -/
theorem lemma5_2_selected_side_candidate_core
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (roots : Finset A) (hforest : (rootedForestCone F roots).IsTree)
    (level : A → ℕ) (hrootLevel : ∀ a ∈ roots, level a = 0)
    (side : A → Fin 2) (X0 X1 Y1 Z1 : Finset B)
    (hsize : Fintype.card A + 1 ≤ #X0)
    (hcross : ∀ ⦃a b⦄, F.Adj a b →
      ∀ v ∈ (if a ∈ roots then X0 else if level a % 2 = 0 then X1
        else if side a = 0 then Y1 else Z1),
        Fintype.card A + 1 ≤
          #{w ∈ (if b ∈ roots then X0 else if level b % 2 = 0 then X1
            else if side b = 0 then Y1 else Z1) | G.Adj v w}) :
    ∃ f : F.Copy G,
      (∀ a ∈ roots, f a ∈ X0) ∧
      (∀ a, a ∉ roots → level a % 2 = 0 → f a ∈ X1) ∧
      (∀ a, level a % 2 = 1 →
        f a ∈ if side a = 0 then Y1 else Z1) := by
  let candidate : A → Finset B := fun a =>
    if a ∈ roots then X0 else if level a % 2 = 0 then X1
      else if side a = 0 then Y1 else Z1
  obtain ⟨f, hf⟩ := exists_forest_candidate_copy F G roots hforest candidate (by
    intro a ha
    simpa [candidate, ha] using hsize) (by
    intro a b hab v hv
    exact hcross hab v hv)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a ha
    simpa [candidate, ha] using hf a
  · intro a ha hlev
    simpa [candidate, ha, hlev] using hf a
  · intro a hlev
    have hnotroot : a ∉ roots := by
      intro ha
      have := hrootLevel a ha
      omega
    simpa [candidate, hnotroot, hlev] using hf a

/-- The three-layer placement core of Zhao Lemma 5.9(2).  Roots are embedded
in the root layer `A0`; level-one and specially exposed odd vertices are
embedded in `C0`; all remaining vertices are embedded in the matching layer
`M0`.  This is the exact online invariant used after Lemma 5.9's aggregate
cluster-degree hypotheses have supplied the pointwise candidate bounds. -/
theorem lemma5_9_three_layer_candidate_core
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (roots special : Finset A) (hforest : (rootedForestCone F roots).IsTree)
    (level : A → ℕ) (hrootLevel : ∀ a ∈ roots, level a = 0)
    (hspecialOdd : ∀ a ∈ special, level a % 2 = 1)
    (A0 C0 M0 : Finset B)
    (hsize : Fintype.card A + 1 ≤ #A0)
    (hcross : ∀ ⦃a b⦄, F.Adj a b →
      ∀ v ∈ (if a ∈ roots then A0 else if level a = 1 ∨ a ∈ special then C0 else M0),
        Fintype.card A + 1 ≤
          #{w ∈ (if b ∈ roots then A0 else if level b = 1 ∨ b ∈ special then C0 else M0) |
            G.Adj v w}) :
    ∃ f : F.Copy G,
      (∀ a ∈ roots, f a ∈ A0) ∧
      (∀ a, level a = 1 ∨ a ∈ special → f a ∈ C0) ∧
      (∀ a, a ∉ roots → level a ≠ 1 → a ∉ special → f a ∈ M0) := by
  let candidate : A → Finset B := fun a =>
    if a ∈ roots then A0 else if level a = 1 ∨ a ∈ special then C0 else M0
  obtain ⟨f, hf⟩ := exists_forest_candidate_copy F G roots hforest candidate (by
    intro a ha
    simpa [candidate, ha] using hsize) (by
    intro a b hab v hv
    exact hcross hab v hv)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a ha
    simpa [candidate, ha] using hf a
  · intro a ha
    have hnotroot : a ∉ roots := by
      intro haroot
      have hzero := hrootLevel a haroot
      rcases ha with hlevel | hspecial
      · omega
      · have hodd := hspecialOdd a hspecial
        omega
    simpa [candidate, hnotroot, ha] using hf a
  · intro a haroot hlevel hspecial
    have hm := hf a
    simpa [candidate, haroot, hlevel, hspecial] using hm

#print axioms Erdos547b.ZhaoLemma59.exists_rooted_candidate_copy
#print axioms Erdos547b.ZhaoLemma59.exists_forest_candidate_copy
#print axioms Erdos547b.ZhaoLemma59.exists_forest_candidate_copy_avoiding
#print axioms Erdos547b.ZhaoLemma59.lemma5_2_candidate_core
#print axioms Erdos547b.ZhaoLemma59.lemma5_2_selected_side_candidate_core
#print axioms Erdos547b.ZhaoLemma59.lemma5_9_three_layer_candidate_core

end Erdos547b.ZhaoLemma59
