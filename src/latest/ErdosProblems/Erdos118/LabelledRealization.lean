import ErdosProblems.Erdos118.LabelledFrames

/-!
Chronological realization of labelled parser frames. Bounds track decorated
words, while the ordinal embedding compares nonempty ordinary blocks.
Earlier annotations are preserved explicitly. No color conclusion is assumed.
-/

namespace Erdos118.LabelledRealization

open Ordinal Negative Negative.Exact WeakPigeon LabelledExtensions LabelledFrames PrefixOrder
open PrefixRealization (Phase decode decode_code parent_code_lt run_append run_word_terminal
  run_dead live_of_next_ne_dead live_ne_dead ne_dead_of_run live_of_proper_prefix
  lex_split head_eq_of_common_prefix below below_eq_self below_append_above)

theorem ordinary_sublist (F : Frame) : F.ordinary.Sublist F.decorated := by
  cases F with
  | initial => exact List.Sublist.refl _
  | pending P => exact P.position.ordinary_sublist
  | terminal S hS => exact S.ordinary_sublist
  | dead => exact List.Sublist.refl _

theorem decorated_pairwise (F : Frame) : F.decorated.Pairwise (· < ·) := by
  cases F with
  | initial => simp [Frame.decorated]
  | pending P => exact P.position.increasing
  | terminal S hS => exact S.increasing
  | dead => simp [Frame.decorated]

noncomputable def advance {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) : Frame :=
  Classical.choose (step_budget_exists hH F a b)

theorem advance_phase {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    (advance hH F a b).phase = F.phase.next a :=
  (Classical.choose_spec (step_budget_exists hH F a b)).1

theorem advance_spec {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ)
    (hF : F.phase.live) :
    ∃ d v : List ℕ, (advance hH F a b).decorated = F.decorated ++ d ∧
      (advance hH F a b).ordinary = F.ordinary ++ v ∧ v ≠ [] ∧ v.Sublist d ∧
      (∀ z ∈ d, z ∈ H ∧ b < z) ∧ LabelsExtend F (advance hH F a b) :=
  (Classical.choose_spec (step_budget_exists hH F a b)).2.1 hF

theorem advance_budget {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    LabelBudget F a (advance hH F a b) :=
  (Classical.choose_spec (step_budget_exists hH F a b)).2.2

def previousBound (n : ℕ) (rec : ∀ i, i < n → Frame) : ℕ :=
  Finset.univ.sup (fun i : Fin n ↦ (rec i.1 i.2).decorated.sum)

noncomputable def buildStep {H : Set ℕ} (hH : H.Infinite) (n : ℕ)
    (rec : ∀ i, i < n → Frame) : Frame :=
  if hn : decode n = [] then .initial
  else advance hH (rec (code (decode n).dropLast) (parent_code_lt n hn))
    ((decode n).getLast hn) (previousBound n rec)

noncomputable def build {H : Set ℕ} (hH : H.Infinite) : ℕ → Frame :=
  Nat.strongRec (buildStep hH)

noncomputable def frame {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) : Frame :=
  build hH (code p)

@[simp] theorem frame_nil {H : Set ℕ} (hH : H.Infinite) : frame hH [] = .initial := by
  unfold frame build
  rw [Nat.strongRec_eq]
  simp [buildStep, decode]

theorem frame_child {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ) :
    frame hH (p ++ [a]) = advance hH (frame hH p) a
      (previousBound (code (p ++ [a])) (fun i _ ↦ build hH i)) := by
  unfold frame
  rw [build, Nat.strongRec_eq]
  simp only [buildStep, decode_code, List.concat_ne_nil, ↓reduceDIte,
    List.dropLast_concat, List.getLast_concat]
  rfl

theorem frame_phase {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) :
    (frame hH p).phase = Phase.root.run p := by
  induction p using List.reverseRecOn with
  | nil => simp [Frame.phase, Phase.run]
  | append_singleton p a ih =>
    rw [frame_child, advance_phase, ih, run_append]
    rfl

theorem previousBound_ge {H : Set ℕ} (hH : H.Infinite) (p : List ℕ)
    {n : ℕ} (hp : code p < n) :
    (frame hH p).decorated.sum ≤ previousBound n (fun i _ ↦ build hH i) := by
  exact Finset.le_sup (f := fun i : Fin n ↦ (build hH i).decorated.sum)
    (Finset.mem_univ (⟨code p, hp⟩ : Fin n))

theorem frame_budget {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ) :
    LabelBudget (frame hH p) a (frame hH (p ++ [a])) := by
  rw [frame_child]
  exact advance_budget hH _ _ _

noncomputable def ordinaryBlock {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ) : List ℕ :=
  (frame hH (p ++ [a])).ordinary.drop (frame hH p).ordinary.length

noncomputable def decoratedBlock {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ) : List ℕ :=
  (frame hH (p ++ [a])).decorated.drop (frame hH p).decorated.length

structure BlockSpec {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ) : Prop where
  ordinary_eq : (frame hH (p ++ [a])).ordinary =
    (frame hH p).ordinary ++ ordinaryBlock hH p a
  decorated_eq : (frame hH (p ++ [a])).decorated =
    (frame hH p).decorated ++ decoratedBlock hH p a
  nonempty : ordinaryBlock hH p a ≠ []
  sublist : (ordinaryBlock hH p a).Sublist (decoratedBlock hH p a)
  supported : ∀ y ∈ decoratedBlock hH p a, y ∈ H
  earlier : ∀ q : List ℕ, code q < code (p ++ [a]) →
    ∀ x ∈ (frame hH q).decorated, ∀ y ∈ decoratedBlock hH p a, x < y
  labels : LabelsExtend (frame hH p) (frame hH (p ++ [a]))

theorem block_spec {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ)
    (hp : (Phase.root.run p).live) : BlockSpec hH p a := by
  have hp' : (frame hH p).phase.live := (frame_phase hH p).symm ▸ hp
  obtain ⟨d, v, hd, hv, hvne, hvd, hfresh, hlabels⟩ := advance_spec hH (frame hH p) a
    (previousBound (code (p ++ [a])) (fun i _ ↦ build hH i)) hp'
  rw [← frame_child] at hd hv hlabels
  have hdb : decoratedBlock hH p a = d := by simp [decoratedBlock, hd]
  have hvb : ordinaryBlock hH p a = v := by simp [ordinaryBlock, hv]
  refine ⟨by simpa only [hvb] using hv, by simpa only [hdb] using hd,
    hvb ▸ hvne, ?_, ?_, ?_, hlabels⟩
  · rw [hvb, hdb]
    exact hvd
  · rw [hdb]
    exact fun y hy ↦ (hfresh y hy).1
  · rw [hdb]
    intro q hq x hx y hy
    exact ((nat_le_sum_of_mem hx).trans (previousBound_ge hH q hq)).trans_lt
      (hfresh y hy).2

structure PrefixSpec {H : Set ℕ} (hH : H.Infinite) (p q : List ℕ) : Prop where
  ordinary : (frame hH p).ordinary <+: (frame hH q).ordinary
  decorated : (frame hH p).decorated <+: (frame hH q).decorated
  labels : LabelsExtend (frame hH p) (frame hH q)

theorem frame_prefix_append {H : Set ℕ} (hH : H.Infinite) (p r : List ℕ)
    (hvalid : Phase.root.run (p ++ r) ≠ .dead) : PrefixSpec hH p (p ++ r) := by
  induction r generalizing p with
  | nil =>
    simpa only [List.append_nil] using
      (show PrefixSpec hH p p from ⟨List.prefix_rfl, List.prefix_rfl, LabelsExtend.refl _⟩)
  | cons a r ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      apply ne_dead_of_run _ r
      simpa only [run_append, Phase.run] using hvalid
    have hs := block_spec hH p a (live_of_next_ne_dead _ _ hnext)
    have htail := ih (p ++ [a]) (by simpa [List.append_assoc] using hvalid)
    have hord : (frame hH p).ordinary <+: (frame hH (p ++ [a])).ordinary :=
      ⟨ordinaryBlock hH p a, hs.ordinary_eq.symm⟩
    have hdec : (frame hH p).decorated <+: (frame hH (p ++ [a])).decorated :=
      ⟨decoratedBlock hH p a, hs.decorated_eq.symm⟩
    simpa only [List.append_assoc, List.singleton_append] using
      (show PrefixSpec hH p ((p ++ [a]) ++ r) from
        ⟨hord.trans htail.ordinary, hdec.trans htail.decorated, hs.labels.trans htail.labels⟩)

theorem frame_prefix {H : Set ℕ} (hH : H.Infinite) {p q : List ℕ}
    (hpq : p <+: q) (hq : Phase.root.run q ≠ .dead) : PrefixSpec hH p q := by
  obtain ⟨r, rfl⟩ := hpq
  exact frame_prefix_append hH p r hq

theorem frame_supported {H : Set ℕ} (hH : H.Infinite) (p : List ℕ)
    (hp : Phase.root.run p ≠ .dead) : ∀ x ∈ (frame hH p).decorated, x ∈ H := by
  induction p using List.reverseRecOn with
  | nil => simp [Frame.decorated]
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead _ _ hnext
    have hs := block_spec hH p a hlive
    rw [hs.decorated_eq]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih (live_ne_dead _ hlive) x hx
    · exact hs.supported x hx

structure Completed where
  stem : Stem
  full : stem.done.length = stem.root

def Completed.vertex (S : Completed) : G := S.stem.toGood S.full

def terminalData (F : Frame) (hF : F.phase = .terminal) : Completed :=
  match F with
  | .terminal S hS => ⟨S, hS⟩
  | .initial => False.elim (Phase.noConfusion hF)
  | .pending _ => False.elim (Phase.noConfusion hF)
  | .dead => False.elim (Phase.noConfusion hF)

theorem terminalData_frame (F : Frame) (hF : F.phase = .terminal) :
    Frame.terminal (terminalData F hF).stem (terminalData F hF).full = F := by
  cases F with
  | terminal S hS => rfl
  | initial => exact False.elim (Phase.noConfusion hF)
  | pending P => exact False.elim (Phase.noConfusion hF)
  | dead => exact False.elim (Phase.noConfusion hF)

noncomputable def output {H : Set ℕ} (hH : H.Infinite) (s : G2) : Completed :=
  terminalData (frame hH (word s ++ [0]))
    ((frame_phase hH _).trans (run_word_terminal s))

theorem output_frame {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    Frame.terminal (output hH s).stem (output hH s).full = frame hH (word s ++ [0]) :=
  terminalData_frame _ _

theorem output_ordinary {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    (output hH s).stem.ordinary = (frame hH (word s ++ [0])).ordinary :=
  congrArg Frame.ordinary (output_frame hH s)

theorem output_decorated {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    (output hH s).stem.decorated = (frame hH (word s ++ [0])).decorated :=
  congrArg Frame.decorated (output_frame hH s)

noncomputable def vertex {H : Set ℕ} (hH : H.Infinite) (s : G2) : G := (output hH s).vertex

theorem vertex_word {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    word (vertex hH s).1 = (frame hH (word s ++ [0])).ordinary :=
  ((output hH s).stem.toGood_word (output hH s).full).trans (output_ordinary hH s)

theorem output_supported {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    ∀ x ∈ (output hH s).stem.decorated, x ∈ H := by
  rw [output_decorated]
  exact frame_supported hH _ (by simp [run_word_terminal])

theorem vertex_supported {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    vertex hH s ∈ CoordinateModel.Supported H := by
  intro x hx
  rw [vertex_word] at hx
  exact frame_supported hH _ (by simp [run_word_terminal]) x ((ordinary_sublist _).subset hx)

theorem vertex_mono {H : Set ℕ} (hH : H.Infinite) {s t : G2} (hst : G2LT s t) :
    G2LT (vertex hH s).1 (vertex hH t).1 := by
  have hnpre : ¬ word s <+: word t := by
    intro hp
    have he := WordResponses.word_prefix_rigid hp
    subst t
    exact irrefl _ hst
  obtain ⟨p, a, b, u, v, hs, ht, hab⟩ := lex_split (word_lex_mono hst) hnpre
  have hp_live : (Phase.root.run p).live := by
    have hvalid : Phase.root.run (p ++ (a :: (u ++ [0]))) ≠ .dead := by
      have he := run_word_terminal s
      rw [hs, List.append_assoc, List.cons_append] at he
      rw [he]
      decide
    exact live_of_next_ne_dead _ a (ne_dead_of_run _ (u ++ [0])
      (by simpa only [run_append, Phase.run] using hvalid))
  have ha := block_spec hH p a hp_live
  have hb := block_spec hH p b hp_live
  have hpa : p ++ [a] <+: word s ++ [0] := by
    exact ⟨u ++ [0], by simp [hs, List.append_assoc]⟩
  have hpb : p ++ [b] <+: word t ++ [0] := by
    exact ⟨v ++ [0], by simp [ht, List.append_assoc]⟩
  obtain ⟨ua, hua⟩ := (frame_prefix hH hpa (by simp [run_word_terminal])).ordinary
  obtain ⟨ub, hub⟩ := (frame_prefix hH hpb (by simp [run_word_terminal])).ordinary
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil ha.nonempty
  obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hb.nonempty
  have hxy : x < y := by
    apply hb.earlier (p ++ [a]) (code_siblings p hab) x
    · rw [ha.decorated_eq]
      apply List.mem_append_right _
      apply ha.sublist.subset
      rw [hx]
      exact List.mem_cons_self ..
    · apply hb.sublist.subset
      rw [hy]
      exact List.mem_cons_self ..
  apply word_lex_iff.mp
  rw [vertex_word, vertex_word, ← hua, ← hub, ha.ordinary_eq, hb.ordinary_eq, hx, hy]
  simp only [List.append_assoc, List.cons_append]
  exact List.Lex.append_left _ (List.Lex.rel hxy) (frame hH p).ordinary

noncomputable def embedding {H : Set ℕ} (hH : H.Infinite) :
    G2LT ↪r ((· < ·) : G → G → Prop) :=
  RelEmbedding.ofMonotone (vertex hH) (fun _ _ h ↦ vertex_mono hH h)

theorem vertex_range_type {H : Set ℕ} (hH : H.Infinite) :
    typeLT (Set.range (vertex hH)) = lambda := by
  apply le_antisymm
  · exact (Ordinal.type_set_le _).trans_eq (type_G.trans lambda_eq_natural_inner_power.symm)
  · rw [lambda_eq_natural_inner_power, ← g2_type]
    exact (RelEmbedding.ofMonotone
      (r := G2LT)
      (s := ((· < ·) : Set.range (vertex hH) → Set.range (vertex hH) → Prop))
      (fun s ↦ ⟨vertex hH s, s, rfl⟩) (fun _ _ h ↦ vertex_mono hH h)).ordinal_type_le

theorem decorated_coordinate_block {H : Set ℕ} (hH : H.Infinite) (p : List ℕ)
    (hp : Phase.root.run p ≠ .dead) {x : ℕ} (hx : x ∈ (frame hH p).decorated) :
    ∃ q : List ℕ, ∃ a : ℕ, q ++ [a] <+: p ∧
      (Phase.root.run q).live ∧ x ∈ decoratedBlock hH q a := by
  induction p using List.reverseRecOn with
  | nil => simp [Frame.decorated] at hx
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead _ _ hnext
    have hs := block_spec hH p a hlive
    rw [hs.decorated_eq] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨q, b, hq, hqLive, hxb⟩ := ih (live_ne_dead _ hlive) hx
      exact ⟨q, b, hq.trans (List.prefix_append p [a]), hqLive, hxb⟩
    · exact ⟨p, a, List.prefix_rfl, hlive, hx⟩

theorem blocks_ordered {H : Set ℕ} (hH : H.Infinite) (p q : List ℕ) (a b : ℕ)
    (hp : (Phase.root.run p).live) (hq : (Phase.root.run q).live)
    (hcode : code (p ++ [a]) < code (q ++ [b])) :
    ∀ x ∈ decoratedBlock hH p a, ∀ y ∈ decoratedBlock hH q b, x < y := by
  intro x hx y hy
  apply (block_spec hH q b hq).earlier (p ++ [a]) hcode x _ y hy
  rw [(block_spec hH p a hp).decorated_eq]
  exact List.mem_append_right _ hx

theorem block_separated_from_coordinate {H : Set ℕ} (hH : H.Infinite)
    (p q : List ℕ) (hheads : p.head? ≠ q.head?)
    (hq : Phase.root.run q ≠ .dead) {y : ℕ} (hy : y ∈ (frame hH q).decorated)
    (r : List ℕ) (a : ℕ) (hrp : r ++ [a] <+: p)
    (hr : (Phase.root.run r).live) :
    (∀ x ∈ decoratedBlock hH r a, x < y) ∨
      (∀ x ∈ decoratedBlock hH r a, y < x) := by
  obtain ⟨s, b, hsq, hs, hyb⟩ := decorated_coordinate_block hH q hq hy
  rcases lt_trichotomy (code (r ++ [a])) (code (s ++ [b])) with hc | hc | hc
  · exact Or.inl (fun x hx ↦ blocks_ordered hH r s a b hr hs hc x hx y hyb)
  · have he := code_injective hc
    exact (hheads (head_eq_of_common_prefix (List.concat_ne_nil a r) hrp
      (he ▸ hsq))).elim
  · exact Or.inr (fun x hx ↦ blocks_ordered hH s r b a hs hr hc y hyb x hx)

theorem below_frame_prefix_joint {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (y : ℕ)
    (hp : Phase.root.run p ≠ .dead)
    (hblocks : ∀ r : List ℕ, ∀ a : ℕ, r ++ [a] <+: p →
      (Phase.root.run r).live →
      (∀ x ∈ decoratedBlock hH r a, x < y) ∨
        (∀ x ∈ decoratedBlock hH r a, y < x)) :
    ∃ q : List ℕ, q <+: p ∧
      (frame hH q).ordinary = below y (frame hH p).ordinary ∧
      (frame hH q).decorated = below y (frame hH p).decorated := by
  induction p using List.reverseRecOn with
  | nil => exact ⟨[], List.prefix_rfl, by simp [Frame.ordinary, below],
      by simp [Frame.decorated, below]⟩
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead _ _ hnext
    have hs := block_spec hH p a hlive
    rcases hblocks p a List.prefix_rfl hlive with hlow | hhigh
    · have halld : ∀ x ∈ (frame hH (p ++ [a])).decorated, x < y := by
        obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hs.nonempty
        have hzb : z ∈ decoratedBlock hH p a := by
          apply hs.sublist.subset
          rw [hz]
          exact List.mem_cons_self ..
        intro x hx
        rw [hs.decorated_eq] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hs.earlier p (code_lt_child p a) x hx z hzb).trans (hlow z hzb)
        · exact hlow x hx
      have hallo : ∀ x ∈ (frame hH (p ++ [a])).ordinary, x < y :=
        fun x hx ↦ halld x ((ordinary_sublist _).subset hx)
      exact ⟨p ++ [a], List.prefix_rfl, (below_eq_self y _ hallo).symm,
        (below_eq_self y _ halld).symm⟩
    · obtain ⟨q, hqp, hqo, hqd⟩ := ih (live_ne_dead _ hlive)
        (fun r b hr hb ↦ hblocks r b (hr.trans (List.prefix_append p [a])) hb)
      refine ⟨q, hqp.trans (List.prefix_append p [a]), ?_, ?_⟩
      · rw [hs.ordinary_eq, below_append_above y _ _
          (fun x hx ↦ hhigh x (hs.sublist.subset hx))]
        exact hqo
      · rw [hs.decorated_eq, below_append_above y _ _ hhigh]
        exact hqd

/-- Both cuts are the same labelled pending frame, and its annotations persist
into the completed output. The threshold may be a node or a label coordinate. -/
theorem output_joint_cut {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : s.length ≠ t.length) {y : ℕ} (hy : y ∈ (output hH t).stem.decorated)
    (hnil : below y (output hH s).stem.ordinary ≠ [])
    (hproper : below y (output hH s).stem.ordinary ≠ (output hH s).stem.ordinary) :
    ∃ P : Pending,
      P.position.ordinary = below y (output hH s).stem.ordinary ∧
      P.position.decorated = below y (output hH s).stem.decorated ∧
      LabelsExtend (.pending P) (.terminal (output hH s).stem (output hH s).full) := by
  let p := word s ++ [0]
  let q := word t ++ [0]
  have hp : Phase.root.run p ≠ .dead := by simp [p, run_word_terminal]
  have hq : Phase.root.run q ≠ .dead := by simp [q, run_word_terminal]
  have hheads : p.head? ≠ q.head? := by simpa [p, q, word] using hroots
  have hy' : y ∈ (frame hH q).decorated := by simpa [q, output_decorated] using hy
  obtain ⟨r, hrp, hro, hrd⟩ := below_frame_prefix_joint hH p y hp
    (fun r a hra hrLive ↦ block_separated_from_coordinate hH p q hheads hq hy'
      r a hra hrLive)
  have hrne : r ≠ p := by
    intro he
    subst r
    apply hproper
    rw [output_ordinary]
    exact hro.symm
  have hlive : (frame hH r).phase.live :=
    (frame_phase hH r).symm ▸ live_of_proper_prefix hrp hrne hp
  have hro' : (frame hH r).ordinary = below y (output hH s).stem.ordinary := by
    rw [output_ordinary]
    exact hro
  have hrd' : (frame hH r).decorated = below y (output hH s).stem.decorated := by
    rw [output_decorated]
    exact hrd
  have hlabels := (frame_prefix hH hrp hp).labels
  change LabelsExtend (frame hH r) (frame hH (word s ++ [0])) at hlabels
  rw [← output_frame] at hlabels
  cases he : frame hH r with
  | initial => exact (hnil (hro'.symm.trans (by rw [he]; rfl))).elim
  | pending P =>
    exact ⟨P, by simpa only [he, Frame.ordinary] using hro',
      by simpa only [he, Frame.decorated] using hrd', by simpa only [he] using hlabels⟩
  | terminal S hS => rw [he] at hlive; exact hlive.elim
  | dead => rw [he] at hlive; exact hlive.elim

theorem vertex_root_eq_of_length_eq {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hst : s.length = t.length) : (vertex hH s).1.length = (vertex hH t).1.length := by
  have hs : [s.length] <+: word s ++ [0] :=
    ⟨s.flatMap levelWord ++ [0], rfl⟩
  have ht : [s.length] <+: word t ++ [0] :=
    ⟨t.flatMap levelWord ++ [0], by simp [word, hst]⟩
  have hps := (frame_prefix hH hs (by simp [run_word_terminal])).ordinary
  have hpt := (frame_prefix hH ht (by simp [run_word_terminal])).ordinary
  have hnonempty : (frame hH [s.length]).ordinary ≠ [] := by
    have hspec := block_spec hH [] s.length (by trivial)
    have hw : (frame hH [s.length]).ordinary = ordinaryBlock hH [] s.length := by
      simpa only [List.nil_append, frame_nil, Frame.ordinary] using hspec.ordinary_eq
    rw [hw]
    exact hspec.nonempty
  have hheads := head_eq_of_common_prefix hnonempty hps hpt
  rw [← vertex_word, ← vertex_word] at hheads
  simpa only [word, List.head?_cons, Option.some.injEq] using hheads

theorem output_decorated_disjoint {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : s.length ≠ t.length) :
    Disjoint (output hH s).stem.decorated.toFinset (output hH t).stem.decorated.toFinset := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  have hs : x ∈ (frame hH (word s ++ [0])).decorated := by
    rw [← output_decorated]
    exact List.mem_toFinset.mp hxs
  have ht : x ∈ (frame hH (word t ++ [0])).decorated := by
    rw [← output_decorated]
    exact List.mem_toFinset.mp hxt
  obtain ⟨p, a, hps, hp, hxp⟩ := decorated_coordinate_block hH _
    (by simp [run_word_terminal]) hs
  have hheads : (word s ++ [0]).head? ≠ (word t ++ [0]).head? := by
    simpa [word] using hroots
  rcases block_separated_from_coordinate hH _ _ hheads
      (by simp [run_word_terminal]) ht p a hps hp with h | h
  · exact (Nat.lt_irrefl x) (h x hxp)
  · exact (Nat.lt_irrefl x) (h x hxp)

theorem output_properties_of_roots_ne {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : (vertex hH s).1.length ≠ (vertex hH t).1.length) :
    Disjoint (output hH s).stem.decorated.toFinset (output hH t).stem.decorated.toFinset ∧
      ∀ y ∈ (output hH t).stem.decorated,
        below y (output hH s).stem.ordinary ≠ [] →
        below y (output hH s).stem.ordinary ≠ (output hH s).stem.ordinary →
        ∃ P : Pending,
          P.position.ordinary = below y (output hH s).stem.ordinary ∧
          P.position.decorated = below y (output hH s).stem.decorated ∧
          LabelsExtend (.pending P) (.terminal (output hH s).stem (output hH s).full) := by
  have hst : s.length ≠ t.length :=
    fun he ↦ hroots (vertex_root_eq_of_length_eq hH s t he)
  exact ⟨output_decorated_disjoint hH s t hst,
    fun _ hy hnil hproper ↦ output_joint_cut hH s t hst hy hnil hproper⟩

end Erdos118.LabelledRealization
