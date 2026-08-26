import ErdosProblems.Erdos118.InteriorWords
import ErdosProblems.Erdos118.PrefixOrder

/-!
Parsing raw nested lists and realizing their prefixes by fresh blocks ending
at interior leaves. This construction has no coloring or node labels.
-/

namespace Erdos118.PrefixRealization

open Ordinal Negative Negative.Exact WeakPigeon InteriorWords PrefixOrder

inductive Phase
  | root
  | pending (bodies leaves : ℕ)
  | terminal
  | dead
  deriving DecidableEq

def Phase.next : Phase → ℕ → Phase
  | .root, a => .pending a 0
  | .pending r (n + 1), _ => .pending r n
  | .pending 0 0, _ => .terminal
  | .pending (r + 1) 0, a => .pending r a
  | .terminal, _ => .dead
  | .dead, _ => .dead

def Phase.live : Phase → Prop
  | .root | .pending _ _ => True
  | .terminal | .dead => False

def Phase.run (q : Phase) : List ℕ → Phase
  | [] => q
  | a :: p => (q.next a).run p

theorem run_append (q : Phase) (p s : List ℕ) :
    q.run (p ++ s) = (q.run p).run s := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih => exact ih (q.next a)

theorem run_entries (r : ℕ) (a : List ℕ) :
    (Phase.pending r a.length).run a = .pending r 0 := by
  induction a with
  | nil => rfl
  | cons x a ih => exact ih

theorem run_bodies (r : ℕ) (s : G2) :
    (Phase.pending (r + s.length) 0).run (s.flatMap levelWord) = .pending r 0 := by
  induction s with
  | nil => simp [Phase.run]
  | cons a s ih =>
    simp only [List.length_cons, List.flatMap_cons, levelWord,
      List.cons_append, Phase.run, Phase.next]
    rw [run_append, run_entries]
    exact ih

theorem run_word (s : G2) : Phase.root.run (word s) = .pending 0 0 := by
  simpa [word, Phase.run, Phase.next] using run_bodies 0 s

theorem run_word_terminal (s : G2) :
    Phase.root.run (word s ++ [0]) = .terminal := by
  rw [run_append, run_word]
  rfl

theorem run_dead (p : List ℕ) : Phase.dead.run p = .dead := by
  induction p with
  | nil => rfl
  | cons a p ih => exact ih

inductive Frame
  | initial
  | pending (r n : ℕ) (P : Position)
      (bodies : P.done.length + r + 1 < P.root)
      (leaves : P.entries.length + n < P.size)
  | terminal (x : G)
  | dead

def Frame.phase : Frame → Phase
  | .initial => .root
  | .pending r n _ _ _ => .pending r n
  | .terminal _ => .terminal
  | .dead => .dead

def Frame.word : Frame → List ℕ
  | .initial | .dead => []
  | .pending _ _ P _ _ => P.word
  | .terminal x => Negative.Exact.word x.1

theorem step_exists {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    ∃ F' : Frame, F'.phase = F.phase.next a ∧
      (F.phase.live → ∃ v : List ℕ, F'.word = F.word ++ v ∧ v ≠ [] ∧
        ∀ z ∈ v, z ∈ H ∧ b < z) := by
  cases F with
  | initial =>
    obtain ⟨P, hroot, hdone, _, _, hfresh⟩ := start hH b a 0
    have hb : P.done.length + a + 1 < P.root := by simpa [hdone] using hroot
    refine ⟨.pending a 0 P hb (by simpa using P.unfinished), rfl, ?_⟩
    intro _
    exact ⟨P.word, rfl, by simp [Position.word, PartialWordResponses.partialWord], hfresh⟩
  | pending r n P hb hl =>
    cases n with
    | succ n =>
      have hnext : P.entries.length + 1 < P.size := by omega
      obtain ⟨Q, v, hroot, hdone, hsize, hlen, hw, hv, hfresh⟩ :=
        advance_leaf P hH b (P.entries.length + 1) (by omega) hnext
      have hb' : Q.done.length + r + 1 < Q.root := by rwa [hdone, hroot]
      have hl' : Q.entries.length + n < Q.size := by rw [hlen, hsize]; omega
      exact ⟨.pending r n Q hb' hl', rfl, fun _ ↦ ⟨v, hw, hv, hfresh⟩⟩
    | zero =>
      cases r with
      | zero =>
        obtain ⟨x, v, _, hw, hv, hfresh⟩ := complete P hH b
        exact ⟨.terminal x, rfl, fun _ ↦ ⟨v, hw, hv, hfresh⟩⟩
      | succ r =>
        have hj : P.done.length + 1 + 1 < P.root := by omega
        obtain ⟨Q, v, hroot, hdone, hlen, hsize, hw, hv, hfresh⟩ :=
          advance_body P hH b (P.done.length + 1) a (by omega) hj
        have hb' : Q.done.length + r + 1 < Q.root := by rw [hdone, hroot]; omega
        have hl' : Q.entries.length + a < Q.size := by rw [hlen]; omega
        exact ⟨.pending r a Q hb' hl', rfl, fun _ ↦ ⟨v, hw, hv, hfresh⟩⟩
  | terminal x => exact ⟨.dead, rfl, fun h ↦ h.elim⟩
  | dead => exact ⟨.dead, rfl, fun h ↦ h.elim⟩

noncomputable def advance {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) : Frame :=
  Classical.choose (step_exists hH F a b)

theorem advance_phase {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    (advance hH F a b).phase = F.phase.next a :=
  (Classical.choose_spec (step_exists hH F a b)).1

theorem advance_word {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ)
    (hF : F.phase.live) :
    ∃ v : List ℕ, (advance hH F a b).word = F.word ++ v ∧ v ≠ [] ∧
      ∀ z ∈ v, z ∈ H ∧ b < z :=
  (Classical.choose_spec (step_exists hH F a b)).2 hF

def decode (n : ℕ) : List ℕ := (Denumerable.ofNat (List ℕ) n).reverse

@[simp] theorem decode_code (p : List ℕ) : decode (code p) = p := by
  simp [decode, code]

@[simp] theorem code_decode (n : ℕ) : code (decode n) = n := by
  simp [decode, code]

theorem parent_code_lt (n : ℕ) (hn : decode n ≠ []) :
    code (decode n).dropLast < n := by
  have h := code_lt_child (decode n).dropLast ((decode n).getLast hn)
  rwa [List.dropLast_concat_getLast, code_decode] at h

def previousBound (n : ℕ) (rec : ∀ i, i < n → Frame) : ℕ :=
  Finset.univ.sup (fun i : Fin n ↦ (rec i.1 i.2).word.sum)

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
    (frame hH p).word.sum ≤ previousBound n (fun i _ ↦ build hH i) := by
  exact Finset.le_sup (f := fun i : Fin n ↦ (build hH i).word.sum)
    (Finset.mem_univ (⟨code p, hp⟩ : Fin n))

noncomputable def block {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ) : List ℕ :=
  (frame hH (p ++ [a])).word.drop (frame hH p).word.length

theorem block_spec {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (a : ℕ)
    (hp : (Phase.root.run p).live) :
    (frame hH (p ++ [a])).word = (frame hH p).word ++ block hH p a ∧
      block hH p a ≠ [] ∧ (∀ y ∈ block hH p a, y ∈ H) ∧
      ∀ q : List ℕ, code q < code (p ++ [a]) →
        ∀ x ∈ (frame hH q).word, ∀ y ∈ block hH p a, x < y := by
  have hp' : (frame hH p).phase.live := (frame_phase hH p).symm ▸ hp
  obtain ⟨v, hv, hvne, hfresh⟩ := advance_word hH (frame hH p) a
    (previousBound (code (p ++ [a])) (fun i _ ↦ build hH i)) hp'
  rw [← frame_child] at hv
  have hblock : block hH p a = v := by simp [block, hv]
  rw [hblock]
  refine ⟨hv, hvne, fun y hy ↦ (hfresh y hy).1, ?_⟩
  intro q hq x hx y hy
  exact ((nat_le_sum_of_mem hx).trans (previousBound_ge hH q hq)).trans_lt
    (hfresh y hy).2

theorem live_of_next_ne_dead (q : Phase) (a : ℕ) (h : q.next a ≠ .dead) : q.live := by
  cases q with
  | root => trivial
  | pending r n => trivial
  | terminal => exact (h rfl).elim
  | dead => exact (h rfl).elim

theorem live_ne_dead (q : Phase) (h : q.live) : q ≠ .dead := by
  cases q <;> simp_all [Phase.live]

theorem ne_dead_of_run (q : Phase) (p : List ℕ) (h : q.run p ≠ .dead) : q ≠ .dead := by
  intro he
  subst q
  exact h (run_dead p)

theorem frame_prefix_append {H : Set ℕ} (hH : H.Infinite) (p r : List ℕ)
    (hvalid : Phase.root.run (p ++ r) ≠ .dead) :
    (frame hH p).word <+: (frame hH (p ++ r)).word := by
  induction r generalizing p with
  | nil => simp
  | cons a r ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      apply ne_dead_of_run _ r
      simpa only [run_append, Phase.run] using hvalid
    have hlive := live_of_next_ne_dead (Phase.root.run p) a hnext
    have hfirst : (frame hH p).word <+: (frame hH (p ++ [a])).word :=
      ⟨block hH p a, (block_spec hH p a hlive).1.symm⟩
    have htail := ih (p ++ [a]) (by simpa [List.append_assoc] using hvalid)
    simpa only [List.append_assoc, List.singleton_append] using hfirst.trans htail

theorem frame_prefix {H : Set ℕ} (hH : H.Infinite) {p q : List ℕ}
    (hpq : p <+: q) (hq : Phase.root.run q ≠ .dead) :
    (frame hH p).word <+: (frame hH q).word := by
  obtain ⟨r, rfl⟩ := hpq
  exact frame_prefix_append hH p r hq

theorem frame_supported {H : Set ℕ} (hH : H.Infinite) (p : List ℕ)
    (hp : Phase.root.run p ≠ .dead) : ∀ x ∈ (frame hH p).word, x ∈ H := by
  induction p using List.reverseRecOn with
  | nil => simp [Frame.word]
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead (Phase.root.run p) a hnext
    have hs := block_spec hH p a hlive
    rw [hs.1]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih (live_ne_dead _ hlive) x hx
    · exact hs.2.2.1 x hx

def terminalValue (F : Frame) (hF : F.phase = .terminal) : G :=
  match F with
  | .terminal x => x
  | .initial => False.elim (Phase.noConfusion hF)
  | .pending _ _ _ _ _ => False.elim (Phase.noConfusion hF)
  | .dead => False.elim (Phase.noConfusion hF)

theorem terminalValue_word (F : Frame) (hF : F.phase = .terminal) :
    word (terminalValue F hF).1 = F.word := by
  cases F with
  | terminal x => rfl
  | initial => exact False.elim (Phase.noConfusion hF)
  | pending r n P hb hl => exact False.elim (Phase.noConfusion hF)
  | dead => exact False.elim (Phase.noConfusion hF)

noncomputable def output {H : Set ℕ} (hH : H.Infinite) (s : G2) : G :=
  terminalValue (frame hH (word s ++ [0]))
    ((frame_phase hH _).trans (run_word_terminal s))

theorem output_word {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    word (output hH s).1 = (frame hH (word s ++ [0])).word :=
  terminalValue_word _ _

theorem output_supported {H : Set ℕ} (hH : H.Infinite) (s : G2) :
    output hH s ∈ CoordinateModel.Supported H := by
  intro x hx
  rw [output_word] at hx
  exact frame_supported hH _ (by simp [run_word_terminal]) x hx

theorem lex_split {p q : List ℕ} (h : List.Lex (· < ·) p q) (hpq : ¬ p <+: q) :
    ∃ r : List ℕ, ∃ a b : ℕ, ∃ s t : List ℕ,
      p = r ++ a :: s ∧ q = r ++ b :: t ∧ a < b := by
  induction h with
  | nil => exact (hpq (by simp)).elim
  | @rel a s b t hab => exact ⟨[], a, b, s, t, rfl, rfl, hab⟩
  | @cons a p q h ih =>
    have hpq' : ¬ p <+: q := by
      rintro ⟨r, hr⟩
      exact hpq ⟨r, congrArg (List.cons a) hr⟩
    obtain ⟨r, b, c, s, t, hp, hq, hbc⟩ := ih hpq'
    exact ⟨a :: r, b, c, s, t, by simp [hp], by simp [hq], hbc⟩

theorem output_mono {H : Set ℕ} (hH : H.Infinite) {s t : G2} (hst : G2LT s t) :
    G2LT (output hH s).1 (output hH t).1 := by
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
    refine ⟨u ++ [0], ?_⟩
    simp [hs, List.append_assoc]
  have hpb : p ++ [b] <+: word t ++ [0] := by
    refine ⟨v ++ [0], ?_⟩
    simp [ht, List.append_assoc]
  obtain ⟨ua, hua⟩ := frame_prefix hH hpa (by simp [run_word_terminal])
  obtain ⟨ub, hub⟩ := frame_prefix hH hpb (by simp [run_word_terminal])
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil ha.2.1
  obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hb.2.1
  have hxy : x < y := by
    apply hb.2.2.2 (p ++ [a]) (code_siblings p hab) x
    · rw [ha.1, hx]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    · rw [hy]
      exact List.mem_cons_self ..
  apply word_lex_iff.mp
  rw [output_word, output_word, ← hua, ← hub, ha.1, hb.1, hx, hy]
  simp only [List.append_assoc, List.cons_append]
  exact List.Lex.append_left _ (List.Lex.rel hxy) (frame hH p).word

noncomputable def embedding {H : Set ℕ} (hH : H.Infinite) :
    G2LT ↪r ((· < ·) : G → G → Prop) :=
  RelEmbedding.ofMonotone (output hH) (fun _ _ h ↦ output_mono hH h)

theorem output_range_type {H : Set ℕ} (hH : H.Infinite) :
    typeLT (Set.range (output hH)) = lambda := by
  apply le_antisymm
  · exact (Ordinal.type_set_le _).trans_eq (type_G.trans lambda_eq_natural_inner_power.symm)
  · rw [lambda_eq_natural_inner_power, ← g2_type]
    exact (RelEmbedding.ofMonotone
      (r := G2LT)
      (s := ((· < ·) : Set.range (output hH) → Set.range (output hH) → Prop))
      (fun s ↦ ⟨output hH s, s, rfl⟩) (fun _ _ h ↦ output_mono hH h)).ordinal_type_le

theorem coordinate_block {H : Set ℕ} (hH : H.Infinite) (p : List ℕ)
    (hp : Phase.root.run p ≠ .dead) {x : ℕ} (hx : x ∈ (frame hH p).word) :
    ∃ q : List ℕ, ∃ a : ℕ, q ++ [a] <+: p ∧
      (Phase.root.run q).live ∧ x ∈ block hH q a := by
  induction p using List.reverseRecOn with
  | nil => simp [Frame.word] at hx
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead (Phase.root.run p) a hnext
    have hs := block_spec hH p a hlive
    rw [hs.1] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨q, b, hq, hqLive, hxb⟩ := ih (live_ne_dead _ hlive) hx
      exact ⟨q, b, hq.trans (List.prefix_append p [a]), hqLive, hxb⟩
    · exact ⟨p, a, List.prefix_rfl, hlive, hx⟩

theorem blocks_ordered {H : Set ℕ} (hH : H.Infinite) (p q : List ℕ) (a b : ℕ)
    (hp : (Phase.root.run p).live) (hq : (Phase.root.run q).live)
    (hcode : code (p ++ [a]) < code (q ++ [b])) :
    ∀ x ∈ block hH p a, ∀ y ∈ block hH q b, x < y := by
  intro x hx y hy
  apply (block_spec hH q b hq).2.2.2 (p ++ [a]) hcode x _ y hy
  rw [(block_spec hH p a hp).1]
  exact List.mem_append_right _ hx

theorem head_eq_of_common_prefix {p q r : List ℕ} (hr : r ≠ [])
    (hrp : r <+: p) (hrq : r <+: q) : p.head? = q.head? := by
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  obtain ⟨u, rfl⟩ := hrp
  obtain ⟨v, rfl⟩ := hrq
  rfl

theorem block_separated_from_coordinate {H : Set ℕ} (hH : H.Infinite)
    (p q : List ℕ) (hheads : p.head? ≠ q.head?)
    (hq : Phase.root.run q ≠ .dead) {y : ℕ} (hy : y ∈ (frame hH q).word)
    (r : List ℕ) (a : ℕ) (hrp : r ++ [a] <+: p)
    (hr : (Phase.root.run r).live) :
    (∀ x ∈ block hH r a, x < y) ∨ (∀ x ∈ block hH r a, y < x) := by
  obtain ⟨s, b, hsq, hs, hyb⟩ := coordinate_block hH q hq hy
  rcases lt_trichotomy (code (r ++ [a])) (code (s ++ [b])) with hc | hc | hc
  · exact Or.inl (fun x hx ↦ blocks_ordered hH r s a b hr hs hc x hx y hyb)
  · have he := code_injective hc
    exact (hheads (head_eq_of_common_prefix (List.concat_ne_nil a r) hrp
      (he ▸ hsq))).elim
  · exact Or.inr (fun x hx ↦ blocks_ordered hH s r b a hs hr hc y hyb x hx)

def below (y : ℕ) (p : List ℕ) : List ℕ := p.takeWhile (fun x ↦ decide (x < y))

theorem below_eq_self (y : ℕ) (p : List ℕ) (hp : ∀ x ∈ p, x < y) : below y p = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : a < y := hp a (List.mem_cons_self ..)
    have htail : ∀ x ∈ p, x < y := fun x hx ↦ hp x (List.mem_cons_of_mem _ hx)
    simpa [below, List.takeWhile_cons, ha] using congrArg (List.cons a) (ih htail)

theorem below_append_above (y : ℕ) (p q : List ℕ) (hq : ∀ x ∈ q, y < x) :
    below y (p ++ q) = below y p := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | cons a q =>
      have ha : ¬ a < y := (hq a (List.mem_cons_self ..)).asymm
      simp [below, ha]
  | cons a p ih =>
    by_cases ha : a < y
    · simpa [below, List.takeWhile_cons, ha] using congrArg (List.cons a) ih
    · simp [below, ha]

theorem below_frame_prefix {H : Set ℕ} (hH : H.Infinite) (p : List ℕ) (y : ℕ)
    (hp : Phase.root.run p ≠ .dead)
    (hblocks : ∀ r : List ℕ, ∀ a : ℕ, r ++ [a] <+: p →
      (Phase.root.run r).live →
      (∀ x ∈ block hH r a, x < y) ∨ (∀ x ∈ block hH r a, y < x)) :
    ∃ q : List ℕ, q <+: p ∧ (frame hH q).word = below y (frame hH p).word := by
  induction p using List.reverseRecOn with
  | nil => exact ⟨[], List.prefix_rfl, by simp [Frame.word, below]⟩
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead (Phase.root.run p) a hnext
    have hs := block_spec hH p a hlive
    rcases hblocks p a List.prefix_rfl hlive with hlow | hhigh
    · have hall : ∀ x ∈ (frame hH (p ++ [a])).word, x < y := by
        obtain ⟨z, zs, hz⟩ := List.exists_cons_of_ne_nil hs.2.1
        have hzb : z ∈ block hH p a := by rw [hz]; exact List.mem_cons_self ..
        intro x hx
        rw [hs.1] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact (hs.2.2.2 p (code_lt_child p a) x hx z hzb).trans (hlow z hzb)
        · exact hlow x hx
      exact ⟨p ++ [a], List.prefix_rfl, (below_eq_self y _ hall).symm⟩
    · obtain ⟨q, hqp, hq⟩ := ih (live_ne_dead _ hlive)
        (fun r b hr hb ↦ hblocks r b (hr.trans (List.prefix_append p [a])) hb)
      refine ⟨q, hqp.trans (List.prefix_append p [a]), ?_⟩
      rw [hs.1, below_append_above y _ _ hhigh]
      exact hq

theorem live_of_proper_prefix {p q : List ℕ} (hpq : p <+: q) (hne : p ≠ q)
    (hq : Phase.root.run q ≠ .dead) : (Phase.root.run p).live := by
  obtain ⟨r, rfl⟩ := hpq
  have hr : r ≠ [] := by intro he; simp [he] at hne
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  apply live_of_next_ne_dead _ a
  apply ne_dead_of_run _ r
  simpa only [run_append, Phase.run] using hq

/-- A nontrivial threshold cut made by a different-root output is an actual
interior position. This statement has no graph-color hypothesis. -/
theorem output_interior_cut {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : s.length ≠ t.length) {y : ℕ} (hy : y ∈ word (output hH t).1)
    (hnil : below y (word (output hH s).1) ≠ [])
    (hproper : below y (word (output hH s).1) ≠ word (output hH s).1) :
    ∃ P : Position, P.word = below y (word (output hH s).1) := by
  let p := word s ++ [0]
  let q := word t ++ [0]
  have hp : Phase.root.run p ≠ .dead := by simp [p, run_word_terminal]
  have hq : Phase.root.run q ≠ .dead := by simp [q, run_word_terminal]
  have hheads : p.head? ≠ q.head? := by simpa [p, q, word] using hroots
  have hy' : y ∈ (frame hH q).word := by simpa [q, output_word] using hy
  obtain ⟨r, hrp, hr⟩ := below_frame_prefix hH p y hp
    (fun r a hra hrLive ↦ block_separated_from_coordinate hH p q hheads hq hy'
      r a hra hrLive)
  have hrne : r ≠ p := by
    intro he
    subst r
    apply hproper
    rw [output_word]
    exact hr.symm
  have hlive : (frame hH r).phase.live :=
    (frame_phase hH r).symm ▸ live_of_proper_prefix hrp hrne hp
  have hrword : (frame hH r).word = below y (word (output hH s).1) := by
    rw [output_word]
    exact hr
  cases he : frame hH r with
  | initial => exact (hnil (hrword.symm.trans (by rw [he]; rfl))).elim
  | pending i j P hb hl => exact ⟨P, by simpa only [he, Frame.word] using hrword⟩
  | terminal x => rw [he] at hlive; exact hlive.elim
  | dead => rw [he] at hlive; exact hlive.elim

theorem output_root_eq_of_length_eq {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hst : s.length = t.length) : (output hH s).1.length = (output hH t).1.length := by
  have hs : [s.length] <+: word s ++ [0] := by
    exact ⟨s.flatMap levelWord ++ [0], rfl⟩
  have ht : [s.length] <+: word t ++ [0] := by
    exact ⟨t.flatMap levelWord ++ [0], by simp [word, hst]⟩
  have hps := frame_prefix hH hs (by simp [run_word_terminal])
  have hpt := frame_prefix hH ht (by simp [run_word_terminal])
  have hnonempty : (frame hH [s.length]).word ≠ [] := by
    have hspec := block_spec hH [] s.length (by trivial)
    have hw : (frame hH [s.length]).word = block hH [] s.length := by
      simpa only [List.nil_append, frame_nil, Frame.word] using hspec.1
    rw [hw]
    exact hspec.2.1
  have hheads := head_eq_of_common_prefix hnonempty hps hpt
  rw [← output_word, ← output_word] at hheads
  simpa only [word, List.head?_cons, Option.some.injEq] using hheads

theorem output_support_disjoint {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (hroots : s.length ≠ t.length) :
    Disjoint (WordResponses.support (output hH s)) (WordResponses.support (output hH t)) := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  have hs : x ∈ (frame hH (word s ++ [0])).word := by
    rw [← output_word]
    exact List.mem_toFinset.mp hxs
  have ht : x ∈ (frame hH (word t ++ [0])).word := by
    rw [← output_word]
    exact List.mem_toFinset.mp hxt
  obtain ⟨p, a, hps, hp, hxp⟩ := coordinate_block hH _ (by simp [run_word_terminal]) hs
  have hheads : (word s ++ [0]).head? ≠ (word t ++ [0]).head? := by
    simpa [word] using hroots
  rcases block_separated_from_coordinate hH _ _ hheads
      (by simp [run_word_terminal]) ht p a hps hp with h | h
  · exact (Nat.lt_irrefl x) (h x hxp)
  · exact (Nat.lt_irrefl x) (h x hxp)

/-- A full-order structural family with disjoint different-root supports and
only interior-leaf cuts between different roots. No color conclusion is made. -/
theorem exists_interior_family {H : Set ℕ} (hH : H.Infinite) :
    ∃ W : Set G, W ⊆ CoordinateModel.Supported H ∧ typeLT W = lambda ∧
      ∀ s ∈ W, ∀ t ∈ W, s.1.length ≠ t.1.length →
        Disjoint (WordResponses.support s) (WordResponses.support t) ∧
        ∀ y ∈ word t.1, below y (word s.1) ≠ [] →
          below y (word s.1) ≠ word s.1 →
          ∃ P : Position, P.word = below y (word s.1) := by
  refine ⟨Set.range (output hH), ?_, output_range_type hH, ?_⟩
  · rintro s ⟨a, rfl⟩
    exact output_supported hH a
  · rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩ hroots
    have hab : a.length ≠ b.length := fun he ↦ hroots (output_root_eq_of_length_eq hH a b he)
    exact ⟨output_support_disjoint hH a b hab,
      fun _ hy hnil hproper ↦ output_interior_cut hH a b hab hy hnil hproper⟩

end Erdos118.PrefixRealization
