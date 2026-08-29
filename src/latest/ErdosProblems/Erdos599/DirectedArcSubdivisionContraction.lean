/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedArcSubdivision

/-!
# Contracting directed-arc subdivisions

A subdivided walk is contracted by discarding its first two private edges
and retaining the last edge of every three-edge gadget as the represented
original arc.  The support formula below is stated for arbitrary endpoints;
the finite-path interface then specializes to original endpoints.
-/

namespace Erdos599
namespace DirectedArcSubdivision

open DirectedPath Set

universe u

variable {V : Type u} {D : Digraph V}

/-- Extract an original vertex and discard either kind of private vertex. -/
def original? : Vertex D → Option V
  | .original x => some x
  | .first _ => none
  | .second _ => none

@[simp] theorem original?_original (x : V) :
    original? (D := D) (.original x) = some x := rfl

@[simp] theorem original?_first (e : Arc D) :
    original? (.first e) = none := rfl

@[simp] theorem original?_second (e : Arc D) :
    original? (.second e) = none := rfl

@[simp] theorem project_original (x : V) :
    project (D := D) (.original x) = x := rfl

@[simp] theorem project_first (e : Arc D) :
    project (.first e) = e.1.1 := rfl

@[simp] theorem project_second (e : Arc D) :
    project (.second e) = e.1.1 := rfl

/-- Contract a subdivided walk.  Only a `second e → original e.head` edge
emits the represented original edge `e`; the other two gadget edges are
stutters under `project`. -/
private def castWalkStart {x y z : V} (h : x = y) (p : Walk D y z) :
    Walk D x z := by
  subst y
  exact p

def contractWalk : {a b : Vertex D} → Walk (graph D) a b →
    Walk D (project a) (project b)
  | _, _, .nil => .nil
  | .original x, _, .cons (v := .original y) h _ => False.elim h
  | .original x, _, .cons (v := .first e) h p =>
      castWalkStart h (contractWalk p)
  | .original x, _, .cons (v := .second e) h _ => False.elim h
  | .first e, _, .cons (v := .original y) h _ => False.elim h
  | .first e, _, .cons (v := .first f) h _ => False.elim h
  | .first e, _, .cons (v := .second f) h p =>
      castWalkStart (congrArg (fun g : Arc D => g.1.1) h) (contractWalk p)
  | .second e, _, .cons (v := .original y) h p =>
      Walk.cons e.2 (castWalkStart h (contractWalk p))
  | .second e, _, .cons (v := .first f) h _ => False.elim h
  | .second e, _, .cons (v := .second f) h _ => False.elim h

/-- Exact list formula for contraction of an arbitrary subdivided walk. -/
theorem support_contractWalk {a b : Vertex D}
    (p : Walk (graph D) a b) :
    (contractWalk p).support =
      project a :: p.support.tail.filterMap original? := by
  induction p with
  | nil => rfl
  | @cons a c b h p ih =>
      cases a with
      | original x =>
          cases c with
          | original y => exact False.elim h
          | first e =>
              have hxe : x = e.1.1 := h
              subst x
              change (contractWalk p).support =
                e.1.1 :: p.support.filterMap original?
              rw [ih]
              have hp : p.support = .first e :: p.support.tail := by
                calc
                  p.support = p.support.head p.support_ne_nil ::
                      p.support.tail :=
                    (p.support.cons_head_tail p.support_ne_nil).symm
                  _ = .first e :: p.support.tail := by rw [p.head_support]
              rw [hp]
              rfl
          | second e => exact False.elim h
      | first e =>
          cases c with
          | original y => exact False.elim h
          | first f => exact False.elim h
          | second f =>
              have hef : e = f := h
              subst f
              change (contractWalk p).support =
                e.1.1 :: p.support.filterMap original?
              rw [ih]
              have hp : p.support = .second e :: p.support.tail := by
                calc
                  p.support = p.support.head p.support_ne_nil ::
                      p.support.tail :=
                    (p.support.cons_head_tail p.support_ne_nil).symm
                  _ = .second e :: p.support.tail := by rw [p.head_support]
              rw [hp]
              rfl
      | second e =>
          cases c with
          | original y =>
              have hey : e.1.2 = y := h
              subst y
              rw [contractWalk.eq_def]
              dsimp only [castWalkStart, project, Walk.support]
              have hp : p.support = .original e.1.2 :: p.support.tail := by
                calc
                  p.support = p.support.head p.support_ne_nil ::
                      p.support.tail :=
                    (p.support.cons_head_tail p.support_ne_nil).symm
                  _ = .original e.1.2 :: p.support.tail := by rw [p.head_support]
              have ih' : (contractWalk p).support =
                  e.1.2 :: p.support.tail.filterMap original? := by
                simpa only [project_original] using ih
              congr 1
              calc
                (contractWalk p).support =
                    e.1.2 :: p.support.tail.filterMap original? := ih'
                _ = p.support.filterMap original? := by rw [hp]; rfl
                _ = (Vertex.second e :: p.support).tail.filterMap original? := rfl
          | first f => exact False.elim h
          | second f => exact False.elim h

/-- For an original-start walk, contraction keeps exactly the original
vertices in its support. -/
theorem support_contractWalk_original_start {a : V} {b : Vertex D}
    (p : Walk (graph D) (.original a) b) :
    (contractWalk p).support = p.support.filterMap original? := by
  rw [support_contractWalk]
  cases hp : p.support with
  | nil => exact (p.support_ne_nil hp).elim
  | cons x xs =>
      have hx : x = .original a := by
        apply Option.some.inj
        calc
          some x = p.support.head? := by simp [hp]
          _ = some (.original a) := by
            rw [List.head?_eq_some_head p.support_ne_nil, p.head_support]
      subst x
      simpa using project_original (D := D) a

/-- Original-vertex support is preserved exactly by contraction. -/
@[simp] theorem original_mem_support_contractWalk {a : V} {b : Vertex D}
    (p : Walk (graph D) (.original a) b) (x : V) :
    x ∈ (contractWalk p).support ↔ .original x ∈ p.support := by
  rw [support_contractWalk_original_start]
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨z, hz, hzx⟩
    cases z with
    | original y =>
        simp at hzx
        subst y
        exact hz
    | first e => simp at hzx
    | second e => simp at hzx
  · intro hx
    exact ⟨.original x, hx, by simp⟩

/-- Every subdivided-walk vertex projects onto the contracted support. -/
theorem project_mem_support_contractWalk {a b : Vertex D}
    (p : Walk (graph D) a b) {z : Vertex D}
    (hz : z ∈ p.support) : project z ∈ (contractWalk p).support := by
  induction p with
  | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact (contractWalk (.nil : Walk (graph D) _ _)).start_mem_support
  | @cons a c b h p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hz
      cases a with
      | original x =>
          cases c with
          | original y => exact False.elim h
          | first e =>
              have hxe : x = e.1.1 := h
              subst x
              rcases hz with rfl | hz
              · exact (contractWalk p).start_mem_support
              · exact ih hz
          | second e => exact False.elim h
      | first e =>
          cases c with
          | original y => exact False.elim h
          | first f => exact False.elim h
          | second f =>
              have hef : e = f := h
              subst f
              rcases hz with rfl | hz
              · exact (contractWalk p).start_mem_support
              · exact ih hz
      | second e =>
          cases c with
          | original y =>
              have hey : e.1.2 = y := h
              subst y
              rcases hz with rfl | hz
              · exact (Walk.cons e.2 (contractWalk p)).start_mem_support
              · exact List.mem_cons_of_mem _ (ih hz)
          | first f => exact False.elim h
          | second f => exact False.elim h

private theorem original?_fiber_injective
    (a b : Vertex D) (x : V)
    (ha : x ∈ original? a) (hb : x ∈ original? b) : a = b := by
  cases a with
  | original y =>
      cases b with
      | original z =>
          simp at ha hb
          subst y
          subst z
          rfl
      | first e => simp at hb
      | second e => simp at hb
  | first e => simp at ha
  | second e => simp at ha

/-- Contraction of a simple subdivided walk with original endpoints is an
original finite path. -/
def contractFinitePath (p : FinitePath (graph D)) {a b : V}
    (hstart : p.start = .original a) (hfinish : p.finish = .original b) :
    FinitePath D := by
  rcases p with ⟨s, t, p, hp⟩
  dsimp only at hstart hfinish
  subst s
  subst t
  exact
    { start := a
      finish := b
      walk := contractWalk p
      isPath := by
        change (contractWalk p).support.Nodup
        rw [support_contractWalk_original_start]
        exact hp.filterMap original?_fiber_injective }

@[simp] theorem contractFinitePath_start
    (p : FinitePath (graph D)) {a b : V}
    (hstart : p.start = .original a) (hfinish : p.finish = .original b) :
    (contractFinitePath p hstart hfinish).start = a := by
  rcases p with ⟨s, t, p, hp⟩
  dsimp only at hstart hfinish
  subst s
  subst t
  rfl

@[simp] theorem contractFinitePath_finish
    (p : FinitePath (graph D)) {a b : V}
    (hstart : p.start = .original a) (hfinish : p.finish = .original b) :
    (contractFinitePath p hstart hfinish).finish = b := by
  rcases p with ⟨s, t, p, hp⟩
  dsimp only at hstart hfinish
  subst s
  subst t
  rfl

/-- Exact original-vertex support formula for a contracted finite path. -/
@[simp] theorem mem_support_contractFinitePath_iff
    (p : FinitePath (graph D)) {a b x : V}
    (hstart : p.start = .original a) (hfinish : p.finish = .original b) :
    x ∈ (contractFinitePath p hstart hfinish).support ↔
      .original x ∈ p.support := by
  rcases p with ⟨s, t, p, hp⟩
  dsimp only at hstart hfinish
  subst s
  subst t
  exact original_mem_support_contractWalk p x

/-- Every vertex of the split finite path projects onto the contracted
finite-path support. -/
theorem project_mem_support_contractFinitePath
    (p : FinitePath (graph D)) {a b : V} {z : Vertex D}
    (hstart : p.start = .original a) (hfinish : p.finish = .original b)
    (hz : z ∈ p.support) :
    project z ∈ (contractFinitePath p hstart hfinish).support := by
  rcases p with ⟨s, t, p, hp⟩
  dsimp only at hstart hfinish hz
  subst s
  subst t
  exact project_mem_support_contractWalk p hz

#print axioms support_contractWalk
#print axioms contractFinitePath
#print axioms mem_support_contractFinitePath_iff
#print axioms project_mem_support_contractFinitePath

end DirectedArcSubdivision
end Erdos599
