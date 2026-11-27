import MackeyDiagrams

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

def plainVertex : PlanarEvent → Prop
  | .vertex _ _ => True
  | _ => False

def Rigid (a : Code) : Prop :=
  (∀ e ∈ a, plainVertex e) ∧
  ∀ (pre post : Code) (e f : PlanarEvent), a = pre ++ [e, f] ++ post →
    f.position < e.position + e.outputs.length ∧
    e.position < f.position + f.inputs.length

theorem Rigid.inContext {a pre post : Code} (h : Rigid (pre ++ a ++ post)) :
    Rigid a := by
  constructor
  · intro e he
    exact h.1 e (by simp [he])
  · intro before after e f he
    exact h.2 (pre ++ before) (after ++ post) e f (by simp [he, List.append_assoc])

theorem position_place (e : PlanarEvent) (i : Nat) : (e.place i).position = i := by
  cases e <;> rfl

theorem inputs_place (e : PlanarEvent) (i : Nat) : (e.place i).inputs = e.inputs := by
  cases e <;> rfl

theorem outputs_place (e : PlanarEvent) (i : Nat) : (e.place i).outputs = e.outputs := by
  cases e <;> rfl

-- The two orientations of exchange are both excluded by intersecting
-- adjacent vertices. The context case passes rigidity to its inner segment.
theorem rigid_eq {a b : Code} (h : Equivalent a b) : (Rigid a → a = b) ∧ (Rigid b → a = b) := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨fun h => (ih.2 h).symm, fun h => (ih.1 h).symm⟩
  | trans _ _ ih₁ ih₂ =>
    constructor
    · intro hr
      have e := ih₁.1 hr
      exact e.trans (ih₂.1 (e ▸ hr))
    · intro hr
      have e := ih₂.2 hr
      exact (ih₁.2 (e.symm ▸ hr)).trans e
  | context pre post _ ih =>
    exact ⟨fun h => congrArg (fun c => pre ++ c ++ post) (ih.1 h.inContext),
      fun h => congrArg (fun c => pre ++ c ++ post) (ih.2 h.inContext)⟩
  | exchange pre post i gap l r =>
    constructor <;> intro h
    · have bad := (h.2 pre post _ _ rfl).1
      simp only [position_place, outputs_place] at bad
      omega
    · have bad := (h.2 pre post _ _ rfl).2
      simp only [position_place, inputs_place] at bad
      omega
  | scale => constructor <;> intro h <;> exact False.elim (h.1 _ (List.mem_cons_self))
  | add => constructor <;> intro h <;> exact False.elim (h.1 _ (List.mem_cons_self))

def rightCode : Code :=
  [.vertex 1 .mixedProjection, .vertex 0 .parallelUp, .vertex 1 .mixedMultiplication]

theorem rigid_rightCode : Rigid rightCode := by
  constructor
  · intro e h
    simp only [rightCode, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> trivial
  · intro pre post e f he
    have hlen := congrArg List.length he
    simp only [rightCode, List.length_append, List.length_cons, List.length_nil] at hlen
    change 3 = pre.length + 2 + post.length at hlen
    cases pre with
    | nil =>
      simp only [rightCode, List.nil_append, List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl, _⟩ := he
      decide
    | cons p pre =>
      cases pre with
      | nil =>
        simp only [rightCode, List.cons_append, List.nil_append, List.cons.injEq] at he
        obtain ⟨_, rfl, rfl, _⟩ := he
        decide
      | cons q pre =>
        simp only [List.length_cons] at hlen
        omega

end CaseFiveInfiniteAux
