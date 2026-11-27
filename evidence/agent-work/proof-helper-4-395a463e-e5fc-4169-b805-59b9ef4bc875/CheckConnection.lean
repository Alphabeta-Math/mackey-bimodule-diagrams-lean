import Middle
import MackeyDiagrams.PlanarShape

namespace CaseOneExample
open MackeyDiagrams

section Trace
universe u w
variable {U : Type u} [Group U]

private def Boundary.width {K H : Subgroup U} : Boundary K H → Nat
  | .empty _ => 0
  | .cons _ tail => width tail + 1

private abbrev two {K L H : Subgroup U} (s : Strand K L) (t : Strand L H) :
    Boundary K H :=
  .cons s (.cons t (.empty H))

private abbrev MixedEvidence (U : Type u) [Group U] :=
  ∀ {G J C P : Subgroup U}, ConjEmbedding G P → ConjEmbedding J P →
    ConjEmbedding C G → ConjEmbedding C J → Type w

variable (Evidence : MixedEvidence.{u, w} U)

private inductive TraceEdge :
    {K H : Subgroup U} → Nat → VertexKind → Boundary K H → Boundary K H → Prop
  | parallelUp {K H J J' L : Subgroup U}
      (a : ConjEmbedding J K) (b : ConjEmbedding L J)
      (a' : ConjEmbedding J' K) (b' : ConjEmbedding L J') (suffix : Boundary L H) :
      TraceEdge 0 .parallelUp ((two (.up a) (.up b)).append suffix)
        ((two (.up a') (.up b')).append suffix)
  | mixedProjection {K H P J C : Subgroup U}
      (α : ConjEmbedding K P) (β : ConjEmbedding J P)
      (η : ConjEmbedding C K) (θ : ConjEmbedding C J)
      (label : Evidence α β η θ) (suffix : Boundary J H) :
      TraceEdge 0 .mixedProjection ((two (.down α) (.up β)).append suffix)
        ((two (.up η) (.down θ)).append suffix)
  | prepend {K L H : Subgroup U} {pos : Nat} {kind : VertexKind}
      {p q : Boundary L H} (strand : Strand K L) (edge : TraceEdge pos kind p q) :
      TraceEdge (pos + 1) kind (.cons strand p) (.cons strand q)

private theorem TraceEdge.pad {K L H : Subgroup U} {p q : Boundary L H}
    {pos : Nat} {kind : VertexKind} (edge : TraceEdge Evidence pos kind p q)
    (pre : Boundary K L) :
    TraceEdge Evidence (pos + Boundary.width pre) kind (pre.append p) (pre.append q) := by
  induction pre with
  | empty => exact edge
  | cons strand tail ih =>
    simpa only [Boundary.width, Boundary.append, Nat.add_assoc] using
      (TraceEdge.prepend (Evidence := Evidence) strand (ih edge))

private theorem TraceEdge.appendSuffix {K L H : Subgroup U} {p q : Boundary K L}
    {pos : Nat} {kind : VertexKind} (edge : TraceEdge Evidence pos kind p q)
    (suffix : Boundary L H) :
    TraceEdge Evidence pos kind (p.append suffix) (q.append suffix) := by
  induction edge with
  | parallelUp a b a' b' rest => exact .parallelUp a b a' b' (rest.append suffix)
  | mixedProjection α β η θ label rest =>
    exact .mixedProjection α β η θ label (rest.append suffix)
  | prepend strand _ ih => exact .prepend strand (ih suffix)

private inductive TracePath {K H : Subgroup U} :
    PlanarCode.Code → Boundary K H → Boundary K H → Prop
  | nil (p : Boundary K H) : TracePath [] p p
  | cons {p q r : Boundary K H} {pos : Nat} {kind : VertexKind} {code : PlanarCode.Code}
      (edge : TraceEdge Evidence pos kind p q) (rest : TracePath code q r) :
      TracePath (.vertex pos kind :: code) p r

private theorem TracePath.append {K H : Subgroup U} {p q r : Boundary K H}
    {left right : PlanarCode.Code}
    (first : TracePath Evidence left p q) (second : TracePath Evidence right q r) :
    TracePath Evidence (left ++ right) p r := by
  induction first with
  | nil => exact second
  | cons edge _ ih => exact .cons edge (ih second)

private theorem TracePath.appendSuffix {K L H : Subgroup U} {p q : Boundary K L}
    {code : PlanarCode.Code} (path : TracePath Evidence code p q) (suffix : Boundary L H) :
    TracePath Evidence code (p.append suffix) (q.append suffix) := by
  induction path with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (edge.appendSuffix Evidence suffix) ih

private theorem TracePath.prependPrefix {K L H : Subgroup U} {p q : Boundary L H}
    {code : PlanarCode.Code} (path : TracePath Evidence code p q) (pre : Boundary K L) :
    TracePath Evidence (PlanarCode.shift (Boundary.width pre) code)
      (pre.append p) (pre.append q) := by
  induction path with
  | nil => exact .nil _
  | @cons p q r pos kind code edge _ ih =>
    have padded := edge.pad Evidence pre
    rw [Nat.add_comm] at padded
    exact .cons padded ih

private theorem trace_middle {G A C D E : Subgroup U}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding D D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E D)
    (path : TracePath Evidence
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]
      (Boundary.cons (.down a) (two (.up b) (.up c)))
      (Boundary.cons (.up d) (two (.up e) (.down f)))) :
    ∃ (P J : Subgroup U) (α : ConjEmbedding G P) (β : ConjEmbedding J P)
      (η : ConjEmbedding C G) (θ : ConjEmbedding C J) (_w : ConjEmbedding D J),
      Nonempty (Evidence α β η θ) := by
  cases path with
  | cons first rest =>
    cases rest with
    | cons middle rest =>
      cases rest with
      | cons last tail =>
        cases tail
        cases last with
        | prepend strand last =>
          cases last with
          | mixedProjection α β η θ label suffix =>
            cases middle with
            | mixedProjection αm βm ηm θm m suffix =>
              exact ⟨_, _, αm, βm, d, α, β, ⟨m⟩⟩

private abbrev MixedWitness : MixedEvidence.{u, u} U :=
  fun α β η θ => ProjectionDot.Mixed α β η θ

end Trace
end CaseOneExample
namespace CaseOneExample
open MackeyDiagrams

private theorem right_trace_impossible {A E : Subgroup U}
    (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding D D)
    (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E D)
    (path : TracePath MixedWitness
      [.vertex 1 .parallelUp, .vertex 0 .mixedProjection, .vertex 1 .mixedProjection]
      (((Word.down a).tensor (.up b)).tensor (.up c)).boundary
      (((Word.up d).tensor (.up e)).tensor (.down f)).boundary) : False := by
  obtain ⟨P, J, α, β, η, θ, w, ⟨m⟩⟩ := trace_middle MixedWitness a b c d e f path
  exact middle_projection_empty α β η θ w m

#print axioms right_trace_impossible
end CaseOneExample
