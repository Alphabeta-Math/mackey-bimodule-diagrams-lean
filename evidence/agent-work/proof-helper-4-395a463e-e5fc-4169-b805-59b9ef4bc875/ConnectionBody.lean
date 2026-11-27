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
