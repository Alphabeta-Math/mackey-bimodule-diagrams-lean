import NotesProofs.General.BimoduleTensorCategory

universe a b

/-- The rings may lie in a smaller universe than the modules. -/
theorem notesWatts_universeAudit (R S : Type a) [Ring R] [Ring S] :
    Nonempty (NotesProofs.General.ConcreteBimodule.{a,b} R S ≌
      NotesProofs.General.ConcreteBimodule.GoodFunctors.{a,b} R S) :=
  ⟨NotesProofs.General.ConcreteBimodule.eilenbergWattsEquivalence.{a,b} R S⟩

#print axioms notesWatts_universeAudit
