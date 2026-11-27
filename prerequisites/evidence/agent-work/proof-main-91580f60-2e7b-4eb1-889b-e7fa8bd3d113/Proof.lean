by
  -- Theorem 10.1, p. 32. Portal steps 1.2 and 1.3 supply the comparison
  -- directions after using the article's evaluation direction for the unit.
  intro R _
  refine ⟨NotesTensorDictionary.regular R, ?_⟩
  intro S T _ _ B C _ _ _ _ _ _ _ _ TB TC CB pureCB
  refine ⟨NotesTensorDictionary.left_pure B C, ?_⟩
  refine ⟨NotesTensorDictionary.rightModule B C, NotesTensorDictionary.right_pure B C, ?_⟩
  exact ⟨NotesTensorDictionary.rightCommutes B C, NotesTensorDictionary.composition R S T B C,
    NotesTensorDictionary.composition_pure R S T B C⟩
