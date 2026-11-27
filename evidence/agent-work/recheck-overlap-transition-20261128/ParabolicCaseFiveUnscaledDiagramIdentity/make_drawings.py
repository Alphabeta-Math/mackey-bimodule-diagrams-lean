p='Support.lean';s=open(p).read()
s=s[:s.rfind('\nend\nend CaseFiveUnscaled')]
s+='''
private abbrev caseWord {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :=
  (Word.up a).tensor ((Word.down b).tensor (.up d))

private abbrev casePoint {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (g : G) (x : D) : (caseWord a b d).basis.carrier :=
  (Biset.induction a).pair ((Word.down b).tensor (.up d)).basis g (Generator.mixedPair b d x)

private theorem casePoint_surjective {G A D F : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
    (z : (caseWord a b d).basis.carrier) : ∃ g x, casePoint a b d g x = z := by
  obtain ⟨⟨g, y⟩, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x, rfl⟩ := (Generator.mixedEquiv b d).symm.surjective y
  exact ⟨g, x, rfl⟩

private theorem caseWord_finite {G A D F : Subgroup U}
    [Finite G] [Finite D]
    (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D) :
    Finite (caseWord a b d).basis.carrier :=
  Finite.of_surjective (fun p : G × D => casePoint a b d p.1 p.2) (by
    intro z
    obtain ⟨g, x, h⟩ := casePoint_surjective a b d z
    exact ⟨(g, x), h⟩)
'''
source=open('/home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/Proofs/ParabolicRightOrbitMultiplicity.lean').read()
t=source[source.index('private abbrev Sinf :='):source.index('private theorem parabolic_extremal')]
s+=t[:t.index('private abbrev swaps')]+t[t.index('private theorem parabolic_finite'):]
s+='''
section Drawings

variable {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (u : ConjEmbedding G B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)

private abbrev lowerLabel := Dot (u.comp a) (v.comp b)
private abbrev middleLabel := Dot (v.comp d) (w.comp f)
private abbrev upperLabel := Dot (u.comp c) (w.comp e)

private abbrev leftDrawing
    (rs : List (R × lowerLabel a b u v)) (ts : List (R × middleLabel d f v w))
    (ss : List (R × ProjectionDot.Mixed u w c e)) :
    LabelledDrawing R (caseWord a b d) (caseWord c e f) :=
  .vertical (.ordinary (.unassociate (.up a) (.down b) (.up d)))
    (.vertical (.horizontal (.mixedMultiplication u v a b rs) (.ordinary (.id (.up d))))
      (.vertical (.ordinary (.associate (.down u) (.up v) (.up d)))
        (.vertical (.horizontal (.ordinary (.id (.down u))) (.parallelUp v d w f ts))
          (.vertical (.ordinary (.unassociate (.down u) (.up w) (.up f)))
            (.vertical (.horizontal (.compactProjection u w c e ss) (.ordinary (.id (.up f))))
              (.ordinary (.associate (.up c) (.down e) (.up f)))))))

private abbrev rightDrawing (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (k : ConjEmbedding B C) (r : ProjectionDot.Mixed b d i j)
    (t : Dot (a.comp i) (c.comp k)) (s : Dot (e.comp k) (f.comp j)) :
    LabelledDrawing R (caseWord a b d) (caseWord c e f) :=
  .vertical (.horizontal (.ordinary (.id (.up a))) (.compactProjection b d i j [(1,r)]))
    (.vertical (.ordinary (.unassociate (.up a) (.up i) (.down j)))
      (.vertical (.horizontal (.parallelUp a i c k [(1,t)]) (.ordinary (.id (.down j))))
        (.vertical (.ordinary (.associate (.up c) (.up k) (.down j)))
          (.horizontal (.ordinary (.id (.up c))) (.mixedMultiplication e f k j [(1,s)])))))

-- The coefficient count in the proof of Proposition 8.7 is independent of the ring.
-- Check the same singleton drawing first over Nat. Its identity and reassociation
-- columns are deterministic, and its compact projection sums over the same fiber.
private theorem natural_left (r : lowerLabel a b u v) (t : middleLabel d f v w)
    (s : ProjectionDot.Mixed u w c e) :
    NaturalDrawing (leftDrawing a b d c e f u v w [(1,r)] [(1,t)] [(1,s)])
      (leftDrawing (R := R) a b d c e f u v w [(1,r)] [(1,t)] [(1,s)]) := by
  repeat first
    | apply natural_drawing_vertical
    | apply natural_drawing_horizontal
    | apply natural_drawing_id
    | apply natural_associate
    | apply natural_unassociate
    | apply natural_parallel
    | apply natural_multiplication
    | apply natural_projection

private theorem natural_right (i : ConjEmbedding B A) (j : ConjEmbedding B F)
    (k : ConjEmbedding B C) (r : ProjectionDot.Mixed b d i j)
    (t : Dot (a.comp i) (c.comp k)) (s : Dot (e.comp k) (f.comp j)) :
    NaturalDrawing (rightDrawing a b d c e f i j k r t s)
      (rightDrawing (R := R) a b d c e f i j k r t s) := by
  repeat first
    | apply natural_drawing_vertical
    | apply natural_drawing_horizontal
    | apply natural_drawing_id
    | apply natural_associate
    | apply natural_unassociate
    | apply natural_parallel
    | apply natural_multiplication
    | apply natural_projection

private theorem weighted_left
    (rs : DotLabel R (u.comp a) (v.comp b)) (ts : DotLabel R (v.comp d) (w.comp f))
    (ss : DotLabel R (u.comp c) (w.comp e))
    (fin : ∀ s : upperLabel c e u w, ∀ z,
      Set.Finite {p | Generator.mixedMultiplicationBasis u w c e s p = z})
    (m : (caseWord a b d).basis.carrier →₀ R) :
    (drawingEval (leftDrawing a b d c e f u v w rs.terms ts.terms
      (ss.terms.map (fun (cs,s) => (cs, ⟨s, fin s⟩))))).toLinearMap m =
    rs.sum (fun r cr => ts.sum (fun t ct => ss.sum (fun s cs => (cr * ct * cs) •
      (drawingEval (leftDrawing a b d c e f u v w [(1,r)] [(1,t)]
        [(1, ⟨s, fin s⟩)] )).toLinearMap m))) := by
  classical
  let ga := Word.up a
  let ad := Word.down b
  let df := Word.up d
  let gc := Word.up c
  let ce := Word.down e
  let ef := Word.up f
  let du := Word.down u
  let uv := Word.up v
  let uw := Word.up w
  let pre := (Diagram.unassociate (R := R) ga ad df).eval.toLinearMap
  let mid₁ := (Diagram.associate (R := R) du uv df).eval.toLinearMap
  let mid₂ := (Diagram.unassociate (R := R) du uw ef).eval.toLinearMap
  let post := (Diagram.associate (R := R) gc ce ef).eval.toLinearMap
  let lower (r : lowerLabel a b u v) := ScopedDiagram.ordinary (Diagram.mixedMultiplication (R := R) u v a b r)
  let center (t : middleLabel d f v w) := ScopedDiagram.ordinary (Diagram.parallelUp (R := R) v d w f t)
  let upper (s : upperLabel c e u w) := ScopedDiagram.ordinary (Diagram.mixedProjection (R := R) u w c e s (fin s))
  let terms {ι : Type} {K H : Subgroup U} {p q : Word K H}
      (l : ι →₀ R) (Dg : ι → ScopedDiagram R p q) :=
    ScopedDiagram.linearCombination (l.support.toList.map (fun i => (l i, Dg i)))
  let L := ((terms rs lower).eval.horizontal (Biset.Hom.id df.basis)).toLinearMap
  let M := ((Biset.Hom.id du.basis).horizontal (terms ts center).eval).toLinearMap
  let N := ((terms ss upper).eval.horizontal (Biset.Hom.id ef.basis)).toLinearMap
  let Lr := fun r => ((lower r).eval.horizontal (Biset.Hom.id df.basis)).toLinearMap
  let Mt := fun t => ((Biset.Hom.id du.basis).horizontal (center t).eval).toLinearMap
  let Ns := fun s => ((upper s).eval.horizontal (Biset.Hom.id ef.basis)).toLinearMap
  have hL x : L x = rs.sum (fun r cr => cr • Lr r x) :=
    frame_right_sum rs _ _ _ (linearCombination_map rs lower) x
  have hM x : M x = ts.sum (fun t ct => ct • Mt t x) :=
    frame_left_sum ts _ _ _ (linearCombination_map ts center) x
  have hN x : N x = ss.sum (fun s cs => cs • Ns s x) :=
    frame_right_sum ss _ _ _ (linearCombination_map ss upper) x
  have singleton r t s :
      (drawingEval (leftDrawing a b d c e f u v w [(1,r)] [(1,t)]
        [(1, ⟨s, fin s⟩)])).toLinearMap m =
      post (Ns s (mid₂ (Mt t (mid₁ (Lr r (pre m)))))) := by
    change post ((((ScopedDiagram.linearCombination [(1, upper s)]).eval.horizontal
      (Biset.Hom.id ef.basis)).toLinearMap
        (mid₂ (((Biset.Hom.id du.basis).horizontal
          (ScopedDiagram.linearCombination [(1, center t)]).eval).toLinearMap
            (mid₁ ((((ScopedDiagram.linearCombination [(1, lower r)]).eval.horizontal
              (Biset.Hom.id df.basis)).toLinearMap (pre m))))))) = _
    rw [eval_singleton, eval_singleton, eval_singleton]
  have hmain :
      (drawingEval (leftDrawing a b d c e f u v w rs.terms ts.terms
        (ss.terms.map (fun (cs,s) => (cs, ⟨s, fin s⟩))))).toLinearMap m =
      post (N (mid₂ (M (mid₁ (L (pre m)))))) := by
    have ht : (ss.terms.map (fun (cs,s) => (cs, (⟨s, fin s⟩ : ProjectionDot.Mixed u w c e)))).map
        (fun (cs,s) => (cs, ScopedDiagram.ordinary
          (Diagram.mixedProjection (R := R) u w c e s.dot s.finite))) =
        ss.support.toList.map (fun s => (ss s, upper s)) := by
      simp only [DotLabel.terms, List.map_map]
      rfl
    change post (((ScopedDiagram.linearCombination _).eval.horizontal
      (Biset.Hom.id ef.basis)).toLinearMap (mid₂ (M (mid₁ (L (pre m)))))) = _
    rw [ht]
  rw [hmain, hL]
  simp only [Finsupp.sum, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro r _
  rw [hM]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [hN]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum, singleton, smul_smul]

end Drawings

end
end CaseFiveUnscaled
'''
s=s.replace('let terms {ι : Type} {K H : Subgroup U}', 'let terms {ι : Type u} {K H : Subgroup U}')
open(p,'w').write(s)
