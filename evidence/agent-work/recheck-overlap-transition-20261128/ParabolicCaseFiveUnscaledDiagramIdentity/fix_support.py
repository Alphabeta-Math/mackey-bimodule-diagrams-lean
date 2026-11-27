p='Support.lean';s=open(p).read()
s=s.replace('(.ordinary (.associate (.up c) (.down e) (.up f)))))))','(.ordinary (.associate (.up c) (.down e) (.up f))))))))')
start=s.index('  repeat first\n')
en=s.index('\nprivate theorem natural_right',start)
s=s[:start]+'''  exact natural_drawing_vertical (natural_unassociate (.up a) (.down b) (.up d))
    (natural_drawing_vertical
      (natural_drawing_horizontal (natural_multiplication u v a b r) (natural_drawing_id (.up d)))
      (natural_drawing_vertical (natural_associate (.down u) (.up v) (.up d))
        (natural_drawing_vertical
          (natural_drawing_horizontal (natural_drawing_id (.down u)) (natural_parallel v d w f t))
          (natural_drawing_vertical (natural_unassociate (.down u) (.up w) (.up f))
            (natural_drawing_vertical
              (natural_drawing_horizontal (natural_projection u w c e s) (natural_drawing_id (.up f)))
              (natural_associate (.up c) (.down e) (.up f)))))))
''' +s[en:]
start=s.index('  repeat first\n')
en=s.index('\nprivate theorem weighted_left',start)
s=s[:start]+'''  exact natural_drawing_vertical
    (natural_drawing_horizontal (natural_drawing_id (.up a)) (natural_projection b d i j r))
    (natural_drawing_vertical (natural_unassociate (.up a) (.up i) (.down j))
      (natural_drawing_vertical
        (natural_drawing_horizontal (natural_parallel a i c k t) (natural_drawing_id (.down j)))
        (natural_drawing_vertical (natural_associate (.up c) (.up k) (.down j))
          (natural_drawing_horizontal (natural_drawing_id (.up c)) (natural_multiplication e f k j s)))))
''' +s[en:]
st=s.index('    change post ((((ScopedDiagram.linearCombination')
en=s.index('  have hmain',st)
s=s[:st]+'''    let L' := ((ScopedDiagram.linearCombination [(1, lower r)]).eval.horizontal
      (Biset.Hom.id df.basis)).toLinearMap
    let M' := ((Biset.Hom.id du.basis).horizontal
      (ScopedDiagram.linearCombination [(1, center t)]).eval).toLinearMap
    let N' := ((ScopedDiagram.linearCombination [(1, upper s)]).eval.horizontal
      (Biset.Hom.id ef.basis)).toLinearMap
    change post (N' (mid₂ (M' (mid₁ (L' (pre m)))))) = _
    dsimp only [L', M', N']
    rw [eval_singleton, eval_singleton, eval_singleton]
''' +s[en:]
st=s.index('    have ht : ')
en=s.index('  rw [hmain',st)
s=s[:st]+'''    let rawTerms := (ss.terms.map (fun (cs,s) => (cs, (⟨s, fin s⟩ : ProjectionDot.Mixed u w c e)))).map
        (fun (cs,s) => (cs, ScopedDiagram.ordinary
          (Diagram.mixedProjection (R := R) u w c e s.dot s.finite)))
    have ht : rawTerms = ss.support.toList.map (fun s => (ss s, upper s)) := by
      simp only [rawTerms, DotLabel.terms, List.map_map]
      rfl
    let N' := ((ScopedDiagram.linearCombination rawTerms).eval.horizontal
      (Biset.Hom.id ef.basis)).toLinearMap
    change post (N' (mid₂ (M (mid₁ (L (pre m)))))) = _
    dsimp only [N']
    rw [ht]
''' +s[en:]
s += '\nopen MackeyDiagrams CaseFiveUnscaled\n'
open(p,'w').write(s)
p='Proof.txt';s=open(p).read().replace('  · open MackeyDiagrams CaseFiveUnscaled in\n    intro', '  · intro');open(p,'w').write(s)
