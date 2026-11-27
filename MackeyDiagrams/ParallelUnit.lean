import MackeyDiagrams.ParallelComposition

/-! A unit product removes its dot. If both boundary words agree, the two
remaining trivalent vertices cancel as well. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {G K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace Dot

theorem sameEmbedding_of_unit {a b : ConjEmbedding K G} (d : Dot a b)
    (unit : d.element = 1) : a = b := by
  apply ConjEmbedding.ext
  apply MonoidHom.ext
  intro k
  simpa [unit] using d.intertwines k

end Dot

namespace Diagram

def transportUpId {a b : ConjEmbedding K G} (same : a = b) :
    Diagram R (.up a) (.up b) :=
  same ▸ id (.up a)

theorem eval_upDot_unit {a b : ConjEmbedding K G} (d : Dot a b) (unit : d.element = 1) :
    ∃ same : a = b, (upDot (R := R) d).eval = (transportUpId same).eval := by
  have same := d.sameEmbedding_of_unit unit
  subst b
  have he : d = Dot.id a := Dot.ext unit
  exact ⟨rfl, by change (upDot (R := R) d).eval = (id (.up a)).eval
                 rw [he, eval_upDot_id]⟩

theorem eval_linearUpDot_unit [Nontrivial R] {a b : ConjEmbedding K G}
    (c : Dot a b →₀ R)
    (unit : Finsupp.mapDomain Dot.element c = Finsupp.single (1 : G) (1 : R)) :
    ∃ same : a = b, (linearUpDot c).eval = (transportUpId same).eval := by
  have h1 : (1 : G) ∈ Set.range (Dot.element (a := a) (b := b)) := by
    by_contra hh
    have hv := DFunLike.congr_fun unit (1 : G)
    rw [Finsupp.mapDomain_of_notMem_range c 1 hh, Finsupp.single_eq_same] at hv
    exact zero_ne_one hv
  obtain ⟨d,hd⟩ := h1
  have same := d.sameEmbedding_of_unit hd
  subst b
  have hu : c = Finsupp.single (Dot.id a) 1 := by
    apply Finsupp.mapDomain_injective (fun _ _ e => Dot.ext e)
    rw [unit, Finsupp.mapDomain_single]
    rfl
  refine ⟨rfl, ?_⟩
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change G →₀ R at z
  rw [hu, eval_linearUpDot_apply, freeLift_single, one_smul]
  exact LinearMap.congr_fun (congrArg Biset.Hom.toLinearMap (eval_upDot_id (R := R) a)) z

private def middleGroup {A B : Subgroup U} (w : Word A B) : Option (Subgroup U) :=
  match w with
  | .tensor (B := M) _ _ => some M
  | _ => none

theorem eval_unitCrossing_sameBoundary {H' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (same : b.comp a = b'.comp a')
    (boundary : (Word.up b).tensor (.up a) = (Word.up b').tensor (.up a')) :
    (((mergeUp (R := R) b a).vertical (transportUpId same)).vertical (splitUp b' a')).eval =
      (Eq.ndrec (motive := fun word => Diagram R ((Word.up b).tensor (.up a)) word)
        (id ((Word.up b).tensor (.up a))) boundary).eval := by
  have hmid : H = H' := Option.some.inj (congrArg middleGroup boundary)
  subst H'
  have hb : b = b' := by
    cases boundary
    rfl
  have ha : a = a' := by
    cases boundary
    rfl
  subst b'
  subst a'
  have hSame : same = rfl := Subsingleton.elim _ _
  have hBoundary : boundary = rfl := Subsingleton.elim _ _
  cases hSame
  cases hBoundary
  change (mergeUp (R := R) b a).eval.vertical
    ((Biset.Hom.id _).vertical (splitUp b a).eval) = _
  rw [Biset.Hom.id_vertical]
  exact mergeUp_splitUp b a

end Diagram
end MackeyDiagrams
