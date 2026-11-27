import Proofs.EvaluationWithOneProjection

set_option Elab.async false
set_option maxHeartbeats 2000000
namespace OverlapLeft
open MackeyDiagrams MackeyDiagrams.Generator
open scoped BigOperators
noncomputable section

variable {U : Type} [Group U] {D E B : Subgroup U}
local notation "T" => (⊥ : Subgroup U)

abbrev a {U : Type} [Group U] : ConjEmbedding (⊥ : Subgroup U) ⊥ := ConjEmbedding.id _
def dot {H : Subgroup U} {α β : ConjEmbedding T H} (z : H) : Dot α β :=
  ⟨z, fun y => by
    have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.mp y.property)
    simp [hy]⟩

abbrev lo (u : ConjEmbedding T B) (v : ConjEmbedding D B) (b : ConjEmbedding T D) : Dot (u.comp a) (v.comp b) := dot 1
abbrev hi (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) : Dot (u.comp a) (w.comp e) := dot 1
abbrev mid (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E) (r : D) (s : E) : Dot (v.comp b) (w.comp e) :=
  dot ((v.toHom r)⁻¹ * w.toHom s)

abbrev targetPair (e : ConjEmbedding T E) : Word T E := (Word.up (a (U := U))).tensor (Word.down e)
abbrev targetRep (e : ConjEmbedding T E) (y : E) : (targetPair e).basis.carrier :=
  Biset.pair (Word.up a).basis (Word.down e).basis (1 : T) y

abbrev q (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) (p : (targetPair e).basis.carrier) :=
  mixedProduct u w (mixedMultiplicationBasis u w a e (hi u w e) p)

theorem targetRep_surj (e : ConjEmbedding T E) : Function.Surjective (targetRep e) := by
  intro p
  refine Quotient.inductionOn p (fun ⟨h,y⟩ => ?_)
  have hh : h = 1 := Subtype.ext (Subgroup.mem_bot.mp h.property)
  exact ⟨y, by subst h; rfl⟩

theorem q_rep (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) (y : E) : q u w e (targetRep e y) = w.toHom y := by
  change mixedProduct u w (mixedPair u w (u.toHom 1 * 1 * w.toHom y)) = _
  rw [mixedProduct_mixedPair, map_one, one_mul, one_mul]

theorem q_inj (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) : Function.Injective (q u w e) := by
  intro p p'
  obtain ⟨y, rfl⟩ := targetRep_surj e p
  obtain ⟨y', rfl⟩ := targetRep_surj e p'
  rw [q_rep, q_rep]
  exact fun h => congrArg (targetRep e) (w.injective h)

theorem finite_inj {X Y : Type} {f : X → Y} (hf : Function.Injective f) (y : Y) :
    Set.Finite {x | f x = y} := by
  by_cases h : ∃ x, f x = y
  · obtain ⟨x, hx⟩ := h
    exact (Set.finite_singleton x).subset
      (fun z hz => Set.mem_singleton_iff.mpr (hf (hz.trans hx.symm)))
  · exact Set.finite_empty.subset (fun z hz => (h ⟨z, hz⟩).elim)

theorem finite_q (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) (z : B) : Set.Finite {p | q u w e p = z} :=
  finite_inj (q_inj u w e) z

theorem finite_left (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E)
    (z : ((Biset.restriction u).tensor (Biset.induction w)).carrier) :
    Set.Finite {p | mixedMultiplicationBasis u w a e (hi u w e) p = z} :=
  (finite_q u w e (mixedProduct u w z)).subset
    (fun _ hp => congrArg (mixedProduct u w) hp)

theorem matrix_eq (v : ConjEmbedding D B) (w : ConjEmbedding E B) (hDE : D ⊓ E = ⊥) (hv : ∀ z : D, (v.toHom z : U) = z)
    (hw : ∀ z : E, (w.toHom z : U) = z) (r x : D) (s y : E) :
    w.toHom y = v.toHom x * ((v.toHom r)⁻¹ * w.toHom s) ↔ x = r ∧ y = s := by
  constructor
  · intro h
    have he : (x : U) * (r : U)⁻¹ = (y : U) * (s : U)⁻¹ := by
      have hz := congrArg Subtype.val h
      change (w.toHom y : U) =
        (v.toHom x : U) * ((v.toHom r : U)⁻¹ * (w.toHom s : U)) at hz
      rw [hw, hv, hv, hw] at hz
      calc
        _ = ((x : U) * ((r : U)⁻¹ * (s : U))) * (s : U)⁻¹ := by group
        _ = _ := by rw [← hz]
    have hm : (x : U) * (r : U)⁻¹ ∈ D ⊓ E :=
      ⟨D.mul_mem x.property (D.inv_mem r.property),
        he ▸ E.mul_mem y.property (E.inv_mem s.property)⟩
    have hone : (x : U) * (r : U)⁻¹ = 1 := Subgroup.mem_bot.mp (hDE ▸ hm)
    have hxr : x = r := Subtype.ext (mul_inv_eq_one.mp hone)
    subst x
    exact ⟨rfl, w.injective (by simpa [mul_assoc] using h)⟩
  · rintro ⟨rfl, rfl⟩
    simp

abbrev drawId {H K : Subgroup U} (p : Word H K) :=
  LabelledDrawing.ordinary (Diagram.id (R := Complex) p)

abbrev atLeft {K J J' L M : Subgroup U}
    {p : Word K J} {q : Word J L} {p' : Word K J'} {q' : Word J' L}
    (tail : Word L M) (cross : LabelledDrawing Complex (p.tensor q) (p'.tensor q')) :=
  LabelledDrawing.vertical (.ordinary (.unassociate p q tail))
    (.vertical (.horizontal cross (drawId tail)) (.ordinary (.associate p' q' tail)))

abbrev bottom (b : ConjEmbedding T D) : Word T T := (Word.up (a (U := U))).tensor ((Word.down b).tensor (Word.up b))
abbrev top (e : ConjEmbedding T E) : Word T T := (Word.up (a (U := U))).tensor ((Word.down e).tensor (Word.up e))

abbrev left (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E) (r : D) (s : E) : LabelledDrawing Complex (bottom b) (top e) :=
  .vertical
    (atLeft (.up b) (.mixedMultiplication u v a b [(1, lo u v b)]))
    (.vertical (.horizontal (drawId (.down u)) (.parallelUp v b w e [(1, mid v w b e r s)]))
      (atLeft (.up e) (.compactProjection u w a e [(1, ⟨hi u w e, finite_left u w e⟩)])))

abbrev ev {K H : Subgroup U} {p p' : Word K H} (drawing : LabelledDrawing Complex p p') :=
  drawing.interpret.eval.toLinearMap

abbrev basis {H : Subgroup U} (l : ConjEmbedding T H) (x : H) :
    (((Word.up a).tensor ((Word.down l).tensor (Word.up l))).basis.carrier →₀ Complex) :=
  Finsupp.single (Biset.pair (Biset.induction a) ((Word.down l).tensor (Word.up l)).basis
    (1 : T) (mixedPair l l x)) (1 : Complex)

abbrev output (e : ConjEmbedding T E) (p : (targetPair e).basis.carrier) :
    ((targetPair e).tensor (.up e)).basis.carrier :=
  (targetPair e).basis.pair (Word.up e).basis p (1 : E)

abbrev fiber (u : ConjEmbedding T B) (w : ConjEmbedding E B) (e : ConjEmbedding T E) (z : B) :=
  ∑ p ∈ (finite_q u w e z).toFinset, Finsupp.single (output e p) (1 : Complex)

abbrev native (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E) (r : D) (s : E) :
    LabelledDrawing Complex (((Word.up a).tensor (.down b)).tensor (.up b))
      ((targetPair e).tensor (.up e)) :=
  .vertical
    (.horizontal (.mixedMultiplication u v a b [(1, lo u v b)]) (drawId (.up b)))
    (.vertical (.ordinary (.associate (.down u) (.up v) (.up b)))
      (.vertical (.horizontal (drawId (.down u)) (.parallelUp v b w e [(1, mid v w b e r s)]))
        (.vertical (.ordinary (.unassociate (.down u) (.up w) (.up e)))
          (.horizontal (.compactProjection u w a e [(1, ⟨hi u w e, finite_left u w e⟩)])
            (drawId (.up e))))))

abbrev start (b : ConjEmbedding T D) := (Diagram.unassociate (R := Complex) (.up a) (.down b) (.up b)).eval.toLinearMap
abbrev finish (e : ConjEmbedding T E) := (Diagram.associate (R := Complex) (.up a) (.down e) (.up e)).eval.toLinearMap

theorem native_column (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E)
    (r x : D) (s : E) :
    ev (native u v w b e r s) (start b (basis b x)) =
      fiber u w e (v.toHom x * ((v.toHom r)⁻¹ * w.toHom s)) := by
  let p := Word.up (a (U := U))
  let q' := Word.down b
  let t := Word.up b
  have hin := Diagram.eval_unassociate_single (R := Complex) p q' t (1 : T) x (1 : D) 1
  change ev (native u v w b e r s)
    ((Diagram.unassociate (R := Complex) p q' t).eval.toLinearMap
      (Finsupp.single (p.basis.pair (q'.basis.tensor t.basis) (1 : T)
        (q'.basis.pair t.basis x (1 : D))) 1)) = _
  rw [hin]
  have h := ((EvaluationWithOneProjection a b b a e e).1 u v w).1
    (lo u v b) (mid v w b e r s) (hi u w e) (finite_q u w e) 1 x
  change ev (native u v w b e r s)
    (Finsupp.single ((p.basis.tensor q'.basis).pair t.basis
      (p.basis.pair q'.basis (1 : T) x) (1 : D)) 1) =
    fiber u w e (u.toHom 1 * (lo u v b).element * v.toHom x * (mid v w b e r s).element) at h
  simpa only [show (lo u v b).element = 1 from rfl,
    show (mid v w b e r s).element = (v.toHom r)⁻¹ * w.toHom s from rfl,
    map_one, one_mul] using h

theorem left_framed (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E)
    (r x : D) (s : E) :
    ev (left u v w b e r s) (basis b x) =
      finish e (fiber u w e (v.toHom x * ((v.toHom r)⁻¹ * w.toHom s))) := by
  change finish e (ev (native u v w b e r s) (start b (basis b x))) = _
  rw [native_column]

theorem fiber_finset (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (e : ConjEmbedding T E) (hDE : D ⊓ E = ⊥) (hv : ∀ z : D, (v.toHom z : U) = z)
    (hw : ∀ z : E, (w.toHom z : U) = z) (r x : D) (s : E) :
    let z := v.toHom x * ((v.toHom r)⁻¹ * w.toHom s)
    (finite_q u w e z).toFinset =
      @ite _ (x = r) (Classical.propDecidable (x = r))
        ({targetRep e s} : Finset _) ∅ := by
  classical
  dsimp only
  ext p
  obtain ⟨y, rfl⟩ := targetRep_surj e p
  rw [Set.Finite.mem_toFinset]
  change q u w e (targetRep e y) = _ ↔ _
  rw [q_rep, matrix_eq v w hDE hv hw]
  by_cases h : x = r
  · simp only [h, ite_eq_left, Finset.mem_singleton, true_and]
    constructor
    · rintro rfl
      rfl
    · intro he'
      apply w.injective
      calc
        w.toHom y = q u w e (targetRep e y) := (q_rep u w e y).symm
        _ = q u w e (targetRep e s) := congrArg (q u w e) he'
        _ = w.toHom s := q_rep u w e s
  · simp [h]

theorem finish_rep (e : ConjEmbedding T E) (s : E) :
    finish e (Finsupp.single (output e (targetRep e s)) 1) = basis e s := by
  exact Diagram.eval_associate_single (R := Complex) (.up a) (.down e) (.up e)
    (1 : T) s (1 : E) 1

theorem left_column (u : ConjEmbedding T B) (v : ConjEmbedding D B) (w : ConjEmbedding E B)
    (b : ConjEmbedding T D) (e : ConjEmbedding T E)
    (hDE : D ⊓ E = ⊥) (hv : ∀ z : D, (v.toHom z : U) = z)
    (hw : ∀ z : E, (w.toHom z : U) = z) (r x : D) (s : E) :
    ev (left u v w b e r s) (basis b x) =
      @ite _ (x = r) (Classical.propDecidable (x = r)) (basis e s) 0 := by
  classical
  rw [left_framed]
  unfold fiber
  rw [fiber_finset u v w e hDE hv hw]
  by_cases h : x = r
  · rw [ite_eq_left h, ite_eq_left h, Finset.sum_singleton, finish_rep]
  · rw [ite_eq_right h, ite_eq_right h, Finset.sum_empty, map_zero]

#print axioms OverlapLeft.left_column

end
end OverlapLeft
