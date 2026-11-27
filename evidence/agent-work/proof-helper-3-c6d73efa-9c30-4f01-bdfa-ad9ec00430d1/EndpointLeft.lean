import Proofs.EvaluationWithOneProjection
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map

namespace OverlapBlocks

variable {U : Type} [Group U] (ambient : U →* Equiv.Perm Nat)

private theorem fixes {a b : Nat} (swap : U) (hswap : ambient swap = Equiv.swap a b)
    {x : U} (hx : x ∈ Subgroup.closure {swap}) {i : Nat} (hia : i ≠ a) (hib : i ≠ b) :
    ambient x i = i := by
  let fix := Subgroup.comap ambient (MulAction.stabilizer (Equiv.Perm Nat) i)
  have hle : Subgroup.closure {swap} ≤ fix := by
    apply (Subgroup.closure_le fix).2
    apply Set.singleton_subset_iff.mpr
    change ambient swap i = i
    rw [hswap, Equiv.swap_apply_of_ne_of_ne hia hib]
  exact hle hx

theorem overlap_inf_bot (hinj : Function.Injective ambient) (swap12 swap23 : U)
    (h12 : ambient swap12 = Equiv.swap 1 2) (h23 : ambient swap23 = Equiv.swap 2 3) :
    Subgroup.closure {swap12} ⊓ Subgroup.closure {swap23} = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hx12, hx23⟩ := hx
  apply Subgroup.mem_bot.mpr
  apply hinj
  rw [map_one]
  apply Equiv.ext
  have hfix : ∀ i : Nat, i ≠ 2 → ambient x i = i := by
    intro i hi
    by_cases h1 : i = 1
    · subst i
      exact fixes ambient swap23 h23 hx23 (by decide) (by decide)
    · exact fixes ambient swap12 h12 hx12 h1 hi
  intro i
  change ambient x i = i
  by_cases hi : i = 2
  · subst i
    by_contra hn
    exact hn ((ambient x).injective (hfix _ hn))
  · exact hfix i hi

end OverlapBlocks

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


end
end OverlapLeft
set_option maxHeartbeats 2000000 in
theorem overlap_exact_left : (
let P := Equiv.Perm Nat
let finitary := Subgroup.closure {σ : P | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let T : Subgroup U := ⊥
let swap := fun (i j : Nat) (hij : i ≠ j) =>
  (⟨Equiv.swap i j, Subgroup.subset_closure ⟨i, j, hij, rfl⟩⟩ : U)
let swap12 := swap 1 2 (by decide)
let swap23 := swap 2 3 (by decide)
let D : Subgroup U := Subgroup.closure {swap12}
let E : Subgroup U := Subgroup.closure {swap23}
let points : Finset Nat := {1, 2, 3}
let extend := Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ points)
let B : Subgroup U := Subgroup.comap (Subgroup.subtype finitary) (MonoidHom.range extend)
let includeConj := fun {H K : Subgroup U} (h : H ≤ K) =>
  (⟨Subgroup.inclusion h, ⟨1, fun x => by simp⟩⟩ : MackeyDiagrams.ConjEmbedding H K)
let a := MackeyDiagrams.ConjEmbedding.id T
let b := includeConj (show T ≤ D from bot_le)
let e := includeConj (show T ≤ E from bot_le)
let u := includeConj (show T ≤ B from bot_le)
let v := includeConj (show D ≤ B by
  apply (Subgroup.closure_le B).mpr
  apply Set.singleton_subset_iff.mpr
  change ∃ p, extend p = Equiv.swap 1 2
  exact ⟨Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩)
let w := includeConj (show E ≤ B by
  apply (Subgroup.closure_le B).mpr
  apply Set.singleton_subset_iff.mpr
  change ∃ p, extend p = Equiv.swap 2 3
  exact ⟨Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩)
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let straight := fun {K L : Subgroup U} (p : MackeyDiagrams.Word K L) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let bottom := tensor (up a) (tensor (down b) (up b))
let top := tensor (up a) (tensor (down e) (up e))
let atLeft := fun {K J J' L M : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J L}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' L}
    (tail : MackeyDiagrams.Word L M)
    (crossing : MackeyDiagrams.LabelledDrawing Complex (tensor p q) (tensor p' q')) =>
  vertical (ordinary (MackeyDiagrams.Diagram.unassociate p q tail))
    (vertical (horizontal crossing (straight tail))
      (ordinary (MackeyDiagrams.Diagram.associate p' q' tail)))
let dot := fun {H : Subgroup U} {α β : MackeyDiagrams.ConjEmbedding T H} (x : H) =>
  (⟨x, fun y => by
    have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.mp y.property)
    simp [hy]⟩ : MackeyDiagrams.Dot α β)
let lowerLeft : MackeyDiagrams.Dot (comp u a) (comp v b) := dot 1
let upperLeft : MackeyDiagrams.Dot (comp u a) (comp w e) := dot 1
let middleRight : MackeyDiagrams.Dot (comp a a) (comp a a) := dot 1
let finiteFibers := fun {X Y : Type} (q : X → Y) => ∀ z, Set.Finite {y | q y = z}
let basisVector := fun {H : Subgroup U} (h : MackeyDiagrams.ConjEmbedding T H) (x : H) =>
  Finsupp.single
    (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
      (MackeyDiagrams.Word.basis (tensor (down h) (up h))) 1
      (MackeyDiagrams.Generator.mixedPair h h x)) (1 : Complex)
∀ (r : D) (s : E),
  let middleLeft : MackeyDiagrams.Dot (comp v b) (comp w e) :=
    dot ((MackeyDiagrams.ConjEmbedding.toHom v r)⁻¹ * MackeyDiagrams.ConjEmbedding.toHom w s)
  ∃ (hLeft : finiteFibers
        (MackeyDiagrams.Generator.mixedMultiplicationBasis u w a e upperLeft)),
    let left : MackeyDiagrams.LabelledDrawing Complex bottom top :=
      vertical
        (atLeft (up b) (MackeyDiagrams.LabelledDrawing.mixedMultiplication u v a b
          [(1, lowerLeft)]))
        (vertical
          (horizontal (straight (down u))
            (MackeyDiagrams.LabelledDrawing.parallelUp v b w e [(1, middleLeft)]))
          (atLeft (up e) (MackeyDiagrams.LabelledDrawing.compactProjection u w a e
            [(1, ⟨upperLeft, hLeft⟩)])))
    let evaluate := fun (drawing : MackeyDiagrams.LabelledDrawing Complex bottom top) =>
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
    ∀ x : D,
      MackeyDiagrams.Biset.Hom.toLinearMap (evaluate left) (basisVector b x) =
        @ite _ (x = r) (Classical.propDecidable (x = r)) (basisVector e s) 0
) := by
  -- Keep the endpoint's lets available so the concrete permutation data
  -- does not enter elaboration of the symbolic diagram computation.
  intro P finitary U T swap swap12 swap23 D E points extend B includeConj
    a b e u v w up down tensor comp vertical horizontal ordinary straight bottom top
    atLeft dot lowerLeft upperLeft middleRight finiteFibers basisVector
    r s middleLeft
  have hinter : D ⊓ E = ⊥ :=
    OverlapBlocks.overlap_inf_bot (Subgroup.subtype finitary) Subtype.val_injective
      swap12 swap23 rfl rfl
  refine ⟨OverlapLeft.finite_left u w e, ?_⟩
  intro left evaluate x
  exact OverlapLeft.left_column u v w b e hinter (fun _ => rfl) (fun _ => rfl) r x s

#print axioms overlap_exact_left
