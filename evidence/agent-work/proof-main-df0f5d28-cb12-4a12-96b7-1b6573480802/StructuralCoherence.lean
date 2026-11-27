import MackeyDiagrams.PlanarShape
import MackeyDiagrams.BoundaryEvaluation

namespace DotSlideStructuralCoherence

open MackeyDiagrams

universe u v

section Basis

variable {K H J F : Type u} [Group K] [Group H] [Group J] [Group F]
variable {R : Type v} [CommSemiring R]
variable {X X' X'' : Biset K H} {Y Y' : Biset H J}

/-- Equivariant maps taking each basis element to a basis element. -/
private structure BasisMap (X X' : Biset K H) where
  run : X.carrier → X'.carrier
  commute : ∀ g x, run (X.act g x) = X'.act g (run x)

namespace BasisMap

private noncomputable def linear (f : BasisMap X X') : Biset.Hom R X X' :=
  Biset.Hom.ofFunction f.run f.commute

private theorem linear_single (f : BasisMap X X') (x : X.carrier) (c : R) :
    (f.linear (R := R)).toLinearMap (Finsupp.single x c) = Finsupp.single (f.run x) c :=
  Biset.Hom.ofFunction_single _ _ _ _

private def ident (X : Biset K H) : BasisMap X X := ⟨id, fun _ _ => rfl⟩

private def vert (f : BasisMap X X') (g : BasisMap X' X'') : BasisMap X X'' :=
  ⟨g.run ∘ f.run, fun k x => by simp only [Function.comp_apply, f.commute, g.commute]⟩

private def hor (f : BasisMap X X') (g : BasisMap Y Y') :
    BasisMap (X.tensor Y) (X'.tensor Y') where
  run := Quotient.lift (fun z => X'.pair Y' (f.run z.1) (g.run z.2)) (by
    intro x y h
    obtain ⟨k, hk, hk'⟩ := h
    rw [← hk, ← hk', f.commute, g.commute, Biset.pair_orbit])
  commute := by
    intro k z
    refine Quotient.inductionOn z ?_
    rintro ⟨x,y⟩
    change X'.pair Y' (f.run (X.act (k.1,1) x)) (g.run (Y.act (1,k.2) y)) =
      X'.pair Y' (X'.act (k.1,1) (f.run x)) (Y'.act (1,k.2) (g.run y))
    rw [f.commute, g.commute]

private theorem linear_ident (X : Biset K H) : ((ident X).linear (R := R)) = Biset.Hom.id X := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  exact linear_single _ _ _

private theorem linear_vert (f : BasisMap X X') (g : BasisMap X' X'') :
    ((f.vert g).linear (R := R)) = f.linear.vertical g.linear := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  change ((f.vert g).linear (R := R)).toLinearMap (Finsupp.single x c) =
    g.linear.toLinearMap (f.linear.toLinearMap (Finsupp.single x c))
  rw [linear_single, linear_single, linear_single]
  rfl

private theorem linear_hor (f : BasisMap X X') (g : BasisMap Y Y') :
    ((f.hor g).linear (R := R)) = f.linear.horizontal g.linear := by
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro z c
  refine Quotient.inductionOn z ?_
  rintro ⟨x,y⟩
  change ((f.hor g).linear (R := R)).toLinearMap (Finsupp.single (X.pair Y x y) c) =
    (f.linear.horizontal g.linear).toLinearMap (Finsupp.single (X.pair Y x y) c)
  rw [linear_single, Biset.Hom.horizontal_single, linear_single, linear_single,
    Biset.pairLinear_single, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

private def assoc (X : Biset K H) (Y : Biset H J) (Z : Biset J F) :
    BasisMap ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z)) :=
  ⟨Biset.associateBasis X Y Z, by
    intro g w
    refine Quotient.inductionOn w (fun ⟨xy,z⟩ => ?_)
    exact Quotient.inductionOn xy (fun _ => rfl)⟩

private def left (X : Biset K H) : BasisMap ((Biset.regular K).tensor X) X :=
  ⟨Biset.leftUnitBasis X, by
    intro g z
    refine Quotient.inductionOn z ?_
    rintro ⟨k,x⟩
    change X.act (g.1 * k * (1 : K)⁻¹, 1) (X.act (1,g.2) x) =
      X.act g (X.act (k,1) x)
    rw [← X.mul_act, ← X.mul_act]
    rcases g with ⟨a,b⟩
    simp⟩

private def insRight (X : Biset K H) : BasisMap X (X.tensor (Biset.regular H)) :=
  ⟨fun x => X.pair (Biset.regular H) x 1, by
    intro g x
    change X.pair (Biset.regular H) (X.act g x) 1 =
      X.pair (Biset.regular H) (X.act (g.1,1) x) (1 * 1 * g.2⁻¹)
    have e := X.pair_balance (Biset.regular H) g.2⁻¹ (X.act (g.1,1) x) 1
    rw [← X.mul_act] at e
    rcases g with ⟨k,h⟩
    simpa [Biset.regular] using e⟩

end BasisMap

end Basis


section Words

variable {U : Type u} [Group U] {A B C D : Subgroup U}
variable {R : Type v} [CommSemiring R]

private def appendBasis : {A B C : Subgroup U} →
    (a : Boundary A B) → (b : Boundary B C) →
    BasisMap (a.word.basis.tensor b.word.basis) (a.append b).word.basis
  | _, _, _, .empty _, b => BasisMap.left b.word.basis
  | _, _, _, .cons s t, b => (BasisMap.assoc s.word.basis t.word.basis b.word.basis).vert
      ((BasisMap.ident s.word.basis).hor (appendBasis t b))

private def join (a : Boundary A B) (b : Boundary B C)
    (x : a.word.basis.carrier) (y : b.word.basis.carrier) :
    (a.append b).word.basis.carrier :=
  (appendBasis a b).run (a.word.basis.pair b.word.basis x y)

private theorem join_cons (s : Strand A B) (t : Boundary B C) (b : Boundary C D)
    (x : s.word.basis.carrier) (y : t.word.basis.carrier) (z : b.word.basis.carrier) :
    join (.cons s t) b (s.word.basis.pair t.word.basis x y) z =
      s.word.basis.pair (t.append b).word.basis x (join t b y z) := rfl

private theorem join_left_action (a : Boundary A B) (b : Boundary B C)
    (g : A) (x : a.word.basis.carrier) (y : b.word.basis.carrier) :
    join a b (a.word.basis.act (g,1) x) y =
      (a.append b).word.basis.act (g,1) (join a b x y) := by
  have h := (appendBasis a b).commute (g,1) (a.word.basis.pair b.word.basis x y)
  rw [Biset.act_pair] at h
  change (appendBasis a b).run
    (a.word.basis.pair b.word.basis (a.word.basis.act (g,1) x) (b.word.basis.act 1 y)) = _ at h
  rwa [Biset.one_act] at h

private def reindex {a b : Boundary A B} (h : a = b) :
    a.word.basis.carrier → b.word.basis.carrier :=
  fun x => h ▸ x

private theorem reindex_cons (s : Strand A B) {a b : Boundary B C}
    (h : a = b) (x : s.word.basis.carrier) (y : a.word.basis.carrier) :
    reindex (congrArg (Boundary.cons s) h) (s.word.basis.pair a.word.basis x y) =
      s.word.basis.pair b.word.basis x (reindex h y) := by
  cases h
  rfl

private theorem join_assoc (a : Boundary A B) (b : Boundary B C) (c : Boundary C D)
    (x : a.word.basis.carrier) (y : b.word.basis.carrier) (z : c.word.basis.carrier) :
    reindex (Boundary.append_assoc a b c) (join (a.append b) c (join a b x y) z) =
      join a (b.append c) x (join b c y z) := by
  induction a with
  | empty => exact join_left_action b c x y z
  | cons s t ih =>
    refine Quotient.inductionOn x ?_
    rintro ⟨x',x''⟩
    change reindex (congrArg (Boundary.cons s) (Boundary.append_assoc t b c))
      (join (.cons s (t.append b)) c (join (.cons s t) b (s.word.basis.pair t.word.basis x' x'') y) z) =
      join (.cons s t) (b.append c) (s.word.basis.pair t.word.basis x' x'') (join b c y z)
    simp only [join_cons, reindex_cons s (Boundary.append_assoc t b c), ih]
    rfl

private theorem join_empty (a : Boundary A B) (x : a.word.basis.carrier) (y : B) :
    reindex (Boundary.append_empty a) (join a (.empty B) x y) =
      a.word.basis.act (1,y⁻¹) x := by
  induction a with
  | @empty K =>
    change ↥K at x
    change x * y * (1 : K)⁻¹ = 1 * x * (y⁻¹)⁻¹
    simp
  | @cons K H J s t ih =>
    refine Quotient.inductionOn x ?_
    rintro ⟨x',x''⟩
    change reindex (congrArg (Boundary.cons s) (Boundary.append_empty t))
      (join (.cons s t) (.empty J) (s.word.basis.pair t.word.basis x' x'') y) =
      (s.word.basis.tensor t.word.basis).act (1,y⁻¹) (s.word.basis.pair t.word.basis x' x'')
    have step := congrArg (reindex (congrArg (Boundary.cons s) (Boundary.append_empty t)))
      (join_cons s t (.empty J) x' x'' y)
    refine step.trans ((reindex_cons s (Boundary.append_empty t) x' _).trans ?_)
    rw [ih, Biset.act_pair]
    change s.word.basis.pair t.word.basis x' _ =
      s.word.basis.pair t.word.basis (s.word.basis.act 1 x') _
    rw [Biset.one_act]

private theorem eval_appendBasis (a : Boundary A B) (b : Boundary B C) :
    ((appendBasis a b).linear (R := R)) = (a.appendDiagram b).eval := by
  induction a with
  | empty => rfl
  | cons s t ih =>
    change (((BasisMap.assoc s.word.basis t.word.basis b.word.basis).vert
      ((BasisMap.ident s.word.basis).hor (appendBasis t b))).linear (R := R)) =
      (Biset.associate _ _ _ R).vertical ((Biset.Hom.id _).horizontal (t.appendDiagram b).eval)
    rw [BasisMap.linear_vert, BasisMap.linear_hor, BasisMap.linear_ident, ih]
    rfl

private def normBasis : {A B : Subgroup U} →
    (p : Word A B) → BasisMap p.basis p.boundary.word.basis
  | _, _, .empty A => BasisMap.ident (Biset.regular A)
  | _, _, .up a => BasisMap.insRight (Biset.induction a)
  | _, _, .down a => BasisMap.insRight (Biset.restriction a)
  | _, _, .tensor p q => ((normBasis p).hor (normBasis q)).vert (appendBasis p.boundary q.boundary)

private theorem eval_normBasis (p : Word A B) :
    ((normBasis p).linear (R := R)) = (p.reorderToBoundary (R := R)).eval := by
  induction p with
  | empty => exact BasisMap.linear_ident (R := R) _
  | up => rfl
  | down => rfl
  | tensor p q ihp ihq =>
    change ((((normBasis p).hor (normBasis q)).vert
      (appendBasis p.boundary q.boundary)).linear (R := R)) =
      ((p.reorderToBoundary (R := R)).eval.horizontal (q.reorderToBoundary (R := R)).eval).vertical
        (p.boundary.appendDiagram q.boundary).eval
    rw [BasisMap.linear_vert, BasisMap.linear_hor, ihp, ihq, eval_appendBasis]


/-- Transport the target of a map across equality of ordered strand data. -/
def transport {X : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X a.word.basis) : Biset.Hom R X b.word.basis :=
  h ▸ f

private theorem transport_single {X : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X a.word.basis) (x : X.carrier) (y : a.word.basis.carrier) (c : R)
    (hf : f.toLinearMap (Finsupp.single x c) = Finsupp.single y c) :
    (transport h f).toLinearMap (Finsupp.single x c) = Finsupp.single (reindex h y) c := by
  cases h
  exact hf

private theorem transport_trans {X : Biset A B} {a b c : Boundary A B}
    (h : a = b) (k : b = c) (f : Biset.Hom R X a.word.basis) :
    transport (h.trans k) f = transport k (transport h f) := by
  cases h
  cases k
  rfl

private theorem transport_vertical {X Y : Biset A B} {a b : Boundary A B} (h : a = b)
    (f : Biset.Hom R X Y) (g : Biset.Hom R Y a.word.basis) :
    transport h (f.vertical g) = f.vertical (transport h g) := by
  cases h
  rfl

private theorem transport_append {X : Biset A B} {Y : Biset B C}
    {a a' : Boundary A B} {b b' : Boundary B C} (ha : a = a') (hb : b = b')
    (f : Biset.Hom R X a.word.basis) (g : Biset.Hom R Y b.word.basis) :
    transport (congrArg₂ Boundary.append ha hb) ((f.horizontal g).vertical (a.appendDiagram b).eval) =
      ((transport ha f).horizontal (transport hb g)).vertical (a'.appendDiagram b').eval := by
  cases ha
  cases hb
  rfl

private def Coherent {p q : Word A B} (f : Biset.Hom R p.basis q.basis) : Prop :=
  ∃ h : p.boundary = q.boundary, transport h (p.reorderToBoundary (R := R)).eval =
    f.vertical (q.reorderToBoundary (R := R)).eval

private theorem coherent_of_single {p q : Word A B} (f : Biset.Hom R p.basis q.basis)
    (h : p.boundary = q.boundary) (g : p.basis.carrier → q.basis.carrier)
    (hf : ∀ x c, f.toLinearMap (Finsupp.single x c) = Finsupp.single (g x) c)
    (hg : ∀ x, reindex h ((normBasis p).run x) = (normBasis q).run (g x)) :
    Coherent (p := p) (q := q) f := by
  refine ⟨h, ?_⟩
  rw [← eval_normBasis p, ← eval_normBasis q]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x c
  change (transport h (normBasis p).linear).toLinearMap (Finsupp.single x c) =
    (normBasis q).linear.toLinearMap (f.toLinearMap (Finsupp.single x c))
  rw [transport_single h _ x _ c (BasisMap.linear_single _ _ _), hf, BasisMap.linear_single, hg]

private theorem coherent_id (p : Word A B) : Coherent (p := p) (q := p) (Biset.Hom.id (R := R) _) :=
  ⟨rfl, rfl⟩

private theorem coherent_vertical {p q t : Word A B}
    {f : Biset.Hom R p.basis q.basis} {g : Biset.Hom R q.basis t.basis}
    (hf : Coherent (p := p) (q := q) f) (hg : Coherent (p := q) (q := t) g) :
    Coherent (p := p) (q := t) (f.vertical g) := by
  obtain ⟨h, hf⟩ := hf
  obtain ⟨k, hg⟩ := hg
  exact ⟨h.trans k, by rw [transport_trans h k, hf, transport_vertical k, hg, Biset.Hom.vertical_assoc]⟩

private theorem coherent_horizontal {p p' : Word A B} {q q' : Word B C}
    {f : Biset.Hom R p.basis p'.basis} {g : Biset.Hom R q.basis q'.basis}
    (hf : Coherent (p := p) (q := p') f) (hg : Coherent (p := q) (q := q') g) :
    Coherent (p := p.tensor q) (q := p'.tensor q') (f.horizontal g) := by
  obtain ⟨h, hf⟩ := hf
  obtain ⟨k, hg⟩ := hg
  refine ⟨congrArg₂ Boundary.append h k, ?_⟩
  change transport (congrArg₂ Boundary.append h k)
    (((p.reorderToBoundary (R := R)).eval.horizontal (q.reorderToBoundary (R := R)).eval).vertical
      (p.boundary.appendDiagram q.boundary).eval) =
    (f.horizontal g).vertical
      (((p'.reorderToBoundary (R := R)).eval.horizontal (q'.reorderToBoundary (R := R)).eval).vertical
        (p'.boundary.appendDiagram q'.boundary).eval)
  rw [transport_append h k, hf, hg, ← Biset.Hom.horizontal_vertical, Biset.Hom.vertical_assoc]

private theorem coherent_inverse {p q : Word A B}
    {f : Biset.Hom R p.basis q.basis} {g : Biset.Hom R q.basis p.basis}
    (hf : Coherent (p := p) (q := q) f) (hg : g.vertical f = Biset.Hom.id _) :
    Coherent (p := q) (q := p) g := by
  obtain ⟨h, hf⟩ := hf
  have hc := congrArg (transport h.symm) hf
  rw [← transport_trans h h.symm] at hc
  change (p.reorderToBoundary (R := R)).eval = transport h.symm
    (f.vertical (q.reorderToBoundary (R := R)).eval) at hc
  refine ⟨h.symm, ?_⟩
  rw [hc, transport_vertical h.symm, ← Biset.Hom.vertical_assoc, hg, Biset.Hom.id_vertical]

private theorem coherent_associate (p : Word A B) (q : Word B C) (t : Word C D) :
    Coherent (p := (p.tensor q).tensor t) (q := p.tensor (q.tensor t))
      (Diagram.associate (R := R) p q t).eval := by
  refine coherent_of_single _ (Word.boundary_associate p q t)
    (Biset.associateBasis p.basis q.basis t.basis) ?_ ?_
  · intro x c
    change (Biset.associate p.basis q.basis t.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.associate, Biset.Hom.ofFunction_single]
  · intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨xy,z⟩
    refine Quotient.inductionOn xy ?_
    rintro ⟨x,y⟩
    change reindex (Boundary.append_assoc p.boundary q.boundary t.boundary)
      ((normBasis ((p.tensor q).tensor t)).run ((p.basis.tensor q.basis).pair t.basis (p.basis.pair q.basis x y) z)) =
      (normBasis (p.tensor (q.tensor t))).run (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z))
    exact join_assoc p.boundary q.boundary t.boundary _ _ _

private theorem coherent_leftUnit (p : Word A B) :
    Coherent (p := (Word.empty A).tensor p) (q := p) (Diagram.leftUnit (R := R) p).eval := by
  refine coherent_of_single _ (Word.boundary_leftUnit p) (Biset.leftUnitBasis p.basis) ?_ ?_
  · intro x c
    change (Biset.leftUnit p.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.leftUnit, Biset.Hom.ofFunction_single]
  · intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨k,x⟩
    change p.boundary.word.basis.act (k,1) ((normBasis p).run x) =
      (normBasis p).run (p.basis.act (k,1) x)
    exact ((normBasis p).commute _ _).symm

private theorem coherent_rightUnit (p : Word A B) :
    Coherent (p := p.tensor (.empty B)) (q := p) (Diagram.rightUnit (R := R) p).eval := by
  refine coherent_of_single _ (Word.boundary_rightUnit p) (Biset.rightUnitBasis p.basis) ?_ ?_
  · intro x c
    change (Biset.rightUnit p.basis R).toLinearMap (Finsupp.single x c) = _
    rw [Biset.rightUnit, Biset.Hom.ofFunction_single]
  · intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨x,k⟩
    change reindex (Boundary.append_empty p.boundary) (join p.boundary (.empty B) ((normBasis p).run x) k) =
      (normBasis p).run (p.basis.act (1,k⁻¹) x)
    exact (join_empty p.boundary _ k).trans ((normBasis p).commute _ _).symm

end Words

end DotSlideStructuralCoherence
