import MackeyDiagrams
import Proofs.MixedCrossingFiberMaps

set_option maxHeartbeats 2000000

namespace MixedCrossingFiniteFiberConventionAux

open MackeyDiagrams

variable {U : Type*} [Group U]

private theorem embedding_eq_of_rep {A B : Subgroup U} (e : ConjEmbedding A B) (p : U)
    (hp : ∀ x : A, (e.toHom x : U) = p * (x : U) * p⁻¹) :
    e = ConjEmbedding.ofConjugator p (fun x => hp x ▸ (e.toHom x).property) := by
  apply ConjEmbedding.ext
  exact MonoidHom.ext (fun x => Subtype.ext (hp x))

private theorem representativeCoset {A B : Subgroup U} (e : ConjEmbedding A B) (p : U)
    (hp : ∀ x : A, (e.toHom x : U) = MulAut.conj p (x : U)) :
    {q : U | ∀ x : A, (e.toHom x : U) = MulAut.conj q (x : U)} =
      {q : U | p⁻¹ * q ∈ Subgroup.centralizer (A : Set U)} := by
  ext q
  change (∀ x : A, (e.toHom x : U) = q * (x : U) * q⁻¹) ↔
    p⁻¹ * q ∈ Subgroup.centralizer (A : Set U)
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hq x hx
    have he := (hp ⟨x, hx⟩).symm.trans (hq ⟨x, hx⟩)
    change p * x * p⁻¹ = q * x * q⁻¹ at he
    calc
      x * (p⁻¹ * q) = p⁻¹ * (p * x * p⁻¹) * q := by group
      _ = p⁻¹ * (q * x * q⁻¹) * q := by rw [he]
      _ = (p⁻¹ * q) * x := by group
  · intro h x
    calc
      (e.toHom x : U) = p * (x : U) * p⁻¹ := hp x
      _ = p * ((x : U) * (p⁻¹ * q)) * q⁻¹ := by group
      _ = p * ((p⁻¹ * q) * (x : U)) * q⁻¹ := by rw [h _ x.property]
      _ = q * (x : U) * q⁻¹ := by group

section
variable {K H G L : Subgroup U}
variable (α : ConjEmbedding K G) (β : ConjEmbedding H G)
variable (a : ConjEmbedding L K) (b : ConjEmbedding L H)
variable (d : Dot (α.comp a) (β.comp b))

private abbrev qBasis := Generator.mixedMultiplicationBasis α β a b d
private abbrev q (w : ((Word.up a).tensor (.down b)).basis.carrier) : G :=
  Generator.mixedProduct α β (qBasis α β a b d w)
private abbrev traceInput (z : G) (t : H) :=
  z * (β.toHom t)⁻¹ * d.element⁻¹

private theorem groupFiber (z : G) :
    {w | qBasis α β a b d w = Generator.mixedPair α β z} = {w | q α β a b d w = z} := by
  ext w
  change qBasis α β a b d w = Generator.mixedPair α β z ↔ q α β a b d w = z
  constructor
  · intro hw
    show Generator.mixedProduct α β (qBasis α β a b d w) = z
    rw [hw, Generator.mixedProduct_mixedPair]
  · intro hw
    apply (Generator.mixedEquiv α β).injective
    change q α β a b d w = Generator.mixedProduct α β (Generator.mixedPair α β z)
    rw [Generator.mixedProduct_mixedPair, hw]

private abbrev Columns : Prop :=
    (∀ (k : K) (h : H),
      q α β a b d ((Biset.induction a).pair (Biset.restriction b) k h) =
        α.toHom k * d.element * β.toHom h) ∧
    (∀ w,
      (Diagram.mixedMultiplication (R := Complex) α β a b d).eval.toLinearMap
          (Finsupp.single w 1) =
        Finsupp.single (Generator.mixedPair α β (q α β a b d w)) 1) ∧
    (∀ hf : ∀ z, Set.Finite {w | qBasis α β a b d w = z},
      let diagram := Diagram.mixedProjection (R := Complex) α β a b d hf
      let valueAt := fun z : G => diagram.eval.toLinearMap
        (Finsupp.single (Generator.mixedPair α β z) 1)
      (∀ z : G, valueAt z = Finset.sum (hf (Generator.mixedPair α β z)).toFinset
        (fun w => Finsupp.single w 1)) ∧
      (∀ (T : Set H) (_ : ∀ h : H, ∃! t : H, t ∈ T ∧ h * t⁻¹ ∈ b.toHom.range)
        (z : G),
        ∃ hs : Set.Finite {t : H | t ∈ T ∧ traceInput α β a b d z t ∈ α.toHom.range},
          valueAt z = Finset.sum hs.toFinset (fun t =>
            Biset.pairLinear Complex (Biset.induction a) (Biset.restriction b)
              (Generator.traceBasis Complex α (traceInput α β a b d z t)) (Finsupp.single t 1))))

/- Article §6.2, finite-fiber convention, invoking Proposition 5.1.
   The portal supplies no numbered proof for this convention. The registered
   MixedCrossingFiberMaps works with representative conjugators and a section.
   The dot equation lets us pick a representative of the inner left embedding
   so that (p * s) * (r * t)⁻¹ is the given dot. This realizes the representative
   equation in the first paragraph of the proof of Proposition 5.1. The section
   exists for every double-coset quotient. The transversal for
   the trace formula is the one supplied by the endpoint. -/
private theorem singletonColumns : Columns α β a b d := by
  classical
  obtain ⟨p, hp⟩ := α.hasRepresentative
  obtain ⟨r, hr⟩ := β.hasRepresentative
  obtain ⟨t, ht⟩ := b.hasRepresentative
  let s : U := p⁻¹ * (d.element : U) * (r * t)
  have hs : ∀ x : L, (a.toHom x : U) = s * (x : U) * s⁻¹ := by
    intro x
    have hd := congrArg (fun y : G => (y : U)) (d.intertwines x)
    change (α.toHom (a.toHom x) : U) * (d.element : U) =
      (d.element : U) * (β.toHom (b.toHom x) : U) at hd
    rw [hp, hr, ht] at hd
    calc
      (a.toHom x : U) =
          p⁻¹ * ((p * (a.toHom x : U) * p⁻¹) * (d.element : U)) *
            (d.element : U)⁻¹ * p := by group
      _ = p⁻¹ * ((d.element : U) * (r * (t * (x : U) * t⁻¹) * r⁻¹)) *
            (d.element : U)⁻¹ * p := by rw [hd]
      _ = s * (x : U) * s⁻¹ := by dsimp [s]; group
  have hquot : (p * s) * (r * t)⁻¹ = (d.element : U) := by dsimp [s]; group
  have hdG : (p * s) * (r * t)⁻¹ ∈ G := hquot ▸ d.element.property
  have hpG : ∀ k : K, p * (k : U) * p⁻¹ ∈ G := fun k => hp k ▸ (α.toHom k).property
  have hrG : ∀ h : H, r * (h : U) * r⁻¹ ∈ G := fun h => hr h ▸ (β.toHom h).property
  have hsK : ∀ x : L, s * (x : U) * s⁻¹ ∈ K := fun x => hs x ▸ (a.toHom x).property
  have htH : ∀ x : L, t * (x : U) * t⁻¹ ∈ H := fun x => ht x ▸ (b.toHom x).property
  let eα := ConjEmbedding.ofConjugator p hpG
  let eβ := ConjEmbedding.ofConjugator r hrG
  let ea := ConjEmbedding.ofConjugator s hsK
  let eb := ConjEmbedding.ofConjugator t htH
  let e : Dot (eα.comp ea) (eβ.comp eb) :=
    Dot.ofRepresentatives (p * s) (r * t)
      (by intro x; change p * (s * (x : U) * s⁻¹) * p⁻¹ = _; group)
      (by intro x; change r * (t * (x : U) * t⁻¹) * r⁻¹ = _; group) hdG
  have supplied := MixedCrossingFiberMaps K H G L p r s t hpG hrG hsK htH hdG
    (fun j => j.out) DoubleCoset.out_eq'
  obtain ⟨_, hpair, hpush, _, _, _, _, _, _, hpull⟩ := supplied
  have transport (α' : ConjEmbedding K G) (β' : ConjEmbedding H G)
      (a' : ConjEmbedding L K) (b' : ConjEmbedding L H)
      (e' : Dot (α'.comp a') (β'.comp b'))
      (hα' : α = α') (hβ' : β = β') (ha' : a = a') (hb' : b = b')
      (he' : (e'.element : U) = (d.element : U))
      (columns : Columns α' β' a' b' e') : Columns α β a b d := by
    cases hα'
    cases hβ'
    cases ha'
    cases hb'
    have heq : e' = d := Dot.ext (Subtype.ext he')
    subst e'
    exact columns
  exact transport eα eβ ea eb e (embedding_eq_of_rep α p hp) (embedding_eq_of_rep β r hr)
    (embedding_eq_of_rep a s hs) (embedding_eq_of_rep b t ht) hquot
    ⟨hpair, hpush, hpull⟩

private theorem multiplyColumn (label : List (Complex × Dot (α.comp a) (β.comp b)))
    (w : ((Word.up a).tensor (.down b)).basis.carrier) :
    (LabelledDrawing.mixedMultiplication α β a b label).interpret.eval.toLinearMap
        (Finsupp.single w 1) =
      (label.map fun term => term.1 •
        Finsupp.single (qBasis α β a b term.2 w) 1).sum := by
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change term.1 • ((Generator.mixedMultiplication α β a b term.2 Complex).toLinearMap
    (Finsupp.single w 1)) = _
  rw [Generator.mixedMultiplication, Biset.Hom.ofFunction_single]

private theorem projectColumn (label : List (Complex × ProjectionDot.Mixed α β a b))
    (z : ((Word.down α).tensor (.up β)).basis.carrier) :
    (LabelledDrawing.compactProjection α β a b label).interpret.eval.toLinearMap
        (Finsupp.single z 1) =
      (label.map fun term => term.1 • Finset.sum (term.2.finite z).toFinset
        (fun w => Finsupp.single w 1)).sum := by
  unfold LabelledDrawing.interpret
  rw [ScopedDiagram.eval_linearCombination_apply, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  change term.1 • ((Generator.mixedProjection α β a b term.2.dot Complex
    term.2.finite).toLinearMap (Finsupp.single z 1)) = _
  rw [Generator.mixedProjection, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]

end
end MixedCrossingFiniteFiberConventionAux

theorem MixedCrossingFiniteFiberConvention : (
∀ {U : Type u} [Group U],
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let plain := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let Stage := fun {K H : Subgroup U} (p q : MackeyDiagrams.Word K H) =>
    Σ D : Type u, Σ valid : D → Prop,
      (x : Finsupp D Complex) → (∀ d ∈ Finsupp.support x, valid d) →
        MackeyDiagrams.LabelledDrawing Complex p q
  let place := fun {A B K H : Subgroup U}
      {p q : MackeyDiagrams.Word A B} {p' q' : MackeyDiagrams.Word K H}
      (stage : Stage p q)
      (frame : MackeyDiagrams.LabelledDrawing Complex p q →
        MackeyDiagrams.LabelledDrawing Complex p' q') =>
    (⟨stage.1, stage.2.1, fun x hx => frame (stage.2.2 x hx)⟩ : Stage p' q')
  let at₁ := fun {A B C : Subgroup U} {p q : MackeyDiagrams.Word A B}
      (stage : Stage p q) (spectator : MackeyDiagrams.Word B C) =>
    place stage (fun d => juxtapose d (plain (MackeyDiagrams.Diagram.id spectator)))
  let at₂ := fun {A B C D C' : Subgroup U}
      (spectator : MackeyDiagrams.Word A B)
      {p₁ : MackeyDiagrams.Word B C} {p₂ : MackeyDiagrams.Word C D}
      {q₁ : MackeyDiagrams.Word B C'} {q₂ : MackeyDiagrams.Word C' D}
      (stage : Stage (tensor p₁ p₂) (tensor q₁ q₂)) =>
    place stage (fun d => stack (plain (MackeyDiagrams.Diagram.associate spectator p₁ p₂))
      (stack (juxtapose (plain (MackeyDiagrams.Diagram.id spectator)) d)
        (plain (MackeyDiagrams.Diagram.unassociate spectator q₁ q₂))))
  let parallel := fun {P Q Q' S : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding Q P) (b : MackeyDiagrams.ConjEmbedding S Q)
      (a' : MackeyDiagrams.ConjEmbedding Q' P) (b' : MackeyDiagrams.ConjEmbedding S Q') =>
    (⟨MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a b)
        (MackeyDiagrams.ConjEmbedding.comp a' b'), fun _ => True,
      fun x _ => MackeyDiagrams.LabelledDrawing.parallelUp a b a' b'
        (MackeyDiagrams.DotLabel.terms x)⟩ :
      Stage (tensor (up a) (up b)) (tensor (up a') (up b')))
  let finiteFibers := fun {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H)
      (d : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b)) =>
    ∀ z : (MackeyDiagrams.Word.basis (tensor (down α) (up β))).carrier,
      Set.Finite {w | MackeyDiagrams.Generator.mixedMultiplicationBasis α β a b d w = z}
  let multiply := fun {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H) =>
    (⟨MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b), fun _ => True,
      fun x _ => MackeyDiagrams.LabelledDrawing.mixedMultiplication α β a b
        (MackeyDiagrams.DotLabel.terms x)⟩ :
      Stage (tensor (up a) (down b)) (tensor (down α) (up β)))
  let projectionTerms := fun {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b))
      (hx : ∀ d ∈ Finsupp.support x, finiteFibers α β a b d) =>
    (Finset.toList (Finset.attach (Finsupp.support x))).map fun d =>
      (x d.val, (⟨d.val, hx d.val d.property⟩ : MackeyDiagrams.ProjectionDot.Mixed α β a b))
  let project := fun {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H) =>
    (⟨MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b), finiteFibers α β a b,
      fun x hx => MackeyDiagrams.LabelledDrawing.compactProjection α β a b
        (projectionTerms α β a b x hx)⟩ :
      Stage (tensor (down α) (up β)) (tensor (up a) (down b)))
  let eval := fun {K H : Subgroup U} {p q : MackeyDiagrams.Word K H}
      (d : MackeyDiagrams.LabelledDrawing Complex p q) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret d)
  let planar := fun (bottom top : List Bool) (wiring : List MackeyDiagrams.PlanarEvent) =>
    (⟨bottom, top, Quotient.mk MackeyDiagrams.PlanarCode.setoid wiring⟩ :
      MackeyDiagrams.PlanarShape)
  let leftShape := fun (bottom top : List Bool) (a b c : MackeyDiagrams.VertexKind) =>
    planar bottom top
      [MackeyDiagrams.PlanarEvent.vertex 0 a, MackeyDiagrams.PlanarEvent.vertex 1 b,
        MackeyDiagrams.PlanarEvent.vertex 0 c]
  let rightShape := fun (bottom top : List Bool) (a b c : MackeyDiagrams.VertexKind) =>
    planar bottom top
      [MackeyDiagrams.PlanarEvent.vertex 1 a, MackeyDiagrams.PlanarEvent.vertex 0 b,
        MackeyDiagrams.PlanarEvent.vertex 1 c]
  let realizes := fun {K H : Subgroup U}
      {bottom p q top : MackeyDiagrams.Word K H}
      (first : Stage bottom p) (second : Stage p q) (third : Stage q top)
      (shape : MackeyDiagrams.PlanarShape) =>
    ∀ (x : Finsupp first.1 Complex) (y : Finsupp second.1 Complex)
      (z : Finsupp third.1 Complex)
      (hx : ∀ d ∈ Finsupp.support x, first.2.1 d)
      (hy : ∀ d ∈ Finsupp.support y, second.2.1 d)
      (hz : ∀ d ∈ Finsupp.support z, third.2.1 d),
      let d₁ := first.2.2 x hx
      let d₂ := second.2.2 y hy
      let d₃ := third.2.2 z hz
      let drawing := stack d₁ (stack d₂ d₃)
      MackeyDiagrams.LabelledDrawing.planarShape drawing = shape ∧
        eval drawing = MackeyDiagrams.Biset.Hom.vertical (eval d₁)
          (MackeyDiagrams.Biset.Hom.vertical (eval d₂) (eval d₃))
  (∀ {A B : Subgroup U} (a : MackeyDiagrams.ConjEmbedding A B) (p : U)
      (_ : ∀ x : A, (MackeyDiagrams.ConjEmbedding.toHom a x : U) = MulAut.conj p (x : U)),
    {q : U | ∀ x : A, (MackeyDiagrams.ConjEmbedding.toHom a x : U) = MulAut.conj q (x : U)} =
      {q : U | p⁻¹ * q ∈ Subgroup.centralizer (A : Set U)}) ∧
  (∀ {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H)
      (d : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b)),
    let inner := tensor (up a) (down b)
    let q := fun (w : (MackeyDiagrams.Word.basis inner).carrier) =>
      MackeyDiagrams.Generator.mixedProduct α β
        (MackeyDiagrams.Generator.mixedMultiplicationBasis α β a b d w)
    let traceDot := MackeyDiagrams.Dot.inverse d
    let traceInput := fun (z : G) (t : H) =>
      z * (MackeyDiagrams.ConjEmbedding.toHom β t)⁻¹ * MackeyDiagrams.Dot.element traceDot
    let traceSurvivors := fun (T : Set H) (z : G) =>
      {t : H | t ∈ T ∧ traceInput z t ∈ MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom α)}
    (∀ (k : K) (h : H),
      q (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
          (MackeyDiagrams.Biset.restriction b) k h) =
        MackeyDiagrams.ConjEmbedding.toHom α k * MackeyDiagrams.Dot.element d *
          MackeyDiagrams.ConjEmbedding.toHom β h) ∧
    (∀ w : (MackeyDiagrams.Word.basis inner).carrier,
      MackeyDiagrams.Biset.Hom.toLinearMap
          (MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.mixedMultiplication (R := Complex) α β a b d))
          (Finsupp.single w 1) =
        Finsupp.single (MackeyDiagrams.Generator.mixedPair α β (q w)) 1) ∧
    MackeyDiagrams.Dot.element traceDot = (MackeyDiagrams.Dot.element d)⁻¹ ∧
    (∀ hf : ∀ z : G, Set.Finite {w | q w = z},
      let diagram := MackeyDiagrams.Diagram.mixedProjection (R := Complex) α β a b d
        (fun z => Set.Finite.subset (hf (MackeyDiagrams.Generator.mixedProduct α β z))
          (fun _ hw => congrArg (MackeyDiagrams.Generator.mixedProduct α β) hw))
      let valueAt := fun z : G => MackeyDiagrams.Biset.Hom.toLinearMap
        (MackeyDiagrams.Diagram.eval diagram)
        (Finsupp.single (MackeyDiagrams.Generator.mixedPair α β z) 1)
      (∀ z : G, valueAt z = Finset.sum (Set.Finite.toFinset (hf z))
        (fun w => Finsupp.single w 1)) ∧
      (∀ (T : Set H)
          (_ : ∀ h : H, ∃! t : H, t ∈ T ∧
            h * t⁻¹ ∈ MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b))
          (z : G),
        ∃ hs : Set.Finite (traceSurvivors T z),
          valueAt z = Finset.sum (Set.Finite.toFinset hs) (fun t =>
            MackeyDiagrams.Biset.pairLinear Complex (MackeyDiagrams.Biset.induction a)
              (MackeyDiagrams.Biset.restriction b)
              (MackeyDiagrams.Generator.traceBasis Complex α (traceInput z t))
              (Finsupp.single t 1))))) ∧
  (∀ {K H G L : Subgroup U}
      (α : MackeyDiagrams.ConjEmbedding K G) (β : MackeyDiagrams.ConjEmbedding H G)
      (a : MackeyDiagrams.ConjEmbedding L K) (b : MackeyDiagrams.ConjEmbedding L H)
      (x : MackeyDiagrams.DotLabel Complex (MackeyDiagrams.ConjEmbedding.comp α a)
        (MackeyDiagrams.ConjEmbedding.comp β b)),
    (∀ w : (MackeyDiagrams.Word.basis (tensor (up a) (down b))).carrier,
      MackeyDiagrams.Biset.Hom.toLinearMap (eval ((multiply α β a b).2.2 x (fun _ _ => True.intro)))
          (Finsupp.single w 1) =
        List.sum (List.map (fun term =>
          term.1 • Finsupp.single
            (MackeyDiagrams.Generator.mixedMultiplicationBasis α β a b term.2 w) 1)
          (MackeyDiagrams.DotLabel.terms x))) ∧
    (∀ hx : ∀ d ∈ Finsupp.support x, finiteFibers α β a b d,
      let terms := projectionTerms α β a b x hx
      let drawing := (project α β a b).2.2 x hx
      eval drawing = eval (MackeyDiagrams.LabelledDrawing.expandedProjection α β a b terms
        MackeyDiagrams.ProjectionOpening.cupAndMerge MackeyDiagrams.ProjectionClosing.splitAndTrace) ∧
      (∀ z : G,
        let basis := MackeyDiagrams.Generator.mixedPair α β z
        MackeyDiagrams.Biset.Hom.toLinearMap (eval drawing) (Finsupp.single basis 1) =
          List.sum (List.map (fun term =>
            term.1 • Finset.sum (Set.Finite.toFinset
              (MackeyDiagrams.ProjectionDot.finite
                (multiplication := MackeyDiagrams.Generator.mixedMultiplicationBasis α β a b)
                term.2 basis)) (fun w => Finsupp.single w 1)) terms)))) ∧
  (∀ {G A D F C E B B' : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding G A) (b : MackeyDiagrams.ConjEmbedding D A)
      (c : MackeyDiagrams.ConjEmbedding F D) (d : MackeyDiagrams.ConjEmbedding C G)
      (e : MackeyDiagrams.ConjEmbedding E C) (f : MackeyDiagrams.ConjEmbedding E F)
      (r : MackeyDiagrams.ConjEmbedding B G) (s : MackeyDiagrams.ConjEmbedding B D)
      (t : MackeyDiagrams.ConjEmbedding E B) (u' : MackeyDiagrams.ConjEmbedding B' A)
      (v : MackeyDiagrams.ConjEmbedding C B') (w : MackeyDiagrams.ConjEmbedding F B'),
    let left₁ := at₁ (project a b r s) (up c)
    let left₂ := at₂ (up r) (project s c t f)
    let left₃ := at₁ (parallel r t d e) (down f)
    let right₁ := at₂ (down a) (parallel b c u' w)
    let right₂ := at₁ (project a u' d v) (up w)
    let right₃ := at₂ (up d) (project v w e f)
    let left₁' := at₁ (parallel d e r t) (down f)
    let left₂' := at₂ (up r) (multiply s c t f)
    let left₃' := at₁ (multiply a b r s) (up c)
    let right₁' := at₂ (up d) (multiply v w e f)
    let right₂' := at₁ (multiply a u' d v) (up w)
    let right₃' := at₂ (down a) (parallel u' w b c)
    let projectLeft := realizes left₁ left₂ left₃
      (leftShape [false, true, true] [true, true, false]
        MackeyDiagrams.VertexKind.mixedProjection MackeyDiagrams.VertexKind.mixedProjection
        MackeyDiagrams.VertexKind.parallelUp)
    let projectRight := realizes right₁ right₂ right₃
      (rightShape [false, true, true] [true, true, false]
        MackeyDiagrams.VertexKind.parallelUp MackeyDiagrams.VertexKind.mixedProjection
        MackeyDiagrams.VertexKind.mixedProjection)
    let multiplyLeft := realizes left₁' left₂' left₃'
      (leftShape [true, true, false] [false, true, true]
        MackeyDiagrams.VertexKind.parallelUp MackeyDiagrams.VertexKind.mixedMultiplication
        MackeyDiagrams.VertexKind.mixedMultiplication)
    let multiplyRight := realizes right₁' right₂' right₃'
      (rightShape [true, true, false] [false, true, true]
        MackeyDiagrams.VertexKind.mixedMultiplication MackeyDiagrams.VertexKind.mixedMultiplication
        MackeyDiagrams.VertexKind.parallelUp)
    let cases : List (Nat × (Prop × Prop)) :=
      [(1, (projectLeft, projectRight)), (2, (projectRight, projectLeft)),
       (3, (multiplyLeft, multiplyRight)), (4, (multiplyRight, multiplyLeft))]
    ∀ direction ∈ cases, direction.2.1 ∧ direction.2.2) ∧
  (∀ {G A D F C E B B' : Subgroup U}
      (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
      (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
      (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E)
      (u' : MackeyDiagrams.ConjEmbedding G B) (v : MackeyDiagrams.ConjEmbedding D B)
      (w : MackeyDiagrams.ConjEmbedding E B) (i : MackeyDiagrams.ConjEmbedding B' A)
      (j : MackeyDiagrams.ConjEmbedding B' F) (k : MackeyDiagrams.ConjEmbedding B' C),
    let left₁ := at₁ (multiply u' v a b) (up d)
    let left₂ := at₂ (down u') (parallel v d w f)
    let left₃ := at₁ (project u' w c e) (up f)
    let right₁ := at₂ (up a) (project b d i j)
    let right₂ := at₁ (parallel a i c k) (down j)
    let right₃ := at₂ (up c) (multiply e f k j)
    let mixedLeft := realizes left₁ left₂ left₃
      (leftShape [true, false, true] [true, false, true]
        MackeyDiagrams.VertexKind.mixedMultiplication MackeyDiagrams.VertexKind.parallelUp
        MackeyDiagrams.VertexKind.mixedProjection)
    let mixedRight := realizes right₁ right₂ right₃
      (rightShape [true, false, true] [true, false, true]
        MackeyDiagrams.VertexKind.mixedProjection MackeyDiagrams.VertexKind.parallelUp
        MackeyDiagrams.VertexKind.mixedMultiplication)
    let cases : List (Nat × (Prop × Prop)) :=
      [(5, (mixedLeft, mixedRight)), (6, (mixedRight, mixedLeft))]
    ∀ direction ∈ cases, direction.2.1 ∧ direction.2.2)
) :=
(by
  classical
  intro U inst up down tensor stack juxtapose plain Stage place at₁ at₂ parallel finiteFibers
    multiply projectionTerms project eval planar leftShape rightShape realizes
  refine ⟨MixedCrossingFiniteFiberConventionAux.representativeCoset, ?_, ?_, ?_, ?_⟩
  · -- Proposition 5.1 identifies the projection column in group coordinates.
    -- Match that fiber with the shared balanced basis before comparing the sums.
    intro K H G L α β a b d inner q traceDot traceInput traceSurvivors
    obtain ⟨hq, hm, hp⟩ := MixedCrossingFiniteFiberConventionAux.singletonColumns α β a b d
    refine ⟨hq, hm, rfl, ?_⟩
    intro hf diagram valueAt
    have hf' : finiteFibers α β a b d :=
      fun z => (hf (MackeyDiagrams.Generator.mixedProduct α β z)).subset
        (fun _ hw => congrArg (MackeyDiagrams.Generator.mixedProduct α β) hw)
    obtain ⟨hcolumn, htrace⟩ := hp hf'
    refine ⟨?_, htrace⟩
    intro z
    refine (hcolumn z).trans ?_
    congr 1
    ext w
    simp only [Set.Finite.mem_toFinset]
    exact Set.ext_iff.mp (MixedCrossingFiniteFiberConventionAux.groupFiber α β a b d z) w
  · -- The convention is termwise on the actual finite support of the linear label.
    -- The expansion theorem uses finite surviving columns even at infinite cup index.
    intro K H G L α β a b x
    refine ⟨MixedCrossingFiniteFiberConventionAux.multiplyColumn α β a b
      (MackeyDiagrams.DotLabel.terms x), ?_⟩
    intro hx terms drawing
    exact ⟨(MackeyDiagrams.LabelledDrawing.eval_expandProjection α β a b terms
      .cupAndMerge .splitAndTrace).symm, fun z =>
      MixedCrossingFiniteFiberConventionAux.projectColumn α β a b terms
        (MackeyDiagrams.Generator.mixedPair α β z)⟩
  · -- Cases 1–4 use the drawings on archived pp. 22 and 24 (published pp. 24 and 26).
    -- The tensor reassociations are straight wiring. Projection labels affect
    -- evaluation through the per-term finite witness and leave the vertex in place.
    intro G A D F C E B B' a b c d e f r s t u' v w
      left₁ left₂ left₃ right₁ right₂ right₃ left₁' left₂' left₃' right₁' right₂' right₃'
      projectLeft projectRight multiplyLeft multiplyRight cases
    have hpl : projectLeft := by intro x y z hx hy hz; exact ⟨rfl, rfl⟩
    have hpr : projectRight := by intro x y z hx hy hz; exact ⟨rfl, rfl⟩
    have hml : multiplyLeft := by intro x y z hx hy hz; exact ⟨rfl, rfl⟩
    have hmr : multiplyRight := by intro x y z hx hy hz; exact ⟨rfl, rfl⟩
    intro direction hd
    change direction ∈ [(1, (projectLeft, projectRight)), (2, (projectRight, projectLeft)),
      (3, (multiplyLeft, multiplyRight)), (4, (multiplyRight, multiplyLeft))] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨hpl, hpr⟩
    · exact ⟨hpr, hpl⟩
    · exact ⟨hml, hmr⟩
    · exact ⟨hmr, hml⟩
  · -- Cases 5–6 each have one multiplication and one projection. The two
    -- bottom-to-top crossing orders are those on archived p. 25 (published p. 27).
    intro G A D F C E B B' a b d c e f u' v w i j k
      left₁ left₂ left₃ right₁ right₂ right₃ mixedLeft mixedRight cases
    have hml : mixedLeft := by intro x y z hx hy hz; exact ⟨rfl, rfl⟩
    have hmr : mixedRight := by intro x y z hx hy hz; exact ⟨rfl, rfl⟩
    intro direction hd
    change direction ∈ [(5, (mixedLeft, mixedRight)), (6, (mixedRight, mixedLeft))] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hml, hmr⟩
    · exact ⟨hmr, hml⟩)

#print axioms MixedCrossingFiniteFiberConvention
