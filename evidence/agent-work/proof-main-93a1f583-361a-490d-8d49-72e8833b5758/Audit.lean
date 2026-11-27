import MackeyDiagrams
import Proofs.MixedCrossingFiberMaps
universe u
set_option maxHeartbeats 2000000

def originalEndpoint : Prop :=
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
          (MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.mixedMultiplication α β a b d))
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

def correctedEndpoint : Prop :=
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

open Lean in
run_cmd do
  for (decl, expected) in [(`originalEndpoint, `Nat), (`correctedEndpoint, `Complex)] do
    let proposition := (← getConstInfoDefn decl).value
    let some multiplication := proposition.find? (fun e =>
      e.getAppFn.isConstOf `MackeyDiagrams.Diagram.mixedMultiplication && e.getAppNumArgs == 12)
      | throwError "Missing multiplication diagram in {decl}"
    let coefficient := multiplication.getAppArgs[2]!
    unless coefficient.isConstOf expected do
      throwError "Unexpected coefficient in {decl}"
    logInfo m!"{decl} uses {expected}"
