
set_option maxHeartbeats 3000000

universe u v

theorem GeneralizedMackeyDecomposition : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (α β : U),
  let Kα := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj α)) K
  let Hβ := Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj β)) H
  ∀ (hK : Kα ≤ G) (hH : Hβ ≤ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator (H := K) (G := G) α
      (fun k => hK ⟨(k : U), k.property, rfl⟩)
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator (H := H) (G := G) β
      (fun h => hH ⟨(h : U), h.property, rfl⟩)
    let A := Subgroup.comap (Subgroup.subtype G) Kα
    let B := Subgroup.comap (Subgroup.subtype G) Hβ
    let J := DoubleCoset.Quotient (A : Set G) (B : Set G)
    ∀ (σ : J → G) (_ : ∀ j : J, DoubleCoset.mk A B (σ j) = j),
      let L := fun j : J =>
        Kα ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj ((σ j : U) * β))) H
      let l := fun j : J =>
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := K) α⁻¹
          (by
            intro ℓ
            obtain ⟨k, hk, h⟩ := ℓ.property.1
            change α * k * α⁻¹ = (ℓ : U) at h
            change k ∈ K at hk
            rw [← h]
            convert hk using 1
            group)
      let r := fun j : J =>
        let s := σ j
        MackeyDiagrams.ConjEmbedding.ofConjugator (H := L j) (G := H)
          (β⁻¹ * (s : U)⁻¹)
          (by
            intro ℓ
            obtain ⟨h, hh, e⟩ := ℓ.property.2
            change (s : U) * β * h * ((s : U) * β)⁻¹ = (ℓ : U) at e
            change h ∈ H at hh
            rw [← e]
            convert hh using 1
            group)
      let down := MackeyDiagrams.Word.down a
      let up := MackeyDiagrams.Word.up b
      let M := MackeyDiagrams.Word.tensor down up
      let Mj := fun j : J =>
        MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up (l j)) (MackeyDiagrams.Word.down (r j))
      let W := MackeyDiagrams.Word.basis M
      let Wj := fun j : J => MackeyDiagrams.Word.basis (Mj j)
      let V := Finsupp W.carrier Complex
      let Vj := fun j : J => Finsupp (Wj j).carrier Complex
      let groupAlgebra := MonoidAlgebra Complex G
      let coordinates : LinearEquiv (RingHom.id Complex) V groupAlgebra :=
        LinearEquiv.trans
          (Finsupp.domLCongr (MackeyDiagrams.Generator.mixedEquiv a b))
          (MonoidAlgebra.coeffLinearEquiv Complex).symm
      let groupAlgebraAction := fun (g : K × H) (x : groupAlgebra) =>
        MonoidAlgebra.of Complex G (MackeyDiagrams.ConjEmbedding.toHom a g.1) * x *
          MonoidAlgebra.of Complex G ((MackeyDiagrams.ConjEmbedding.toHom b g.2)⁻¹)
      let Mod := fun S : Subgroup U => ModuleCat.{max u v} (MonoidAlgebra Complex S)
      let Res := fun {S T : Subgroup U} (f : MackeyDiagrams.ConjEmbedding S T) =>
        (ModuleCat.restrictScalars
          (MonoidAlgebra.mapDomainAlgHom Complex Complex
            (MackeyDiagrams.ConjEmbedding.toHom f)).toRingHom :
          CategoryTheory.Functor (Mod T) (Mod S))
      let Ind := fun {S T : Subgroup U} (f : MackeyDiagrams.ConjEmbedding S T) =>
        (CategoryTheory.Functor.comp
          (CategoryTheory.Functor.comp
            (Rep.ofModuleMonoidAlgebra (k := Complex) (G := S))
            (Rep.indFunctor Complex (MackeyDiagrams.ConjEmbedding.toHom f)))
          (Rep.toModuleMonoidAlgebra (k := Complex) (G := T)) :
          CategoryTheory.Functor (Mod S) (Mod T))
      let summand := fun j : J => CategoryTheory.Functor.comp (Res (r j)) (Ind (l j))
      (∀ (g : K × H) (x : V),
        coordinates (MackeyDiagrams.Biset.actLinear Complex W g x) =
          groupAlgebraAction g (coordinates x)) ∧
      ∃ (projection : ∀ j : J, MackeyDiagrams.Diagram Complex M (Mj j))
        (inclusion : ∀ j : J, MackeyDiagrams.Diagram Complex (Mj j) M),
        let straight : MackeyDiagrams.Diagram Complex M M :=
          MackeyDiagrams.Diagram.horizontal
            (MackeyDiagrams.Diagram.id down) (MackeyDiagrams.Diagram.id up)
        let term := fun (x : V) (j : J) =>
          MackeyDiagrams.Biset.Hom.toLinearMap
            (MackeyDiagrams.Diagram.eval
              (MackeyDiagrams.Diagram.vertical (projection j) (inclusion j))) x
        (∃ finite : ∀ x : V, Set.Finite (Function.support (term x)),
          ∀ x : V, MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval straight) x =
            Finset.sum (Set.Finite.toFinset (finite x)) (term x)) ∧
        (∀ j : J,
          MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical (inclusion j) (projection j)) =
            MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id (Mj j))) ∧
        (∀ (i j : J), i ≠ j →
          MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical (inclusion i) (projection j)) =
            MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.zero (Mj i) (Mj j))) ∧
        (∃ e : LinearEquiv (RingHom.id Complex) groupAlgebra (DFinsupp Vj),
          (∀ (x : V) (j : J),
            e (coordinates x) j = MackeyDiagrams.Biset.Hom.toLinearMap
              (MackeyDiagrams.Diagram.eval (projection j)) x) ∧
          (∀ (g : K × H) (x : groupAlgebra) (j : J),
            e (groupAlgebraAction g x) j =
              MackeyDiagrams.Biset.actLinear Complex (Wj j) g (e x j))) ∧
        Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp (Ind b) (Res a))
          (CategoryTheory.Limits.sigmaObj summand))
) :=
