import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionBimoduleOrbitSumBasis

#check (∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
  (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
  (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let A := MonoidAlgebra Complex H
  let B := MonoidAlgebra Complex G
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom a)
  let ψ := MonoidAlgebra.mapDomainAlgHom Complex Complex (MackeyDiagrams.ConjEmbedding.toHom b)
  let action := fun (h : H) (g : G) =>
    MackeyDiagrams.ConjEmbedding.toHom a h * g * (MackeyDiagrams.ConjEmbedding.toHom b h)⁻¹
  let orbit := fun g : G => Set.range (fun h : H => action h g)
  let OrbitIndex := {s : Finset G // ∃ g : G, (s : Set G) = orbit g}
  let orbitSum := fun i : OrbitIndex =>
    Finset.sum (Subtype.val i) (fun g => MonoidAlgebra.single g (1 : Complex))
  let HomSpace : Submodule Complex (LinearMap (RingHom.id Complex) B B) :=
    { carrier := { f |
        (∀ s x : B, f (s * x) = s * f x) ∧
        (∀ (r : A) (x : B), f (x * φ r) = f x * ψ r) }
      zero_mem' := by
        simp
      add_mem' := by
        rintro f g ⟨hfL, hfR⟩ ⟨hgL, hgR⟩
        exact ⟨fun s x => by simp [hfL, hgL, mul_add],
          fun r x => by simp [hfR, hgR, add_mul]⟩
      smul_mem' := by
        rintro c f ⟨hfL, hfR⟩
        exact ⟨fun s x => by simp [hfL],
          fun r x => by simp [hfR]⟩ }
  ∃ basis : Module.Basis OrbitIndex Complex HomSpace,
    (∀ (i : OrbitIndex) (x : B), Subtype.val (basis i) x = x * orbitSum i) ∧
    (∀ g : G, (∃ d : MackeyDiagrams.Dot a b, MackeyDiagrams.Dot.element d = g) ↔ orbit g = {g}) ∧
    (∀ [Finite H],
      let T : Subgroup U := ⊥
      let j : MackeyDiagrams.ConjEmbedding T H :=
        MackeyDiagrams.ConjEmbedding.ofConjugator (1 : U) (by
          intro t
          have ht : (t : U) = 1 := Subgroup.mem_bot.mp t.property
          simp [ht])
      let finiteIndex : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom j)) :=
        Subgroup.finiteIndex_of_finite
      let p := MackeyDiagrams.Word.up a
      let q := MackeyDiagrams.Word.up b
      let up := MackeyDiagrams.Word.up j
      let down := MackeyDiagrams.Word.down j
      let groupElements : Finset H := @Finset.univ H (Fintype.ofFinite H)
      ∀ g : G,
        let finiteOrbit : Set.Finite (orbit g) := Set.finite_range (fun h : H => action h g)
        let i : OrbitIndex :=
          ⟨Set.Finite.toFinset finiteOrbit, ⟨g, Set.Finite.coe_toFinset finiteOrbit⟩⟩
        let order : Complex := (Nat.card {h : H // action h g = g} : Complex)
        let dot : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a j)
            (MackeyDiagrams.ConjEmbedding.comp b j) :=
          { element := g
            intertwines := by
              intro t
              have ht : t = 1 := Subtype.ext (Subgroup.mem_bot.mp t.property)
              rw [ht, map_one, map_one, one_mul, mul_one] }
        let cup := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.id p) (MackeyDiagrams.Diagram.reverseCup (R := Complex) j finiteIndex)
        let merge := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.mergeUp (R := Complex) a j) (MackeyDiagrams.Diagram.id down)
        let dotStep := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.upDot (R := Complex) dot) (MackeyDiagrams.Diagram.id down)
        let split := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.splitUp (R := Complex) b j) (MackeyDiagrams.Diagram.id down)
        let cap := MackeyDiagrams.Diagram.horizontal
          (MackeyDiagrams.Diagram.id q) (MackeyDiagrams.Diagram.multiplicationCap (R := Complex) j)
        let d : MackeyDiagrams.Diagram Complex p q :=
          MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.insertRightUnit p)
            (MackeyDiagrams.Diagram.vertical cup
              (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.unassociate p up down)
                (MackeyDiagrams.Diagram.vertical merge
                  (MackeyDiagrams.Diagram.vertical dotStep
                    (MackeyDiagrams.Diagram.vertical split
                      (MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.associate q up down)
                        (MackeyDiagrams.Diagram.vertical cap (MackeyDiagrams.Diagram.rightUnit q))))))))
        let sumOverH : B := Finset.sum groupElements (fun t =>
          MonoidAlgebra.single
            (MackeyDiagrams.ConjEmbedding.toHom a t⁻¹ * g * MackeyDiagrams.ConjEmbedding.toHom b t)
            (1 : Complex))
        IsUnit order ∧
        (∀ x : B,
          MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval d)
              (MonoidAlgebra.coeff x) = MonoidAlgebra.coeff (x * sumOverH) ∧
          x * sumOverH = x * (order • orbitSum i)) ∧
        (∀ x : B,
          MackeyDiagrams.Biset.Hom.toLinearMap
              (MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.scale order⁻¹ d))
              (MonoidAlgebra.coeff x) = MonoidAlgebra.coeff (Subtype.val (basis i) x))))
#check FiniteIndexReverseAdjunction
#check InductionBimoduleOrbitSumBasis
