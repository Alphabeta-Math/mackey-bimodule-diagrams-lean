import Final
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  for n in [ `FiniteParabolicCompositionSupport.middleMackey,
             `FiniteParabolicCompositionSupport.spanTensorIso,
             `FiniteParabolicCompositionSupport.composeSpan_basis,
             `ParabolicTensorSupport.mackeyBisetIso ] do
    let name := mkPrivateNameCore `Final n
    unless env.contains name do
      throwError "Missing declaration {name}"
    logInfo m!"{n}: {← collectAxioms name}"

#print axioms FiniteParabolicBicategoryComposition
#print axioms GeneralizedMackeyDecomposition
#check DoubleCoset.out_eq'
#check @sigmaFinsuppLequivDFinsupp
#check @DFinsupp.ext
#check MackeyDiagrams.ConjEmbedding.ext

open MackeyDiagrams

section
variable {U : Type} [Group U]

private abbrev conjugate (p : U) (S : Subgroup U) :=
  S.map (MulAut.conj p).toMonoidHom

private abbrev inside (G A : Subgroup U) := Subgroup.comap G.subtype A
private abbrev Cosets (G A B : Subgroup U) := DoubleCoset.Quotient (inside G A : Set G) (inside G B : Set G)
private abbrev classOf (G A B : Subgroup U) (r : G) : Cosets G A B :=
  DoubleCoset.mk (inside G A) (inside G B) r

private theorem conjugate_mul_checked (p q : U) (S : Subgroup U) :
    conjugate (p * q) S = conjugate p (conjugate q S) := by
  change S.map (MulAut.conj (p * q)).toMonoidHom =
    (S.map (MulAut.conj q).toMonoidHom).map (MulAut.conj p).toMonoidHom
  have h : (MulAut.conj (p * q)).toMonoidHom =
      (MulAut.conj p).toMonoidHom.comp (MulAut.conj q).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change (p * q) * x * (p * q)⁻¹ = p * (q * x * q⁻¹) * p⁻¹
    group
  rw [Subgroup.map_map, h]

private theorem quotOut_checked (G A B : Subgroup U) (j : Cosets G A B) :
    classOf G A B j.out = j := DoubleCoset.out_eq' j

private theorem left_comp_checked (a b x : U) :
    a * (b⁻¹ * x * (b⁻¹)⁻¹) * a⁻¹ = (a * b⁻¹) * x * (a * b⁻¹)⁻¹ := by
  group

private theorem right_middle_checked (c r x : U) :
    c⁻¹ * (r⁻¹ * x * (r⁻¹)⁻¹) * (c⁻¹)⁻¹ =
      (r * c)⁻¹ * x * ((r * c)⁻¹)⁻¹ := by
  group

private theorem right_comp_checked (d c r x : U) :
    d * (c⁻¹ * (r⁻¹ * x * (r⁻¹)⁻¹) * (c⁻¹)⁻¹) * d⁻¹ =
      (d * c⁻¹ * r⁻¹) * x * (d * c⁻¹ * r⁻¹)⁻¹ := by
  group

private theorem mixed_action_checked {A B G : Subgroup U}
    (a : ConjEmbedding A G) (b : ConjEmbedding B G) (g : A × B)
    (x : ((Biset.restriction a).tensor (Biset.induction b)).carrier) :
    Generator.mixedEquiv a b (((Biset.restriction a).tensor (Biset.induction b)).act g x) =
      a.toHom g.1 * Generator.mixedEquiv a b x * (b.toHom g.2)⁻¹ := by
  refine Quotient.inductionOn x (fun z => ?_)
  change (a.toHom g.1 * z.1 * (1 : G)⁻¹) * (1 * z.2 * (b.toHom g.2)⁻¹) =
    a.toHom g.1 * (z.1 * z.2) * (b.toHom g.2)⁻¹
  simp [mul_assoc]

private theorem section_checked (A B G : Subgroup U) (α β : U)
    (hA : conjugate α A ≤ G) (hB : conjugate β B ≤ G)
    (r : Cosets G (conjugate α A) (conjugate β B) → G)
    (hr : ∀ j, classOf G (conjugate α A) (conjugate β B) (r j) = j) : True := by
  obtain ⟨hcoord, projection, inclusion, hsum, hdiag, hoff, ⟨e, _, he⟩, _⟩ :=
    GeneralizedMackeyDecomposition.{0, 0} A B G α β hA hB r hr
  trivial

end
